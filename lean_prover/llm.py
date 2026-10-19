from __future__ import annotations

import http.client
import json
import os
import threading
import time
import urllib.parse
from dataclasses import dataclass

BASE_URL = os.environ.get("LEAN_PROVER_BASE_URL", "http://localhost:8000/v1")
MODEL = os.environ.get("LEAN_PROVER_MODEL", "")
API_KEY = os.environ.get("LEAN_PROVER_API_KEY", "")


def _headers() -> dict:
    if not MODEL:
        raise LLMFailure("LEAN_PROVER_MODEL is not set (the model name served at LEAN_PROVER_BASE_URL)")
    h = {"Content-Type": "application/json"}
    if API_KEY:
        h["Authorization"] = f"Bearer {API_KEY}"
    return h


def _connect(url, timeout: float):
    if url.scheme == "https":
        return http.client.HTTPSConnection(url.hostname, url.port or 443, timeout=timeout)
    return http.client.HTTPConnection(url.hostname, url.port or 80, timeout=timeout)


class PrioritySemaphore:
    """Semaphore where waiters with higher priority are served first (FIFO within a priority)."""

    def __init__(self, n: int):
        self._n = n
        self._cv = threading.Condition()
        self._waiting: list[tuple[int, int]] = []  # (-priority, ticket)
        self._ticket = 0

    def acquire(self, priority: int = 0, stop_check=None) -> bool:
        """Returns False (without taking a slot) if stop_check() becomes true while waiting."""
        import heapq
        with self._cv:
            self._ticket += 1
            me = (-priority, self._ticket)
            heapq.heappush(self._waiting, me)
            while not (self._n > 0 and self._waiting[0] == me):
                self._cv.wait(timeout=5.0)
                if stop_check is not None and stop_check():
                    self._waiting.remove(me)
                    heapq.heapify(self._waiting)
                    self._cv.notify_all()
                    return False
            heapq.heappop(self._waiting)
            self._n -= 1
            self._cv.notify_all()
            return True

    def release(self):
        with self._cv:
            self._n += 1
            self._cv.notify_all()


_llm_sem = PrioritySemaphore(int(os.environ.get("LEAN_PROVER_LLM_JOBS", "6")))  # thinking requests
_quick_sem = PrioritySemaphore(int(os.environ.get("LEAN_PROVER_QUICK_JOBS", "2")))  # non-thinking requests

_stats_lock = threading.Lock()
STATS = {"calls": 0, "completion_tokens": 0, "reasoning_tokens": 0, "errors": 0, "seconds": 0.0}


@dataclass
class LLMResponse:
    content: str
    reasoning: str
    completion_tokens: int
    finish_reason: str | None
    seconds: float


REPEAT_LINES = 12  # this many recent non-empty lines with at most 2 distinct values = a degenerate loop


class LLMFailure(Exception):
    pass


def chat(messages: list[dict], *, max_tokens: int = 16000, temperature: float = 0.7,
         thinking: bool = True, total_timeout: float = 3600.0, retries: int = 2,
         stop_check=None, prefill: str | None = None, priority: int = 0) -> LLMResponse:
    last: Exception | None = None
    for attempt in range(retries + 1):
        try:
            sem = _llm_sem if thinking else _quick_sem
            if not sem.acquire(priority, stop_check):
                return LLMResponse("", "", 0, "cancelled", 0.0)
            try:
                if stop_check is not None and stop_check():
                    return LLMResponse("", "", 0, "cancelled", 0.0)
                return _chat_once(messages, max_tokens=max_tokens, temperature=temperature,
                                  thinking=thinking, total_timeout=total_timeout, stop_check=stop_check,
                                  prefill=prefill)
            finally:
                sem.release()
        except LLMFailure as exc:
            if prefill and "HTTP 400" in str(exc):
                prefill = None
                continue
            last = exc
            with _stats_lock:
                STATS["errors"] += 1
            time.sleep(5 * (attempt + 1))
    raise LLMFailure(str(last))


def _chat_once(messages, *, max_tokens, temperature, thinking, total_timeout, stop_check=None,
               prefill: str | None = None) -> LLMResponse:
    url = urllib.parse.urlparse(BASE_URL.rstrip("/") + "/chat/completions")
    body = {
        "model": MODEL,
        "messages": messages,
        "max_tokens": max_tokens,
        "temperature": temperature,
        "top_p": 0.95,
        "stream": True,
        "stream_options": {"include_usage": True},
        "chat_template_kwargs": {"enable_thinking": thinking},
    }
    if not thinking:
        body["repetition_penalty"] = 1.05
    if prefill:
        body["messages"] = list(messages) + [{"role": "assistant", "content": prefill}]
        body["add_generation_prompt"] = False
        body["continue_final_message"] = True
    start = time.time()
    conn = _connect(url, 600)
    content: list[str] = []
    reasoning: list[str] = []
    line_buf = ""
    recent_lines: list[str] = []
    usage = None
    finish = None
    try:
        conn.request("POST", url.path, body=json.dumps(body), headers=_headers())
        resp = conn.getresponse()
        if resp.status != 200:
            raise LLMFailure(f"HTTP {resp.status}: {resp.read()[:500]!r}")
        while True:
            line = resp.readline()
            if not line:
                break
            if time.time() - start > total_timeout:
                finish = "client_timeout"
                break
            if stop_check is not None and stop_check():
                finish = "cancelled"
                break
            if finish == "degenerate":
                break
            line = line.decode("utf-8", "replace").strip()
            if not line.startswith("data:"):
                continue
            payload = line[5:].strip()
            if payload == "[DONE]":
                break
            try:
                d = json.loads(payload)
            except json.JSONDecodeError:
                continue
            if d.get("usage"):
                usage = d["usage"]
            for ch in d.get("choices") or []:
                delta = ch.get("delta") or {}
                if delta.get("content"):
                    content.append(delta["content"])
                    line_buf += delta["content"]
                    while "\n" in line_buf:
                        done, line_buf = line_buf.split("\n", 1)
                        if done.strip():
                            recent_lines.append(done.strip())
                            recent_lines = recent_lines[-REPEAT_LINES:]
                    if len(recent_lines) == REPEAT_LINES and len(set(recent_lines)) <= 2:
                        finish = "degenerate"
                r = delta.get("reasoning_content") or delta.get("reasoning")
                if r:
                    reasoning.append(r)
                if ch.get("finish_reason"):
                    finish = ch["finish_reason"]
    except (OSError, http.client.HTTPException) as exc:
        raise LLMFailure(f"transport: {exc}") from exc
    finally:
        conn.close()
    secs = time.time() - start
    ctoks = int((usage or {}).get("completion_tokens") or 0)
    rtoks = int(((usage or {}).get("completion_tokens_details") or {}).get("reasoning_tokens") or 0)
    with _stats_lock:
        STATS["calls"] += 1
        STATS["completion_tokens"] += ctoks
        STATS["reasoning_tokens"] += rtoks
        STATS["seconds"] += secs
    text = "".join(content)
    if prefill:
        text = prefill + text
    return LLMResponse(text, "".join(reasoning), ctoks, finish, secs)


def chat_salvage(messages: list[dict], *, max_tokens: int = 14000, temperature: float = 0.8,
                 stop_check=None, final_instruction: str = "", answer_tokens: int = 6000,
                 prefill: str | None = "```lean4\n", priority: int = 0) -> LLMResponse:
    """Thinking call; if the budget is exhausted while still thinking, ask a non-thinking follow-up
    to turn the partial reasoning into a final answer."""
    resp = chat(messages, max_tokens=max_tokens, temperature=temperature, stop_check=stop_check, priority=priority)
    if resp.finish_reason == "cancelled":
        return resp
    if "```" in resp.content and resp.finish_reason != "length":
        return resp
    if "```" in resp.content and resp.content.count("```") % 2 == 0:
        return resp
    reasoning = resp.reasoning[-24000:]
    follow = list(messages) + [{
        "role": "user",
        "content": ("Your previous attempt ran out of thinking budget. Here is the tail of your reasoning so far:\n\n"
                    "<reasoning>\n" + reasoning + "\n</reasoning>\n\n" + resp.content[-4000:] +
                    "\n\nNow stop deliberating and write the final answer immediately, based on the reasoning above. "
                    + final_instruction),
    }]
    resp2 = chat(follow, max_tokens=answer_tokens, temperature=0.3, thinking=False, stop_check=stop_check,
                 prefill=prefill, priority=priority + 1)
    return LLMResponse(resp2.content, resp.reasoning, resp.completion_tokens + resp2.completion_tokens,
                       resp2.finish_reason, resp.seconds + resp2.seconds)


def chat_n(messages: list[dict], n: int, *, max_tokens: int = 4000, temperature: float = 0.6,
           prefill: str | None = None, priority: int = 0, stop_check=None) -> list[LLMResponse]:
    """Non-thinking, non-streaming request for n samples sharing one prompt (one server-side prefill)."""
    if n <= 1:
        return [chat(messages, max_tokens=max_tokens, temperature=temperature, thinking=False,
                     prefill=prefill, priority=priority, stop_check=stop_check)]
    url = urllib.parse.urlparse(BASE_URL.rstrip("/") + "/chat/completions")
    body = {
        "model": MODEL, "messages": list(messages), "max_tokens": max_tokens, "temperature": temperature,
        "top_p": 0.95, "n": n, "stream": False, "repetition_penalty": 1.05,
        "chat_template_kwargs": {"enable_thinking": False},
    }
    if prefill:
        body["messages"] = list(messages) + [{"role": "assistant", "content": prefill}]
        body["add_generation_prompt"] = False
        body["continue_final_message"] = True
    if not _quick_sem.acquire(priority, stop_check):
        return [LLMResponse("", "", 0, "cancelled", 0.0)]
    try:
        if stop_check is not None and stop_check():
            return [LLMResponse("", "", 0, "cancelled", 0.0)]
        start = time.time()
        conn = _connect(url, 1200)
        try:
            conn.request("POST", url.path, body=json.dumps(body), headers=_headers())
            resp = conn.getresponse()
            raw = resp.read()
            if resp.status != 200:
                raise LLMFailure(f"HTTP {resp.status}: {raw[:300]!r}")
            d = json.loads(raw)
        except (OSError, http.client.HTTPException, ValueError) as exc:
            raise LLMFailure(f"transport: {exc}") from exc
        finally:
            conn.close()
    finally:
        _quick_sem.release()
    secs = time.time() - start
    usage = d.get("usage") or {}
    ctoks = int(usage.get("completion_tokens") or 0)
    with _stats_lock:
        STATS["calls"] += 1
        STATS["completion_tokens"] += ctoks
        STATS["seconds"] += secs
    out = []
    choices = sorted(d.get("choices") or [], key=lambda c: c.get("index", 0))
    for ch in choices:
        text = (ch.get("message") or {}).get("content") or ""
        if prefill:
            text = prefill + text
        out.append(LLMResponse(text, "", ctoks // max(1, len(choices)), ch.get("finish_reason"), secs))
    return out
