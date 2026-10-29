from __future__ import annotations

import http.client
import json
import os
import threading
import time
import urllib.parse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass

DEFAULT_BASE_URL = "https://api.deepseek.com"
DEFAULT_MODEL = "deepseek-v4-flash"
DEEPSEEK_MODELS = ["deepseek-v4-flash", "deepseek-v4-pro"]  # offered in the web UI
# Request dialects: which fields switch thinking on/off and which sampling options the server accepts.
#   deepseek: `thinking: {type: enabled|disabled}` (+ `reasoning_effort`), as in the DeepSeek V4 API
#   vllm:     `chat_template_kwargs.enable_thinking` (Qwen-style templates), `n`, assistant prefill
#   openai:   plain Chat Completions (+ `reasoning_effort` when set)
API_STYLES = ("deepseek", "vllm", "openai")

_local = threading.local()  # per-thread model override (the web UI lets each request pick a model)


class LLMFailure(Exception):
    pass


def settings() -> dict:
    """Endpoint settings, read from the environment on every call so the web UI can change them at runtime."""
    style = (os.environ.get("LEMMATA_API_STYLE") or "deepseek").strip().lower()
    if style not in API_STYLES:
        raise LLMFailure(f"LEMMATA_API_STYLE must be one of {', '.join(API_STYLES)}, not {style!r}")
    return {
        "base_url": os.environ.get("LEMMATA_BASE_URL") or DEFAULT_BASE_URL,
        "model": getattr(_local, "model", None) or os.environ.get("LEMMATA_MODEL") or DEFAULT_MODEL,
        "api_key": os.environ.get("LEMMATA_API_KEY", ""),
        "style": style,
        "reasoning_effort": os.environ.get("LEMMATA_REASONING_EFFORT", ""),
    }


class use_model:
    """`with llm.use_model("deepseek-v4-pro"): ...` sends this thread's requests to another model."""

    def __init__(self, model: str | None):
        self.model = model or None

    def __enter__(self):
        self.prev = getattr(_local, "model", None)
        _local.model = self.model

    def __exit__(self, *exc):
        _local.model = self.prev


def _headers(s: dict) -> dict:
    if s["style"] == "deepseek" and not s["api_key"]:
        raise LLMFailure("LEMMATA_API_KEY is not set (get a DeepSeek API key at https://platform.deepseek.com)")
    h = {"Content-Type": "application/json"}
    if s["api_key"]:
        h["Authorization"] = f"Bearer {s['api_key']}"
    return h


def _request_body(s: dict, messages: list[dict], *, max_tokens: int, temperature: float, thinking: bool,
                  prefill: str | None, stream: bool, n: int = 1) -> tuple[dict, str | None]:
    """Returns (request body, the prefill actually sent). Only vLLM continues an assistant prefill."""
    body: dict = {"model": s["model"], "messages": list(messages), "max_tokens": max_tokens}
    if s["style"] == "vllm":
        body.update(temperature=temperature, top_p=0.95, chat_template_kwargs={"enable_thinking": thinking})
        if not thinking:
            body["repetition_penalty"] = 1.05
        if n > 1:
            body["n"] = n
        if prefill:
            body["messages"].append({"role": "assistant", "content": prefill})
            body["add_generation_prompt"] = False
            body["continue_final_message"] = True
    else:
        prefill = None
        if s["style"] == "deepseek":
            body["thinking"] = {"type": "enabled" if thinking else "disabled"}
        if not thinking or s["style"] == "openai":
            body.update(temperature=temperature, top_p=0.95)  # ignored by DeepSeek in thinking mode
        if thinking and s["reasoning_effort"]:
            body["reasoning_effort"] = s["reasoning_effort"]
    if stream:
        body["stream"] = True
        body["stream_options"] = {"include_usage": True}
    return body, prefill


def _http_error(status: int, raw: bytes) -> LLMFailure:
    hint = {401: " (API key rejected)", 402: " (account balance exhausted)", 404: " (wrong base URL or model name)",
            429: " (rate limited)"}.get(status, "")
    return LLMFailure(f"HTTP {status}{hint}: {raw[:500].decode('utf-8', 'replace')}")


def _retryable(exc: Exception) -> bool:
    msg = str(exc)
    return not any(msg.startswith(f"HTTP {c}") for c in (400, 401, 402, 403, 404, 422)) and "is not set" not in msg


def ping(timeout: float = 120.0) -> str:
    """One tiny non-thinking request, so a misconfigured endpoint fails at startup with a readable message
    instead of every attempt failing silently. Returns the model's reply."""
    s = settings()
    url = urllib.parse.urlparse(s["base_url"].rstrip("/") + "/chat/completions")
    body, _ = _request_body(s, [{"role": "user", "content": "Reply with the single word OK."}], max_tokens=16,
                            temperature=0.0, thinking=False, prefill=None, stream=False)
    conn = _connect(url, timeout)
    try:
        conn.request("POST", url.path, body=json.dumps(body), headers=_headers(s))
        resp = conn.getresponse()
        raw = resp.read()
        if resp.status != 200:
            raise _http_error(resp.status, raw)
        d = json.loads(raw)
    except (OSError, http.client.HTTPException, ValueError) as exc:
        raise LLMFailure(f"cannot reach {s['base_url']}: {exc}") from exc
    finally:
        conn.close()
    return ((d.get("choices") or [{}])[0].get("message") or {}).get("content") or ""


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


_llm_sem = PrioritySemaphore(int(os.environ.get("LEMMATA_LLM_JOBS", "6")))  # thinking requests
_quick_sem = PrioritySemaphore(int(os.environ.get("LEMMATA_QUICK_JOBS", "2")))  # non-thinking requests

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
                STATS["last_error"] = str(exc)[:300]
            if not _retryable(exc):
                break
            time.sleep(5 * (attempt + 1))
    raise LLMFailure(str(last))


def _chat_once(messages, *, max_tokens, temperature, thinking, total_timeout, stop_check=None,
               prefill: str | None = None) -> LLMResponse:
    s = settings()
    url = urllib.parse.urlparse(s["base_url"].rstrip("/") + "/chat/completions")
    body, prefill = _request_body(s, messages, max_tokens=max_tokens, temperature=temperature, thinking=thinking,
                                  prefill=prefill, stream=True)
    start = time.time()
    conn = _connect(url, 600)
    content: list[str] = []
    reasoning: list[str] = []
    line_buf = ""
    recent_lines: list[str] = []
    usage = None
    finish = None
    try:
        conn.request("POST", url.path, body=json.dumps(body), headers=_headers(s))
        resp = conn.getresponse()
        if resp.status != 200:
            raise _http_error(resp.status, resp.read())
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
    s = settings()
    if s["style"] != "vllm":
        # only vLLM returns several samples for one request; elsewhere send n requests side by side
        model = s["model"]

        def one(_):
            with use_model(model):
                return chat(messages, max_tokens=max_tokens, temperature=temperature, thinking=False,
                            prefill=prefill, priority=priority, stop_check=stop_check)
        with ThreadPoolExecutor(max_workers=n) as ex:
            return list(ex.map(one, range(n)))
    url = urllib.parse.urlparse(s["base_url"].rstrip("/") + "/chat/completions")
    body, prefill = _request_body(s, messages, max_tokens=max_tokens, temperature=temperature, thinking=False,
                                  prefill=prefill, stream=False, n=n)
    if not _quick_sem.acquire(priority, stop_check):
        return [LLMResponse("", "", 0, "cancelled", 0.0)]
    try:
        if stop_check is not None and stop_check():
            return [LLMResponse("", "", 0, "cancelled", 0.0)]
        start = time.time()
        conn = _connect(url, 1200)
        try:
            conn.request("POST", url.path, body=json.dumps(body), headers=_headers(s))
            resp = conn.getresponse()
            raw = resp.read()
            if resp.status != 200:
                raise _http_error(resp.status, raw)
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
