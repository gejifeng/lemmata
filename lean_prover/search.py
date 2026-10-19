"""Mathlib premise search: LeanSearch (natural language), Loogle (constant/type patterns), checked against the
local Mathlib environment so only declarations that really exist here (with their local types) are returned."""
from __future__ import annotations

import hashlib
import json
import re
import threading
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass

from . import names

from .paths import SEARCH_CACHE as CACHE_FILE
LEANSEARCH_URL = "https://leansearch.net/search"
LOOGLE_URL = "https://loogle.lean-lang.org/json"
_cache: dict[str, list] | None = None
_cache_lock = threading.Lock()
_net_sem = threading.Semaphore(4)
STATS = {"leansearch": 0, "loogle": 0, "cache_hits": 0, "errors": 0, "dropped_not_local": 0}


@dataclass
class Premise:
    name: str
    type: str
    source: str
    informal: str = ""

    def render(self) -> str:
        line = f"{self.name} : {self.type}"
        return line if len(line) < 400 else line[:400] + " …"


def _load_cache() -> dict[str, list]:
    global _cache
    with _cache_lock:
        if _cache is None:
            _cache = {}
            try:
                for line in CACHE_FILE.read_text(encoding="utf-8").splitlines():
                    row = json.loads(line)
                    _cache[row["key"]] = row["value"]
            except (OSError, ValueError):
                pass
        return _cache


def _cached(kind: str, query: str, fetch) -> list:
    key = hashlib.sha256(f"{kind}\n{query}".encode()).hexdigest()
    cache = _load_cache()
    if key in cache:
        STATS["cache_hits"] += 1
        return cache[key]
    value = fetch()
    if value is None:  # network failure: do not cache
        return []
    with _cache_lock:
        cache[key] = value
        with CACHE_FILE.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps({"key": key, "kind": kind, "query": query, "value": value}, ensure_ascii=False) + "\n")
    return value


USER_AGENT = "lean_prover/0.1 (automated Lean theorem proving research)"


def _http_json(req: urllib.request.Request, timeout: float = 25.0):
    req.add_header("User-Agent", USER_AGENT)
    req.add_header("Accept", "application/json")
    with _net_sem:
        for attempt in range(2):
            try:
                with urllib.request.urlopen(req, timeout=timeout) as r:
                    return json.loads(r.read().decode("utf-8"))
            except Exception:
                STATS["errors"] += 1
                time.sleep(1 + attempt)
    return None


def leansearch(query: str, k: int = 8) -> list[dict]:
    def fetch():
        STATS["leansearch"] += 1
        body = json.dumps({"query": [query], "num_results": k}).encode()
        req = urllib.request.Request(LEANSEARCH_URL, data=body, headers={"Content-Type": "application/json"})
        d = _http_json(req)
        if not isinstance(d, list) or not d:
            return None
        out = []
        for item in d[0]:
            r = item.get("result") or {}
            nm = r.get("name")
            nm = ".".join(nm) if isinstance(nm, list) else str(nm or "")
            out.append({"name": nm, "type": r.get("type") or "", "informal": r.get("informal_name") or ""})
        return out
    return _cached("leansearch", f"{k}\n{query}", fetch)


def loogle(query: str, k: int = 8) -> list[dict]:
    def fetch():
        STATS["loogle"] += 1
        req = urllib.request.Request(LOOGLE_URL + "?q=" + urllib.parse.quote(query))
        d = _http_json(req)
        if not isinstance(d, dict):
            return None
        if d.get("error"):
            return []
        return [{"name": h.get("name", ""), "type": h.get("type", ""), "informal": ""} for h in (d.get("hits") or [])[:k]]
    return _cached("loogle", f"{k}\n{query}", fetch)


def localize(rows: list[dict], source: str) -> list[Premise]:
    """Keep only declarations present in the local Mathlib, using the local type."""
    names._load()
    out = []
    for r in rows:
        nm = r["name"].strip()
        if nm in names._types:
            out.append(Premise(nm, names._types[nm] or r["type"].strip(), source, r.get("informal", "")))
        else:
            STATS["dropped_not_local"] += 1
    return out


def search(queries: list[str], k: int = 6, limit: int = 15) -> list[Premise]:
    """Natural-language queries go to LeanSearch; queries that look like Loogle patterns (contain a dotted
    constant name, `_`/`?` metavariables or `⊢`) go to Loogle. Results are de-duplicated and interleaved."""
    per_query: list[list[Premise]] = []
    for q in queries:
        q = q.strip()
        if not q:
            continue
        if is_loogle_query(q):
            per_query.append(localize(loogle(q, k), "loogle"))
        else:
            per_query.append(localize(leansearch(q, k), "leansearch"))
    seen: set[str] = set()
    merged: list[Premise] = []
    for rank in range(k):
        for lst in per_query:
            if rank < len(lst) and lst[rank].name not in seen:
                seen.add(lst[rank].name)
                merged.append(lst[rank])
    return merged[:limit]


def is_loogle_query(q: str) -> bool:
    return bool(re.search(r"⊢|\?[a-z]|\b_\b|^[A-Z][\w']*\.[\w'.]+(,|$)|\"", q)) or (
        "," in q and all(re.fullmatch(r"\s*[\w'.]+\s*", part) for part in q.split(",")))


def render_premises(prems: list[Premise], title: str = "Possibly useful Mathlib declarations (verified to exist):") -> str:
    if not prems:
        return ""
    return title + "\n" + "\n".join("- " + p.render() for p in prems)


QUERY_PROMPT = """You are preparing to prove a Lean 4 / Mathlib theorem. Propose search queries to find relevant Mathlib lemmas.

Theorem:
```lean
{statement}
```
{extra}
Output 3 to 5 queries, one per line, nothing else. Use two kinds:
- natural-language descriptions of a single mathematical fact you expect to need (e.g. `binomial coefficient of p*a choose p*b is congruent mod p to a choose b`);
- Loogle patterns listing Mathlib constants that must appear (e.g. `Nat.choose, Nat.ModEq` or `Polynomial.eval, Polynomial.roots`).
"""


def propose_queries(statement: str, extra: str = "", priority: int = 0) -> list[str]:
    from . import llm
    try:
        r = llm.chat([{"role": "user", "content": QUERY_PROMPT.format(statement=statement[-3000:], extra=extra)}],
                     max_tokens=400, temperature=0.3, thinking=False, priority=priority)
    except llm.LLMFailure:
        return []
    out = []
    for line in r.content.splitlines():
        line = line.strip().strip("`").lstrip("-*0123456789. ").strip().strip("`")
        if 4 <= len(line) <= 200:
            out.append(line)
    return out[:5]


SEARCH_BLOCK = re.compile(r"```search\s*\n(.*?)```", re.S)


def run_search_blocks(text: str) -> str:
    """Execute ```search blocks written by the model; return rendered results ('' if none)."""
    queries = []
    for blk in SEARCH_BLOCK.findall(text):
        queries += [l.strip() for l in blk.splitlines() if l.strip()]
    if not queries:
        return ""
    prems = search(queries[:6], k=6, limit=18)
    return render_premises(prems, "Results of your ```search queries (verified to exist in this Mathlib):") or \
        "Your ```search queries returned nothing usable."
