"""Optional pluggable embedding module (OpenAI-compatible `/v1/embeddings`, e.g. local Qwen3-Embedding-4B).

Master switch: `embedding` in `config/default.json` (or `LEMMATA_EMBEDDING=1` / CLI `--embedding`).
When disabled or when the embedding endpoint is unreachable, all callers seamlessly fall back to legacy behavior.

Sub-capabilities (individually toggleable for ablation via config or `LEMMATA_EMB_FEATURES`):
- `emb_experience`: semantic retrieval & proof-body transfer of proved lemmas and validated skeletons
- `emb_search`:     semantic reranking of Mathlib premise search + persistent local declaration pool
- `emb_names`:      semantic reranking of real Mathlib declarations for unknown/hallucinated identifiers
- `emb_repair`:     error-to-fix retrieval from verified `fail -> solved` repair pairs in earlier runs
"""
from __future__ import annotations

import difflib
import hashlib
import json
import math
import operator
import os
import re
import sqlite3
import threading
import time
import urllib.request
from array import array
from pathlib import Path

from .paths import EMBED_DB, NAMES_FILE, RUNS_DIR, SEARCH_CACHE

DEFAULT_EMBED_URL = "http://127.0.0.1:8090/v1/embeddings"

INSTRUCT_LEMMA = "Given a Lean 4 theorem statement, retrieve proved Lean 4 lemmas with analogous mathematical structure or proof techniques."
INSTRUCT_SKETCH = "Given a Lean 4 theorem statement, retrieve Lean 4 proof decomposition skeletons for similar theorems."
INSTRUCT_PREMISE = "Given a Lean 4 theorem goal or query, retrieve Mathlib declarations and lemmas needed to prove it."
INSTRUCT_IDENT = "Given a hallucinated or unknown Lean 4 identifier and its compiler error context, retrieve the real Mathlib declaration with matching meaning and type."
INSTRUCT_REPAIR = "Given a Lean 4 compiler error message and failing proof line, retrieve verified Lean 4 fixes for the same kind of error."

STATS = {
    "calls": 0,
    "texts": 0,
    "cache_hits": 0,
    "fallbacks": 0,
    "lemma_transfers": 0,
    "exp_hits": 0,
    "search_reranks": 0,
    "name_reranks": 0,
    "repair_hits": 0,
}

_db_lock = threading.RLock()
_conn: sqlite3.Connection | None = None
_mem_vecs: dict[str, array] = {}
_http_sem = threading.Semaphore(2)
_model_lock = threading.Lock()
_resolved_models: dict[str, str] = {}
_circuit_until: float = 0.0
_sync_lock = threading.Lock()
_last_sync_ts: float = 0.0


def _parse_bool_env(val: str | None) -> bool | None:
    if val is None or not val.strip():
        return None
    v = val.strip().lower()
    if v in ("1", "true", "yes", "on"):
        return True
    if v in ("0", "false", "no", "off"):
        return False
    return None


def emb_settings(cfg: dict | None = None) -> dict:
    if cfg is None:
        from .agent import runtime_config
        cfg = runtime_config()
    enabled = bool(cfg.get("embedding", False))
    env_master = _parse_bool_env(os.environ.get("LEMMATA_EMBEDDING"))
    if env_master is not None:
        enabled = env_master

    url = (os.environ.get("LEMMATA_EMBEDDING_URL") or cfg.get("embedding_url") or DEFAULT_EMBED_URL).strip()
    model = (os.environ.get("LEMMATA_EMBEDDING_MODEL") or cfg.get("embedding_model") or "").strip()

    feats = {
        "experience": bool(cfg.get("emb_experience", True)),
        "search": bool(cfg.get("emb_search", True)),
        "names": bool(cfg.get("emb_names", True)),
        "repair": bool(cfg.get("emb_repair", True)),
    }
    env_feats = (os.environ.get("LEMMATA_EMB_FEATURES") or "").strip()
    if env_feats:
        items = {x.strip().lower().removeprefix("emb_") for x in env_feats.split(",") if x.strip()}
        if "none" in items:
            feats = {k: False for k in feats}
        elif "all" in items:
            feats = {k: True for k in feats}
        else:
            feats = {k: (k in items) for k in feats}
    return {"enabled": enabled, "url": url, "model": model, "features": feats}


def emb_enabled(feature: str | None = None, cfg: dict | None = None) -> bool:
    s = emb_settings(cfg)
    if not s["enabled"]:
        return False
    if time.time() < _circuit_until:
        return False
    if feature is None:
        return True
    key = feature.removeprefix("emb_")
    return bool(s["features"].get(key, True))


def _base_root(embed_url: str) -> str:
    u = embed_url.rstrip("/")
    for suf in ("/v1/embeddings", "/embeddings"):
        if u.endswith(suf):
            return u[: -len(suf)]
    return u


def resolve_model(embed_url: str, configured_model: str = "") -> str:
    if configured_model:
        return configured_model
    with _model_lock:
        if embed_url in _resolved_models:
            return _resolved_models[embed_url]
    models_url = _base_root(embed_url) + "/v1/models"
    found = "default"
    try:
        req = urllib.request.Request(models_url, headers={"Accept": "application/json"})
        with urllib.request.urlopen(req, timeout=4.0) as r:
            data = json.loads(r.read().decode("utf-8"))
            items = data.get("data") or data.get("models") or []
            if items and isinstance(items[0], dict):
                found = str(items[0].get("id") or items[0].get("name") or "default")
    except Exception:
        pass
    with _model_lock:
        _resolved_models[embed_url] = found
    return found


def ping(embed_url: str | None = None, model: str | None = None) -> dict:
    """Check whether the embedding service is reachable and return `{ok, model, dim, latency_ms, error}`."""
    s = emb_settings()
    url = (embed_url or s["url"] or DEFAULT_EMBED_URL).strip()
    mdl = resolve_model(url, (model if model is not None else s["model"]))
    t0 = time.time()
    try:
        payload = json.dumps({"model": mdl, "input": ["theorem ping_test : True"]}).encode("utf-8")
        req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=6.0) as r:
            resp = json.loads(r.read().decode("utf-8"))
        emb = resp["data"][0]["embedding"]
        return {
            "ok": True,
            "url": url,
            "model": resp.get("model") or mdl,
            "dim": len(emb),
            "latency_ms": round((time.time() - t0) * 1000, 1),
            "error": "",
        }
    except Exception as exc:
        return {"ok": False, "url": url, "model": mdl, "dim": 0, "latency_ms": 0.0, "error": str(exc)}


# --- SQLite persistence & vector cache -----------------------------------------------------------------------------

def _db() -> sqlite3.Connection:
    global _conn
    with _db_lock:
        if _conn is None:
            EMBED_DB.parent.mkdir(parents=True, exist_ok=True)
            conn = sqlite3.connect(str(EMBED_DB), check_same_thread=False, timeout=30.0)
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS vec_cache (
                    vec_hash TEXT PRIMARY KEY,
                    model    TEXT NOT NULL,
                    dim       INTEGER NOT NULL,
                    vec      BLOB NOT NULL,
                    created  REAL NOT NULL
                );
                CREATE TABLE IF NOT EXISTS experience_items (
                    item_id     TEXT PRIMARY KEY,
                    kind        TEXT NOT NULL,
                    name        TEXT NOT NULL,
                    run_id      TEXT NOT NULL,
                    statement   TEXT NOT NULL,
                    clean_block TEXT NOT NULL,
                    helpers     TEXT NOT NULL,
                    body        TEXT NOT NULL,
                    doc_text    TEXT NOT NULL,
                    vec_hash    TEXT NOT NULL,
                    meta_json   TEXT NOT NULL,
                    created     REAL NOT NULL
                );
                CREATE INDEX IF NOT EXISTS idx_exp_kind ON experience_items(kind);
                CREATE TABLE IF NOT EXISTS decl_pool (
                    name     TEXT PRIMARY KEY,
                    type_str TEXT NOT NULL,
                    informal TEXT NOT NULL,
                    doc_text TEXT NOT NULL,
                    vec_hash TEXT NOT NULL,
                    hits     INTEGER NOT NULL DEFAULT 1,
                    updated  REAL NOT NULL
                );
                CREATE TABLE IF NOT EXISTS indexed_sources (
                    source TEXT PRIMARY KEY,
                    mtime  REAL NOT NULL
                );
                """
            )
            conn.commit()
            _conn = conn
        return _conn


def _vec_hash(model: str, text: str) -> str:
    return hashlib.sha256(f"{model}\n{text}".encode("utf-8")).hexdigest()


def _normalize(floats: list[float]) -> array:
    norm = math.sqrt(sum(map(operator.mul, floats, floats))) or 1.0
    inv = 1.0 / norm
    return array("f", (x * inv for x in floats))


def _cosine(a: array | None, b: array | None) -> float:
    if a is None or b is None or len(a) != len(b):
        return -1.0
    return float(sum(map(operator.mul, a, b)))


def _get_cached_vecs(hashes: list[str]) -> dict[str, array]:
    out: dict[str, array] = {}
    missing: list[str] = []
    for h in hashes:
        v = _mem_vecs.get(h)
        if v is not None:
            out[h] = v
        else:
            missing.append(h)
    if not missing:
        return out
    conn = _db()
    with _db_lock:
        for i in range(0, len(missing), 400):
            chunk = missing[i : i + 400]
            qmarks = ",".join("?" for _ in chunk)
            for vh, blob in conn.execute(f"SELECT vec_hash, vec FROM vec_cache WHERE vec_hash IN ({qmarks})", chunk):
                arr = array("f")
                arr.frombytes(blob)
                _mem_vecs[vh] = arr
                out[vh] = arr
    return out


def embed_texts(texts: list[str], *, instruct: str = "", batch_size: int = 16, timeout: float = 35.0) -> list[array | None]:
    """Embed `texts` (with optional Qwen3 `Instruct:` query prefix), backed by SQLite + RAM cache."""
    global _circuit_until
    if not texts:
        return []
    s = emb_settings()
    if not s["enabled"] or time.time() < _circuit_until:
        return [None] * len(texts)

    url = s["url"]
    model = resolve_model(url, s["model"])
    formatted = [
        (f"Instruct: {instruct}\nQuery: {t[:6000]}" if instruct else t[:6000])
        for t in texts
    ]
    hashes = [_vec_hash(model, ft) for ft in formatted]
    cached = _get_cached_vecs(list(dict.fromkeys(hashes)))

    to_fetch_idx: list[int] = []
    seen_missing: dict[str, int] = {}
    for idx, h in enumerate(hashes):
        if h in cached:
            STATS["cache_hits"] += 1
        elif h not in seen_missing:
            seen_missing[h] = idx
            to_fetch_idx.append(idx)

    if to_fetch_idx:
        conn = _db()
        for start in range(0, len(to_fetch_idx), batch_size):
            batch_indices = to_fetch_idx[start : start + batch_size]
            batch_inputs = [formatted[i] for i in batch_indices]
            payload = json.dumps({"model": model, "input": batch_inputs}).encode("utf-8")
            req = urllib.request.Request(url, data=payload, headers={"Content-Type": "application/json"})
            try:
                with _http_sem:
                    STATS["calls"] += 1
                    STATS["texts"] += len(batch_inputs)
                    with urllib.request.urlopen(req, timeout=timeout) as r:
                        resp = json.loads(r.read().decode("utf-8"))
                data = sorted(resp.get("data") or [], key=lambda d: d.get("index", 0))
                if len(data) != len(batch_indices):
                    raise ValueError(f"expected {len(batch_indices)} embeddings, got {len(data)}")
                now = time.time()
                batch_rows = []
                for bi, item in zip(batch_indices, data):
                    arr = _normalize(item["embedding"])
                    vh = hashes[bi]
                    cached[vh] = arr
                    _mem_vecs[vh] = arr
                    batch_rows.append((vh, model, len(arr), arr.tobytes(), now))
                with _db_lock:
                    conn.executemany(
                        "INSERT OR REPLACE INTO vec_cache(vec_hash, model, dim, vec, created) VALUES (?, ?, ?, ?, ?)",
                        batch_rows,
                    )
                    conn.commit()
            except Exception:
                STATS["fallbacks"] += 1
                _circuit_until = time.time() + 30.0
                break

    return [cached.get(h) for h in hashes]


def embed_one(text: str, *, instruct: str = "") -> array | None:
    res = embed_texts([text], instruct=instruct)
    return res[0] if res else None


# --- Incremental Experience Indexing (Lemmas, Skeletons, Repairs) --------------------------------------------------

def _clean_error_core(feedback: str) -> str:
    """Strip appended Name hints / search blocks from compiler feedback so we embed the core Lean error."""
    core = feedback.split("\n\nName hints (")[0]
    core = core.split("\n\nMathlib search for")[0]
    core = core.split("\n\nResults of your ```search")[0]
    return core.strip()[:1200]


def _extract_diff_snippet(bad_block: str, good_block: str, max_chars: int = 650) -> str:
    bad_lines = [l.rstrip() for l in bad_block.strip().splitlines()]
    good_lines = [l.rstrip() for l in good_block.strip().splitlines()]
    diff = list(difflib.unified_diff(bad_lines, good_lines, lineterm="", n=1))
    if not diff:
        return good_block.strip()[:max_chars]
    body = "\n".join(l for l in diff[2:] if not l.startswith("@@"))
    return (body.strip() or good_block.strip())[:max_chars]


def record_solved_lemma(problem, cand, *, run_id: str = "live", source: str = "") -> None:
    """Index a newly proved theorem/sub-lemma into the experience vector store."""
    if not emb_enabled("experience"):
        return
    from .problem import candidate_block
    cblock = candidate_block(problem, cand)
    stmt = (problem.statement or "").strip()
    if not stmt or not cblock:
        return
    doc_parts = []
    if getattr(problem, "informal", ""):
        doc_parts.append(problem.informal[:400])
    doc_parts.append(stmt)
    doc_text = "\n".join(doc_parts)[:3000]
    vec = embed_one(doc_text)
    if vec is None:
        return
    s = emb_settings()
    model = resolve_model(s["url"], s["model"])
    vh = _vec_hash(model, doc_text[:6000])
    item_id = "lemma:" + hashlib.sha256((stmt + "\n" + cblock).encode("utf-8")).hexdigest()[:24]
    conn = _db()
    with _db_lock:
        conn.execute(
            """INSERT OR REPLACE INTO experience_items
               (item_id, kind, name, run_id, statement, clean_block, helpers, body, doc_text, vec_hash, meta_json, created)
               VALUES (?, 'lemma', ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (item_id, problem.name, run_id, stmt, cblock, cand.helpers or "", cand.body or "",
             doc_text, vh, json.dumps({"source": source}), time.time()),
        )
        conn.commit()


def record_valid_skeleton(problem, clean_block: str, lemma_names: list[str], *,
                          tree_solved: bool = False, run_id: str = "live", source: str = "") -> None:
    if not emb_enabled("experience"):
        return
    stmt = (problem.statement or "").strip()
    if not stmt or not clean_block.strip():
        return
    doc_text = ((problem.informal[:400] + "\n") if getattr(problem, "informal", "") else "") + stmt
    vec = embed_one(doc_text)
    if vec is None:
        return
    s = emb_settings()
    model = resolve_model(s["url"], s["model"])
    vh = _vec_hash(model, doc_text[:6000])
    item_id = "skel:" + hashlib.sha256((stmt + "\n" + clean_block).encode("utf-8")).hexdigest()[:24]
    conn = _db()
    with _db_lock:
        conn.execute(
            """INSERT OR REPLACE INTO experience_items
               (item_id, kind, name, run_id, statement, clean_block, helpers, body, doc_text, vec_hash, meta_json, created)
               VALUES (?, 'skeleton', ?, ?, ?, ?, '', '', ?, ?, ?, ?)""",
            (item_id, problem.name, run_id, stmt, clean_block.strip(), doc_text, vh,
             json.dumps({"lemmas": lemma_names, "tree_solved": tree_solved, "source": source}), time.time()),
        )
        conn.commit()


def record_verified_repair(problem_name: str, statement: str, bad_feedback: str, bad_block: str, good_block: str, *,
                           run_id: str = "live", source: str = "") -> None:
    if not emb_enabled("repair"):
        return
    err_core = _clean_error_core(bad_feedback)
    if not err_core or not good_block.strip() or bad_block.strip() == good_block.strip():
        return
    diff_txt = _extract_diff_snippet(bad_block, good_block)
    doc_text = f"Goal: {statement[:400]}\nCompiler error:\n{err_core}"[:2500]
    vec = embed_one(doc_text)
    if vec is None:
        return
    s = emb_settings()
    model = resolve_model(s["url"], s["model"])
    vh = _vec_hash(model, doc_text[:6000])
    item_id = "rep:" + hashlib.sha256((err_core + "\n" + diff_txt).encode("utf-8")).hexdigest()[:24]
    conn = _db()
    with _db_lock:
        conn.execute(
            """INSERT OR REPLACE INTO experience_items
               (item_id, kind, name, run_id, statement, clean_block, helpers, body, doc_text, vec_hash, meta_json, created)
               VALUES (?, 'repair', ?, ?, ?, ?, '', '', ?, ?, ?, ?)""",
            (item_id, problem_name, run_id, err_core[:800], diff_txt, doc_text, vh,
             json.dumps({"source": source}), time.time()),
        )
        conn.commit()


def sync_experience_index(*, max_new_items: int = 260) -> int:
    """Incrementally scan historical `runs/` (skipping `selftest`) and index unindexed proofs, skeletons, and repairs."""
    global _last_sync_ts
    if not emb_enabled():
        return 0
    if time.time() - _last_sync_ts < 20.0:
        return 0
    with _sync_lock:
        if time.time() - _last_sync_ts < 20.0:
            return 0
        _last_sync_ts = time.time()
        if not RUNS_DIR.exists():
            return 0

        from .problem import Problem, candidate_block, prune_unused, split_full_code
        from .decompose import parse_skeleton

        conn = _db()
        with _db_lock:
            known_sources = dict(conn.execute("SELECT source, mtime FROM indexed_sources").fetchall())

        pending_entries: list[tuple[str, str, str, str, str, str, str, str, str, dict]] = []
        touched_sources: list[tuple[str, float]] = []

        for pj in sorted(RUNS_DIR.rglob("problem.json")):
            if "selftest" in pj.parts:
                continue
            node_dir = pj.parent
            try:
                rel = pj.relative_to(RUNS_DIR)
                run_id = rel.parts[0]
            except ValueError:
                run_id = "runs"

            try:
                prob = Problem(**json.loads(pj.read_text(encoding="utf-8")))
            except Exception:
                continue

            # 1. Proved lemma / theorem
            pf = node_dir / "proof.lean"
            if pf.exists():
                sk_src = str(pf)
                mtime = pf.stat().st_mtime
                if known_sources.get(sk_src) != mtime:
                    code = pf.read_text(encoding="utf-8", errors="replace")
                    cand = split_full_code(prob, code.split("#print axioms")[0])
                    if cand is not None:
                        cand = prune_unused(cand)
                        cblock = candidate_block(prob, cand)
                        stmt = prob.statement.strip()
                        doc_text = ((prob.informal[:400] + "\n") if prob.informal else "") + stmt
                        iid = "lemma:" + hashlib.sha256((stmt + "\n" + cblock).encode("utf-8")).hexdigest()[:24]
                        pending_entries.append((iid, "lemma", prob.name, run_id, stmt, cblock,
                                                cand.helpers, cand.body, doc_text[:3000], {"source": sk_src}))
                    touched_sources.append((sk_src, mtime))

            # 2. Validated skeletons
            for sj in sorted(node_dir.glob("sketch_*/skeletons.jsonl")):
                sk_src = str(sj)
                mtime = sj.stat().st_mtime
                if known_sources.get(sk_src) != mtime:
                    asm = sj.parent / "assembly.json"
                    tree_ok = False
                    if asm.exists():
                        try:
                            tree_ok = bool(json.loads(asm.read_text(encoding="utf-8")).get("solved"))
                        except Exception:
                            tree_ok = False
                    for line in sj.read_text(encoding="utf-8", errors="replace").splitlines():
                        try:
                            srow = json.loads(line)
                        except ValueError:
                            continue
                        if not srow.get("ok") or srow.get("round") in ("resumed", "harvested"):
                            continue
                        sk = parse_skeleton(prob, srow.get("content") or "")
                        if sk is None or not sk.lemmas:
                            continue
                        if re.search(r"\bsorry\b", re.sub(r"--[^\n]*", "", sk.candidate.body)):
                            continue
                        cblock = srow.get("clean_block") or candidate_block(prob, sk.candidate)
                        stmt = prob.statement.strip()
                        doc_text = ((prob.informal[:400] + "\n") if prob.informal else "") + stmt
                        iid = "skel:" + hashlib.sha256((stmt + "\n" + cblock).encode("utf-8")).hexdigest()[:24]
                        pending_entries.append((iid, "skeleton", prob.name, run_id, stmt, cblock, "", "",
                                                doc_text[:3000],
                                                {"lemmas": [n for n, _ in sk.lemmas], "tree_solved": tree_ok, "source": sk_src}))
                    touched_sources.append((sk_src, mtime))

            # 3. Verified repair transitions (`fail -> solved` on same node)
            aj = node_dir / "attempts.jsonl"
            if aj.exists() and pf.exists():
                aj_src = str(aj)
                mtime = aj.stat().st_mtime
                if known_sources.get(aj_src) != mtime:
                    rows = []
                    for line in aj.read_text(encoding="utf-8", errors="replace").splitlines():
                        try:
                            rows.append(json.loads(line))
                        except ValueError:
                            continue
                    wins = [r for r in rows if r.get("solved") and r.get("code")]
                    fails = [r for r in rows if not r.get("solved") and r.get("code") and r.get("feedback")]
                    if wins and fails:
                        w0 = wins[0]
                        f0 = fails[-1]
                        w_cand = split_full_code(prob, w0["code"].split("#print axioms")[0])
                        f_cand = split_full_code(prob, f0["code"].split("#print axioms")[0])
                        if w_cand is not None and f_cand is not None:
                            good_blk = w0.get("clean_block") or candidate_block(prob, prune_unused(w_cand))
                            bad_blk = f0.get("clean_block") or candidate_block(prob, f_cand)
                            err_core = _clean_error_core(f0["feedback"])
                            if err_core and good_blk and bad_blk != good_blk:
                                diff_txt = _extract_diff_snippet(bad_blk, good_blk)
                                doc_text = f"Goal: {prob.statement[:400]}\nCompiler error:\n{err_core}"[:2500]
                                iid = "rep:" + hashlib.sha256((err_core + "\n" + diff_txt).encode("utf-8")).hexdigest()[:24]
                                pending_entries.append((iid, "repair", prob.name, run_id, err_core[:800], diff_txt,
                                                        "", "", doc_text, {"source": aj_src}))
                    touched_sources.append((aj_src, mtime))

            if len(pending_entries) >= max_new_items:
                break

        if not pending_entries and not touched_sources:
            return 0

        # Deduplicate pending_entries by item_id
        dedup: dict[str, tuple] = {}
        for item in pending_entries:
            dedup[item[0]] = item
        unique_items = list(dedup.values())

        added = 0
        if unique_items:
            docs = [it[8] for it in unique_items]
            vecs = embed_texts(docs)
            s = emb_settings()
            model = resolve_model(s["url"], s["model"])
            now = time.time()
            db_rows = []
            for it, v in zip(unique_items, vecs):
                if v is None:
                    continue
                iid, kind, name, run_id, stmt, cblock, helpers, body, doc_text, meta = it
                vh = _vec_hash(model, doc_text[:6000])
                db_rows.append((iid, kind, name, run_id, stmt, cblock, helpers, body, doc_text, vh,
                                json.dumps(meta, ensure_ascii=False), now))
            if db_rows:
                with _db_lock:
                    conn.executemany(
                        """INSERT OR REPLACE INTO experience_items
                           (item_id, kind, name, run_id, statement, clean_block, helpers, body, doc_text, vec_hash, meta_json, created)
                           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                        db_rows,
                    )
                    added = len(db_rows)
                    if len(db_rows) == len(unique_items) and touched_sources:
                        conn.executemany("INSERT OR REPLACE INTO indexed_sources(source, mtime) VALUES (?, ?)", touched_sources)
                    conn.commit()
        elif touched_sources:
            with _db_lock:
                conn.executemany("INSERT OR REPLACE INTO indexed_sources(source, mtime) VALUES (?, ?)", touched_sources)
                conn.commit()
        return added


# --- Capability 1: Experience Retrieval (Lemmas & Skeletons) -------------------------------------------------------

def retrieve_lemmas(problem, *, k: int = 3, min_score: float = 0.62,
                    exclude_name: str = "", exclude_runs: set[str] | None = None,
                    max_block_chars: int = 1500) -> list[dict]:
    if not emb_enabled("experience"):
        return []
    sync_experience_index()
    q_text = ((problem.informal[:400] + "\n") if getattr(problem, "informal", "") else "") + problem.statement.strip()
    q_vec = embed_one(q_text, instruct=INSTRUCT_LEMMA)
    if q_vec is None:
        return []
    conn = _db()
    with _db_lock:
        rows = conn.execute(
            "SELECT name, run_id, statement, clean_block, helpers, body, vec_hash FROM experience_items WHERE kind = 'lemma'"
        ).fetchall()
    if not rows:
        return []
    vmap = _get_cached_vecs(list({r[6] for r in rows}))
    scored: list[tuple[float, dict]] = []
    seen_stmt: set[str] = set()
    for name, run_id, stmt, cblock, helpers, body, vh in rows:
        if exclude_name and name == exclude_name:
            continue
        if exclude_runs and run_id in exclude_runs:
            continue
        if max_block_chars and len(cblock) > max_block_chars:
            continue
        norm_stmt = re.sub(r"\s+", " ", stmt).strip()
        if norm_stmt in seen_stmt:
            continue
        sim = _cosine(q_vec, vmap.get(vh))
        if sim >= min_score:
            seen_stmt.add(norm_stmt)
            scored.append((sim, {
                "score": round(sim, 4),
                "name": name,
                "run_id": run_id,
                "statement": stmt,
                "clean_block": cblock,
                "helpers": helpers,
                "body": body,
            }))
    scored.sort(key=lambda x: x[0], reverse=True)
    out = [d for _, d in scored[:k]]
    if out:
        STATS["exp_hits"] += 1
    return out


def render_lemma_hints(items: list[dict]) -> str:
    if not items:
        return ""
    blocks = ["Similar verified proofs from earlier runs (adapt names/types as needed; do not copy blindly):"]
    for it in items:
        blocks.append(f"```lean\n{it['clean_block']}\n```")
    return "\n\n".join(blocks)


def retrieve_skeletons(problem, *, k: int = 1, min_score: float = 0.64,
                       exclude_name: str = "", exclude_runs: set[str] | None = None,
                       max_block_chars: int = 1800) -> list[dict]:
    if not emb_enabled("experience"):
        return []
    sync_experience_index()
    q_text = ((problem.informal[:400] + "\n") if getattr(problem, "informal", "") else "") + problem.statement.strip()
    q_vec = embed_one(q_text, instruct=INSTRUCT_SKETCH)
    if q_vec is None:
        return []
    conn = _db()
    with _db_lock:
        rows = conn.execute(
            "SELECT name, run_id, statement, clean_block, vec_hash, meta_json FROM experience_items WHERE kind = 'skeleton'"
        ).fetchall()
    if not rows:
        return []
    vmap = _get_cached_vecs(list({r[4] for r in rows}))
    scored: list[tuple[float, dict]] = []
    seen_blk: set[str] = set()
    for name, run_id, stmt, cblock, vh, meta_s in rows:
        if exclude_name and name == exclude_name:
            continue
        if exclude_runs and run_id in exclude_runs:
            continue
        if max_block_chars and len(cblock) > max_block_chars:
            continue
        sig = re.sub(r"\s+", " ", cblock).strip()
        if sig in seen_blk:
            continue
        sim = _cosine(q_vec, vmap.get(vh))
        if sim < min_score:
            continue
        try:
            meta = json.loads(meta_s)
        except ValueError:
            meta = {}
        # Slight bonus for skeletons whose entire sub-tree was verified solved
        rank_score = sim + (0.03 if meta.get("tree_solved") else 0.0)
        seen_blk.add(sig)
        scored.append((rank_score, {"score": round(sim, 4), "name": name, "clean_block": cblock, "meta": meta}))
    scored.sort(key=lambda x: x[0], reverse=True)
    out = [d for _, d in scored[:k]]
    if out:
        STATS["exp_hits"] += 1
    return out


# --- Capability 2: Semantic Premise Reranking & Local Declaration Pool ---------------------------------------------

def _decl_doc(name: str, type_str: str, informal: str = "") -> str:
    base = f"{name} : {type_str[:360]}"
    if informal:
        base += f" -- {informal[:200]}"
    return base


def _upsert_decls(decls: list[tuple[str, str, str]], *, max_new_embeds: int = 24) -> dict[str, array]:
    """Ensure up to `max_new_embeds` declarations are embedded and saved in `decl_pool`; return `{name: vec}`."""
    if not decls:
        return {}
    s = emb_settings()
    model = resolve_model(s["url"], s["model"])
    docs = [(nm, ty, inf, _decl_doc(nm, ty, inf)) for nm, ty, inf in decls if nm]
    hashes = [_vec_hash(model, d[3][:6000]) for d in docs]
    vmap = _get_cached_vecs(list(dict.fromkeys(hashes)))

    missing_docs: list[tuple[str, str, str, str, str]] = []
    for (nm, ty, inf, doc), vh in zip(docs, hashes):
        if vh not in vmap and len(missing_docs) < max_new_embeds:
            missing_docs.append((nm, ty, inf, doc, vh))

    if missing_docs:
        vecs = embed_texts([m[3] for m in missing_docs])
        now = time.time()
        pool_rows = []
        for (nm, ty, inf, doc, vh), v in zip(missing_docs, vecs):
            if v is not None:
                vmap[vh] = v
                pool_rows.append((nm, ty[:500], inf[:300], doc, vh, now))
        if pool_rows:
            conn = _db()
            with _db_lock:
                conn.executemany(
                    """INSERT INTO decl_pool(name, type_str, informal, doc_text, vec_hash, hits, updated)
                       VALUES (?, ?, ?, ?, ?, 1, ?)
                       ON CONFLICT(name) DO UPDATE SET
                           vec_hash=excluded.vec_hash, hits=decl_pool.hits + 1, updated=excluded.updated""",
                    pool_rows,
                )
                conn.commit()

    # Also ensure already-cached declarations are registered in decl_pool so the local pool grows passively
    existing_rows = []
    now = time.time()
    for (nm, ty, inf, doc), vh in zip(docs, hashes):
        if vh in vmap:
            existing_rows.append((nm, ty[:500], inf[:300], doc, vh, now))
    if existing_rows:
        conn = _db()
        with _db_lock:
            conn.executemany(
                """INSERT OR IGNORE INTO decl_pool(name, type_str, informal, doc_text, vec_hash, hits, updated)
                   VALUES (?, ?, ?, ?, ?, 1, ?)""",
                existing_rows,
            )
            conn.commit()

    return {nm: vmap[vh] for (nm, _, _, _), vh in zip(docs, hashes) if vh in vmap}


def search_local_pool(query_context: str, *, k: int = 8, min_score: float = 0.52) -> list[tuple[str, str, str, float]]:
    """Retrieve `(name, type_str, informal, score)` from the persistent local Mathlib declaration vector pool."""
    if not emb_enabled("search") or not query_context.strip():
        return []
    q_vec = embed_one(query_context[:2500], instruct=INSTRUCT_PREMISE)
    if q_vec is None:
        return []
    conn = _db()
    with _db_lock:
        rows = conn.execute("SELECT name, type_str, informal, vec_hash FROM decl_pool").fetchall()
    if not rows:
        return []
    vmap = _get_cached_vecs(list({r[3] for r in rows}))
    scored = []
    for nm, ty, inf, vh in rows:
        sim = _cosine(q_vec, vmap.get(vh))
        if sim >= min_score:
            scored.append((sim, nm, ty, inf))
    scored.sort(key=lambda x: x[0], reverse=True)
    return [(nm, ty, inf, sim) for sim, nm, ty, inf in scored[:k]]


def rerank_premises(query_context: str, premises: list, *, limit: int = 15,
                    include_local_pool: bool = True) -> list:
    """Semantically rerank `Premise` candidates against `query_context` and augment from local declaration pool."""
    if not emb_enabled("search") or not query_context.strip():
        return premises[:limit]
    from .search import Premise
    from . import names

    q_vec = embed_one(query_context[:2500], instruct=INSTRUCT_PREMISE)
    if q_vec is None:
        return premises[:limit]

    by_name: dict[str, tuple[int, object]] = {}
    for rank, p in enumerate(premises):
        if p.name not in by_name:
            by_name[p.name] = (rank, p)

    if include_local_pool and len(by_name) < limit:
        names._load()
        need = limit - len(by_name) + 4
        for nm, ty, inf, _ in search_local_pool(query_context, k=need, min_score=0.60):
            if nm not in by_name and (not names._types or nm in names._types):
                real_ty = names._types.get(nm, ty) if names._types else ty
                by_name[nm] = (len(premises) + 4, Premise(nm, real_ty, "local_emb", inf))

    if not by_name:
        return []

    decl_tuples = [(p.name, p.type, getattr(p, "informal", "")) for _, p in by_name.values()]
    vec_by_name = _upsert_decls(decl_tuples, max_new_embeds=40)
    if not vec_by_name:
        return premises[:limit]

    scored: list[tuple[float, object]] = []
    for nm, (orig_rank, p) in by_name.items():
        v = vec_by_name.get(nm)
        rr_prior = 1.0 / (4.0 + orig_rank)  # gentle rank prior keeps exact Loogle top-1 grounded
        if v is not None:
            sim = _cosine(q_vec, v)
            hybrid = 0.78 * sim + 0.22 * (rr_prior * 4.0)
        else:
            hybrid = 0.52 + 0.22 * (rr_prior * 4.0)
        scored.append((hybrid, p))

    scored.sort(key=lambda x: x[0], reverse=True)
    STATS["search_reranks"] += 1
    return [p for _, p in scored[:limit]]


# --- Capability 3: Semantic Identifier Grounding (`names.py`) ------------------------------------------------------

def rerank_identifiers(ident: str, error_context: str, candidates: list[tuple[str, str]], *, k: int = 6) -> list[str]:
    """Rerank `(real_name, real_type)` Mathlib candidates for unknown `ident` using semantic + lexical hybrid score."""
    if not emb_enabled("names") or len(candidates) <= 1:
        return [nm for nm, _ in candidates[:k]]

    q_str = f"Unknown identifier: {ident}"
    if error_context.strip():
        q_str += f"\nLean error context:\n{error_context.strip()[:900]}"
    q_vec = embed_one(q_str, instruct=INSTRUCT_IDENT)
    if q_vec is None:
        return [nm for nm, _ in candidates[:k]]

    decl_tuples = [(nm, ty, "") for nm, ty in candidates[:24]]
    vec_by_name = _upsert_decls(decl_tuples, max_new_embeds=24)
    if not vec_by_name:
        return [nm for nm, _ in candidates[:k]]

    ident_low = ident.lower()
    ident_last = ident.rsplit(".", 1)[-1].lower()
    scored: list[tuple[float, str]] = []
    for idx, (nm, _) in enumerate(candidates[:24]):
        lex = difflib.SequenceMatcher(None, ident_low, nm.lower()).ratio()
        if nm.rsplit(".", 1)[-1].lower() == ident_last:
            lex = min(1.0, lex + 0.20)
        v = vec_by_name.get(nm)
        if v is not None:
            sim = _cosine(q_vec, v)
            score = 0.72 * sim + 0.28 * lex
        else:
            score = 0.40 * lex - 0.01 * idx
        scored.append((score, nm))

    scored.sort(key=lambda x: x[0], reverse=True)
    STATS["name_reranks"] += 1
    return [nm for _, nm in scored[:k]]


# --- Capability 4: Error-to-Fix Repair Memory ----------------------------------------------------------------------

def _error_kind(err_txt: str) -> str:
    low = err_txt.lower()
    if "unknown identifier" in low or "unknown constant" in low or "does not contain" in low:
        return "unknown_ident"
    if "type mismatch" in low:
        return "type_mismatch"
    if "unsolved goals" in low:
        return "unsolved_goals"
    if "failed to synthesize" in low:
        return "synth_instance"
    if "tactic" in low and "failed" in low:
        return "tactic_failed"
    return "other"


def retrieve_repairs(feedback: str, goal_statement: str = "", *, k: int = 2, min_score: float = 0.74,
                     exclude_name: str = "", exclude_runs: set[str] | None = None) -> list[dict]:
    if not emb_enabled("repair"):
        return []
    err_core = _clean_error_core(feedback)
    if not err_core:
        return []
    q_kind = _error_kind(err_core)
    sync_experience_index()
    q_text = (f"Goal: {goal_statement[:400]}\n" if goal_statement else "") + f"Compiler error:\n{err_core}"
    q_vec = embed_one(q_text[:2500], instruct=INSTRUCT_REPAIR)
    if q_vec is None:
        return []
    conn = _db()
    with _db_lock:
        rows = conn.execute(
            "SELECT name, run_id, statement, clean_block, vec_hash FROM experience_items WHERE kind = 'repair'"
        ).fetchall()
    if not rows:
        return []
    vmap = _get_cached_vecs(list({r[4] for r in rows}))
    scored: list[tuple[float, dict]] = []
    seen_diff: set[str] = set()
    for name, run_id, err_stmt, diff_blk, vh in rows:
        if exclude_name and name == exclude_name:
            continue
        if exclude_runs and run_id in exclude_runs:
            continue
        if q_kind != "other" and _error_kind(err_stmt) != q_kind:
            continue
        sig = re.sub(r"\s+", " ", diff_blk).strip()
        if sig in seen_diff:
            continue
        sim = _cosine(q_vec, vmap.get(vh))
        if sim >= min_score:
            seen_diff.add(sig)
            scored.append((sim, {
                "score": round(sim, 4),
                "name": name,
                "error": err_stmt[:320],
                "diff": diff_blk[:550],
            }))
    scored.sort(key=lambda x: x[0], reverse=True)
    out = [d for _, d in scored[:k]]
    if out:
        STATS["repair_hits"] += 1
    return out


def render_repair_hints(items: list[dict]) -> str:
    if not items:
        return ""
    lines = ["\n\nVerified fixes for similar Lean compiler errors in earlier runs (pattern reference only):"]
    for it in items:
        err_one = " ".join(it["error"].splitlines()[:2])[:220]
        lines.append(f"- Similar error: `{err_one}`\n  Diff that fixed it:\n```diff\n{it['diff']}\n```")
    return "\n".join(lines)
