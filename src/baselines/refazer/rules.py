"""The original Refazer (Rolim et al., ICSE 2017) as a rule source for src.core.repair.

``tools_refazer/<pid>/refazer/`` holds one learned transformation per worked pair
(``<k>.json``, written by ``Refazer.exe learn``) and ``learn_log.json``. Each
transformation becomes ``Rule("refazer_<k>")``, whose ``apply`` asks a
``Refazer.exe serve`` process for every program Refazer's ``Apply`` returns.
One server per Python process (restarted after a fork, a crash or a switch to
another tool dir), started on first use; build it with ``build.sh``.

Replies are cached in ``<tool_dir>/apply_cache.sqlite`` by (rule, source hash).
The search's frontier depends only on T, so both builders' runs (and shards of
one run) request the same applies; the cache serves the second from the first
and makes a timed-out apply read back the same way in every run.
"""
from __future__ import annotations

import hashlib
import json
import os
import sqlite3
import subprocess
import threading
from pathlib import Path

from src.core.repair import Rule

EXE = Path(__file__).resolve().parent / "build" / "Refazer.exe"
APPLY_TIMEOUT = 5.0     # seconds per request, enforced inside the server


class _Server:
    def __init__(self):
        self.proc = self.tool_dir = self.pid = None
        self.seq = 0
        self.lock = threading.Lock()

    def _kill(self):
        if self.proc is not None and self.pid == os.getpid():
            self.proc.kill()
            self.proc.wait()
        self.proc = None

    def _start(self, tool_dir: str):
        self._kill()
        self.proc = subprocess.Popen(
            ["mono", str(EXE), "serve", tool_dir, str(APPLY_TIMEOUT)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            text=True, encoding="utf-8", bufsize=1)
        self.tool_dir, self.pid = tool_dir, os.getpid()

    def apply(self, tool_dir: str, k: int, source: str) -> list[str]:
        with self.lock:
            if (self.proc is None or self.pid != os.getpid() or self.tool_dir != tool_dir
                    or self.proc.poll() is not None):
                self._start(tool_dir)
            self.seq += 1
            seq = self.seq
            try:
                self.proc.stdin.write(json.dumps({"rule": k, "source": source, "seq": seq}) + "\n")
                self.proc.stdin.flush()
                reply = json.loads(self.proc.stdout.readline() or "null")
                if reply is None or reply.get("seq") != seq:   # died on this input, or out of step
                    self._kill()
                    return []
                return reply["outputs"]
            except (OSError, ValueError):        # broken pipe, or a malformed reply
                self._kill()
                return []
            except BaseException:                # the caller's alarm (repair.RULE_APPLY_TIMEOUT)
                # Restart rather than let the server finish an abandoned request
                # while the next one waits behind it (and times out in turn).
                self._kill()
                raise


_SERVER = _Server()
_DB: dict = {}
_DB_LOCK = threading.Lock()


def _cached_apply(tool_dir: str, k: int, source: str) -> list[str]:
    h = hashlib.sha256(source.encode()).hexdigest()
    with _DB_LOCK:
        con = _DB.get((tool_dir, os.getpid()))
        if con is None:
            con = sqlite3.connect(Path(tool_dir) / "apply_cache.sqlite", timeout=120,
                                  check_same_thread=False)
            con.execute("PRAGMA journal_mode=WAL")
            con.execute("CREATE TABLE IF NOT EXISTS apply "
                        "(rule INTEGER, src TEXT, outputs TEXT, PRIMARY KEY (rule, src))")
            _DB[(tool_dir, os.getpid())] = con
        row = con.execute("SELECT outputs FROM apply WHERE rule=? AND src=?", (k, h)).fetchone()
    if row:
        return json.loads(row[0])
    out = _SERVER.apply(tool_dir, k, source)
    with _DB_LOCK:
        con.execute("INSERT OR REPLACE INTO apply VALUES (?,?,?)", (k, h, json.dumps(out)))
        con.commit()
    return out


def load_refazer_rules(tool_dir) -> list[Rule]:
    """One Rule per transformation ``learn`` produced in ``tool_dir``."""
    tool_dir = str(Path(tool_dir).resolve())
    log = json.loads((Path(tool_dir) / "learn_log.json").read_text())
    rules = []
    for rec in log:
        if rec["ok"]:
            k = int(rec["id"])
            # local=True: a Refazer transformation may edit several sites by design.
            # total=True: the server bounds every request at 5 s itself, as the engine
            # bounds a rule-language rule, so the search's 2 s alarm is not needed.
            rules.append(Rule(name=f"refazer_{k}", local=True, total=True,
                              apply=lambda src, k=k: _cached_apply(tool_dir, k, src)))
    return rules
