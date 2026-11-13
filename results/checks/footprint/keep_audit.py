"""Keep on the real rules: every rule of the 106 tools and the always-on rules applied to every buggy program of its
assignment. `refused` counts candidates Keep refuses; `differ` counts candidates that differ from the engine that
tested Keep only where a metavariable omitted or moved binding code (rulelang_skip.py), so a zero means no stored
result of a first application moves.
    python3 -I keep_audit.py REPO   -> keep_audit.txt"""
import glob, importlib.util, signal, sys
from collections import Counter
from multiprocessing import Pool
from pathlib import Path
REPO = Path(sys.argv[1]); sys.path[:0] = [str(REPO), str(Path(__file__).resolve().parent)]
from src.core import rulelang as L                 # noqa: E402
from src.core.generic_rules import GENERIC_LANG    # noqa: E402
spec = importlib.util.spec_from_file_location("rulelang_skip", Path(__file__).resolve().parent / "rulelang_skip.py")
O = importlib.util.module_from_spec(spec); sys.modules["rulelang_skip"] = O; spec.loader.exec_module(O)
SEEN = Counter(); keeps = L._keeps_scope


def counted(*a):
    ok = keeps(*a)
    SEEN["refused"] += not ok
    return ok


L._keeps_scope = counted


def job(f):
    pid, model = Path(f).parts[-3], Path(f).parts[-2]
    progs = [g.read_text() for g in sorted((REPO / "benchmark" / pid / "buggy").glob("*.py"))]
    assert progs, f
    c = Counter(); ex = []
    text = Path(f).read_text()
    if f.startswith(str(REPO / "tools" / pid)) and model == "claude-sonnet-5":   # once per assignment
        text += "\n" + GENERIC_LANG
    for r, o in zip(L.compile_rules(text)[0], O.compile_rules(text)[0]):
        assert r.name == o.name
        c["rules"] += 1
        if L.effect(r)[1]:
            c["kind"] += 1
            continue
        for src in progs:
            signal.alarm(20)
            SEEN.clear()
            try:
                a, b = r.apply(src), o.apply(src)
            except Exception:                      # noqa: BLE001 - a rule that abstains on this program
                c["raised"] += 1
                continue
            finally:
                signal.alarm(0)
            c["applications"] += 1; c["candidates"] += len(a); c["refused"] += SEEN["refused"]
            c["differ"] += len(set(a) ^ set(b))
            if set(a) ^ set(b) and len(ex) < 3:
                ex.append((f, r.name))
            if SEEN["refused"]:
                c["refused@" + f.split("/tools/")[-1].split("/splits_work/")[-1] + "#" + r.name] += SEEN["refused"]
    return c, ex


if __name__ == "__main__":
    files = sorted(glob.glob(str(REPO / "tools/*/*/fixer.rules")) + glob.glob(str(REPO / "tools/rebuild/r*/*/*/fixer.rules"))
                   + glob.glob(str(REPO / "splits_work/tools/s*/f10/*/*/fixer.rules")))
    with Pool(10) as pool:
        got = pool.map(job, files, chunksize=1)
    tot = Counter(); ex = []
    for c, e in got:
        tot.update(c); ex += e
    out = [f"{len(files)} tools: {dict(tot)}", f"examples: {ex[:6]}"]
    print("\n".join(out)); (Path(__file__).resolve().parent / "keep_audit.txt").write_text("\n".join(out) + "\n")
