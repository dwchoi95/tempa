"""Random programs on sets of ints, floats, tuples and None, printing the sets'
iteration order after every operation; compares the Lean interpreter with CPython.
python3 -I setfuzz.py N SEED"""
import json, random, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent / "lean_cls"))
from difftest import job, cpython   # noqa

def elem(r):
    k = r.randrange(10)
    if k < 5: return str(r.randrange(-20, 60))
    if k < 6: return str(r.choice([2**61, 2**62 + 3, -2**61 + 1, 10**20, -1, -2, 2**61 - 1]))
    if k < 7: return repr(r.choice([0.5, 1.5, -2.25, 3.0, 1e-3, 1e100]))
    if k < 8: return "(%d, %d)" % (r.randrange(5), r.randrange(5))
    if k < 9: return "None"
    return str(r.randrange(1000))

def prog(r):
    L = ["a = {%s}" % ", ".join(elem(r) for _ in range(r.randrange(0, 12))),
         "b = set([%s])" % ", ".join(elem(r) for _ in range(r.randrange(0, 12)))]
    for _ in range(r.randrange(3, 12)):
        op = r.randrange(16)
        v = r.choice("ab")
        w = "b" if v == "a" else "a"
        L.append({0: f"{v}.add({elem(r)})", 1: f"{v}.discard({elem(r)})", 2: f"{v} = {v} | {w}",
                  3: f"{v} = {v} & {w}", 4: f"{v} = {v} - {w}", 5: f"{v} = {v} ^ {w}",
                  6: f"{v}.update([{', '.join(elem(r) for _ in range(r.randrange(5)))}])",
                  7: f"{v} = {v}.copy()", 8: f"{v} = set({v})", 9: f"{v}.pop() if {v} else None",
                  10: f"{v} |= {w}", 11: f"{v} &= {w}", 12: f"{v} -= {w}", 13: f"{v} ^= {w}",
                  14: f"{v} = {{x for x in {v}}}", 15: f"{v} = {v}.union({w}, [{elem(r)}])"}[op])
        L.append("print(list(a), list(b))")
    return "\n".join(L) + "\n"

n, seed = int(sys.argv[1]), int(sys.argv[2])
r = random.Random(seed)
srcs = [prog(r) for _ in range(n)]
jobs = [job(s, "", "stdio", [{"stdin": ""}], 1000000) for s in srcs]
p = subprocess.run([str(HERE.parents[2] / "mech/.lake/build/bin/pycore"), "run", "/dev/stdin"], input="\n".join(jobs),
                   capture_output=True, text=True)
outs = [json.loads(l) for l in p.stdout.splitlines() if l.startswith("{")]
bad = 0
for src, ln in zip(srcs, outs):
    py = cpython(src, "", "stdio", [{"stdin": ""}])[0]
    if (py.get("out"), py.get("exc")) != (ln.get("out"), ln.get("exc")):
        bad += 1
        if bad <= 2:
            sys.stdout = sys.__stdout__
            print(src); print("PY", py); print("LN", ln)
sys.stdout = sys.__stdout__
print("programs", len(srcs), "differ", bad)
