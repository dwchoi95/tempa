"""Is each draw of a builder's generator a function of the random stream alone?
Draws as augment._draw does (seed `<pid>:llm`, 20 * N_CAND calls of gen(rng)),
saving rng's state before each call, then replays every draw alone, in a fresh
process, from that state. A generator that keeps state between draws (globals,
the module-level `random`, the clock) fails to reproduce.
    python3 -I results/checks/iid/replay.py REPO  -> replay.txt beside this file"""
import json, pickle, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

R = Path(sys.argv[1])
sys.path.insert(0, str(R))
from src.experiments.augment import CS1, MODELS, N_CAND
from src.runner._values import SOURCE as VALUES

RUN = """
import json, pickle, random, sys
def one(rng):
    try:
        t = gen(rng)
        if isinstance(t, dict) and isinstance(t.get("args"), (list, tuple)):
            t = dict(t, args=[encode(a) for a in t["args"]])
        return json.dumps(t, sort_keys=True, default=repr)
    except Exception as e:
        return "!" + type(e).__name__
if sys.argv[1] == "all":
    rng, out = random.Random(sys.argv[2]), []
    for _ in range(int(sys.argv[3])):
        s = rng.getstate()
        out.append((s, one(rng)))
    sys.stdout.buffer.write(pickle.dumps(out))
else:
    rng = random.Random()
    rng.setstate(pickle.loads(sys.stdin.buffer.read()))
    print(one(rng))
"""


def check(pid, model):
    code = (R / "benchmark" / pid / "amplified" / model / "generator.py").read_text() + "\n" + VALUES + RUN
    draws = pickle.loads(subprocess.run([sys.executable, "-c", code, "all", f"{pid}:llm", str(20 * N_CAND)],
                                        capture_output=True, check=True).stdout)
    def alone(d):
        r = subprocess.run([sys.executable, "-c", code, "one"], input=pickle.dumps(d[0]), capture_output=True)
        return r.stdout.decode().strip() == d[1]
    with ThreadPoolExecutor(16) as ex:
        same = sum(ex.map(alone, draws))
    return f"{pid} {model}: {same} of {len(draws)} draws reproduce alone"


if __name__ == "__main__":
    lines = [check(p, m) for p in CS1 for m in MODELS]
    (Path(__file__).parent / "replay.txt").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
