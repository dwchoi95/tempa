"""A per-program bound with a stated confidence, in place of plugging a mean count of observed error sets into
Proposition 4.5. Every candidate is fixed before D is sampled, and err(c) is measured on m draws of D independent of
T_amp, so Clopper-Pearson intervals at level alpha/|pool|, joined by a union bound, hold for every candidate of a
program at once with probability at least 1 - alpha. On that event, no candidate with err(c) > eps escapes
    B(b) = sum over T-passing c with upper(c) > eps of (1 - lower(c))^n,
which bounds the probability of Proposition 4.5 by its first sum, each error set counted at least once.
    python3 -I certified.py REPO   -> certified.txt, certified.csv
The pools and err(c) are a4_pool.py's (a4_pool/, a4_err/). D is common.sample's, cached in cache/ (not
tracked); without it, D is drawn and labelled again: 2 minutes instead of 1 s."""
import csv, hashlib, json, statistics as st, sys
from pathlib import Path
from scipy.stats import beta
HERE = Path(__file__).resolve().parent
REPO = Path(sys.argv[1]); sys.path[:0] = [str(REPO), str(HERE)]
from common import kept, sample                    # noqa: E402
CS1 = [f"refactory_q{i}" for i in range(1, 6)]
M = ("claude-sonnet-5", "gpt-5.4-mini")
N, ALPHA = 100, 0.01
sha = lambda s: hashlib.sha1(s.encode()).hexdigest()


def interval(k, m, a):
    """The exact two-sided interval for k failures in m draws at level a."""
    lo = beta.ppf(a / 2, k, m - k + 1) if k else 0.0
    hi = beta.ppf(1 - a / 2, k + 1, m - k) if k < m else 1.0
    return lo, hi


rows = []
for pid in CS1:
    for m in M:
        ins, mult = kept(sample(pid, m))
        draws = sum(mult)
        err = json.loads((HERE / "a4_err" / f"{pid}_{m}.json").read_text())
        for l in open(HERE / "a4_pool" / f"{pid}_{m}.jsonl"):
            r = json.loads(l)
            cands = [err[sha(s)][0] for s, _ in r["tpass"]]
            row = dict(pid=pid, model=m, buggy=r["buggy"], draws=draws, tpass=len(cands))
            for eps in (0.01, 0.05, 0.10):
                b, may = 0.0, 0
                for e in cands:
                    lo, hi = interval(round(e * draws), draws, ALPHA / max(len(cands), 1))
                    if hi > eps:
                        b += (1 - lo) ** N
                        may += 1
                row[f"bound_{eps}"] = min(1.0, b)
                row[f"may_{eps}"] = may
            rows.append(row)
with open(HERE / "certified.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
out = [f"{len(rows)} programs, draws {min(r['draws'] for r in rows)}-{max(r['draws'] for r in rows)}, n={N}, confidence {1 - ALPHA}"]
for m in M + ("both",):
    g = [r for r in rows if m in (r["model"], "both")]
    for eps in (0.01, 0.05, 0.10):
        v = sorted(r[f"bound_{eps}"] for r in g)
        out.append(f"{m} eps={eps}: n {len(v)} mean {100 * st.mean(v):.3f}% median {100 * st.median(v):.3f}% "
                   f"p90 {100 * v[int(.9 * len(v))]:.3f}% max {100 * v[-1]:.2f}%  <=1%: {sum(x <= .01 for x in v)}  <=5%: {sum(x <= .05 for x in v)}")
out.append("the same programs at eps=0.05 by counting, (1-eps)^n per candidate instead of (1-lower)^n:")
for name, k in (("every T-passing candidate", "tpass"), ("those that may exceed eps", "may_0.05")):
    v = [min(1.0, r[k] * .95 ** N) for r in rows]
    out.append(f"{name}: count mean {st.mean(r[k] for r in rows):.1f}  <=1%: {sum(x <= .01 for x in v)}  <=5%: {sum(x <= .05 for x in v)}  max {100 * max(v):.2f}%")
print("\n".join(out)); (HERE / "certified.txt").write_text("\n".join(out) + "\n")
