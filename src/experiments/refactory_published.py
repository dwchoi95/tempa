"""Enter Refactory's published numbers (its own corpus) into the unified
summary CSVs, per protocol: on refactory_q1..q5 we do not re-run the tool --
RR/RPS/ATT come verbatim from the paper's strongest configuration
(per-problem times 3.5/4.8/4.7/8.7/13.1 s; overall 5.5 s). Quoting the authors
on their own corpus leaves no room to argue we configured their tool wrongly.

``refactory_results`` can also collect the authors' shipped run of the tool and
re-measure it on our footing; that output is archived at
``archive/results/refactory_ours.json`` (dev branch) and reproduces these published repair rates
to 0.05 points corpus-wide, but it is not what the paper reports.

Usage: python3 -m src.experiments.refactory_published
"""
from __future__ import annotations

from src.experiments.results_io import build_overall, upsert_summary

# pid: (N_wrong, RR, RPS, ATT_cpu_seconds)
PUBLISHED = {
    "refactory_q1": (575, 0.9896, 0.39, 3.5),
    "refactory_q2": (435, 0.7816, 0.56, 4.8),
    "refactory_q3": (308, 0.9740, 0.34, 4.7),
    "refactory_q4": (357, 0.8824, 0.31, 8.7),
    "refactory_q5": (108, 0.8796, 0.32, 13.1),
}


def main(argv=None) -> int:
    for pid, (n, rr, rps, att) in PUBLISHED.items():
        upsert_summary("", pid, {
            "Approach": "Refactory", "Model": "none", "N": n,
            "RR": rr, "RPS": rps,
            "ATT_all": att, "ATT_cpu": att, "ATT_api": 0.0,
            "ATT_build": 0.0, "InT": 0, "OuT": 0,
            "$API": 0.0, "$Build": 0.0,
            "Rules_build": "[]", "Rules_add": "[]", "Rules_used": "{}",
        })
        print(f"[{pid}] Refactory published: RR={rr} RPS={rps}")
    build_overall("")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
