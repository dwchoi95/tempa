"""Worked pairs per assignment, recomputed with Select's own code (no LLM call).

No build log records the worked pairs by name: tools/<pid>/<model>/cost.json keeps
only their number (n_samples). Select is model-free and deterministic
(pair_by_bfs + cluster_docs(distance_threshold=None) + modal member), so the same
set fed both builders and both rebuilds. We recompute it exactly as
src/experiments/cluster_once.clusters() does (cluster -> representative, by index
into the sorted buggy files) and check, per assignment, that
  (a) the number of representatives equals n_samples in every cost.json
      (campaign, tools/rebuild/r1, r2; both builders), and
  (b) the representatives' texts equal the texts select_sample_pairs() returns.
text_dup flags a non-worked program whose source text equals a worked pair's
(the builder saw that exact text): the stricter "unseen" set excludes them too.
same_edit flags a program whose edit script to its minimum-edit partner equals, as a multiset
of operations (Select's own comparison, cluster._modal_member), its representative's.

    python3 results/checks/baselines/worked_pairs.py   -> worked_pairs.csv
"""
import json, os, sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
from src.core.cluster import cluster, cluster_docs, edit_script, pair_by_bfs  # noqa
from src.core.synthesis import select_sample_pairs  # noqa
from src.experiments._common import IDS, ORDER, load_pool  # noqa

HERE = Path(__file__).resolve().parent
MODELS = ["claude-sonnet-5", "gpt-5.4-mini"]


def main():
    rows = []
    for pid in ORDER:
        files = sorted((ROOT / "benchmark" / pid / "buggy").glob("*.py"))   # load_pool's order
        names = [f.stem for f in files]
        buggy, correct = load_pool(pid, "buggy"), load_pool(pid, "correct")
        partner, _ = pair_by_bfs(buggy, correct)
        docs = [edit_script(b, correct[int(partner[i])]) for i, b in enumerate(buggy)]
        cs, _ = cluster_docs(docs, distance_threshold=None) if any(docs) else cluster(buggy)
        rep = {i: c.medoid for c in cs for i in c.members}
        reps = {c.medoid for c in cs}
        # (a) count against every build record
        for root in ("tools", "tools/rebuild/r1", "tools/rebuild/r2"):
            for m in MODELS:
                n = json.loads((ROOT / root / pid / m / "cost.json").read_text())["n_samples"]
                assert n == len(reps), (pid, root, m, n, len(reps))
        # (b) same texts as Select's own output
        sel = [b for b, _f, _n in select_sample_pairs(buggy, correct)]
        assert sorted(sel) == sorted(buggy[i] for i in reps), pid
        seen = {buggy[i] for i in reps}
        for i, n in enumerate(names):
            rows.append({"pid": pid, "id": IDS[pid], "buggy": n, "worked": i in reps,
                         "cluster_rep": names[rep[i]], "cluster_size": sum(rep[j] == rep[i] for j in rep),
                         "text_dup": i not in reps and buggy[i] in seen,
                         "same_edit": sorted(docs[i].split()) == sorted(docs[rep[i]].split())})
        print(IDS[pid], len(names), "worked", len(reps), "text-dup", sum(r["text_dup"] for r in rows if r["pid"] == pid), flush=True)
    d = pd.DataFrame(rows)
    d.to_csv(HERE / "worked_pairs.csv", index=False)
    print("total", len(d), "worked", int(d.worked.sum()), "never worked", int((~d.worked).sum()),
          "never worked and no text duplicate", int((~d.worked & ~d.text_dup).sum()),
          "never worked, same edit as its worked pair", int((~d.worked & d.same_edit).sum()))


if __name__ == "__main__":
    main()
