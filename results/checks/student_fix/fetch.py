"""Who wrote each C1-C6 submission and when, from Codeforces' public API (contest.status),
kept only for the submissions of the benchmark. Handles are never written: an author is an
integer that means nothing outside this file. One request per 2.5 s.
    python3 -I fetch.py REPO   -> authors.csv (pid, submission, author, time, verdict)"""
import csv, json, sys, time, urllib.request
from pathlib import Path
REPO = Path(sys.argv[1]); HERE = Path(__file__).resolve().parent
PIDS = {"cf_1011B": (1011, "B"), "cf_10C": (10, "C"), "cf_110A": (110, "A"),
        "cf_11B": (11, "B"), "cf_125A": (125, "A"), "cf_131A": (131, "A")}
PAGE = 10000


def get(contest, start):
    url = f"https://codeforces.com/api/contest.status?contestId={contest}&from={start}&count={PAGE}"
    for i in range(8):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            d = json.load(urllib.request.urlopen(req, timeout=120))
            if d["status"] == "OK":
                return d["result"]
        except Exception as e:                     # noqa: BLE001
            print("retry", contest, start, repr(e)[:80], flush=True)
        time.sleep(10 * (i + 1))
    raise SystemExit(f"gave up at {contest} {start}")


ids, rows = {}, []
for pid, (contest, index) in PIDS.items():
    want = {f.stem: k for k in ("buggy", "correct") for f in (REPO / "benchmark" / pid / k).glob("*.py")}
    start, seen, found = 1, 0, 0
    while True:
        page = get(contest, start)
        for s in page:
            seen += 1
            if s["problem"]["index"] != index or str(s["id"]) not in want:
                continue
            m = s["author"].get("members") or [{}]
            who = m[0].get("handle") or f"team{s['author'].get('teamId')}"
            a = ids.setdefault(who, len(ids))
            rows.append((pid, s["id"], a, s["creationTimeSeconds"], s.get("verdict", "")))
            found += 1
        print(pid, start, len(page), "found", found, "of", len(want), flush=True)
        if len(page) < PAGE or found >= len(want):
            break
        start += PAGE
        time.sleep(2.5)
    time.sleep(2.5)
    with open(HERE / "authors.csv", "w", newline="") as f:
        w = csv.writer(f); w.writerow(["pid", "submission", "author", "time", "verdict"]); w.writerows(rows)
print("done", len(rows))
