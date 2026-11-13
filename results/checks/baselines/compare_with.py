"""compare.py with the rules of a non-LLM baseline in place of a builder's.

    python3 results/checks/baselines/compare_with.py SOURCE <compare args>

SOURCE is refazer (transformations served by the original Refazer under
tools_refazer/<pid>/refazer/). It gets the same 8 always-on rules, the same
transplant, and the --model builder's amplified suite, so the arm differs from
TEMPA_L only in where its rules came from.

baseline_SOURCE/<pid>/tempa_l.csv, which analyze.py reads, came from, per PID and MODEL:
    python3 results/checks/baselines/compare_with.py SOURCE --problem PID --model MODEL \\
        --no-llm --amplified --only-missing --ver checks/baselines/baseline_SOURCE
Refazer runs under Mono (src/baselines/refazer/build.sh)."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from src.experiments import compare            # noqa: E402
from src.core.generic_rules import generic_rules  # noqa: E402

source, argv = sys.argv[1], sys.argv[2:]
pid = argv[argv.index("--problem") + 1]
tool_dir = ROOT / f"tools_{source}" / pid / source
if source == "refazer":
    from src.baselines.refazer.rules import load_refazer_rules
    compare.load_fixer = lambda _path: load_refazer_rules(tool_dir) + generic_rules()
else:
    raise SystemExit(f"unknown source {source}")
compare._build_cost = lambda _path: (0.0, 0.0)  # no model is queried to build these
sys.exit(compare.main(argv))
