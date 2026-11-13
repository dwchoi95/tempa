"""compare.py with the rules of build_filter.py: Python rules that passed the filter, each dropping at repair time the
candidates that read a name nothing binds. All else is as in run_python.py. No model is queried.
    python3 results/checks/python_rules/filter/run_filter.py BUILD <compare args>"""
import json, sys
from common import HERE, guarded, rewrites
from src.core.generic_rules import generic_rules
from src.experiments import compare


def load(tool):
    rejected = tool / "rejected.json"
    if not rejected.exists():                      # no round loaded: the always-on rules alone
        return generic_rules()
    skip = set(json.loads(rejected.read_text())["names"])
    return [guarded(r) for r in rewrites(tool / "fixer.py") if r.name not in skip] + generic_rules()


if __name__ == "__main__":
    build, argv = sys.argv[1], sys.argv[2:]
    tool = HERE / "tools" / build / argv[argv.index("--problem") + 1] / argv[argv.index("--model") + 1]
    compare.load_fixer = lambda _path: load(tool)
    cost = json.loads((tool / "cost.json").read_text())
    compare._build_cost = lambda _path: (float(cost.get("build_seconds") or 0), float(cost.get("usd") or 0))
    sys.exit(compare.main(argv))
