"""compare.py with the same builders' rules as Python match/replace functions in place of the
rule-language ones. The engine still replaces one hole, a time limit bounds each application,
and the always-on rules, transplant, tests, and budgets are those of TEMPA_L, so an arm differs
from it only in the form the builder wrote its rules in. The tools are those of commit
f3fde1df~1, the engine they call is rewrite.py. No model is queried.
    python3 results/checks/python_rules/run_python.py BUILD <compare args>"""
import importlib.util, json, sys
from pathlib import Path
ROOT, HERE = Path(__file__).resolve().parents[3], Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT), str(HERE)]
import rewrite                                     # noqa: E402
sys.modules["src.core.rewrite"] = rewrite
from src.core.generic_rules import generic_rules   # noqa: E402
from src.experiments import compare                # noqa: E402


def load(d: Path):
    """The Fixer's rules and any learned ones, as the loader of that commit returned them."""
    def module(f):
        spec = importlib.util.spec_from_file_location("_tool_" + f.stem, f)
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        return m
    rules = module(d / "fixer.py").Fixer().rules()
    if (d / "learned.py").exists():
        rules = rules + list(getattr(module(d / "learned.py"), "LEARNED", []))
    return [r.rule() if isinstance(r, rewrite.Rewrite) else r for r in rules]


if __name__ == "__main__":
    build, argv = sys.argv[1], sys.argv[2:]
    tool = HERE / "tools_python" / build / argv[argv.index("--problem") + 1] / argv[argv.index("--model") + 1]
    compare.load_fixer = lambda _path: load(tool) + generic_rules()
    cost = json.loads((tool / "cost.json").read_text())
    compare._build_cost = lambda _path: (float(cost.get("build_seconds") or 0), float(cost.get("usd") or 0))
    sys.exit(compare.main(argv))
