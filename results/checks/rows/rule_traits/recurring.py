"""Mistake kinds that recur across assignments: each used rule of the main build, built-in
or the builder's, is assigned a kind by keywords of its name, checked by hand (the lists
printed below); for each kind, the assignments where such a rule repaired a program.
No model call.  python3 -I results/checks/rows/rule_traits/recurring.py"""
import collections, json, re, sys
from pathlib import Path
import pandas as pd
ROOT = Path(__file__).resolve().parents[4]; sys.path.insert(0, str(ROOT))
from src.experiments._common import ORDER                    # noqa: E402
IDS = dict(zip(ORDER, ["R1", "R2", "R3", "R4", "R5", "C1", "C2", "C3", "C4", "C5", "C6"]))
KINDS = [  # first match wins
    ("boundary", r"off_by_one|range|slice|plus_one|minus_one|non_strict|strict_cmp|_le$|_le_|le_one|ge_should|_gt$|bound|shift|eq_one|flip_compare|i_plus_one|unshift|round_plus"),
    ("missing call", r"missing_call|_call$|call_|bracket|parens|subscript|method_used|missing_parens"),
    ("wrong name", r"undefined|rename|typo|mismatch|shadow|name_used|wrong_.*var|collector|wrong_bound_variable|lowercase_true"),
    ("missing init, return, or step", r"missing_|_init|increment|return_after|fallback_return|default_return"),
    ("empty input", r"empty"),
    ("output", r"wording|print|debug|yes|_no_|_no$"),
]
FIX = {  # checked by hand against each rule's match and rewrite
    "wrong_bound_variable_in_prune_loop": "wrong name", "undefined_i_range_while_loop": "wrong name",
    "return_lhs_instead_of_result_slice": "wrong name", "bare_index_compare_in_range_loop": "assignment-specific",
    "broken_count_range_function": "assignment-specific", "sort_then_wrong_slice": "assignment-specific",
    "self_shadow_call": "wrong name", "plus_equal_typo": "assignment-specific", "digital_root_single_call_no_loop": "assignment-specific",
    "add_missing_empty_alt_check": "empty input", "tuple_concat_missing_wrap": "assignment-specific",
    "ordereddict_missing_list_wrap": "assignment-specific", "stray_double_equals_init": "assignment-specific",
    "carry_fix_end_kw_print": "assignment-specific", "carry_fix_format_print": "assignment-specific",
    "carry_fix_plain_print": "assignment-specific", "carry_fix_strconcat_print": "assignment-specific",
    "int_cast_printed_feet_and_inches": "assignment-specific", "wrap_print_manual_capitalize_lower": "assignment-specific",
    "wrap_print_manual_capitalize_nolower": "assignment-specific", "missing_parens_isupper": "missing call",
    "digital_root_bruteforce_missing_c_loop": "assignment-specific",
}
def kind(n):
    if n in FIX:
        return FIX[n]
    for k, rx in KINDS:
        if re.search(rx, n):
            return k
    return "assignment-specific"
seen = collections.defaultdict(lambda: collections.defaultdict(set)); names = collections.defaultdict(set)
for pid in ORDER:
    d = pd.read_csv(ROOT / "results" / pid / "tempa_lf.csv", keep_default_na=False)
    d = d[(d.Fixed.astype(str) == "True") & (d.Source == "rules")]
    for m, x in zip(d.Model, d.Rules_L):
        ns = json.loads(x) if x.startswith("[") else []
        ns = json.loads(ns) if isinstance(ns, str) else ns
        for n in ns:
            k = kind(n); seen[k][IDS[pid]].add(m); names[k].add((IDS[pid], n))
builtin = collections.defaultdict(set)
for k, i in ((k, i) for k in names for i, n in names[k] if n.startswith("generic_")):
    builtin[k].add(i)
own = {k: {i for i, n in names[k] if not n.startswith("generic_")} for k in names}
cols = ["R1", "R2", "R3", "R4", "R5", "C1", "C2", "C3", "C4", "C5", "C6"]
print("matrix (B builder rule, b built-in only):")
for k, _ in KINDS + [("assignment-specific", "")]:
    print(f"  {k:32s}", " ".join("B " if i in own.get(k, ()) else "b " if i in builtin.get(k, ()) else ". " for i in cols),
          "| own", len(own.get(k, ())), "built-in", len(builtin.get(k, ())), "any", len(own.get(k, set()) | builtin.get(k, set())))
for k, _ in KINDS + [("assignment-specific", "")]:
    a = sorted(seen[k], key=lambda i: (i[0] != "R", int(i[1:])))
    print(f"\n{k}: {len(a)} assignments {a}")
    print("   ", ", ".join(f"{i}:{n}" for i, n in sorted(names[k]))[:2500])

json.dump({k: {i: ("B" if i in own.get(k, ()) else "b") for i in cols if i in own.get(k, ()) or i in builtin.get(k, ())}
           for k, _ in KINDS}, open(Path(__file__).with_name("recurring.json"), "w"), indent=1)
