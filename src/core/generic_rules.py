"""A shared library of generic small-edit repair operators.

Every tool includes these regardless of what the builder wrote, so the common
CS1 slips — a strict/non-strict comparison, an off-by-one on a ``range`` bound,
an index shifted by one — are always covered even when the build sample happened
not to show them. They are written in the rule language (src/core/rulelang.py),
as the builder's rules are, so every rule a tool carries is data the engine
interprets.
"""
from __future__ import annotations

from src.core.repair import Rule

GENERIC_LANG = '''
rule generic_flip_compare
symptoms: wrong
match: $a $o:Cmp $b
rewrite: $a ${f1[$o]} $b
  |
  $a ${f2[$o]} $b
  |
  $a ${f3[$o]} $b
table f1: {"<": "<=", "<=": "<", ">": ">=", ">=": ">", "==": "!=", "!=": "=="}
table f2: {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "<="}
table f3: {"==": ">="}

rule generic_shift_range
symptoms: wrong, err:IndexError
match: range($*xs, $s)
rewrite: range($*xs, $s - 1)
  |
  range($*xs, $s + 1)

rule generic_drop_range_start
symptoms: wrong, err:IndexError
match: range($a, $s)
where: text($a) in {"0", "1"}
rewrite: range($s)

rule generic_shift_index
symptoms: wrong, err:IndexError
match: $x[$i]
where: kind($i) != "Slice"
rewrite: $x[$i - 1]
  |
  $x[$i + 1]

rule generic_unshift_index
symptoms: wrong, err:IndexError
match: $x[$j $o:Arith $c]
where: text($o) in {"+", "-"}
rewrite: $x[$j]

rule generic_flip_bool_op
symptoms: wrong
match: $a $o:Bool $b
rewrite: $a ${flip[$o]} $b
table flip: {"and": "or", "or": "and"}

rule generic_flip_first_and
symptoms: wrong
match: $a and $b and $*rest
where: len($rest) >= 1
rewrite: $a or $b and $*rest

rule generic_flip_first_or
symptoms: wrong
match: $a or $b or $*rest
where: len($rest) >= 1
rewrite: $a and $b or $*rest
'''


def generic_rules() -> list[Rule]:
    """The always-on operators, compiled."""
    from src.core.rulelang import compile_rules
    rules, errors = compile_rules(GENERIC_LANG)
    assert not errors, errors
    return [r.rule() for r in rules]
