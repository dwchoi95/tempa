from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_lucky_count_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.In))
    )


def _replace_count_membership(node, ctx):
    left = ctx.text(node.left)
    if isinstance(node.ops[0], ast.In):
        right = ctx.text(node.comparators[0])
        return [f"{left} in {right}"]
    if isinstance(node.ops[0], ast.Eq):
        right = ctx.text(node.comparators[0])
        if right in {"4", "7"}:
            return [f"{left} in {{4, 7}}"]
    return []


def _is_digit_not_digit_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and (
            (isinstance(node.left, ast.Constant) and node.left.value in (4, 7))
            or any(isinstance(c, ast.Constant) and c.value in (4, 7) for c in node.comparators)
        )
    )


def _fix_digit_compare(node, ctx):
    if isinstance(node.left, ast.Constant) and node.left.value in (4, 7):
        return [f"{ctx.text(node.left)} == '4' or {ctx.text(node.left)} == '7'"]
    if len(node.comparators) == 1 and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value in (4, 7):
        return [f"{ctx.text(node.left)} == '4' or {ctx.text(node.left)} == '7'"]
    return []


def _is_len_equal_digits(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == "len")
            or any(isinstance(c, ast.Call) and isinstance(c.func, ast.Name) and c.func.id == "len" for c in node.comparators)
        )
    )


def _fix_len_equal_digits(node, ctx):
    if isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == "len":
        return [f"{ctx.text(node.left.args[0])}.count('4') + {ctx.text(node.left.args[0])}.count('7') in {{4, 7}}"]
    return []


def _is_count_vs_len(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (isinstance(node.left, ast.Name) and node.left.id in {"count", "c", "s", "num", "cnt", "ans", "total", "x", "k", "p", "q"})
            or (isinstance(node.comparators[0], ast.Call) and isinstance(node.comparators[0].func, ast.Name) and node.comparators[0].func.id == "len")
        )
    )


def _fix_count_vs_len(node, ctx):
    if isinstance(node.left, ast.Name):
        return [f"{ctx.text(node.left)} in {{4, 7}}"]
    return []


def _is_wrong_mod_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Mod)
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (0, 1, 4, 7)
    )


def _fix_wrong_mod_check(node, ctx):
    return []


def _is_range_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Sub)
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _fix_range_off_by_one(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1].left)})"]


def _is_print_yes_no_lower(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print"


def _fix_print_yes_no_lower(node, ctx):
    txt = ctx.text(node)
    if '"yes"' in txt or "'yes'" in txt:
        return [txt.replace('"yes"', '"YES"').replace("'yes'", "'YES'").replace('"no"', '"NO"').replace("'no'", "'NO'")]
    return []


def _is_wrong_input_len_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
    )


def _fix_wrong_input_len_check(node, ctx):
    arg = ctx.text(node.left.args[0])
    return [f"{arg}.count('4') + {arg}.count('7') in {{4, 7}}"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="count_digits_should_be_in_lucky_set", match=_is_lucky_count_check, replace=_replace_count_membership, symptoms=("wrong",)),
            Rewrite(name="digit_compare_must_use_strings", match=_is_digit_not_digit_compare, replace=_fix_digit_compare, symptoms=("wrong",)),
            Rewrite(name="len_equals_should_be_count_digits", match=_is_len_equal_digits, replace=_fix_len_equal_digits, symptoms=("wrong",)),
            Rewrite(name="count_variable_should_be_lucky_count", match=_is_count_vs_len, replace=_fix_count_vs_len, symptoms=("wrong",)),
            Rewrite(name="mod_check_not_needed", match=_is_wrong_mod_check, replace=_fix_wrong_mod_check, symptoms=("wrong",)),
            Rewrite(name="range_stop_off_by_one", match=_is_range_off_by_one, replace=_fix_range_off_by_one, symptoms=("wrong",)),
            Rewrite(name="normalize_yes_no_case", match=_is_print_yes_no_lower, replace=_fix_print_yes_no_lower, symptoms=("wrong",)),
            Rewrite(name="len_of_input_is_wrong_property", match=_is_wrong_input_len_check, replace=_fix_wrong_input_len_check, symptoms=("wrong",)),
        ]