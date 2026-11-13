from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
    )


def _is_count_lucky_digits(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.left, ast.Call)
        and isinstance(node.right, ast.Call)
        and isinstance(node.left.func, ast.Attribute)
        and isinstance(node.right.func, ast.Attribute)
        and node.left.func.attr == "count"
        and node.right.func.attr == "count"
        and ctx.text(node.left.func.value) == ctx.text(node.right.func.value)
    )


def _fix_count_4_to_7(node, ctx):
    return [ctx.text(node).replace(".count('4')", ".count('7')")]


def _is_count_compare_4_or_7(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.ops[1], ast.Eq)
        and any(ctx.text(c).strip() in ("4", "'4'", '"4"') for c in node.comparators)
        and any(ctx.text(c).strip() in ("7", "'7'", '"7"') for c in node.comparators)
    )


def _fix_count_compare_4_or_7(node, ctx):
    left = ctx.text(node.left)
    return [f"{left} in {{4, 7}}"]


def _is_digit_eq_int_4_or_7(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Constant)
        and node.left.value in ("4", "7", 4, 7)
        and len(node.comparators) == 1
        and ctx.text(node.comparators[0]).strip() not in ("4", "7", "'4'", "'7'", '"4"', '"7"')
    )


def _fix_digit_eq_int(node, ctx):
    return [ctx.text(node).replace("== 4", "== '4'").replace("== 7", "== '7'")]


def _is_num_eq_or_7(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and all(isinstance(op, ast.Eq) for op in node.ops)
        and len(node.comparators) == 2
        and any(ctx.text(c).strip() in ("4", "'4'", '"4"') for c in [node.left] + node.comparators)
        and any(ctx.text(c).strip() in ("7", "'7'", '"7"') for c in [node.left] + node.comparators)
    )


def _fix_or_to_in(node, ctx):
    return [f"{ctx.text(node.left)} in (4, 7)"]


def _is_mod_count_bug(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Mod)
        and ctx.text(node.left.right).strip() in ("4", "7")
        and ctx.text(node.comparators[0]).strip() in ("0", "1")
    )


def _fix_mod_count_bug(node, ctx):
    return [ctx.text(node.left.left) + " in (4, 7)"]


def _is_len_compare_bug(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and ctx.text(node.comparators[0]).strip() in ("4", "7")
    )


def _fix_len_compare_bug(node, ctx):
    arg = ctx.text(node.left.args[0])
    return [f"({arg}.count('4') + {arg}.count('7')) in {{4, 7}}"]


def _is_not_lucky_digit_loop_cond(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and ctx.text(node.left).strip() in ("i", "ch", "digit", "x", "num", "c")
        and ctx.text(node.comparators[0]).strip() in ("4", "7", "'4'", "'7'", '"4"', '"7"')
    )


def _fix_not_lucky_digit_loop_cond(node, ctx):
    return [ctx.text(node).replace("!=", "==")]


def _is_range_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Sub)
        and ctx.text(node.args[1].right).strip() == "1"
    )


def _fix_range_off_by_one(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1].left)})"]


def _is_bad_yes_no_case(node, ctx):
    return isinstance(node, ast.Constant) and isinstance(node.value, str) and node.value in {
        "Yes", "yes", "No", "no", "si", "Si", "NO ", "YES ", "Yes!", "No!"
    }


def _fix_yes_no_case(node, ctx):
    v = node.value
    if v.lower().startswith("y"):
        return ['"YES"']
    return ['"NO"']


def _is_wrong_count_count(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "count"
        and len(node.args) == 1
        and ctx.text(node.args[0]).strip() in ("'4'", '"4"')
    )


def _fix_wrong_count_count(node, ctx):
    return [ctx.text(node).replace(".count('4')", ".count('7')")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="count_4_but_missing_7",
                match=_is_wrong_count_count,
                replace=_fix_wrong_count_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_lucky_digits_addition_to_membership",
                match=_is_count_compare_4_or_7,
                replace=_fix_count_compare_4_or_7,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_digit_as_int_instead_of_string",
                match=_is_digit_eq_int_4_or_7,
                replace=_fix_digit_eq_int,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="or_lucky_values_should_be_membership",
                match=_is_num_eq_or_7,
                replace=_fix_or_to_in,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="modulo_used_as_count_check",
                match=_is_mod_count_bug,
                replace=_fix_mod_count_bug,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_equals_lucky_digit_should_be_count_of_lucky_digits",
                match=_is_len_compare_bug,
                replace=_fix_len_compare_bug,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_not_equal_on_digit_should_be_equal",
                match=_is_not_lucky_digit_loop_cond,
                replace=_fix_not_lucky_digit_loop_cond,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_off_by_one_stop",
                match=_is_range_off_by_one,
                replace=_fix_range_off_by_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="normalize_yes_no_literals",
                match=_is_bad_yes_no_case,
                replace=_fix_yes_no_case,
                symptoms=("wrong",),
            ),
        ]