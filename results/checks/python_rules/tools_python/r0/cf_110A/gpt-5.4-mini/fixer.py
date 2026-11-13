from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_count_lucky_digits(node, ctx):
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Add):
        return False
    left, right = node.left, node.right
    return (
        isinstance(left, ast.Call)
        and isinstance(right, ast.Call)
        and isinstance(left.func, ast.Attribute)
        and isinstance(right.func, ast.Attribute)
        and left.func.attr == "count"
        and right.func.attr == "count"
        and ctx.text(left.func.value) == ctx.text(right.func.value)
        and ctx.text(left.args[0]) == "'4'"
        and ctx.text(right.args[0]) == "'7'"
    )


def _fix_second_count(node, ctx):
    return [ctx.text(node.func.value) + ".count('7')"]


def _is_compare_to_4_or_7_count(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 2 or len(node.comparators) != 2:
        return False
    if not (isinstance(node.ops[0], ast.Eq) and isinstance(node.ops[1], ast.Eq)):
        return False
    left = node.left
    if not isinstance(left, ast.Name):
        return False
    c1, c2 = node.comparators
    return (
        isinstance(c1, ast.Constant) and c1.value == 4
        and isinstance(c2, ast.Constant) and c2.value == 7
    )


def _fix_compare_to_membership(node, ctx):
    return [f"{ctx.text(node.left)} in (4, 7)"]


def _is_compare_count_eq_4_or_7(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 2 or len(node.comparators) != 2:
        return False
    if not (isinstance(node.ops[0], ast.Eq) and isinstance(node.ops[1], ast.Eq)):
        return False
    return (
        isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 4
        and isinstance(node.comparators[1], ast.Constant) and node.comparators[1].value == 7
    )


def _fix_count_in_set(node, ctx):
    return [f"{ctx.text(node.left)} in {{4, 7}}"]


def _is_digit_vs_int_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
        and isinstance(node.left, (ast.Name, ast.Subscript, ast.Attribute, ast.Call))
    )


def _fix_digit_vs_int_compare(node, ctx):
    return [f"{ctx.text(node.left)} == '{ctx.text(node.comparators[0])}'"]


def _is_range_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Sub)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 1
    )


def _fix_range_len_minus_one(node, ctx):
    a = node.args[0]
    return [f"range({ctx.text(a.left)})"]


def _is_wrong_or_in_digit_check(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) for v in node.values)
        and all(len(v.ops) == 1 and isinstance(v.ops[0], ast.NotEq) for v in node.values)
    )


def _fix_or_to_and(node, ctx):
    return [f"{ctx.text(node.values[0])} and {ctx.text(node.values[1])}"]


def _is_len_check_for_exact_count(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Name)
        and node.comparators[0].func.id == "len"
    )


def _fix_len_check_to_lucky_count(node, ctx):
    return [ctx.text(node.left)]


def _is_print_yes_no_case(node, ctx):
    return (
        isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and node.value in ("Yes", "No", "yes", "no", "si", "Si", "NO", "YES!")
    )


def _fix_print_case(node, ctx):
    mapping = {
        "Yes": "YES",
        "No": "NO",
        "yes": "YES",
        "no": "NO",
        "si": "YES",
        "Si": "YES",
        "YES!": "YES",
    }
    return [repr(mapping[node.value])]


def _is_modulo_on_count(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.left, ast.Name)
        and isinstance(node.right, ast.Constant)
        and node.right.value in (4, 7)
    )


def _fix_modulo_on_count(node, ctx):
    return [ctx.text(node.left)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="second_count_should_count_7",
                match=_is_count_lucky_digits,
                replace=_fix_second_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_count_to_lucky_membership",
                match=_is_compare_count_eq_4_or_7,
                replace=_fix_count_in_set,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_digits_as_strings",
                match=_is_digit_vs_int_compare,
                replace=_fix_digit_vs_int_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_len_minus_one_off_by_one",
                match=_is_range_len_minus_one,
                replace=_fix_range_len_minus_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="or_between_neq_checks_should_be_and",
                match=_is_wrong_or_in_digit_check,
                replace=_fix_or_to_and,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_check_should_use_count",
                match=_is_len_check_for_exact_count,
                replace=_fix_len_check_to_lucky_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_yes_no_casing",
                match=_is_print_yes_no_case,
                replace=_fix_print_case,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="modulo_on_count_should_be_plain_count",
                match=_is_modulo_on_count,
                replace=_fix_modulo_on_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_to_four_or_seven_membership",
                match=_is_compare_to_4_or_7_count,
                replace=_fix_compare_to_membership,
                symptoms=("wrong",),
            ),
        ]