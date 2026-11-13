from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_count_lucky_digits_expr(node):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.left, ast.Call)
        and isinstance(node.right, ast.Call)
        and isinstance(node.left.func, ast.Attribute)
        and isinstance(node.right.func, ast.Attribute)
        and node.left.func.attr == "count"
        and node.right.func.attr == "count"
    )


def _replace_count_4_7(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.right)
    return [f"{left}.count('4') + {right}.count('7')"]


def _match_len_equals_4_or_7(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 for v in node.values)
    )


def _replace_len_to_count_check(node, ctx):
    return ["(s.count('4')+s.count('7') in {4,7})"]


def _match_digit_is_int_4_or_7(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) and len(v.ops) == 1 for v in node.values)
        and any(isinstance(v.left, ast.Subscript) for v in node.values)
    )


def _replace_digit_is_int_4_or_7(node, ctx):
    return [ctx.text(node).replace("== 4", "== '4'").replace("== 7", "== '7'")]


def _match_wrong_count_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
        and not isinstance(node.ops[0], (ast.In, ast.NotIn))
    )


def _replace_wrong_count_compare(node, ctx):
    left = ctx.text(node.left)
    return [f"{left} in {{4, 7}}"]


def _match_count_mod_check(node, ctx):
    return (
        isinstance(node, ast.BoolOp)
        and isinstance(node.op, ast.Or)
        and len(node.values) == 2
        and all(isinstance(v, ast.Compare) for v in node.values)
    )


def _replace_count_mod_check(node, ctx):
    return ["count in (4, 7)"]


def _match_count_equal_len(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Name)
        and node.comparators[0].func.id == "len"
    )


def _replace_count_equal_len(node, ctx):
    return ["count in {4, 7}"]


def _match_for_range_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name)
        and node.iter.func.id == "range"
        and len(node.iter.args) == 1
        and isinstance(node.iter.args[0], ast.BinOp)
        and isinstance(node.iter.args[0].op, ast.Sub)
        and isinstance(node.iter.args[0].right, ast.Constant)
        and node.iter.args[0].right.value == 1
    )


def _replace_for_range_len_minus_one(node, ctx):
    it = ctx.text(node.iter.args[0].left)
    return [ctx.text(node).replace(f"range({it} - 1)", f"range({it})")]


def _match_wrong_digit_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
        and isinstance(node.left.ctx, ast.Load)
    )


def _replace_wrong_digit_check(node, ctx):
    left = ctx.text(node.left)
    val = node.comparators[0].value
    return [f"{left} == '{val}'"]


def _match_len_digits_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value in (4, 7)
    )


def _replace_len_digits_check(node, ctx):
    return ["count == 4 or count == 7"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="count_4_7_digits_not_double_4",
                match=_is_count_lucky_digits_expr,
                replace=_replace_count_4_7,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="nearly_lucky_should_check_count_digits_not_length",
                match=_match_len_equals_4_or_7,
                replace=_replace_len_to_count_check,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="digit_comparison_should_use_strings",
                match=_match_digit_is_int_4_or_7,
                replace=_replace_digit_is_int_4_or_7,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_compared_to_lucky_number",
                match=_match_wrong_count_compare,
                replace=_replace_wrong_count_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_mod_lucky_wrongly",
                match=_match_count_mod_check,
                replace=_replace_count_mod_check,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_equals_length_should_be_lucky_count",
                match=_match_count_equal_len,
                replace=_replace_count_equal_len,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="off_by_one_range_upper_bound",
                match=_match_for_range_len_minus_one,
                replace=_replace_for_range_len_minus_one,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="numeric_digit_compare_to_string",
                match=_match_wrong_digit_check,
                replace=_replace_wrong_digit_check,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_of_digits_should_be_count_check",
                match=_match_len_digits_check,
                replace=_replace_len_digits_check,
                symptoms=("wrong",),
            ),
        ]