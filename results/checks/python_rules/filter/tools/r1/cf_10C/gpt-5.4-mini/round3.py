from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_digit_root_basecase(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and len(node.comparators) == 1
        and isinstance(node.left, ast.Name)
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 9
    )


def _fix_digit_root_basecase(node, ctx):
    return [ctx.text(node.left) + " < 10"]


def _is_bad_range_start_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) >= 1
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
    )


def _fix_range_start_one(node, ctx):
    args = [ctx.text(a) for a in node.args]
    if len(args) == 1:
        return ["range(" + args[0] + ")"]
    return ["range(" + ", ".join(args[1:]) + ")"]


def _is_bad_range_to_nplus1(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Add)
        and isinstance(node.args[1].left, ast.Name)
        and ctx.text(node.args[1].left) == "n"
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _fix_range_to_n(node, ctx):
    return ["range(" + ctx.text(node.args[0]) + ", n)"]


def _is_bad_input_not_int(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and isinstance(ctx.parent(node), ast.Call)
        and isinstance(ctx.parent(node).func, ast.Name)
        and ctx.parent(node).func.id in {"d", "root"}
    )


def _fix_input_to_int(node, ctx):
    return ["int(input())"]


def _is_bad_len_str_loop(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Call)
        and isinstance(node.left.args[0].func, ast.Name)
        and node.left.args[0].func.id == "str"
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_len_str_loop(node, ctx):
    return ["len(str(" + ctx.text(node.left.args[0].args[0]) + ")) > 1"]


def _is_bad_c_for_i_j(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and isinstance(node.ops[0], ast.Lt)
        and isinstance(node.ops[1], ast.Lt)
        and isinstance(node.left, ast.Name)
        and ctx.text(node.left) == "c"
        and isinstance(node.comparators[0], ast.Name)
        and ctx.text(node.comparators[0]) == "n"
        and isinstance(node.comparators[1], ast.Constant)
        and node.comparators[1].value == 1
    )


def _fix_c_bound(node, ctx):
    return ["c <= n"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="digital_root_basecase_lt10",
                match=_is_bad_digit_root_basecase,
                replace=_fix_digit_root_basecase,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_should_start_at_zero_when_looping_over_all_values",
                match=_is_bad_range_start_one,
                replace=_fix_range_start_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_should_be_exclusive_n",
                match=_is_bad_range_to_nplus1,
                replace=_fix_range_to_n,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="input_should_be_converted_to_int",
                match=_is_bad_input_not_int,
                replace=_fix_input_to_int,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="loop_until_single_digit_using_greater_than_one",
                match=_is_bad_len_str_loop,
                replace=_fix_len_str_loop,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_c_with_n_not_n_plus_one",
                match=_is_bad_c_for_i_j,
                replace=_fix_c_bound,
                symptoms=("wrong",),
            ),
        ]