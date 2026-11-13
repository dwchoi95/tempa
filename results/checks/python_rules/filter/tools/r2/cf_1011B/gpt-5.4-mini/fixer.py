from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bound_100(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 100


def _to_100000(node, ctx):
    return ["100000"]


def _is_bad_zero_start_range(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 0
    )


def _to_one_start_range(node, ctx):
    return ["range(1, " + ctx.text(node.args[1]) + ")"]


def _is_list_len_alloc(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mult)
        and isinstance(node.left, ast.List)
        and len(node.left.elts) == 1
        and isinstance(node.left.elts[0], ast.Constant)
        and node.left.elts[0].value == 0
        and isinstance(node.right, ast.Call)
        and isinstance(node.right.func, ast.Name)
        and node.right.func.id == "len"
    )


def _to_hundred_list(node, ctx):
    return ["[0] * 100"]


def _is_plain_len(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len"


def _to_len_plus_one(node, ctx):
    return [ctx.text(node) + " + 1"]


def _is_zero_or_one_check(node, ctx):
    return (
        isinstance(node, ast.UnaryOp)
        and isinstance(node.op, ast.Not)
        and isinstance(node.operand, ast.Call)
    )


def _to_direct_check(node, ctx):
    call = node.operand
    return [ctx.text(call)]


def _is_lt_100_bound(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 100


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="search_upper_bound_100_to_100000",
                match=_is_bound_100,
                replace=_to_100000,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_start_zero_to_one",
                match=_is_bad_zero_start_range,
                replace=_to_one_start_range,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="alloc_list_to_hundred",
                match=_is_list_len_alloc,
                replace=_to_hundred_list,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_off_by_one",
                match=_is_plain_len,
                replace=_to_len_plus_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="negated_call_check_to_direct_call",
                match=_is_zero_or_one_check,
                replace=_to_direct_check,
                symptoms=("wrong",),
            ),
        ]