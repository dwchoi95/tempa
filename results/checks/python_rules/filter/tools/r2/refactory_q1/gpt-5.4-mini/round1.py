from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.Is))
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], (ast.Tuple, ast.List))
        and len(node.comparators[0].elts) == 0
    )


def _replace_empty_check_with_zero(node, ctx):
    return ["0"]


def _is_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _lte_from_lt(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _gte_from_gt(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_return_none_zero(node, ctx):
    return ["return 0"]


def _is_return_minus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.UnaryOp)
        and isinstance(node.value.op, ast.USub)
        and isinstance(node.value.operand, ast.Constant)
        and node.value.operand.value == 1
    )


def _replace_return_minus_one_zero(node, ctx):
    return ["return 0"]


def _is_i_plus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.left, ast.Name)
        and node.left.id == "i"
        and isinstance(node.right, ast.Constant)
        and node.right.value == 1
    )


def _replace_i_plus_one_i(node, ctx):
    return ["i"]


def _is_i_minus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Sub)
        and isinstance(node.left, ast.Name)
        and node.left.id == "i"
        and isinstance(node.right, ast.Constant)
        and node.right.value == 1
    )


def _replace_i_minus_one_i(node, ctx):
    return ["i"]


def _is_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Sub)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.right, ast.Constant)
        and node.right.value == 1
    )


def _replace_len_minus_one_len(node, ctx):
    return [ctx.text(node.left)]


def _is_break_in_if_else(node, ctx):
    return isinstance(node, ast.If) and len(node.body) == 1 and isinstance(node.body[0], ast.Return) and len(node.orelse) == 1 and isinstance(node.orelse[0], ast.Return)


class Fixer:
    def rules(self):
        return [
            Rewrite("empty_sequence_returns_zero", _is_empty_check, _replace_empty_check_with_zero, ("wrong",)),
            Rewrite("strict_lt_to_lte", _is_strict_lt_compare, _lte_from_lt, ("wrong",)),
            Rewrite("strict_gt_to_gte", _is_strict_gt_compare, _gte_from_gt, ("wrong",)),
            Rewrite("return_none_to_zero", _is_return_none, _replace_return_none_zero, ("wrong",)),
            Rewrite("return_minus_one_to_zero", _is_return_minus_one, _replace_return_minus_one_zero, ("wrong",)),
            Rewrite("off_by_one_i_plus_one_to_i", _is_i_plus_one, _replace_i_plus_one_i, ("wrong",)),
            Rewrite("off_by_one_i_minus_one_to_i", _is_i_minus_one, _replace_i_minus_one_i, ("wrong",)),
            Rewrite("len_minus_one_to_len", _is_len_minus_one, _replace_len_minus_one_len, ("wrong",)),
        ]