from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_range_100(node, ctx):
    return (
        isinstance(node, ast.Constant)
        and isinstance(node.value, int)
        and node.value == 100
    )


def _replace_100_with_100000(node, ctx):
    return ["100000"]


def _is_not_f_not1_check(node, ctx):
    return (
        isinstance(node, ast.UnaryOp)
        and isinstance(node.op, ast.Not)
        and isinstance(node.operand, ast.Call)
        and isinstance(node.operand.func, ast.Name)
        and node.operand.func.id == "f"
        and len(node.operand.args) == 1
        and isinstance(node.operand.args[0], ast.Constant)
        and node.operand.args[0].value == 1
    )


def _replace_not_f1(node, ctx):
    return ["not f(1)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="increase_bsearch_upper_bound",
                match=_is_range_100,
                replace=_replace_100_with_100000,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="keep_one_day_guard_intact",
                match=_is_not_f_not1_check,
                replace=_replace_not_f1,
                symptoms=("wrong",),
            ),
        ]