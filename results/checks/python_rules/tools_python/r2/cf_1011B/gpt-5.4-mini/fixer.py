from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_binop_with_const(node, op_type, const_value=None):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, op_type)
        and isinstance(node.right, ast.Constant)
        and (const_value is None or node.right.value == const_value)
    )


def _fix_hundred_bound(node, ctx):
    return [
        ctx.text(node.left) + " " + node.op.__class__.__name__.replace("Lt", "<").replace("Gt", ">").replace("Add", "+").replace("Sub", "-") + " 100000"
        if False else ctx.text(node.left) + " + 100000"
    ]


def _match_r_bound_100(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "r"
        and isinstance(node.value, ast.Constant)
        and node.value.value == 100
    )


def _replace_r_bound_100(node, ctx):
    return ["r = 100000"]


def _match_range_exclusive_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.Constant)
        and isinstance(node.args[1].value, int)
    )


def _replace_range_add_one(node, ctx):
    end = ctx.text(node.args[1])
    return [f"range({ctx.text(node.args[0])}, {end} + 1)"]


def _match_floor_div_plus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.BinOp)
        and isinstance(node.right.op, ast.Add)
        and isinstance(node.right.right, ast.Constant)
        and node.right.right.value == 1
    )


def _replace_drop_plus_one(node, ctx):
    return [f"{ctx.text(node.left)} // {ctx.text(node.right.left)}"]


def _match_if_not_f1_print0(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.UnaryOp)
        and isinstance(node.test.op, ast.Not)
        and isinstance(node.test.operand, ast.Call)
        and isinstance(node.test.operand.func, ast.Name)
        and node.test.operand.func.id == "f"
        and len(node.test.operand.args) == 1
        and isinstance(node.test.operand.args[0], ast.Constant)
        and node.test.operand.args[0].value == 1
    )


def _replace_if_not_f1_print0(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="binary_search_upper_bound_too_small",
                match=_match_r_bound_100,
                replace=_replace_r_bound_100,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="drop_plus_one_in_division_threshold",
                match=_match_floor_div_plus_one,
                replace=_replace_drop_plus_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_off_by_one",
                match=_match_range_exclusive_off_by_one,
                replace=_replace_range_add_one,
                symptoms=("wrong",),
            ),
        ]