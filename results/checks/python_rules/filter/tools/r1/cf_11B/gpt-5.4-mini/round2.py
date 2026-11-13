from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_map_print(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _fix_input_map_print(node, ctx):
    target = ctx.text(node.targets[0])
    return [f"{target} = abs(int(input()))"]


def _is_while_ne_guard(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
    )


def _fix_while_ne_guard(node, ctx):
    left = ctx.text(node.test.left)
    right = ctx.text(node.test.comparators[0])
    return [f"while {left} < {right} or ({left}-{right}) % 2 != 0:"]


def _is_add_sub_branch(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.LtE)
        and len(node.body) == 1
        and isinstance(node.body[0], ast.AugAssign)
        and isinstance(node.body[0].op, ast.Add)
        and len(node.orelse) == 1
        and isinstance(node.orelse[0], ast.AugAssign)
        and isinstance(node.orelse[0].op, ast.Sub)
    )


def _fix_add_sub_branch(node, ctx):
    return [f"{ctx.text(node.body[0].target)} += {ctx.text(node.body[0].value)}"]


def _is_add_sub_if_chain(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Lt)
        and len(node.body) == 1
        and isinstance(node.body[0], ast.Assign)
        and len(node.orelse) >= 1
    )


def _fix_add_sub_if_chain(node, ctx):
    return [f"{ctx.text(node.body[0].targets[0])} = {ctx.text(node.body[0].value)}"]


def _is_triangle_formula(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Div)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.left, ast.BinOp)
        and isinstance(node.left.left.op, ast.Mult)
    )


def _fix_triangle_formula(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="map_input_should_be_integer_input",
                match=_is_input_map_print,
                replace=_fix_input_map_print,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="loop_should_allow_negative_and_parity",
                match=_is_while_ne_guard,
                replace=_fix_while_ne_guard,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="greedy_branch_should_only_accumulate_forward",
                match=_is_add_sub_branch,
                replace=_fix_add_sub_branch,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="if_chain_wrongly_uses_directional_simulation",
                match=_is_add_sub_if_chain,
                replace=_fix_add_sub_if_chain,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="triangle_number_formula_needs_abs_based_search",
                match=_is_triangle_formula,
                replace=_fix_triangle_formula,
                symptoms=("wrong",),
            ),
        ]