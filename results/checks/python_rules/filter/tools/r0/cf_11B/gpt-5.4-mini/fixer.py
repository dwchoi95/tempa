from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_int_input(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0])
    )


def _match_plain_int_input(node, ctx):
    return _is_int_input(node)


def _replace_abs_int_input(node, ctx):
    return [f"abs({ctx.text(node)})"]


def _match_map_int_input_assignment(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
        and len(node.value.args) == 2
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id == "int"
        and _is_input_call(node.value.args[1])
    )


def _replace_map_int_input_assignment(node, ctx):
    target = ctx.text(node.targets[0])
    return [f"{target} = abs(int(input()))"]


def _match_while_eq(node, ctx):
    return isinstance(node, ast.While) and isinstance(node.test, ast.Compare) and len(node.test.ops) == 1 and isinstance(node.test.ops[0], ast.NotEq)


def _replace_while_eq_to_abs_parity(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Module):
        return []
    return []


def _match_wrong_jump_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and len(node.body) >= 1
    )


def _replace_wrong_jump_loop(node, ctx):
    return []


def _match_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_strict_lt(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _match_eq_to_lt_parity_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
    )


def _replace_eq_loop(node, ctx):
    return []


def _match_int_input_assigned_to_x(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.targets[0].id, str)
        and node.targets[0].id == "x"
        and _is_int_input(node.value)
    )


def _replace_x_abs_int_input(node, ctx):
    return ["x = abs(int(input()))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="wrap_int_input_with_abs",
                match=_match_plain_int_input,
                replace=_replace_abs_int_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="map_int_input_to_abs_int_input",
                match=_match_map_int_input_assignment,
                replace=_replace_map_int_input_assignment,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="assign_x_from_abs_int_input",
                match=_match_int_input_assigned_to_x,
                replace=_replace_x_abs_int_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_lt_should_be_lte",
                match=_match_strict_lt,
                replace=_replace_strict_lt,
                symptoms=("wrong",),
            ),
        ]