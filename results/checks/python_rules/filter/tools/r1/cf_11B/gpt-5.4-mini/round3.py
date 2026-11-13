from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "map"
        and len(node.args) >= 2
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id == "int"
        and isinstance(node.args[1], ast.Call)
        and isinstance(node.args[1].func, ast.Name)
        and node.args[1].func.id == "input"
    )


def _fix_input_call(node, ctx):
    return ["abs(int(input()))"]


def _is_abs_missing(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _add_abs(node, ctx):
    return ["abs(" + ctx.text(node) + ")"]


def _is_wrong_while_for_jump(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and len(node.body) >= 1
    )


def _fix_while_for_jump(node, ctx):
    return [
        "while pos < x or (pos-x) % 2 != 0:\n    jumps += 1\n    pos += jumps"
    ]


def _is_bad_triangle_formula_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Constant)
        and node.test.value is True
        and len(node.body) >= 1
    )


def _fix_triangle_formula_loop(node, ctx):
    return [
        "while pos < x or (pos-x) % 2 != 0:\n    jumps += 1\n    pos += jumps"
    ]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="map_input_to_abs_int_input",
                match=_is_bad_input_call,
                replace=_fix_input_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_abs_on_input",
                match=_is_abs_missing,
                replace=_add_abs,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="loop_should_use_monotone_position_and_parity",
                match=_is_wrong_while_for_jump,
                replace=_fix_while_for_jump,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="triangle_formula_loop_should_be_abs_search",
                match=_is_bad_triangle_formula_loop,
                replace=_fix_triangle_formula_loop,
                symptoms=("wrong",),
            ),
        ]