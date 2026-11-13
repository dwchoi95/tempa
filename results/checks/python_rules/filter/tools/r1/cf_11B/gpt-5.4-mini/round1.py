from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_abs_input_assign(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "int"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Name)
        and node.value.args[0].func.id == "input"
    )


def _replace_with_abs_input(node, ctx):
    target = ctx.text(node.targets[0])
    return [f"{target} = abs(int(input()))"]


def _is_input_map_print(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
        and len(node.value.args) == 2
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id == "int"
        and isinstance(node.value.args[1], ast.Call)
        and isinstance(node.value.args[1].func, ast.Name)
        and node.value.args[1].func.id == "input"
    )


def _replace_map_input(node, ctx):
    target = ctx.text(node.targets[0])
    return [f"{target} = abs(int(input()))"]


def _is_wrong_jump_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and len(node.test.comparators) == 1
        and isinstance(node.test.comparators[0], ast.Name)
        and any(isinstance(n, ast.AugAssign) and isinstance(n.op, ast.Add) for n in ast.walk(node))
    )


def _replace_wrong_jump_loop(node, ctx):
    ind = ctx.text(node.test.left)
    x = ctx.text(node.test.comparators[0])
    body = "\n".join(ctx.text(s) for s in node.body)
    if body:
        body = "\n" + body
    return [f"while {ind} < {x} or ({ind}-{x}) % 2 != 0:\n{body}"]


def _is_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_strict_lt(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _is_wrong_parity_formula(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mult)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Div)
        and isinstance(node.left.left, ast.BinOp)
        and isinstance(node.left.left.op, ast.Add)
    )


def _replace_parity_formula(node, ctx):
    return ["(pos-x) % 2 != 0"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="abs_integer_input",
                match=_is_abs_input_assign,
                replace=_replace_with_abs_input,
                symptoms=("wrong", "err:ValueError"),
            ),
            Rewrite(
                name="map_input_should_parse_int",
                match=_is_input_map_print,
                replace=_replace_map_input,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="jump_loop_should_use_abs_and_parity",
                match=_is_wrong_jump_loop,
                replace=_replace_wrong_jump_loop,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="strict_lt_should_be_lte",
                match=_is_strict_lt_compare,
                replace=_replace_strict_lt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_parity_formula",
                match=_is_wrong_parity_formula,
                replace=_replace_parity_formula,
                symptoms=("wrong",),
            ),
        ]