from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_jump_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and len(node.body) >= 1
    )


def _fix_jump_loop(node, ctx):
    tgt = ctx.text(node.test.comparators[0])
    body = "\n".join(ctx.text(stmt) for stmt in node.body)
    return [f"while pos < abs({tgt}) or (pos-abs({tgt})) % 2 != 0:\n    jumps += 1\n    pos += jumps"]


def _is_print_var(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _print_jump_count(node, ctx):
    return ["print(jumps)"]


def _is_input_as_map(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _fix_input_as_int_abs(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


def _is_absent_abs_input(node, ctx):
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


def _fix_abs_input(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="while_not_equal_jump_simulation_to_parity_condition",
                match=_is_bad_jump_loop,
                replace=_fix_jump_loop,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_jump_count_instead_of_current_variable",
                match=_is_print_var,
                replace=_print_jump_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_map_input_with_integer_input",
                match=_is_input_as_map,
                replace=_fix_input_as_int_abs,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="add_abs_to_integer_input",
                match=_is_absent_abs_input,
                replace=_fix_abs_input,
                symptoms=("wrong",),
            ),
        ]