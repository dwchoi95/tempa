from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_int_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and len(node.keywords) == 0
        and _is_input_call(node.args[0])
    )


def _fix_abs_int_input(node, ctx):
    return [f"abs({ctx.text(node)})"]


def _match_print_raw_input(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and len(node.value.keywords) == 0
        and _is_input_call(node.value.args[0])
    )


def _fix_print_raw_input(node, ctx):
    return [f"print(abs(int(input())))"]


def _match_zero_based_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and (
            (isinstance(node.test.left, ast.Name) and node.test.left.id in {"s", "pos"})
            or (len(node.test.comparators) == 1 and isinstance(node.test.comparators[0], ast.Name) and node.test.comparators[0].id in {"s", "pos"})
        )
    )


def _fix_zero_based_loop(node, ctx):
    test = f"{ctx.text(node.test.left)} < {ctx.text(node.test.comparators[0])} or ({ctx.text(node.test.left)}-{ctx.text(node.test.comparators[0])}) % 2 != 0"
    return [f"while {test}:\n    {ctx.text(node.body[0])}"]


def _match_strict_progression_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
    )


def _fix_strict_progression_loop(node, ctx):
    return [f"while pos < x or (pos-x) % 2 != 0:\n    jumps += 1\n    pos += jumps"]


def _match_half_triangle_float(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Div)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.BinOp)
    )


def _fix_half_triangle_float(node, ctx):
    return [f"(({ctx.text(node.left.left)}*{ctx.text(node.left.left)} + {ctx.text(node.left.left)}) // 2)"]


def _match_add_input_misparse(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "x"
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _fix_add_abs_int(node, ctx):
    return [f"x = abs(int(input()))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="wrap_input_int_with_abs",
                match=_is_int_input,
                replace=_fix_abs_int_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_raw_input_is_not_solution",
                match=_match_print_raw_input,
                replace=_fix_print_raw_input,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="loop_should_use_parity_condition",
                match=_match_zero_based_loop,
                replace=_fix_zero_based_loop,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="replace_exact_reach_loop_with_parity_loop",
                match=_match_strict_progression_loop,
                replace=_fix_strict_progression_loop,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="triangle_number_division_should_be_integer",
                match=_match_half_triangle_float,
                replace=_fix_half_triangle_float,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="parse_input_as_integer",
                match=_match_add_input_misparse,
                replace=_fix_add_abs_int,
                symptoms=("wrong", "err:TypeError"),
            ),
        ]