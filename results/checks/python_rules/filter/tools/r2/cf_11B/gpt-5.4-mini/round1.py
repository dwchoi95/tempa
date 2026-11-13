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


def _replace_with_abs_int_input(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


def _is_input_without_int(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _replace_map_input(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


def _is_while_neq_x(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
    )


def _replace_while_guard(node, ctx):
    if not isinstance(node.test, ast.Compare) or len(node.test.ops) != 1:
        return []
    left = ctx.text(node.test.left)
    right = ctx.text(node.test.comparators[0])
    return [f"while {left} < {right} or ({left} - {right}) % 2 != 0:"]


def _is_simple_pos_update_if(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], (ast.Lt, ast.Gt, ast.Eq))
        and len(node.body) == 1
        and isinstance(node.body[0], ast.Assign)
        and len(node.body[0].targets) == 1
        and isinstance(node.body[0].targets[0], ast.Name)
    )


def _replace_simple_pos_update_if(node, ctx):
    return [f"{ctx.text(node.body[0].targets[0])} += {ctx.text(node.test.comparators[0])}"]


def _is_triangular_float_div(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)


def _replace_div_with_floor(node, ctx):
    return [f"({ctx.text(node.left)}) // ({ctx.text(node.right)})"]


def _is_print_count(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _replace_print_count(node, ctx):
    return [f"print({ctx.text(node.value.args[0])})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="use_abs_int_input_for_distance_problem",
                match=_is_abs_input_assign,
                replace=_replace_with_abs_int_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="map_input_is_not_parsing_integer",
                match=_is_input_without_int,
                replace=_replace_map_input,
                symptoms=("err:ValueError", "wrong"),
            ),
            Rewrite(
                name="while_neq_should_be_distance_and_parity_guard",
                match=_is_while_neq_x,
                replace=_replace_while_guard,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="update_position_with_jump_length",
                match=_is_simple_pos_update_if,
                replace=_replace_simple_pos_update_if,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="avoid_float_division_in_arithmetic",
                match=_is_triangular_float_div,
                replace=_replace_div_with_floor,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="print_variable_as_result",
                match=_is_print_count,
                replace=_replace_print_count,
                symptoms=("wrong",),
            ),
        ]