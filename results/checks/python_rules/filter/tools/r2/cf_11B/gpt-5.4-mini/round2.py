from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_print_name(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print" and len(node.args) == 1


def _fix_print_name(node, ctx):
    arg = node.args[0]
    return [f"print({ctx.text(arg)})"]


def _is_input_to_int(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _fix_abs_int_input(node, ctx):
    return ["abs(int(input()))"]


def _is_int_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _fix_abs_wrap(node, ctx):
    return [f"abs({ctx.text(node)})"]


def _is_while_not_eq_zero(node, ctx):
    return isinstance(node, ast.While) and isinstance(node.test, ast.Compare) and len(node.test.ops) == 1 and isinstance(node.test.ops[0], ast.NotEq)


def _fix_while_condition(node, ctx):
    return [f"while pos < x or (pos-x) % 2 != 0:"]


def _is_map_int_input_print(node, ctx):
    return isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "map"


def _fix_map_to_abs_int(node, ctx):
    return ["x = abs(int(input()))"]


def _is_wrong_jump_loop(node, ctx):
    return isinstance(node, ast.While) and isinstance(node.test, ast.Compare) and len(node.test.ops) == 1 and isinstance(node.test.ops[0], ast.NotEq)


def _fix_jump_loop(node, ctx):
    return ["while pos < x or (pos-x) % 2 != 0:"]


def _is_bad_triangle_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _fix_triangle_compare(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="print_variable_as_result", match=_is_print_name, replace=_fix_print_name, symptoms=("wrong",)),
            Rewrite(name="wrap_input_with_abs", match=_is_input_to_int, replace=_fix_abs_int_input, symptoms=("wrong",)),
            Rewrite(name="abs_of_raw_int_input", match=_is_int_input, replace=_fix_abs_wrap, symptoms=("wrong",)),
            Rewrite(name="wrong_loop_condition_for_jump_parity", match=_is_while_not_eq_zero, replace=_fix_while_condition, symptoms=("wrong",)),
            Rewrite(name="map_input_instead_of_integer_input", match=_is_map_int_input_print, replace=_fix_map_to_abs_int, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="strict_lt_should_be_lte", match=_is_bad_triangle_compare, replace=_fix_triangle_compare, symptoms=("wrong",)),
        ]