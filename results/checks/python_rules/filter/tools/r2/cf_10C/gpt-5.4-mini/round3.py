from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_digital_root_base(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and isinstance(node.left, ast.Name)
        and node.left.id in {"x", "n", "num"}
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 9
    )


def _fix_digital_root_base(node, ctx):
    return [ctx.text(node.left) + " < 10"]


def _is_input_not_int(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input" and len(node.args) == 0


def _fix_input_to_int(node, ctx):
    return ["int(" + ctx.text(node) + ")"]


def _is_wrong_pairing_range(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 3
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[1], ast.Name)
        and isinstance(node.args[2], ast.Constant)
        and node.args[2].value == 1
    )


def _fix_pairing_range(node, ctx):
    return ["range(1, n+1)"]


def _is_wrong_printing_input(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print" and len(node.args) == 1 and isinstance(node.args[0], ast.Call) and isinstance(node.args[0].func, ast.Name) and node.args[0].func.id in {"d", "root", "digr"}


def _fix_printing_input(node, ctx):
    return [ctx.text(node)]


def _is_digitroot_solution_whole(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in {"d", "res", "s", "true_products"}
        and isinstance(node.value, ast.Constant)
        and node.value.value == 0
    )


def _fix_digitroot_solution_whole(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="digital_root_base_should_be_strict_lt_10",
                match=_is_bad_digital_root_base,
                replace=_fix_digital_root_base,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="input_should_be_converted_to_int",
                match=_is_input_not_int,
                replace=_fix_input_to_int,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="range_should_cover_all_values_inclusive",
                match=_is_wrong_pairing_range,
                replace=_fix_pairing_range,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_called_on_input_function_result",
                match=_is_wrong_printing_input,
                replace=_fix_printing_input,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="keep_existing_result_variable_initialization",
                match=_is_digitroot_solution_whole,
                replace=_fix_digitroot_solution_whole,
                symptoms=("wrong",),
            ),
        ]