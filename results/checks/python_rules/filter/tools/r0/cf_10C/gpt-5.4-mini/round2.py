from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _wrap_int_input(node, ctx):
    return [f"int({ctx.text(node)})"]


def _is_print_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 1
        and _is_input_call(node.args[0], ctx)
    )


def _print_int_input(node, ctx):
    return [f"print(int({ctx.text(node.args[0])}))"]


def _is_len_str_neq_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Call)
        and isinstance(node.left.args[0].func, ast.Name)
        and node.left.args[0].func.id == "str"
        and len(node.left.args[0].args) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _len_str_eq_1(node, ctx):
    return [f"{ctx.text(node.left)} == 1"]


def _is_range_start_1_end_nplus1(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 3
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[2], ast.Constant)
        and node.args[2].value == 1
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Add)
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _range_start_0_end_n(node, ctx):
    return [f"range(0, {ctx.text(node.args[1].left)})"]


def _is_leq_n_plus_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and isinstance(node.comparators[0], ast.BinOp)
        and isinstance(node.comparators[0].op, ast.Add)
        and isinstance(node.comparators[0].right, ast.Constant)
        and node.comparators[0].right.value == 1
    )


def _lt_n(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0].left)}"]


def _is_eq_zero(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 0
    )


def _neq_zero(node, ctx):
    return [f"{ctx.text(node.left)} != 0"]


def _is_assign_zero(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.Constant)
        and node.value.value == 0
    )


def _assign_one(node, ctx):
    return [f"{ctx.text(node.targets[0])} = 1"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_needs_int_conversion",
                match=_is_input_call,
                replace=_wrap_int_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="print_input_needs_int_conversion",
                match=_is_print_input_call,
                replace=_print_int_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="len_str_should_stop_at_one_digit",
                match=_is_len_str_neq_1,
                replace=_len_str_eq_1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_should_start_at_one_and_include_n",
                match=_is_range_start_1_end_nplus1,
                replace=_range_start_0_end_n,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_n_plus_one_should_be_n",
                match=_is_leq_n_plus_1,
                replace=_lt_n,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="eq_zero_should_be_neq_zero",
                match=_is_eq_zero,
                replace=_neq_zero,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="counter_should_start_at_one",
                match=_is_assign_zero,
                replace=_assign_one,
                symptoms=("wrong",),
            ),
        ]