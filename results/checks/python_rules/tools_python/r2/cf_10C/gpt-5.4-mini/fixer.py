from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_int_input_assign(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "int"
        and len(node.value.args) == 1
        and _is_input_call(node.value.args[0], ctx)
    )


def _fix_int_input_assign(node, ctx):
    return [f"{ctx.text(node.targets[0])} = int(input())"]


def _is_input_to_int_expr(node, ctx):
    return _is_input_call(node, ctx) and isinstance(ctx.parent(node), ast.Call)


def _fix_input_to_int_expr(node, ctx):
    return ["int(input())"]


def _is_len_str_compare_neq_one(node, ctx):
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
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_len_str_compare_neq_one(node, ctx):
    return [f"{ctx.text(node.left)} == 1"]


def _is_for_range_start_1(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name)
        and node.iter.func.id == "range"
        and len(node.iter.args) >= 1
        and isinstance(node.iter.args[0], ast.Constant)
        and node.iter.args[0].value == 1
    )


def _fix_for_range_start_1(node, ctx):
    call = node.iter
    args = [ctx.text(a) for a in call.args]
    if len(args) == 1:
        new_iter = "range(0, " + args[0] + ")"
    else:
        new_iter = "range(0, " + ", ".join(args[1:]) + ")"
    return [f"for {ctx.text(node.target)} in {new_iter}:" + ("\n" + ctx.text(node.body[0]) if node.body else "")]


def _is_range_n_plus_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Add)
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _fix_range_n_plus_one(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1].left)})"]


def _is_eq_zero_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Compare)
        and len(node.value.ops) == 1
        and isinstance(node.value.ops[0], ast.Eq)
        and len(node.value.comparators) == 1
        and isinstance(node.value.comparators[0], ast.Constant)
        and node.value.comparators[0].value == 0
    )


def _fix_eq_zero_return(node, ctx):
    return [f"return {ctx.text(node.value.left)}"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="convert_input_to_int",
                match=_is_input_to_int_expr,
                replace=_fix_input_to_int_expr,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="wrap_input_with_int",
                match=_is_int_input_assign,
                replace=_fix_int_input_assign,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="len_str_neq_one_should_be_eq_one",
                match=_is_len_str_compare_neq_one,
                replace=_fix_len_str_compare_neq_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_start_one_off_by_one",
                match=_is_for_range_start_1,
                replace=_fix_for_range_start_1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_plus_one",
                match=_is_range_n_plus_one,
                replace=_fix_range_n_plus_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_comparison_to_value",
                match=_is_eq_zero_return,
                replace=_fix_eq_zero_return,
                symptoms=("wrong",),
            ),
        ]