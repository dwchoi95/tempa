from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_call_name(node, ctx, name):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_append_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
    )


def _replace_append_arg_with_max(node, ctx):
    return [f"{ctx.text(node.func.value)}.append(max({ctx.text(node.args[0])}))"]


def _replace_append_arg_with_name(node, ctx, name):
    return [f"{ctx.text(node.func.value)}.append({name})"]


def _is_return_slice_constant(node, ctx, value):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.slice, ast.Constant)
        and node.slice.value == value
    )


def _replace_slice_with_k(node, ctx):
    return [f"{ctx.text(node.value)}[:k]"]


def _is_len_compare_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.ops[0], ast.LtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Name)
        and node.comparators[0].id == "k"
    )


def _replace_lte_with_lt(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]


def _is_wrong_return_lst_slice(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript) and isinstance(node.value.value, ast.Name) and node.value.value.id == "lst"


def _replace_return_lst_slice_with_result(node, ctx):
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _is_append_list_instead_of_value(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _replace_append_with_maximum_var(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.Expr):
        return [f"{ctx.text(node.func.value)}.append(maximum)"]
    return [f"{ctx.text(node.func.value)}.append(maximum)"]


def _is_return_result_kplus1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Add)
    )


def _replace_kplus1_with_k(node, ctx):
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _is_append_remove_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr == "remove"
    )


def _replace_append_remove_with_arg(node, ctx):
    return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0].args[0].func.value)})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="append_maximum_instead_of_removed_value",
                match=lambda node, ctx: _is_append_call(node, ctx)
                and isinstance(node.args[0], ast.Name)
                and node.args[0].id in {"a", "maximum", "maxi", "big", "biggest", "element", "largest", "highest"},
                replace=lambda node, ctx: [f"{ctx.text(node.func.value)}.append(max({ctx.text(node.args[0])}))"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_wrong_variable_name",
                match=lambda node, ctx: _is_append_call(node, ctx)
                and isinstance(node.args[0], ast.Name)
                and node.args[0].id in {"oldest", "smallest", "numbers", "number", "numberss", "x", "y", "i", "lst"},
                replace=lambda node, ctx: [f"{ctx.text(node.func.value)}.append(biggest)"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_input_list_slice",
                match=_is_wrong_return_lst_slice,
                replace=lambda node, ctx: [f"return {ctx.text(node.value.value)}[:k]"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="slice_constant_five_to_k",
                match=lambda node, ctx: _is_return_slice_constant(node, ctx, 5),
                replace=_replace_slice_with_k,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="slice_k_plus_one_to_k",
                match=_is_return_result_kplus1,
                replace=_replace_kplus1_with_k,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_compare_lte_to_lt",
                match=_is_len_compare_off_by_one,
                replace=_replace_lte_with_lt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_removed_value_instead_of_none",
                match=_is_append_remove_call,
                replace=lambda node, ctx: [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0].args[0])})"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_value_not_removed_result",
                match=lambda node, ctx: isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "append"
                and len(node.args) == 1
                and isinstance(node.args[0], ast.Call)
                and isinstance(node.args[0].func, ast.Name)
                and node.args[0].func.id == "max",
                replace=lambda node, ctx: [ctx.text(node)],
                symptoms=("wrong",),
            ),
        ]