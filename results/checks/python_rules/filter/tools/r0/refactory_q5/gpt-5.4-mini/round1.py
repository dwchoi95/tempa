from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_max_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "max"
        and len(node.args) == 1
    )


def _is_max_remove_then_append_wrong(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id in {"numbers", "number", "element", "ele", "biggest", "largest", "maximum", "minimum", "oldest", "big", "maxi"}
    )


def _fix_append_max(node, ctx):
    arg = ctx.text(node.value.args[0])
    return [f"{ctx.text(node.value.func.value)}.append({arg})"]


def _is_wrong_remove_append_max(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
        and len(node.value.args) == 1
        and _is_max_call(node.value.args[0], ctx)
    )


def _fix_remove_then_append(node, ctx):
    lst = ctx.text(node.value.func.value)
    arg = ctx.text(node.value.args[0].args[0])
    return [f"{lst}.append({arg})\n{lst}.remove({arg})"]


def _is_return_slice_wrong_k1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Sub)
        and isinstance(node.value.slice.right, ast.Constant)
        and node.value.slice.right.value == 1
    )


def _fix_slice_k(node, ctx):
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _is_return_lst_slice_k(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and _is_name(node.value.value, ctx, "lst")
    )


def _fix_return_sorted_var(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.FunctionDef):
        return []
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _is_append_remove_call(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Attribute)
        and node.value.args[0].func.attr == "remove"
    )


def _fix_append_removed_value(node, ctx):
    inner = node.value.args[0]
    return [f"{ctx.text(node.value.func.value)}.append({ctx.text(inner.func.value)})\n{ctx.text(inner.func.value)}.remove({ctx.text(inner.args[0])})"]


def _is_while_len_le_k(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.LtE)
        and isinstance(node.test.left, ast.Call)
        and isinstance(node.test.left.func, ast.Name)
        and node.test.left.func.id == "len"
    )


def _fix_while_len_lt(node, ctx):
    return [f"while {ctx.text(node.test.left)} < {ctx.text(node.test.comparators[0])}:" if False else f"while len({ctx.text(node.test.left.args[0])}) < {ctx.text(node.test.comparators[0])}:" ]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="append_the_maximum_not_the_removed_value",
                    match=_is_max_remove_then_append_wrong,
                    replace=_fix_append_max,
                    symptoms=("wrong",)),
            Rewrite(name="append_removed_call_result_should_append_value_then_remove",
                    match=_is_append_remove_call,
                    replace=_fix_append_removed_value,
                    symptoms=("wrong",)),
            Rewrite(name="return_list_slice_should_use_k_not_constant_one",
                    match=_is_return_slice_wrong_k1,
                    replace=_fix_slice_k,
                    symptoms=("wrong",)),
            Rewrite(name="return_lst_slice_should_use_sorted_result",
                    match=_is_return_lst_slice_k,
                    replace=_fix_return_sorted_var,
                    symptoms=("wrong",)),
            Rewrite(name="while_len_le_k_off_by_one",
                    match=_is_while_len_le_k,
                    replace=_fix_while_len_lt,
                    symptoms=("wrong",)),
        ]