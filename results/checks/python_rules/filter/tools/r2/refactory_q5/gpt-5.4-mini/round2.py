from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_return_slice_wrong_bound(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Add)
        and isinstance(node.value.slice.right, ast.Constant)
        and node.value.slice.right.value == 1
    )


def _fix_return_slice_wrong_bound(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:{ctx.text(sub.slice.left)}]"]


def _is_return_wrong_name(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Name)
        and ctx.text(node.value) in {"lst", "list", "new_lst", "newlist"}
    )


def _fix_return_wrong_name(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.FunctionDef):
        return []
    return [f"return {ctx.text(node.value)}"]


def _is_append_var_mismatch(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id not in {node.value.func.value.id if isinstance(node.value.func.value, ast.Name) else ""}
    )


def _fix_append_var_mismatch(node, ctx):
    call = node.value
    target = ctx.text(call.func.value)
    return [f"{target}.append({target})"]


def _is_append_wrong_name(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _fix_append_wrong_name(node, ctx):
    call = node.value
    if isinstance(call.func.value, ast.Name) and isinstance(call.args[0], ast.Name):
        lhs = ctx.text(call.func.value)
        rhs = ctx.text(call.args[0])
        if lhs != rhs:
            return [f"{lhs}.append({lhs})"]
    return []


def _is_remove_append_pair(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
    )


def _fix_remove_append_pair(node, ctx):
    call = node.value
    if isinstance(call.func.value, ast.Name):
        name = ctx.text(call.func.value)
        return [f"{name}.append(max({name}))\n{name}.remove(max({name}))"]
    return []


def _is_slice_k_plus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Add)
        and isinstance(node.value.slice.right, ast.Constant)
        and node.value.slice.right.value == 1
    )


def _fix_slice_k_plus_one(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:{ctx.text(sub.slice.left)}]"]


def _is_slice_constant_five(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.Constant)
        and node.value.slice.value == 5
    )


def _fix_slice_constant_five(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:k]"]


def _is_pop_max_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "pop"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and ctx.text(node.args[0]) == "largest"
    )


def _fix_pop_max_call(node, ctx):
    return [f"{ctx.text(node.func.value)}.remove({ctx.text(node.args[0])})"]


def _is_pop_index_max(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "pop"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and ctx.text(node.args[0].func) == "max"
    )


def _fix_pop_index_max(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop({ctx.text(node.func.value)}.index(max({ctx.text(node.func.value)})))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_slice_k_plus_one", match=_is_slice_k_plus_one, replace=_fix_slice_k_plus_one, symptoms=("wrong",)),
            Rewrite(name="return_slice_constant_five", match=_is_slice_constant_five, replace=_fix_slice_constant_five, symptoms=("wrong",)),
            Rewrite(name="return_variable_itself", match=_is_return_wrong_name, replace=_fix_return_wrong_name, symptoms=("wrong",)),
            Rewrite(name="append_loop_variable_instead_of_max", match=_is_append_var_mismatch, replace=_fix_append_var_mismatch, symptoms=("wrong",)),
            Rewrite(name="remove_then_append_max", match=_is_remove_append_pair, replace=_fix_remove_append_pair, symptoms=("wrong",)),
            Rewrite(name="pop_with_max_value_instead_of_index", match=_is_pop_max_call, replace=_fix_pop_max_call, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="pop_index_of_max", match=_is_pop_index_max, replace=_fix_pop_index_max, symptoms=("err:TypeError", "wrong")),
        ]