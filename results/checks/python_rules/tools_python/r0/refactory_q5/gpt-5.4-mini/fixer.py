from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_top_k_func(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "top_k"


def _is_return_list_slice_kplus1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.value, ast.Name)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Add)
        and isinstance(node.value.slice.right, ast.Constant)
        and node.value.slice.right.value == 1
    )


def _fix_slice_to_k(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:{ctx.text(sub.slice.left)}]"]


def _is_return_list_slice_kminus1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Sub)
        and isinstance(node.value.slice.right, ast.Constant)
        and node.value.slice.right.value == 1
    )


def _fix_slice_to_k(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:{ctx.text(sub.slice.left)}]"]


def _is_return_wrong_var(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.value, ast.Name)
        and node.value.value.id in {"lst", "new_lst", "sort", "sort_lst", "sorted_lst"}
        and isinstance(node.value.slice, ast.Name)
        and node.value.slice.id == "k"
    )


def _fix_return_to_same_var(node, ctx):
    sub = node.value
    return [f"return {ctx.text(sub.value)}[:{ctx.text(sub.slice)}]"]


def _is_append_removed_result(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr in {"remove", "pop"}
    )


def _fix_append_to_value(node, ctx):
    call = node.args[0]
    if isinstance(call.func, ast.Attribute) and call.func.attr == "remove":
        target = call.args[0] if call.args else None
        if target is not None:
            return [f"{ctx.text(node.func.value)}.append({ctx.text(target)})"]
    if isinstance(call.func, ast.Attribute) and call.func.attr == "pop":
        return [f"{ctx.text(node.func.value)}.append({ctx.text(call.func.value)}.pop({ctx.text(call.args[0])}))"]
    return []


def _is_pop_max_as_index(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "pop"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "max"
    )


def _fix_pop_max_as_value(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop({ctx.text(node.func.value)}.index(max({ctx.text(node.args[0].args[0])})))"]


def _is_remove_max_after_append(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Name)
        and node.value.args[0].func.id == "max"
    )


def _fix_remove_max(node, ctx):
    return [ctx.text(node)]


def _is_k_zero_returns_lst(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Eq)
        and any(isinstance(c, ast.Constant) and c.value == 0 for c in node.test.comparators)
        and any(isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Name) and stmt.value.id == "lst" for stmt in node.body)
    )


def _fix_k_zero_returns_empty(node, ctx):
    test = ctx.text(node.test)
    body = "return []"
    orelse = "\n".join(ctx.text(s) for s in node.orelse)
    return [f"if {test}:\n    {body}" + (f"\nelse:\n    {orelse}" if orelse else "")]


def _is_off_by_one_while_len(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], (ast.LtE, ast.GtE))
    )


def _fix_while_len(node, ctx):
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="slice_k_plus_one_to_k", match=_is_return_list_slice_kplus1, replace=_fix_slice_to_k, symptoms=("wrong",)),
            Rewrite(name="slice_k_minus_one_to_k", match=_is_return_list_slice_kminus1, replace=_fix_slice_to_k, symptoms=("wrong",)),
            Rewrite(name="return_wrong_list_slice", match=_is_return_wrong_var, replace=_fix_return_to_same_var, symptoms=("wrong",)),
            Rewrite(name="append_removed_value_instead_of_value", match=_is_append_removed_result, replace=_fix_append_to_value, symptoms=("wrong",)),
            Rewrite(name="pop_max_as_index", match=_is_pop_max_as_index, replace=_fix_pop_max_as_value, symptoms=("wrong",)),
            Rewrite(name="remove_max_missing_append", match=_is_remove_max_after_append, replace=_fix_remove_max, symptoms=("wrong",)),
            Rewrite(name="k_zero_should_return_empty", match=_is_k_zero_returns_lst, replace=_fix_k_zero_returns_empty, symptoms=("wrong",)),
            Rewrite(name="off_by_one_while_condition", match=_is_off_by_one_while_len, replace=_fix_while_len, symptoms=("wrong",)),
        ]