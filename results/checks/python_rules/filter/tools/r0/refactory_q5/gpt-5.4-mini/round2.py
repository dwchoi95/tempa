from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_call_named(node, name):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name


def _is_expr_append_call(node, ctx):
    p = ctx.parent(node)
    return isinstance(p, ast.Call) and p.func is node and isinstance(ctx.parent(p), ast.Expr)


def _match_append_removed_value(node, ctx):
    return _is_expr_append_call(node, ctx) and isinstance(node, ast.Attribute) and node.attr == "append"


def _replace_append_removed_value(node, ctx):
    call = ctx.parent(node)
    arg = ctx.text(call.args[0]) if call.args else ""
    return [f"{ctx.text(node.value)}.append({arg})"]


def _match_return_wrong_list(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript) and ctx.text(node.value.value) != ctx.text(node.value.slice)


def _replace_return_wrong_list(node, ctx):
    return [f"return {ctx.text(node.value.value)}"]


def _match_return_list_slice_k(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript) and isinstance(node.value.slice, ast.Constant) and node.value.slice.value in (5, 4, 3, 1, -1)


def _replace_return_list_slice_k(node, ctx):
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _match_wrong_pop_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "pop" and len(node.args) == 1


def _replace_wrong_pop_call(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop({ctx.text(node.func.value)}.index({ctx.text(node.args[0])}))"]


def _match_remove_then_append_max(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "remove"


def _replace_remove_then_append_max(node, ctx):
    return [ctx.text(node).replace(".remove(max(", ".append(max(").replace("))", "))\n")]


def _match_append_loop_var(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and node.value.args and isinstance(node.value.args[0], ast.Name) and node.value.args[0].id in {"numbers", "number", "element", "elements", "i", "item", "x", "j", "k", "elements"}


def _replace_append_loop_var(node, ctx):
    return [f"{ctx.text(node.value.func.value)}.append(biggest)"]


def _match_newlist_append_lst(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and node.value.args and ctx.text(node.value.args[0]) == ctx.text(ctx.parent(node).targets[0]) if isinstance(ctx.parent(node), ast.Assign) else False


def _match_sort_call_self(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and ctx.text(node.func) == ctx.text(node)


class Fixer:
    def rules(self):
        return [
            Rewrite(name="append_the_maximum_not_the_removed_value", match=_match_append_removed_value, replace=_replace_append_removed_value, symptoms=("wrong",)),
            Rewrite(name="return_input_not_slice", match=_match_return_wrong_list, replace=_replace_return_wrong_list, symptoms=("wrong",)),
            Rewrite(name="slice_to_k_not_constant", match=_match_return_list_slice_k, replace=_replace_return_list_slice_k, symptoms=("wrong",)),
            Rewrite(name="pop_index_of_value", match=_match_wrong_pop_call, replace=_replace_wrong_pop_call, symptoms=("wrong",)),
            Rewrite(name="append_max_not_loop_variable", match=_match_append_loop_var, replace=_replace_append_loop_var, symptoms=("wrong",)),
        ]