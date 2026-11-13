from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_max_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "max" and len(node.args) == 1


def _is_min_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "min" and len(node.args) == 1


def _is_len_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1


def _replace_wrong_append_max(node, ctx):
    return [ctx.text(node.value) + ".append(max(" + ctx.text(node.value) + "))"]


def _match_append_wrong_arg(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and _is_name(node.value.args[0], ctx, "lst")
    )


def _match_append_name_mismatch(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id in {"oldest", "numbers", "number", "element", "elements", "i"}
    )


def _replace_append_with_arg(node, ctx):
    return [ctx.text(node.value.func.value) + ".append(" + ctx.text(node.value.args[0]) + ")"]


def _match_return_lst_slice(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and _is_name(node.value.value, ctx, "lst")
    )


def _replace_return_sort_slice(node, ctx):
    return ["return " + ctx.text(node.value.value) + "[:k]"]


def _match_return_wrong_slice_plus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.BinOp)
        and isinstance(node.value.slice.op, ast.Add)
    )


def _replace_return_slice_k(node, ctx):
    return ["return " + ctx.text(node.value.value) + "[:k]"]


def _match_missing_return(node, ctx):
    return isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id in {"new_lst", "newlist", "result", "sort_k", "new"} for t in node.targets)


def _insert_return_node(node, ctx):
    return [ctx.text(node) + "\nreturn " + ctx.text(node.targets[0])]


def _match_for_pop_max(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "pop"
        and len(node.args) == 1
        and _is_max_call(node.args[0], ctx)
    )


def _replace_pop_max(node, ctx):
    return [ctx.text(node.func.value) + ".pop(" + ctx.text(node.func.value) + ".index(max(" + ctx.text(node.func.value) + ")))"]


def _match_remove_then_append_max(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
        and len(node.value.args) == 1
        and _is_max_call(node.value.args[0], ctx)
    )


def _replace_remove_then_append_max(node, ctx):
    return [ctx.text(node.value.func.value) + ".append(max(" + ctx.text(node.value.func.value) + "))\n" + ctx.text(node)]


def _match_k_plus_one(node, ctx):
    return isinstance(node, ast.Subscript) and isinstance(node.slice, ast.BinOp) and isinstance(node.slice.op, ast.Add) and _is_name(node.slice.left, ctx, "k")


def _replace_k_slice(node, ctx):
    return [ctx.text(node.value) + "[:k]"]


def _match_range_k_minus_one(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range" and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp) and isinstance(node.args[0].op, ast.Sub) and _is_name(node.args[0].left, ctx, "k") and isinstance(node.args[0].right, ast.Constant) and node.args[0].right.value == 1


def _replace_range_k(node, ctx):
    return ["range(k)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="append_list_instead_of_maximum", match=_match_append_wrong_arg, replace=_replace_append_with_arg, symptoms=("wrong",)),
            Rewrite(name="append_wrong_variable_name", match=_match_append_name_mismatch, replace=_replace_append_with_arg, symptoms=("wrong",)),
            Rewrite(name="return_input_list_slice", match=_match_return_lst_slice, replace=_replace_return_sort_slice, symptoms=("wrong",)),
            Rewrite(name="off_by_one_slice_k_plus_one", match=_match_return_wrong_slice_plus_one, replace=_replace_return_slice_k, symptoms=("wrong",)),
            Rewrite(name="missing_return_statement", match=_match_missing_return, replace=_insert_return_node, symptoms=("wrong",)),
            Rewrite(name="pop_max_is_index_not_value", match=_match_for_pop_max, replace=_replace_pop_max, symptoms=("err:TypeError", "wrong")),
            Rewrite(name="append_after_remove_max", match=_match_remove_then_append_max, replace=_replace_remove_then_append_max, symptoms=("wrong",)),
            Rewrite(name="slice_k_plus_one_to_k", match=_match_k_plus_one, replace=_replace_k_slice, symptoms=("wrong",)),
            Rewrite(name="range_k_minus_one_to_k", match=_match_range_k_minus_one, replace=_replace_range_k, symptoms=("wrong",)),
        ]