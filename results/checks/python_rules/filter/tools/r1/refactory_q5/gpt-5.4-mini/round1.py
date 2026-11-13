from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_max_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "max" and len(node.args) == 1


def _is_min_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "min" and len(node.args) == 1


def _is_len_cmp(node, ctx):
    return isinstance(node, ast.Compare) and isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name) and node.left.func.id == "len"


def _fix_k_slice(node, ctx):
    return [ctx.text(node.value) + "[:k]"]


def _fix_k_plus1_slice(node, ctx):
    return [ctx.text(node.value) + "[:k]"]


def _fix_pop_arg_max(node, ctx):
    return [ctx.text(node.value) + ".pop(" + ctx.text(node.value) + ".index(max(" + ctx.text(node.value) + ")))"]


def _fix_remove_then_append(node, ctx):
    parent = ctx.parent(node)
    return [ctx.text(node) + "\n" + ctx.text(parent.body[parent.body.index(node) + 1]).replace(ctx.text(parent.body[parent.body.index(node) + 1]), "")] if False else []


def _is_return_slice_five(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript) and isinstance(node.value.slice, ast.Constant) and node.value.slice.value == 5


def _replace_return_k_slice(node, ctx):
    return ["return " + ctx.text(node.value.value) + "[:k]"]


def _is_return_k_plus1(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Subscript) and isinstance(node.value.slice, ast.BinOp) and isinstance(node.value.slice.op, ast.Add)


def _replace_return_k_plus1(node, ctx):
    return ["return " + ctx.text(node.value.value) + "[:k]"]


def _is_assign_sort_call_self(node, ctx):
    return (isinstance(node, ast.Assign) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name)
            and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
            and any(isinstance(a, ast.Name) and a.id == node.targets[0].id for a in node.value.args))


def _fix_self_call(node, ctx):
    return [ctx.text(node.value.func) + "(" + ", ".join(ctx.text(a) for a in node.value.args if not (isinstance(a, ast.Name) and a.id == ctx.text(node.targets[0]))) + ")"]


def _is_wrong_append_var(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _fix_append_max(node, ctx):
    arg = node.value.args[0] if node.value.args else None
    if isinstance(arg, ast.Name):
        return [ctx.text(node.value.func.value) + ".append(" + ctx.text(arg) + ")"]
    return []


def _is_bad_list_remove_return(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Call) and isinstance(node.value.args[0].func, ast.Attribute) and node.value.args[0].func.attr == "remove"


def _fix_remove_append(node, ctx):
    return [ctx.text(node.value.func.value) + ".append(max(" + ctx.text(node.value.func.value) + "))\n" + ctx.text(node.value.args[0].func.value) + ".remove(max(" + ctx.text(node.value.args[0].func.value) + "))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_slice_5_to_k", match=_is_return_slice_five, replace=_replace_return_k_slice, symptoms=("wrong",)),
            Rewrite(name="return_slice_k_plus_one_to_k", match=_is_return_k_plus1, replace=_replace_return_k_plus1, symptoms=("wrong",)),
            Rewrite(name="self_call_instead_of_recursive_list", match=_is_assign_sort_call_self, replace=_fix_self_call, symptoms=("err:TypeError", "wrong")),
        ]