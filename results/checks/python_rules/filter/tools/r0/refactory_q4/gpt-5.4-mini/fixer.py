from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_sort_age(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _is_reverse_call_expr(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "reverse"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _fix_reverse_return(node, ctx):
    return [ctx.text(node.func.value) + "[::-1]"]


def _fix_reverse_stmt(node, ctx):
    return [ctx.text(node.func.value) + ".reverse()\nreturn " + ctx.text(node.func.value)]


def _is_wrong_list_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"sort", "lst1", "newlst", "final", "output", "result", "new_list", "sorted", "sort1"}


def _fix_return_name(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.FunctionDef) and ctx.field(node) == "body":
        return []
    return [ctx.text(node)]


def _is_cmp_age(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.comparators[0], ast.Subscript)
    )


def _flip_compare(node, ctx):
    op = node.ops[0]
    if isinstance(op, ast.Lt):
        return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]
    if isinstance(op, ast.Gt):
        return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]
    if isinstance(op, ast.LtE):
        return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]
    if isinstance(op, ast.GtE):
        return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]
    return []


def _is_remove_name_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "remove"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _fix_remove_name_call(node, ctx):
    return [ctx.text(node.func.value) + ".remove(" + ctx.text(node.args[0]) + ")"]


def _is_pop_index_stmt(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "pop"
        and len(node.value.args) == 1
    )


def _fix_pop_to_del(node, ctx):
    return ["del " + ctx.text(node.value.func.value) + "[" + ctx.text(node.value.args[0]) + "]"]


def _is_append_name_instead_of_item(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Name)


def _fix_append_name(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="reverse_call_should_return_reversed_slice", match=_is_reverse_call_expr, replace=_fix_reverse_return, symptoms=("wrong",)),
            Rewrite(name="reverse_method_needs_followup_return", match=_is_reverse_call_expr, replace=_fix_reverse_stmt, symptoms=("wrong",)),
            Rewrite(name="return_wrong_list_variable", match=_is_wrong_list_name, replace=_fix_return_name, symptoms=("wrong",)),
            Rewrite(name="compare_age_direction", match=_is_cmp_age, replace=_flip_compare, symptoms=("wrong",)),
            Rewrite(name="remove_selected_element_not_iterator_name", match=_is_remove_name_call, replace=_fix_remove_name_call, symptoms=("wrong",)),
            Rewrite(name="pop_index_should_be_del_index", match=_is_pop_index_stmt, replace=_fix_pop_to_del, symptoms=("wrong",)),
        ]