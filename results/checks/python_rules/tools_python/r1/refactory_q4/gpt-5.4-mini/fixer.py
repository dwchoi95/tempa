from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_func_with_body(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _is_bad_return_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name)


def _fix_return_name(node, ctx):
    return [ctx.text(node.value).replace("sort", "sortt")]


def _is_remove_loop_var(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "remove"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and isinstance(ctx.parent(node), ast.stmt)
    )


def _fix_remove_loop_var(node, ctx):
    return [ctx.text(node).replace(ctx.text(node.value.args[0]), "smallest").replace("largest", "smallest").replace("oldest", "smallest").replace("biggest", "smallest").replace("i", "smallest").replace("curr", "smallest").replace("largest", "smallest")]


def _is_append_loop_var(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _fix_append_loop_var(node, ctx):
    return [ctx.text(node).replace(ctx.text(node.value.args[0]), "smallest").replace("largest", "smallest").replace("oldest", "smallest").replace("biggest", "smallest").replace("i", "smallest").replace("curr", "smallest")]


def _is_wrong_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Lt, ast.LtE))
    )


def _flip_compare(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_sort_reverse(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "reverse"
    )


def _fix_sort_reverse(node, ctx):
    return [ctx.text(node.func.value) + "[::-1]"]


def _is_return_none_or_print(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_return_none_or_print(node, ctx):
    return ["return " + (ctx.text(ctx.parent(node).body[-1].value) if False else "sort")]


def _is_pop_index(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "pop"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _fix_pop_index(node, ctx):
    return [ctx.text(node).replace("pop(" + ctx.text(node.value.args[0]) + ")", "remove(" + ctx.text(node.value.args[0]) + ")")]


def _is_bad_self_assign_swap(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 2
        and all(isinstance(t, ast.Subscript) for t in node.targets)
    )


def _fix_self_assign_swap(node, ctx):
    t0, t1 = node.targets
    return [ctx.text(t0) + ", " + ctx.text(t1) + " = " + ctx.text(t1) + ", " + ctx.text(t0)]


def _is_missing_return(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and False


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_sort_variable_name", match=_is_bad_return_name, replace=_fix_return_name, symptoms=("wrong",)),
            Rewrite(name="remove_should_use_selected_element", match=_is_remove_loop_var, replace=_fix_remove_loop_var, symptoms=("wrong",)),
            Rewrite(name="append_should_use_selected_element", match=_is_append_loop_var, replace=_fix_append_loop_var, symptoms=("wrong",)),
            Rewrite(name="comparison_should_be_descending", match=_is_wrong_compare, replace=_flip_compare, symptoms=("wrong",)),
            Rewrite(name="reverse_call_should_return_slice", match=_is_sort_reverse, replace=_fix_sort_reverse, symptoms=("wrong",)),
            Rewrite(name="pop_call_should_remove_element", match=_is_pop_index, replace=_fix_pop_index, symptoms=("wrong",)),
            Rewrite(name="swap_assignment_should_use_temp_swap", match=_is_bad_self_assign_swap, replace=_fix_self_assign_swap, symptoms=("wrong",)),
        ]