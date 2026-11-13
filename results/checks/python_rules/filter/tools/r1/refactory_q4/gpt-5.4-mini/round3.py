from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_function_named(node, ctx, name="sort_age"):
    return isinstance(node, ast.FunctionDef) and node.name == name


def _is_return_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name)


def _replace_return_name_with_value(node, ctx):
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef):
        return []
    returns = []
    for stmt in func.body:
        if isinstance(stmt, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == node.value.id for t in stmt.targets
        ):
            returns.append(stmt)
    if not returns:
        return []
    last_assign = returns[-1]
    if isinstance(last_assign.value, ast.List) and len(last_assign.targets) == 1:
        return [f"return {ctx.text(last_assign.targets[0])}"]
    return []


def _is_wrong_tuple_var_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "sort"


def _fix_return_sort(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return []
    for stmt in parent.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1:
            tgt = stmt.targets[0]
            if isinstance(tgt, ast.Name) and tgt.id in {"sortt", "output", "new_list", "sorted_lst", "sort_list", "result", "new", "a", "rslt", "lst1"}:
                return [f"return {ctx.text(tgt)}"]
    return []


def _is_bad_remove_append_pair(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr in {"append", "remove"}


def _fix_append_remove_selected(node, ctx):
    call = node.value
    if not (isinstance(call.func, ast.Attribute) and len(call.args) == 1):
        return []
    arg = call.args[0]
    if isinstance(arg, ast.Name):
        if call.func.attr == "remove" and arg.id in {"i", "j", "counter", "smallest", "largest", "biggest", "oldest"}:
            return [f"{ctx.text(call.func.value)}.remove({ctx.text(arg)})"]
        if call.func.attr == "append" and arg.id in {"i", "j", "counter", "smallest", "largest", "biggest", "oldest"}:
            return [f"{ctx.text(call.func.value)}.append({ctx.text(arg)})"]
    return []


def _is_list_pop_noarg(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "pop" and len(node.args) == 0


def _fix_pop0(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop(0)"]


def _is_reverse_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_reverse_return(node, ctx):
    return [ctx.text(node.value.func.value) + "[::-1]"]


def _is_compare_age_wrong_dir(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE))


def _flip_compare(node, ctx):
    op = node.ops[0]
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if isinstance(op, ast.Lt):
        return [f"{left} > {right}"]
    if isinstance(op, ast.Gt):
        return [f"{left} < {right}"]
    if isinstance(op, ast.LtE):
        return [f"{left} >= {right}"]
    if isinstance(op, ast.GtE):
        return [f"{left} <= {right}"]
    return []


def _is_bool_name_wrong(node, ctx):
    return isinstance(node, ast.Name) and node.id in {"sort", "new", "result", "output", "new_list", "sorted_lst", "sort_list", "a", "rslt", "final"} and isinstance(ctx.parent(node), ast.Return)


def _return_same_name(node, ctx):
    return [f"return {node.id}"]


def _is_bare_pass(node, ctx):
    return isinstance(node, ast.Pass)


def _delete_pass(node, ctx):
    return [""]


class Fixer:
    def rules(self):
        return [
            Rewrite("fix_return_variable_name", _is_wrong_tuple_var_return, _fix_return_sort, ("wrong",)),
            Rewrite("fix_return_to_assigned_list", _is_return_name, _replace_return_name_with_value, ("wrong",)),
            Rewrite("remove_selected_variable_use", _is_bad_remove_append_pair, _fix_append_remove_selected, ("wrong",)),
            Rewrite("fix_pop_noarg", _is_list_pop_noarg, _fix_pop0, ("wrong", "err:TypeError")),
            Rewrite("fix_reverse_return", _is_reverse_return, _fix_reverse_return, ("wrong",)),
            Rewrite("flip_age_comparison", _is_compare_age_wrong_dir, _flip_compare, ("wrong",)),
            Rewrite("delete_pass", _is_bare_pass, _delete_pass, ("wrong",)),
        ]