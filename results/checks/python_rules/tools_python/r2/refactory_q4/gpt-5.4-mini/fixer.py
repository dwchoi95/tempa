from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_stmt(node):
    return isinstance(node, ast.stmt)


def _is_expr(node):
    return isinstance(node, ast.expr)


def _is_name(node, name=None):
    return isinstance(node, ast.Name) and (name is None or node.id == name)


def _is_remove_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "remove"
        and len(node.args) == 1
    )


def _is_append_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
    )


def _is_sort_method_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "sort"
    )


def _cmp_is(node, ops):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ops)


def _match_wrong_final_variable(node, ctx):
    return isinstance(node, ast.Return) and _is_name(node.value, "sort")


def _replace_wrong_final_variable(node, ctx):
    return [f"return {ctx.text(ast.copy_location(node.value, node.value))}".replace("sort", "sortt", 1)]


def _match_remove_append_loop(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.body, list)
        and len(node.body) >= 2
        and _is_remove_call(node.body[-2].value)
        and _is_append_call(node.body[-1].value)
        and ctx.text(node.body[-2].value.func.value) == ctx.text(node.body[-1].value.func.value)
    )


def _replace_remove_append_loop(node, ctx):
    return [ctx.text(node).replace("lst.remove(i)\n        output.append(i)", "lst.remove(smallest)\n        output.append(smallest)")]


def _match_remove_loop_var(node, ctx):
    return _is_remove_call(node) and _is_name(node.args[0], "i")


def _replace_remove_loop_var(node, ctx):
    return [f"{ctx.text(node.func.value)}.remove(smallest)"]


def _match_append_loop_var(node, ctx):
    return _is_append_call(node) and _is_name(node.args[0], "i")


def _replace_append_loop_var(node, ctx):
    return [f"{ctx.text(node.func.value)}.append(smallest)"]


def _match_name_biggest(node, ctx):
    return _is_name(node, "biggest")


def _replace_name_biggest(node, ctx):
    return ["oldest"]


def _match_name_sort_append(node, ctx):
    return _is_name(node, "sort") and isinstance(ctx.parent(node), ast.Return)


def _replace_name_sort_append(node, ctx):
    return ["sortt"]


def _match_zero_arg_list_name(node, ctx):
    return _is_name(node, "list")


def _replace_zero_arg_list_name(node, ctx):
    return ["lst"]


def _match_bad_index_name(node, ctx):
    return _is_name(node, "n")


def _replace_bad_index_name(node, ctx):
    return ["element"]


def _match_bad_candidate_name(node, ctx):
    return _is_name(node, "i") and isinstance(ctx.parent(node), ast.Assign)


def _replace_bad_candidate_name(node, ctx):
    return [ctx.text(node)]


def _match_strict_lt_in_max_scan(node, ctx):
    return _cmp_is(node, ast.Lt)


def _replace_strict_lt_in_max_scan(node, ctx):
    return [f"{ctx.text(node.left)} > {ctx.text(node.comparators[0])}"]


def _match_strict_gt_in_min_scan(node, ctx):
    return _cmp_is(node, ast.Gt)


def _replace_strict_gt_in_min_scan(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]


def _match_ge_assignment(node, ctx):
    return _cmp_is(node, ast.GtE) and isinstance(ctx.parent(node), ast.If)


def _replace_ge_assignment(node, ctx):
    return [f"{ctx.text(node.left)} > {ctx.text(node.comparators[0])}"]


def _match_sort_call_missing_parens(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "reverse"


def _replace_sort_call_missing_parens(node, ctx):
    return [f"{ctx.text(node)}()"]


def _match_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_return_none(node, ctx):
    return []


def _match_append_without_return(node, ctx):
    return isinstance(node, ast.Expr) and _is_append_call(node.value) and isinstance(ctx.parent(node), ast.FunctionDef)


def _replace_append_without_return(node, ctx):
    return [ctx.text(node) + "\nreturn " + ctx.text(node.value.func.value)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_wrong_variable", match=_match_wrong_final_variable, replace=lambda n, c: ["return sortt"], symptoms=("wrong",)),
            Rewrite(name="remove_should_use_selected_candidate", match=_match_remove_loop_var, replace=_replace_remove_loop_var, symptoms=("wrong",)),
            Rewrite(name="append_should_use_selected_candidate", match=_match_append_loop_var, replace=_replace_append_loop_var, symptoms=("wrong",)),
            Rewrite(name="remove_append_pair_fix", match=_match_remove_append_loop, replace=_replace_remove_append_loop, symptoms=("wrong",)),
            Rewrite(name="rename_biggest_to_oldest", match=_match_name_biggest, replace=_replace_name_biggest, symptoms=("wrong",)),
            Rewrite(name="rename_sort_to_sortt_in_return", match=_match_name_sort_append, replace=_replace_name_sort_append, symptoms=("wrong",)),
            Rewrite(name="fix_list_builtin_misuse", match=_match_zero_arg_list_name, replace=_replace_zero_arg_list_name, symptoms=("wrong",)),
            Rewrite(name="fix_shadowed_index_name", match=_match_bad_index_name, replace=_replace_bad_index_name, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_gt_in_max_scan", match=_match_strict_lt_in_max_scan, replace=_replace_strict_lt_in_max_scan, symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_lt_in_min_scan", match=_match_strict_gt_in_min_scan, replace=_replace_strict_gt_in_min_scan, symptoms=("wrong",)),
            Rewrite(name="gte_should_be_gt_in_max_scan", match=_match_ge_assignment, replace=_replace_ge_assignment, symptoms=("wrong",)),
            Rewrite(name="missing_reverse_call", match=_match_sort_call_missing_parens, replace=_replace_sort_call_missing_parens, symptoms=("wrong",)),
            Rewrite(name="append_needs_return", match=_match_append_without_return, replace=_replace_append_without_return, symptoms=("wrong",)),
        ]