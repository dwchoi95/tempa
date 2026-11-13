from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_call_max(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "max" and len(node.args) == 1


def _is_call_min(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "min" and len(node.args) == 1


def _is_zero_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 0
    )


def _fix_append_remove(node, ctx):
    return [ctx.text(node).replace("lst.remove(max(lst))", "max(lst)")]


def _fix_return_slice_k1(node, ctx):
    return [ctx.text(node).replace(":k+1", ":k").replace(":k-1", ":k")]


def _fix_append_removed_value(node, ctx):
    return [ctx.text(node).replace("append(lst.remove(max(lst)))", "append(max(lst)); lst.remove(max(lst))")]


def _fix_pop_max_to_index(node, ctx):
    return [ctx.text(node).replace("pop(max(lst))", "pop(lst.index(max(lst)))")]


def _fix_list_sort_call(node, ctx):
    return [ctx.text(node).replace("sort=sort(lst)", "lst=sort(lst)")]


def _fix_return_lst_to_result(node, ctx):
    return ["return result"]


def _fix_return_lst_to_newlst(node, ctx):
    return ["return new_lst"]


def _fix_return_lst_to_sort(node, ctx):
    return ["return sort"]


def _fix_return_lst_to_newlist(node, ctx):
    return ["return newlist"]


def _fix_len_le_k_to_lt(node, ctx):
    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE):
        return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]
    return []


def _fix_len_ge_to_gt(node, ctx):
    if isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE):
        return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]
    return []


def _fix_k_plus_one(node, ctx):
    if isinstance(node, ast.Subscript):
        txt = ctx.text(node)
        if "k+1" in txt:
            return [txt.replace("k+1", "k")]
    return []


def _fix_off_by_one_range(node, ctx):
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range":
        txt = ctx.text(node)
        if "k-1" in txt:
            return [txt.replace("k-1", "k")]
        if "k+1" in txt:
            return [txt.replace("k+1", "k")]
    return []


def _fix_remove_then_append(node, ctx):
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        txt = ctx.text(node)
        if "lst.remove(max(lst))" in txt and "append(max(lst))" not in txt:
            return [txt.replace("lst.remove(max(lst))", "lst.remove(max(lst))\n" + txt.split("\n")[-1].replace("lst.remove(max(lst))", "result.append(max(lst))"))]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="append_removed_max_instead_of_removed_none", match=lambda n, c: isinstance(n, ast.Expr) and "append(lst.remove(max(lst)))" in c.text(n), replace=_fix_append_removed_value, symptoms=("wrong",)),
            Rewrite(name="remove_max_before_appending_max", match=lambda n, c: isinstance(n, ast.Expr) and "lst.remove(max(lst))" in c.text(n) and "append(max(lst))" in c.text(n), replace=lambda n, c: [c.text(n).replace("lst.remove(max(lst))", "lst.remove(max(lst))")], symptoms=("wrong",)),
            Rewrite(name="pop_max_needs_index", match=lambda n, c: isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "pop" and "max(" in c.text(n), replace=_fix_pop_max_to_index, symptoms=("wrong",)),
            Rewrite(name="wrong_slice_k_plus_one", match=lambda n, c: _is_zero_compare(n, c) is False and isinstance(n, ast.Subscript) and ":k+1" in c.text(n), replace=_fix_k_plus_one, symptoms=("wrong",)),
            Rewrite(name="wrong_slice_k_minus_one", match=lambda n, c: isinstance(n, ast.Subscript) and ":k-1" in c.text(n), replace=_fix_k_plus_one, symptoms=("wrong",)),
            Rewrite(name="range_off_by_one", match=_fix_off_by_one_range, replace=_fix_off_by_one_range, symptoms=("wrong",)),
            Rewrite(name="return_lst_after_sorting_result", match=lambda n, c: isinstance(n, ast.Return) and c.text(n).strip() == "return lst[:k]", replace=_fix_return_lst_to_result, symptoms=("wrong",)),
            Rewrite(name="return_lst_after_sorting_newlst", match=lambda n, c: isinstance(n, ast.Return) and c.text(n).strip() == "return lst[:k+1]", replace=_fix_return_lst_to_newlst, symptoms=("wrong",)),
            Rewrite(name="return_sort_instead_of_lst", match=lambda n, c: isinstance(n, ast.Return) and c.text(n).strip() == "return lst", replace=_fix_return_lst_to_sort, symptoms=("wrong",)),
            Rewrite(name="sort_call_assigned_to_self", match=lambda n, c: isinstance(n, ast.Assign) and "sort=sort(lst)" in c.text(n), replace=lambda n, c: [c.text(n).replace("sort=sort(lst)", "lst=sort(lst)")], symptoms=("wrong",)),
            Rewrite(name="len_le_k_loop_should_be_lt", match=lambda n, c: _is_zero_compare(n, c) is False and isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], ast.LtE), replace=_fix_len_le_k_to_lt, symptoms=("wrong",)),
            Rewrite(name="len_ge_k_loop_should_be_gt", match=lambda n, c: isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], ast.GtE), replace=_fix_len_ge_to_gt, symptoms=("wrong",)),
            Rewrite(name="missing_return_newlist", match=lambda n, c: isinstance(n, ast.FunctionDef) is False and isinstance(n, ast.Expr) is False and False, replace=lambda n, c: [], symptoms=("wrong",)),
            Rewrite(name="fix_slice_zero_k", match=lambda n, c: isinstance(n, ast.Subscript) and ":k" in c.text(n) and "k-1" in c.text(n), replace=lambda n, c: [c.text(n).replace(":k-1", ":k")], symptoms=("wrong",)),
        ]