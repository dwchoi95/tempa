from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_list(node, ctx):
    return isinstance(node, ast.Name) and node.id == "list"


def _is_output_like(node, ctx):
    return isinstance(node, ast.Name) and node.id in {
        "output", "new_list", "new_lst", "newlist", "new", "result", "final",
        "a", "b", "c", "d", "keep", "remove_lst", "remove_list", "removed",
        "pst", "o", "store", "lst1", "lst2", "seq", "res", "rem_lst", "sumx",
        "newseq"
    }


def _is_wrong_container_in_membership(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    return isinstance(node.ops[0], (ast.In, ast.NotIn)) and _is_list(node.left, ctx)


def _fix_container_membership(node, ctx):
    other = ctx.text(node.comparators[0])
    op = " in " if isinstance(node.ops[0], ast.In) else " not in "
    return [f"{ctx.text(node.left)}{op}{other}"]


def _is_wrong_return_name(node, ctx):
    return isinstance(node, ast.Return) and _is_name(node.value, ctx, "lst")


def _fix_return_output(node, ctx):
    return ["return output"]


def _is_return_wrong_var(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {
        "new_list", "newlst", "new_lst", "newlist", "result", "keep", "remove_lst",
        "removed", "a", "o", "pst", "seq", "final", "newseq"
    }


def _fix_return_name(node, ctx):
    return ["return output"]


def _is_append_stmt(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _fix_append_stmt(node, ctx):
    return [ctx.text(node) + "\nreturn output"]


def _is_extend_or_add_wrong(node, ctx):
    if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute):
        return False
    return node.func.attr in {"extend", "insert"} and len(node.args) == 1


def _fix_extend_to_append(node, ctx):
    return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0])})"]


def _is_count_compare_one(node, ctx):
    return (
        isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 1
        and isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Attribute)
        and node.left.func.attr == "count"
    )


def _fix_count_one_to_zero(node, ctx):
    return [ctx.text(node.left) + " == 0"]


def _is_count_lt_one(node, ctx):
    return (
        isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)
        and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 1
    )


def _fix_count_lt_one(node, ctx):
    return [ctx.text(node.left) + " == 0"]


def _is_sort_then_unique(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "sort"


def _fix_sort_noop(node, ctx):
    return [""]


def _is_reverse_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_reverse_return(node, ctx):
    return ["return lst"]


def _is_off_by_one_range(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range" and len(node.args) == 1


def _fix_range_len(node, ctx):
    arg = ctx.text(node.args[0])
    return [f"range({arg})"]


def _is_name_seen(node, ctx):
    return isinstance(node, ast.Name) and node.id == "seen"


def _fix_seen_name(node, ctx):
    return ["output"]


def _is_newlist_count(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "count" and isinstance(node.value, ast.Name) and node.value.id == "new_list"


def _fix_newlist_count(node, ctx):
    return ["output.count"]


def _is_list_reverse_call_assigned(node, ctx):
    return isinstance(node, ast.Assign) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _fix_reverse_assign(node, ctx):
    return [ctx.text(node.value.func.value) + ".reverse()"]


def _is_bad_set_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "set"


def _fix_set_return(node, ctx):
    return ["return list(OrderedDict.fromkeys(lst))"]


def _is_ordereddict_no_list(node, ctx):
    return isinstance(node, ast.Return) and "OrderedDict.fromkeys" in ctx.text(node)


def _fix_ordereddict_list(node, ctx):
    return ["return list(OrderedDict.fromkeys(lst))"]


class Fixer:
    def rules(self):
        return [
            Rewrite("wrong_iterable_name_list", lambda n, c: _is_list(n, c), lambda n, c: ["lst"], symptoms=("wrong",)),
            Rewrite("membership_should_use_result_not_input", _is_wrong_container_in_membership, _fix_container_membership, symptoms=("wrong",)),
            Rewrite("return_lst_should_return_output", _is_wrong_return_name, _fix_return_output, symptoms=("wrong",)),
            Rewrite("wrong_return_name_generic", _is_return_wrong_var, _fix_return_name, symptoms=("wrong",)),
            Rewrite("append_call_as_statement", _is_append_stmt, _fix_append_stmt, symptoms=("wrong",)),
            Rewrite("extend_should_append_single_item", _is_extend_or_add_wrong, _fix_extend_to_append, symptoms=("wrong",)),
            Rewrite("count_equal_one_should_be_zero", _is_count_compare_one, _fix_count_one_to_zero, symptoms=("wrong",)),
            Rewrite("count_less_than_one_should_be_zero", _is_count_lt_one, _fix_count_lt_one, symptoms=("wrong",)),
            Rewrite("remove_sort_statement", _is_sort_then_unique, _fix_sort_noop, symptoms=("wrong",)),
            Rewrite("fix_reverse_return", _is_reverse_return, _fix_reverse_return, symptoms=("wrong",)),
            Rewrite("range_len_off_by_one", _is_off_by_one_range, _fix_range_len, symptoms=("wrong",)),
            Rewrite("seen_should_be_output", _is_name_seen, _fix_seen_name, symptoms=("wrong",)),
            Rewrite("new_list_count_should_be_output_count", _is_newlist_count, _fix_newlist_count, symptoms=("wrong",)),
            Rewrite("reverse_call_assigned_to_variable", _is_list_reverse_call_assigned, _fix_reverse_assign, symptoms=("wrong",)),
            Rewrite("ordered_dict_result_needs_list", _is_ordereddict_no_list, _fix_ordereddict_list, symptoms=("wrong",)),
            Rewrite("set_return_needs_ordered_list", _is_bad_set_return, _fix_set_return, symptoms=("wrong",)),
        ]