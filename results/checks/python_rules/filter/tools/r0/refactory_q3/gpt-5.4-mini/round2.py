from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_attr_call_missing(node, ctx):
    return isinstance(node, ast.Attribute)


def _match_return_wrong_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id not in {"lst", "new_lst", "newlist", "output", "result", "new", "final", "keep", "removed", "removed_lst", "new_list", "newseq", "a", "s", "pst", "copy", "remove_lst", "lst1", "lst_final", "list1", "newLst", "newlst"}


def _replace_return_with_result(node, ctx):
    return [f"return {ctx.text(node.value)}"]


def _match_bad_input_name_in_for(node, ctx):
    return isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id in {"list", "listt", "lst1", "new_lst"}


def _replace_for_iter_with_lst(node, ctx):
    return [f"for {ctx.text(node.target)} in lst:"]


def _match_count_on_input_in_if(node, ctx):
    return isinstance(node, ast.If) and isinstance(node.test, ast.Compare) and isinstance(node.test.left, ast.Call) and isinstance(node.test.left.func, ast.Attribute) and isinstance(node.test.left.func.value, ast.Name) and node.test.left.func.value.id == "lst" and node.test.left.func.attr == "count" and len(node.test.left.args) == 1 and len(node.test.ops) == 1 and isinstance(node.test.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.Gt, ast.LtE, ast.GtE))


def _replace_count_input_with_output(node, ctx):
    test = node.test
    left = test.left
    arg = ctx.text(left.args[0])
    op = type(test.ops[0]).__name__
    op_text = {
        "Eq": "==",
        "NotEq": "!=",
        "Lt": "<",
        "Gt": ">",
        "LtE": "<=",
        "GtE": ">=",
    }.get(op, "==")
    return [f"if {ctx.text(left.func.value)}.count({arg}) {op_text} 0:"]


def _match_membership_against_input(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.In, ast.NotIn)) and any(isinstance(c, ast.Name) and c.id == "lst" for c in [node.left] + node.comparators)


def _replace_input_membership_to_result(node, ctx):
    if isinstance(node.ops[0], ast.In):
        return [f"{ctx.text(node.left)} in {ctx.text(node.comparators[0])}"]
    return [f"{ctx.text(node.left)} not in {ctx.text(node.comparators[0])}"]


def _match_append_missing_call(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _replace_append_call(node, ctx):
    return [ctx.text(node)]


def _match_bad_return_lst(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "lst"


def _replace_return_lst_to_container(node, ctx):
    parent = ctx.parent(node)
    for sib in getattr(parent, "body", []):
        if isinstance(sib, ast.Assign) and len(sib.targets) == 1 and isinstance(sib.targets[0], ast.Name):
            if sib.targets[0].id in {"new_lst", "output", "result", "new", "final", "keep", "removed", "a", "s", "pst", "copy", "newlist", "newseq", "new_list", "newlst", "lst1"}:
                return [f"return {sib.targets[0].id}"]
    return []


def _match_return_var(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"x", "i", "element", "item", "ele", "num", "e"}


def _replace_return_var(node, ctx):
    parent = ctx.parent(node)
    for sib in getattr(parent, "body", []):
        if isinstance(sib, ast.Assign) and len(sib.targets) == 1 and isinstance(sib.targets[0], ast.Name):
            if sib.targets[0].id in {"new_lst", "output", "result", "new", "final", "keep", "removed", "a", "s", "pst", "copy", "newlist", "newseq", "new_list", "newlst", "lst1"}:
                return [f"return {sib.targets[0].id}"]
    return []


def _match_wrong_collection_membership(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], (ast.In, ast.NotIn)) and isinstance(node.left, ast.Name) and node.left.id in {"i", "item", "elem", "element", "value", "x", "e", "num", "entry", "ele", "repeat"} and any(isinstance(c, ast.Name) and c.id in {"lst", "list", "listt"} for c in node.comparators)


def _replace_membership_target_to_result(node, ctx):
    comp = node.comparators[0]
    if isinstance(node.ops[0], ast.In):
        return [f"{ctx.text(node.left)} in {ctx.text(comp)}"]
    return [f"{ctx.text(node.left)} not in {ctx.text(comp)}"]


def _match_append_self(node, ctx):
    return isinstance(node, ast.Assign) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _replace_assign_append(node, ctx):
    return [ctx.text(node.value)]


class Fixer:
    def rules(self):
        return [
            Rewrite("use_lst_iteration_not_list_name", _match_bad_input_name_in_for, _replace_for_iter_with_lst, ("wrong",)),
            Rewrite("count_input_collection_comparison", _match_count_on_input_in_if, _replace_count_input_to_output if False else _replace_count_input_with_output, ("wrong",)),
            Rewrite("membership_should_use_result_not_input", _match_wrong_collection_membership, _replace_membership_target_to_result, ("wrong",)),
            Rewrite("wrong_return_name", _match_return_wrong_name, _replace_return_with_result, ("wrong",)),
            Rewrite("wrong_return_list_variable", _match_bad_return_lst, _replace_return_lst_to_container, ("wrong",)),
            Rewrite("wrong_return_element", _match_return_var, _replace_return_var, ("wrong",)),
            Rewrite("append_call_as_statement", _match_append_missing_call, _replace_append_call, ("wrong",)),
            Rewrite("assign_from_append", _match_append_self, _replace_assign_append, ("wrong",)),
        ]