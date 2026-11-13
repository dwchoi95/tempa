from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_remove_extras_func(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "remove_extras"


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_append_call(node, ctx):
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and len(node.args) == 1)


def _is_extend_call(node, ctx):
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "extend"
            and len(node.args) == 1)


def _is_reverse_call(node, ctx):
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "reverse"
            and len(node.args) == 0)


def _is_return(node, ctx):
    return isinstance(node, ast.Return)


def _match_wrong_collection_in_membership(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    if not isinstance(node.ops[0], ast.NotIn) and not isinstance(node.ops[0], ast.In):
        return False
    left = node.left
    right = node.comparators[0]
    if isinstance(left, ast.Name) and isinstance(right, ast.Name):
        return left.id != right.id and left.id in {"lst", "list", "values"} and right.id in {"new_list", "new_lst", "output", "result", "new", "a", "keep", "final", "remove_lst", "keep"}
    return False


def _replace_compare_collection(node, ctx):
    op = node.ops[0]
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if isinstance(op, ast.NotIn):
        return [f"{left} not in {right}"]
    return [f"{left} in {right}"]


def _match_return_wrong_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"lst", "x", "i", "element", "new_list", "newlst", "new_list", "result"}


def _replace_return_output(node, ctx):
    return ["return output"]


def _match_return_wrong_var_to_list(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"new_list", "new_lst", "output", "result", "new", "final", "keep", "a", "removed", "remove_lst", "newseq", "newlist", "lst1"}


def _replace_return_same_name(node, ctx):
    return [f"return {ctx.text(node.value)}"]


def _match_append_misused_as_attr(node, ctx):
    return isinstance(node, ast.Assign) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"


def _replace_assign_append(node, ctx):
    return [ctx.text(node.value)]


def _match_extend_scalar(node, ctx):
    return _is_extend_call(node, ctx) and not isinstance(node.args[0], (ast.List, ast.Tuple, ast.Set, ast.Dict))


def _replace_extend_scalar(node, ctx):
    return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0])})"]


def _match_bad_list_concat_scalar(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add) and (
        (isinstance(node.left, ast.Name) and isinstance(node.right, ast.Name) and node.left.id == "new_lst" and node.right.id != "new_lst") or
        (isinstance(node.left, ast.List) and isinstance(node.right, ast.Name))
    )


def _replace_bad_list_concat_scalar(node, ctx):
    if isinstance(node.left, ast.Name) and isinstance(node.right, ast.Name):
        return [f"{ctx.text(node.left)} + [{ctx.text(node.right)}]"]
    return [ctx.text(node)]


def _match_append_wrong_target(node, ctx):
    return _is_append_call(node, ctx) and isinstance(node.func.value, ast.Name) and node.func.value.id in {"lst", "list"}


def _replace_append_wrong_target(node, ctx):
    return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0])})"]


def _match_return_none_empty(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is None


def _replace_return_empty_list(node, ctx):
    return ["return []"]


def _match_reverse_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and _is_reverse_call(node.value, ctx)


def _replace_reverse_return(node, ctx):
    return [f"{ctx.text(node.value.func.value)}.reverse()\nreturn {ctx.text(node.value.func.value)}"]


def _match_for_list_instead_of_lst(node, ctx):
    return isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == "list"


def _replace_for_list_instead_of_lst(node, ctx):
    return [ctx.text(node).replace("for " + ctx.text(node.target) + " in list", "for " + ctx.text(node.target) + " in lst")]


def _match_membership_against_input_instead_of_output(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.NotIn)
            and isinstance(node.comparators[0], ast.Name) and node.comparators[0].id in {"lst", "list"})


def _replace_membership_against_input_instead_of_output(node, ctx):
    return [f"{ctx.text(node.left)} not in output"]


def _match_count_against_input(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)
            and isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Attribute)
            and node.left.func.attr == "count"
            and isinstance(node.left.func.value, ast.Name)
            and node.left.func.value.id in {"lst", "list"})


def _replace_count_against_input(node, ctx):
    return [f"{ctx.text(node.left.func.value)}.count({ctx.text(node.left.args[0])}) == {ctx.text(node.comparators[0])}"]


def _match_wrong_index_range(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range" and len(node.args) == 2


def _replace_wrong_index_range(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite("use_input_list_in_loop", lambda n, c: isinstance(n, ast.For) and isinstance(n.iter, ast.Name) and n.iter.id == "list",
                    lambda n, c: [ctx_text_for_loop(n, c)], symptoms=("wrong",)),
            Rewrite("membership_should_use_output_not_input", _match_membership_against_input_instead_of_output,
                    _replace_membership_against_input_instead_of_output, symptoms=("wrong",)),
            Rewrite("wrong_return_name", _match_return_wrong_name, _replace_return_output, symptoms=("wrong",)),
            Rewrite("return_none_on_empty_should_return_empty_list", _match_return_none_empty, _replace_return_empty_list, symptoms=("wrong",)),
            Rewrite("append_return_value_misuse", _match_append_misused_as_attr, _replace_assign_append, symptoms=("wrong", "err:TypeError")),
            Rewrite("extend_scalar_to_append", _match_extend_scalar, _replace_extend_scalar, symptoms=("wrong", "err:TypeError")),
            Rewrite("bad_list_concat_scalar", _match_bad_list_concat_scalar, _replace_bad_list_concat_scalar, symptoms=("wrong", "err:TypeError")),
            Rewrite("append_to_input_list", _match_append_wrong_target, _replace_append_wrong_target, symptoms=("wrong",)),
            Rewrite("reverse_call_returned", _match_reverse_return, _replace_reverse_return, symptoms=("wrong", "err:AttributeError")),
            Rewrite("for_iterates_over_list_name", _match_for_list_instead_of_lst, _replace_for_list_instead_of_lst, symptoms=("wrong",)),
            Rewrite("count_input_collection_comparison", _match_count_against_input, _replace_count_against_input, symptoms=("wrong",)),
            Rewrite("compare_wrong_collection_name", _match_wrong_collection_in_membership, _replace_compare_collection, symptoms=("wrong",)),
        ]


def ctx_text_for_loop(node, ctx):
    return ctx.text(node).replace(" in list", " in lst")