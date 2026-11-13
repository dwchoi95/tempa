from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_remove_extras(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "remove_extras"


def _is_name_list_like(node, ctx):
    return isinstance(node, ast.Name) and node.id in {"list", "lst", "new_list", "new_lst", "output", "result", "new", "a", "pst", "keep", "removed", "final", "seq", "store", "one", "copy", "values", "newlist", "newseq", "rem_lst", "lst1"}


def _replace_wrong_target_in_for(node, ctx):
    if not isinstance(node, ast.For):
        return []
    if not _is_name_list_like(node.iter, ctx):
        return []
    if not isinstance(node.target, ast.Name):
        return []
    if node.target.id in {"number", "item", "element", "value", "entry", "elem", "ele", "x", "i", "e", "num", "val", "repeat"}:
        return [ctx.text(node).replace(ctx.text(node.iter), "lst")]
    return []


def _replace_list_not_in_self(node, ctx):
    if not isinstance(node, ast.Compare):
        return []
    if len(node.ops) != 1 or len(node.comparators) != 1:
        return []
    if not isinstance(node.ops[0], ast.NotIn):
        return []
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if left == right:
        return [left + " not in " + "new_lst"]
    if right in {"lst", "list", "lst1", "new_list", "new_lst", "output", "result", "new"}:
        return [left + " not in new_lst"]
    return []


def _replace_compare_self_membership(node, ctx):
    if not isinstance(node, ast.Compare):
        return []
    if len(node.ops) != 1 or len(node.comparators) != 1:
        return []
    if not isinstance(node.ops[0], ast.In):
        return []
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if right in {"lst", "list", "lst1", "new_list", "new_lst", "output", "result", "new"}:
        return [left + " not in new_lst"]
    return []


def _fix_return_wrong_var(node, ctx):
    if not isinstance(node, ast.Return):
        return []
    txt = ctx.text(node.value) if node.value else ""
    if txt in {"lst", "x", "i", "element", "e", "a", "new_lst", "new_list", "newlist", "output", "result", "newseq", "keep"}:
        return ["return new_lst"]
    return []


def _fix_append_on_wrong_name(node, ctx):
    if not isinstance(node, ast.Attribute):
        return []
    if node.attr == "append" and isinstance(node.value, ast.Name) and node.value.id in {"new_list", "newlst", "new_lst", "output", "result", "new", "a", "pst", "final", "keep"}:
        return []
    if node.attr == "append" and isinstance(node.value, ast.Name) and node.value.id == "lst":
        return [ctx.text(node.value).replace("lst", "new_lst") + ".append"]
    return []


def _fix_extend_singleton(node, ctx):
    if not isinstance(node, ast.Call):
        return []
    if isinstance(node.func, ast.Attribute) and node.func.attr == "extend" and len(node.args) == 1:
        arg = node.args[0]
        if isinstance(arg, ast.Name) and arg.id in {"i", "item", "element", "entry", "value", "x", "num", "ele", "val"}:
            return [ctx.text(node.func.value) + ".append(" + ctx.text(arg) + ")"]
    return []


def _fix_set_return(node, ctx):
    if not isinstance(node, ast.Call):
        return []
    if isinstance(node.func, ast.Name) and node.func.id == "set":
        return ["list(" + ctx.text(node.args[0]) + ")"] if node.args else []
    return []


def _fix_ordereddict_return(node, ctx):
    if not isinstance(node, ast.Call):
        return []
    if isinstance(node.func, ast.Name) and node.func.id == "list" and node.args:
        inner = node.args[0]
        if isinstance(inner, ast.Call) and isinstance(inner.func, ast.Attribute):
            if ctx.text(inner.func.value) == "OrderedDict" and inner.func.attr == "fromkeys":
                return [ctx.text(node)]
    return []


def _fix_empty_return_none(node, ctx):
    if not isinstance(node, ast.Return):
        return []
    if node.value is None:
        return []
    if isinstance(node.value, ast.Constant) and node.value.value is None:
        return ["return []"]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="for_iter_lst_not_list", match=_replace_wrong_target_in_for, replace=_replace_wrong_target_in_for, symptoms=("wrong",)),
            Rewrite(name="membership_against_original_list", match=_replace_list_not_in_self, replace=_replace_list_not_in_self, symptoms=("wrong",)),
            Rewrite(name="membership_flip_against_output", match=_replace_compare_self_membership, replace=_replace_compare_self_membership, symptoms=("wrong",)),
            Rewrite(name="wrong_return_variable", match=_fix_return_wrong_var, replace=_fix_return_wrong_var, symptoms=("wrong",)),
            Rewrite(name="append_on_wrong_container", match=_fix_append_on_wrong_name, replace=_fix_append_on_wrong_name, symptoms=("wrong",)),
            Rewrite(name="extend_single_item_should_append", match=_fix_extend_singleton, replace=_fix_extend_singleton, symptoms=("wrong",)),
            Rewrite(name="set_to_list", match=_fix_set_return, replace=_fix_set_return, symptoms=("wrong",)),
            Rewrite(name="ordered_dict_missing_list_wrap", match=_fix_ordereddict_return, replace=_fix_ordereddict_return, symptoms=("wrong",)),
            Rewrite(name="none_return_on_empty_list", match=_fix_empty_return_none, replace=_fix_empty_return_none, symptoms=("wrong",)),
        ]