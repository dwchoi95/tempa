from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name=None):
    return isinstance(node, ast.Name) and (name is None or node.id == name)


def _is_append_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
        and not node.keywords
    )


def _is_extend_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "extend"
        and len(node.args) == 1
        and not node.keywords
    )


def _fix_wrong_list_target(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.iter, ast.Name)
        and isinstance(node.target, ast.Name)
        and node.iter.id == "list"
    )


def _fix_wrong_if_list_membership(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.In)
        and isinstance(node.comparators[0], ast.Name)
        and node.comparators[0].id in {"lst", "list", "new_lst", "new_list", "output", "result", "keep", "a", "pst", "newseq", "newlist", "new"}
    )


def _fix_return_wrong_var(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Name)
        and node.value.id in {"lst", "x", "i", "new_list", "newlst", "result"}
    )


def _fix_set_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "set"


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="use_function_parameter_in_for_loop",
                match=_fix_wrong_list_target,
                replace=lambda node, ctx: [ctx.text(node).replace(" in list", " in lst")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="membership_against_output_not_input",
                match=_fix_wrong_if_list_membership,
                replace=lambda node, ctx: [
                    ctx.text(node.left) + " not in " + ctx.text(node.comparators[0]).replace("list", "new_lst").replace("lst", "new_lst")
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_accumulator_not_loop_var",
                match=_fix_return_wrong_var,
                replace=lambda node, ctx: [
                    "return " + (
                        "output" if ctx.text(node.value) in {"lst", "x", "i"} else
                        "new_lst" if ctx.text(node.value) in {"new_list", "newlst"} else
                        "result"
                    )
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_set_return_with_ordered_dict",
                match=_fix_set_return,
                replace=lambda node, ctx: ["return list(OrderedDict.fromkeys(" + ctx.text(node.value.args[0]) + "))"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_instead_of_extend_singleton",
                match=_is_extend_call,
                replace=lambda node, ctx: [
                    ctx.text(node.func.value) + ".append(" + ctx.text(node.args[0]).replace("list(", "").replace(")", "") + ")"
                ],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_call_not_attribute_object",
                match=lambda node, ctx: _is_append_call(node, ctx),
                replace=lambda node, ctx: [ctx.text(node.func.value) + ".append(" + ctx.text(node.args[0]) + ")"],
                symptoms=("err:AttributeError", "wrong"),
            ),
            Rewrite(
                name="fix_wrong_list_vs_variable_name",
                match=lambda node, ctx: isinstance(node, ast.Name) and node.id in {"list", "new_list", "newlst", "newseq"} and isinstance(ctx.parent(node), ast.For) and ctx.field(node) == "iter",
                replace=lambda node, ctx: ["lst" if node.id == "list" else node.id.replace("new_list", "new_lst")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_return_wrong_name_to_output",
                match=lambda node, ctx: isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"new_list", "newlst", "newseq", "keep", "removed", "remove_lst", "lst1", "a", "s", "final"},
                replace=lambda node, ctx: ["return " + node.value.id.replace("new_list", "new_lst").replace("newlst", "new_lst").replace("newseq", "new_lst").replace("removed", "output").replace("remove_lst", "output").replace("lst1", "output").replace("final", "output").replace("a", "output").replace("s", "output")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_ordered_dict_import_needed",
                match=lambda node, ctx: isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "OrderedDict",
                replace=lambda node, ctx: ["return list(OrderedDict.fromkeys(" + ctx.text(node.value.args[0]) + "))"],
                symptoms=("wrong",),
            ),
        ]