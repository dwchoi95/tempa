from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, *names):
    return isinstance(node, ast.Name) and node.id in names


def _is_call_append(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
    )


def _is_call_extend(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "extend"
        and len(node.args) == 1
    )


def _same_id(a, b):
    return isinstance(a, ast.Name) and isinstance(b, ast.Name) and a.id == b.id


def _is_bad_for_iter_list(node, ctx):
    return isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == "list"


def _fix_for_iter_to_lst(node, ctx):
    return [ctx.text(node).replace("for " + ctx.text(node.target) + " in list", "for " + ctx.text(node.target) + " in lst", 1)]


def _is_membership_against_original_list(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotIn)
        and isinstance(node.comparators[0], ast.Name)
        and ctx.text(node.comparators[0]) == "lst"
    )


def _fix_membership_to_output(node, ctx):
    left = ctx.text(node.left)
    return [f"{left} not in {ctx.text(node.left.parent) if False else 'new_lst'}"]


class Fixer:
    def rules(self):
        rules = []

        def r(name, match, replace, symptoms=("wrong",)):
            return Rewrite(name=name, match=match, replace=replace, symptoms=symptoms)

        def is_for_list(node, ctx):
            return isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id == "list"

        def rep_for_list(node, ctx):
            return [ctx.text(node).replace(" in list", " in lst")]

        rules.append(r("for_iter_list_to_lst", is_for_list, rep_for_list))

        def is_compare_against_lst(node, ctx):
            return (
                isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.NotIn)
                and len(node.comparators) == 1
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id == "lst"
            )

        def rep_compare_against_lst(node, ctx):
            left = ctx.text(node.left)
            return [f"{left} not in new_lst", f"{left} not in output", f"{left} not in result", f"{left} not in keep"]

        rules.append(r("membership_against_original_list", is_compare_against_lst, rep_compare_against_lst))

        def is_bad_return_name(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {
                "lst",
                "x",
                "i",
                "new_list",
                "newlst",
                "newseq",
            }

        def rep_return_name(node, ctx):
            return ["return new_lst", "return output", "return result", "return newlist", "return new"]

        rules.append(r("wrong_return_variable", is_bad_return_name, rep_return_name))

        def is_append_on_wrong_container(node, ctx):
            return _is_call_append(node, ctx) and isinstance(node.func.value, ast.Name) and node.func.value.id in {"lst", "list"}

        def rep_append_on_wrong_container(node, ctx):
            return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0])})"]

        rules.append(r("append_on_wrong_container", is_append_on_wrong_container, rep_append_on_wrong_container))

        def is_extend_single_item(node, ctx):
            return _is_call_extend(node, ctx) and isinstance(node.args[0], ast.Name)

        def rep_extend_single_item(node, ctx):
            return [f"{ctx.text(node.func.value)}.append({ctx.text(node.args[0])})", f"{ctx.text(node.func.value)} += [{ctx.text(node.args[0])}]"]

        rules.append(r("extend_single_item_should_append", is_extend_single_item, rep_extend_single_item))

        def is_return_list_set(node, ctx):
            return (
                isinstance(node, ast.Return)
                and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and node.value.func.id in {"set", "lists"}
            )

        def rep_return_list_set(node, ctx):
            return [f"return list({ctx.text(node.value.args[0])})"] if isinstance(node.value, ast.Call) and node.value.args else []

        rules.append(r("set_or_lists_should_be_list", is_return_list_set, rep_return_list_set))

        def is_return_ordered_dict(node, ctx):
            return (
                isinstance(node, ast.Return)
                and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Attribute)
                and ctx.text(node.value.func.value) == "OrderedDict"
                and node.value.func.attr == "fromkeys"
            )

        def rep_return_ordered_dict(node, ctx):
            return [f"return list({ctx.text(node.value)})"]

        rules.append(r("ordered_dict_missing_list_wrap", is_return_ordered_dict, rep_return_ordered_dict))

        def is_count_check_against_lst(node, ctx):
            return (
                isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.Eq)
                and isinstance(node.left, ast.Call)
                and isinstance(node.left.func, ast.Attribute)
                and node.left.func.attr == "count"
                and ctx.text(node.left.func.value) == "lst"
                and len(node.comparators) == 1
                and isinstance(node.comparators[0], ast.Constant)
                and node.comparators[0].value == 1
            )

        def rep_count_check_against_lst(node, ctx):
            return [f"{ctx.text(node.left.func.value)}.count({ctx.text(node.left.args[0])}) == 0"]

        rules.append(r("count_on_original_list_should_be_zero", is_count_check_against_lst, rep_count_check_against_lst))

        def is_list_count_zero_bad(node, ctx):
            return (
                isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.Eq)
                and isinstance(node.left, ast.Call)
                and isinstance(node.left.func, ast.Attribute)
                and node.left.func.attr == "count"
                and len(node.comparators) == 1
                and isinstance(node.comparators[0], ast.Constant)
                and node.comparators[0].value == 0
            )

        def rep_list_count_zero(node, ctx):
            return [f"{ctx.text(node.left.func.value)}.count({ctx.text(node.left.args[0])}) == 0"]

        rules.append(r("count_zero_ok", is_list_count_zero_bad, rep_list_count_zero))

        def is_append_wrong_name(node, ctx):
            return isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id in {"new_list", "newlst", "newseq"} for t in node.targets
            ) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append"

        def rep_append_assign(node, ctx):
            return [f"{ctx.text(node.targets[0])}.append({ctx.text(node.value.args[0])})"] if isinstance(node.targets[0], ast.Name) and node.value.args else []

        rules.append(r("append_assignment_loses_value", is_append_wrong_name, rep_append_assign))

        def is_return_wrong_name(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"new_list", "newlst", "newseq", "lst", "x", "i"}

        def rep_return_output(node, ctx):
            return ["return output", "return result", "return new_lst", "return newlist", "return new"]

        rules.append(r("wrong_return_name_generic", is_return_wrong_name, rep_return_output))

        return rules