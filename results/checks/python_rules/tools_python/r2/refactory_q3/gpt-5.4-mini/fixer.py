from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name=None):
    return isinstance(node, ast.Name) and (name is None or node.id == name)


def _is_list_append_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and len(node.args) == 1
    )


def _is_list_extend_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "extend"
        and len(node.args) == 1
    )


def _is_return_name(node, ctx, name=None):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Name)
        and (name is None or node.value.id == name)
    )


def _replace_name_with(node, ctx, new_name):
    return [new_name]


def _rule_for_list_name_misuse(node, ctx):
    return (
        isinstance(node, ast.Name)
        and node.id != "lst"
        and isinstance(ctx.parent(node), (ast.For, ast.Call, ast.Compare, ast.BinOp, ast.Attribute, ast.Subscript, ast.While, ast.If))
    )


class Fixer:
    def rules(self):
        rules = []

        def r(name, match, replace, symptoms=("wrong",)):
            return Rewrite(name=name, match=match, replace=replace, symptoms=symptoms)

        def make_name_fix(bad, good):
            def m(node, ctx):
                return isinstance(node, ast.Name) and node.id == bad
            def rep(node, ctx):
                return [good]
            return m, rep

        m, rep = make_name_fix("list", "lst")
        rules.append(r("use_lst_not_builtin_list", m, rep))

        m, rep = make_name_fix("new_list", "new_lst")
        rules.append(r("prefer_consistent_new_lst_name", m, rep))

        m, rep = make_name_fix("newlst", "new_lst")
        rules.append(r("prefer_consistent_new_lst_name_2", m, rep))

        m, rep = make_name_fix("output", "new_list")
        rules.append(r("prefer_output_name_when_returned", m, rep))

        def m_return_wrong_name(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"x", "i", "lst"}
        def rep_return_output(node, ctx):
            return ["return output"]
        rules.append(r("return_output_instead_of_loop_var_or_input", m_return_wrong_name, rep_return_output))

        def m_append_on_wrong_target(node, ctx):
            return (
                _is_list_append_call(node)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id in {"lst", "list", "copy"}
            )
        def rep_append_new(node, ctx):
            if isinstance(node.func.value, ast.Name) and node.func.value.id in {"lst", "list"}:
                return [ctx.text(node).replace(ctx.text(node.func.value), "new_list")]
            return [ctx.text(node).replace(ctx.text(node.func.value), "copy")]
        rules.append(r("append_to_output_not_input", m_append_on_wrong_target, rep_append_new))

        def m_extend_singleton(node, ctx):
            return _is_list_extend_call(node) and len(node.args) == 1
        def rep_extend_to_append(node, ctx):
            return [ctx.text(node).replace(".extend(", ".append(")]
        rules.append(r("extend_singleton_should_append", m_extend_singleton, rep_extend_to_append))

        def m_count_on_input_instead_of_result(node, ctx):
            return (
                isinstance(node, ast.Compare)
                and isinstance(node.left, ast.Call)
                and isinstance(node.left.func, ast.Attribute)
                and node.left.func.attr == "count"
                and isinstance(node.left.func.value, ast.Name)
                and node.left.func.value.id == "lst"
                and len(node.ops) == 1
                and isinstance(node.ops[0], (ast.Eq, ast.LtE, ast.Lt))
            )
        def rep_count_on_output(node, ctx):
            return [ctx.text(node).replace("lst.count", "new_list.count")]
        rules.append(r("count_should_target_accumulator", m_count_on_input_instead_of_result, rep_count_on_output))

        def m_return_input(node, ctx):
            return _is_return_name(node, ctx, "lst")
        def rep_return_output_stmt(node, ctx):
            return ["return new_list"]
        rules.append(r("return_accumulator_instead_of_input", m_return_input, rep_return_output_stmt))

        def m_return_last_loop_var(node, ctx):
            return _is_return_name(node, ctx) and node.value.id in {"i", "x", "e", "element", "item", "num"}
        def rep_return_output2(node, ctx):
            return ["return output"]
        rules.append(r("return_final_accumulator_instead_of_loop_var", m_return_last_loop_var, rep_return_output2))

        def m_compare_to_self(node, ctx):
            return isinstance(node, ast.Compare) and any(isinstance(op, ast.NotEq) for op in node.ops) and isinstance(node.left, ast.Name)
        def rep_not_eq_to_not_in(node, ctx):
            if len(node.ops) == 1 and isinstance(node.ops[0], ast.NotEq):
                return [ctx.text(node.left) + " not in " + ctx.text(node.comparators[0])]
            return []
        rules.append(r("use_membership_instead_of_inequality_for_list_check", m_compare_to_self, rep_not_eq_to_not_in))

        def m_append_call_missing_paren(node, ctx):
            return isinstance(node, ast.Attribute) and node.attr == "append"
        def rep_append_parens(node, ctx):
            return [ctx.text(node) + "(%s)" % ""]
        rules.append(r("append_needs_call_parens", m_append_call_missing_paren, rep_append_parens, ("err:TypeError", "wrong")))

        def m_return_none_on_empty(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is None
        def rep_return_empty_list(node, ctx):
            return ["return []"]
        rules.append(r("empty_input_should_return_empty_list", m_return_none_on_empty, rep_return_empty_list))

        def m_ordered_dict_return(node, ctx):
            return isinstance(node, ast.Return) and "OrderedDict.fromkeys" in ctx.text(node)
        def rep_wrap_list(node, ctx):
            txt = ctx.text(node.value)
            if txt.startswith("return "):
                expr = txt[len("return "):]
                return [f"return list({expr})"]
            return []
        rules.append(r("ordered_dict_must_be_listified", m_ordered_dict_return, rep_wrap_list))

        def m_set_return(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == "set"
        def rep_set_to_ordered(node, ctx):
            return ["from collections import OrderedDict\n\ndef remove_extras(lst):\n    return list(OrderedDict.fromkeys(lst))"]
        rules.append(r("set_is_unordered_use_ordereddict", m_set_return, rep_set_to_ordered, ("wrong",)))

        def m_range_len_minus1(node, ctx):
            return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range" and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp)
        def rep_range_fix(node, ctx):
            txt = ctx.text(node.args[0])
            if "- 1" in txt or "-1" in txt:
                return [ctx.text(node).replace(txt, txt.replace("- 1", "").replace("-1", ""))]
            return []
        rules.append(r("off_by_one_range_bound", m_range_len_minus1, rep_range_fix))

        def m_if_in_output_append(node, ctx):
            return (
                isinstance(node, ast.If)
                and isinstance(node.test, ast.Compare)
                and len(node.test.ops) == 1
                and isinstance(node.test.ops[0], ast.In)
                and isinstance(node.body, list)
                and any(isinstance(s, ast.Expr) and _is_list_append_call(s.value) for s in node.body)
            )
        def rep_flip_membership(node, ctx):
            return [ctx.text(node).replace(" in ", " not in ")]
        rules.append(r("duplicate_elimination_membership_flip", m_if_in_output_append, rep_flip_membership))

        return rules