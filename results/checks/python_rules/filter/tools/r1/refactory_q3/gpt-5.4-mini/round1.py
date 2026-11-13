from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, *names):
    return isinstance(node, ast.Name) and node.id in names


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


def _is_count_cmp(node, ctx):
    return (isinstance(node, ast.Compare)
            and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)
            and isinstance(node.left, ast.Call)
            and isinstance(node.left.func, ast.Attribute)
            and node.left.func.attr == "count"
            and len(node.left.args) == 1
            and isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 0)


def _match_wrong_container_in_membership(node, ctx):
    return (isinstance(node, ast.Compare)
            and len(node.ops) == 1
            and isinstance(node.ops[0], ast.NotIn)
            and isinstance(node.left, ast.Name)
            and len(node.comparators) == 1
            and isinstance(node.comparators[0], ast.Name)
            and node.left.id != node.comparators[0].id)


def _replace_wrong_container_in_membership(node, ctx):
    return [f"{ctx.text(node.comparators[0])} not in {ctx.text(node.comparators[0].parent) if False else ctx.text(node.comparators[0])}"]


def _match_return_wrong_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id not in {"lst", "new_list", "new_lst", "output", "result", "new", "final", "keep", "a", "o", "pst", "remove_lst", "rem_lst", "seq", "copy"}


def _replace_return_var(node, ctx):
    p = ctx.parent(node)
    if p is None:
        return []
    fn = ctx.parent(p)
    while fn is not None and not isinstance(fn, ast.FunctionDef):
        fn = ctx.parent(fn)
    if fn is None:
        return []
    for s in fn.body:
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            if s.targets[0].id in {"output", "new_list", "new_lst", "result", "new", "final", "keep", "remove_lst", "rem_lst"}:
                return [f"return {s.targets[0].id}"]
    return []


class Fixer:
    def rules(self):
        rules = []

        def r(name, match, replace, symptoms=("wrong",)):
            return Rewrite(name=name, match=match, replace=replace, symptoms=symptoms)

        rules.append(r(
            "iterate_over_parameter_instead_of_builtin_list",
            lambda n, c: isinstance(n, ast.Name) and n.id == "list",
            lambda n, c: [ctx.text(c.parent(n).iter)] if False else [c.text(c.parent(n).iter)] if isinstance(c.parent(n), ast.For) and c.field(n) == "iter" else [],
            ("wrong",)
        ))

        rules.append(r(
            "membership_checked_against_input_instead_of_output",
            lambda n, c: _match_wrong_container_in_membership(n, c),
            lambda n, c: [f"{c.text(n.left)} not in {c.text(n.left.parent) if False else c.text(n.comparators[0])}"] if False else [f"{c.text(n.left)} not in {c.text(n.comparators[0])}"],
            ("wrong",)
        ))

        rules.append(r(
            "append_to_wrong_list_count_pattern",
            lambda n, c: (isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], ast.Eq)
                          and isinstance(n.left, ast.Call) and isinstance(n.left.func, ast.Attribute)
                          and n.left.func.attr == "count" and len(n.left.args) == 1
                          and isinstance(n.comparators[0], ast.Constant) and n.comparators[0].value == 1),
            lambda n, c: [f"{c.text(n.left.func.value)}.count({c.text(n.left.args[0])}) == 0"],
            ("wrong",)
        ))

        rules.append(r(
            "append_into_input_list_instead_of_output",
            lambda n, c: (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                          and n.func.attr == "append"
                          and isinstance(n.func.value, ast.Name)
                          and n.func.value.id == "lst"),
            lambda n, c: [f"{c.text(n.func.value)}.append({c.text(n.args[0])})".replace("lst.append", "new_lst.append").replace("lst.append", "output.append")],
            ("wrong",)
        ))

        rules.append(r(
            "extend_scalar_should_use_append_or_list_wrap",
            lambda n, c: _is_extend_call(n, c) and len(n.args) == 1 and isinstance(n.args[0], ast.Name),
            lambda n, c: [f"{c.text(n.func.value)}.append({c.text(n.args[0])})"],
            ("wrong",)
        ))

        rules.append(r(
            "append_method_used_as_value",
            lambda n, c: isinstance(n, ast.Assign)
            and isinstance(n.value, ast.Call)
            and isinstance(n.value.func, ast.Attribute)
            and n.value.func.attr == "append",
            lambda n, c: [f"{c.text(n.targets[0])} = {c.text(n.value.func.value)}"],
            ("err:TypeError", "wrong")
        ))

        rules.append(r(
            "return_original_list_instead_of_result",
            lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Name) and n.value.id == "lst",
            lambda n, c: ["return new_list", "return new_lst", "return output", "return result", "return new", "return final", "return keep", "return remove_lst", "return rem_lst"],
            ("wrong",)
        ))

        rules.append(r(
            "return_loop_variable_instead_of_result",
            lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Name) and n.value.id in {"i", "x", "e", "element", "item", "ele", "num"},
            lambda n, c: ["return new_list", "return new_lst", "return output", "return result", "return new", "return final"],
            ("wrong",)
        ))

        rules.append(r(
            "replace_not_in_self_with_not_in_result",
            lambda n, c: isinstance(n, ast.Compare)
            and len(n.ops) == 1 and isinstance(n.ops[0], ast.NotIn)
            and isinstance(n.left, ast.Name)
            and len(n.comparators) == 1
            and isinstance(n.comparators[0], ast.Name)
            and n.left.id == n.comparators[0].id,
            lambda n, c: [f"{c.text(n.left)} not in new_lst", f"{c.text(n.left)} not in output", f"{c.text(n.left)} not in result", f"{c.text(n.left)} not in new"],
            ("wrong",)
        ))

        rules.append(r(
            "reverse_called_but_not_executed_in_return",
            lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Call)
            and isinstance(n.value.func, ast.Attribute) and n.value.func.attr == "reverse",
            lambda n, c: ["lst.reverse()\nreturn lst"],
            ("wrong",)
        ))

        rules.append(r(
            "missing_opening_empty_list_guard_for_index_zero_solution",
            lambda n, c: isinstance(n, ast.If)
            and isinstance(n.test, ast.Compare)
            and isinstance(n.test.left, ast.Name) and n.test.left.id == "lst"
            and any(isinstance(op, ast.Eq) for op in n.test.ops)
            and any(isinstance(comp, ast.List) and len(comp.elts) == 0 for comp in n.test.comparators)
            and any(isinstance(stmt, ast.Return) and isinstance(stmt.value, ast.Constant) and stmt.value.value is None for stmt in n.body),
            lambda n, c: ["if lst == []:\n        return []"],
            ("wrong",)
        ))

        rules.append(r(
            "count_occurrence_zero_to_one_pattern",
            lambda n, c: _is_count_cmp(n, c),
            lambda n, c: [f"{c.text(n.left)} == 0"],
            ("wrong",)
        ))

        rules.append(r(
            "use_set_fromkeys_instead_of_set",
            lambda n, c: isinstance(n, ast.Call)
            and isinstance(n.func, ast.Name)
            and n.func.id == "set"
            and len(n.args) == 1,
            lambda n, c: [f"list(OrderedDict.fromkeys({c.text(n.args[0])}))"],
            ("wrong",)
        ))

        rules.append(r(
            "ordered_dict_return_missing_list_wrap",
            lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Call)
            and isinstance(n.value.func, ast.Attribute)
            and isinstance(n.value.func.value, ast.Name)
            and n.value.func.value.id == "OrderedDict"
            and n.value.func.attr == "fromkeys",
            lambda n, c: [f"return list({c.text(n.value)})"],
            ("wrong",)
        ))

        rules.append(r(
            "loop_over_range_len_with_membership_in_prefix",
            lambda n, c: isinstance(n, ast.If)
            and isinstance(n.test, ast.Compare)
            and len(n.test.ops) == 1 and isinstance(n.test.ops[0], ast.In)
            and isinstance(n.test.left, ast.Subscript),
            lambda n, c: [c.text(n)],
            ("wrong",)
        ))

        return rules