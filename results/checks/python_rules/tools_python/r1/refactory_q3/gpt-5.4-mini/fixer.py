from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, value=None):
    return isinstance(node, ast.Name) and (value is None or node.id == value)


def _is_attr_call_missing_parens(node, ctx, attr_name=None):
    return isinstance(node, ast.Attribute) and (attr_name is None or node.attr == attr_name)


def _is_append_attr(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == "append"


def _is_list_method_call(node, ctx, method):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == method
    )


def _is_wrong_return_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name)


def _is_returning_input(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"lst", "list", "values", "n"}


def _is_count_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.NotEq, ast.Lt, ast.Gt, ast.LtE, ast.GtE))
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Attribute)
        and node.left.func.attr == "count"
    )


def _fix_count_one_to_zero(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    if right == "1":
        return [f"{left} == 0"]
    return []


def _count_call_target(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "count"
        and len(node.args) == 1
    )


def _append_attr_stmt(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
    )


def _replace_append_missing_call(node, ctx):
    return [ctx.text(node.value.func) + "(" + ", ".join(ctx.text(a) for a in node.value.args) + ")"]


def _loop_over_list_name(node, ctx):
    return isinstance(node, ast.For) and isinstance(node.iter, ast.Name) and node.iter.id in {"list", "lst1", "new_lst", "newlist", "listt", "listtt"}


def _return_name_node(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name)


def _return_wrong_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"lst", "x", "i", "output", "new_list", "newlst", "new_list", "new", "result", "set"}


def _body_contains(node, kind):
    return any(isinstance(n, kind) for n in ast.walk(node))


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="iterate_over_parameter_instead_of_builtin_list",
                match=lambda n, c: isinstance(n, ast.For) and isinstance(n.iter, ast.Name) and n.iter.id == "list",
                replace=lambda n, c: [f"for {c.text(n.target)} in {c.text(ast.Name(id='lst', ctx=ast.Load()))}:"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="test_new_list_not_input_list",
                match=lambda n, c: isinstance(n, ast.Compare)
                and isinstance(n.left, ast.Name)
                and n.left.id in {"lst", "list", "values", "newseq", "new_lst", "newlist", "remove_lst", "keep", "removed", "output", "a", "s", "final", "result", "pst", "new"}
                and any(isinstance(op, ast.NotIn) for op in n.ops)
                and len(n.comparators) == 1
                and isinstance(n.comparators[0], ast.Name)
                and n.comparators[0].id in {"new_lst", "newlist", "output", "result", "keep", "a", "s", "final", "removed", "pst", "new"},
                replace=lambda n, c: [f"{c.text(n.comparators[0])} not in {c.text(n.left)}"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="test_item_not_input_list",
                match=lambda n, c: isinstance(n, ast.Compare)
                and isinstance(n.left, ast.Name)
                and n.left.id in {"i", "item", "element", "elem", "value", "entry", "x", "e", "num", "ele", "repeat", "entry", "element"}
                and any(isinstance(op, ast.NotIn) for op in n.ops)
                and len(n.comparators) == 1
                and isinstance(n.comparators[0], ast.Name)
                and n.comparators[0].id in {"lst", "list", "values"},
                replace=lambda n, c: [f"{c.text(n.left)} not in {c.text(ast.Name(id='new_list', ctx=ast.Load()))}"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_condition_should_be_zero",
                match=_is_count_compare,
                replace=_fix_count_one_to_zero,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_to_list_instead_of_input_or_wrong_name",
                match=lambda n, c: _is_list_method_call(n, c, "append")
                and len(n.args) == 1
                and isinstance(n.func.value, ast.Name)
                and n.func.value.id in {"lst", "list", "new_list", "newlst", "result", "output", "new", "a", "s", "final", "keep", "removed", "pst", "newseq"},
                replace=lambda n, c: [f"{c.text(n.func.value)}.append({c.text(n.args[0])})"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_missing_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "append",
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("err:TypeError",),
            ),
            Rewrite(
                name="extend_list_instead_of_scalar",
                match=lambda n, c: _is_list_method_call(n, c, "extend")
                and len(n.args) == 1
                and not isinstance(n.args[0], ast.List),
                replace=lambda n, c: [f"{c.text(n.func.value)}.append({c.text(n.args[0])})"],
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="wrong_return_variable",
                match=lambda n, c: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Name)
                and n.value.id in {"lst", "x", "i", "output", "new_list", "newlst", "new", "result", "set", "None"}
                and c.parent(n) is not None,
                replace=lambda n, c: [f"return {self._infer_return_name(n, c)}"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_input_list_when_should_return_new_list",
                match=lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Name) and n.value.id in {"lst", "list"},
                replace=lambda n, c: ["return new_lst" if self._has_new_lst(c.tree) else "return output"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_name_instead_of_calling_reverse",
                match=lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr == "reverse",
                replace=lambda n, c: [ctx.text(n.value.func.value)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_ordered_dict_to_list",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name)
                and n.func.id == "OrderedDict"
                and len(n.args) == 1,
                replace=lambda n, c: [f"list({c.text(n)})"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_set_to_ordered_dict",
                match=lambda n, c: isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "set" and len(n.args) == 1,
                replace=lambda n, c: [f"list(OrderedDict.fromkeys({c.text(n.args[0])}))"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_return_set_to_ordered_dict",
                match=lambda n, c: isinstance(n, ast.Return) and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name) and n.value.func.id == "set",
                replace=lambda n, c: [f"return list(OrderedDict.fromkeys({c.text(n.value.args[0])}))" if n.value.args else "return []"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_wrong_loop_target_newlst",
                match=lambda n, c: isinstance(n, ast.For) and isinstance(n.target, ast.Name) and n.target.id in {"new_lst", "newlist", "output", "result", "a", "s", "keep"} and isinstance(n.iter, ast.Name) and n.iter.id in {"lst", "list"},
                replace=lambda n, c: [f"for {c.text(ast.Name(id='i', ctx=ast.Store()))} in {c.text(ast.Name(id='lst', ctx=ast.Load()))}:"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_pop_without_call",
                match=lambda n, c: isinstance(n, ast.Attribute) and n.attr == "pop",
                replace=lambda n, c: [c.text(n) + "()"],
                symptoms=("err:TypeError",),
            ),
        ]

    def _has_new_lst(self, tree):
        return any(isinstance(n, ast.Name) and n.id == "new_lst" for n in ast.walk(tree))

    def _infer_return_name(self, node, ctx):
        names = ["output", "new_lst", "newlist", "new", "result", "final", "keep", "removed", "pst", "a", "s"]
        used = {n.id for n in ast.walk(ctx.tree) if isinstance(n, ast.Name)}
        for name in names:
            if name in used:
                return name
        return "output"