from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_stmt(node):
    return isinstance(node, ast.stmt)


def _is_expr(node):
    return isinstance(node, ast.expr)


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_attr(node, name):
    return isinstance(node, ast.Attribute) and node.attr == name


def _is_call_name(node, name):
    return isinstance(node, ast.Call) and _is_name(node.func, name)


def _is_list_append(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
    )


def _is_return_none_like(node):
    return isinstance(node, ast.Return) and node.value is not None


def _replace_text(node, ctx, old, new):
    return ctx.text(node).replace(old, new)


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="use_lst_when_variable_a_is_undefined",
                match=lambda n, c: isinstance(n, ast.Name) and n.id == "a",
                replace=lambda n, c: ["lst"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="use_lst_when_variable_list_is_undefined",
                match=lambda n, c: isinstance(n, ast.Name) and n.id == "list",
                replace=lambda n, c: ["lst"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="use_final_when_undefined_output_list_exists",
                match=lambda n, c: isinstance(n, ast.Name) and n.id == "final",
                replace=lambda n, c: ["people"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="use_biggest_variable_name",
                match=lambda n, c: isinstance(n, ast.Name) and n.id == "biggest",
                replace=lambda n, c: ["oldest"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="use_smallest_variable_name",
                match=lambda n, c: isinstance(n, ast.Name) and n.id == "smallest",
                replace=lambda n, c: ["oldest"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="fix_min_to_max_for_descending_sort",
                match=lambda n, c: isinstance(n, ast.Call)
                and _is_name(n.func, "min")
                and len(n.args) == 1,
                replace=lambda n, c: ["max(" + c.text(n.args[0]) + ")"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_max_to_keyed_max",
                match=lambda n, c: isinstance(n, ast.Call)
                and _is_name(n.func, "max")
                and len(n.args) == 1
                and not n.keywords,
                replace=lambda n, c: ["max(" + c.text(n.args[0]) + ", key=lambda x: x[1])"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_max_on_list_to_keyed_max",
                match=lambda n, c: isinstance(n, ast.Call)
                and _is_name(n.func, "max")
                and len(n.args) == 1
                and not n.keywords,
                replace=lambda n, c: ["max(" + c.text(n.args[0]) + ", key=lambda p: p[1])"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_ages_not_whole_tuples",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], (ast.Lt, ast.Gt, ast.LtE, ast.GtE))
                and any(
                    isinstance(x, ast.Name) and x.id in {"lst", "a", "lst1", "lst2"}
                    for x in [n.left] + n.comparators
                ),
                replace=lambda n, c: [c.text(n.left) + " " + n.ops[0].__class__.__name__.replace("LtE", "<=").replace("GtE", ">=").replace("Lt", "<").replace("Gt", ">") + " " + c.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="flip_age_comparison_for_descending_sort",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.Lt)
                and isinstance(n.left, ast.Subscript)
                and isinstance(n.comparators[0], ast.Subscript),
                replace=lambda n, c: [c.text(n.left) + " > " + c.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="flip_age_comparison_for_ascending_sort",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.Gt)
                and isinstance(n.left, ast.Subscript)
                and isinstance(n.comparators[0], ast.Subscript),
                replace=lambda n, c: [c.text(n.left) + " < " + c.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_remove_placeholder_to_remove_variable",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "remove"
                and len(n.args) == 1
                and isinstance(n.args[0], ast.Name)
                and n.args[0].id in {"i", "j", "k", "counter", "smallest", "biggest"},
                replace=lambda n, c: [c.text(n.func.value) + ".remove(" + c.text(n.args[0]) + ")"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_append_none_from_reverse",
                match=lambda n, c: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr == "reverse",
                replace=lambda n, c: [c.text(n.value.func.value) + "[::-1]"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="remove_stray_reverse_call",
                match=lambda n, c: isinstance(n, ast.Expr)
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr == "reverse",
                replace=lambda n, c: [""],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_missing_sorted_list",
                match=lambda n, c: isinstance(n, ast.Pass),
                replace=lambda n, c: ["return sort"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_missing_output_list",
                match=lambda n, c: isinstance(n, ast.Expr)
                and isinstance(n.value, ast.Name)
                and n.value.id == "t",
                replace=lambda n, c: ["return new"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_list_append_expression_to_assignment",
                match=lambda n, c: isinstance(n, ast.Assign)
                and len(n.targets) == 1
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Attribute)
                and n.value.func.attr == "append",
                replace=lambda n, c: [c.text(n.targets[0]) + " = " + c.text(n.targets[0]) + " + [" + c.text(n.value.args[0]) + "]"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_pop_index_call",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "pop"
                and len(n.args) == 1
                and isinstance(n.args[0], ast.Subscript),
                replace=lambda n, c: [c.text(n.func.value) + ".pop(" + c.text(n.args[0].slice) + ")"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_pop_brackets_on_index",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Attribute)
                and n.func.attr == "pop"
                and len(n.args) == 1
                and isinstance(n.args[0], ast.Name),
                replace=lambda n, c: [c.text(n.func.value) + ".pop(" + c.text(n.args[0]) + ")"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_comparison_assignment_in_loop",
                match=lambda n, c: isinstance(n, ast.Assign)
                and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.Name)
                and n.targets[0].id == n.value.id,
                replace=lambda n, c: [c.text(n.targets[0]) + " = " + c.text(n.targets[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_return_none_to_return_lst",
                match=lambda n, c: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Constant)
                and n.value.value is None,
                replace=lambda n, c: ["return lst"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_sort_return_none_attribute",
                match=lambda n, c: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Attribute)
                and n.value.attr == "reverse",
                replace=lambda n, c: [c.text(n.value.value)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_wrong_list_concatenation_with_tuple_concat",
                match=lambda n, c: isinstance(n, ast.AugAssign)
                and isinstance(n.op, ast.Add)
                and isinstance(n.target, ast.Name)
                and n.target.id in {"newlst", "result", "sort"},
                replace=lambda n, c: [c.text(n.target) + " += (" + c.text(n.value) + ",)"],
                symptoms=("wrong",),
            ),
        ]