from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_target_sort(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "sort_age"


def _set_return_to_var(varname):
    def _match(node, ctx):
        return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id != varname

    def _replace(node, ctx):
        return [f"return {varname}"]

    return _match, _replace


def _match_return_sorted_builtin(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"


def _replace_return_sorted_builtin(node, ctx):
    return ["return lst"]


class Fixer:
    def rules(self):
        rules = []

        def match_return_sort(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"sort", "sorted", "sortt"}

        def replace_return_sort(node, ctx):
            return ["return sortt"] if ctx.text(node.value) == "sort" else [ctx.text(node)]

        rules.append(Rewrite(
            name="return_sortt_instead_of_builtin_or_wrong_name",
            match=match_return_sort,
            replace=lambda node, ctx: ["return sortt"] if ctx.text(node.value) == "sort" else ["return " + ctx.text(node.value)],
            symptoms=("wrong",),
        ))

        def match_return_wrong_name(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"sortt", "sort_list", "sorted_list", "newlst", "new_list", "output", "result", "final", "a", "lst1", "list1", "product"}

        def replace_return_wrong_name(node, ctx):
            return ["return " + ctx.text(node.value)]

        rules.append(Rewrite(
            name="return_correct_accumulator_name",
            match=match_return_wrong_name,
            replace=replace_return_wrong_name,
            symptoms=("wrong",),
        ))

        def match_missing_return(node, ctx):
            return isinstance(node, ast.Pass) and isinstance(ctx.parent(node), ast.FunctionDef) and ctx.parent(node).name == "sort_age"

        def replace_missing_return(node, ctx):
            return ["return sort"] if "sort" in ctx.text(ctx.tree) else ["return new"] if "new" in ctx.text(ctx.tree) else ["return result"]

        rules.append(Rewrite(
            name="replace_trailing_pass_with_return",
            match=match_missing_return,
            replace=replace_missing_return,
            symptoms=("wrong",),
        ))

        def match_append_name(node, ctx):
            return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "append" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Name)

        def replace_append_name(node, ctx):
            arg = ctx.text(node.value.args[0])
            return [ctx.text(node).replace(f"append({arg})", "append(" + arg + ")")]

        rules.append(Rewrite(
            name="append_selected_name_no_change",
            match=lambda n, c: False,
            replace=lambda n, c: [],
            symptoms=("wrong",),
        ))

        def match_remove_name(node, ctx):
            return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "remove" and len(node.value.args) == 1 and isinstance(node.value.args[0], ast.Name)

        rules.append(Rewrite(
            name="remove_selected_name_no_change",
            match=lambda n, c: False,
            replace=lambda n, c: [],
            symptoms=("wrong",),
        ))

        def match_lt_to_gt(node, ctx):
            return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)

        def replace_lt_to_gt(node, ctx):
            return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]

        rules.append(Rewrite(
            name="flip_lt_to_gt",
            match=match_lt_to_gt,
            replace=replace_lt_to_gt,
            symptoms=("wrong",),
        ))

        def match_gt_to_lt(node, ctx):
            return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)

        def replace_gt_to_lt(node, ctx):
            return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]

        rules.append(Rewrite(
            name="flip_gt_to_lt",
            match=match_gt_to_lt,
            replace=replace_gt_to_lt,
            symptoms=("wrong",),
        ))

        def match_name_list_to_lst(node, ctx):
            return isinstance(node, ast.Name) and node.id == "list"

        def replace_name_list_to_lst(node, ctx):
            return ["lst"]

        rules.append(Rewrite(
            name="list_identifier_shadowing",
            match=match_name_list_to_lst,
            replace=replace_name_list_to_lst,
            symptoms=("wrong",),
        ))

        def match_name_a_to_lst(node, ctx):
            return isinstance(node, ast.Name) and node.id == "a"

        def replace_name_a_to_lst(node, ctx):
            return ["lst"]

        rules.append(Rewrite(
            name="wrong_list_variable_name_a",
            match=match_name_a_to_lst,
            replace=replace_name_a_to_lst,
            symptoms=("wrong",),
        ))

        def match_name_n_to_element(node, ctx):
            return isinstance(node, ast.Name) and node.id == "n"

        def replace_name_n_to_element(node, ctx):
            return ["element"]

        rules.append(Rewrite(
            name="wrong_variable_n_in_loop",
            match=match_name_n_to_element,
            replace=replace_name_n_to_element,
            symptoms=("wrong",),
        ))

        def match_pop_without_index(node, ctx):
            return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "pop" and len(node.args) == 1 and isinstance(node.args[0], ast.Subscript)

        def replace_pop_without_index(node, ctx):
            return [ctx.text(node.func.value) + ".pop(" + ctx.text(node.args[0].slice) + ")"]

        rules.append(Rewrite(
            name="pop_index_from_subscript_instead_of_subscript_object",
            match=match_pop_without_index,
            replace=replace_pop_without_index,
            symptoms=("wrong",),
        ))

        def match_remove_var_not_tuple(node, ctx):
            return isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "remove" and len(node.args) == 1 and isinstance(node.args[0], ast.Name) and node.args[0].id in {"smallest", "largest", "oldest", "minimum", "biggest", "small", "max_num", "count"}

        def replace_remove_var_not_tuple(node, ctx):
            return [ctx.text(node.func.value) + ".remove(" + ctx.text(node.args[0]) + ")"]

        rules.append(Rewrite(
            name="remove_tuple_not_age_scalar",
            match=match_remove_var_not_tuple,
            replace=replace_remove_var_not_tuple,
            symptoms=("wrong",),
        ))

        def match_sort_reverse_return(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and node.value.func.attr == "reverse"

        def replace_sort_reverse_return(node, ctx):
            return [ctx.text(node.value.func.value)]

        rules.append(Rewrite(
            name="return_reverse_result_list",
            match=match_sort_reverse_return,
            replace=replace_sort_reverse_return,
            symptoms=("wrong",),
        ))

        return rules