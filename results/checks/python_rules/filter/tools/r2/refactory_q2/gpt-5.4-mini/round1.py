from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, s):
    return isinstance(node, ast.Name) and node.id == s


def _is_bool_true(node):
    return _is_name(node, "True") or _is_name(node, "true")


def _is_bool_false(node):
    return _is_name(node, "False") or _is_name(node, "false")


def _count_cmp(node, op_type, left_text, right_text, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], op_type)
        and ctx.text(node.left) == left_text
        and ctx.text(node.comparators[0]) == right_text
    )


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="day_param_should_be_used_in_unique_day",
                match=lambda n, ctx: _count_cmp(n, ast.Eq, "day", "day", ctx) or _count_cmp(n, ast.Eq, "date", "day", ctx),
                replace=lambda n, ctx: [ctx.text(n.left) + " == " + ctx.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="month_index_should_be_zero",
                match=lambda n, ctx: isinstance(n, ast.Subscript)
                and ctx.text(n).endswith("[1]")
                and isinstance(n.slice, ast.Constant)
                and n.slice.value == 1
                and isinstance(ctx.parent(n), ast.Compare),
                replace=lambda n, ctx: [ctx.text(n.value) + "[0]"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="count_comparison_should_be_equal_one",
                match=lambda n, ctx: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], (ast.LtE, ast.GtE, ast.Gt, ast.NotEq))
                and (
                    ctx.text(n.left) in {"counter", "count", "result", "total", "num", "days", "months", "appearance", "checker", "product", "value"}
                    or any(ctx.text(c) in {"1", "0", "2"} for c in n.comparators)
                ),
                replace=lambda n, ctx: [ctx.text(n.left) + " == " + ctx.text(n.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="true_literal_misspelling",
                match=_is_bool_true,
                replace=lambda n, ctx: ["True"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="false_literal_misspelling",
                match=_is_bool_false,
                replace=lambda n, ctx: ["False"],
                symptoms=("err:NameError", "wrong"),
            ),
            Rewrite(
                name="return_boolean_variable_not_comparison",
                match=lambda n, ctx: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Name)
                and ctx.text(n.value) in {"count", "result", "counter", "num", "tester", "flag", "appearance", "check", "days", "months"},
                replace=lambda n, ctx: [f"return {ctx.text(n.value)} == 1"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_return_true_on_any_match",
                match=lambda n, ctx: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Constant)
                and n.value.value is True
                and isinstance(ctx.parent(n), ast.If)
                and isinstance(ctx.parent(ctx.parent(n)), ast.If),
                replace=lambda n, ctx: [ctx.text(n)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_return_none_with_false",
                match=lambda n, ctx: isinstance(n, ast.Return) and n.value is None,
                replace=lambda n, ctx: ["return False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_call_should_use_day_argument",
                match=lambda n, ctx: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name)
                and n.func.id in {"unique_day", "unique_date"}
                and len(n.args) == 1
                and ctx.text(n.args[0]) in {"birthday[0]", "i[0]"},
                replace=lambda n, ctx: [f"{ctx.text(n.func)}({ctx.text(n.args[0]).replace('[0]', '[1]')})"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_should_pass_month_filtered_days",
                match=lambda n, ctx: isinstance(n, ast.Return)
                and isinstance(n.value, ast.Constant)
                and n.value.value is True
                and isinstance(ctx.parent(n), ast.If)
                and isinstance(ctx.parent(ctx.parent(n)), ast.For),
                replace=lambda n, ctx: [ctx.text(n)],
                symptoms=("wrong",),
            ),
        ]