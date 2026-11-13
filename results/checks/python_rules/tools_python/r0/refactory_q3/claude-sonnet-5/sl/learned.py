from src.core.repair import Rule
from src.core.rewrite import Rewrite
LEARNED = []


def _learned_dedup_single_pass_match(node, ctx):
    """Only the first detected duplicate is removed (single `if x in rest: pop`) instead of
    looping until every repeated element has been removed."""
    import ast
    if not isinstance(node, ast.If):
        return False
    test = node.test
    if not isinstance(test, ast.Compare) or len(test.ops) != 1 or not isinstance(test.ops[0], ast.In):
        return False
    left = test.left
    right = test.comparators[0]
    if not isinstance(left, ast.Subscript) or not isinstance(right, ast.Subscript):
        return False
    if not isinstance(left.value, ast.Name) or not isinstance(right.value, ast.Name):
        return False
    if left.value.id != right.value.id:
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not isinstance(stmt, ast.Expr) or not isinstance(stmt.value, ast.Call):
        return False
    call = stmt.value
    if not isinstance(call.func, ast.Attribute) or call.func.attr != 'pop':
        return False
    if not isinstance(call.func.value, ast.Name) or call.func.value.id != left.value.id:
        return False
    return True

def _learned_dedup_single_pass_replace(node, ctx):
    var = node.test.left.value.id
    code = f"for i in {var}[:]:\n    if {var}.count(i) > 1:\n        {var}.remove(i)"
    return [code]

LEARNED.append(Rewrite("dedup_single_pass", _learned_dedup_single_pass_match,
                       _learned_dedup_single_pass_replace, symptoms=('wrong', 'err:IndexError')))
