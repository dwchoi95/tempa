You are building a deterministic, local repair tool for ONE programming
assignment. You will be shown the problem, its test suite, and worked repairs
drawn from the class's buggy submissions. You write a Python module that repairs
these and *other* submissions with the same misconceptions — with no further
help from you at run time.

## Problem
{description}

## Test suite (the tool's patches are validated against the full suite)
{tests}

## Worked repairs to generalize (buggy → a correct fix)

Every buggy submission in the class was grouped by the repair it needs, and each
pair below is one group's most representative case.

Write a rule that reproduces the *transformation* from buggy to fixed and also
fires on OTHER submissions with the same misconception. Do not hard-code these
exact programs.

Two traps to avoid, in order of how much they cost:

- **One rule per pair.** Many of these pairs need the *same* transformation
  wearing different variable names, loop shapes, or helper functions. Merge them:
  one rule matching the shared AST pattern beats five rules that each fire on
  exactly one submission. Fewer, more general rules is the goal.
- **Rules that only fit the example.** A rule keyed on a specific identifier, a
  specific literal, or a specific statement order will fire on the pair you were
  shown and nothing else. Key on the structure that carries the misconception.

{samples}

## What to write

A single Python module. It MUST expose:

```python
import ast
from src.core.rewrite import Rewrite

class Fixer:
    def rules(self):
        return [ Rewrite(name=..., match=..., replace=..., symptoms=(...)), ... ]
```

Every rule is a `Rewrite`: a one-hole rewrite of ONE node of the program. You
do not edit source text yourself; the harness does, at exactly the node you
match, and nowhere else.

- `name`: a string naming the misconception it targets (e.g. `"strict_lt_should_be_lte"`).
- `match(node, ctx) -> bool`: called on every expression and statement node of a
  program; return True for the node your rule rewrites. Read the program only
  through `node` (its fields and subtrees) and `ctx`.
- `replace(node, ctx) -> list[str]`: the text(s) that replace that node. For an
  expression node, each text is an expression; for a statement node, each text
  is zero or more statements written at column 0 (the harness re-indents them;
  `""` deletes the statement). Return `[]` when there is nothing to propose.
  Build the text from the original pieces with `ctx.text(subnode)`, so unchanged
  sub-expressions keep the student's exact spelling.
- `symptoms`: a tuple of failure classes it addresses (`"wrong"`, `"timeout"`,
  or `"err:<ExceptionType>"`), used only to order the search -- never for
  correctness.

`ctx` is read-only: `ctx.text(n)` is the source text of node `n`, `ctx.parent(n)`
its parent node, `ctx.field(n)` the name of the parent's field holding it, and
`ctx.tree` the whole module.

To insert a statement, replace a neighbouring statement by itself plus the new
one (e.g. `ctx.text(n) + "\nreturn total"`); to add a missing call, replace the
expression `x.isupper` by `ctx.text(n) + "()"`. A replacement that would not
parse as the same kind of node is discarded, and parentheses are added where
precedence requires them.

### A worked example rule (relax a strict comparison to non-strict)

```python
def _is_strict_lt(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Lt))

def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]

class Fixer:
    def rules(self):
        return [Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt,
                        replace=_to_lte, symptoms=("wrong",))]
```

## Requirements
- Output ONLY one ```python code block: the complete module, importable as-is.
- Import only the standard library and `from src.core.rewrite import Rewrite`.
- Every rule is a `Rewrite`; do not return `Rule` objects or edit source text yourself.
- Write *problem-specific* rules targeting the misconceptions in the pairs above,
  plus a couple of generic slips (comparison flips, off-by-one on a `range`/index,
  a wrong `return`) if cheap. A submission no rule fires on escalates safely,
  whereas a bad rule fires everywhere, so omit a rule you cannot state cleanly.
  There is no target number of rules — as many as there are distinct
  transformations worth generalizing, and no more.
- Emit candidates only. Do not test, do not print, do not claim correctness —
  the harness validates every candidate against the full suite.
- No comments explaining your reasoning; a short docstring per rule is fine.

## Forbidden: wholesale rewrites
Each candidate must differ from its input by a **small, local edit** — a changed
operator, one rewritten expression, an inserted/removed statement, a fixed
argument or bound. A rule that **replaces an entire function or the whole module
with a fixed/"canonical" solution is not allowed**, even if it makes tests pass:
it defeats the tool's purpose. Patch size is measured (tree-edit distance over
the buggy AST) and reported; a repair that rewrites the program scores as badly
as no repair, and gives an instructor no misconception signal. If you cannot see
a targeted edit for a misconception, omit the rule and let the submission
escalate — do not paper over it by copying the fixed half of a pair. As a guard, never match a
`FunctionDef` or the module itself.

{feedback}
