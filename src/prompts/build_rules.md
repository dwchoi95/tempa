You are building a deterministic, local repair tool for ONE programming
assignment. You will be shown the problem, its test suite, and worked repairs
drawn from the class's buggy submissions. You write repair rules, in the rule
language described below, that repair these and *other* submissions with the
same misconceptions -- with no further help from you at run time.

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
  one rule matching the shared pattern beats five rules that each fire on
  exactly one submission. Fewer, more general rules is the goal.
- **Rules that only fit the example.** A rule keyed on a specific identifier, a
  specific literal, or a specific statement order will fire on the pair you were
  shown and nothing else. Key on the structure that carries the misconception.

{samples}

## The rule language

A rule rewrites ONE place of a program: one expression, one statement, or a run
of two or three consecutive statements. The engine finds the place, checks your
condition, and splices your rewrite there and nowhere else. A rule file is a
sequence of rules:

```rules
rule NAME
symptoms: wrong, err:IndexError
match: PATTERN
where: CONDITION
rewrite: TEMPLATE
table T: {{"key": "value", ...}}
```

`symptoms` (optional) lists the failure classes the rule addresses (`wrong`,
`timeout`, `err:<ExceptionType>`); it only orders the search. `where` and `table`
are optional. A section can span several indented lines; alternatives of `match`
or `rewrite` are separated by a line holding only `|`.

**Patterns** are Python code with metavariables:
- `$X` matches any expression; `$X:Name` a variable name, `$X:Int` an integer
  literal, `$X:Str` a string literal, `$X:Const` any literal, `$X:Attr` an
  attribute or parameter name (`$obj.$m:Attr()`), `$X:Stmt` one statement,
  `$X:Stmts` a run of statements (on its own line), `$o:Cmp`, `$o:Arith`,
  `$o:Bool` an operator (`$a $o:Cmp $b`).
- `$*xs` matches a run of list elements (call arguments, list items, parameters).
- `$_` or a bare `_` matches anything. A metavariable used twice must match equal code.
- A match of two or three statements on separate lines matches that many
  consecutive statements.
- A compound statement written as its header alone (`while $c <= $k:`) matches
  that header whatever its body; a rewrite written as a header alone keeps the
  matched body.

**Conditions** are `and`/`or`/`not` combinations of:
- `$x == $y`, `$x != $y` (equal code), `$k < 3` (integer literals),
  `text($x) in {{"a", "b"}}`, `text($x) == "s"`, `kind($x) == "Call"`, `len($xs) >= 1`;
- `regex($x, r"...")` (the source text of `$x` matches);
- `match($x, "PATTERN")` (`$x` itself matches PATTERN and binds its metavariables),
  `some($x, "PATTERN")` (some part of `$x` does);
- `builtin($v)`, `load($v)` (a name being read), `bound($x)` (the match bound `$x`,
  useful when alternatives bind different metavariables);
- where the place sits: `field("If", "test")`, `parent("PATTERN")`,
  `inside("PATTERN")` (the nearest enclosing `for`, `while`, `if` or `def` of that
  kind matches, e.g. `inside("def $f($*xs, $p, $*ys): $B:Stmts")` binds a parameter
  `$p` and the body `$B`), `first()`, `last()`, `prev("PATTERN")`, `next("PATTERN")`,
  `before("PATTERN")`, `after("PATTERN")` (earlier or later statements of the block).

A pattern inside a condition is a string on one line; write a line break as `\n`.

**Rewrites** are Python code with the bound metavariables; `${{T[$k]}}` looks up
the text of `$k` in table `T` (a rewrite whose key is missing proposes nothing).
For a statement place, a rewrite is zero or more statements (an empty rewrite
deletes them); write them at column 0, the engine re-indents.

**Names.** A rewrite may only use names that the match or the condition bound,
names written in the pattern itself, Python builtins, and names the rewrite
itself assigns (the engine renames those apart from the program's). To use the
function's parameter or another variable of the program, bind it -- e.g. with
`inside("def ...")` or `some($B, "$v:Name = _")` -- never guess its spelling.

### Example rules

```rules
rule rest_isupper_to_equality_form
symptoms: wrong
match: $X.isupper()
where: match($X, "$W[1:]")
rewrite: $X.upper() == $X

rule strict_lt_should_be_lte
symptoms: wrong
match: $a $o:Cmp $b
where: text($o) in {{"<", ">"}}
rewrite: $a ${{relax[$o]}} $b
table relax: {{"<": "<=", ">": ">="}}

rule empty_sequence_guard
symptoms: wrong, err:IndexError
match: return $e
where: inside("def $f($*xs, $p, $*ys): $B:Stmts") and some($e, "$p2:Name[0]") and $p2 == $p
rewrite:
    if not $p:
        return 0
    return $e

rule append_before_remove
symptoms: wrong
match:
    $a.remove($v)
    $b.append($w)
where: $v == $w
rewrite:
    $b.append($w)
    $a.remove($v)
```

## Requirements
- Output ONLY one ```rules code block holding the whole rule file.
- The engine rejects, with a reason it will show you: a rule that does not parse,
  a rewrite that does not parse at its place, a rewrite equal to its match, a
  rewrite of a `return` that drops the `return`, a rewrite that uses a name it did
  not bind, and a match of a `def` or `class`.
- Write *problem-specific* rules targeting the misconceptions in the pairs above,
  plus a couple of generic slips (comparison flips, off-by-one on a `range`/index,
  a wrong `return`) if cheap. A submission no rule fires on escalates safely,
  whereas a bad rule fires everywhere, so omit a rule you cannot state cleanly.
  There is no target number of rules -- as many as there are distinct
  transformations worth generalizing, and no more.
- Emit candidates only. The harness validates every candidate against the full suite.
- Small, local edits only: a changed operator, one rewritten expression, an
  inserted or removed statement, a fixed argument or bound. Never replace a whole
  loop or function with a canonical solution; patch size is measured and a
  rewrite of the program scores as badly as no repair.

{feedback}
