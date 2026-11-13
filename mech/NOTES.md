# A Lean mechanization of the footprint theorem

This directory mechanizes the paper's footprint theorem (Theorem 5) and the translation
behind it (Lemma A.3): an edit `q` of a program `p` behaves as `p` on every input whose
run never reaches the footprint F(p, q). It is a Lake project for Lean 4.35.0 with no
dependency beyond Lean's core and `Std`.

The development has three parts.

1. **PyCore**, the core language of the paper's Figure A.1, its small-step semantics, and the
   footprint theorem for it, proved by a lock-step simulation (`PyCore/`).
2. **Surf**, the Python of the paper's programs and repairs, node for node as CPython's `ast`
   gives it: its static analysis, the translation ⌊·⌋ into PyCore, and the syntactic half of
   the theorem for translated programs (`Surf/Syntax.lean` to `Surf/Canon.lean`). Surf also has
   a semantics of its own, written from the language reference (`Surf/Semantics.lean`), and a
   reference interpretation of Python's values and builtins for differential testing
   (`Surf/Ref.lean`).
3. **T2**, a stuttering simulation between Surf's semantics and PyCore's run of ⌊p⌋: the
   translation keeps outcomes, and the core run reaches the footprint's image only if the Surf
   run reaches the footprint. Composed with part 2, this gives the footprint theorem on Surf
   runs (`Surf/T2*.lean`).

Both semantics run over one abstract interface, `Py.Interp σ` (`Common/Interp.lean`), so every
theorem holds for every interpretation of constants, builtins and operations on values.

## What is proved

### PyCore

```lean
theorem PyCore.footprint_theorem {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option Val) (s : S)
    (h : NoReach I (inFootprint R p) (init p σ s)) :
    (∀ o, Terminates I (init p σ s) o ↔ Terminates I (init (editB R p) σ s) o) ∧
    (Diverges I (init p σ s) ↔ Diverges I (init (editB R p) σ s))
```

Let `q = editB R p`, the program `p` with the subtrees at the sites of `R` replaced. For every
interpretation `I` with initial state `s` and every initial module dictionary `σ`: if no step
of `p`'s run evaluates a node of F(p, q), then `p` ends with outcome `o` exactly when `q` does,
and `p` diverges exactly when `q` does. An outcome (`PyCore.Outcome`) is a normal end with the
output list, the final module dictionary and the interpretation's state; an uncaught exception
with the output and state; or a stuck configuration with the output and state.

- `PyCore.footprint_theorem_min`: the same conclusion when the run evaluates no node of
  `rootsB R p` (the site roots, not their subtrees) or `flagged R p` (the occurrences of part (2)
  and, instead of all of `p`, the `def` or lambda node of each function whose kind changes).
- `PyCore.footprint_theorem_of_good`: the same for any label set `F` with `goodB R F [] p`.
- `PyCore.step_sim` (Lemma A.2): `Rel R F c d → (∀ l, focus c = some l → ¬ F l) →
  OptRel (Rel R F) (step I c) (step I d)`. Both configurations step to related ones, or neither
  steps.

How the statement reads the paper:

- **Edits** (`Edit`): an expression replaced by an expression, a statement of a block by a list
  of statements (a deletion, a replacement, or an insertion `[t, s]` before `s` or `[s, t]` after
  the last statement `s`), a handler clause by a handler clause. Part (1) is the set of nodes of
  the replaced subtrees. The appendix's alignment of `p` and `q` is not mechanized: the theorem
  holds for every set of sites, so in particular for the sites the alignment finds.
- **The footprint** (`footprint?`, membership `inFootprint`): part (1) `part1B`; part (2) `part2`,
  the occurrences outside the sites of a name classified differently in `q` in their scope or in
  a scope around it (`alike`); part (3) `kindChanges`, which makes the footprint all of `p`.
- **Reaching a node**: a step evaluates the node `focus c`: the expression or statement it enters,
  or the handler clause whose expression `Catch` evaluates. Steps that continue a node already
  entered evaluate no new node. `NoReach I F c` says no configuration of the run from `c` focuses
  a label in `F`.
- **Labels**: nodes carry natural-number labels and F is a set of labels. The theorem holds for
  any labelling; with distinct labels a label set is a node set.
- **The relation** (`Rel`): `q`'s code is the edit of `p`'s; values, cells, the module
  dictionary, the output, the interpretation's state and the object counter are equal; closure and
  frame environments agree on the names classified alike. Cells are addressed by (frame id, name)
  and objects by a counter both runs advance together, so the paper's injection β is the identity.
- **No other hypothesis.** Programs that CPython rejects (`return` at module level, `nonlocal`
  without a binding) are not excluded: the semantics gets stuck or raises, deterministically, in
  both runs. `step` is a function, so determinism holds by construction.
- **Class bodies.** A class body starts with `__module__ = __name__` and `__qualname__ = q`, stored
  through the body's own classification, so both names are in `bind(S)` of every class scope and
  the class node counts as an occurrence of `__name__`, `__module__` and `__qualname__` in the
  body's scope. A `global __qualname__` added in a dead branch of the body thus puts the class node
  in part (2) (`examples/classdunder.sx`).
- **Exceptions** get their `__context__` when raised, from the innermost handler running on the
  stack (CPython's topmost exception state); a `StopIteration` leaving a generator becomes a
  `RuntimeError` whose cause and context it is.

### Surf and the translation

```lean
theorem Surf.footprint_theorem_surf {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option PyCore.Val) (s : S)
    (hp : (labelsB p).Nodup) (hq : (labelsB (editB R p)).Nodup) (h0 : 0 ∉ labelsB p)
    (hd : NoDot p) (hdq : NoDot (editB R p)) (hg : GenOk p) (hk : KeepsLabels R)
    (hr : regB R [] p = true) (hgp : regB {} [] p = true) (hgq : regB {} [] (editB R p) = true)
    (h : PyCore.NoReach I (imgF R p) (PyCore.init (tr p) σ s)) :
    (∀ o, PyCore.Terminates I (PyCore.init (tr p) σ s) o ↔
          PyCore.Terminates I (PyCore.init (tr (editB R p)) σ s) o) ∧
    (PyCore.Diverges I (PyCore.init (tr p) σ s) ↔ PyCore.Diverges I (PyCore.init (tr (editB R p)) σ s))
```

For a Surf edit `R` and `q = editB R p`: if the PyCore run of ⌊p⌋ evaluates no node the
translation made for a node of F_surf(p, q) (`imgF R p x := ∃ l k, x = sub l k ∧ k < 64 ∧ inF R p l`),
then ⌊p⌋ and ⌊q⌋ have the same outcomes and diverge together. The steps:

- `Surf.translation_keeps_scopes (p) (hp : NoDot p) (hg : GenOk p)` (T1): every occurrence of a
  name in `p` has an image in ⌊p⌋ at a node made for it (`sub l k`, `k < 64`), in the image of its
  scope chain, classified alike; every other occurrence in ⌊p⌋ is of a fresh name; every function
  (`def`, lambda, comprehension) has its image at `sub l 1`, of the same kind; ⌊p⌋ has no other
  function. `Surf.cls_tr` gives the classification on every chain, `Surf.kind_tr` the kinds.
- `Surf.tr_edit (R) (p) (hp) (h0) (hk) (hr) : tr (editB R p) = PyCore.editB (trEdit R p) (tr p)`:
  the translation commutes with edits. `trEdit R p` is the PyCore edit that replaces the nodes
  made for each Surf site.
- `Surf.roots_image`: the roots of the PyCore sites of `trEdit R p` lie in `imgF R p`.
- `Surf.flagged_image_canon`: the flagged items (`PyCore.flagged`) of `trEdit R p` on ⌊p⌋ lie in
  `imgF R p`, given the fresh-name invariant `FreshCanon` of ⌊p⌋ and ⌊q⌋, which
  `Surf.fresh_canon (p) (hp) (hd) (hg : regB {} [] p)` proves of every translated program.
- `footprint_theorem_surf` is `PyCore.footprint_theorem_min` for `trEdit R p`, rewritten by
  `tr_edit`. The full PyCore footprint F(⌊p⌋, ⌊q⌋) need not lie in the image: when the qualified
  name of a class changes, PyCore's part (1) holds the whole `def` or class whose name changed,
  body included. The smaller footprint of `footprint_theorem_min` does lie in it.

### T2: Surf runs

```lean
theorem Surf.T2.t2 (I : Py.Interp σ) (p : List Stmt) (W : WF p) (σ0 : Std.HashMap Name Val) (s0 : σ) :
    (∀ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) →
      ∃ o', PyCore.Terminates I (PyCore.init (tr p) (fun x => σ0[x]?) s0) o' ∧ OCorr o o') ∧
    (∀ o', PyCore.Terminates I (PyCore.init (tr p) (fun x => σ0[x]?) s0) o' →
      ∃ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) ∧ OCorr o o') ∧
    (Sem.Diverges I (Sem.init p σ0 s0) ↔ PyCore.Diverges I (PyCore.init (tr p) (fun x => σ0[x]?) s0))
```

The translation keeps outcomes: for every interpretation, the Surf run of `p` and the PyCore run
of ⌊p⌋ from the same module dictionary and interpretation state terminate with corresponding
outcomes, in both directions, or diverge together. `OCorr` asks for the same interpretation state
(which holds the output: `print` is the interpretation's), the same exception, and module
dictionaries equal on every name with no leading dot; PyCore's own output list stays empty.

```lean
theorem Surf.T2.reach_corr (I : Py.Interp σ) (R : Edit) (p : List Stmt) (W : WF p)
    (σ0 : Std.HashMap Name Val) (s0 : σ)
    (h : NoReachT p I (inF R p) (Sem.init p σ0 s0)) :
    PyCore.NoReach I (imgF R p) (PyCore.init (tr p) (fun x => σ0[x]?) s0)
```

The reach correspondence: if the Surf run of `p` touches no node of F_surf(p, q) (`Touch`, below),
the PyCore run of ⌊p⌋ evaluates no node made for one.

```lean
theorem Surf.T2.footprint_theorem_surf_sem (I : Py.Interp σ) (R : Edit) (p : List Stmt)
    (σ0 : Std.HashMap Name Val) (s0 : σ) (W : WF p) (Wq : WF (editB R p))
    (hk : KeepsLabels R) (hr : regB R [] p = true)
    (h : NoReachT p I (inF R p) (Sem.init p σ0 s0)) :
    (∀ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) →
      ∃ o', Sem.Terminates I (Sem.init (editB R p) σ0 s0) (· = o') ∧ OEq o o') ∧
    (∀ o', Sem.Terminates I (Sem.init (editB R p) σ0 s0) (· = o') →
      ∃ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) ∧ OEq o o') ∧
    (Sem.Diverges I (Sem.init p σ0 s0) ↔ Sem.Diverges I (Sem.init (editB R p) σ0 s0))
```

The footprint theorem on Surf runs: if the Surf run of `p` touches no node of F_surf(p, q), then
`p` and `q` end with equal outcomes (`OEq`: the same state, and the same exception or module
dictionaries equal on the names with no dot) and diverge together. It chains `t2` for `p`,
`footprint_theorem_surf` (its premise from `reach_corr`), and `t2` for `q`.

### The hypotheses, and why every Python program meets them

`footprint_theorem_surf_sem` takes `WF p`, `WF q`, `KeepsLabels R` and `regB R [] p`, and derives
the hypotheses of `footprint_theorem_surf` from them (`hp`, `hq` from `nodup`; `h0` from `pos`;
`hd`, `hdq` from `nodot`; `hgp`, `hgq` from `reg`; `hg` from `ok` by `genOk_of_ok`).

`WF p` (`Surf/T2Rel.lean`) has five fields.

| field | says | why every Python program meets it |
| --- | --- | --- |
| `nodup : (labelsB p).Nodup` | labels are distinct | labels are positions: `export_surf.py` numbers the AST's nodes 1, 2, … in preorder |
| `pos : ∀ l ∈ labelsB p, 0 < l` | no label is 0 | the exporter starts at 1; label 0's nodes `sub 0 k` hold the module's `SETUP_ANNOTATIONS` |
| `nodot : NoDot p` | no name of `p` starts with a dot | no Python identifier does, mangled or not; every fresh name of the translation does |
| `reg : regB {} [] p` | every augmented assignment's target is a name, an attribute or a subscript | the grammar allows no other (`(a, b) += 1` is a `SyntaxError`) |
| `ok : okB p` | the shapes CPython's parser produces | see below |

`okB` holds of every AST CPython's parser produces: identifiers, operator class names (`Add`,
`Eq`) and module paths hold no `:` or `,`, are not empty or `*`, and do not start with `=`; a
constant is a literal's `repr`, which never starts with `$`; a Boolean operation has two operands
or more; a comparison has one operator per operand after the first, and at least one; a
comprehension has a generator at least, one element (two for a dictionary comprehension), clause
targets that are targets, and no `yield` in its own scope; a starred expression stands only in a
display, a call's arguments or a target; an annotated assignment's target is a name, an attribute
or a subscript; `raise … from c` has an exception; `from m import *` imports nothing else and
`import` imports no `*`; a handler with no class has no name; no `del` target is starred. The
translation writes names into the constants it makes (`$op:getattr:x`, `$kw:x`, `$param:…`), which
split at `:` and `,`; `okName` keeps that split exact. `GenOk p` (every generator expression has one
element, as `ast.GeneratorExp` has one `elt`) follows from `okB p`.

The other hypotheses:

- `Wq : WF (editB R p)`: `q` is a Python program too, labelled by positions.
- `hk : KeepsLabels R`: each expression replacement carries the label of the node it replaces.
  Labels are positions, and a replacement's root sits at its site's position.
- `hr : regB R [] p`: outside the statement sites, each augmented target and the replacement of a
  replaced target are names, attributes or subscripts. They are augmented targets of `p` and of `q`.
- `h : NoReachT p I (inF R p) (Sem.init p σ0 s0)`: the premise of the theorem.

Each condition is needed. `SurfTests.lean` and `CexTr.lean` give an edit for each that breaks the
commutation or puts a flagged node outside the image when the condition is dropped: a comparison
operand replaced by a node with another label (`KeepsLabels`), a replacement that reuses a label of
`p` (`hq`), a replacement that writes a dotted name (`hdq`), a tuple as an augmented target
(`regB`), and a site at label 0 (`h0`).

## Status

PyCore, Surf and T2 are proved with no `sorry`, `admit` or `axiom` declaration, and `lake build`
(every default target) passes. `lake env lean Axioms.lean` and `lake env lean AxiomsT2.lean` print
the axioms of the main theorems and lemmas, 29 and 52 declarations. Each depends on `propext`,
`Classical.choice` and `Quot.sound` at most; the main theorems on all three:

```text
'PyCore.footprint_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'PyCore.footprint_theorem_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'PyCore.step_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.translation_keeps_scopes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.tr_edit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.fresh_canon' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.footprint_theorem_surf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.T2.step_sim' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.T2.t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.T2.reach_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Surf.T2.footprint_theorem_surf_sem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The reference interpretation (`Surf/Ref.lean`, `Surf/RefFloat.lean`), the runners and the CLI are
executable code with no proofs. No theorem depends on them: the theorems quantify over every
interpretation.

## Files

Line counts by `wc -l`, `.lake` excluded. 39,093 lines of Lean in all.

| file | lines | content |
| --- | ---: | --- |
| `Common/Interp.lean` | 701 | the interface: `Py.Val`, `Py.Op`, `Py.Res`, `Py.Interp`, constants, core gadgets, markers, `bindArgs`, `memo` |
| `PyCore/Syntax.lean` | 420 | PyCore's syntax, own body, `bind`/G/N, classification `clsOf`, kind, edits, the footprint |
| `PyCore/Semantics.lean` | 981 | configurations, `step`, `focus`, `run`, `init`, outcomes, `NoReach`; the core gadgets' steps |
| `PyCore/Relation.lean` | 256 | the invariant `goodE`/`goodS`/`goodB` and the relation `Rel` (Definition A.1) |
| `PyCore/Sim.lean` | 1,161 | `step_sim` (Lemma A.2), `run_sim`, `same_outcome` |
| `PyCore/Theorem.lean` | 355 | `footprint_good`, `init_rel`, `footprint_theorem`, `_of_good`, `_min` |
| `PyCore/Cli.lean` | 215 | the `pycore` command on PyCore programs and edits |
| `Surf/Syntax.lean` | 496 | Surf's syntax, scopes, mangling, own body, classification, kind, occurrences, `qualIn`, `inlinedLocal` |
| `Surf/Translate.lean` | 475 | the translation `tr` (`trE`, `trT`, `trD`, `trAug`, `trS`, `trB`, `trHs`), `trScope`, `trChain`, `sub`, `fresh`, markers |
| `Surf/T1.lean` | 1,431 | (T1): `scope_facts`, `cls_tr`, `kind_tr`, `items_tr`, `translation_keeps_scopes`; `NoDot`, `GenOk` |
| `Surf/Footprint.lean` | 655 | Surf edits, F_surf (`p1B`, `alike`, `part2`, `kindChanges`, `footprint?`), the PyCore sites and `trEdit`, `regB`, `KeepsLabels`; the executable checks `commutes`, `imageOk`, `imageMinOk`, `rootsOk` |
| `Surf/Commute.lean` | 2,257 | `trB_edit` (the local commutation), `trEdit_ok`, `tr_edit`, `tr_footprint` |
| `Surf/Image.lean` | 631 | `inF`, `imgF`, `roots_image`, `alike_tr`, `kind_edit_tr`, `flagged_image_of`, `footprint_theorem_surf_of` |
| `Surf/Chain.lean` | 862 | (T1) for edits: `trB_itemsR`, `flagged_image_fresh` |
| `Surf/Fresh.lean` | 245 | `poccB_edit`, `alike_of_xf`, `FreshCanon`, `fresh_not_bad`, `flagged_image_canon`, `footprint_theorem_surf_canon` |
| `Surf/Own.lean` | 613 | the nodes' entries (`ncB`), a fresh name's home, the translation's facts about fresh names (`trB_fc`) |
| `Surf/Canon.lean` | 866 | the occurrences of fresh names (`trB_oc`), `fresh_inj'`, `fresh_canon`, `footprint_theorem_surf` |
| `Surf/Cli.lean` | 176 | `pycore surf`: Surf s-expressions in, both classifications out |
| `Surf/Semantics.lean` | 1,069 | `Surf.Sem`: Surf's small-step semantics over `Py.Interp σ` |
| `Surf/RefFloat.lean` | 223 | IEEE doubles computed exactly with integers |
| `Surf/Ref.lean` | 3,895 | the reference interpretation `Ref.interp` |
| `Surf/Run.lean` | 236 | `pycore run`: programs on test inputs, as the test harness runs them |
| `Surf/RunCore.lean` | 251 | `pycore runcore`: Surf.Sem against PyCore on ⌊p⌋ under a traced interpretation |
| `Surf/T2Sim.lean` | 538 | the generic stuttering simulation with history: `SimStep`, `sim_term_ab`/`_ba`, `sim_div_ab`/`_ba`, `sim_reach` |
| `Surf/T2Rel.lean` | 1,503 | the relation: `WF`, `okB`, `touchB`, `Good*`, `KRel` and its families, `CR`, `Special`, `FRel`, `ORel`, `Ids`, `EnterInv`, `CRel`, `PendRel`, `OCorr`, `Touch`, `NoReachT`, `μ`, `Goal` |
| `Surf/T2Cases.lean` | 4,292 | framework lemmas and the cases of the constructs ⌊·⌋ maps to PyCore's own |
| `Surf/T2Call.lean` | 2,182 | cases: calls, `def`, lambdas, parameters, decorators |
| `Surf/T2Class.lean` | 1,508 | cases: classes, `SETUP_ANNOTATIONS`, the initial configurations (`init_sim`) |
| `Surf/T2Comp.lean` | 2,269 | cases: comprehensions and generator expressions |
| `Surf/T2Loop.lean` | 847 | cases: `for … else` |
| `Surf/T2Assign.lean` | 2,234 | cases: assignments, unpacking, augmented and annotated assignments, `del` |
| `Surf/T2Access.lean` | 1,411 | cases: attributes, subscripts, slices, unary operators, displays, f-strings |
| `Surf/T2Misc.lean` | 2,132 | cases: comparison chains, `yield from`, `raise`, imports, `assert`, bare `except`; `inF_labels` |
| `Surf/T2.lean` | 541 | `step_sim` (dispatch to the cases), `t2`, `reach_corr`, `genOk_of_ok`, `footprint_theorem_surf_sem` |
| `Main.lean` | 30 | the `pycore` executable |
| `Common.lean`, `PyCore.lean`, `Surf.lean` | 1, 5, 12 | library roots |
| `Axioms.lean` | 34 | `#print axioms`, PyCore and Surf |
| `AxiomsT2.lean` | 57 | `#print axioms`, T2 |
| `Tests.lean` | 451 | 27 `#guard`s: PyCore runs on a toy interpretation (the paper's witnesses, edits the footprint clears, exception contexts, error classes) |
| `SurfTests.lean` | 293 | 37 `#guard`s: both classifications against CPython 3.11's symbol tables; commutation and image checks on edits |
| `SurfSemTests.lean` | 83 | 18 `#guard`s: Surf.Sem with `Ref.interp`, one program per construct family, against CPython 3.13 |
| `CoreTests.lean` | 64 | 18 `#guard`s: the same programs by Surf.Sem and by PyCore on ⌊p⌋, traces compared |
| `CexTr.lean` | 136 | 24 `#guard`s on edits that test locality and the hypotheses (not a default target) |
| `examples/*.sx` | 46 | five CLI inputs: the paper's two necessity witnesses, an insertion, nested scopes, a class's implicit `__qualname__` |
| `lakefile.toml`, `lean-toolchain` | 27, 1 | Lake configuration: libraries `Common`, `PyCore`, `Surf`, the tests; the executable `pycore` |

Scripts outside this directory, in the repository's `results/checks/`:
`lean_cls/export_surf.py` (Python `ast` to Surf s-expressions, labels in preorder, nothing
resolved or rewritten), `lean_cls/surf_cls.py` and `lean_cls/symtab311.py` (the classification
check), `lean_sem/difftest.py`, `lean_sem/progs.py` (Surf.Sem against CPython),
`lean_sem/coretest.py` (Surf.Sem against PyCore on ⌊p⌋), `lean_sem/gen_tests.py` and
`lean_sem/cases/` (`SurfSemTests.lean`), `lean_sem/census.py` (what the programs use),
`lean_sem/setfuzz.py` (set iteration order).

## The interpretation interface (`Common/Interp.lean`)

The core semantics (PyCore's or Surf's) owns names, frames, cells, closures, generators and class
bodies. Everything else is an interpretation:

```lean
structure Py.Interp (σ : Type) where
  const : String → Val                      -- a constant's value, from its repr
  builtin : Name → Option Val               -- the builtins' namespace
  op : σ → Op → List Val → Res σ            -- every operation on values
```

- `Py.Val`: `prim c`, `no` (the core's false), `none`, `bool`, `int` (unbounded), `float` (IEEE
  bits), `str`, `tuple`, `data tag vs` (an immutable value of the interpretation: slices, ranges,
  views), `fn o` and `gen o` (a function object and a generator of the core, by address), `obj o`
  (an object of the interpretation's state: lists, dicts, sets, classes, instances, iterators),
  `bfun k`, `meth f self`, `next`, `err k args` (a builtin exception), `exn v context cause`,
  `op o`.
- `Py.Op`: every operation, with the values it takes: `binop` (operators, comparisons, in-place
  operators such as `Add=`), `unop`, `truth`, `iter`, `next`, `getattr`/`setattr`/`delattr`,
  `getitem`/`setitem`/`delitem`, `call kws` (of what is no function object of the core),
  `display d` (list, tuple, set, constant set, dict, slice, f-string, keyword arguments),
  `accum k` (a comprehension's element), `unpack before star after`, `convert`, `format`,
  `mkClass x q kws ns`, `mkExc`, `excMatch`, `import`, `importFrom`, `importStar`.
- `Py.Res σ`: `ok s v`; `raise s e`, a new exception, which the core gives its context; `reraise
  s e`, a callback's exception passed on; `call s f args kws k`, a callback: the core calls `f`
  and hands the outcome and the state to the native continuation `k`. Callbacks run `sum(genexp)`,
  `sorted(key=…)`, `map(f, xs)`, `__init__` and the special methods of instances.
- **Lock step.** Every operation is a function of the state and the values. A value shows a
  function object or a generator of the core by its address only, so two runs with equal states
  and values that agree up to closures' code get equal results from every operation.
- **Constants the core fixes** (`Py.constVal`): `$false` (`Val.no`, false in every truth test
  without asking the interpretation), `$true`, `$none`, `$args` (the empty argument record),
  `$next` (the core's `next`), `$op:…` (an operation, e.g. `$op:getattr:x`), the gadgets' names
  and the markers (`Val.prim`). Any other constant is `I.const`.
- **Core gadgets** (`Py.Gadget`): what the translation needs the core to do without the
  interpretation, each a constant whose call on an argument record (`$args` extended by `,`) the
  core performs: `$call` (a call with positional, starred and keyword arguments), `$def:N:NP`
  (a function object with its signature and defaults, then its decorators), `$cls:N` (a class
  statement's arguments), `$unpack`, `$display:list|tuple|set`, `$cunary:op` and `$ctuple` (a set
  item's constness), `$setup` (`SETUP_ANNOTATIONS`), `$annot:x`, `$starstore`, `$reraise`,
  `$raise:K`, `$raisefrom`, `$item:I`, `$set:x`/`$get:x` (the frame's own cell of a fresh name),
  `$stuck` (no step).
- **Markers** (`Py.isMarker`): `$pos`, `$star`, `$c0`, `$c1`, `$nc`, `$kw:x`, `$kwstar`,
  `$param:<kind><=?><name>`. A gadget reads its children's markers, which come after all the
  values in its record.
- `Py.bindArgs`: CPython's `initialize_locals`, a pure function of the signature, the defaults
  and the arguments; `TypeError` for an argument too many or missing, an unexpected keyword, or a
  parameter given twice. A `**` parameter's dictionary is made by `Op.display`.
- `Py.memo`, with `memo_eq : (memo xs g).get = g`: what a frame caches from syntax alone (the
  classification of names, a closure's cells), computed once.

## Surf.Sem, and what the theorems exclude

`Surf.Sem` (`Surf/Semantics.lean`) is a CEK machine like PyCore's, over any `Py.Interp σ`,
written from the language reference, with CPython 3.13's order where the reference leaves it
open, and not through the translation. It covers every Surf construct. A comprehension is a
function scope: the scope around evaluates the first iterable and its `iter`, then calls the
comprehension's function on it. Defaults are evaluated at the `def`, after the decorators and
before the annotations, and stored with the function object; decorators apply innermost first. An
augmented assignment evaluates its target's parts once and applies the in-place operator. `for`
catches `StopIteration` around its `next` call only. A comparison chain evaluates each middle
operand once. Module- and class-level annotated assignments store into `__annotations__`. An
unset name read in a list, set or dict comprehension raises `UnboundLocalError` when it is a local
of the enclosing function, as CPython 3.13's inlining (PEP 709) makes it (`inlinedLocal`, in both
semantics).

The reference interpretation `Ref.interp` (`Surf/Ref.lean`) implements what the programs use
(`lean_sem/census.txt`, over the 2,970 buggy programs and the 4,693 distinct repairs): `int`,
`bool`, `None`, `float`, `str`, `list`, `tuple`, `dict` (`Counter`, `defaultdict`, `OrderedDict`),
`set`, `frozenset`, `deque`, `range`, slices, iterators, user classes with C3 MRO, the builtins and
methods they call, and the modules `math`, `sys`, `collections`, `itertools`, `functools`, `heapq`,
`bisect`, `copy`, `string`, `operator`, `queue`, `typing`. What it lacks raises `$Unsupported`,
which the state records, so a handler cannot hide it; such a run is not covered. Floats are
computed exactly with integers (shortest `repr`, correctly rounded parsing and division, `%.nf`
rounding of the exact binary value); set iteration follows CPython's `setobject.c` table. These were
checked against CPython 3.13 on 3,027 doubles and on 1,500 random programs of set operations for
each of the seeds 0 to 3 (`setfuzz.py 1500 SEED`); all agree.

### Deviations from CPython

1. **Identity** (`Py.Val`). Numbers, strings, tuples, exceptions and ranges have no identity, so
   `is` compares them structurally. An exception is a value, so its context is set whenever it is
   raised while a handler runs; CPython skips `raise e` of the handled `e` itself.
2. **Function objects are opaque** (the interface). The interpretation sees a function or a
   generator of the core by address only: `f.__name__`, `repr(f)`, and `repr` of an instance with no
   `__repr__` are not covered.
3. **Annotated assignment** (Surf). A parenthesized name target `(x): int` is treated as simple;
   Surf does not keep `ast`'s `simple` flag.
4. **Recursion limit** (the runner). A run whose stack passes 19,900 frames is not covered (the
   harness sets 20,000).
5. **Strings** (`Ref`). Strings are sequences of code points, but case mapping and character
   classes (`upper`, `isupper`, `isdigit`, `isalpha`, `title`, …) are ASCII only.
6. **String hashes** (`Ref`) are CPython's under `PYTHONHASHSEED=0`, so a set of strings iterates as
   CPython's does with that seed.
7. **Sorting** (`Ref`) is a stable merge sort: the result of CPython's Timsort for a consistent
   order, with another sequence of `__lt__` calls.
8. **itertools** (`Ref`): `permutations`, `combinations`, `product`, `groupby` and `accumulate`
   build their output when called, so an infinite input does not terminate.
9. **Not modeled** (`Ref`, `$Unsupported`): `send`/`throw`/`close` of generators, class keywords
   (metaclasses), subclasses of builtin types other than `object` and the exceptions, `__new__`,
   user `__hash__`/`__eq__` on dictionary keys and set elements, `super`, properties with setters,
   `id`, `hash` of what is no int, `print` to a file, `open`, what `random`, `time`, `os`, `io`,
   `threading` provide (importing them is covered), regular expressions beyond character classes,
   `.`, anchors and greedy quantifiers, `int ** n` for `n > 100000`, repetitions over 50 MB or
   10^7 items, and CPython's 4,300-digit limit on `int` to `str`. A bound special method of a builtin
   value (`(5).__ne__`) is the operator, so on an operand of another type it gives the operator's
   result rather than `NotImplemented`.
10. **`StopIteration` subclasses** raised by a user `__next__` end a `for` loop in CPython; here only
    `StopIteration` does.
11. **Steps** (`Ref`). The interpretation returns to the core between long internal loops and calls
    a bound method by a callback. This changes the step count, not the outcome.
12. **`SETUP_ANNOTATIONS` always** (Surf.Sem, ⌊·⌋). Every module and class body starts by setting
    `__annotations__ = {}` unless set; CPython does so only in a body that holds an annotated
    assignment. A setup that depended on the body's content would break the footprint theorem and
    `tr_edit`: an annotated assignment inserted in a branch never taken would add `__annotations__`
    to the final namespace. The difference shows only to a program that names `__annotations__` or
    introspects.

Unobservable choices, in both semantics: a truth test of `Val.bool b` is `b` without the
interpretation; `yield from` takes a generator of the core as its delegate without `Op.iter`
(`iter` of a generator is the generator); `from m import *` drops dotted names, which no
identifier is.

### What the theorems exclude

The theorems hold for every Surf program and every interpretation. What they say about Python
stops where Surf.Sem's model of Python stops, as the paper's Theorem 5 and Lemma A.3
state:

- **Syntax outside Surf**: `with`, `try … finally`, `match`, `async`/`await`, `except*`, type
  parameters.
- **Code and frame introspection**: `eval`, `exec`, `locals`, `globals`, `vars`, `dir()` with no
  argument, `__dict__` of a module, frame objects. They observe bindings without naming them. An
  interpretation sees no frame of the core, and the module dictionaries of ⌊p⌋ and ⌊q⌋ hold the
  translation's fresh names, which only introspection could see; `OCorr` and `OEq` compare
  dictionaries on the names with no dot. `Ref` raises `$Unsupported` for `eval`, `exec`, `locals`,
  `globals`, `vars` and `dir`.
- **Object death**: objects never die, so finalizers (`__del__`) and weak-reference callbacks do
  not run.
- **`__class__` and bare `super()`**: the implicit `__class__` cell of methods is not modeled; a
  name `__class__` in a method is an ordinary name.
- **`__annotations__`**: see deviation 12.

`lean_sem/census.txt` finds none of these in the 2,970 buggy programs and the 4,693 distinct
repairs: no program names `__annotations__` or calls `vars`, `dir`, `locals`, `globals` or reads
`__dict__`.

## The translation (`Surf/Translate.lean`)

⌊p⌋ is `tr p = setupS 0 :: trB [] p`. The translation is a homomorphism on control flow:
conditional and Boolean expressions, `if`, `while … else`, `break`, `continue`, `return`,
`raise`, `try` with several handlers and `else`, `global`, `nonlocal`, `yield` and `yield from` are
PyCore's own. Each Surf statement becomes one PyCore statement (several are grouped by a `try` with
no handler and no `else`, `blk l`). Scopes are kept: a `def`, a lambda and a comprehension become a
PyCore lambda (a comprehension's is the comprehension function `λ°`), a class a class, and no
other scope is added. A translated run asks the interpretation for exactly the operations Surf.Sem
asks for, with the same values, in the same order, and allocates the same objects in the same
order: every operation is a call of a constant `$op:…` on an argument record, and what Surf's core
does itself is a call of a core gadget.

**Labels.** The `k`-th node made for the Surf node labelled `l` is labelled `sub l k = 64 l + k`,
`k < 64`; the root of the translation of `l` is `sub l 0`. A node's own nodes use `k < 46`; the
nodes made for it in its parent's place use `k ≥ 46`: 50 the constness marker of a part of a set
item, 54 a dead branch and 55 the stop for a target CPython rejects, 56 a parameter's marker, 57 an
item's, argument's, base's or keyword's marker, 58 an annotation's key store, 59 and 61 an unpacked
item, 60 a bare annotated target's binding, 62 a bare annotated target's parts, 63 a target's
source. The module's `SETUP_ANNOTATIONS` is labelled `sub 0 4`, `sub 0 5`, `sub 0 6`, below 64,
which no Surf node's translation uses since Surf labels start at 1.

**Locality.** Everything the translation takes from a Surf node lives in PyCore nodes made for that
node. A parent's nodes depend only on the parent's own fields (its operator, its number of
children, its chain), never on a child's form. What a parent's gadget must know about a child at
run time is the child's **marker**, a constant made for the child that the gadget reads when it
runs: `$pos` or `$star` for a positional item or argument (`starMark`), `$kw:x` or `$kwstar` for a
keyword (`kwMark`), a set item's constness `$c0`, `$c1` or `$nc`, computed by `$cunary` and
`$ctuple` from the markers of its parts when it is a sign or a tuple (`constMark`), and
`$param:<kind><=?><name>` for a parameter (`paramMark`). An unpacking reads its shape from its
targets' markers. A comprehension's translation does not depend on its body's walrus targets:
`λ°` binds them in the scope around. The parent's nodes still depend on fields of children that are
no site of any edit: which parameters of a `def` have defaults and annotations, and their kinds
(the order of evaluation), and whether a dictionary item is `**m` (an item has no label). An edit
can change those only by replacing the parent.

**Code CPython rejects** is stuck where Surf.Sem is stuck, with its subterms kept in a branch that
never runs (`dead r ss` tests the constant `$false`), so classifications, kinds and occurrences
need no grammar hypothesis.

**Fresh names.** `fresh tag l = "." ++ tag ++ toString l`, for the Surf node `l`: `t` (an
assigned value), `g` (a `for` loop's flag; an augmented target's old value), `v` (a `for` loop's
item; an augmented assignment's new value), `i` (a `for` loop's iterator; a comprehension's
parameter), `j` (a later clause's iterator), `s` (a `for` loop's `StopIteration`), `e` (a handler
with no name), `o`, `k` (an augmented target's object and key), `u` (an unpacked tuple), `m` (a
`from` import's module), `acc` (a comprehension's accumulator), `n` (an annotation's value), `a`
(a function's PyCore parameter, unused: arguments are bound by name from the signature), and `c`
(a comparison's middle operand, kept in the frame's own cell by `$set`/`$get`). Every fresh name
starts with a dot, which no Python identifier does; no tag holds a digit, so `fresh tag l`
determines `tag` and `l` (`fresh_inj'`). The translation depends on names only through mangling.

The main shapes (`⟦e⟧` is `trE C e`, `x̂` the mangled name, `g(e₁, …)` a call of the core constant
`g` on the argument record; fresh names are written without their label, and `.c_b` is the `.c` of
the operand `b`):

| Surf | ⌊·⌋ |
| --- | --- |
| `a op b` | `bin op ⟦a⟧ ⟦b⟧` |
| `a₁ and a₂ and …` | `bool true ⟦a₁⟧ (bool true ⟦a₂⟧ …)` |
| `a op₁ b op₂ c …` | `bool true (bin op₁ ⟦a⟧ ($set:.c_b(⟦b⟧))) (bin op₂ ($get:.c_b()) ⟦c⟧ …)` |
| `f(a, *b, k=v, **m)` | `$call(⟦f⟧, ⟦a⟧, ⟦b⟧, ⟦v⟧, ⟦m⟧, $pos, $star, $kw:k, $kwstar)` |
| `e.a`, `e[i]`, `op e` | `$op:getattr:â(⟦e⟧)`, `$op:getitem(⟦e⟧, ⟦i⟧)`, `$op:unop:op(⟦e⟧)` |
| `[es]`, `(es)`, `{es}` | `$display:list(…)`, `$display:tuple(…)`, `$display:set(…)`, values then markers |
| `{k: v, **m}` | `$op:display:dict:ST(⟦k⟧, ⟦v⟧, ⟦m⟧)` |
| `lambda ps: b` | `$def:0:NP(⟦defaults⟧…, dead annotations, markers…, lam .a (bindings; return ⟦b⟧))` |
| `[e for t in it if c]` | `(λ° .i. acc = []; loops; return acc)($op:iter(⟦it⟧))` |
| `t₁ = t₂ = e` | `blk [.t = ⟦e⟧; t₁ ← .t; t₂ ← .t]` |
| `(a, *b) = …` (target) | `blk [.u = $unpack(src, $pos, $star); a ← $item:0(.u); b ← $item:1(.u)]` |
| `t op= e` | `blk [read t into .o, .k, .g; .v = bin "op=" .g ⟦e⟧; write .v into t]` |
| `x: A = v` | `blk [.t = ⟦v⟧; x̂ = .t; .n = ⟦A⟧; $annot:x̂(.n)]` at module or class level; in a function the annotation is in a dead branch |
| `for t in it: b else: u` | `blk [.i = $op:iter(⟦it⟧); .g = $true; while .g: try: .v = $next(.i) except $stop as .s: .g = $false else: t ← .v; ⟦b⟧ else: ⟦u⟧]` |
| `@ds def f(ps) -> r: b` | `f̂ = $def:N:NP(⟦ds⟧…, ⟦defaults⟧…, ⟦annotations⟧…, markers…, lam .a (bindings; ⟦b⟧))` |
| `@ds class C(bs, ks): b` | `blk [$cls:N(⟦ds⟧…, ⟦bs⟧…, ⟦ks⟧…, markers…); class Ĉ q: $setup(…); ⟦b⟧]` |
| `try … except T as x … else` | `tryE` with the handlers `⟦T⟧ as x̂`; bare `except` is `$any`, no name `.e` |
| `raise e from c`, bare `raise` | `$raisefrom(⟦e⟧, ⟦c⟧)`, `$reraise()` |
| `import a.b as c`, `from m import x` | `ĉ = $op:import:a.b:1()`, `blk [.m = $op:import:m:1(); x̂ = $op:importFrom:x(.m)]` |
| `assert t, m` | `ite ⟦t⟧ [] [$raise:AssertionError(⟦m⟧)]` |

A function body starts with a dead binding of each parameter (`paramBind`), so the parameters stay
in the scope's own body; a class body and the module start with `$setup`.

## The footprint on Surf, and touching a node

**F_surf(p, q)** (`Surf/Footprint.lean`) is Definition 4 on Surf: part (1) `p1B`, the nodes of the
replaced subtrees; part (2) `part2`, the occurrences outside part (1) of a name classified
differently in `q` in their scope or in a scope around it (`alike`); part (3) `kindChanges`, which
makes the footprint all of `p` (`footprint? R p = none`). `inF R p l` is membership. Surf's
classification (`Surf.clsOf`) and occurrences (`Surf.itemsB`) are defined from the language
reference, not through the translation:

- occurrences are Name nodes (load, store, `del`), a walrus target at its NamedExpr node, a
  parameter at its `arg` node in the function's scope, a `def`'s or class's name at its statement
  in the scope around, an import's bound name at its `alias` node (`from m import *` binds nothing
  statically), the names of `global` and `nonlocal` at the statement, and a handler's name at the
  handler. A class node is also an occurrence of `__name__`, `__module__` and `__qualname__` in its
  body's scope. Keyword names and attribute names are no occurrences;
- names are mangled as `_Py_Mangle` does, with the innermost class around the occurrence;
- a comprehension is a function scope; its walrus targets are bound in the nearest enclosing scope
  that is no comprehension, and global in the comprehension if that scope is the module or declares
  them global, free otherwise;
- functions are `def`s, lambdas and comprehensions; a generator expression is a generator.

`SurfTests.lean` checks both classifications against CPython's symbol tables on the scoping rules
(walrus in a comprehension, nested and sibling comprehensions, mangling, a comprehension in a class
body, a global walrus target, kinds).

**The PyCore edit** `trEdit R p` replaces, for each Surf site, the PyCore nodes made for it, each by
its translation in `q`'s chain: an expression site's root, and its marker if it is an item, an
argument or a set item; a target's statements. A class's qualified name is part of PyCore's
`class` node, so the outermost `def` or class outside the sites whose qualified name changes
(`qualCh`, by adding or removing a `global` in the scope around) is a PyCore site too; its node is
an occurrence of its name classified differently, in part (2).

**The image.** `imgF R p x` holds of the PyCore nodes made for nodes of F_surf(p, q).
`footprint_theorem_surf` needs ⌊p⌋'s run to avoid `imgF R p`.

**Touching a node** (`Touch`, `Surf/T2Rel.lean`). A Surf configuration touches the node it focuses
(`Sem.focus`: the expression or statement it enters, or the handler clause whose class it
evaluates), and also, at the top frame (`TouchF`):

- an assignment target, and each element target of an unpacking (`tgtKids`), when the store
  starts: the unpacking reads the elements' markers then;
- an augmented assignment's target, and a bare annotated assignment's target (`x: T`), when the
  statement is entered;
- each `del` target when it is deleted;
- a `def`'s or lambda's parameters when its function object is made, after its decorators, defaults
  and annotations: `$def` reads the parameters' markers then;
- a keyword argument's node when its value is evaluated, a starred item's node when its operand
  is evaluated (`touchB`): their markers are those nodes';
- a set item's constness nodes (`constNodes`: the item and, through a sign or a tuple, its parts)
  when the item is evaluated in a set display: the item's constness marker reads them;
- a comprehension clause's node when its iterable is evaluated, at each `next` of its iterator, and
  when its loop starts after the clause before it;
- an import alias when its name is bound.

Each is a node whose PyCore code runs at that point although Surf.Sem's step enters no expression
or statement of it, and each is part of the code the top frame is running. So `NoReachT p I F c`
(no configuration of the run from `c` touches a node of `F`) asks a little more than that no step
focuses a node of `F`: it also excludes these nodes. The translation is laid out so that a node
made for a child is entered only once Surf's run touches the child, or just before it focuses a
node of the child's subtree with no operation between: markers come after all values in a gadget's
record, and a comparison chain's and a Boolean chain's nodes are the parent's own.

## The T2 simulation design

`Surf/T2Sim.lean` proves, for two deterministic machines, that a stuttering simulation with a
measure gives termination with corresponding final configurations and divergence, in both
directions (`sim_term_ab`, `sim_term_ba`, `sim_div_ab`, `sim_div_ba`), and the reach
correspondence (`sim_reach`). One simulation step (`SimStep`) from related `a ~ b` is one of: both
runs end in finitely many steps with corresponding outcomes (`Fin`); both make at least one step,
to related configurations; only `a`'s run steps and the measure `μ` decreases; only `b`'s run steps
and `μ` decreases. Every node `b`'s run evaluates on the way, `x`, has `x / 64` touched by `a`'s run
then or before (`Cover`). The relation carries the history `H`, the Surf nodes touched before, and
grows it as `a` steps (`Seen`).

`Surf.T2.step_sim (W : WF p) (H) (s) (t) (h : CRelI p H s t) : Goal I p H s t` is that step for
Surf.Sem and PyCore, with `μ` the lengths of the top frames' continuations. It goes by cases on
the top frame's control and on the family of its continuation's top item; each case is a lemma of
`T2Cases.lean` or of one file per group of constructs. The relation (`Surf/T2Rel.lean`):

- **Configurations** (`CRel`): frames related pairwise; objects at each address related (a Surf
  function object with a PyCore closure of the translated scope and the same signature and
  defaults, `ORel`; generators with suspended frames related, `GRel`); cells and the module
  dictionary equal on every name with no dot; PyCore's output list empty; the object counter, the
  result and the interpretation's state equal; every frame below the top waiting for its callee;
  `Ids`; `EnterInv`. `CRelI` adds the initial configurations (`InitRel`) and pending calls
  (`PendRel`).
- **Frames** (`FRel0`, `FRel`): the same id and kind; PyCore's chain the image of Surf's
  (`trChain`); both classifications cached as `clsOf` of the chain; closure environments equal on
  the names with no dot; a class namespace equal to PyCore's without its dotted names; the frame's
  scope node touched; PyCore's kind of each comprehension's function equal to the comprehension's
  (`KOk`); the control related by `CR` and the continuation by `KRel`.
- **Relation families.** `KRel x U i K K'` pairs each Surf continuation item with the PyCore items
  the translated code has pushed for it at that point. It is `nil` or one item of a family:
  `CoreK` (the constructs ⌊·⌋ maps to PyCore's own), `CallK`, `ClsK`, `CompK`, `LoopK`, `AsgK`,
  `AccK`, `MiscK`, one per file of cases, so each file's lemmas analyse only their own family. The
  index `i` says whether the top item awaits a value.
- **Fresh-name contents.** PyCore keeps in fresh names what Surf keeps in its continuation: a `for`
  loop's iterator and flag, an assignment's value while the targets' parts are evaluated, an
  augmented target's parts, a comprehension's accumulator, a comparison's middle operand. Items read
  them through `Cx.rd` (the frame's reading of a name) and `Cx.own` (its own cell).
- **Label budgets.** A fresh name `.tag l` is written only by code made for the node `l`. `KRel` is
  indexed by a label set `U`: every code piece that may run above the continuation has its labels
  in `U`, and an item that reads a fresh name of `l` sits below a level whose set excludes `l`
  (`Rm U l`). So the running code never changes what an item below reads (`KRel.ext`).
- **History.** An item whose PyCore code evaluates nodes made for a node touched earlier (a loop's
  nodes at each iteration, a comparison's middle operand read back, a target's source after its
  object, a class body, a comprehension's frame, a closure's parameters) records that node in `H`
  (`x.H l`), which is what `Cover` needs for those steps.
- **Pending calls** (`PendRel`): Surf is at a call `g(v)` (a loop's `next`, a comprehension's
  function on its iterator) while PyCore holds `v` with the call of `g` next on its continuation, or
  a `yield from` asks its suspended delegate generator. The two are related as the call.
- **Special frames** (`Special`): a suspended generator before its first resumption (a generator
  expression's loops not yet started, a generator function's or lambda's parameters' bindings not
  yet run) or inside a `yield from`, where PyCore has steps to make before the frames correspond;
  the resumption lemmas take them.
- **Ids** (`Ids`): PyCore's own cells (`$set`/`$get`) are addressed by frame id, so the ids of the
  frames on the stack are distinct and below the counter, a suspended generator's frame has the
  generator's address, which no frame on the stack has, and the module frame has id 0.
- **`EnterInv`**: every pending `enterK` (a `**` parameter's dictionary awaited before a function is
  entered), of a frame or of a suspended generator, names an allocated address that holds no
  comprehension's function object, which Surf and PyCore would enter differently.
- **Reach.** `pfocus` is PyCore's focus but for labels below 64 (the module's `SETUP_ANNOTATIONS`).
  `reach_corr` applies `sim_reach`: each node `sub l k` ⌊p⌋'s run evaluates has `l` touched by Surf's
  run; a node below 64 would need `l = 0`, which `WF.pos` rules out.

## Differential checks

**Surf.Sem against CPython 3.13** (`lean_sem/difftest.py`, results in `lean_sem/difftest.txt` and
`difftest.jsonl`). Each program is exported by `export_surf.py` and run on its problem's tests
(`problem.json` and `heldout.json`) as the harness `src/runner/_child.py` runs them: under CPython
3.13 with `PYTHONHASHSEED=0`, 2 s a test (and again with seed 1 to find seed-dependent tests), and
under `pycore run`, 20,000,000 steps a test. Per test, the returned value (`repr`, a set's elements
sorted), the printed output and the uncaught exception's class are compared. A test CPython does
not finish in 2 s is not run by Lean (in call mode, nor are the tests after it).

| programs | number | tests agree | differ | not covered |
| --- | ---: | ---: | ---: | ---: |
| buggy | 2,970 | 244,232 | 0 | 3,909 |
| `tempa_l` repairs | 2,216 | 182,686 | 0 | 31 |
| `tempa_lf` repairs | 2,477 | 198,445 | 0 | 31 |
| all | 7,663 | 625,363 | 0 | 3,971 |

7,609 programs agree on every test and 54 on every test they cover; none differs. Not covered:
3,545 tests CPython does not finish in 2 s, 111 over Lean's wall-clock limit, 105 after a call-mode
test that ran out of fuel, 14 out of fuel, 1 deeper than the recursion limit, and 195 that need what
`Ref` lacks (`io.BytesIO` 93, `fileinput.input` 31, `repr` of an object or a function 30, `repr` of
a method 19, `fractions.gcd` 22). 61 tests whose CPython output changes with the hash seed (sets of
tuples of strings, `refactory_q4`) agree with the seed-0 run.

**Surf.Sem against PyCore on ⌊p⌋** (`lean_sem/coretest.py`, results in `lean_sem/coretest.txt`).
Every test of the same 7,663 programs runs twice under `Ref.interp` with a trace (`pycore runcore`):
by Surf.Sem on `p` and by PyCore on ⌊p⌋, with eight times the fuel. The trace is a hash of every
operation the interpretation is asked for, with its values (function objects and generators by
address), and of every callback outcome; with the object counter at the end, equal traces mean the
same operations in the same order and the same allocations. Per test, the status, output, exception
class or returned value, trace and counter are compared. Tests CPython timed out on are skipped.
Results on the final build (`lean_sem/coretest.txt`): 7,663 programs; 625,349 tests agree,
0 differ, 507 not covered (the reference interpretation lacks a feature: 208; CPython timed out,
so the test is skipped: 174; after a call-mode test ran out of fuel: 105; out of fuel: 15;
wall-clock limit: 4; recursion depth: 1). 7,608 programs agree on every test and 55 on every
covered test.

**The classification check** (`lean_cls/surf_cls.py`, results in `lean_cls/surf_cls.txt` and
`surf_cls_fuzz.txt`). Each program is exported, `pycore surf` prints every occurrence's
classification as Surf's own analysis gives it and as PyCore's analysis of ⌊p⌋ gives it, and both
are compared with CPython 3.13's symbol tables (with the folding of list, set and dict
comprehensions undone) and with CPython 3.11's, which keep each comprehension as a scope.

| programs | number | occurrences | Surf agrees (3.13 / 3.11) | ⌊p⌋ agrees (3.13 / 3.11) |
| --- | ---: | ---: | ---: | ---: |
| buggy | 2,970 | 61,437 | 61,437 / 61,437 | 61,437 / 61,437 |
| repairs, all arms | 54,776 | 1,117,957 | 1,117,957 / 1,117,957 | 1,117,957 / 1,117,957 |
| random (`--fuzz 100000`) | 100,000 | 1,045,581 | 1,026,208 / 1,045,581 | 1,026,208 / 1,045,581 |

Surf and the translation never differ from each other, and Lean reports no occurrence the exporter
does not, besides the class nodes' implicit `__name__`, `__module__` and `__qualname__`, which
CPython's tables omit. The programs and repairs use no `global`, `nonlocal`, private name or walrus
in a comprehension, so the random programs exercise them: nested functions, lambdas, classes,
comprehensions with several generators and walrus targets, `global`, `nonlocal`, private names,
`del`, `for`, `except … as`, imports. Against 3.13 the check skips the 19,373 occurrences in
comprehensions in class bodies.

**In the build.** `Tests.lean`, `SurfTests.lean`, `SurfSemTests.lean` and `CoreTests.lean` are
default targets whose `#guard`s fail the build if a check fails (see Files). Their expected outputs
come from CPython 3.13 or, for symbol tables, CPython 3.11.

## CLI

`lake build` makes `.lake/build/bin/pycore`, which reads a file or standard input.

**`pycore [FILE]`**: one PyCore program or a program with an edit, as an s-expression. Atoms are
bare words or double-quoted strings (`\"`, `\\` escapes); `;` starts a comment; labels `L` are
natural numbers.

```text
program := (module stmt*)
block   := (stmt*)
stmt    := (assign L x e) | (del L x) | (expr L e) | (if L e block block)
         | (while L e block) | (while L e block block) | (return L e) | (def L f x block)
         | (class L x block) | (class L x Q block) | (global L x) | (nonlocal L x)
         | (try L block LH e x block) | (try L block (handler*) block)
         | (raise L e) | (print L e) | (break L) | (continue L)
handler := (handler LH e x block)
expr    := (const L c) | (name L x) | (name L x K) | (bin L op e e) | (call L e e)
         | (lambda L x block) | (complambda L x block) | (walrus L x e) | (yield L e)
         | (yieldfrom L e) | (ifexp L c e e) | (and L e e) | (or L e e)
pair    := (pair program (sites site*))
site    := (stmts L block)            ; replace the statement at L by the block
         | (before L block)           ; insert the block before the statement at L
         | (after L block)            ; insert it after the statement at L
         | (expr L e)                 ; replace the expression at L
         | (handler LH e x block)     ; replace the handler clause at LH
```

`(class L x block)` takes `x` as the qualified name. `(name L x K)` makes every failing lookup of
the read raise `K`. The output has one line per item, in source order:

```text
occ L x SCOPE CLS      ; x at node L, in the scope introduced at node SCOPE (or module); CLS local, free or global
fn L KIND              ; the function at node L; KIND plain or generator
```

For a pair, each `occ` and `fn` line gets a last column with `q`'s classification or kind, then
`part1 L*`, `part2 L*`, `part3 L*`, and `footprint L*` or `footprint ALL`.

**`pycore surf [FILE]`**: Surf programs as `export_surf.py` writes them, one constructor per `ast`
node (`(Module (Assign 3 ((Name 4 "r")) …))`, `()` for an absent part). For each program, between
`prog` and `end`: `socc L x SCOPE CLS` and `sfn L KIND` from Surf's analysis, `tocc` and `tfn` from
PyCore's analysis of ⌊p⌋ with labels mapped back (`l / 64`) and fresh names left out.

**`pycore run [FILE]`**: Surf programs on test inputs with `Ref.interp`, as the harness runs them,
one JSON line per test between `job` and `end`:

```text
job   := (job MODE FUEL (prelude PROG?) PROG (tests test*))
MODE  := stdio | call
test  := (stdin "text") | (call "entry" (val*)) | (skip)
val   := (int "n") | (float "bits") | (str "s") | (none) | (bool 0|1)
       | (list val*) | (tuple val*) | (set val*) | (dict (val val)*)
```

**`pycore runcore [FILE]`**: the same jobs, each test run by Surf.Sem and by PyCore on ⌊p⌋ under
the traced interpretation. Each line has Surf's status and `core`: `agree`, `mismatch` (with both
sides), or `nc` (Surf's run is not covered, or PyCore ran out of its fuel).

## How to reproduce

From this directory:

```text
lake build                      # libraries, pycore, and the #guard tests (Tests, SurfTests, SurfSemTests, CoreTests)
lake env lean Axioms.lean       # axioms of the PyCore and Surf theorems
lake env lean AxiomsT2.lean     # axioms of the T2 theorems
lake env lean CexTr.lean        # the locality and hypothesis edits (not a default target)
.lake/build/bin/pycore examples/witness2.sx
```

The differential scripts take the repository root `REPO` (they read `REPO/benchmark/` and the
stored repairs under `REPO/results/`) and write their results next to themselves. They run
`<this directory>/.lake/build/bin/pycore`; `PYCORE` names another binary:

```text
cd REPO
python3 -I results/checks/lean_sem/difftest.py REPO        # -> difftest.txt, difftest.jsonl
python3 -I results/checks/lean_sem/coretest.py REPO        # -> coretest.txt, coretest.jsonl
python3 -I results/checks/lean_cls/surf_cls.py REPO        # -> surf_cls.txt
python3 -I results/checks/lean_cls/surf_cls.py REPO --fuzz 100000   # -> surf_cls_fuzz.txt
```

`difftest.py` needs CPython 3.13 as `python3`; `surf_cls.py` also needs CPython 3.11 (`PYTHON311`,
default `python3.11`). `coretest.py` skips the tests CPython timed out on, from `difftest.py`'s
cache of CPython runs, or from its own run of a program `difftest.py` has not run;
`coretest.py --src FILE.py --stdin TEXT` runs one script.
