/-
Surf's classification of every occurrence, computed on Surf directly (`socc`) and
through the translation (`tocc`), on programs that exercise the scoping rules; each
expected line is CPython 3.11's symbol table (which keeps every comprehension as a
scope of its own), and each program runs the same under CPython 3.13.
`lake build SurfTests` fails if a check fails.
-/
import Surf.Cli
import Surf.Footprint

/-- Every line of `want`, for Surf and for the translation, is in the report on `src`. -/
def reports (src : String) (want : List String) : Bool :=
  match Surf.Cli.runAll src with
  | .ok out => want.all fun w => out.contains ("socc " ++ w) && out.contains ("tocc " ++ w)
  | .error _ => false

def kinds (src : String) (want : List String) : Bool :=
  match Surf.Cli.runAll src with
  | .ok out => want.all fun w => out.contains ("sfn " ++ w) && out.contains ("tfn " ++ w)
  | .error _ => false

-- A walrus target in a comprehension: free in it, local to the function around it.
--   def f(a):
--       r = [y := x for x in a]
--       return y
def walrus := "(Module (FunctionDef 1 \"f\" ((arg 2 \"a\" pos () ())) ((Assign 3 ((Name 4 \"r\")) (ListComp 5 (NamedExpr 6 \"y\" (Name 7 \"x\")) ((comprehension 8 (Name 9 \"x\") (Name 10 \"a\") ())))) (Return 11 (Name 12 \"y\"))) () ()))"
#guard reports walrus ["1 f module global", "2 a 1 local", "4 r 1 local", "6 y 5 free", "7 x 5 local", "9 x 5 local", "10 a 1 local", "12 y 1 local"]

-- A name the outer comprehension binds is free in the inner one; the inner one's first iterable is evaluated in the outer one.
--   def f(m, n):
--       return [[i for r in m] for i in n]
def nested := "(Module (FunctionDef 1 \"f\" ((arg 2 \"m\" pos () ()) (arg 3 \"n\" pos () ())) ((Return 4 (ListComp 5 (ListComp 6 (Name 7 \"i\") ((comprehension 8 (Name 9 \"r\") (Name 10 \"m\") ()))) ((comprehension 11 (Name 12 \"i\") (Name 13 \"n\") ()))))) () ()))"
#guard reports nested ["1 f module global", "2 m 1 local", "3 n 1 local", "7 i 6 free", "9 r 6 local", "10 m 5 free", "12 i 5 local", "13 n 1 local"]

-- A comprehension does not see the names a sibling comprehension binds (CPython 3.13's folded symbol table makes `a` local to the generator expression).
--   g = ([a for q in z] for x in [b for (b, a) in w])
def sibling := "(Module (Assign 1 ((Name 2 \"g\")) (GeneratorExp 3 (ListComp 4 (Name 5 \"a\") ((comprehension 6 (Name 7 \"q\") (Name 8 \"z\") ()))) ((comprehension 9 (Name 10 \"x\") (ListComp 11 (Name 12 \"b\") ((comprehension 13 (Tuple 14 ((Name 15 \"b\") (Name 16 \"a\"))) (Name 17 \"w\") ()))) ())))))"
#guard reports sibling ["2 g module global", "5 a 4 global", "7 q 4 local", "8 z 3 global", "10 x 3 local", "12 b 11 local", "15 b 11 local", "16 a 11 local", "17 w module global"]

-- A private parameter name is mangled in a class's method.
--   class C:
--       def m(self, __q):
--           return __q
def mangle := "(Module (ClassDef 1 \"C\" () () ((FunctionDef 2 \"m\" ((arg 3 \"self\" pos () ()) (arg 4 \"__q\" pos () ())) ((Return 5 (Name 6 \"__q\"))) () ())) ()))"
#guard reports mangle ["1 C module global", "2 m 1 local", "3 self 2 local", "4 _C__q 2 local", "6 _C__q 2 local"]

-- A comprehension in a class body skips the class scope.
--   class C:
--       y = 1
--       xs = [y for _ in z]
def classcomp := "(Module (ClassDef 1 \"C\" () () ((Assign 2 ((Name 3 \"y\")) (Constant 4 \"1\")) (Assign 5 ((Name 6 \"xs\")) (ListComp 7 (Name 8 \"y\") ((comprehension 9 (Name 10 \"_\") (Name 11 \"z\") ()))))) ()))"
#guard reports classcomp ["1 C module global", "3 y 1 local", "6 xs 1 local", "8 y 7 global", "10 _ 7 local", "11 z 1 global"]

-- A walrus target the function around declares global is global in the comprehension.
--   def f(a):
--       global y
--       return [y := 1 for _ in a]
def globalwalrus := "(Module (FunctionDef 1 \"f\" ((arg 2 \"a\" pos () ())) ((Global 3 (\"y\")) (Return 4 (ListComp 5 (NamedExpr 6 \"y\" (Constant 7 \"1\")) ((comprehension 8 (Name 9 \"_\") (Name 10 \"a\") ()))))) () ()))"
#guard reports globalwalrus ["1 f module global", "2 a 1 local", "3 y 1 global", "6 y 5 global", "9 _ 5 local", "10 a 1 local"]

-- A yield in a comprehension's first iterable makes the function around it a generator;
-- a generator expression is a generator, a list comprehension is not.
--   def f(a):
--       return [x for x in (yield a)]
--   g = (x for x in a)
def kindsSrc := "(Module (FunctionDef 1 \"f\" ((arg 2 \"a\" pos () ())) ((Return 3 (ListComp 4 (Name 5 \"x\") ((comprehension 6 (Name 7 \"x\") (Yield 8 (Name 9 \"a\")) ()))))) () ()) (Assign 10 ((Name 11 \"g\")) (GeneratorExp 12 (Name 13 \"x\") ((comprehension 14 (Name 15 \"x\") (Name 16 \"a\") ())))))"
#guard kinds kindsSrc ["1 generator", "4 plain", "12 generator"]

/-! The syntactic half of (T3), checked on edits: `commutes` is
`⌊editB R p⌋ = editB (trEdit R p) ⌊p⌋`, `imageOk` is "F(⌊p⌋, ⌊q⌋) lies in the image
of F_surf(p, q)". -/

def parse (src : String) : List Surf.Stmt :=
  match (do let (sx, _) ← PyCore.Cli.parseSx (← PyCore.Cli.tokenize src.toList); Surf.Cli.program sx) with
  | .ok p => p
  | .error _ => []

def check3 (src : String) (R : Surf.Edit) : Bool × Bool :=
  let p := parse src
  (Surf.commutes R p, Surf.imageOk R p)

-- c = False; a = [1]; print(c and 1), with `1` replaced by `[y for y in a]`: the comprehension's
-- function stays in place, under the `and`
def e1 := "(Module (Assign 1 ((Name 2 \"c\")) (Constant 3 \"False\")) (Assign 4 ((Name 5 \"a\")) (List 6 ((Constant 7 \"1\")))) (Expr 8 (Call 9 (Name 10 \"print\") ((BoolOp 11 And ((Name 12 \"c\") (Constant 13 \"1\")))) ())))"
#guard check3 e1 { e := fun l => if l = 13 then some (.comp 20 .list [.name 21 "y"]
  [.mk 22 (.name 23 "y") (.name 24 "a") []]) else none } == (true, true)

-- the list comprehension of `print(c and [y for y in a])` replaced by a generator expression
def e2 := "(Module (Assign 1 ((Name 2 \"c\")) (Constant 3 \"False\")) (Assign 4 ((Name 5 \"a\")) (List 6 ((Constant 7 \"1\")))) (Expr 8 (Call 9 (Name 10 \"print\") ((BoolOp 11 And ((Name 12 \"c\") (ListComp 13 (Name 14 \"y\") ((comprehension 15 (Name 16 \"y\") (Name 17 \"a\") ())))))) ())))"
#guard check3 e2 { e := fun l => if l = 13 then some (.comp 20 .gen [.name 21 "y"]
  [.mk 22 (.name 23 "y") (.name 24 "a") []]) else none } == (true, true)

-- def f(a): r = [x for x in a]; x = 1; return r, with `x = 1` replaced by `global x`:
-- part (2) holds the occurrences of x in f and in the comprehension
def e3 := "(Module (FunctionDef 1 \"f\" ((arg 2 \"a\" pos () ())) ((Assign 3 ((Name 4 \"r\")) (ListComp 5 (Name 6 \"x\") ((comprehension 7 (Name 8 \"x\") (Name 9 \"a\") ())))) (Assign 10 ((Name 11 \"x\")) (Constant 12 \"1\")) (Return 13 (Name 14 \"r\"))) () ()))"
#guard check3 e3 { s := fun l => if l = 10 then some [.glob 30 ["x"]] else none } == (true, true)

-- for i in range(3): if i: x = i else: pass, with the target `x` renamed and `pass` replaced
def e4 := "(Module (For 1 (Name 2 \"i\") (Call 3 (Name 4 \"range\") ((Constant 5 \"3\")) ()) ((If 6 (Name 7 \"i\") ((Assign 8 ((Name 9 \"x\")) (Name 10 \"i\"))) ((Pass 11)))) ()))"
#guard check3 e4 { e := fun l => if l = 9 then some (.name 30 "y") else none,
                   s := fun l => if l = 11 then some [.brk 31] else none } == (true, true)

-- an edit that adds a walrus target to a comprehension (the element `x` of
-- `[x for x in a]` replaced by `(y := x)`; F_surf is that element) commutes: a comprehension's
-- function binds its walrus targets in the scope around it, so its translation does not
-- depend on its body
#guard check3 e3 { e := fun l => if l = 6 then some (.walrus 30 "y" (.name 31 "x")) else none } ==
  (true, true)

-- the smaller footprint (site roots and flagged nodes) lies in the image on the same edits
#guard Surf.imageMinOk { e := fun l => if l = 13 then some (.comp 20 .list [.name 21 "y"]
  [.mk 22 (.name 23 "y") (.name 24 "a") []]) else none } (parse e1)
#guard Surf.imageMinOk { s := fun l => if l = 10 then some [.glob 30 ["x"]] else none } (parse e3)

-- def f(): pass; class C: pass, with `pass` replaced by `global C`: the class's qualified
-- name changes from `f.<locals>.C` to `C` outside the sites, so the class node is a PyCore
-- site (`qualCh`); it is in part (2), an occurrence of `C` classified differently. The
-- commutation holds, and the smaller footprint lies in the image; the full one does not
-- (part (1) of F(⌊p⌋, ⌊q⌋) holds the class body, whose Surf nodes are not in F_surf)
def qualP : List Surf.Stmt := [.defn 1 "f" [] [.pass 2, .cls 3 "C" [] [] [.pass 4] []] [] none]
def qualR : Surf.Edit := { s := fun l => if l = 2 then some [.glob 30 ["C"]] else none }
#guard (Surf.commutes qualR qualP, Surf.regB qualR [] qualP, Surf.imageMinOk qualR qualP,
  Surf.imageOk qualR qualP) == (true, true, true, false)
#guard Surf.footprint? qualR qualP == some [2, 3]

-- CPython 3.13's qualified names: `def f(): global g; def g(): class C: pass` gives
-- `g.<locals>.C`; `class G: global H; class H: class I: pass` gives `H.I`; a class in a
-- method, `A.m.<locals>.B`
def ngC : List Surf.Scope := [.fn 3 "g" [] [.cls 4 "C" [] [] [.pass 5] []],
  .fn 1 "f" [] [.glob 2 ["g"], .defn 3 "g" [] [.cls 4 "C" [] [] [.pass 5] []] [] none]]
#guard Surf.qualIn ngC "C" == "g.<locals>.C"
#guard Surf.qualIn [.cl 3 "H" [.cls 4 "I" [] [] [.pass 5] []],
  .cl 1 "G" [.glob 2 ["H"], .cls 3 "H" [] [] [.cls 4 "I" [] [] [.pass 5] []] []]] "I" == "H.I"
#guard Surf.qualIn [.fn 2 "m" [] [], .cl 1 "A" [.defn 2 "m" [] [] [] none]] "B" == "A.m.<locals>.B"
-- the same with `global g` added by the edit: `C`'s qualified name changes from
-- `f.<locals>.g.<locals>.C` to `g.<locals>.C` though `C`'s node is in no part of F_surf;
-- the PyCore site is the outermost `def` whose own qualified name changes, `g`, whose node
-- is in part (2)
def ngP : List Surf.Stmt := [.defn 1 "f" [] [.pass 2, .defn 3 "g" [] [.cls 4 "C" [] [] [.pass 5] []] [] none] [] none]
def ngR : Surf.Edit := { s := fun l => if l = 2 then some [.glob 30 ["g"]] else none }
#guard (Surf.commutes ngR ngP, Surf.regB ngR [] ngP, Surf.imageMinOk ngR ngP,
  Surf.footprint? ngR ngP) == (true, true, true, some [2, 3])
#guard (PyCore.rootsB (Surf.trEdit ngR ngP) (Surf.tr ngP)).map (· / 64) == [2, 3]

/-! The conditions of `Surf.tr_edit`, each necessary: without them the commutation fails. -/

-- a < b < c with b replaced by d: the chain's nodes are made after b's label, so the
-- replacement must keep it (`KeepsLabels`)
def cmpP : List Surf.Stmt := [.expr 1 (.compare 2 (.name 3 "a") ["<", "<"] [.name 4 "b", .name 5 "c"])]
#guard Surf.commutes { e := fun l => if l = 4 then some (.name 99 "d") else none } cmpP == false
#guard Surf.commutes { e := fun l => if l = 4 then some (.name 4 "d") else none } cmpP

-- a Boolean operation of one operand (which CPython's parser never makes) as a site: its
-- translation's root is the operand's, where `trEdit` puts the site
#guard Surf.commutes { e := fun l => if l = 2 then some (.name 99 "d") else none }
  [.expr 1 (.boolop 2 "And" [.name 3 "a"])]

-- def f(): x += 1, with the target x replaced by the tuple (a, b) (the parser rejects
-- `(a, b) += 1`): the commutation holds (the target's reading and storing statements are
-- replaced), but ⌊q⌋ reads `.g2` at the statement's own node `sub 2 3` and never binds it, so
-- that occurrence is classified differently, outside the image of F_surf = {3}; `regB`
-- requires an augmented target and its replacement to be names, attributes, or subscripts.
-- With `a.b` it is, and the smaller footprint lies in the image.
def augP : List Surf.Stmt := [.defn 1 "f" [] [.augassign 2 (.name 3 "x") "+" (.const 4 "1")] [] none]
def augR : Surf.Edit := { e := fun l => if l = 3 then some (.tuple 3 [.name 5 "a", .name 6 "b"]) else none }
#guard (Surf.commutes augR augP, Surf.regB augR [] augP, Surf.imageMinOk augR augP,
  PyCore.flagged (Surf.trEdit augR augP) (Surf.tr augP), Surf.footprint? augR augP) ==
  (true, false, false, [Surf.sub 2 3], some [3])
#guard (Surf.regB { e := fun l => if l = 3 then some (.attr 3 (.name 5 "a") "b") else none } [] augP,
  Surf.imageMinOk { e := fun l => if l = 3 then some (.attr 3 (.name 5 "a") "b") else none } augP) ==
  (true, true)

-- a replacement that reuses a label of `p` outside the sites: `def f(): pass; def g(): for x
-- in a: pass` with `pass` (2) replaced by `for y in b: pass` labelled 4, the label of `g`'s
-- loop. The fresh names `.g4`, `.v4`, `.s4` of `g`'s loop become local to `f` in ⌊q⌋, so
-- their occurrences in `g` are classified differently (flagged at `sub 4 k`, `sub 5 63`),
-- while F_surf = {2}: the smaller footprint is not in the image. Labels are positions, so a
-- replacement's nodes take labels `p` does not use; with label 11 the image holds.
def lblP : List Surf.Stmt := [.defn 1 "f" [] [.pass 2, .defn 3 "g" [] [.for 4 (.name 5 "x") (.name 6 "a")
  [.pass 7] []] [] none] [] none]
def lblR (l : Nat) : Surf.Edit := { s := fun l' => if l' = 2 then some [.for l (.name 8 "y") (.name 9 "b")
  [.pass 10] []] else none }
#guard (Surf.commutes (lblR 4) lblP, Surf.regB (lblR 4) [] lblP, Surf.imageMinOk (lblR 4) lblP,
  Surf.footprint? (lblR 4) lblP) == (true, true, false, some [2])
#guard (Surf.commutes (lblR 11) lblP, Surf.imageMinOk (lblR 11) lblP) == (true, true)
-- The labels of `q` are distinct with label 11 (the condition `footprint_theorem_surf` takes),
-- not with label 4.
#guard decide (Surf.labelsB (Surf.editB (lblR 11) lblP)).Nodup
#guard !decide (Surf.labelsB (Surf.editB (lblR 4) lblP)).Nodup

-- A replacement name that is no Python identifier (why `NoDot q` is a condition). `def g(): pass; def f(): x = 1`
-- with `pass` (2) replaced by `.t4 = 1` (labels 7–9, new): in ⌊q⌋, `g` binds `.t4`, the fresh
-- name of `f`'s assignment (4), so its occurrences in `f` are classified differently in the scope
-- around `f` (flagged at `sub 4 1`, `sub 5 63`), while F_surf = {2}. The labels of `q` are
-- distinct; `NoDot q` fails.
def dotP : List Surf.Stmt := [.defn 1 "g" [] [.pass 2, .defn 3 "f" [] [.assign 4 [.name 5 "x"]
  (.const 6 "1")] [] none] [] none]
def dotR : Surf.Edit := { s := fun l => if l = 2 then some [.assign 7 [.name 8 ".t4"] (.const 9 "1")] else none }
#guard (Surf.commutes dotR dotP, Surf.regB dotR [] dotP, Surf.imageMinOk dotR dotP,
  Surf.footprint? dotR dotP) == (true, true, false, some [2])
#guard decide (Surf.labelsB (Surf.editB dotR dotP)).Nodup
#guard ((PyCore.flagged (Surf.trEdit dotR dotP) (Surf.tr dotP)).map (· / 64)).all ([4, 5].contains ·)

-- `def f(): (a, b) += 1` (which the parser rejects) with the target (3) replaced by the name
-- `x`: ⌊p⌋ has no statement where ⌊q⌋ stores into `x` (after the statement's own `.v2 = …`),
-- so the commutation fails. `regB R [] p` checks the replaced target as well as its
-- replacement and fails, as does `regB {} [] p`; `regB {} [] q` holds.
def augP2 : List Surf.Stmt := [.defn 1 "f" [] [.augassign 2 (.tuple 3 [.name 5 "a", .name 6 "b"]) "+"
  (.const 4 "1")] [] none]
def augR2 : Surf.Edit := { e := fun l => if l = 3 then some (.name 3 "x") else none }
#guard (Surf.commutes augR2 augP2, Surf.regB augR2 [] augP2, Surf.regB {} [] (Surf.editB augR2 augP2),
  Surf.regB {} [] augP2, Surf.imageMinOk augR2 augP2, PyCore.flagged (Surf.trEdit augR2 augP2) (Surf.tr augP2),
  Surf.footprint? augR2 augP2) == (false, false, true, false, false, [Surf.sub 2 3], some [3, 5, 6])

/-! A sweep: three programs (a closure with a loop, a comparison chain, an augmented
assignment, a comprehension; a class with a `global`, a lambda; a handler, a class with
a generator expression, `while … else`, an annotated assignment; `def`s and classes nested
in `def`s and classes, whose qualified names change with a `global` around them), every
label, and 20 replacements of an expression or a statement. Whenever `regB` holds, the commutation
holds and the smaller footprint lies in the image of F_surf. -/
section
open Surf
def nm (l : Nat) (x : String) : Expr := .name l x
def sProgs : List (List Stmt) := [
  [.defn 1 "f" [.mk 2 "a" .pos none none]
    [.for 3 (nm 4 "x") (nm 5 "a")
      [.ite 6 (.compare 7 (nm 8 "x") ["<", "<"] [nm 9 "y", nm 10 "z"])
        [.augassign 11 (nm 12 "x") "+" (.const 13 "1")] [.pass 14]] [],
     .ret 15 (some (.comp 16 .list [nm 17 "x"] [.mk 18 (nm 19 "x") (nm 20 "a") [nm 21 "x"]]))] [] none,
   .cls 22 "C" [] [] [.defn 23 "g" [.mk 24 "self" .pos none none] [.glob 25 ["y"], .ret 26 (some (nm 27 "y"))] [] none,
     .assign 28 [nm 29 "k"] (.lam 30 [.mk 31 "u" .pos none none] (.boolop 32 "And" [nm 33 "u", nm 34 "k"]))] []],
  [.defn 1 "h" [] [.tryE 2 [.expr 3 (.call 4 (nm 5 "g") [] [])]
      [.mk 6 (some (nm 7 "E")) (some "e") [.augassign 8 (.attr 9 (nm 10 "o") "f") "+" (nm 11 "e")]] [.pass 12],
    .cls 13 "D" [nm 14 "B"] [] [.assign 15 [nm 16 "v"] (.comp 17 .gen [nm 18 "w"] [.mk 19 (nm 20 "w") (nm 21 "v") []])] [],
    .while 22 (nm 23 "D") [.brk 24] [.annassign 25 (nm 26 "t") (nm 27 "int") (some (.const 28 "0"))]] [] none],
  [.defn 1 "f" [] [.pass 2, .defn 3 "g" [] [.cls 4 "C" [] [] [.defn 5 "m" [] [.cls 6 "E" [] [] [.pass 7] []] [] none] []] [] none,
    .cls 8 "K" [] [] [.pass 9, .cls 10 "L" [] [] [.pass 11] []] []] [] none]
]
def sEReps (l : Nat) : List Expr := [nm l "q", .const l "2", .attr l (nm 1001 "q") "r", .sub l (nm 1001 "q") (nm 1002 "i"),
  .walrus l "q" (nm 1001 "r"), .yield l none, .comp l .list [nm 1001 "q"] [.mk 1002 (nm 1003 "q") (nm 1004 "y") []],
  .lam l [] (nm 1001 "x"), .tuple l [nm 1001 "a", nm 1002 "b"]]
def sSReps : List (List Stmt) := [[.pass 1001], [.glob 1001 ["x"]], [.glob 1001 ["C"]], [.glob 1001 ["D"]],
  [.assign 1001 [nm 1002 "y"] (.const 1003 "1")], [.expr 1001 (.yield 1002 none)], [.nonloc 1001 ["x"]],
  [.for 1001 (nm 1002 "x") (nm 1003 "z") [.pass 1004] []], [.cls 1001 "x" [] [] [.pass 1002] []],
  [.glob 1001 ["g"]], [.glob 1001 ["L"]]]
def imageBad : List (Nat × Nat × Nat) := Id.run do
  let mut out := []
  let mut pi := 0
  for p in sProgs do
    for l in labelsB p do
      let mut ri := 0
      for e' in sEReps l do
        let R : Edit := { e := fun l' => if l' = l then some e' else none }
        if regB R [] p && !(commutes R p && imageMinOk R p) then out := (pi, l, ri) :: out
        ri := ri + 1
      for ss in sSReps do
        let R : Edit := { s := fun l' => if l' = l then some ss else none }
        if regB R [] p && !(commutes R p && imageMinOk R p) then out := (pi, l, 100 + ri) :: out
        ri := ri + 1
    pi := pi + 1
  return out
#guard imageBad == []

/-- `FreshCanon`, checked: along the chain of each occurrence of a fresh name, its facts follow
`patB`. -/
def fcB (P : List PyCore.Stmt) : Bool := (PyCore.itemsB R0 [] P).all fun
  | .occ L x C' => !x.startsWith "." ||
      C'.map (xf x) == patB C'
  | .fn .. => true
/-- The invariant holds of ⌊p⌋ for the three programs, and of ⌊q⌋ for each edit of the sweep
under which `q`'s labels are distinct and its augmented targets are names, attributes, or
subscripts (`regB {} [] q`; with `(a, b) += 1`, `.g` is read and never bound). -/
def freshBad : List (Nat × Nat × Nat) := Id.run do
  let mut out := []
  let mut pi := 0
  for p in sProgs do
    if !(regB {} [] p && fcB (tr p)) then out := (pi, 0, 0) :: out
    for l in labelsB p do
      let mut ri := 0
      for e' in sEReps l do
        let q := editB { e := fun l' => if l' = l then some e' else none } p
        if (labelsB q).Nodup && regB {} [] q && !fcB (tr q) then out := (pi, l, ri) :: out
        ri := ri + 1
      for ss in sSReps do
        let q := editB { s := fun l' => if l' = l then some ss else none } p
        if (labelsB q).Nodup && regB {} [] q && !fcB (tr q) then out := (pi, l, 100 + ri) :: out
        ri := ri + 1
    pi := pi + 1
  return out
#guard freshBad == []
-- ⌊p⌋ reads `.g2` and never binds it (`regB {} [] p` fails); ⌊q⌋ keeps the pattern.
#guard (fcB (tr augP2), fcB (tr (editB augR2 augP2))) == (false, true)
end
