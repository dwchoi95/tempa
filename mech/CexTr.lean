/-
Edits that test the translation's locality and the conditions of the theorems on Surf
(`lake env lean CexTr.lean`, not a default target). Each `#guard` checks, on one program and
edit, the hypotheses, the commutation, the image of the footprint, or the runs of ⌊p⌋ and ⌊q⌋
(and of Surf.Sem). (5) is why `tr_edit` needs `0 ∉ labelsB p`. Outputs of the Python programs
are CPython 3.13's.
-/
import Surf.Footprint
import Surf.RunCore
open Surf Surf.RunCore

def runP (p : List Stmt) : String :=
  let (cp, sp) := driveP (PyCore.init (tr p) (fun y => mainGlob[y]?) (({ inp := [] }, 0) : TSt)) 800000
  sideJson (pSide cp sp)
def runS (p : List Stmt) : String :=
  let (cs, ss) := driveS (Surf.Sem.init p mainGlob (({ inp := [] }, 0) : TSt)) 100000
  sideJson (sSide cs ss)
def focuses (c : PC) : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc =>
    let acc := match PyCore.focus c with | some l => l :: acc | none => acc
    match PyCore.step tInterp c with
    | some c' => focuses c' n acc
    | none => acc
/-- ⌊p⌋'s run evaluates a node made for a node of F_surf(p, q). -/
def reaches (R : Edit) (p : List Stmt) : Bool :=
  let L := (footprint? R p).getD (labelsB p)
  (focuses (PyCore.init (tr p) (fun y => mainGlob[y]?) (({ inp := [] }, 0) : TSt)) 100000 []).any
    fun l => L.contains (l / 64)
def hyps (R : Edit) (p : List Stmt) : Bool :=
  decide (labelsB p).Nodup && decide (labelsB (editB R p)).Nodup && regB R [] p && regB {} [] p &&
    regB {} [] (editB R p)

/-! (1) An annotated assignment in a function: the annotation is kept in a branch that never
runs, so the symbol table sees its walrus target and its `yield`.
    y = 7
    def f():
        x: (y := 0) = 1
        if False:
            pass              # q: y = 2
        return y
    print(f())
CPython: UnboundLocalError for p and q; so do ⌊p⌋ and ⌊q⌋. `y` is local in ⌊p⌋'s `f`, and
`def g(): x: (yield) = 1` is a generator in ⌊·⌋. -/
def ann1 (s : Stmt) : List Stmt :=
  [.assign 1 [.name 2 "y"] (.const 3 "7"),
   .defn 4 "f" [] [.annassign 5 (.name 6 "x") (.walrus 7 "y" (.const 8 "0")) (some (.const 9 "1")),
     .ite 10 (.const 11 "False") [s] [], .ret 13 (some (.name 14 "y"))] [] none,
   .expr 15 (.call 16 (.name 17 "print") [.call 18 (.name 19 "f") [] []] [])]
def annP := ann1 (.pass 12)
def annR : Edit := { s := fun l => if l = 12 then some [.assign 20 [.name 21 "y"] (.const 22 "2")] else none }
def annS : Scope := .fn 4 "f" [] [.annassign 5 (.name 6 "x") (.walrus 7 "y" (.const 8 "0")) (some (.const 9 "1"))]
#guard (clsOf [annS] "y", PyCore.clsOf (trChain [annS]) "y") == (.loc, .loc)
def genS : Scope := .fn 1 "g" [] [.annassign 2 (.name 3 "x") (.yield 4 none) (some (.const 5 "1"))]
#guard (genS.kind [], (trScope [] genS).kind) == (.gen, .gen)
#guard hyps annR annP && footprint? annR annP == some [12] && !reaches annR annP
#guard runP annP == runP (editB annR annP)
#guard runP annP == "{\"st\": \"exc\", \"out\": \"\", \"exc\": \"UnboundLocalError\", \"trace\": \"5325179711203323034\", \"next\": 3}"
#guard runS annP == runS (editB annR annP)
#guard (commutes annR annP, rootsOk annR annP, imageMinOk annR annP) == (true, true, true)

/-! (2) An annotated assignment without a value at module level, its target `x` replaced by
`o.a`: the key store `__annotations__['x'] = …` is a node made for the target (`sub 2 58`),
so ⌊p⌋'s run reaches the image of F_surf = {2} and the footprint theorem's premise fails.
    x: int                    # q: o.a: int
    print(__annotations__)
CPython: p prints {'x': <class 'int'>}, q raises NameError; so do ⌊p⌋ and ⌊q⌋. Every target
form leaves one node made for it at each position (`annBare`, `annT`, `annBind`), so the
commutation holds with its sites in the image, for `o.a` as for `y`. -/
def annMod (t : Expr) : List Stmt :=
  [.annassign 1 t (.name 3 "int") none, .expr 4 (.call 5 (.name 6 "print") [.name 7 "__annotations__"] [])]
def amR : Edit := { e := fun l => if l = 2 then some (.attr 2 (.name 8 "o") "a") else none }
#guard hyps amR (annMod (.name 2 "x")) && footprint? amR (annMod (.name 2 "x")) == some [2] &&
  reaches amR (annMod (.name 2 "x"))
#guard runP (annMod (.name 2 "x")) != runP (editB amR (annMod (.name 2 "x")))
#guard commutes amR (annMod (.name 2 "x")) && rootsOk amR (annMod (.name 2 "x")) &&
  imageMinOk amR (annMod (.name 2 "x"))
#guard commutes { e := fun l => if l = 2 then some (.name 2 "y") else none } (annMod (.name 2 "x")) &&
  rootsOk { e := fun l => if l = 2 then some (.name 2 "y") else none } (annMod (.name 2 "x"))

/-! (3) An unpacking target whose element becomes starred: the shape is read from the
elements' markers (`sub 4 57`), made for the element.
    a, b = [1, 2, 3]          # q: a, *b = [1, 2, 3]
    print(a)
CPython: p raises ValueError, q prints 1; ⌊p⌋'s run reaches the image of F_surf = {4} (the
marker), the commutation holds, and the smaller footprint lies in the image. -/
def unp (b : Expr) : List Stmt :=
  [.assign 1 [.tuple 2 [.name 3 "a", b]] (.list 6 [.const 7 "1", .const 8 "2", .const 9 "3"]),
   .expr 10 (.call 11 (.name 12 "print") [.name 13 "a"] [])]
def unR : Edit := { e := fun l => if l = 4 then some (.star 4 (.name 5 "b")) else none }
#guard hyps unR (unp (.name 4 "b")) && footprint? unR (unp (.name 4 "b")) == some [4] &&
  reaches unR (unp (.name 4 "b"))
#guard runP (unp (.name 4 "b")) != runP (editB unR (unp (.name 4 "b")))
#guard commutes unR (unp (.name 4 "b")) && imageMinOk unR (unp (.name 4 "b"))

/-! (4) A display's, a call's and a set's items: whether each is starred, and a set item's
constness, are the item's own markers (`sub l 57`), so replacing one item changes only nodes
made for it: the commutation holds and the smaller footprint lies in the image.
    s = {1, 2, 3}             # q: s = {1, 2, x}
    f(*a)                     # q: f(b)
    [*a]                      # q: [b] -/
def setP (e : Expr) : List Stmt := [.assign 1 [.name 2 "s"] (.set 3 [.const 4 "1", .const 6 "2", e])]
def setR : Edit := { e := fun l => if l = 5 then some (.name 5 "x") else none }
#guard commutes setR (setP (.const 5 "3")) && imageMinOk setR (setP (.const 5 "3"))
def callP : List Stmt := [.expr 1 (.call 2 (.name 5 "f") [.star 3 (.name 4 "a")] [])]
def listP : List Stmt := [.expr 1 (.list 2 [.star 3 (.name 4 "a")])]
def bR : Edit := { e := fun l => if l = 3 then some (.name 3 "b") else none }
#guard commutes bR callP && imageMinOk bR callP && commutes bR listP && imageMinOk bR listP

/-! (5) Label 0: the module's setup is labelled `sub 0 4..6`, and a replaced augmented
attribute target's reading statements are PyCore sites at `sub lt 4`, `sub lt 5`, so with
`lt = 0` the setup is replaced too; `tr_edit` takes `0 ∉ labelsB p` (the exporter labels nodes
from 1). With `lt = 9` the commutation holds. -/
def aug0 (lt : Nat) : List Stmt := [.augassign 1 (.attr lt (.name 2 "o") "a") "+" (.const 3 "1")]
def aug0R (lt : Nat) : Edit := { e := fun l => if l = lt then some (.attr lt (.name 4 "p") "b") else none }
#guard (commutes (aug0R 0) (aug0 0), commutes (aug0R 9) (aug0 9)) == (false, true)

/-! (6) A tuple in a set: an element's star marker in the tuple's display is `sub 4 57`, its
constness marker in the set's marker of the tuple `sub 4 50`, so replacing `x` by `1` changes
the second only, at a node made for x (F_surf = {4}).
    {(x, 2)}                  # q: {(1, 2)} -/
def tsP : List Stmt := [.expr 1 (.set 2 [.tuple 3 [.name 4 "x", .const 5 "2"]])]
def tsR : Edit := { e := fun l => if l = 4 then some (.const 4 "1") else none }
#guard hyps tsR tsP && footprint? tsR tsP == some [4]
#guard commutes tsR tsP && rootsOk tsR tsP && imageMinOk tsR tsP
#guard PyCore.rootsB (trEdit tsR tsP) (tr tsP) == [sub 4 0, sub 4 57, sub 4 50]

/-! (7) An annotated attribute target at module level replaced by a name: `annT` leaves a node
made for any target (`sub 2 58`, a statement that does nothing for an attribute), which
becomes the key store `__annotations__['x']` (F_surf = {2, 3}).
    a.b: int = 5              # q: x: int = 5 -/
def anP : List Stmt := [.annassign 1 (.attr 2 (.name 3 "a") "b") (.name 4 "int") (some (.const 5 "5"))]
def anR : Edit := { e := fun l => if l = 2 then some (.name 2 "x") else none }
#guard hyps anR anP && footprint? anR anP == some [2, 3]
#guard commutes anR anP && rootsOk anR anP && imageMinOk anR anP
#guard PyCore.rootsB (trEdit anR anP) (tr anP) == [sub 2 0, sub 2 58]
