/-
The syntactic half of (T3), executable: edits of Surf programs, the footprint
F_surf(p, q) of Definition 4 on Surf, and the PyCore edit `trEdit R p` that the
translation of an edit is (each Surf site becomes the PyCore sites at the nodes made for
it, translated in `q`'s chain: the root of its translation, its marker in its parent's
gadget, or the statements of a target). `commutes` checks
`tr (editB R p) = PyCore.editB (trEdit R p) (tr p)` and `imageOk` checks that
F(⌊p⌋, ⌊q⌋) lies in the image of F_surf(p, q) under the label map `l ↦ sub l k`;
`SurfTests.lean` runs both, and `imageMinOk` for the smaller footprint of
`footprint_theorem_min`. `Commute.lean` proves the commutation (`tr_edit`); `Image.lean` proves
that the site roots lie in the image (`roots_image`), and `Fresh.lean` with `Canon.lean` that the
flagged items do (`flagged_image_canon`, `fresh_canon`).
-/
import Surf.Translate

namespace Surf
open PyCore (Name Label)

deriving instance BEq for PyCore.Expr, PyCore.Stmt, PyCore.Handler

/-- An edit of a Surf program: subtrees replaced at sites (expressions, statements
by blocks, handler clauses), as PyCore's `Edit`. -/
structure Edit where
  e : Label → Option Expr := fun _ => none
  s : Label → Option (List Stmt) := fun _ => none
  h : Label → Option Handler := fun _ => none

section
variable (R : Edit)

mutual
def editE : Expr → Expr
  | .const l c => (R.e l).getD (.const l c)
  | .name l x => (R.e l).getD (.name l x)
  | .bin l op a b => (R.e l).getD (.bin l op (editE a) (editE b))
  | .unary l op a => (R.e l).getD (.unary l op (editE a))
  | .boolop l op es => (R.e l).getD (.boolop l op (editEs es))
  | .compare l a ops es => (R.e l).getD (.compare l (editE a) ops (editEs es))
  | .ifexp l c a b => (R.e l).getD (.ifexp l (editE c) (editE a) (editE b))
  | .call l f as ks => (R.e l).getD (.call l (editE f) (editEs as) (editKs ks))
  | .attr l e a => (R.e l).getD (.attr l (editE e) a)
  | .sub l e i => (R.e l).getD (.sub l (editE e) (editE i))
  | .slice l a b c => (R.e l).getD (.slice l (editO a) (editO b) (editO c))
  | .star l e => (R.e l).getD (.star l (editE e))
  | .list l es => (R.e l).getD (.list l (editEs es))
  | .tuple l es => (R.e l).getD (.tuple l (editEs es))
  | .set l es => (R.e l).getD (.set l (editEs es))
  | .dict l kvs => (R.e l).getD (.dict l (editDs kvs))
  | .lam l ps b => (R.e l).getD (.lam l (editPs ps) (editE b))
  | .comp l k es gs => (R.e l).getD (.comp l k (editEs es) (editGs gs))
  | .walrus l x e => (R.e l).getD (.walrus l x (editE e))
  | .yield l e => (R.e l).getD (.yield l (editO e))
  | .yieldFrom l e => (R.e l).getD (.yieldFrom l (editE e))
  | .fstr l es => (R.e l).getD (.fstr l (editEs es))
  | .fmt l e c s => (R.e l).getD (.fmt l (editE e) c (editO s))
def editO : Option Expr → Option Expr
  | none => none
  | some e => some (editE e)
def editEs : List Expr → List Expr
  | [] => []
  | e :: es => editE e :: editEs es
def editKs : List Kw → List Kw
  | [] => []
  | .mk l x e :: ks => .mk l x (editE e) :: editKs ks
def editDs : List DItem → List DItem
  | [] => []
  | .mk k v :: kvs => .mk (editO k) (editE v) :: editDs kvs
def editPs : List Param → List Param
  | [] => []
  | .mk l x k d a :: ps => .mk l x k (editO d) (editO a) :: editPs ps
def editGs : List Gen → List Gen
  | [] => []
  | .mk l t i ifs :: gs => .mk l (editE t) (editE i) (editEs ifs) :: editGs gs
end

mutual
def editS : Stmt → List Stmt
  | .expr l e => (R.s l).getD [.expr l (editE R e)]
  | .assign l ts e => (R.s l).getD [.assign l (editEs R ts) (editE R e)]
  | .augassign l t op e => (R.s l).getD [.augassign l (editE R t) op (editE R e)]
  | .annassign l t a v => (R.s l).getD [.annassign l (editE R t) (editE R a) (editO R v)]
  | .del l ts => (R.s l).getD [.del l (editEs R ts)]
  | .ite l c t u => (R.s l).getD [.ite l (editE R c) (editB t) (editB u)]
  | .while l c b u => (R.s l).getD [.while l (editE R c) (editB b) (editB u)]
  | .for l t it b u => (R.s l).getD [.for l (editE R t) (editE R it) (editB b) (editB u)]
  | .brk l => (R.s l).getD [.brk l]
  | .cont l => (R.s l).getD [.cont l]
  | .pass l => (R.s l).getD [.pass l]
  | .ret l e => (R.s l).getD [.ret l (editO R e)]
  | .defn l f ps b ds r =>
    (R.s l).getD [.defn l f (editPs R ps) (editB b) (editEs R ds) (editO R r)]
  | .cls l x bs ks b ds =>
    (R.s l).getD [.cls l x (editEs R bs) (editKs R ks) (editB b) (editEs R ds)]
  | .glob l xs => (R.s l).getD [.glob l xs]
  | .nonloc l xs => (R.s l).getD [.nonloc l xs]
  | .tryE l b hs u => (R.s l).getD [.tryE l (editB b) (editHs hs) (editB u)]
  | .raise l e c => (R.s l).getD [.raise l (editO R e) (editO R c)]
  | .imp l al => (R.s l).getD [.imp l al]
  | .impFrom l m al lv => (R.s l).getD [.impFrom l m al lv]
  | .assert l t m => (R.s l).getD [.assert l (editE R t) (editO R m)]
def editHs : List Handler → List Handler
  | [] => []
  | .mk l ty x b :: hs => (R.h l).getD (.mk l (editO R ty) x (editB b)) :: editHs hs
def editB : List Stmt → List Stmt
  | [] => []
  | s :: ss => editS s ++ editB ss
end

/-- The scope of `q` that corresponds to a scope of `p` outside the sites. -/
def editSc : Scope → Scope
  | .fn l f ps b => .fn l f (editPs R ps) (editB R b)
  | .lam l ps b => .lam l (editPs R ps) (editE R b)
  | .cl l x b => .cl l x (editB R b)
  | .comp l k es gs => .comp l k (editEs R es) (editGs R gs)

def editChain (C : List Scope) : List Scope := C.map (editSc R)

end

/-! ## Labels and part (1) -/

mutual
def labelsE : Expr → List Label
  | .const l _ | .name l _ => [l]
  | .bin l _ a b | .sub l a b => l :: labelsE a ++ labelsE b
  | .unary l _ a | .attr l a _ | .star l a | .walrus l _ a | .yieldFrom l a => l :: labelsE a
  | .boolop l _ es | .list l es | .tuple l es | .set l es | .fstr l es => l :: labelsEs es
  | .compare l a _ es => l :: labelsE a ++ labelsEs es
  | .ifexp l c a b => l :: labelsE c ++ labelsE a ++ labelsE b
  | .call l f as ks => l :: labelsE f ++ labelsEs as ++ labelsKs ks
  | .slice l a b c => l :: labelsO a ++ labelsO b ++ labelsO c
  | .dict l kvs => l :: labelsDs kvs
  | .lam l ps b => l :: labelsPs ps ++ labelsE b
  | .comp l _ es gs => l :: labelsEs es ++ labelsGs gs
  | .yield l e => l :: labelsO e
  | .fmt l e _ s => l :: labelsE e ++ labelsO s
def labelsO : Option Expr → List Label
  | none => []
  | some e => labelsE e
def labelsEs : List Expr → List Label
  | [] => []
  | e :: es => labelsE e ++ labelsEs es
def labelsKs : List Kw → List Label
  | [] => []
  | .mk l _ e :: ks => l :: labelsE e ++ labelsKs ks
def labelsDs : List DItem → List Label
  | [] => []
  | .mk k v :: kvs => labelsO k ++ labelsE v ++ labelsDs kvs
def labelsPs : List Param → List Label
  | [] => []
  | .mk l _ _ d a :: ps => l :: labelsO d ++ labelsO a ++ labelsPs ps
def labelsGs : List Gen → List Label
  | [] => []
  | .mk l t i ifs :: gs => l :: labelsE t ++ labelsE i ++ labelsEs ifs ++ labelsGs gs
end

mutual
def labelsS : Stmt → List Label
  | .expr l e => l :: labelsE e
  | .assign l ts e => l :: labelsEs ts ++ labelsE e
  | .augassign l t _ e => l :: labelsE t ++ labelsE e
  | .annassign l t a v => l :: labelsE t ++ labelsE a ++ labelsO v
  | .del l ts => l :: labelsEs ts
  | .ite l c t u | .while l c t u => l :: labelsE c ++ labelsB t ++ labelsB u
  | .for l t it b u => l :: labelsE t ++ labelsE it ++ labelsB b ++ labelsB u
  | .brk l | .cont l | .pass l | .glob l _ | .nonloc l _ => [l]
  | .ret l e => l :: labelsO e
  | .defn l _ ps b ds r => l :: labelsPs ps ++ labelsB b ++ labelsEs ds ++ labelsO r
  | .cls l _ bs ks b ds => l :: labelsEs bs ++ labelsKs ks ++ labelsB b ++ labelsEs ds
  | .tryE l b hs u => l :: labelsB b ++ labelsHs hs ++ labelsB u
  | .raise l e c => l :: labelsO e ++ labelsO c
  | .imp l al | .impFrom l _ al _ => l :: al.map (·.l)
  | .assert l t m => l :: labelsE t ++ labelsO m
def labelsHs : List Handler → List Label
  | [] => []
  | .mk l ty _ b :: hs => l :: labelsO ty ++ labelsB b ++ labelsHs hs
def labelsB : List Stmt → List Label
  | [] => []
  | s :: ss => labelsS s ++ labelsB ss
end

section
variable (R : Edit)

mutual
/-- Part (1): the nodes of the replaced subtrees. -/
def p1E : Expr → List Label
  | e@(.const l _) | e@(.name l _) => if (R.e l).isSome then labelsE e else []
  | e@(.bin l _ a b) | e@(.sub l a b) => if (R.e l).isSome then labelsE e else p1E a ++ p1E b
  | e@(.unary l _ a) | e@(.attr l a _) | e@(.star l a) | e@(.walrus l _ a) | e@(.yieldFrom l a) =>
    if (R.e l).isSome then labelsE e else p1E a
  | e@(.boolop l _ es) | e@(.list l es) | e@(.tuple l es) | e@(.set l es) | e@(.fstr l es) =>
    if (R.e l).isSome then labelsE e else p1Es es
  | e@(.compare l a _ es) => if (R.e l).isSome then labelsE e else p1E a ++ p1Es es
  | e@(.ifexp l c a b) => if (R.e l).isSome then labelsE e else p1E c ++ p1E a ++ p1E b
  | e@(.call l f as ks) => if (R.e l).isSome then labelsE e else p1E f ++ p1Es as ++ p1Ks ks
  | e@(.slice l a b c) => if (R.e l).isSome then labelsE e else p1O a ++ p1O b ++ p1O c
  | e@(.dict l kvs) => if (R.e l).isSome then labelsE e else p1Ds kvs
  | e@(.lam l ps b) => if (R.e l).isSome then labelsE e else p1Ps ps ++ p1E b
  | e@(.comp l _ es gs) => if (R.e l).isSome then labelsE e else p1Es es ++ p1Gs gs
  | e@(.yield l a) => if (R.e l).isSome then labelsE e else p1O a
  | e@(.fmt l a _ s) => if (R.e l).isSome then labelsE e else p1E a ++ p1O s
def p1O : Option Expr → List Label
  | none => []
  | some e => p1E e
def p1Es : List Expr → List Label
  | [] => []
  | e :: es => p1E e ++ p1Es es
def p1Ks : List Kw → List Label
  | [] => []
  | .mk _ _ e :: ks => p1E e ++ p1Ks ks
def p1Ds : List DItem → List Label
  | [] => []
  | .mk k v :: kvs => p1O k ++ p1E v ++ p1Ds kvs
def p1Ps : List Param → List Label
  | [] => []
  | .mk _ _ _ d a :: ps => p1O d ++ p1O a ++ p1Ps ps
def p1Gs : List Gen → List Label
  | [] => []
  | .mk _ t i ifs :: gs => p1E t ++ p1E i ++ p1Es ifs ++ p1Gs gs
end

/-- A statement's part (1): all of it if it is a site, else `rest`. -/
def p1Site (s : Stmt) (rest : List Label) : List Label := if (R.s s.label).isSome then labelsS s else rest

mutual
def p1S : Stmt → List Label
  | s@(.expr _ e) => p1Site R s (p1E R e)
  | s@(.assign _ ts e) => p1Site R s (p1Es R ts ++ p1E R e)
  | s@(.augassign _ t _ e) => p1Site R s (p1E R t ++ p1E R e)
  | s@(.annassign _ t a v) => p1Site R s (p1E R t ++ p1E R a ++ p1O R v)
  | s@(.del _ ts) => p1Site R s (p1Es R ts)
  | s@(.ite _ c t u) | s@(.while _ c t u) => p1Site R s (p1E R c ++ p1B t ++ p1B u)
  | s@(.for _ t it b u) => p1Site R s (p1E R t ++ p1E R it ++ p1B b ++ p1B u)
  | s@(.ret _ e) => p1Site R s (p1O R e)
  | s@(.defn _ _ ps b ds r) => p1Site R s (p1Ps R ps ++ p1B b ++ p1Es R ds ++ p1O R r)
  | s@(.cls _ _ bs ks b ds) => p1Site R s (p1Es R bs ++ p1Ks R ks ++ p1B b ++ p1Es R ds)
  | s@(.tryE _ b hs u) => p1Site R s (p1B b ++ p1Hs hs ++ p1B u)
  | s@(.raise _ e c) => p1Site R s (p1O R e ++ p1O R c)
  | s@(.assert _ t m) => p1Site R s (p1E R t ++ p1O R m)
  | s@(.brk _) | s@(.cont _) | s@(.pass _) | s@(.glob ..) | s@(.nonloc ..) | s@(.imp ..)
  | s@(.impFrom ..) => p1Site R s []
def p1Hs : List Handler → List Label
  | [] => []
  | .mk l ty x b :: hs =>
    (if (R.h l).isSome then labelsHs [.mk l ty x b] else p1O R ty ++ p1B b) ++ p1Hs hs
def p1B : List Stmt → List Label
  | [] => []
  | s :: ss => p1S s ++ p1B ss
end

/-- `x` is classified alike in `p` and `q` in the scope at the head of the chain and
every scope enclosing it. -/
def alike : List Scope → Name → Bool
  | [], _ => true
  | S :: C, x => clsOf (S :: C) x == clsOf (editChain R (S :: C)) x && alike C x

/-- Part (2): the occurrences outside the sites of a name classified differently in
`q` in their scope or a scope enclosing it. -/
def part2 (p : List Stmt) : List Label :=
  let p1 := p1B R p
  (itemsB [] p).filterMap fun
    | .occ l x C => if !p1.contains l && !alike R C x then some l else none
    | .fn .. => none

/-- The functions outside the sites whose kind differs in `q`. -/
def kindChanges (p : List Stmt) : List Label :=
  let p1 := p1B R p
  (itemsB [] p).filterMap fun
    | .fn l C S => if !p1.contains l && S.kind C != (editSc R S).kind (editChain R C) then some l else none
    | .occ .. => none

/-- F_surf(p, q) (Definition 4): `none` stands for all of `p` (part (3) fires). -/
def footprint? (p : List Stmt) : Option (List Label) :=
  if kindChanges R p = [] then some (p1B R p ++ part2 R p) else none

end

/-! ## The PyCore edit of a Surf edit -/

/-- A PyCore site: the root of the translation of a Surf site, and what replaces it. -/
inductive PSite where
  | e (l : Label) (r : PE)
  | s (l : Label) (r : PS)
  | h (l : Label) (r : PyCore.Handler)

def PSite.root : PSite → Label
  | .e l _ | .s l _ | .h l _ => l

/-- The PyCore sites that replace the statements `ss` of ⌊p⌋ by `r`: the first by `r`, the
others by nothing. -/
def stmtSites : PS → PS → List PSite
  | [], _ => []
  | s :: ss, r => .s s.label r :: ss.map fun s => .s s.label []

def isNameE : Expr → Bool
  | .name .. => true
  | _ => false

section
variable (R : Edit)

/-- The PyCore site of the Surf expression site `e` (in `p`'s chain `C`) replaced by `e'`,
translated in `q`'s chain: at the root of `e`'s translation (`sub l 0`, except for a Boolean
operation of one operand, which CPython's parser never makes). -/
def siteE (C : List Scope) (e e' : Expr) : PSite := .e (trE C e).label (trE (editChain R C) e')

mutual
/-- The marker sites inside a set item's constness marker: the markers of a sign's operand
and of a tuple's elements, which the item's marker reads. -/
def cmSites : Expr → List PSite
  | .unary _ _ a => (match R.e a.label with
      | some a' => [.e (sub a.label 50) (constMark 50 a')]
      | none => cmSites a)
  | .tuple _ es => cmSitesL es
  | _ => []
def cmSitesL : List Expr → List PSite
  | [] => []
  | e :: es => (match R.e e.label with
      | some e' => [.e (sub e.label 50) (constMark 50 e')]
      | none => cmSites e) ++ cmSitesL es
end

mutual
/-- The PyCore sites of the Surf sites of `e`, evaluated in the chain `C`, following the
translation's traversal. -/
def sitesE (C : List Scope) : Expr → List PSite
  | e@(.const l _) | e@(.name l _) => match R.e l with
    | some e' => [siteE R C e e']
    | none => []
  | e@(.bin l _ a b) | e@(.sub l a b) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C a ++ sitesE C b
  | e@(.unary l _ a) | e@(.attr l a _) | e@(.yieldFrom l a) | e@(.walrus l _ a) | e@(.star l a) =>
    match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C a
  | e@(.yield l a) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesO C a
  | e@(.boolop l _ es) | e@(.fstr l es) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesEs C es
  | e@(.list l es) | e@(.tuple l es) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesA C es
  | e@(.set l es) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesSet C es
  | e@(.compare l a _ es) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C a ++ sitesEs C es
  | e@(.ifexp l c a b) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C c ++ sitesE C a ++ sitesE C b
  | e@(.call l f as ks) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C f ++ sitesA C as ++ sitesKs C ks
  | e@(.slice l a b c) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesO C a ++ sitesO C b ++ sitesO C c
  | e@(.dict l kvs) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesKV C kvs
  | e@(.lam l ps b) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesDf C ps ++ sitesAn C ps ++ sitesE (.lam l ps b :: C) b
  | e@(.comp l k es gs) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesG1 C gs ++ sitesGs (.comp l k es gs :: C) true gs ++ sitesEs (.comp l k es gs :: C) es
  | e@(.fmt l a _ s) => match R.e l with
    | some e' => [siteE R C e e']
    | none => sitesE C a ++ sitesO C s
def sitesO (C : List Scope) : Option Expr → List PSite
  | none => []
  | some e => sitesE C e
def sitesEs (C : List Scope) : List Expr → List PSite
  | [] => []
  | e :: es => sitesE C e ++ sitesEs C es
/-- The items of a display, a call's positional arguments, a class's bases: a replaced item
is its value (a starred one's operand) and its star marker. -/
def sitesA (C : List Scope) : List Expr → List PSite
  | [] => []
  | e :: es => (match R.e e.label with
      | some e' => [.e (trE C (unstar e)).label (trE (editChain R C) (unstar e')),
                    .e (sub e.label 57) (starMark e')]
      | none => sitesE C e) ++ sitesA C es
/-- A set's items: a replaced item is its value and its constness marker. -/
def sitesSet (C : List Scope) : List Expr → List PSite
  | [] => []
  | e :: es => (match R.e e.label with
      | some e' => [.e (trE C (unstar e)).label (trE (editChain R C) (unstar e')),
                    .e (sub e.label 57) (constMark 57 e')]
      | none => sitesE C e ++ cmSites R e) ++ sitesSet C es
def sitesKs (C : List Scope) : List Kw → List PSite
  | [] => []
  | .mk _ _ e :: ks => sitesE C e ++ sitesKs C ks
def sitesKV (C : List Scope) : List DItem → List PSite
  | [] => []
  | .mk k v :: kvs => sitesO C k ++ sitesE C v ++ sitesKV C kvs
def sitesDf (C : List Scope) : List Param → List PSite
  | [] => []
  | .mk _ _ _ d _ :: ps => sitesO C d ++ sitesDf C ps
def sitesAn (C : List Scope) : List Param → List PSite
  | [] => []
  | .mk _ _ _ _ a :: ps => sitesO C a ++ sitesAn C ps
def sitesG1 (C : List Scope) : List Gen → List PSite
  | [] => []
  | .mk _ _ i _ :: _ => sitesE C i
def sitesGs (C : List Scope) (first : Bool) : List Gen → List PSite
  | [] => []
  | .mk lg t i ifs :: gs =>
    (if first then [] else sitesE C i) ++ sitesT C (forSrc lg) t (sitesE C t) ++ sitesEs C ifs ++
      sitesGs C false gs
/-- The sites of the store of `src` into the target `t`; `tS` are the sites of `t` as an
expression, kept in a branch that never runs if it is no target. -/
def sitesT (C : List Scope) (src : Label → PE) (t : Expr) (tS : List PSite) : List PSite :=
  match R.e t.label with
  | some t' => stmtSites (trT C src t (trE C t)) (trT (editChain R C) src t' (trE (editChain R C) t'))
  | none => match t with
    | .name .. => []
    | .attr _ o _ => sitesE C o
    | .sub _ o i => sitesE C o ++ sitesE C i
    | .tuple lt ts | .list lt ts => sitesIt C lt 0 ts
    | .star _ e => sitesT C src e (sitesE C e)
    | _ => tS
/-- The element targets of the tuple or list target `lt`, from the `i`-th item on. -/
def sitesIt (C : List Scope) (lt : Label) (i : Nat) : List Expr → List PSite
  | [] => []
  | t :: ts => (match R.e t.label with
      | some t' =>
        stmtSites (trT C (itemSrc lt i) (unstar t) (trE C (unstar t)))
          (trT (editChain R C) (itemSrc lt i) (unstar t') (trE (editChain R C) (unstar t'))) ++
        [.e (sub t.label 57) (starMark t')]
      | none => sitesT C (itemSrc lt i) t (sitesE C t)) ++ sitesIt C lt (i + 1) ts
end

def sitesTs (C : List Scope) (src : Label → PE) : List Expr → List PSite
  | [] => []
  | t :: ts => sitesT R C src t (sitesE R C t) ++ sitesTs C src ts

mutual
/-- The sites of `del t`; `tS` are the sites of the store into `t`, kept in a branch that
never runs if it is no target. -/
def sitesD (C : List Scope) (t : Expr) (tS : List PSite) : List PSite :=
  match R.e t.label with
  | some t' => stmtSites (trD C t (trT C deadSrc t (trE C t)))
      (trD (editChain R C) t' (trT (editChain R C) deadSrc t' (trE (editChain R C) t')))
  | none => match t with
    | .name .. => []
    | .attr _ o _ => sitesE R C o
    | .sub _ o i => sitesE R C o ++ sitesE R C i
    | .tuple _ ts | .list _ ts => sitesDl C ts
    | _ => tS
def sitesDl (C : List Scope) : List Expr → List PSite
  | [] => []
  | t :: ts => sitesD C t (sitesT R C deadSrc t (sitesE R C t)) ++ sitesDl C ts
end

/-- The sites of a `def`'s annotations of the parameters of kind `k`. -/
def sitesAnnK (C : List Scope) (k : PKind) : List Param → List PSite
  | [] => []
  | .mk _ _ k' _ (some a) :: ps => (if k' = k then sitesE R C a else []) ++ sitesAnnK C k ps
  | .mk _ _ _ _ none :: ps => sitesAnnK C k ps

/-- The sites of an augmented assignment's target `t` (in the statement `l`): a replaced
target's reading statements and its store; `tS` the sites of the store into it, kept in a
branch that never runs if it is no name, attribute or subscript. -/
def sitesAug (C : List Scope) (l : Label) (t : Expr) (tS : List PSite) : List PSite :=
  match R.e t.label with
  | some t' =>
    let p := trAug C l t (trT C deadSrc t (trE C t))
    let q := trAug (editChain R C) l t' (trT (editChain R C) deadSrc t' (trE (editChain R C) t'))
    stmtSites p.1 q.1 ++ stmtSites p.2 q.2
  | none => match t with
    | .name .. => []
    | .attr _ o _ => sitesE R C o
    | .sub _ o i => sitesE R C o ++ sitesE R C i
    | _ => tS

/-- The sites of a bare annotated target's evaluation (`annBare`). -/
def sitesBare (C : List Scope) (t : Expr) (tS : List PSite) : List PSite :=
  match R.e t.label with
  | some t' => stmtSites (annBare C t (trT C deadSrc t (trE C t)))
      (annBare (editChain R C) t' (trT (editChain R C) deadSrc t' (trE (editChain R C) t')))
  | none => match t with
    | .name .. => []
    | .attr _ o _ => sitesE R C o
    | .sub _ o i => sitesE R C o ++ sitesE R C i
    | _ => tS

/-- The sites of an annotation and, at module or class level, of a replaced target's key store. -/
def sitesAnnA (C : List Scope) (l : Label) (t a : Expr) : List PSite :=
  sitesE R C a ++ (if isTop C then (match R.e t.label with
    | some t' => stmtSites (annT C l t) (annT (editChain R C) l t')
    | none => []) else [])

/-- The sites of an annotated assignment `l`. -/
def sitesAnn (C : List Scope) (l : Label) (t a : Expr) : Option Expr → List PSite
  | some v => sitesE R C v ++ sitesT R C (nameSrc "t" l) t (sitesE R C t) ++ sitesAnnA R C l t a
  | none => sitesBare R C t (sitesT R C deadSrc t (sitesE R C t)) ++ sitesAnnA R C l t a ++
      (match R.e t.label with
       | some t' => stmtSites (annBind C t) (annBind (editChain R C) t')
       | none => [])

/-- The `def` or class `x` defined in the chain `C` has another qualified name in `q`.
The outermost such node outside the sites is a PyCore site, replaced by its translation in
`q`: a class's qualified name is part of PyCore's `class` node, and it changes with that of
every enclosing `def` and class. Where the enclosing scopes keep their qualified names, the
change is in `x`'s `global` declaration in the scope around, so the node is an occurrence
of `x` classified differently, in part (2). -/
def qualCh (C : List Scope) (x : Name) : Bool := qualIn (editChain R C) x != qualIn C x

/-- A statement's sites: the statement itself if it is a site, else `rest`. -/
def stmtSite (C : List Scope) (s : Stmt) (rest : List PSite) : List PSite :=
  match R.s s.label with
  | some ss => [.s (sub s.label 0) (trB (editChain R C) ss)]
  | none => rest

mutual
def sitesS (C : List Scope) : Stmt → List PSite
  | s@(.expr _ e) => stmtSite R C s (sitesE R C e)
  | s@(.assign l ts e) => stmtSite R C s (sitesE R C e ++ sitesTs R C (nameSrc "t" l) ts)
  | s@(.augassign l t _ e) =>
    stmtSite R C s (sitesAug R C l t (sitesT R C deadSrc t (sitesE R C t)) ++ sitesE R C e)
  | s@(.annassign l t a v) => stmtSite R C s (sitesAnn R C l t a v)
  | s@(.del _ ts) => stmtSite R C s (sitesDl R C ts)
  | s@(.ite _ c t u) | s@(.while _ c t u) => stmtSite R C s (sitesE R C c ++ sitesB C t ++ sitesB C u)
  | s@(.for l t it b u) =>
    stmtSite R C s (sitesE R C it ++ sitesT R C (forSrc l) t (sitesE R C t) ++ sitesB C b ++ sitesB C u)
  | s@(.ret _ e) => stmtSite R C s (sitesO R C e)
  | s@(.defn l f ps b ds r) =>
    stmtSite R C s (if qualCh R C f then [.s (sub l 0) (trB (editChain R C) (editS R s))] else
      sitesEs R C ds ++ sitesDf R C ps ++ sitesAnnK R C .pos ps ++ sitesAnnK R C .posonly ps ++
        sitesAnnK R C .vararg ps ++ sitesAnnK R C .kwonly ps ++ sitesAnnK R C .kwarg ps ++
        sitesO R C r ++ sitesB (.fn l f ps b :: C) b)
  | s@(.cls l x bs ks b ds) =>
    stmtSite R C s (if qualCh R C x then [.s (sub l 0) (trB (editChain R C) (editS R s))] else
      sitesEs R C ds ++ sitesA R C bs ++ sitesKs R C ks ++ sitesB (.cl l x b :: C) b)
  | s@(.tryE _ b hs u) => stmtSite R C s (sitesB C b ++ sitesHs C hs ++ sitesB C u)
  | s@(.raise _ e c) => stmtSite R C s (sitesO R C e ++ sitesO R C c)
  | s@(.assert _ t m) => stmtSite R C s (sitesE R C t ++ sitesO R C m)
  | s@(.brk _) | s@(.cont _) | s@(.pass _) | s@(.glob ..) | s@(.nonloc ..) | s@(.imp ..)
  | s@(.impFrom ..) => stmtSite R C s []
def sitesHs (C : List Scope) : List Handler → List PSite
  | [] => []
  | .mk l ty x b :: hs =>
    (match R.h l with
     | some h' => (trHs (editChain R C) [h']).map (.h (sub l 0))
     | none => sitesO R C ty ++ sitesB C b) ++ sitesHs C hs
def sitesB (C : List Scope) : List Stmt → List PSite
  | [] => []
  | s :: ss => sitesS C s ++ sitesB C ss
end

/-- The replacement of the PyCore site `x` if it is an expression site at `l`. -/
def PSite.selE (l : Label) : PSite → Option PE
  | .e l' r => if l' = l then some r else none
  | _ => none
def PSite.selS (l : Label) : PSite → Option PS
  | .s l' r => if l' = l then some r else none
  | _ => none
def PSite.selH (l : Label) : PSite → Option PyCore.Handler
  | .h l' r => if l' = l then some r else none
  | _ => none

/-- The PyCore edit of `R` on `p` (labels of `p` distinct). -/
def trEdit (p : List Stmt) : PyCore.Edit :=
  let ss := sitesB R [] p
  { e := fun l => ss.findSome? (PSite.selE l)
    s := fun l => ss.findSome? (PSite.selS l)
    h := fun l => ss.findSome? (PSite.selH l) }

/-- The commutation `⌊editB R p⌋ = editB (trEdit R p) ⌊p⌋`, checked. -/
def commutes (p : List Stmt) : Bool := tr (editB R p) == PyCore.editB (trEdit R p) (tr p)

/-- F(⌊p⌋, ⌊q⌋) lies in the image of F_surf(p, q) under `l ↦ sub l k`, checked. -/
def imageOk (p : List Stmt) : Bool :=
  match footprint? R p with
  | none => true
  | some L =>
    match PyCore.footprint? (trEdit R p) (tr p) with
    | some L' => L'.all fun l' => L.contains (l' / 64)
    | none => false

/-- The roots of the PyCore sites of `trEdit R p` lie in the image of F_surf(p, q) (all of
`p` if part (3) fires), checked. -/
def rootsOk (p : List Stmt) : Bool :=
  let L := (footprint? R p).getD (labelsB p)
  (PyCore.rootsB (trEdit R p) (tr p)).all fun l' => L.contains (l' / 64)

/-- The smaller PyCore footprint of `footprint_theorem_min` (the site roots and the
flagged nodes) lies in the image of F_surf(p, q) (all of `p` if part (3) fires), checked. -/
def imageMinOk (p : List Stmt) : Bool :=
  let L := (footprint? R p).getD (labelsB p)
  (PyCore.rootsB (trEdit R p) (tr p) ++ PyCore.flagged (trEdit R p) (tr p)).all fun l' => L.contains (l' / 64)

end

/-! ## Conditions on edits and the fresh-name pattern, executable (checked in `SurfTests.lean`) -/

abbrev R0 := PyCore.Edit.none

section
variable (R : Edit)

/-- A name, an attribute, or a subscript. -/
def simpleT : Expr → Bool
  | .name .. | .attr .. | .sub .. => true
  | _ => false

/-- An augmented assignment's target, in `p` and in `q`, is a name, an attribute, or a
subscript (Python's grammar allows no other), which the translation reads and stores once. -/
def augOk (t : Expr) : Bool :=
  simpleT t && (match R.e t.label with
    | some t' => simpleT t'
    | none => true)

mutual
/-- Outside the sites, every augmented assignment's target and its replacement is a name,
an attribute, or a subscript (Python's grammar allows no other target). -/
def regS (C : List Scope) : Stmt → Bool
  | .augassign l t _ _ => (R.s l).isSome || augOk R t
  | .ite l _ t u | .while l _ t u | .for l _ _ t u => (R.s l).isSome || (regB C t && regB C u)
  | .defn l f ps b _ _ => (R.s l).isSome || regB (.fn l f ps b :: C) b
  | .cls l x _ _ b _ => (R.s l).isSome || regB (.cl l x b :: C) b
  | .tryE l b hs u => (R.s l).isSome || (regB C b && regHs C hs && regB C u)
  | _ => true
def regHs (C : List Scope) : List Handler → Bool
  | [] => true
  | .mk l _ _ b :: hs => ((R.h l).isSome || regB C b) && regHs C hs
def regB (C : List Scope) : List Stmt → Bool
  | [] => true
  | s :: ss => regS C s && regB C ss
end

/-- Each expression replacement is labelled as the node it replaces. -/
def KeepsLabels : Prop := ∀ l e', R.e l = some e' → e'.label = l

end

/-- What a scope's own body says about `x`: binds it, binds it by a walrus, declares it
`global`, declares it `nonlocal`. -/
def xf (x : Name) (S : PyCore.Scope) : Bool × Bool × Bool × Bool :=
  (S.facts.contains (.bind x), S.facts.contains (.wal x), S.facts.contains (.glob x),
    S.facts.contains (.nonloc x))

def none4 : Bool × Bool × Bool × Bool := (false, false, false, false)

/-- A fresh name: bound in the scope of the occurrence, and in no scope around it. -/
def patB : List PyCore.Scope → List (Bool × Bool × Bool × Bool)
  | [] => []
  | _ :: C => (true, false, false, false) :: C.map fun _ => none4

end Surf
