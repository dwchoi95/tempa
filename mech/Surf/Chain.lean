/-
(T1) for edits: every item of ⌊p⌋ outside the PyCore sites of `trEdit R p` is fresh, or
the image of an item of `p` in part (1) or whose chain satisfies the chain equation
(`ChainEq`). The induction follows `trB_edit` and cuts where it does: at the Surf sites
and at the `def` and class nodes whose qualified name changes (PyCore sites).
-/
import Surf.Image

set_option linter.unusedSectionVars false

namespace Surf
open PyCore (Name Label)

/-- The chain equation of a chain: under `R'`, its image is the image of its edit. -/
abbrev CE (R : Edit) (R' : PyCore.Edit) (C : List Scope) : Prop :=
  (trChain C).map (PyCore.editSc R') = trChain (editChain R C)

/-- A Surf item in part (1) `P`, or whose chain satisfies the chain equation. -/
def Gd (R : Edit) (R' : PyCore.Edit) (P : List Label) (j : Item) : Prop :=
  j.lab ∈ P ∨ ChainEq R R' j

section
variable {R : Edit} {R' : PyCore.Edit}

theorem CE.cons {S : Scope} {C : List Scope}
    (h1 : PyCore.editSc R' (trScope C S) = trScope (editChain R C) (editSc R S)) (h2 : CE R R' C) :
    CE R R' (S :: C) := by
  simp only [CE, trChain, List.map_cons, editChain_cons, h1]; exact congrArg _ h2

theorem Gd.mono {P P' : List Label} {j : Item} (h : ∀ x ∈ P, x ∈ P') : Gd R R' P j → Gd R R' P' j :=
  Or.imp (h _) id

theorem gd_paramOccs {P : List Label} {C : List Scope} (h : CE R R' C) :
    ∀ ps, ∀ j ∈ paramOccs C ps, Gd R R' P j := by
  intro ps j hj
  simp only [paramOccs, List.mem_map] at hj
  obtain ⟨q, -, rfl⟩ := hj
  exact .inr h

/-- Every Surf item of a node inside a site is in part (1). -/
theorem gd_site {P : List Label} {B : List Item} (h : ∀ j ∈ B, j.lab ∈ P) : ∀ j ∈ B, Gd R R' P j :=
  fun j hj => .inl (h j hj)

variable (hk : KeepsLabels R)
include hk

/-! ## The scope equations of lambdas and comprehensions -/

theorem scope_lam {C : List Scope} {l : Label} {ps : List Param} {b : Expr}
    (hR : R.e l = none) (hs : ∀ x ∈ sitesE R C (.lam l ps b), x.Agrees R')
    (ho : ∀ l' ∈ olabelsE R (.lam l ps b), NB R' l') :
    PyCore.editSc R' (trScope C (.lam l ps b)) = trScope (editChain R C) (editSc R (.lam l ps b)) := by
  nbl
  have ih2 := trE_edit hk (.lam l ps b :: C) b cmFromS fromO
  simp only [editChain_cons, editSc] at ih2
  have hpb := peditB_paramBind (.lam l ps b :: C) ps
    (fun q hq => ho _ (by simp [olabelsE, ocut, hR, mem_olabelsPs R hq]))
  have hpe := paramBind_edit R (C := .lam l ps b :: C)
    (C' := .lam l (editPs R ps) (editE R b) :: editChain R C) (by simp [priv]) ps
  simp (disch := omega) [trScope, editSc, PyCore.editSc, peditB_append, hpb, hpe, PyCore.editB,
    PyCore.editS, hl.2.1, ih2]

theorem scope_comp {C : List Scope} {l : Label} {k : CompKind} {es : List Expr}
    {gs : List Gen} (hR : R.e l = none) (hs : ∀ x ∈ sitesE R C (.comp l k es gs), x.Agrees R')
    (ho : ∀ l' ∈ olabelsE R (.comp l k es gs), NB R' l') :
    PyCore.editSc R' (trScope C (.comp l k es gs)) =
      trScope (editChain R C) (editSc R (.comp l k es gs)) := by
  nbl
  have ih3 := trEs_edit hk (.comp l k es gs :: C) es cmFromS fromO
  simp only [editChain_cons, editSc] at ih3
  have ih2 := trGs_edit hk (.comp l k es gs :: C) (fresh "i" l) true gs
    (compElt l k (trEs (.comp l k es gs :: C) es))
    (compElt l k (trEs (.comp l k (editEs R es) (editGs R gs) :: editChain R C) (editEs R es)))
    (by rw [peditB_compElt hl, ih3]) cmFromS fromO
  simp only [editChain_cons, editSc] at ih2
  simp only [trScope, editSc, PyCore.editSc, peditB_compWrap hl, ih2]

/-! ## Items of expressions -/

set_option hygiene false in
macro "siteJ" : tactic => `(tactic| exact fun j hj => .inl (by
  simp only [p1E, hR, Option.isSome_some, ite_true]; exact labE _ C j hj))

set_option hygiene false in
/-- Close a non-site case from the children's facts. -/
macro "cj" : tactic => `(tactic| (
  intro j hj
  simp only [itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, p1E, p1O, p1Es,
    p1Ks, p1Ds, p1Ps, p1Gs, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append,
    List.mem_cons] at hj ⊢
  simp only [Gd, List.mem_append] at *
  grind))

set_option hygiene false in
/-- `cj` for the lists of nodes. -/
macro "cjn" : tactic => `(tactic| (
  intro j hj
  simp only [itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, p1E, p1O, p1Es,
    p1Ks, p1Ds, p1Ps, p1Gs, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true,
    List.mem_append, List.mem_cons, List.not_mem_nil, false_or] at hj ⊢
  simp only [Gd, List.mem_append] at *
  grind))

set_option hygiene false in
/-- A non-site node with one child `a`. -/
macro "one" a:term:max : tactic => `(tactic| (
  cases hR : R.e l with
  | some e' => siteJ
  | none => have ih1 := ceE C hC $a cmFromS fromO; cj))

/-- Items whose nodes lie in a list of labels. -/
theorem gd_of_lab {P : List Label} {B : List Item} {Q : List Label} (h : ∀ j ∈ B, j.lab ∈ Q)
    (hQ : ∀ x ∈ Q, x ∈ P) : ∀ j ∈ B, Gd R R' P j := fun j hj => .inl (hQ _ (h j hj))

mutual
theorem ceE (C : List Scope) (hC : CE R R' C) : ∀ (e : Expr),
    (∀ x ∈ sitesE R C e, x.Agrees R') → (∀ l ∈ olabelsE R e, NB R' l) →
    ∀ j ∈ itemsE C e, Gd R R' (p1E R e) j
  | .const .., _, _ => by simp [itemsE]
  | .name .., _, _ => by intro j hj; simp only [itemsE, List.mem_singleton] at hj; subst hj; exact .inr hC
  | .bin l op a b, hs, ho | .sub l a b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceE C hC a cmFromS fromO
      have ih2 := ceE C hC b cmFromS fromO
      cj
  | .unary l _ a, hs, ho => by one a
  | .attr l a _, hs, ho => by one a
  | .yieldFrom l a, hs, ho => by one a
  | .star l a, hs, ho => by one a
  | .walrus l x a, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceE C hC a cmFromS fromO
      have h0 : ChainEq R R' (.occ l (mangle (priv C) x) C) := hC; cj
  | .yield l none, hs, ho => by simp [itemsE, itemsO]
  | .yield l (some a), hs, ho => by one a
  | .boolop l _ es, hs, ho | .fstr l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none => have ih1 := ceEs C hC es cmFromS fromO; cj
  | .list l es, hs, ho | .tuple l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none => have ih1 := ceA C hC es cmFromS fromO; cj
  | .set l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none => have ih1 := ceSet C hC es cmFromS fromO; cj
  | .compare l a _ es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceE C hC a cmFromS fromO; have ih2 := ceEs C hC es cmFromS fromO; cj
  | .ifexp l c a b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceE C hC c cmFromS fromO; have ih2 := ceE C hC a cmFromS fromO
      have ih3 := ceE C hC b cmFromS fromO; cj
  | .call l f as ks, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceE C hC f cmFromS fromO; have ih2 := ceA C hC as cmFromS fromO
      have ih3 := ceKs C hC ks cmFromS fromO; cj
  | .slice l a b c, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have ih1 := ceO C hC a cmFromS fromO; have ih2 := ceO C hC b cmFromS fromO
      have ih3 := ceO C hC c cmFromS fromO; cj
  | .dict l kvs, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none => have ih1 := ceKV C hC kvs cmFromS fromO; cj
  | .fmt l a _ s, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none => have ih1 := ceE C hC a cmFromS fromO; have ih2 := ceO C hC s cmFromS fromO; cj
  | .lam l ps b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have hC' : CE R R' (.lam l ps b :: C) := CE.cons (scope_lam hk hR hs ho) hC
      have ih1 := cePs C hC ps (fun x hx => hs x (by
        simp only [List.mem_append] at hx; simp [sitesE, hR]; grind)) fromO
      have ih2 := ceE (.lam l ps b :: C) hC' b cmFromS fromO
      have ih3 := gd_paramOccs (P := p1Ps R ps ++ p1E R b) hC' ps
      have ih4 : Gd R R' (p1Ps R ps ++ p1E R b) (.fn l C (.lam l ps b)) := .inr hC'
      cj
  | .comp l k es gs, hs, ho => by
    cases hR : R.e l with
    | some e' => siteJ
    | none =>
      have hC' : CE R R' (.comp l k es gs :: C) := CE.cons (scope_comp hk hR hs ho) hC
      have ih1 := ceG1 C hC gs cmFromS fromO
      have ih2 := ceGs (.comp l k es gs :: C) hC' true gs cmFromS fromO
      have ih3 := ceEs (.comp l k es gs :: C) hC' es cmFromS fromO
      have ih4 : Gd R R' (p1Es R es ++ p1Gs R gs) (.fn l C (.comp l k es gs)) := .inr hC'
      cj
theorem ceO (C : List Scope) (hC : CE R R' C) : ∀ o, (∀ x ∈ sitesO R C o, x.Agrees R') →
    (∀ l ∈ olabelsO R o, NB R' l) → ∀ j ∈ itemsO C o, Gd R R' (p1O R o) j
  | none, _, _ => by simp [itemsO]
  | some e, hs, ho => by simp only [itemsO, p1O]; exact ceE C hC e hs ho
theorem ceEs (C : List Scope) (hC : CE R R' C) : ∀ (es : List Expr),
    (∀ x ∈ sitesEs R C es, x.Agrees R') → (∀ l ∈ olabelsEs R es, NB R' l) →
    ∀ j ∈ itemsEs C es, Gd R R' (p1Es R es) j
  | [], _, _ => by simp [itemsEs]
  | e :: es, hs, ho => by
    simp only [sitesEs, olabelsEs, List.forall_mem_append] at hs ho
    have ih1 := ceE C hC e hs.1 ho.1
    have ih2 := ceEs C hC es hs.2 ho.2
    cjn
theorem ceA (C : List Scope) (hC : CE R R' C) : ∀ (es : List Expr),
    (∀ x ∈ sitesA R C es, x.Agrees R') → (∀ l ∈ olabelsEs R es, NB R' l) →
    ∀ j ∈ itemsEs C es, Gd R R' (p1Es R es) j
  | [], _, _ => by simp [itemsEs]
  | e :: es, hs, ho => by
    simp only [sitesA, olabelsEs, List.forall_mem_append] at hs ho
    have ih2 := ceA C hC es hs.2 ho.2
    cases hR : R.e e.label with
    | some e' =>
      have ih1 : ∀ j ∈ itemsE C e, Gd R R' (p1E R e) j :=
        fun j hj => .inl (by rw [p1E_site R hR]; exact labE _ C j hj)
      cjn
    | none =>
      simp only [hR] at hs
      have ih1 := ceE C hC e hs.1 ho.1
      cjn
theorem ceSet (C : List Scope) (hC : CE R R' C) : ∀ (es : List Expr),
    (∀ x ∈ sitesSet R C es, x.Agrees R') → (∀ l ∈ olabelsEs R es, NB R' l) →
    ∀ j ∈ itemsEs C es, Gd R R' (p1Es R es) j
  | [], _, _ => by simp [itemsEs]
  | e :: es, hs, ho => by
    simp only [sitesSet, olabelsEs, List.forall_mem_append] at hs ho
    have ih2 := ceSet C hC es hs.2 ho.2
    cases hR : R.e e.label with
    | some e' =>
      have ih1 : ∀ j ∈ itemsE C e, Gd R R' (p1E R e) j :=
        fun j hj => .inl (by rw [p1E_site R hR]; exact labE _ C j hj)
      cjn
    | none =>
      simp only [hR, List.forall_mem_append] at hs
      have ih1 := ceE C hC e hs.1.1 ho.1
      cjn
theorem ceKs (C : List Scope) (hC : CE R R' C) : ∀ ks, (∀ x ∈ sitesKs R C ks, x.Agrees R') →
    (∀ l ∈ olabelsKs R ks, NB R' l) → ∀ j ∈ itemsKs C ks, Gd R R' (p1Ks R ks) j
  | [], _, _ => by simp [itemsKs]
  | .mk l x e :: ks, hs, ho => by
    have ih1 := ceE C hC e (fun y hy => hs y (by simp [sitesKs, hy])) (fun y hy => ho y (by simp [olabelsKs, hy]))
    have ih2 := ceKs C hC ks (fun y hy => hs y (by simp [sitesKs, hy])) (fun y hy => ho y (by simp [olabelsKs, hy]))
    cjn
theorem ceKV (C : List Scope) (hC : CE R R' C) : ∀ kvs, (∀ x ∈ sitesKV R C kvs, x.Agrees R') →
    (∀ l ∈ olabelsDs R kvs, NB R' l) → ∀ j ∈ itemsDs C kvs, Gd R R' (p1Ds R kvs) j
  | [], _, _ => by simp [itemsDs]
  | .mk k v :: kvs, hs, ho => by
    have ih1 := ceO C hC k (fun y hy => hs y (by simp [sitesKV, hy])) (fun y hy => ho y (by simp [olabelsDs, hy]))
    have ih2 := ceE C hC v (fun y hy => hs y (by simp [sitesKV, hy])) (fun y hy => ho y (by simp [olabelsDs, hy]))
    have ih3 := ceKV C hC kvs (fun y hy => hs y (by simp [sitesKV, hy])) (fun y hy => ho y (by simp [olabelsDs, hy]))
    cjn
theorem cePs (C : List Scope) (hC : CE R R' C) : ∀ ps, (∀ x ∈ sitesDf R C ps ++ sitesAn R C ps, x.Agrees R') →
    (∀ l ∈ olabelsPs R ps, NB R' l) → ∀ j ∈ itemsPs C ps, Gd R R' (p1Ps R ps) j
  | [], _, _ => by simp [itemsPs]
  | .mk l _ _ d a :: ps, hs, ho => by
    have ih1 := ceO C hC d (fun y hy => hs y (by simp [sitesDf, sitesAn, hy]))
      (fun y hy => ho y (by simp [olabelsPs, hy]))
    have ih2 := ceO C hC a (fun y hy => hs y (by simp [sitesDf, sitesAn, hy]))
      (fun y hy => ho y (by simp [olabelsPs, hy]))
    have ih3 := cePs C hC ps (fun y hy => hs y (by
        simp only [List.mem_append] at hy; simp [sitesDf, sitesAn]; grind))
      (fun y hy => ho y (by simp [olabelsPs, hy]))
    cjn
theorem ceG1 (C : List Scope) (hC : CE R R' C) : ∀ gs, (∀ x ∈ sitesG1 R C gs, x.Agrees R') →
    (∀ l ∈ olabelsGs R gs, NB R' l) → ∀ j ∈ itemsG1 C gs, Gd R R' (p1Gs R gs) j
  | [], _, _ => by simp [itemsG1]
  | .mk lg t i ifs :: gs, hs, ho => by
    have ih1 := ceE C hC i (fun y hy => hs y (by simp [sitesG1, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
    cjn
theorem ceGs (C : List Scope) (hC : CE R R' C) : ∀ (first : Bool) (gs : List Gen),
    (∀ x ∈ sitesGs R C first gs, x.Agrees R') → (∀ l ∈ olabelsGs R gs, NB R' l) →
    ∀ j ∈ itemsGs C first gs, Gd R R' (p1Gs R gs) j
  | _, [], _, _ => by simp [itemsGs]
  | first, .mk lg t i ifs :: gs, hs, ho => by
    have ho1 : ∀ y ∈ olabelsE R t, NB R' y := fun y hy => ho y (by simp [olabelsGs, hy])
    have ih2 := ceT C hC (forSrc lg) t (fun h => ceE C hC t h ho1) (fun y hy => hs y (by simp [sitesGs, hy])) ho1
    have ih3 := ceEs C hC ifs (fun y hy => hs y (by simp [sitesGs, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
    have ih4 := ceGs C hC false gs (fun y hy => hs y (by simp [sitesGs, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
    cases first
    · have ih1 := ceE C hC i (fun y hy => hs y (by simp [sitesGs, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
      cjn
    · cjn
theorem ceT (C : List Scope) (hC : CE R R' C) (src : Label → PE) : ∀ t,
    ((∀ x ∈ sitesE R C t, x.Agrees R') → ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j) →
    (∀ x ∈ sitesT R C src t (sitesE R C t), x.Agrees R') → (∀ l ∈ olabelsE R t, NB R' l) →
    ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j
  | t, htE, hs, ho => by
    cases hR : R.e t.label with
    | some t' => exact fun j hj => .inl (by rw [p1E_site R hR]; exact labE _ C j hj)
    | none =>
      cases t with
      | name lt x => intro j hj; simp only [itemsE, List.mem_singleton] at hj; subst hj; exact .inr hC
      | attr l o a =>
        simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label] at hs
        have ih1 := ceE C hC o hs fromO; cj
      | sub l o i =>
        simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label, List.forall_mem_append] at hs
        have ih1 := ceE C hC o hs.1 fromO; have ih2 := ceE C hC i hs.2 fromO; cj
      | tuple l ts =>
        simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label] at hs
        have ih1 := ceIt C hC l 0 ts hs fromO; cj
      | list l ts =>
        simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label] at hs
        have ih1 := ceIt C hC l 0 ts hs fromO; cj
      | star l e =>
        simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label] at hs
        have ih1 := ceT C hC src e (fun h => ceE C hC e h fromO) hs fromO; cj
      | _ => simp only [Expr.label] at hR; simp only [sitesT, hR, Expr.label] at hs; exact htE hs
theorem ceIt (C : List Scope) (hC : CE R R' C) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    (∀ x ∈ sitesIt R C lt i ts, x.Agrees R') → (∀ l ∈ olabelsEs R ts, NB R' l) →
    ∀ j ∈ itemsEs C ts, Gd R R' (p1Es R ts) j
  | _, [], _, _ => by simp [itemsEs]
  | i, t :: ts, hs, ho => by
    simp only [sitesIt, olabelsEs, List.forall_mem_append] at hs ho
    have ih2 := ceIt C hC lt (i + 1) ts hs.2 ho.2
    cases hR : R.e t.label with
    | some t' =>
      have ih1 : ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j :=
        fun j hj => .inl (by rw [p1E_site R hR]; exact labE _ C j hj)
      cjn
    | none =>
      simp only [hR] at hs
      have ih1 := ceT C hC (itemSrc lt i) t (fun h => ceE C hC t h ho.1) hs.1 ho.1
      cjn
end

end


/-! ## Items of ⌊p⌋ outside the PyCore sites -/

section
variable {R : Edit} {R' : PyCore.Edit}

/-- The items `A` of ⌊p⌋ are fresh, or images of items of `B` in `P` or with the chain
equation. -/
def SG (R : Edit) (R' : PyCore.Edit) (A : List PyCore.Item) (B : List Item) (P : List Label) : Prop :=
  ∀ i ∈ A, FreshItem i ∨ ∃ j ∈ B, Img j i ∧ Gd R R' P j

theorem SG.of_sim {A A' : List PyCore.Item} {B : List Item} {P : List Label} (h : Sim A B)
    (hg : ∀ j ∈ B, Gd R R' P j) (hA : ∀ i ∈ A', i ∈ A) : SG R R' A' B P :=
  fun i hi => (h.sound i (hA i hi)).imp id fun ⟨j, hj, hij⟩ => ⟨j, hj, hij, hg j hj⟩

theorem SG.app {A A' : List PyCore.Item} {B B' : List Item} {P P' : List Label}
    (h1 : SG R R' A B P) (h2 : SG R R' A' B' P') : SG R R' (A ++ A') (B ++ B') (P ++ P') := by
  intro i hi
  rcases List.mem_append.1 hi with h | h
  · exact (h1 i h).imp id fun ⟨j, hj, hij, hg⟩ =>
      ⟨j, List.mem_append_left _ hj, hij, hg.mono fun _ h => List.mem_append_left _ h⟩
  · exact (h2 i h).imp id fun ⟨j, hj, hij, hg⟩ =>
      ⟨j, List.mem_append_right _ hj, hij, hg.mono fun _ h => List.mem_append_right _ h⟩

theorem SG.cover {A A' : List PyCore.Item} {B B' : List Item} {P P' : List Label} (h : SG R R' A B P)
    (hA : ∀ i ∈ A', i ∈ A ∨ FreshItem i) (hB : ∀ j ∈ B, j ∈ B') (hP : ∀ x ∈ P, x ∈ P') :
    SG R R' A' B' P' := by
  intro i hi
  rcases hA i hi with h' | h'
  · exact (h i h').imp id fun ⟨j, hj, hij, hg⟩ => ⟨j, hB j hj, hij, hg.mono hP⟩
  · exact .inl h'

theorem SG.oc (l k : Label) (x : Name) {C : List Scope} {P : List Label} (h : CE R R' C)
    (hk : k < 64 := by decide) : SG R R' [.occ (sub l k) x (trChain C)] [.occ l x C] P := by
  intro i hi; simp only [List.mem_singleton] at hi; subst hi
  exact .inr ⟨_, List.mem_singleton_self _, ⟨⟨k, hk, rfl⟩, rfl, rfl⟩, .inr h⟩

theorem SG.fn1 (l : Label) (C : List Scope) (S : Scope) {P : List Label} (h : CE R R' (S :: C)) :
    SG R R' [.fn (sub l 1) (trScope C S)] [.fn l C S] P := by
  intro i hi; simp only [List.mem_singleton] at hi; subst hi
  exact .inr ⟨_, List.mem_singleton_self _, ⟨rfl, rfl⟩, .inr h⟩

theorem sg_implicit (l : Label) (C : List Scope) (S : Scope) {P : List Label} (h : CE R R' (S :: C)) :
    SG R R' (PyCore.classImplicit.map fun y => .occ (sub l 1) y (trChain (S :: C)))
      (PyCore.classImplicit.map fun y => .occ l y (S :: C)) P := by
  intro i hi; simp only [List.mem_map] at hi; obtain ⟨y, hy, rfl⟩ := hi
  exact .inr ⟨_, List.mem_map_of_mem hy, ⟨⟨1, by omega, rfl⟩, rfl, rfl⟩, .inr h⟩

theorem freshItem_fresh (lab : Label) (t : String) (l : Label) (C : List PyCore.Scope) :
    FreshItem (.occ lab (fresh t l) C) := ⟨t, l, rfl⟩

theorem pitemsE_foldlR (C : List PyCore.Scope) {L : Label} (hL : R'.e L = none) :
    ∀ (es : List PE) (acc : PE), PyCore.itemsE R' C (es.foldl (fun acc e => .bin L "," acc e) acc) =
      PyCore.itemsE R' C acc ++ es.flatMap (PyCore.itemsE R' C)
  | [], _ => by simp
  | e :: es, acc => by simp [pitemsE_foldlR C hL es, PyCore.itemsE, hL]

theorem pitemsE_ccRR (C : List PyCore.Scope) {r : Label} (hr : R'.e r = none) (g : String) (es : List PE) :
    PyCore.itemsE R' C (ccR r g es) = es.flatMap (PyCore.itemsE R' C) := by
  simp [ccR, recR, pitemsE_foldlR C hr, PyCore.itemsE, hr]

theorem pitemsE_ccR_nb (C : List PyCore.Scope) {l : Label} (hl : NB R' l) : ∀ k, k < 64 → ∀ g es,
    PyCore.itemsE R' C (ccR (sub l k) g es) = es.flatMap (PyCore.itemsE R' C) :=
  fun k hk g es => pitemsE_ccRR C (hl.1 k hk) g es

@[simp] theorem pitemsE_paramMarkR (D : List PyCore.Scope) (C : List Scope) (q : Param) :
    PyCore.itemsE R' D (paramMark C q) = [] := rfl
@[simp] theorem pitemsE_starMarkR (D : List PyCore.Scope) (e : Expr) : PyCore.itemsE R' D (starMark e) = [] := by
  cases e <;> rfl
@[simp] theorem pitemsE_kwMarkR (D : List PyCore.Scope) (k : Kw) : PyCore.itemsE R' D (kwMark k) = [] := by
  cases k; rfl

/-- `sgcat p₁ … pₙ` appends the `SG` facts `pᵢ`. -/
syntax "sgcat" (ppSpace colGt term:max)+ : term
macro_rules
  | `(sgcat $p) => `($p)
  | `(sgcat $p $ps*) => `(SG.app $p (sgcat $ps*))

variable (hk : KeepsLabels R)
include hk

theorem sgE (C : List Scope) (e : Expr) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesE R C e, x.Agrees R') (ho : ∀ l ∈ olabelsE R e, NB R' l) :
    SG R R' (PyCore.itemsE R' (trChain C) (trE C e)) (itemsE C e) (p1E R e) :=
  SG.of_sim (trE_items C e) (ceE hk C hC e hs ho) (pitemsE_sub _ _ _)

theorem sgEs (C : List Scope) (es : List Expr) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesEs R C es, x.Agrees R') (ho : ∀ l ∈ olabelsEs R es, NB R' l) :
    SG R R' ((trEs C es).flatMap (PyCore.itemsE R' (trChain C))) (itemsEs C es) (p1Es R es) :=
  SG.of_sim (trEs_items C es) (ceEs hk C hC es hs ho) fun i hi => by
    simp only [List.mem_flatMap] at hi ⊢; obtain ⟨e, he, hi⟩ := hi; exact ⟨e, he, pitemsE_sub _ _ _ i hi⟩

theorem sgA (C : List Scope) (es : List Expr) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesA R C es, x.Agrees R') (ho : ∀ l ∈ olabelsEs R es, NB R' l) :
    SG R R' ((trA C es).flatMap (PyCore.itemsE R' (trChain C))) (itemsEs C es) (p1Es R es) :=
  SG.of_sim (trA_items C es) (ceA hk C hC es hs ho) fun i hi => by
    simp only [List.mem_flatMap] at hi ⊢; obtain ⟨e, he, hi⟩ := hi; exact ⟨e, he, pitemsE_sub _ _ _ i hi⟩

theorem sgO (C : List Scope) (l : Label) (k : Nat) (o : Option Expr) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesO R C o, x.Agrees R') (ho : ∀ l ∈ olabelsO R o, NB R' l) :
    SG R R' (PyCore.itemsE R' (trChain C) (trO C l k o)) (itemsO C o) (p1O R o) :=
  SG.of_sim (trO_items C l k o) (ceO hk C hC o hs ho) (pitemsE_sub _ _ _)

theorem sgKs (C : List Scope) (ks : List Kw) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesKs R C ks, x.Agrees R') (ho : ∀ l ∈ olabelsKs R ks, NB R' l) :
    SG R R' ((trKs C ks).flatMap (PyCore.itemsE R' (trChain C))) (itemsKs C ks) (p1Ks R ks) :=
  SG.of_sim (trKs_items C ks) (ceKs hk C hC ks hs ho) fun i hi => by
    simp only [List.mem_flatMap] at hi ⊢; obtain ⟨e, he, hi⟩ := hi; exact ⟨e, he, pitemsE_sub _ _ _ i hi⟩

theorem sgT (C : List Scope) (src : Label → PE) (hsrc : SrcIt src) (t : Expr) (hC : CE R R' C)
    (hs : ∀ x ∈ sitesT R C src t (sitesE R C t), x.Agrees R') (ho : ∀ l ∈ olabelsE R t, NB R' l) :
    SG R R' (PyCore.itemsB R' (trChain C) (trT C src t (trE C t))) (itemsE C t) (p1E R t) :=
  SG.of_sim (trT_items C src hsrc t (trE_items C t)) (ceT hk C hC src t (fun h => ceE hk C hC t h ho) hs ho)
    (pitemsB_sub _ _ _)

/-- The scope equation of a `def` whose body `trB_edit` translates alike. -/
theorem scope_fn {C : List Scope} {l : Label} {f : Name} {ps : List Param} {b : List Stmt}
    (hr : regB R (.fn l f ps b :: C) b = true) (hs : ∀ x ∈ sitesB R (.fn l f ps b :: C) b, x.Agrees R')
    (ho : ∀ l' ∈ olabelsB R (.fn l f ps b :: C) b, NB R' l') (hp : ∀ q ∈ ps, NB R' q.label) :
    PyCore.editSc R' (trScope C (.fn l f ps b)) = trScope (editChain R C) (editSc R (.fn l f ps b)) := by
  have ih4 := trB_edit hk (.fn l f ps b :: C) b hr hs ho
  simp only [editChain_cons, editSc] at ih4
  have hpb := peditB_paramBind (.fn l f ps b :: C) ps hp
  have hpe := paramBind_edit R (C := .fn l f ps b :: C)
    (C' := .fn l f (editPs R ps) (editB R b) :: editChain R C) (by simp [priv]) ps
  simp only [trScope, editSc, PyCore.editSc, peditB_append, hpb, hpe, ih4]

/-- The scope equation of a class body that `trB_edit` translates alike. -/
theorem scope_cl {C : List Scope} {l : Label} {x : Name} {b : List Stmt} (hl : NB R' l)
    (hr : regB R (.cl l x b :: C) b = true) (hs : ∀ y ∈ sitesB R (.cl l x b :: C) b, y.Agrees R')
    (ho : ∀ l' ∈ olabelsB R (.cl l x b :: C) b, NB R' l') :
    PyCore.editSc R' (trScope C (.cl l x b)) = trScope (editChain R C) (editSc R (.cl l x b)) := by
  have ih := trB_edit hk (.cl l x b :: C) b hr hs ho
  simp only [editChain_cons, editSc] at ih
  simp (disch := omega) [trScope, editSc, PyCore.editSc, ih, PyCore.editB, setupS, PyCore.editS, hl.1, hl.2.1,
    gad, cc, peditE_ccR (hl.1 5 (by omega)), peditE_ccR (hl.1 6 (by omega))]

theorem ceAug (C : List Scope) (hC : CE R R' C) (l : Label) (t : Expr)
    (hs : ∀ x ∈ sitesAug R C l t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R')
    (ho : ∀ l ∈ olabelsE R t, NB R' l) :
    ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j := by
  cases hT : R.e t.label with
  | some t' => exact fun j hj => .inl (by rw [p1E_site R hT]; exact labE _ C j hj)
  | none =>
    unfold sitesAug at hs; simp only [hT] at hs
    cases t with
    | name lt x => intro j hj; simp only [itemsE, List.mem_singleton] at hj; subst hj; exact .inr hC
    | attr lt o a =>
      have := ceE hk C hC o hs (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      intro j hj; simp only [itemsE, p1E] at hj ⊢; simp_all [Expr.label]
    | sub lt o i =>
      simp only [List.forall_mem_append] at hs
      have h1 := ceE hk C hC o hs.1 (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      have h2 := ceE hk C hC i hs.2 (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      intro j hj; simp only [itemsE, p1E, List.mem_append] at hj ⊢; simp only [Expr.label] at hT
      simp only [hT, Option.isSome_none, Bool.false_eq_true, ite_false]
      rcases hj with hj | hj
      · exact (h1 j hj).mono (fun _ h => List.mem_append_left _ h)
      · exact (h2 j hj).mono (fun _ h => List.mem_append_right _ h)
    | _ => exact ceT hk C hC deadSrc _ (fun h => ceE hk C hC _ h ho) hs ho

theorem ceBare (C : List Scope) (hC : CE R R' C) (t : Expr)
    (hs : ∀ x ∈ sitesBare R C t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R')
    (ho : ∀ l ∈ olabelsE R t, NB R' l) :
    ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j := by
  cases hT : R.e t.label with
  | some t' => exact fun j hj => .inl (by rw [p1E_site R hT]; exact labE _ C j hj)
  | none =>
    unfold sitesBare at hs; simp only [hT] at hs
    cases t with
    | name lt x => intro j hj; simp only [itemsE, List.mem_singleton] at hj; subst hj; exact .inr hC
    | attr lt o a =>
      have := ceE hk C hC o hs (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      intro j hj; simp only [itemsE, p1E] at hj ⊢; simp_all [Expr.label]
    | sub lt o i =>
      simp only [List.forall_mem_append] at hs
      have h1 := ceE hk C hC o hs.1 (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      have h2 := ceE hk C hC i hs.2 (fun y hy => ho y (by simp_all [olabelsE, ocut, Expr.label]))
      intro j hj; simp only [itemsE, p1E, List.mem_append] at hj ⊢; simp only [Expr.label] at hT
      simp only [hT, Option.isSome_none, Bool.false_eq_true, ite_false]
      rcases hj with hj | hj
      · exact (h1 j hj).mono (fun _ h => List.mem_append_left _ h)
      · exact (h2 j hj).mono (fun _ h => List.mem_append_right _ h)
    | _ => exact ceT hk C hC deadSrc _ (fun h => ceE hk C hC _ h ho) hs ho

mutual
theorem ceD (C : List Scope) (hC : CE R R' C) : ∀ t,
    (∀ x ∈ sitesD R C t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R') → (∀ l ∈ olabelsE R t, NB R' l) →
    ∀ j ∈ itemsE C t, Gd R R' (p1E R t) j
  | t, hs, ho => by
    cases hR : R.e t.label with
    | some t' => exact fun j hj => .inl (by rw [p1E_site R hR]; exact labE _ C j hj)
    | none =>
      unfold sitesD at hs; simp only [hR] at hs
      cases t with
      | name lt x => intro j hj; simp only [itemsE, List.mem_singleton] at hj; subst hj; exact .inr hC
      | attr l o a =>
        simp only [Expr.label] at hR
        have ih1 := ceE hk C hC o hs fromO; cj
      | sub l o i =>
        simp only [Expr.label] at hR; simp only [List.forall_mem_append] at hs
        have ih1 := ceE hk C hC o hs.1 fromO; have ih2 := ceE hk C hC i hs.2 fromO; cj
      | tuple l ts =>
        simp only [Expr.label] at hR
        have ih1 := ceDl C hC ts hs fromO; cj
      | list l ts =>
        simp only [Expr.label] at hR
        have ih1 := ceDl C hC ts hs fromO; cj
      | _ => exact ceT hk C hC deadSrc _ (fun h => ceE hk C hC _ h ho) hs ho
theorem ceDl (C : List Scope) (hC : CE R R' C) : ∀ (ts : List Expr),
    (∀ x ∈ sitesDl R C ts, x.Agrees R') → (∀ l ∈ olabelsEs R ts, NB R' l) →
    ∀ j ∈ itemsEs C ts, Gd R R' (p1Es R ts) j
  | [], _, _ => by simp [itemsEs]
  | t :: ts, hs, ho => by
    simp only [sitesDl, olabelsEs, List.forall_mem_append] at hs ho
    have ih1 := ceD C hC t hs.1 ho.1
    have ih2 := ceDl C hC ts hs.2 ho.2
    cjn
end

set_option hygiene false in
/-- A site statement: the nodes of all its items are in part (1). -/
macro "siteS" : tactic => `(tactic| exact SG.of_sim (trS_items C _) (fun j hj => .inl (by
  simp only [p1S, p1Site, Stmt.label, hR, Option.isSome_some, ite_true]; exact labS _ C j hj))
  (pitemsS_sub _ _ _))

set_option hygiene false in
/-- A statement with no block: (T1) gives the preimage, the children's facts its chain equation. -/
macro "sj" : tactic => `(tactic| exact SG.of_sim (trS_items C _) (by
  intro j hj
  have hC0 : ∀ l x, ChainEq R R' (.occ l x C) := fun _ _ => hC
  simp only [itemsS, itemsO, p1S, p1Site, p1O, Stmt.label, hR, Option.isSome_none,
    Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons, List.mem_map] at hj ⊢
  simp only [Gd, List.mem_append] at *
  grind) (pitemsS_sub _ _ _))

set_option hygiene false in
/-- Close a statement with blocks from the facts about its parts. -/
syntax "sgc" "[" Lean.Parser.Tactic.simpLemma,* "]" (ppSpace colGt term:max)+ : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sgc [$ls,*] $ps*) => `(tactic|
    exact SG.cover (sgcat $ps*)
      (by
        intro i hi
        simp (disch := omega) only [trS, trHs, trChain, trScope, blk, forLoop, PyCore.itemsS,
          PyCore.itemsB, PyCore.itemsE, PyCore.itemsHs, pitemsB_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.nil_append, Option.isSome_none, Bool.false_eq_true, ite_false,
          or_false, false_or, hl.1, hl.2.1, hl.2.2, pitemsE_ccR_nb _ hl, cc, gad, nm, pitemsE_paramMarkR,
          pitemsE_starMarkR, pitemsE_kwMarkR, List.flatMap_map, flatMap_nil_fun, Function.comp_def,
          $ls,*] at hi ⊢
        grind [freshItem_fresh])
      (by
        intro j hj
        simp only [itemsS, itemsHs, itemsO, List.mem_append, List.mem_cons, List.not_mem_nil,
          List.append_nil, List.nil_append, or_false, false_or] at hj ⊢
        grind)
      (by
        intro x hx
        simp only [p1S, p1Site, p1Hs, p1O, Stmt.label, hR, Option.isSome_none, Bool.false_eq_true,
          ite_false, List.mem_append, List.not_mem_nil, List.append_nil, List.nil_append, or_false,
          false_or] at hx ⊢
        grind))

end


theorem annK_mem (R : Edit) (C : List Scope) (x : PSite) : ∀ ps : List Param,
    x ∈ sitesAnnK R C .pos ps ++ sitesAnnK R C .posonly ps ++ sitesAnnK R C .vararg ps ++
      sitesAnnK R C .kwonly ps ++ sitesAnnK R C .kwarg ps ↔ x ∈ sitesAn R C ps
  | [] => by simp [sitesAnnK, sitesAn]
  | .mk _ _ k _ none :: ps => by simpa [sitesAnnK, sitesAn, sitesO] using annK_mem R C x ps
  | .mk _ _ k _ (some a) :: ps => by
    have ih := annK_mem R C x ps
    simp only [List.mem_append] at ih
    cases k <;> simp [sitesAnnK, sitesAn, sitesO, List.mem_append] <;> grind

section
variable {R : Edit} {R' : PyCore.Edit}
variable (hk : KeepsLabels R)
include hk

mutual
theorem ceS (C : List Scope) (hC : CE R R' C) : ∀ s, regS R C s = true →
    (∀ x ∈ sitesS R C s, x.Agrees R') → (∀ l ∈ olabelsS R C s, NB R' l) →
    SG R R' (PyCore.itemsS R' (trChain C) (trS C s)) (itemsS C s) (p1S R s)
  | .expr l e, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none => have ih1 := ceE hk C hC e fromSS fromOS; sj
  | .assign l ts e, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      have ih1 := ceE hk C hC e fromSS fromOS
      have h2 : ∀ ts, (∀ x ∈ sitesTs R C (nameSrc "t" l) ts, x.Agrees R') → (∀ y ∈ olabelsEs R ts, NB R' y) →
          ∀ j ∈ itemsEs C ts, Gd R R' (p1Es R ts) j := by
        intro ts; induction ts with
        | nil => simp [itemsEs]
        | cons t ts ih =>
          intro hs' ho'
          simp only [sitesTs, olabelsEs, List.forall_mem_append] at hs' ho'
          have hT := ceT hk C hC (nameSrc "t" l) t (fun h => ceE hk C hC t h ho'.1) hs'.1 ho'.1
          have hI := ih hs'.2 ho'.2
          intro j hj; simp only [itemsEs, p1Es, List.mem_append] at hj ⊢
          rcases hj with hj | hj
          · exact (hT j hj).mono (fun _ h => List.mem_append_left _ h)
          · exact (hI j hj).mono (fun _ h => List.mem_append_right _ h)
      have ih2 := h2 ts fromSS fromOS
      sj
  | .augassign l t op e, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      have ih1 := ceAug hk C hC l t fromSS fromOS
      have ih2 := ceE hk C hC e fromSS fromOS; sj
  | .annassign l t a v, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      cases v with
      | none =>
        have ih1 := ceE hk C hC a fromSS fromOS
        have ih2 := ceBare hk C hC t fromSS fromOS
        sj
      | some v =>
        have ih1 := ceE hk C hC a fromSS fromOS
        have ih2 := ceT hk C hC (nameSrc "t" l) t (fun h => ceE hk C hC t h fromOS) fromSS fromOS
        have ih3 := ceE hk C hC v fromSS fromOS
        sj
  | .del l ts, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none => have ih1 := ceDl hk C hC ts fromSS fromOS; sj
  | .brk l, _, _, _ | .cont l, _, _, _ | .pass l, _, _, _ => by
    intro i hi; simp [trS, PyCore.itemsS, PyCore.itemsE] at hi
  | .glob l xs, hr, hs, ho | .nonloc l xs, hr, hs, ho | .imp l xs, hr, hs, ho
  | .impFrom l _ xs _, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none => sj
  | .ret l e, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none => have ih1 := ceO hk C hC e fromSS fromOS; sj
  | .raise l e c, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      have ih1 := ceO hk C hC e fromSS fromOS
      have ih2 := ceO hk C hC c fromSS fromOS; sj
  | .assert l t m, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      have ih1 := ceE hk C hC t fromSS fromOS
      have ih2 := ceO hk C hC m fromSS fromOS; sj
  | .ite l c t u, hr, hs, ho | .while l c t u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have h1 := sgE hk C c hC fromSS fromOS
      have h2 := ceB C hC t hr.1 fromSS fromOS
      have h3 := ceB C hC u hr.2 fromSS fromOS
      sgc [] h1 h2 h3
  | .for l t it b u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have h1 := sgE hk C it hC fromSS fromOS
      have h2 := sgT hk C (forSrc l) (srcIt_for l) t hC fromSS fromOS
      have h3 := ceB C hC b hr.1 fromSS fromOS
      have h4 := ceB C hC u hr.2 fromSS fromOS
      sgc [] h1 h2 h3 h4
  | .tryE l b hz u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have h1 := ceB C hC b hr.1.1 fromSS fromOS
      have h2 := ceHs C hC hz hr.1.2 fromSS fromOS
      have h3 := ceB C hC u hr.2 fromSS fromOS
      sgc [] h1 h2 h3
  | .defn l f ps b ds r, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
    cases hq : qualCh R C f with
    | true =>
      have hx := hs (.s (sub l 0) (trB (editChain R C) (editS R (.defn l f ps b ds r))))
        (by simp [sitesS, stmtSite, Stmt.label, hR, hq])
      simp only [PSite.Agrees] at hx
      intro i hi; simp [trS, PyCore.itemsS, hx] at hi
    | false =>
      simp only [sitesS, stmtSite, Stmt.label, hR, hq, Bool.false_eq_true, ite_false] at hs
      simp only [olabelsS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, List.append_nil] at ho
      have hl : NB R' l := ho l (by simp)
      simp only [regS, hR, Option.isSome_none, Bool.false_or] at hr
      have hC' : CE R R' (.fn l f ps b :: C) := CE.cons (scope_fn hk hr fromSS fromOS
        (fun q hq => ho _ (by simp [mem_olabelsPs R hq]))) hC
      have h1 := sgEs hk C ds hC fromSS fromOS
      have hps : Sim ((trDfs C ps ++ (trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++
          trAnnK C .kwonly ps ++ trAnnK C .kwarg ps)).flatMap (PyCore.itemsE R0 (trChain C))) (itemsPs C ps) :=
        Sim.congr (trPs_items C ps) (fun i => by
            have := flatMap_mem_iff (f := PyCore.itemsE R0 (trChain C)) (trAnnK_all C · ps) i
            simp only [List.flatMap_append, List.mem_append] at *; grind)
          (fun _ => Iff.rfl)
      have h2 : SG R R' ((trDfs C ps ++ (trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++
          trAnnK C .kwonly ps ++ trAnnK C .kwarg ps)).flatMap (PyCore.itemsE R' (trChain C))) (itemsPs C ps)
          (p1Ps R ps) :=
        SG.of_sim hps (cePs hk C hC ps (fun x hx => hs x (by
            have := annK_mem R C x ps
            simp only [List.mem_append] at hx this ⊢; grind)) fromOS)
          (fun i hi => by
            simp only [List.mem_flatMap] at hi ⊢; obtain ⟨e, he, hi⟩ := hi; exact ⟨e, he, pitemsE_sub _ _ _ i hi⟩)
      have h3 := sgO hk C l 1 r hC fromSS fromOS
      have h4 := SG.oc (R := R) (R' := R') (P := []) l 0 (mangle (priv C) f) hC
      have h5 := SG.fn1 (R := R) (R' := R') (P := []) l C (.fn l f ps b) hC'
      have h6 : SG R R' (PyCore.itemsB R' (trChain (.fn l f ps b :: C)) (paramBind (.fn l f ps b :: C) ps))
          (paramOccs (.fn l f ps b :: C) ps) [] :=
        SG.of_sim (sim_paramBind _ ps) (gd_paramOccs hC' ps) (pitemsB_sub _ _ _)
      have h7 := ceB (.fn l f ps b :: C) hC' b hr fromSS fromOS
      cases r with
      | none => sgc [trO, List.flatMap_append, pitemsB_append] h1 h2 h4 h5 h6 h7
      | some r => sgc [trO, List.flatMap_append, pitemsB_append] h1 h2 h3 h4 h5 h6 h7
  | .cls l x bs ks b ds, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteS
    | none =>
    cases hq : qualCh R C x with
    | true =>
      have hx := hs (.s (sub l 0) (trB (editChain R C) (editS R (.cls l x bs ks b ds))))
        (by simp [sitesS, stmtSite, Stmt.label, hR, hq])
      simp only [PSite.Agrees] at hx
      intro i hi; simp [trS, blk, PyCore.itemsS, hx] at hi
    | false =>
      simp only [sitesS, stmtSite, Stmt.label, hR, hq, Bool.false_eq_true, ite_false] at hs
      simp only [olabelsS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, List.append_nil] at ho
      have hl : NB R' l := ho l (by simp)
      simp only [regS, hR, Option.isSome_none, Bool.false_or] at hr
      have hC' : CE R R' (.cl l x b :: C) := CE.cons (scope_cl hk hl hr fromSS fromOS) hC
      have h1 := sgEs hk C ds hC fromSS fromOS
      have h2 := sgA hk C bs hC fromSS fromOS
      have h3 := sgKs hk C ks hC fromSS fromOS
      have h4 := SG.oc (R := R) (R' := R') (P := []) l 1 (mangle (priv C) x) hC
      have h5 := sg_implicit (R := R) (R' := R') (P := []) l C (.cl l x b) hC'
      have h6 := ceB (.cl l x b :: C) hC' b hr fromSS fromOS
      sgc [setupS, pitemsB_append, List.flatMap_append] h1 h2 h3 h4 h5 h6
theorem ceHs (C : List Scope) (hC : CE R R' C) : ∀ hz, regHs R C hz = true →
    (∀ x ∈ sitesHs R C hz, x.Agrees R') → (∀ l ∈ olabelsHs R C hz, NB R' l) →
    SG R R' (PyCore.itemsHs R' (trChain C) (trHs C hz)) (itemsHs C hz) (p1Hs R hz)
  | [], _, _, _ => by intro i hi; simp [trHs, PyCore.itemsHs] at hi
  | .mk l ty x b :: hz, hr, hs, ho => by
    simp only [regHs, Bool.and_eq_true] at hr
    have ih := ceHs C hC hz hr.2 (fun y hy => hs y (by simp [sitesHs, hy]))
      (fun y hy => ho y (by simp [olabelsHs, hy]))
    cases hR : R.h l with
    | some h' =>
      have hx := hs
      cases h' with
      | mk l' ty' x' b' =>
        simp only [sitesHs, hR, trHs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.forall_mem_cons, PSite.Agrees] at hx
        exact SG.cover ih (by intro i hi; simp [trHs, PyCore.itemsHs, hx.1] at hi ⊢; exact .inl hi)
          (by intro j hj; simp [itemsHs, hj]) (by intro y hy; simp [p1Hs, hy])
    | none =>
      have hl : NB R' l := ho l (by simp [olabelsHs, ocut, hR])
      have h2 := ceB C hC b (by simpa [hR] using hr.1) (fun y hy => hs y (by simp [sitesHs, hR, hy]))
        (fun y hy => ho y (by simp [olabelsHs, ocut, hR, hy]))
      have hxs : SG R R' [.occ (sub l 0) ((x.map (mangle (priv C))).getD (fresh "e" l)) (trChain C)]
          (x.map fun x => Item.occ l (mangle (priv C) x) C).toList [] := by
        cases x with
        | none => intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact .inl (freshItem_fresh ..)
        | some x => exact SG.oc l 0 _ hC
      cases ty with
      | none => sgc [] h2 hxs ih
      | some t =>
        have h1 := sgE hk C t hC (fun y hy => hs y (by simp [sitesHs, sitesO, hR, hy]))
          (fun y hy => ho y (by simp [olabelsHs, olabelsO, ocut, hR, hy]))
        sgc [] h1 h2 hxs ih
theorem ceB (C : List Scope) (hC : CE R R' C) : ∀ ss, regB R C ss = true →
    (∀ x ∈ sitesB R C ss, x.Agrees R') → (∀ l ∈ olabelsB R C ss, NB R' l) →
    SG R R' (PyCore.itemsB R' (trChain C) (trB C ss)) (itemsB C ss) (p1B R ss)
  | [], _, _, _ => by intro i hi; simp [trB, PyCore.itemsB] at hi
  | s :: ss, hr, hs, ho => by
    simp only [regB, Bool.and_eq_true] at hr
    simp only [sitesB, olabelsB, List.forall_mem_append] at hs ho
    exact SG.app (ceS C hC s hr.1 hs.1 ho.1) (ceB C hC ss hr.2 hs.2 ho.2)
end

end

/-- (T1) for edits, soundness: every item of ⌊p⌋ outside the PyCore sites of `trEdit R p` is
fresh, or the image of an item of `p` in part (1) or whose chain satisfies the chain
equation. This is the premise `hT` of `flagged_image_of`. -/
theorem trB_itemsR (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p)
    (hk : KeepsLabels R) (hr : regB R [] p = true) :
    ∀ i ∈ PyCore.itemsB (trEdit R p) [] (tr p), FreshItem i ∨
      ∃ j ∈ itemsB [] p, Img j i ∧ (j.lab ∈ p1B R p ∨ ChainEq R (trEdit R p) j) := by
  obtain ⟨hag, hn2, hn0⟩ := trEdit_ok R p hp h0 hr
  have := ceB hk [] rfl p hr hag hn2
  intro i hi
  have hi' : i ∈ PyCore.itemsB (trEdit R p) (trChain []) (trB [] p) := by
    simpa [tr, PyCore.itemsB, setupS, PyCore.itemsS, PyCore.itemsE, hn0.2.1 4 (by omega), gad, cc,
      pitemsE_ccR_nb _ hn0, trChain] using hi
  exact this i hi'

/-- Parts (2) and (3) of the image inclusion, given only the fresh names (`hF`). -/
theorem flagged_image_fresh (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p)
    (hd : NoDot p) (hg : GenOk p) (hk : KeepsLabels R) (hr : regB R [] p = true)
    (hF : ∀ i ∈ PyCore.itemsB (trEdit R p) [] (tr p), FreshItem i → i.bad (trEdit R p) = true →
      imgF R p i.label) :
    ∀ x ∈ PyCore.flagged (trEdit R p) (tr p), imgF R p x :=
  flagged_image_of R p hp hd hg (trB_itemsR R p hp h0 hk hr) hF

end Surf
