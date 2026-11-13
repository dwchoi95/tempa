/-
The image of the footprint: the smaller PyCore footprint of `PyCore.footprint_theorem_min`
for `trEdit R p` on ⌊p⌋ lies in the image of F_surf(p, q) under `l ↦ sub l k`.

Part (1), the site roots (`roots_image`): each root of a PyCore site is made for a node
of a Surf site (part (1)) or for the outermost `def` or class node whose qualified name
changes (`qcB`), which is an occurrence of its name classified differently (part (2),
`qcB_occ`). Parts (2) and (3), the flagged items (`flagged_image_of`), from (T1) for edits
and the fresh names, which are its premises.
-/
import Surf.Commute

set_option linter.unusedSectionVars false

namespace Surf
open PyCore (Name Label)

/-- Membership in F_surf(p, q); part (3) makes it every node of `p`. -/
def inF (R : Edit) (p : List Stmt) (l : Label) : Prop :=
  match footprint? R p with
  | some L => l ∈ L
  | none => l ∈ labelsB p

/-- The image of F_surf(p, q) under `l ↦ sub l k`: the nodes the translation makes for
nodes of F_surf(p, q). -/
def imgF (R : Edit) (p : List Stmt) (x : Label) : Prop := ∃ l k, x = sub l k ∧ k < 64 ∧ inF R p l

/-! ## PyCore: the roots are sites -/

/-- `R` replaces the node `l`. -/
def PSiteAt (R : PyCore.Edit) (l : Label) : Prop :=
  (R.e l).isSome ∨ (R.s l).isSome ∨ (R.h l).isSome

mutual
theorem rootsE_at (R : PyCore.Edit) : ∀ (e : PyCore.Expr) (l : Label), l ∈ PyCore.rootsE R e → PSiteAt R l
  | .const l' _, l, h | .name l' _ _, l, h => by
    simp only [PyCore.rootsE] at h; split at h <;> simp_all [PSiteAt]
  | .bin l' _ a b, l, h | .call l' a b, l, h | .bool l' _ a b, l, h => by
    simp only [PyCore.rootsE] at h; split at h
    · simp_all [PSiteAt]
    · rcases List.mem_append.mp h with h | h
      · exact rootsE_at R a l h
      · exact rootsE_at R b l h
  | .lam l' _ _ b, l, h => by
    simp only [PyCore.rootsE] at h; split at h
    · simp_all [PSiteAt]
    · exact rootsB_at R b l h
  | .walrus l' _ b, l, h | .yield l' b, l, h | .yieldFrom l' b, l, h => by
    simp only [PyCore.rootsE] at h; split at h
    · simp_all [PSiteAt]
    · exact rootsE_at R b l h
  | .cond l' c a b, l, h => by
    simp only [PyCore.rootsE] at h; split at h
    · simp_all [PSiteAt]
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact rootsE_at R c l h
        · exact rootsE_at R a l h
      · exact rootsE_at R b l h
theorem rootsS_at (R : PyCore.Edit) : ∀ (s : PyCore.Stmt) (l : Label), l ∈ PyCore.rootsS R s → PSiteAt R l
  | .assign l' _ e, l, h | .expr l' e, l, h | .ret l' e, l, h | .raise l' e, l, h | .print l' e, l, h => by
    simp only [PyCore.rootsS] at h; split at h
    · simp_all [PSiteAt]
    · exact rootsE_at R e l h
  | .del l' _, l, h | .glob l' _, l, h | .nonloc l' _, l, h | .brk l', l, h | .cont l', l, h => by
    simp only [PyCore.rootsS] at h; split at h <;> simp_all [PSiteAt]
  | .ite l' c t u, l, h | .while l' c t u, l, h => by
    simp only [PyCore.rootsS] at h; split at h
    · simp_all [PSiteAt]
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact rootsE_at R c l h
        · exact rootsB_at R t l h
      · exact rootsB_at R u l h
  | .defn l' _ _ b, l, h | .cls l' _ _ b, l, h => by
    simp only [PyCore.rootsS] at h; split at h
    · simp_all [PSiteAt]
    · exact rootsB_at R b l h
  | .tryE l' b hs u, l, h => by
    simp only [PyCore.rootsS] at h; split at h
    · simp_all [PSiteAt]
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact rootsB_at R b l h
        · exact rootsHs_at R hs l h
      · exact rootsB_at R u l h
theorem rootsHs_at (R : PyCore.Edit) : ∀ (hs : List PyCore.Handler) (l : Label), l ∈ PyCore.rootsHs R hs → PSiteAt R l
  | [], _, h => by simp [PyCore.rootsHs] at h
  | .mk lh e _ hb :: hs, l, h => by
    simp only [PyCore.rootsHs] at h
    rcases List.mem_append.mp h with h | h
    · split at h
      · simp_all [PSiteAt]
      · rcases List.mem_append.mp h with h | h
        · exact rootsE_at R e l h
        · exact rootsB_at R hb l h
    · exact rootsHs_at R hs l h
theorem rootsB_at (R : PyCore.Edit) : ∀ (ss : List PyCore.Stmt) (l : Label), l ∈ PyCore.rootsB R ss → PSiteAt R l
  | [], _, h => by simp [PyCore.rootsB] at h
  | s :: ss, l, h => by
    simp only [PyCore.rootsB] at h
    rcases List.mem_append.mp h with h | h
    · exact rootsS_at R s l h
    · exact rootsB_at R ss l h
end

/-- Where `trEdit R p` replaces a node, a site of `sitesB R [] p` is rooted. -/
theorem trEdit_at (R : Edit) (p : List Stmt) (L : Label) (h : PSiteAt (trEdit R p) L) :
    ∃ x ∈ sitesB R [] p, x.root = L := by
  by_cases hn : ∃ x ∈ sitesB R [] p, x.root = L
  · exact hn
  · have hL : ∀ x ∈ sitesB R [] p, x.root ≠ L := fun x hx he => hn ⟨x, hx, he⟩
    obtain ⟨h1, h2, h3⟩ := trEdit_none R p L hL
    simp [PSiteAt, h1, h2, h3] at h

/-! ## Classes whose qualified name changes are in part (2) -/

/-- The chain of a statement keeps its qualified prefix: its head is a `def` or a class (or
the chain is the module's) whose own qualified name the edit keeps. -/
def QualOk (R : Edit) : List Scope → Prop
  | [] => True
  | S :: C => ∃ n, S.qualPart = some n ∧ qualIn (editChain R C) n = qualIn C n

theorem qualPart_edit (R : Edit) (S : Scope) : (editSc R S).qualPart = S.qualPart := by
  cases S with
  | comp l k _ _ => cases k <;> rfl
  | _ => rfl

/-- A `def` or class outside the sites that keeps its qualified name gives its body a
prefix that the edit keeps. -/
theorem qualOk_fn {R : Edit} {C : List Scope} {l : Label} {f : Name} {ps : List Param}
    {b : List Stmt} (hq : qualCh R C f = false) : QualOk R (.fn l f ps b :: C) :=
  ⟨f, rfl, by simpa [qualCh] using hq⟩

theorem qualOk_cl {R : Edit} {C : List Scope} {l : Label} {x : Name} {b : List Stmt}
    (hq : qualCh R C x = false) : QualOk R (.cl l x b :: C) :=
  ⟨x, rfl, by simpa [qualCh] using hq⟩

theorem isComp_edit (R : Edit) (S : Scope) : (editSc R S).isComp = S.isComp := by
  cases S <;> rfl

theorem sfactsB_append (p : Option Name) : ∀ a b : List Stmt, factsB p (a ++ b) = factsB p a ++ factsB p b
  | [], _ => rfl
  | s :: a, b => by simp [factsB, sfactsB_append p a b]

/-- The facts `A` (of `p`) and `B` (of `q`) are in the own bodies of the scope at the
head of `C` and of its image in `q`, a function or class scope. -/
def Owns (R : Edit) (C : List Scope) (A B : List PyCore.Fact) : Prop :=
  match C with
  | [] => True
  | S :: C' => S.isComp = false ∧ (∀ f ∈ A, f ∈ S.facts C') ∧
      (∀ f ∈ B, f ∈ (editSc R S).facts (editChain R C'))

theorem Owns.mono {R : Edit} {C : List Scope} {A B A' B' : List PyCore.Fact} (h : Owns R C A B)
    (hA : ∀ f ∈ A', f ∈ A) (hB : ∀ f ∈ B', f ∈ B) : Owns R C A' B' := by
  cases C with
  | nil => trivial
  | cons S C' => exact ⟨h.1, fun f hf => h.2.1 f (hA f hf), fun f hf => h.2.2 f (hB f hf)⟩

/-- With the prefix kept, the qualified name of `x` changes only with its `global` declaration
in the scope around. -/
theorem qual_same {R : Edit} {S : Scope} {C' : List Scope} {x : Name} (hP : QualOk R (S :: C'))
    (heq : (editSc R S).declG (editChain R C') (mangle (priv (S :: C')) x) =
      S.declG C' (mangle (priv (S :: C')) x)) : qualCh R (S :: C') x = false := by
  obtain ⟨n, hn, hpre⟩ := hP
  have hpe : priv (editSc R S :: editChain R C') = priv (S :: C') := priv_edit R (S :: C')
  simp only [qualCh, bne_eq_false_iff_eq, editChain_cons]
  rw [← hpe] at heq
  cases S with
  | fn l f ps b => simp_all [qualIn, editSc, Scope.qualPart]
  | lam l ps b => simp_all [qualIn, editSc, Scope.qualPart]
  | cl l y b => simp_all [qualIn, editSc, Scope.qualPart]
  | comp l k es gs => cases k <;> simp_all [qualIn, editSc, Scope.qualPart]

/-- A `def` or class whose qualified name changes is classified differently in the scope
around: its name's `global` declaration there changed. -/
theorem qual_alike {R : Edit} {C : List Scope} {x : Name} (hq : qualCh R C x = true) (hP : QualOk R C)
    (ho : Owns R C [PyCore.Fact.bind (mangle (priv C) x)] [PyCore.Fact.bind (mangle (priv C) x)]) :
    alike R C (mangle (priv C) x) = false := by
  cases C with
  | nil => simp [qualCh, qualIn, editChain] at hq
  | cons S C' =>
    obtain ⟨hc, h1, h2⟩ := ho
    have hb1 := h1 _ (List.mem_singleton_self _)
    have hb2 := h2 _ (List.mem_singleton_self _)
    have hpe : priv (editSc R S :: editChain R C') = priv (S :: C') := priv_edit R (S :: C')
    have hc2 : (editSc R S).isComp = false := by rw [isComp_edit]; exact hc
    simp only [alike, clsOf, editChain_cons, Scope.walrus, Scope.binds, hc, hc2, Bool.false_and,
      Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false, Bool.and_eq_false_iff,
      List.contains_iff_mem.mpr hb1, List.contains_iff_mem.mpr hb2, Bool.true_or, ite_true]
    left
    cases hd1 : S.declG C' (mangle (priv (S :: C')) x) <;>
      cases hd2 : (editSc R S).declG (editChain R C') (mangle (priv (S :: C')) x)
    · rw [qual_same hP (by rw [hd1, hd2])] at hq; cases hq
    · simp only [ite_true, ite_false, Bool.false_eq_true]; split <;> simp
    · simp only [ite_true, ite_false, Bool.false_eq_true]; split <;> simp
    · rw [qual_same hP (by rw [hd1, hd2])] at hq; cases hq

set_option hygiene false in
macro "ownsB" : tactic => `(tactic| exact Owns.mono ho (fun f hf => by
  simp [factsS, factsB, factsHs, sfactsB_append, hf]) (fun f hf => by
  simp [editS, editB, editHs, hR, factsS, factsB, factsHs, sfactsB_append, hf]))

mutual
theorem qcS_occ (R : Edit) (C : List Scope) (hP : QualOk R C) :
    ∀ s, Owns R C (factsS (priv C) s) (factsB (priv C) (editS R s)) →
    ∀ l ∈ qcS R C s, ∃ y C0, Item.occ l y C0 ∈ itemsS C s ∧ alike R C0 y = false
  | .ite l' c t u, ho, l, hl | .while l' c t u, ho, l, hl => by
    cases hR : R.s l' with
    | some _ => simp [qcS, hR] at hl
    | none =>
      simp only [qcS, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append] at hl
      rcases hl with hl | hl
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP t (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP u (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
  | .for l' tg it t u, ho, l, hl => by
    cases hR : R.s l' with
    | some _ => simp [qcS, hR] at hl
    | none =>
      simp only [qcS, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append] at hl
      rcases hl with hl | hl
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP t (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP u (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
  | .defn l' f ps b ds r, ho, l, hl => by
    cases hR : R.s l' with
    | some _ => simp [qcS, hR] at hl
    | none =>
      cases hq : qualCh R C f with
      | true =>
        simp only [qcS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true,
          List.mem_singleton] at hl; subst hl
        refine ⟨_, C, by simp [itemsS], qual_alike hq hP (Owns.mono ho (fun f hf => ?_) (fun f hf => ?_))⟩
        · simp at hf; simp [factsS, hf]
        · simp at hf; simp [editS, hR, factsB, factsS, hf]
      | false =>
        simp only [qcS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false] at hl
        obtain ⟨y, C0, h1, h2⟩ := qcB_occ R (.fn l' f ps b :: C) (qualOk_fn hq) b ⟨rfl, fun f hf => by
          simp [Scope.facts, hf], fun f hf => by simp [Scope.facts, editSc, priv] at hf ⊢; simp [hf]⟩ l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
  | .cls l' x bs ks b ds, ho, l, hl => by
    cases hR : R.s l' with
    | some _ => simp [qcS, hR] at hl
    | none =>
      cases hq : qualCh R C x with
      | true =>
        simp only [qcS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true,
          List.mem_singleton] at hl; subst hl
        refine ⟨_, C, by simp [itemsS], qual_alike hq hP (Owns.mono ho (fun f hf => ?_) (fun f hf => ?_))⟩
        · simp at hf; simp [factsS, hf]
        · simp at hf; simp [editS, hR, factsB, factsS, hf]
      | false =>
        simp only [qcS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false] at hl
        obtain ⟨y, C0, h1, h2⟩ := qcB_occ R (.cl l' x b :: C) (qualOk_cl hq) b ⟨rfl, fun f hf => by
          simp [Scope.facts, hf], fun f hf => by simp [Scope.facts, editSc, priv] at hf ⊢; simp [hf]⟩ l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
  | .tryE l' b hs u, ho, l, hl => by
    cases hR : R.s l' with
    | some _ => simp [qcS, hR] at hl
    | none =>
      simp only [qcS, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP b (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
      · obtain ⟨y, C0, h1, h2⟩ := qcHs_occ R C hP hs (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
      · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP u (by ownsB) l hl
        exact ⟨y, C0, by simp [itemsS, h1], h2⟩
  | .expr .., _, l, hl | .assign .., _, l, hl | .augassign .., _, l, hl | .annassign .., _, l, hl
  | .del .., _, l, hl | .brk .., _, l, hl | .cont .., _, l, hl | .pass .., _, l, hl | .ret .., _, l, hl
  | .glob .., _, l, hl | .nonloc .., _, l, hl | .raise .., _, l, hl | .imp .., _, l, hl
  | .impFrom .., _, l, hl | .assert .., _, l, hl => by simp [qcS] at hl
theorem qcHs_occ (R : Edit) (C : List Scope) (hP : QualOk R C) : ∀ hs,
    Owns R C (factsHs (priv C) hs) (factsHs (priv C) (editHs R hs)) →
    ∀ l ∈ qcHs R C hs, ∃ y C0, Item.occ l y C0 ∈ itemsHs C hs ∧ alike R C0 y = false
  | [], _, l, hl => by simp [qcHs] at hl
  | .mk l' ty x b :: hs, ho, l, hl => by
    simp only [qcHs, List.mem_append] at hl
    rcases hl with hl | hl
    · cases hR : R.h l' with
      | some _ => simp [hR] at hl
      | none =>
        simp only [hR, Option.isSome_none, Bool.false_eq_true, ite_false] at hl
        obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP b (Owns.mono ho (fun f hf => by simp [factsHs, hf])
          (fun f hf => by simp [editHs, hR, factsHs, hf])) l hl
        exact ⟨y, C0, by simp [itemsHs, h1], h2⟩
    · obtain ⟨y, C0, h1, h2⟩ := qcHs_occ R C hP hs (Owns.mono ho (fun f hf => by simp [factsHs, hf])
        (fun f hf => by
          simp only [editHs]; generalize (R.h l').getD _ = h0; cases h0; simp [factsHs, hf])) l hl
      exact ⟨y, C0, by simp [itemsHs, h1], h2⟩
theorem qcB_occ (R : Edit) (C : List Scope) (hP : QualOk R C) : ∀ ss,
    Owns R C (factsB (priv C) ss) (factsB (priv C) (editB R ss)) →
    ∀ l ∈ qcB R C ss, ∃ y C0, Item.occ l y C0 ∈ itemsB C ss ∧ alike R C0 y = false
  | [], _, l, hl => by simp [qcB] at hl
  | s :: ss, ho, l, hl => by
    simp only [qcB, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨y, C0, h1, h2⟩ := qcS_occ R C hP s (Owns.mono ho (fun f hf => by simp [factsB, hf])
        (fun f hf => by simp [editB, sfactsB_append, hf])) l hl
      exact ⟨y, C0, by simp [itemsB, h1], h2⟩
    · obtain ⟨y, C0, h1, h2⟩ := qcB_occ R C hP ss (Owns.mono ho (fun f hf => by simp [factsB, hf])
        (fun f hf => by simp [editB, sfactsB_append, hf])) l hl
      exact ⟨y, C0, by simp [itemsB, h1], h2⟩
end

/-! ## Part (1): the site roots -/

/-- A node of part (1) or of `qcB` is in F_surf(p, q). -/
theorem inF_of (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (l : Label)
    (hl : l ∈ p1B R p ++ qcB R [] p) : inF R p l := by
  have hc := cnt_le R p hp l
  have hlab : l ∈ labelsB p := by
    have := cntB R l [] p
    rcases List.mem_append.mp hl with h | h <;> have := List.count_pos_iff.mpr h <;>
      exact List.count_pos_iff.mp (by omega)
  unfold inF footprint?
  split
  · rename_i L hL
    split at hL
    · simp only [Option.some.injEq] at hL; subst hL
      rcases List.mem_append.mp hl with h | h
      · exact List.mem_append_left _ h
      · refine List.mem_append_right _ ?_
        obtain ⟨y, C0, h1, h2⟩ := qcB_occ R [] trivial p trivial l h
        have hn : l ∉ p1B R p := fun h' => by
          have := List.count_pos_iff.mpr h; have := List.count_pos_iff.mpr h'; omega
        exact List.mem_filterMap.mpr ⟨_, h1, by simp [hn, h2]⟩
    · simp at hL
  · exact hlab

/-- Part (1) of the image: every root of a PyCore site of `trEdit R p` is made for a node
of F_surf(p, q). -/
theorem roots_image (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (hr : regB R [] p = true) :
    ∀ x ∈ PyCore.rootsB (trEdit R p) (tr p), imgF R p x := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := trEdit_at R p x (rootsB_at _ _ x hx)
  obtain ⟨l', hl', k, hk, h⟩ := sites_root R p hr y hy
  exact ⟨l', k, by rw [← hyx, h], hk, inF_of R p hp l' hl'⟩

/-! ## PyCore: the items outside the sites are items -/

set_option hygiene false in
macro "subI" : tactic => `(tactic| (split at h; simp at h; simp only [List.mem_append, List.mem_cons,
  enone_e, enone_s, enone_h, Option.isSome_none, Bool.false_eq_true, ite_false] at h ⊢))

mutual
/-- The items of a PyCore expression outside the sites of `R` are among all its items
(the first step of (T1) for edits: below the statement level, `trE_items` applies). -/
theorem pitemsE_sub (R : PyCore.Edit) (C : List PyCore.Scope) : ∀ (e : PyCore.Expr) (i : PyCore.Item),
    i ∈ PyCore.itemsE R C e → i ∈ PyCore.itemsE R0 C e
  | .const .., _, h => by simp [PyCore.itemsE] at h
  | .name .., i, h => by simp only [PyCore.itemsE] at h ⊢; subI; exact h
  | .bin _ _ a b, i, h | .call _ a b, i, h | .bool _ _ a b, i, h => by
    simp only [PyCore.itemsE] at h ⊢; subI
    exact h.imp (pitemsE_sub R C a i) (pitemsE_sub R C b i)
  | .lam _ _ _ b, i, h => by
    simp only [PyCore.itemsE] at h ⊢; subI
    exact h.imp id (Or.imp id (pitemsB_sub R _ b i))
  | .walrus _ _ e, i, h => by
    simp only [PyCore.itemsE] at h ⊢; subI; exact h.imp id (pitemsE_sub R C e i)
  | .yield _ e, i, h | .yieldFrom _ e, i, h => by
    simp only [PyCore.itemsE] at h ⊢; subI; exact pitemsE_sub R C e i h
  | .cond _ c a b, i, h => by
    simp only [PyCore.itemsE] at h ⊢; subI
    exact h.imp (Or.imp (pitemsE_sub R C c i) (pitemsE_sub R C a i)) (pitemsE_sub R C b i)
theorem pitemsS_sub (R : PyCore.Edit) (C : List PyCore.Scope) : ∀ (s : PyCore.Stmt) (i : PyCore.Item),
    i ∈ PyCore.itemsS R C s → i ∈ PyCore.itemsS R0 C s
  | .assign .., i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI; exact h.imp id (pitemsE_sub R C _ i)
  | .del .., i, h | .glob .., i, h | .nonloc .., i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI; exact h
  | .expr _ e, i, h | .ret _ e, i, h | .raise _ e, i, h | .print _ e, i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI; exact pitemsE_sub R C e i h
  | .ite _ c t u, i, h | .while _ c t u, i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI
    exact h.imp (Or.imp (pitemsE_sub R C c i) (pitemsB_sub R C t i)) (pitemsB_sub R C u i)
  | .defn _ _ _ b, i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI
    exact h.imp id (Or.imp id (Or.imp id (pitemsB_sub R _ b i)))
  | .cls _ _ _ b, i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI
    exact h.imp id (pitemsB_sub R _ b i)
  | .tryE _ b hs u, i, h => by
    simp only [PyCore.itemsS] at h ⊢; subI
    exact h.imp (Or.imp (pitemsB_sub R C b i) (pitemsHs_sub R C hs i)) (pitemsB_sub R C u i)
  | .brk _, _, h | .cont _, _, h => by simp [PyCore.itemsS] at h
theorem pitemsHs_sub (R : PyCore.Edit) (C : List PyCore.Scope) : ∀ (hs : List PyCore.Handler) (i : PyCore.Item),
    i ∈ PyCore.itemsHs R C hs → i ∈ PyCore.itemsHs R0 C hs
  | [], _, h => by simp [PyCore.itemsHs] at h
  | .mk lh e _ hb :: hs, i, h => by
    simp only [PyCore.itemsHs, List.mem_append] at h ⊢
    rcases h with h | h
    · left; split at h
      · simp at h
      · simp only [List.mem_append, List.mem_cons, enone_h, Option.isSome_none, Bool.false_eq_true,
          ite_false] at h ⊢
        exact h.imp (pitemsE_sub R C e i) (Or.imp id (pitemsB_sub R C hb i))
    · exact .inr (pitemsHs_sub R C hs i h)
theorem pitemsB_sub (R : PyCore.Edit) (C : List PyCore.Scope) : ∀ (ss : List PyCore.Stmt) (i : PyCore.Item),
    i ∈ PyCore.itemsB R C ss → i ∈ PyCore.itemsB R0 C ss
  | [], _, h => by simp [PyCore.itemsB] at h
  | s :: ss, i, h => by
    simp only [PyCore.itemsB, List.mem_append] at h ⊢
    exact h.imp (pitemsS_sub R C s i) (pitemsB_sub R C ss i)
end

/-! ## The nodes of Surf items -/

/-- The node of a Surf item. -/
def Item.lab : Item → Label
  | .occ l _ _ | .fn l _ _ => l

theorem mem_labelsPs' {q : Param} : ∀ {ps : List Param}, q ∈ ps → q.label ∈ labelsPs ps
  | .mk .. :: ps, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [labelsPs, Param.label]
    · simp [labelsPs, mem_labelsPs' h]

set_option hygiene false in
macro "labC" : tactic => `(tactic| (
  simp only [itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, itemsS, itemsHs, itemsB,
    labelsE, labelsO, labelsEs, labelsKs, labelsDs, labelsPs, labelsGs, labelsS, labelsHs, labelsB,
    List.mem_append, List.mem_cons, List.mem_map, paramOccs, Option.map, Option.toList,
    List.mem_filter, bindingAliases, List.not_mem_nil, or_false] at hj ⊢
  repeat' (first | (obtain ⟨_, hq, rfl⟩ : ∃ _, _ ∧ _ = _ := hj) | (rcases hj with hj | hj))
  all_goals first
    | (simp [Item.lab]; done)
    | (subst hj; simp [Item.lab]; done)
    | (simp [Item.lab, mem_labelsPs' hq]; done)
    | (simp [Item.lab]; exact .inr ⟨_, hq.1, rfl⟩)
    | solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]))

mutual
theorem labE : ∀ (e : Expr) (C : List Scope) (j : Item), j ∈ itemsE C e → j.lab ∈ labelsE e
  | .const .., _, _, hj => by labC
  | .name .., _, _, hj => by labC
  | .bin _ _ a b, _, _, hj | .sub _ a b, _, _, hj => by have h1 := labE a; have h2 := labE b; labC
  | .unary _ _ a, _, _, hj | .attr _ a _, _, _, hj | .star _ a, _, _, hj | .yieldFrom _ a, _, _, hj => by
    have h1 := labE a; labC
  | .boolop _ _ es, _, _, hj | .set _ es, _, _, hj | .fstr _ es, _, _, hj | .list _ es, _, _, hj
  | .tuple _ es, _, _, hj => by have h1 := labEs es; labC
  | .compare _ a _ es, _, _, hj => by have h1 := labE a; have h2 := labEs es; labC
  | .ifexp _ c a b, _, _, hj => by have h1 := labE c; have h2 := labE a; have h3 := labE b; labC
  | .call _ f as ks, _, _, hj => by have h1 := labE f; have h2 := labEs as; have h3 := labKs ks; labC
  | .slice _ a b c, _, _, hj => by have h1 := labO a; have h2 := labO b; have h3 := labO c; labC
  | .dict _ kvs, _, _, hj => by have h1 := labDs kvs; labC
  | .lam _ ps b, _, _, hj => by have h1 := labPs ps; have h2 := labE b; labC
  | .comp _ _ es gs, _, _, hj => by have h1 := labEs es; have h2 := labG1 gs; have h3 := labGs gs; labC
  | .walrus _ _ a, _, _, hj => by have h1 := labE a; labC
  | .yield _ e, _, _, hj => by have h1 := labO e; labC
  | .fmt _ e _ s, _, _, hj => by have h1 := labE e; have h2 := labO s; labC
theorem labO : ∀ (o : Option Expr) (C : List Scope) (j : Item), j ∈ itemsO C o → j.lab ∈ labelsO o
  | none, _, _, hj => by labC
  | some e, _, _, hj => by have h1 := labE e; labC
theorem labEs : ∀ (es : List Expr) (C : List Scope) (j : Item), j ∈ itemsEs C es → j.lab ∈ labelsEs es
  | [], _, _, hj => by labC
  | e :: es, _, _, hj => by have h1 := labE e; have h2 := labEs es; labC
theorem labKs : ∀ (ks : List Kw) (C : List Scope) (j : Item), j ∈ itemsKs C ks → j.lab ∈ labelsKs ks
  | [], _, _, hj => by labC
  | .mk _ _ e :: ks, _, _, hj => by have h1 := labE e; have h2 := labKs ks; labC
theorem labDs : ∀ (kvs : List DItem) (C : List Scope) (j : Item), j ∈ itemsDs C kvs → j.lab ∈ labelsDs kvs
  | [], _, _, hj => by labC
  | .mk k v :: kvs, _, _, hj => by have h1 := labO k; have h2 := labE v; have h3 := labDs kvs; labC
theorem labPs : ∀ (ps : List Param) (C : List Scope) (j : Item), j ∈ itemsPs C ps → j.lab ∈ labelsPs ps
  | [], _, _, hj => by labC
  | .mk _ _ _ d a :: ps, _, _, hj => by have h1 := labO d; have h2 := labO a; have h3 := labPs ps; labC
theorem labG1 : ∀ (gs : List Gen) (C : List Scope) (j : Item), j ∈ itemsG1 C gs → j.lab ∈ labelsGs gs
  | [], _, _, hj => by labC
  | .mk _ _ i _ :: _, _, _, hj => by have h1 := labE i; labC
theorem labGs : ∀ (gs : List Gen) (C : List Scope) (f : Bool) (j : Item), j ∈ itemsGs C f gs → j.lab ∈ labelsGs gs
  | [], _, _, _, hj => by labC
  | .mk _ t i ifs :: gs, _, true, _, hj | .mk _ t i ifs :: gs, _, false, _, hj => by
    have h1 := labE t; have h2 := labE i; have h3 := labEs ifs; have h4 := labGs gs; labC
end

mutual
theorem labS : ∀ (s : Stmt) (C : List Scope) (j : Item), j ∈ itemsS C s → j.lab ∈ labelsS s
  | .expr _ e, _, _, hj => by have h1 := labE e; labC
  | .assign _ ts e, _, _, hj => by have h1 := labEs ts; have h2 := labE e; labC
  | .augassign _ t _ e, _, _, hj => by have h1 := labE t; have h2 := labE e; labC
  | .annassign _ t a v, _, _, hj => by have h1 := labE t; have h2 := labE a; have h3 := labO v; labC
  | .del _ ts, _, _, hj => by have h1 := labEs ts; labC
  | .ite _ c t u, _, _, hj | .while _ c t u, _, _, hj => by have h1 := labE c; have h2 := labB t; have h3 := labB u; labC
  | .for _ t it b u, _, _, hj => by
    have h1 := labE t; have h2 := labE it; have h3 := labB b; have h4 := labB u; labC
  | .brk .., _, _, hj | .cont .., _, _, hj | .pass .., _, _, hj => by labC
  | .ret _ e, _, _, hj => by have h1 := labO e; labC
  | .defn _ _ ps b ds r, _, _, hj => by have h1 := labPs ps; have h2 := labB b; have h3 := labEs ds; have h4 := labO r; labC
  | .cls _ _ bs ks b ds, _, _, hj => by have h1 := labEs bs; have h2 := labKs ks; have h3 := labB b; have h4 := labEs ds; labC
  | .glob .., _, _, hj | .nonloc .., _, _, hj => by labC
  | .tryE _ b hs u, _, _, hj => by have h1 := labB b; have h2 := labHs hs; have h3 := labB u; labC
  | .raise _ e c, _, _, hj => by have h1 := labO e; have h2 := labO c; labC
  | .imp .., _, _, hj | .impFrom .., _, _, hj => by labC
  | .assert _ t m, _, _, hj => by have h1 := labE t; have h2 := labO m; labC
theorem labHs : ∀ (hs : List Handler) (C : List Scope) (j : Item), j ∈ itemsHs C hs → j.lab ∈ labelsHs hs
  | [], _, _, hj => by labC
  | .mk _ ty none b :: hs, _, _, hj | .mk _ ty (some _) b :: hs, _, _, hj => by
    have h1 := labO ty; have h2 := labB b; have h3 := labHs hs; labC
theorem labB : ∀ (ss : List Stmt) (C : List Scope) (j : Item), j ∈ itemsB C ss → j.lab ∈ labelsB ss
  | [], _, _, hj => by labC
  | s :: ss, _, _, hj => by have h1 := labS s; have h2 := labB ss; labC
end

/-! ## Parts (2) and (3): the flagged items -/

/-- The chain of a Surf item (for a function, with its own scope) maps, under the PyCore
edit `R'`, to the image of its edited chain. -/
def ChainEq (R : Edit) (R' : PyCore.Edit) : Item → Prop
  | .occ _ _ C => (trChain C).map (PyCore.editSc R') = trChain (editChain R C)
  | .fn _ C S => (trChain (S :: C)).map (PyCore.editSc R') = trChain (editChain R (S :: C))

/-- With the chain equation, a name that is not fresh is classified alike in ⌊p⌋ and ⌊q⌋
exactly when it is in `p` and `q` (part (2)). -/
theorem alike_tr {R : Edit} {R' : PyCore.Edit} {x : Name} (hx : ¬ IsFresh x) : ∀ C : List Scope,
    (trChain C).map (PyCore.editSc R') = trChain (editChain R C) →
    PyCore.alike R' (trChain C) x = alike R C x
  | [], _ => rfl
  | S :: C, h => by
    have h' := h
    simp only [trChain, List.map_cons, editChain_cons, List.cons.injEq] at h'
    have e1 : PyCore.clsOf (trChain (S :: C)) x = clsOf (S :: C) x := cls_tr hx _
    have e2 : PyCore.clsOf (trChain (editChain R (S :: C))) x = clsOf (editChain R (S :: C)) x := cls_tr hx _
    show (PyCore.clsOf (trChain (S :: C)) x == PyCore.clsOf ((trChain (S :: C)).map (PyCore.editSc R')) x &&
      PyCore.alike R' (trChain C) x) = _
    rw [h, e1, e2, alike_tr hx C h'.2]; rfl

/-- With the chain equation, a function's kind changes in ⌊q⌋ exactly when it does in `q`
(part (3)). -/
theorem genOk_edit (R : Edit) (S : Scope) : (editSc R S).genOk = S.genOk := by
  cases S with
  | comp l k es gs => cases k <;> simp [editSc, Scope.genOk, editEs_length]
  | _ => rfl

theorem kind_edit_tr {R : Edit} {R' : PyCore.Edit} {l : Label} {C : List Scope} {S : Scope}
    (h : ChainEq R R' (.fn l C S)) (hS : S.genOk = true) :
    (PyCore.editSc R' (trScope C S)).kind = (editSc R S).kind (editChain R C) := by
  simp only [ChainEq, trChain, List.map_cons, editChain_cons, List.cons.injEq] at h
  rw [h.1, kind_tr _ _ (by rw [genOk_edit]; exact hS)]

/-- Parts (2) and (3) of the image, from (T1) for edits (`hT`: every item of ⌊p⌋ outside the
PyCore sites is fresh, or the image of an item of `p` in part (1) or whose chain satisfies
the chain equation) and from the fresh names (`hF`: a flagged occurrence of a fresh name is
in the image). -/
theorem flagged_image_of (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (hd : NoDot p) (hg : GenOk p)
    (hT : ∀ i ∈ PyCore.itemsB (trEdit R p) [] (tr p), FreshItem i ∨
      ∃ j ∈ itemsB [] p, Img j i ∧ (j.lab ∈ p1B R p ∨ ChainEq R (trEdit R p) j))
    (hF : ∀ i ∈ PyCore.itemsB (trEdit R p) [] (tr p), FreshItem i → i.bad (trEdit R p) = true →
      imgF R p i.label) :
    ∀ x ∈ PyCore.flagged (trEdit R p) (tr p), imgF R p x := by
  intro x hx
  simp only [PyCore.flagged, List.mem_filterMap] at hx
  obtain ⟨i, hi, hb⟩ := hx
  cases hbad : i.bad (trEdit R p) with
  | false => simp [hbad] at hb
  | true =>
    simp only [hbad, ite_true, Option.some.injEq] at hb; subst hb
    rcases hT i hi with hf | ⟨j, hj, hij, hg'⟩
    · exact hF i hi hf hbad
    · have hlab : j.lab ∈ labelsB p := labB p [] j hj
      have hin : inF R p j.lab := by
        by_cases hp1 : j.lab ∈ p1B R p
        · exact inF_of R p hp _ (List.mem_append_left _ hp1)
        have hgc : ChainEq R (trEdit R p) j := hg'.resolve_left hp1
        cases j with
        | occ l y C =>
          cases i with
          | fn => exact hij.elim
          | occ l' y' C' =>
            obtain ⟨-, rfl, rfl⟩ := hij
            have hy : ¬ IsFresh y' := fun h => hd l y' C hj (fresh_dot h)
            have ha : alike R C y' = false := by
              rw [← alike_tr hy C hgc]; simpa [PyCore.Item.bad] using hbad
            have h2 : l ∈ part2 R p := List.mem_filterMap.mpr ⟨_, hj, by
              simp only [Item.lab] at hp1; simp [hp1, ha, List.contains_iff_mem]⟩
            unfold inF footprint?
            split
            · rename_i L hL
              split at hL
              · simp only [Option.some.injEq] at hL; subst hL; exact List.mem_append_right _ h2
              · simp at hL
            · exact hlab
        | fn l C S =>
          cases i with
          | occ => exact hij.elim
          | fn l' S' =>
            obtain ⟨rfl, rfl⟩ := hij
            have hk : S.kind C != (editSc R S).kind (editChain R C) := by
              rw [← kind_tr C S (hg l C S hj), ← kind_edit_tr hgc (hg l C S hj)]
              simpa [PyCore.Item.bad] using hbad
            have h3 : l ∈ kindChanges R p := List.mem_filterMap.mpr ⟨_, hj, by
              simp only [Item.lab] at hp1; simp [hp1, List.contains_iff_mem] at hk ⊢; exact hk⟩
            unfold inF footprint?
            split
            · rename_i L hL
              split at hL
              · rename_i he; rw [he] at h3; simp at h3
              · simp at hL
            · exact hlab
      cases j with
      | occ l y C =>
        cases i with
        | fn => exact hij.elim
        | occ l' y' C' => obtain ⟨⟨k, hk, rfl⟩, -, -⟩ := hij; exact ⟨l, k, rfl, hk, hin⟩
      | fn l C S =>
        cases i with
        | occ => exact hij.elim
        | fn l' S' => obtain ⟨rfl, -⟩ := hij; exact ⟨l, 1, rfl, by omega, hin⟩

/-! ## Theorem 5 for ⌊p⌋ and ⌊q⌋ with the image of F_surf -/

/-- Theorem 5 composed with the translation: if ⌊p⌋'s run from `σ` evaluates no node
made for a node of F_surf(p, q), then ⌊p⌋ and ⌊q⌋ have the same outcomes. The site roots
are in that image by `roots_image`; `hflag` is the rest of the image inclusion (the
flagged occurrences and functions, parts (2) and (3)), which `flagged_image_canon` (`Fresh.lean`)
gives. -/
theorem footprint_theorem_surf_of {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option PyCore.Val) (s : S) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p) (hk : KeepsLabels R)
    (hr : regB R [] p = true) (hflag : ∀ x ∈ PyCore.flagged (trEdit R p) (tr p), imgF R p x)
    (h : PyCore.NoReach I (imgF R p) (PyCore.init (tr p) σ s)) :
    (∀ o, PyCore.Terminates I (PyCore.init (tr p) σ s) o ↔ PyCore.Terminates I (PyCore.init (tr (editB R p)) σ s) o) ∧
    (PyCore.Diverges I (PyCore.init (tr p) σ s) ↔ PyCore.Diverges I (PyCore.init (tr (editB R p)) σ s)) := by
  rw [tr_edit R p hp h0 hk hr]
  refine PyCore.footprint_theorem_min I _ _ σ s fun n l hl hF => ?_
  rcases hF with hF | hF
  · exact h n l hl (roots_image R p hp hr l hF)
  · exact h n l hl (hflag l hF)

end Surf
