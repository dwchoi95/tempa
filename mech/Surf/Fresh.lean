/-
The fresh names: a flagged occurrence of a fresh name. The premise `hF` of
`flagged_image_of` is reduced to a property of one translated program (`FreshCanon`):
along the chain of each of its occurrences, a fresh name is bound in the scope of the
occurrence and in no scope around it (a comparison's middle operand is kept in a frame cell
by the core's `$set`/`$get`, no name). That pattern is the same in ⌊p⌋ and ⌊q⌋, so no
occurrence of a fresh name outside the PyCore sites is classified differently.
-/
import Surf.Chain
import Std.Data.String.ToNat

namespace Surf
open PyCore (Name Label)

/-! ## Items of `p` outside the sites are items of `editB R p` -/

set_option hygiene false in
macro "oe" : tactic => `(tactic| (
  split at h
  · simp at h
  rename_i hn; simp only [Option.not_isSome_iff_eq_none] at hn
  simp only [PyCore.editE, PyCore.editS, hn, Option.getD_none, PyCore.itemsE, PyCore.itemsS,
    PyCore.itemsB, enone_e, enone_s, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append,
    List.mem_cons, List.append_nil, PyCore.editSc, List.map_cons, List.not_mem_nil, or_false,
    PyCore.Item.occ.injEq, reduceCtorEq, false_or] at h ⊢))

theorem pitemsHs_cons {i : PyCore.Item} {C : List PyCore.Scope} (h' : PyCore.Handler)
    {hs : List PyCore.Handler} (h : i ∈ PyCore.itemsHs R0 C hs) : i ∈ PyCore.itemsHs R0 C (h' :: hs) := by
  cases h'; simp only [PyCore.itemsHs, List.mem_append]; exact .inr h

mutual
/-- An occurrence outside the sites of `R` is an occurrence of the edited program, in the
edited chain. -/
theorem poccE_edit (R : PyCore.Edit) (C : List PyCore.Scope) (l : Label) (x : Name) :
    ∀ (e : PyCore.Expr) (C' : List PyCore.Scope), .occ l x C' ∈ PyCore.itemsE R C e →
      .occ l x (C'.map (PyCore.editSc R)) ∈ PyCore.itemsE R0 (C.map (PyCore.editSc R)) (PyCore.editE R e)
  | .const .., _, h => by simp [PyCore.itemsE] at h
  | .name .., C', h => by
    simp only [PyCore.itemsE] at h; oe; obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | .bin _ _ a b, C', h | .call _ a b, C', h | .bool _ _ a b, C', h => by
    simp only [PyCore.itemsE] at h; oe
    exact h.imp (poccE_edit R C l x a C') (poccE_edit R C l x b C')
  | .lam _ _ _ b, C', h => by
    simp only [PyCore.itemsE] at h; oe
    rcases h with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp [PyCore.editSc]
    · have := poccB_edit R _ l x b C' h; simp only [List.map_cons, PyCore.editSc] at this
      exact .inr this
  | .walrus _ _ e, C', h => by
    simp only [PyCore.itemsE] at h; oe
    rcases h with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · exact .inr (poccE_edit R C l x e C' h)
  | .yield _ e, C', h | .yieldFrom _ e, C', h => by
    simp only [PyCore.itemsE] at h; oe; exact poccE_edit R C l x e C' h
  | .cond _ c a b, C', h => by
    simp only [PyCore.itemsE] at h; oe
    exact h.imp (Or.imp (poccE_edit R C l x c C') (poccE_edit R C l x a C')) (poccE_edit R C l x b C')
theorem poccS_edit (R : PyCore.Edit) (C : List PyCore.Scope) (l : Label) (x : Name) :
    ∀ (s : PyCore.Stmt) (C' : List PyCore.Scope), .occ l x C' ∈ PyCore.itemsS R C s →
      .occ l x (C'.map (PyCore.editSc R)) ∈ PyCore.itemsB R0 (C.map (PyCore.editSc R)) (PyCore.editS R s)
  | .assign _ _ e, C', h => by
    simp only [PyCore.itemsS] at h; oe
    rcases h with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · exact .inr (poccE_edit R C l x e C' h)
  | .del .., C', h | .glob .., C', h | .nonloc .., C', h => by
    simp only [PyCore.itemsS] at h; oe; obtain ⟨rfl, rfl, rfl⟩ := h; simp
  | .expr _ e, C', h | .ret _ e, C', h | .raise _ e, C', h | .print _ e, C', h => by
    simp only [PyCore.itemsS] at h; oe; exact poccE_edit R C l x e C' h
  | .ite _ c t u, C', h | .while _ c t u, C', h => by
    simp only [PyCore.itemsS] at h; oe
    exact h.imp (Or.imp (poccE_edit R C l x c C') (poccB_edit R C l x t C')) (poccB_edit R C l x u C')
  | .defn _ _ _ b, C', h => by
    simp only [PyCore.itemsS] at h; oe
    rcases h with h | h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp [PyCore.editSc]
    · have := poccB_edit R _ l x b C' h; simp only [List.map_cons, PyCore.editSc] at this
      exact .inr (.inr this)
  | .cls _ _ _ b, C', h => by
    simp only [PyCore.itemsS] at h; oe
    rcases h with (h | h) | h
    · obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · simp only [List.mem_map, PyCore.Item.occ.injEq] at h
      obtain ⟨y, hy, rfl, rfl, rfl⟩ := h
      exact .inl (.inr (List.mem_map.2 ⟨_, hy, rfl⟩))
    · have := poccB_edit R _ l x b C' h; simp only [List.map_cons, PyCore.editSc] at this
      exact .inr this
  | .tryE _ b hs u, C', h => by
    simp only [PyCore.itemsS] at h; oe
    exact h.imp (Or.imp (poccB_edit R C l x b C') (poccHs_edit R C l x hs C')) (poccB_edit R C l x u C')
  | .brk _, _, h | .cont _, _, h => by simp [PyCore.itemsS] at h
theorem poccHs_edit (R : PyCore.Edit) (C : List PyCore.Scope) (l : Label) (x : Name) :
    ∀ (hs : List PyCore.Handler) (C' : List PyCore.Scope), .occ l x C' ∈ PyCore.itemsHs R C hs →
      .occ l x (C'.map (PyCore.editSc R)) ∈ PyCore.itemsHs R0 (C.map (PyCore.editSc R)) (PyCore.editHs R hs)
  | [], _, h => by simp [PyCore.itemsHs] at h
  | .mk lh e y hb :: hs, C', h => by
    simp only [PyCore.itemsHs, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h
      · rename_i hn; simp only [Option.not_isSome_iff_eq_none] at hn
        simp only [List.mem_append, List.mem_cons] at h
        simp only [PyCore.editHs, hn, Option.getD_none, PyCore.itemsHs, enone_h, Option.isSome_none,
          Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons]
        rcases h with h | h | h
        · exact .inl (.inl (poccE_edit R C l x e C' h))
        · obtain ⟨rfl, rfl, rfl⟩ := h; simp
        · exact .inl (.inr (.inr (poccB_edit R C l x hb C' h)))
    · exact pitemsHs_cons _ (poccHs_edit R C l x hs C' h)
theorem poccB_edit (R : PyCore.Edit) (C : List PyCore.Scope) (l : Label) (x : Name) :
    ∀ (ss : List PyCore.Stmt) (C' : List PyCore.Scope), .occ l x C' ∈ PyCore.itemsB R C ss →
      .occ l x (C'.map (PyCore.editSc R)) ∈ PyCore.itemsB R0 (C.map (PyCore.editSc R)) (PyCore.editB R ss)
  | [], _, h => by simp [PyCore.itemsB] at h
  | s :: ss, C', h => by
    simp only [PyCore.itemsB, List.mem_append] at h
    simp only [PyCore.editB, pitemsB_append, List.mem_append]
    exact h.imp (poccS_edit R C l x s C') (poccB_edit R C l x ss C')
end

/-! ## Classification by the facts about one name -/


theorem pisComp_edit (R : PyCore.Edit) (S : PyCore.Scope) : (PyCore.editSc R S).isComp = S.isComp := by
  cases S <;> rfl

section
variable (R : PyCore.Edit) (x : Name)

theorem scope_congr {S : PyCore.Scope} (h : xf x (PyCore.editSc R S) = xf x S) :
    (PyCore.editSc R S).declG x = S.declG x ∧ (PyCore.editSc R S).declN x = S.declN x ∧
    (PyCore.editSc R S).walrus x = S.walrus x ∧ (PyCore.editSc R S).binds x = S.binds x := by
  simp only [xf, Prod.mk.injEq] at h
  simp only [PyCore.Scope.declG, PyCore.Scope.declN, PyCore.Scope.walrus, PyCore.Scope.binds,
    pisComp_edit, h, and_self]

theorem walGlobal_congr : ∀ C : List PyCore.Scope, (∀ S ∈ C, xf x (PyCore.editSc R S) = xf x S) →
    PyCore.walGlobal (C.map (PyCore.editSc R)) x = PyCore.walGlobal C x
  | [], _ => rfl
  | S :: C, h => by
    have h1 := scope_congr R x (h S (by simp))
    have ih := walGlobal_congr C (fun S' hS' => h S' (by simp [hS']))
    simp only [List.map_cons, PyCore.walGlobal, pisComp_edit, h1.1, ih]

theorem enclosing_congr : ∀ C : List PyCore.Scope, (∀ S ∈ C, xf x (PyCore.editSc R S) = xf x S) →
    PyCore.enclosing (C.map (PyCore.editSc R)) x = PyCore.enclosing C x
  | [], _ => rfl
  | S :: C, h => by
    have h1 := scope_congr R x (h S (by simp))
    have ih := enclosing_congr C (fun S' hS' => h S' (by simp [hS']))
    have hw := walGlobal_congr R x C (fun S' hS' => h S' (by simp [hS']))
    cases S with
    | cl l ss => simp only [List.map_cons, PyCore.editSc, PyCore.enclosing, ih]
    | fn l c y b =>
      simp only [PyCore.editSc] at h1
      simp only [List.map_cons, PyCore.editSc, PyCore.enclosing, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hw, ih]

theorem clsOf_congr : ∀ C : List PyCore.Scope, (∀ S ∈ C, xf x (PyCore.editSc R S) = xf x S) →
    PyCore.clsOf (C.map (PyCore.editSc R)) x = PyCore.clsOf C x
  | [], _ => rfl
  | S :: C, h => by
    have h1 := scope_congr R x (h S (by simp))
    have he := enclosing_congr R x C (fun S' hS' => h S' (by simp [hS']))
    have hw := walGlobal_congr R x C (fun S' hS' => h S' (by simp [hS']))
    simp only [List.map_cons, PyCore.clsOf, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hw, he]

/-- A name about which every scope of the chain says the same in `q` is classified alike. -/
theorem alike_of_xf : ∀ C : List PyCore.Scope, (∀ S ∈ C, xf x (PyCore.editSc R S) = xf x S) →
    PyCore.alike R C x = true
  | [], _ => rfl
  | S :: C, h => by
    have ih := alike_of_xf C (fun S' hS' => h S' (by simp [hS']))
    have hc := clsOf_congr R x (S :: C) h
    simp only [PyCore.alike, hc, beq_self_eq_true, ih, Bool.and_self]

end

/-! ## The pattern of a fresh name's facts -/




theorem patB_edit (R : PyCore.Edit) (C : List PyCore.Scope) : patB (C.map (PyCore.editSc R)) = patB C := by
  cases C <;> simp [patB, List.map_map]


/-- The fresh-name invariant of a PyCore program: along the chain of each occurrence of a fresh
name, the facts about it follow `patB`. -/
def FreshCanon (P : List PyCore.Stmt) : Prop :=
  ∀ L x C', PyCore.Item.occ L x C' ∈ PyCore.itemsB R0 [] P → IsFresh x → C'.map (xf x) = patB C'

/-- With the invariant in ⌊p⌋ and ⌊q⌋, no occurrence of a fresh name outside the PyCore sites
is classified differently. -/
theorem fresh_not_bad (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p) (hk : KeepsLabels R)
    (hr : regB R [] p = true) (hcp : FreshCanon (tr p)) (hcq : FreshCanon (tr (editB R p))) :
    ∀ i ∈ PyCore.itemsB (trEdit R p) [] (tr p), FreshItem i → i.bad (trEdit R p) = false := by
  intro i hi hf
  cases i with
  | fn => exact hf.elim
  | occ L x C' =>
    have hi0 := pitemsB_sub _ _ _ _ hi
    have h1 := poccB_edit (trEdit R p) [] L x (tr p) C' hi
    rw [← tr_edit R p hp h0 hk hr] at h1
    simp only [List.map_nil] at h1
    have key : C'.map (xf x) = (C'.map (PyCore.editSc (trEdit R p))).map (xf x) := by
      rw [hcp L x C' hi0 hf, hcq L x _ h1 hf, patB_edit]
    rw [List.map_map] at key
    have hpt : ∀ S ∈ C', xf x (PyCore.editSc (trEdit R p) S) = xf x S :=
      fun S hS => (List.map_inj_left.1 key S hS).symm
    simp [PyCore.Item.bad, alike_of_xf _ x C' hpt]

/-- Parts (2) and (3) of the image inclusion, given the fresh-name invariant of ⌊p⌋ and ⌊q⌋. -/
theorem flagged_image_canon (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p)
    (hd : NoDot p) (hg : GenOk p) (hk : KeepsLabels R) (hr : regB R [] p = true) (hcp : FreshCanon (tr p))
    (hcq : FreshCanon (tr (editB R p))) :
    ∀ x ∈ PyCore.flagged (trEdit R p) (tr p), imgF R p x :=
  flagged_image_fresh R p hp h0 hd hg hk hr fun i hi hf hb => by
    rw [fresh_not_bad R p hp h0 hk hr hcp hcq i hi hf] at hb; exact absurd hb (by decide)

/-- Theorem 5 for ⌊p⌋ and ⌊q⌋ with the image of F_surf, given the fresh-name invariant of
⌊p⌋ and ⌊q⌋. -/
theorem footprint_theorem_surf_canon {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option PyCore.Val) (s : S) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p) (hd : NoDot p)
    (hg : GenOk p) (hk : KeepsLabels R) (hr : regB R [] p = true) (hcp : FreshCanon (tr p))
    (hcq : FreshCanon (tr (editB R p)))
    (h : PyCore.NoReach I (imgF R p) (PyCore.init (tr p) σ s)) :
    (∀ o, PyCore.Terminates I (PyCore.init (tr p) σ s) o ↔ PyCore.Terminates I (PyCore.init (tr (editB R p)) σ s) o) ∧
    (PyCore.Diverges I (PyCore.init (tr p) σ s) ↔ PyCore.Diverges I (PyCore.init (tr (editB R p)) σ s)) :=
  footprint_theorem_surf_of I R p σ s hp h0 hk hr (flagged_image_canon R p hp h0 hd hg hk hr hcp hcq) h

/-! ## Fresh names determine their labels -/

/-- Fresh names with one-letter tags are distinct for distinct tags or labels. `fresh_inj'`
(`Canon.lean`), which `fresh_canon` uses, covers every tag with no digit (`acc` too). -/
theorem fresh_inj {t t' : String} {l l' : Label} (ht : t.toList.length = 1) (ht' : t'.toList.length = 1)
    (h : fresh t l = fresh t' l') : t = t' ∧ l = l' := by
  have h1 := congrArg String.toList h
  simp only [fresh, String.toList_append] at h1
  simp at h1
  obtain ⟨h3, h4⟩ := List.append_inj h1 (by omega)
  refine ⟨String.ext h3, ?_⟩
  rw [← Nat.ofDigitChars_ten_toDigits (n := l), h4, Nat.ofDigitChars_ten_toDigits]

end Surf
