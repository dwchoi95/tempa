/-
Theorem 5 (Footprint) for PyCore: the footprint of Definition 4 covers what
the relation needs, and the initial configurations are related.
-/
import PyCore.Sim

namespace PyCore

section
variable {R : Edit} {F : Label → Prop}

theorem not_bad_occ {l x C} (h : Item.bad R (.occ l x C) = true → F l) (hF : ¬ F l) :
    alike R C x = true := by
  cases hx : alike R C x
  · exact absurd (h (by simp [Item.bad, hx])) hF
  · rfl

theorem not_bad_fn {l S} (h : Item.bad R (.fn l S) = true → F l) (hF : ¬ F l) :
    sameKind R S := by
  unfold sameKind
  cases hk : decide (S.kind = (editSc R S).kind)
  · exact absurd (h (by simp_all [Item.bad])) hF
  · simp at hk; exact hk.symm

/-- Unfold the hypotheses on a node that is no site. -/
macro "site_none" hr:ident h1:ident h2:ident : tactic => `(tactic|
  simp only [rootsE, rootsS, rootsHs, itemsE, itemsS, itemsHs, $hr:ident, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte] at $h1:ident $h2:ident)

mutual
/-- Part (1) and the flagged items cover an expression. -/
theorem goodE_of (C : List Scope) : ∀ e : Expr, (∀ l ∈ rootsE R e, F l) →
    (∀ i ∈ itemsE R C e, i.bad R = true → F i.label) → goodE R F C e
  | .const l k, h1, _ => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · exact .inr rfl
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .name l x k, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .bin l _ a b, h1, h2 | .call l a b, h1, h2 | .bool l _ a b, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl, goodE_of C a (fun l hl => h1 l (by simp [hl]))
          (fun i hi => h2 i (by simp [hi])),
        goodE_of C b (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .lam l k x b, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_fn (h2 _ (by simp)) hF,
        goodB_of _ b h1 (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .walrus l x e, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF,
        goodE_of C e h1 (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .yield l e, h1, h2 | .yieldFrom l e, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl, goodE_of C e h1 (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
  | .cond l c a b, h1, h2 => by
    simp only [goodE]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.e l
    · site_none hr h1 h2
      exact .inr ⟨rfl,
        goodE_of C c (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodE_of C a (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodE_of C b (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsE, hr])) hF
theorem goodS_of (C : List Scope) : ∀ s : Stmt, (∀ l ∈ rootsS R s, F l) →
    (∀ i ∈ itemsS R C s, i.bad R = true → F i.label) → goodS R F C s
  | .assign l x e, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF,
        goodE_of C e h1 (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .del l x, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .expr l e, h1, h2 | .ret l e, h1, h2 | .raise l e, h1, h2 | .print l e, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl, goodE_of C e h1 h2⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .ite l e t u, h1, h2 | .while l e t u, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl,
        goodE_of C e (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodB_of C t (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodB_of C u (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .defn l f x b, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF, not_bad_fn (h2 _ (by simp)) hF,
        goodB_of _ b h1 (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .cls l x _ b, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      refine .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hF, ?_,
        goodB_of _ b h1 (fun i hi => h2 i (by simp [hi]))⟩
      intro y hy
      exact not_bad_occ (h2 (.occ l y (.cl l b :: C)) (by simp [hy])) hF
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .glob l x, h1, _ | .nonloc l x, h1, _ | .brk l, h1, _ | .cont l, h1, _ => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · exact .inr rfl
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
  | .tryE l b hs u, h1, h2 => by
    simp only [goodS]
    by_cases hF : F l; · exact .inl hF
    cases hr : R.s l
    · site_none hr h1 h2
      exact .inr ⟨rfl,
        goodB_of C b (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodHs_of C hs (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodB_of C u (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 l (by simp [rootsS, hr])) hF
theorem goodHs_of (C : List Scope) : ∀ hs : List Handler, (∀ l ∈ rootsHs R hs, F l) →
    (∀ i ∈ itemsHs R C hs, i.bad R = true → F i.label) → goodHs R F C hs
  | [], _, _ => trivial
  | .mk lh e x hb :: hs, h1, h2 => by
    simp only [goodHs]
    refine ⟨?_, goodHs_of C hs (fun l hl => h1 l (by simp [rootsHs, hl]))
      (fun i hi => h2 i (by simp [itemsHs, hi]))⟩
    by_cases hFh : F lh; · exact .inl hFh
    cases hh : R.h lh
    · simp only [rootsHs, itemsHs, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h1 h2
      exact .inr ⟨rfl, not_bad_occ (h2 _ (by simp)) hFh,
        goodE_of C e (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
        goodB_of C hb (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
    · exact absurd (h1 lh (by simp [rootsHs, hh])) hFh
theorem goodB_of (C : List Scope) : ∀ ss : List Stmt, (∀ l ∈ rootsB R ss, F l) →
    (∀ i ∈ itemsB R C ss, i.bad R = true → F i.label) → goodB R F C ss
  | [], _, _ => trivial
  | s :: ss, h1, h2 => by
    simp only [rootsB, itemsB] at h1 h2
    exact ⟨goodS_of C s (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi])),
      goodB_of C ss (fun l hl => h1 l (by simp [hl])) (fun i hi => h2 i (by simp [hi]))⟩
end

/-! When part (3) fires, F is every node of `p`, which covers it trivially. -/

theorem goodE_all (C : List Scope) (e : Expr) (h : ∀ l ∈ labelsE e, F l) : goodE R F C e := by
  cases e <;> simp only [goodE] <;> exact .inl (h _ (by simp [labelsE]))

theorem goodS_all (C : List Scope) (s : Stmt) (h : ∀ l ∈ labelsS s, F l) : goodS R F C s := by
  cases s <;> simp only [goodS] <;> exact .inl (h _ (by simp [labelsS]))

theorem goodB_all (C : List Scope) : ∀ ss : List Stmt, (∀ l ∈ labelsB ss, F l) → goodB R F C ss
  | [], _ => trivial
  | s :: ss, h => by
    simp only [labelsB] at h
    exact ⟨goodS_all C s (fun l hl => h l (by simp [hl])),
      goodB_all C ss (fun l hl => h l (by simp [hl]))⟩

end

/-! The site roots lie in part (1). -/

mutual
theorem rootsE_sub (R : Edit) : ∀ (e : Expr) (l : Label), l ∈ rootsE R e → l ∈ part1E R e
  | .const k _, l, h | .name k _ _, l, h => by
    cases hr : R.e k <;> simp_all [rootsE, part1E, labelsE]
  | .bin k _ a b, l, h | .call k a b, l, h | .bool k _ a b, l, h => by
    have ha := rootsE_sub R a l; have hb := rootsE_sub R b l
    cases hr : R.e k <;> simp only [rootsE, part1E, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons] at h ⊢
    · rcases h with h | h
      · exact .inl (ha h)
      · exact .inr (hb h)
    · simp at h; simp [labelsE, h]
  | .lam k _ _ b, l, h => by
    have := rootsB_sub R b l
    cases hr : R.e k <;> simp only [rootsE, part1E, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h ⊢
    · exact this h
    · simp at h; simp [labelsE, h]
  | .walrus k _ b, l, h | .yield k b, l, h | .yieldFrom k b, l, h => by
    have := rootsE_sub R b l
    cases hr : R.e k <;> simp only [rootsE, part1E, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h ⊢
    · exact this h
    · simp at h; simp [labelsE, h]
  | .cond k c a b, l, h => by
    have hc := rootsE_sub R c l; have ha := rootsE_sub R a l; have hb := rootsE_sub R b l
    cases hr : R.e k <;> simp only [rootsE, part1E, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons] at h ⊢
    · rcases h with (h | h) | h
      · exact .inl (.inl (hc h))
      · exact .inl (.inr (ha h))
      · exact .inr (hb h)
    · simp at h; simp [labelsE, h]
theorem rootsS_sub (R : Edit) : ∀ (s : Stmt) (l : Label), l ∈ rootsS R s → l ∈ part1S R s
  | .assign k _ e, l, h | .expr k e, l, h | .ret k e, l, h | .raise k e, l, h
  | .print k e, l, h => by
    have he := rootsE_sub R e l
    cases hr : R.s k <;> simp only [rootsS, part1S, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact he h
    · simp at h; simp [labelsS, h]
  | .del k _, l, h | .glob k _, l, h | .nonloc k _, l, h | .brk k, l, h | .cont k, l, h => by
    cases hr : R.s k <;> simp_all [rootsS, part1S, labelsS]
  | .ite k c t u, l, h | .while k c t u, l, h => by
    have hc := rootsE_sub R c l; have ht := rootsB_sub R t l; have hu := rootsB_sub R u l
    cases hr : R.s k <;> simp only [rootsS, part1S, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at h ⊢
    · rcases h with (h | h) | h
      · exact .inl (.inl (hc h))
      · exact .inl (.inr (ht h))
      · exact .inr (hu h)
    · simp at h; simp [labelsS, h]
  | .defn k _ _ b, l, h | .cls k _ _ b, l, h => by
    have hb := rootsB_sub R b l
    cases hr : R.s k <;> simp only [rootsS, part1S, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact hb h
    · simp at h; simp [labelsS, h]
  | .tryE k b hs u, l, h => by
    have h1 := rootsB_sub R b l; have h2 := rootsHs_sub R hs l; have h3 := rootsB_sub R u l
    cases hr : R.s k <;> simp only [rootsS, part1S, hr, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at h ⊢
    · rcases h with (h | h) | h
      · exact .inl (.inl (h1 h))
      · exact .inl (.inr (h2 h))
      · exact .inr (h3 h)
    · simp at h; simp [labelsS, h]
theorem rootsHs_sub (R : Edit) : ∀ (hs : List Handler) (l : Label), l ∈ rootsHs R hs → l ∈ part1Hs R hs
  | [], _, h => h
  | .mk lh e x hb :: hs, l, h => by
    have h1 := rootsE_sub R e l; have h2 := rootsB_sub R hb l; have h3 := rootsHs_sub R hs l
    cases hh : R.h lh <;> simp only [rootsHs, part1Hs, hh, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons] at h ⊢
    · rcases h with (h | h) | h
      · exact .inl (.inl (h1 h))
      · exact .inl (.inr (h2 h))
      · exact .inr (h3 h)
    · rcases h with h | h
      · simp at h; exact .inl (by simp [labelsHs, h])
      · exact .inr (h3 h)
theorem rootsB_sub (R : Edit) : ∀ (ss : List Stmt) (l : Label), l ∈ rootsB R ss → l ∈ part1B R ss
  | [], _, h => h
  | s :: ss, l, h => by
    have h1 := rootsS_sub R s l; have h2 := rootsB_sub R ss l
    simp only [rootsB, part1B, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (h1 h)
    · exact .inr (h2 h)
end

/-- The footprint of Definition 4 covers every condition the relation needs. -/
theorem footprint_good (R : Edit) (p : List Stmt) : goodB R (inFootprint R p) [] p := by
  by_cases hk : kindChanges R p = []
  · have hF : ∀ l, l ∈ part1B R p ++ part2 R p → inFootprint R p l := by
      intro l hl; simp only [inFootprint, footprint?, hk, ↓reduceIte]; exact hl
    apply goodB_of [] p (fun l hl => hF l (List.mem_append_left _ (rootsB_sub R p l hl)))
    intro i hi hb
    cases i with
    | occ l x C =>
      simp only [Item.bad, Bool.not_eq_true'] at hb
      apply hF
      simp only [Item.label, List.mem_append, part2, List.mem_filterMap]
      exact .inr ⟨_, hi, by simp [hb]⟩
    | fn l S =>
      have : l ∈ kindChanges R p := by
        simp only [kindChanges, List.mem_filterMap]
        exact ⟨_, hi, by simp_all [Item.bad]⟩
      rw [hk] at this; cases this
  · have hF : ∀ l, l ∈ labelsB p → inFootprint R p l := by
      intro l hl; simp only [inFootprint, footprint?, hk, ↓reduceIte]; exact hl
    exact goodB_all [] p hF

/-- The initial configurations: the identity on the input (the module dictionary
and the interpretation's initial state). -/
theorem init_rel {S : Type} {R : Edit} {F : Label → Prop} (p : List Stmt) (σ : Name → Option Val)
    (s : S) (hg : goodB R F [] p) : Rel R F (init p σ s) (init (editB R p) σ s) := by
  refine ⟨⟨⟨rfl, rfl, rfl, fun _ _ => rfl, (fun _ h => nomatch h), rfl, rfl, rfl, fun _ _ => rfl, hg, ?_⟩,
    trivial⟩, fun _ => by simp [init, ObjRel], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [modFrame]

/-- **Theorem 5 (Footprint).** Let `q = editB R p` be obtained from `p` by
replacing the subtrees at the sites of `R`. For every interpretation `I` and
initial state `s` of it, on every input `σ` on which the execution of `p`
evaluates no node of F(p, q), the execution of `q` has the same outcome: the same
output, module dictionary (hence return values) and interpretation state, the same
uncaught exception, or nontermination (lock-step, so also the same step count). -/
theorem footprint_theorem {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option Val) (s : S)
    (h : NoReach I (inFootprint R p) (init p σ s)) :
    (∀ o, Terminates I (init p σ s) o ↔ Terminates I (init (editB R p) σ s) o) ∧
    (Diverges I (init p σ s) ↔ Diverges I (init (editB R p) σ s)) :=
  same_outcome I (init_rel p σ s (footprint_good R p)) h

/-- A smaller footprint also suffices: the site roots, the flagged occurrences,
and only the `def`/lambda nodes of functions whose kind changes (not all of `p`).
Any `F` with `goodB R F [] p` works. -/
theorem footprint_theorem_of_good {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (F : Label → Prop) (σ : Name → Option Val) (s : S) (hg : goodB R F [] p)
    (h : NoReach I F (init p σ s)) :
    (∀ o, Terminates I (init p σ s) o ↔ Terminates I (init (editB R p) σ s) o) ∧
    (Diverges I (init p σ s) ↔ Diverges I (init (editB R p) σ s)) :=
  same_outcome I (init_rel p σ s hg) h


/-- Theorem 5 with a smaller footprint: the site roots, the occurrences of
part (2), and, instead of all of `p`, only the `def`/lambda node of each function
whose kind changes. -/
theorem footprint_theorem_min {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt)
    (σ : Name → Option Val) (s : S)
    (h : NoReach I (fun l => l ∈ rootsB R p ∨ l ∈ flagged R p) (init p σ s)) :
    (∀ o, Terminates I (init p σ s) o ↔ Terminates I (init (editB R p) σ s) o) ∧
    (Diverges I (init p σ s) ↔ Diverges I (init (editB R p) σ s)) := by
  refine footprint_theorem_of_good I R p _ σ s (goodB_of [] p (fun l hl => .inl hl) ?_) h
  intro i hi hb
  exact .inr (List.mem_filterMap.2 ⟨i, hi, by simp [hb]⟩)

end PyCore
