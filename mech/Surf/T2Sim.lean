/-
A stuttering simulation between two deterministic machines (Surf.Sem and PyCore in (T2)).

The relation carries the set `H` of Surf nodes touched before (a run's history), so that a PyCore
node evaluated again later (a parameter's binding at each call, a loop's nodes at each iteration)
may count a touch of an earlier step. Each simulation step from related configurations `a ~ b` is one of: both runs end, after
finitely many steps, in final configurations that correspond (`Fin`); both make at least one
step, to related configurations; only `a`'s run steps, and the measure `μ` decreases; only `b`'s
run steps, and the measure decreases. The measure rules out infinite stuttering, so termination,
its outcome and divergence carry over in both directions. Each step also says that every node
`b`'s run evaluates on the way (`fb`), the node `x`, is touched by `a`'s run there or before (`TA _ (x / 64)`, `H`:
the translation labels the `k`-th node it makes for the Surf node `l` as `64 l + k`), which gives the
reach correspondence.
-/
import PyCore.Syntax

namespace Surf.T2
open PyCore (Label)

section Gen
variable {α : Type} (s : α → Option α)

/-- `n` steps, stopping where the run ends (`Sem.run`, `PyCore.run`). -/
def runF : Nat → α → α
  | 0, a => a
  | n + 1, a => match s a with
    | some a' => runF n a'
    | none => a

/-- `Path s a b xs`: `a` reaches `b` in `xs.length` steps through `xs` (`a` first, `b` excluded). -/
inductive Path : α → α → List α → Prop
  | nil (a : α) : Path a a []
  | cons {a a' b : α} {xs : List α} : s a = some a' → Path a' b xs → Path a b (a :: xs)

variable {s}

theorem runF_stop {a : α} (h : s a = none) : ∀ n, runF s n a = a
  | 0 => rfl
  | n + 1 => by simp [runF, h]

theorem runF_add : ∀ (n m : Nat) (a : α), runF s (n + m) a = runF s m (runF s n a)
  | 0, m, a => by simp [runF]
  | n + 1, m, a => by
    rw [Nat.add_right_comm]
    cases h : s a with
    | none => simp [runF, h, runF_stop h]
    | some a' => simp [runF, h, runF_add n m a']

theorem Path.run {a b : α} {xs : List α} (h : Path s a b xs) : runF s xs.length a = b := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [runF, h, ih]

theorem Path.append {a b c : α} {xs ys : List α} (h1 : Path s a b xs) (h2 : Path s b c ys) :
    Path s a c (xs ++ ys) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h (ih h2)

theorem Path.mem {a b : α} {xs : List α} (h : Path s a b xs) :
    ∀ z ∈ xs, ∃ i, i < xs.length ∧ runF s i a = z ∧ s z ≠ none := by
  induction h with
  | nil => simp
  | cons h p ih =>
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨0, by simp, rfl, by simp [h]⟩
    · obtain ⟨i, hi, rfl, hs⟩ := ih z hz
      exact ⟨i + 1, by simp; omega, by simp [runF, h], hs⟩

theorem Path.at {a b : α} {xs : List α} (h : Path s a b xs) :
    ∀ i, i < xs.length → runF s i a ∈ xs ∧ s (runF s i a) ≠ none := by
  induction h with
  | nil => simp
  | cons h p ih =>
    intro i hi
    cases i with
    | zero => exact ⟨by simp [runF], by simp [runF, h]⟩
    | succ i =>
      have := ih i (by simp at hi; omega)
      simp only [runF, h]
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- Where a run ends, it stays: a final configuration of `a`'s run is the final one `a` reaches. -/
theorem Path.final {a b : α} {xs : List α} (h : Path s a b xs) (hb : s b = none) {n : Nat}
    (hn : s (runF s n a) = none) : runF s n a = b := by
  have hle : xs.length ≤ n := Nat.le_of_not_lt fun hlt => (h.at n hlt).2 hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runF_add, h.run, runF_stop hb]

end Gen

theorem len_pos {γ} {xs : List γ} (h : xs ≠ []) : 0 < xs.length := by
  cases xs <;> simp_all

section Sim
variable {α β : Type} (sa : α → Option α) (sb : β → Option β)
  (R : (Label → Prop) → α → β → Prop) (Fin : α → β → Prop) (μ : α → β → Nat)
  (TA : α → Label → Prop) (fb : β → Option Label)

/-- The Surf nodes touched before: `H`, or by one of `zs`. -/
def Seen (H : Label → Prop) (zs : List α) (l : Label) : Prop := H l ∨ ∃ z ∈ zs, TA z l

/-- Every node a configuration of `ys` evaluates has its Surf node touched before (`H`) or by one
of `zs`. -/
def Cover (H : Label → Prop) (zs : List α) (ys : List β) : Prop :=
  ∀ y ∈ ys, ∀ x, fb y = some x → Seen TA H zs (x / 64)

/-- One simulation step from `a ~ b`, `H` the Surf nodes touched before `a`. The relation after a
step of `a`'s run has the touches of the configurations on the way and of the one reached. -/
def SimStep (H : Label → Prop) (a : α) (b : β) : Prop :=
  (∃ a' b' xs ys, Path sa a a' xs ∧ sa a' = none ∧ Path sb b b' ys ∧ sb b' = none ∧ Fin a' b' ∧
      Cover TA fb H (a' :: xs) (b' :: ys)) ∨
  (∃ a' b' xs ys, Path sa a a' xs ∧ xs ≠ [] ∧ Path sb b b' ys ∧ ys ≠ [] ∧ R (Seen TA H (a' :: xs)) a' b' ∧
      Cover TA fb H (a' :: xs) ys) ∨
  (∃ a' xs, Path sa a a' xs ∧ xs ≠ [] ∧ R (Seen TA H (a' :: xs)) a' b ∧ μ a' b < μ a b) ∨
  (∃ b' ys, Path sb b b' ys ∧ ys ≠ [] ∧ R H a b' ∧ μ a b' < μ a b ∧ Cover TA fb H [a] ys)

/-- A simulation step in which `a`'s run does not stutter alone: both end, both step, or `b`'s run
steps alone. -/
def SimStepB (H : Label → Prop) (a : α) (b : β) : Prop :=
  (∃ a' b' xs ys, Path sa a a' xs ∧ sa a' = none ∧ Path sb b b' ys ∧ sb b' = none ∧ Fin a' b' ∧
      Cover TA fb H (a' :: xs) (b' :: ys)) ∨
  (∃ a' b' xs ys, Path sa a a' xs ∧ xs ≠ [] ∧ Path sb b b' ys ∧ ys ≠ [] ∧ R (Seen TA H (a' :: xs)) a' b' ∧
      Cover TA fb H (a' :: xs) ys) ∨
  (∃ b' ys, Path sb b b' ys ∧ ys ≠ [] ∧ R H a b' ∧ μ a b' < μ a b ∧ Cover TA fb H [a] ys)

/-- A relation that holds again with more nodes touched before. -/
class HMono (R : (Label → Prop) → α → β → Prop) : Prop where
  mono : ∀ {H H' : Label → Prop} {a : α} {b : β}, (∀ l, H l → H' l) → R H a b → R H' a b

variable {sa sb R Fin μ TA fb}

theorem SimStepB.sim {H : Label → Prop} {a : α} {b : β} (h : SimStepB sa sb R Fin μ TA fb H a b) :
    SimStep sa sb R Fin μ TA fb H a b := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr h))

/-- `b'` and `b` make the same step and `b` evaluates no node: a step from `a ~ b'` is one from `a ~ b`
(whose measure is larger). -/
theorem SimStepB.swap {H : Label → Prop} {a : α} {b b' : β} (hst : sb b = sb b') (hfb : fb b = none)
    (hμ : μ a b' ≤ μ a b) (hfin : sb b' = none → ∀ a', Fin a' b' → Fin a' b)
    (h : SimStepB sa sb R Fin μ TA fb H a b') : SimStepB sa sb R Fin μ TA fb H a b := by
  have hb : ∀ {zs : List α} {ys : List β}, Cover TA fb H zs (b' :: ys) → Cover TA fb H zs (b :: ys) := by
    intro zs ys hc y hy x hx
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [hfb] at hx; cases hx
    · exact hc y (List.mem_cons_of_mem _ hy) x hx
  rcases h with ⟨a', b'', xs, ys, pa, ha, pb, hb2, hf, hc⟩ | ⟨a', b'', xs, ys, pa, hxs, pb, hys, hr, hc⟩ |
      ⟨b'', ys, pb, hys, hr, hlt, hc⟩
  · cases pb with
    | nil => exact .inl ⟨a', b, xs, [], pa, ha, .nil _, by rw [hst]; exact hb2, hfin hb2 a' hf,
        fun y hy x hx => by
          rcases List.mem_cons.1 hy with rfl | hy
          · rw [hfb] at hx; cases hx
          · simp at hy⟩
    | cons e p => exact .inl ⟨a', b'', xs, b :: _, pa, ha, .cons (hst ▸ e) p, hb2, hf, fun y hy x hx => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hc _ List.mem_cons_self x hx
        · exact hb (fun y' hy' => hc y' (List.mem_cons_of_mem _ hy')) y hy x hx⟩
  · cases pb with
    | nil => exact absurd rfl hys
    | cons e p => exact .inr (.inl ⟨a', b'', xs, b :: _, pa, hxs, .cons (hst ▸ e) p, by simp, hr, hb hc⟩)
  · cases pb with
    | nil => exact absurd rfl hys
    | cons e p => exact .inr (.inr ⟨b'', b :: _, .cons (hst ▸ e) p, by simp, hr, by omega, hb hc⟩)

theorem seen_cons (H : Label → Prop) (a : α) (xs : List α) : Seen TA (Seen TA H [a]) xs = Seen TA H (a :: xs) := by
  funext l; apply propext
  simp only [Seen, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((h | ⟨z, rfl, h⟩) | ⟨z, hz, h⟩)
    · exact .inl h
    · exact .inr ⟨z, .inl rfl, h⟩
    · exact .inr ⟨z, .inr hz, h⟩
  · rintro (h | ⟨z, rfl | hz, h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨z, rfl, h⟩)
    · exact .inr ⟨z, hz, h⟩

theorem seen_mono {H : Label → Prop} {zs zs' : List α} (h : ∀ z ∈ zs, z ∈ zs') {l : Label} :
    Seen TA H zs l → Seen TA H zs' l
  | .inl h' => .inl h'
  | .inr ⟨z, hz, h'⟩ => .inr ⟨z, h z hz, h'⟩

theorem seen_eq {H : Label → Prop} {zs zs' : List α} (h : ∀ z, z ∈ zs ↔ z ∈ zs') : Seen TA H zs = Seen TA H zs' := by
  funext l; apply propext; exact ⟨seen_mono fun z hz => (h z).1 hz, seen_mono fun z hz => (h z).2 hz⟩

theorem seen_sub {H : Label → Prop} {zs zs' : List α} (h : ∀ z ∈ zs, z ∈ zs') : ∀ l, Seen TA H zs l → Seen TA H zs' l :=
  fun _ => seen_mono h

theorem seen_swap (H : Label → Prop) (a b : α) (l : List α) : Seen TA H (a :: b :: l) = Seen TA H (b :: a :: l) :=
  seen_eq fun _ => (List.Perm.swap b a l).mem_iff

theorem seen_middle (H : Label → Prop) (xs : List α) (a : α) (ys : List α) :
    Seen TA H (xs ++ a :: ys) = Seen TA H (a :: (xs ++ ys)) :=
  seen_eq fun _ => List.perm_middle.mem_iff

theorem Cover.mono {H H' : Label → Prop} {zs zs' : List α} {ys : List β} (h : Cover TA fb H zs ys)
    (hs : ∀ l, Seen TA H zs l → Seen TA H' zs' l) : Cover TA fb H' zs' ys :=
  fun y hy x hx => hs _ (h y hy x hx)

theorem Cover.append {H : Label → Prop} {zs : List α} {ys ys' : List β} (h : Cover TA fb H zs ys)
    (h' : Cover TA fb H zs ys') : Cover TA fb H zs (ys ++ ys') := by
  intro y hy; rcases List.mem_append.1 hy with hy | hy
  · exact h y hy
  · exact h' y hy

/-- A step of `a`'s run and steps of `b`'s run before a simulation step: one simulation step (`b`'s
steps covered by the nodes touched before or by `a`). -/
theorem SimStep.pre [HMono R] {H : Label → Prop} {a a1 : α} {b b1 : β} {ys : List β}
    (ea : sa a = some a1) (pb : Path sb b b1 ys) (hys : ys ≠ []) (hc : Cover TA fb H [a] ys)
    (h : SimStep sa sb R Fin μ TA fb (Seen TA H [a]) a1 b1) : SimStep sa sb R Fin μ TA fb H a b := by
  have c1 : ∀ {zs : List α}, a ∈ zs → Cover TA fb H zs ys :=
    fun hz => hc.mono fun _ => seen_mono fun z h => by simp at h; subst h; exact hz
  have c2 : ∀ {xs zs : List α} {ys2 : List β}, Cover TA fb (Seen TA H [a]) xs ys2 → (∀ z ∈ a :: xs, z ∈ zs) →
      Cover TA fb H zs ys2 :=
    fun h hz => h.mono fun _ h' => seen_mono hz (by rw [seen_cons] at h'; exact h')
  rcases h with ⟨a', b', xs, ys2, pa, ha, pb2, hb, hf, hc2⟩ | ⟨a', b', xs, ys2, pa, hxs, pb2, hys2, hr, hc2⟩ |
      ⟨a', xs, pa, hxs, hr, hlt⟩ | ⟨b', ys2, pb2, hys2, hr, hlt, hc2⟩
  · refine .inl ⟨a', b', a :: xs, ys ++ ys2, .cons ea pa, ha, pb.append pb2, hb, hf, ?_⟩
    have h2 := c2 (zs := a' :: a :: xs) hc2 (by intro z hz; simp at hz ⊢; rcases hz with h | h | h <;> simp [h])
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h2 _ List.mem_cons_self
    · rcases List.mem_append.1 hy with hy | hy
      · exact c1 (by simp) y hy
      · exact h2 y (List.mem_cons_of_mem _ hy)
  · refine .inr (.inl ⟨a', b', a :: xs, ys ++ ys2, .cons ea pa, by simp, pb.append pb2, by simp [hys], ?_,
      Cover.append (c1 (by simp)) (c2 hc2 (by intro z hz; simp at hz ⊢; rcases hz with h | h | h <;> simp [h]))⟩)
    rwa [seen_cons, seen_swap] at hr
  · exact .inr (.inl ⟨a', b1, a :: xs, ys, .cons ea pa, by simp, pb, hys, by rwa [seen_cons, seen_swap] at hr, c1 (by simp)⟩)
  · refine .inr (.inl ⟨a1, b', [a], ys ++ ys2, .cons ea (.nil _), by simp, pb.append pb2, by simp [hys],
      HMono.mono (seen_sub fun z hz => List.mem_cons_of_mem _ hz) hr,
      Cover.append (c1 (by simp)) (c2 hc2 (by intro z hz; simp at hz ⊢; rcases hz with h | h <;> simp [h]))⟩)

/-! Helpers of the `yield from` cases. -/

theorem seen_app (H : Label → Prop) (xs ys : List α) : Seen TA (Seen TA H xs) ys = Seen TA H (xs ++ ys) := by
  funext l; apply propext
  simp only [Seen, List.mem_append]
  constructor
  · rintro ((h | ⟨z, hz, h⟩) | ⟨z, hz, h⟩)
    · exact .inl h
    · exact .inr ⟨z, .inl hz, h⟩
    · exact .inr ⟨z, .inr hz, h⟩
  · rintro (h | ⟨z, hz | hz, h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨z, hz, h⟩)
    · exact .inr ⟨z, hz, h⟩

/-- A cover at a longer history, the touches of `xs` added to `zs`. -/
theorem cover_up {H : Label → Prop} {xs zs zs' : List α} {ys : List β} (h : Cover TA fb (Seen TA H xs) zs ys)
    (hz : ∀ z ∈ xs ++ zs, z ∈ zs') : Cover TA fb H zs' ys :=
  h.mono fun l h' => by rw [seen_app] at h'; exact seen_mono hz h'

theorem cover_zs {H : Label → Prop} {zs zs' : List α} {ys : List β} (h : Cover TA fb H zs ys)
    (hz : ∀ z ∈ zs, z ∈ zs') : Cover TA fb H zs' ys :=
  h.mono fun _ => seen_mono hz

theorem cover_two {H : Label → Prop} {zs : List α} {b0 b : β} {ys : List β} (h0 : fb b0 = none) (h1 : fb b = none)
    (h : ∀ y ∈ ys, ∀ x, fb y = some x → Seen TA H zs (x / 64)) : Cover TA fb H zs (b0 :: b :: ys) := by
  intro y hy x hx
  simp only [List.mem_cons] at hy
  rcases hy with rfl | rfl | hy
  · rw [h0] at hx; cases hx
  · rw [h1] at hx; cases hx
  · exact h y hy x hx

/-- Steps of both runs before a simulation step that does not stutter on `a`'s side alone. -/
theorem SimStepB.pre [HMono R] {H : Label → Prop} {a a1 : α} {b b1 : β} {xs : List α} {ys : List β}
    (pa : Path sa a a1 xs) (hxs : xs ≠ []) (pb : Path sb b b1 ys) (hys : ys ≠ []) (hc : Cover TA fb H xs ys)
    (h : SimStepB sa sb R Fin μ TA fb (Seen TA H xs) a1 b1) : SimStepB sa sb R Fin μ TA fb H a b := by
  rcases h with ⟨a', b', xs2, ys2, pa2, ha, pb2, hb, hf, hc2⟩ | ⟨a', b', xs2, ys2, pa2, hxs2, pb2, hys2, hr, hc2⟩ |
      ⟨b', ys2, pb2, hys2, hr, -, hc2⟩
  · refine .inl ⟨a', b', xs ++ xs2, ys ++ ys2, pa.append pa2, ha, pb.append pb2, hb, hf, ?_⟩
    have c1 := cover_zs (zs' := a' :: (xs ++ xs2)) hc (by intro z hz; simp [hz])
    have c2 := cover_up (zs' := a' :: (xs ++ xs2)) hc2 (by
      intro z hz; simp only [List.mem_append, List.mem_cons] at hz ⊢
      rcases hz with h | h | h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h))
    intro y hy x hx
    simp only [List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · exact c2 _ List.mem_cons_self x hx
    · exact c1 y hy x hx
    · exact c2 y (List.mem_cons_of_mem _ hy) x hx
  · refine .inr (.inl ⟨a', b', xs ++ xs2, ys ++ ys2, pa.append pa2, by simp [hxs], pb.append pb2, by simp [hys], ?_,
      Cover.append (cover_zs hc (by intro z hz; simp [hz])) (cover_up hc2 (by
        intro z hz; simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with h | h | h
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)))⟩)
    rwa [seen_app, seen_middle] at hr
  · exact .inr (.inl ⟨a1, b', xs, ys ++ ys2, pa, hxs, pb.append pb2, by simp [hys], HMono.mono (seen_sub fun z hz => List.mem_cons_of_mem _ hz) hr,
      Cover.append (cover_zs hc (by intro z hz; simp [hz])) (cover_up hc2 (by
        intro z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with h | h
        · exact .inr h
        · exact .inl h))⟩)

/-- A step of `a`'s run before a simulation step that does not stutter on `a`'s side alone. -/
theorem SimStepB.preSurf [HMono R] {H : Label → Prop} {a a1 : α} {b : β} (ea : sa a = some a1)
    (h : SimStepB sa sb R Fin μ TA fb (Seen TA H [a]) a1 b) : SimStepB sa sb R Fin μ TA fb H a b := by
  have hz : ∀ {zs : List α} {z : α}, z ∈ [a] ++ zs → z ∈ (zs.headD a) :: a :: zs.tail ∨ z ∈ zs := by
    intro zs z hz; simp at hz; rcases hz with rfl | h
    · simp
    · exact .inr h
  rcases h with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, hc⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr, hc⟩ |
      ⟨b', ys, pb, hys, hr, -, hc⟩
  · exact .inl ⟨a', b', a :: xs, ys, .cons ea pa, ha, pb, hb, hf, cover_up hc (by
      intro z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      rcases hz with h | h | h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h))⟩
  · refine .inr (.inl ⟨a', b', a :: xs, ys, .cons ea pa, by simp, pb, hys, by rwa [seen_cons, seen_swap] at hr, cover_up hc (by
      intro z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      rcases hz with h | h | h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h))⟩)
  · exact .inr (.inl ⟨a1, b', [a], ys, .cons ea (.nil _), by simp, pb, hys, HMono.mono (seen_sub fun z hz => List.mem_cons_of_mem _ hz) hr, cover_up hc (by
      intro z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      rcases hz with h | h
      · exact .inr h
      · exact .inl h)⟩)

/-- `b` and `bt` make the same step: a simulation step from `a ~ bt`, after a step of each run (from
`a0`, `b0`), is one from `a0 ~ b0`. -/
theorem SimStepB.preSwap [HMono R] {H : Label → Prop} {a0 a : α} {b0 b bt : β} (ea : sa a0 = some a) (eb : sb b0 = some b)
    (hst : sb b = sb bt) (hf0 : fb b0 = none) (hfb : fb b = none) (hfin : sb bt = none → ∀ a', Fin a' bt → Fin a' b)
    (h : SimStepB sa sb R Fin μ TA fb (Seen TA H [a0]) a bt) : SimStepB sa sb R Fin μ TA fb H a0 b0 := by
  have mem3 : ∀ {a' : α} {xs : List α} (z : α), z ∈ [a0] ++ a' :: xs → z ∈ a' :: a0 :: xs := by
    intro a' xs z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  rcases h with ⟨a', b'', xs, ys, pa, ha, pb, hb, hf, hc⟩ | ⟨a', b'', xs, ys, pa, hxs, pb, hys, hr, hc⟩ |
      ⟨b'', ys, pb, hys, hr, -, hc⟩
  · cases pb with
    | nil =>
      refine .inl ⟨a', b, a0 :: xs, [b0], .cons ea pa, ha, .cons eb (.nil _), by rw [hst]; exact hb, hfin hb a' hf, ?_⟩
      intro y hy x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · rw [hfb] at hx; cases hx
      · rw [hf0] at hx; cases hx
    | cons e p =>
      refine .inl ⟨a', b'', a0 :: xs, b0 :: b :: _, .cons ea pa, ha, .cons eb (.cons (hst.trans e) p), hb, hf, ?_⟩
      have c := cover_up hc mem3
      intro y hy x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact c _ List.mem_cons_self x hx
      · rw [hf0] at hx; cases hx
      · rw [hfb] at hx; cases hx
      · exact c y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)) x hx
  · cases pb with
    | nil => exact absurd rfl hys
    | cons e p =>
      refine .inr (.inl ⟨a', b'', a0 :: xs, b0 :: b :: _, .cons ea pa, by simp, .cons eb (.cons (hst.trans e) p), by simp,
        by rwa [seen_cons, seen_swap] at hr, cover_two hf0 hfb fun y hy x hx => cover_up hc mem3 y (List.mem_cons_of_mem _ hy) x hx⟩)
  · cases pb with
    | nil => exact absurd rfl hys
    | cons e p =>
      refine .inr (.inl ⟨a, b'', [a0], b0 :: b :: _, .cons ea (.nil _), by simp, .cons eb (.cons (hst.trans e) p), by simp,
        HMono.mono (seen_sub fun z hz => List.mem_cons_of_mem _ hz) hr, cover_two hf0 hfb fun y hy x hx => cover_up hc (by
          intro z hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with h | h
          · exact .inr h
          · exact .inl h) y (List.mem_cons_of_mem _ hy) x hx⟩)


variable (HS : ∀ H a b, R H a b → SimStep sa sb R Fin μ TA fb H a b)
include HS

/-- A terminating run of `a` gives a terminating run of `b`, with corresponding final configurations. -/
theorem sim_term_ab : ∀ (n : Nat) (H : Label → Prop) (a : α) (b : β), R H a b → sa (runF sa n a) = none →
    ∃ m, sb (runF sb m b) = none ∧ Fin (runF sa n a) (runF sb m b) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro H a b
  induction hμ : μ a b using Nat.strongRecOn generalizing H a b with
  | _ k ihk =>
  intro hr hn
  rcases HS H a b hr with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, -⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr', -⟩ |
      ⟨a', xs, pa, hxs, hr', hlt⟩ | ⟨b', ys, pb, hys, hr', hlt, -⟩
  · have h1 := pa.final ha hn
    exact ⟨ys.length, by rwa [pb.run], by rwa [h1, pb.run]⟩
  · have hle : xs.length ≤ n := Nat.le_of_not_lt fun hlt' => (pa.at n hlt').2 hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [runF_add, pa.run] at hn ⊢
    obtain ⟨m, hm, hf⟩ := ihn j (by have := len_pos hxs; omega) _ a' b' hr' hn
    exact ⟨ys.length + m, by rwa [runF_add, pb.run], by rwa [runF_add, pb.run]⟩
  · have hle : xs.length ≤ n := Nat.le_of_not_lt fun hlt' => (pa.at n hlt').2 hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [runF_add, pa.run] at hn ⊢
    exact ihn j (by have := len_pos hxs; omega) _ a' b hr' hn
  · obtain ⟨m, hm, hf⟩ := ihk _ (hμ ▸ hlt) H a b' rfl hr' hn
    exact ⟨ys.length + m, by rwa [runF_add, pb.run], by rwa [runF_add, pb.run]⟩

/-- A terminating run of `b` gives a terminating run of `a`, with corresponding final configurations. -/
theorem sim_term_ba : ∀ (m : Nat) (H : Label → Prop) (a : α) (b : β), R H a b → sb (runF sb m b) = none →
    ∃ n, sa (runF sa n a) = none ∧ Fin (runF sa n a) (runF sb m b) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro H a b
  induction hμ : μ a b using Nat.strongRecOn generalizing H a b with
  | _ k ihk =>
  intro hr hm
  rcases HS H a b hr with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, -⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr', -⟩ |
      ⟨a', xs, pa, hxs, hr', hlt⟩ | ⟨b', ys, pb, hys, hr', hlt, -⟩
  · have h1 := pb.final hb hm
    exact ⟨xs.length, by rwa [pa.run], by rwa [h1, pa.run]⟩
  · have hle : ys.length ≤ m := Nat.le_of_not_lt fun hlt' => (pb.at m hlt').2 hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [runF_add, pb.run] at hm ⊢
    obtain ⟨n, hn, hf⟩ := ihm j (by have := len_pos hys; omega) _ a' b' hr' hm
    exact ⟨xs.length + n, by rwa [runF_add, pa.run], by rwa [runF_add, pa.run]⟩
  · obtain ⟨n, hn, hf⟩ := ihk _ (hμ ▸ hlt) _ a' b rfl hr' hm
    exact ⟨xs.length + n, by rwa [runF_add, pa.run], by rwa [runF_add, pa.run]⟩
  · have hle : ys.length ≤ m := Nat.le_of_not_lt fun hlt' => (pb.at m hlt').2 hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [runF_add, pb.run] at hm ⊢
    exact ihm j (by have := len_pos hys; omega) H a b' hr' hm

/-- `a`'s run diverges iff `b`'s does. -/
theorem sim_div_ab : ∀ (m : Nat) (H : Label → Prop) (a : α) (b : β), R H a b → (∀ n, sa (runF sa n a) ≠ none) →
    sb (runF sb m b) ≠ none := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro H a b
  induction hμ : μ a b using Nat.strongRecOn generalizing H a b with
  | _ k ihk =>
  intro hr hd
  rcases HS H a b hr with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, -⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr', -⟩ |
      ⟨a', xs, pa, hxs, hr', hlt⟩ | ⟨b', ys, pb, hys, hr', hlt, -⟩
  · exact absurd (by rw [pa.run]; exact ha) (hd xs.length)
  · by_cases hlt' : m < ys.length
    · exact (pb.at m hlt').2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pb.run]
    refine ihm j (by have := len_pos hys; omega) _ a' b' hr' fun n => ?_
    have := hd (xs.length + n); rwa [runF_add, pa.run] at this
  · refine ihk _ (hμ ▸ hlt) _ a' b rfl hr' fun n => ?_
    have := hd (xs.length + n); rwa [runF_add, pa.run] at this
  · by_cases hlt' : m < ys.length
    · exact (pb.at m hlt').2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pb.run]
    exact ihm j (by have := len_pos hys; omega) H a b' hr' hd

theorem sim_div_ba : ∀ (n : Nat) (H : Label → Prop) (a : α) (b : β), R H a b → (∀ m, sb (runF sb m b) ≠ none) →
    sa (runF sa n a) ≠ none := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
  intro H a b
  induction hμ : μ a b using Nat.strongRecOn generalizing H a b with
  | _ k ihk =>
  intro hr hd
  rcases HS H a b hr with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, -⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr', -⟩ |
      ⟨a', xs, pa, hxs, hr', hlt⟩ | ⟨b', ys, pb, hys, hr', hlt, -⟩
  · exact absurd (by rw [pb.run]; exact hb) (hd ys.length)
  · by_cases hlt' : n < xs.length
    · exact (pa.at n hlt').2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pa.run]
    refine ihn j (by have := len_pos hxs; omega) _ a' b' hr' fun m => ?_
    have := hd (ys.length + m); rwa [runF_add, pb.run] at this
  · by_cases hlt' : n < xs.length
    · exact (pa.at n hlt').2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pa.run]
    exact ihn j (by have := len_pos hxs; omega) _ a' b hr' hd
  · refine ihk _ (hμ ▸ hlt) H a b' rfl hr' fun m => ?_
    have := hd (ys.length + m); rwa [runF_add, pb.run] at this

/-- Every node `b`'s run evaluates has its Surf node touched before (`H`) or by `a`'s run. -/
theorem sim_reach : ∀ (m : Nat) (H : Label → Prop) (a : α) (b : β) (x : Label), R H a b →
    fb (runF sb m b) = some x → H (x / 64) ∨ ∃ n, TA (runF sa n a) (x / 64) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro H a b x
  induction hμ : μ a b using Nat.strongRecOn generalizing H a b with
  | _ k ihk =>
  intro hr hx
  have onA : ∀ {a' : α} {xs : List α}, Path sa a a' xs → ∀ z ∈ a' :: xs, ∃ n, runF sa n a = z := by
    intro a' xs pa z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨xs.length, pa.run⟩
    · obtain ⟨i, -, h, -⟩ := pa.mem z hz; exact ⟨i, h⟩
  have seen : ∀ {a' : α} {xs zs : List α}, Path sa a a' xs → (∀ z ∈ zs, z ∈ a' :: xs) → ∀ l,
      Seen TA H zs l → H l ∨ ∃ n, TA (runF sa n a) l := by
    intro a' xs zs pa hz l hs
    rcases hs with h | ⟨z, hz', ht⟩
    · exact .inl h
    · obtain ⟨n, rfl⟩ := onA pa z (hz z hz'); exact .inr ⟨n, ht⟩
  have shift : ∀ {a' : α} {xs : List α}, Path sa a a' xs → ∀ l,
      (Seen TA H (a' :: xs) l ∨ ∃ n, TA (runF sa n a') l) → H l ∨ ∃ n, TA (runF sa n a) l := by
    intro a' xs pa l h
    rcases h with h | ⟨n, hn⟩
    · exact seen pa (fun z hz => hz) l h
    · exact .inr ⟨xs.length + n, by rwa [runF_add, pa.run]⟩
  rcases HS H a b hr with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, hc⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr', hc⟩ |
      ⟨a', xs, pa, hxs, hr', hlt⟩ | ⟨b', ys, pb, hys, hr', hlt, hc⟩
  · have hy : runF sb m b ∈ b' :: ys := by
      by_cases hlt' : m < ys.length
      · exact List.mem_cons_of_mem _ (pb.at m hlt').1
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
        rw [runF_add, pb.run, runF_stop hb]; exact List.mem_cons_self
    exact seen pa (fun z hz => hz) _ (hc _ hy x hx)
  · by_cases hlt' : m < ys.length
    · exact seen pa (fun z hz => hz) _ (hc _ (pb.at m hlt').1 x hx)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pb.run] at hx
    exact shift pa _ (ihm j (by have := len_pos hys; omega) _ a' b' x hr' hx)
  · exact shift pa _ (ihk _ (hμ ▸ hlt) _ a' b rfl hr' hx)
  · by_cases hlt' : m < ys.length
    · exact seen (.nil a) (fun z hz => hz) _ (hc _ (pb.at m hlt').1 x hx)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt')
    rw [runF_add, pb.run] at hx
    exact ihm j (by have := len_pos hys; omega) H a b' x hr' hx

end Sim

end Surf.T2
