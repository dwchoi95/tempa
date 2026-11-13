/-
(T2), `for … else`.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Loop

/-! ## A target's items

The items of a target's translation as an expression are items of its store (`tE` is the
expression's translation). -/

theorem pitemsB_app (R : PyCore.Edit) (C : List PyCore.Scope) :
    ∀ a b : PS, PyCore.itemsB R C (a ++ b) = PyCore.itemsB R C a ++ PyCore.itemsB R C b
  | [], _ => rfl
  | _ :: a, b => by simp [PyCore.itemsB, pitemsB_app R C a b]

theorem items_foldl (C' : List PyCore.Scope) (r : Label) : ∀ (es : List PE) (init : PE),
    PyCore.itemsE R0 C' (es.foldl (fun acc e => .bin r "," acc e) init) =
      PyCore.itemsE R0 C' init ++ es.flatMap (PyCore.itemsE R0 C')
  | [], init => by simp
  | e :: es, init => by simp [items_foldl C' r es, PyCore.itemsE]

theorem trA_eq (C : List Scope) : ∀ ts : List Expr, trA C ts = ts.map fun t => trE C (unstar t)
  | [] => rfl
  | t :: ts => by cases t <;> simp [trA, unstar, trA_eq C ts]

theorem trItems_cons (C : List Scope) (lt : Label) (i : Nat) (t : Expr) (ts : List Expr) :
    trItems C lt i (t :: ts) = trT C (itemSrc lt i) (unstar t) (trE C (unstar t)) ++ trItems C lt (i + 1) ts := by
  cases t <;> rfl

theorem tgtsOk_mem : ∀ {ts : List Expr}, tgtsOk ts = true → ∀ t ∈ ts, tgtOk (unstar t) = true
  | [], _, _, h => by simp at h
  | a :: ts, h, t, ht => by
    have h' : tgtOk (unstar a) = true ∧ tgtsOk ts = true := by cases a <;> simp_all [tgtsOk, unstar]
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h'.1
    · exact tgtsOk_mem h'.2 t ht

theorem sizeOf_unstar (t : Expr) : sizeOf (unstar t) ≤ sizeOf t := by
  cases t <;> simp [unstar] <;> omega

/-- A display's items: those of its elements. -/
theorem disp_items {C : List Scope} {lt : Label} {g : Py.Gadget} {ts : List Expr} {x : PyCore.Item}
    (hx : x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 g (trA C ts ++ ts.map starMark))) :
    ∃ t ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar t)) := by
  simp only [gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
    items_foldl, List.nil_append, trA_eq, List.flatMap_append, List.mem_append, List.mem_flatMap, List.mem_map] at hx
  rcases hx with ⟨_, ⟨t, ht, rfl⟩, hx⟩ | ⟨_, ⟨t, ht, rfl⟩, hx⟩
  · exact ⟨t, ht, hx⟩
  · cases t <;> simp [starMark, PyCore.itemsE] at hx

/-- The stores of an unpacking's targets hold each target's store. -/
theorem trItems_items {C : List Scope} {lt : Label} {x : PyCore.Item} :
    ∀ (i : Nat) (ts : List Expr) (t : Expr), t ∈ ts →
    (∀ j, x ∈ PyCore.itemsB R0 (trChain C) (trT C (itemSrc lt j) (unstar t) (trE C (unstar t)))) →
    x ∈ PyCore.itemsB R0 (trChain C) (trItems C lt i ts)
  | _, [], _, h, _ => by simp at h
  | i, a :: ts, t, ht, hx => by
    rw [trItems_cons, pitemsB_app, List.mem_append]
    rcases List.mem_cons.1 ht with rfl | ht
    · exact .inl (hx i)
    · exact .inr (trItems_items (i + 1) ts t ht hx)

theorem tgt_items {C : List Scope} : ∀ (tg : Expr) (src : Label → PE), tgtOk tg = true →
    ∀ x, x ∈ PyCore.itemsE R0 (trChain C) (trE C tg) →
      x ∈ PyCore.itemsB R0 (trChain C) (trT C src tg (trE C tg)) := by
  suffices h : ∀ n (tg : Expr), sizeOf tg < n → ∀ (src : Label → PE), tgtOk tg = true →
      ∀ x, x ∈ PyCore.itemsE R0 (trChain C) (trE C tg) →
        x ∈ PyCore.itemsB R0 (trChain C) (trT C src tg (trE C tg)) from
    fun tg => h _ tg (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro tg h; omega
  | succ n ih =>
    have hun : ∀ {lt} {ts : List Expr} {src : Label → PE}, sizeOf ts < n → tgtsOk ts = true → ∀ x,
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "tuple") (trA C ts ++ ts.map starMark)) ∨
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "list") (trA C ts ++ ts.map starMark)) →
        x ∈ PyCore.itemsB R0 (trChain C) [blk lt (.assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) ::
          trItems C lt 0 ts)] := by
      intro lt ts src hs hok x hx
      obtain ⟨t, ht, hx⟩ : ∃ t ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar t)) := by
        rcases hx with hx | hx <;> exact disp_items hx
      have hlt : sizeOf (unstar t) < n :=
        Nat.lt_of_le_of_lt (sizeOf_unstar t) (Nat.lt_trans (List.sizeOf_lt_of_mem ht) hs)
      have hi := trItems_items 0 ts t ht fun j => ih (unstar t) hlt (itemSrc lt j) (tgtsOk_mem hok t ht) x hx
      simp [blk, PyCore.itemsB, PyCore.itemsS, hi]
    intro tg hs src htg x hx
    cases tg with
    | name lt y => simp [trE, trT, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS] at hx ⊢; exact .inl hx
    | attr lt o a =>
      simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢; exact .inl hx
    | sub lt o i =>
      simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢
      rcases hx with h | h <;> simp [h]
    | tuple lt ts =>
      exact hun (by simp at hs; omega) (by simpa [tgtOk] using htg) x (.inl (by simpa [trE] using hx))
    | list lt ts =>
      exact hun (by simp at hs; omega) (by simpa [tgtOk] using htg) x (.inr (by simpa [trE] using hx))
    | _ => simp [tgtOk] at htg
theorem GoodB.rm {C : List Scope} {U : Label → Prop} {ss : List Stmt} {l : Label} (h : GoodB p C U ss)
    (hl : l ∉ labelsB ss) : GoodB p C (Rm U l) ss :=
  ⟨h.s, h.t, h.ok, fun l' hl' => ⟨h.u l' hl', fun e => hl (e ▸ hl')⟩, h.pv, h.nd, h.tch⟩


macro "loop_pin" : tactic => `(tactic| (simp [trB, trS, blk, forLoop, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs]))
macro "loop_gs" : tactic => `(tactic| (intro x hx; simp_all [itemsS, trS, PyCore.itemsS, PyCore.itemsB, PyCore.itemsHs,
  PyCore.itemsE, blk, forLoop, pitemsB_app, cc, ccR, recR, List.foldl]))
macro "loop_gs0" : tactic => `(tactic| (simp_all [itemsS, trS, PyCore.itemsS, PyCore.itemsB, PyCore.itemsHs,
  PyCore.itemsE, blk, forLoop, pitemsB_app, cc, ccR, recR, List.foldl]))
macro "loop_ge" : tactic => `(tactic| exact GoodB.e ‹_› (by loop_gs) (by loop_gs) (by gso) (by gsl) (by gsnd) (by gst))
macro "loop_gb" : tactic => `(tactic| exact GoodB.b ‹_› (by loop_gs) (by loop_gs) (by gso) (by gsl) (by gsnd) (by gst))

theorem fresh_ig (l : Label) : fresh "i" l ≠ fresh "g" l := by
  intro h; have := congrArg String.toList h; simp [fresh] at this

theorem fresh_gs (l : Label) : fresh "g" l ≠ fresh "s" l := by
  intro h; have := congrArg String.toList h; simp [fresh] at this

theorem fresh_iv (l : Label) : fresh "i" l ≠ fresh "v" l := by
  intro h; have := congrArg String.toList h; simp [fresh] at this

theorem fresh_gv (l : Label) : fresh "g" l ≠ fresh "v" l := by
  intro h; have := congrArg String.toList h; simp [fresh] at this

/-! ## PyCore's stores of the loop's fresh names

`pstore0` with the readings of every other name kept (the loop's iterator and flag are names of the
same node). -/

section Store
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem pstore1 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (v : Val) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ t1 g', PyCore.store t { f' with kont := k' } fs' (fresh tag l) v c' = some t1 ∧
      At0 p H s t1 f fs g' fs' ∧ g'.ctrl = c' ∧ g'.kont = k' ∧ rdOf t1 g' (fresh tag l) = some v ∧
      ∀ y, y ≠ fresh tag l → rdOf t1 g' y = rdOf t f' y ∧ ownOf t1 g' y = ownOf t f' y := by
  obtain ⟨t1, g', e, A1, h1, h2, hr, -⟩ := pstore0 A htag hfo v c' k'
  refine ⟨t1, g', e, A1, h1, h2, hr, fun y hy => ?_⟩
  have hs := A1.ht
  unfold PyCore.store at e; rw [pplace_kont] at e
  rcases fok_place A hfo with ⟨hq, hc, hk⟩ | ⟨hq, hc, hk⟩ | ⟨hq, hc, hk, hk'⟩ <;> rw [hq] at e <;> cases e <;>
    simp only [PyCore.writeAt, List.cons.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs
  all_goals refine rd_same (t := t) (h := f') (P := (· = fresh tag l)) ?_ ?_ ?_ ?_ ?_ ?_ y hy
  all_goals first
    | rfl
    | (intro _ z hz; simp only [PyCore.writeAt, pglob_ins]; rw [ite_ne]; exact fun e => hz e.symm)
    | (intro z hz; rfl)
    | (intro _ _ _; rfl)
    | (intro _ z hz; exact lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns (some v))
    | (intro z hz; simp only [PyCore.writeAt, Std.HashMap.getElem?_insert, beq_iff_eq]; rw [ite_ne]; intro e
       exact hz (congrArg Prod.snd e).symm)

theorem punset1 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ t1 g', PyCore.unsetThen t f' fs' (fresh tag l) c' k' = some t1 ∧
      At0 p H s t1 f fs g' fs' ∧ g'.ctrl = c' ∧ g'.kont = k' ∧
      ∀ y, y ≠ fresh tag l → rdOf t1 g' y = rdOf t f' y ∧ ownOf t1 g' y = ownOf t f' y := by
  obtain ⟨t1, g', e, A1, h1, h2, -⟩ := punset0 A htag hfo c' k'
  refine ⟨t1, g', e, A1, h1, h2, fun y hy => ?_⟩
  have hs := A1.ht
  unfold PyCore.unsetThen at e
  rcases fok_place A hfo with ⟨hq, hc, hk⟩ | ⟨hq, hc, hk⟩ | ⟨hq, hc, hk, hk'⟩ <;> rw [hq] at e <;> cases e <;>
    simp only [PyCore.writeAt, List.cons.injEq] at hs <;> obtain ⟨rfl, -⟩ := hs
  all_goals refine rd_same (t := t) (h := f') (P := (· = fresh tag l)) ?_ ?_ ?_ ?_ ?_ ?_ y hy
  all_goals first
    | rfl
    | (intro _ z hz; simp only [PyCore.writeAt, pglob_ins]; rw [ite_ne]; exact fun e => hz e.symm)
    | (intro z hz; rfl)
    | (intro _ _ _; rfl)
    | (intro _ z hz; exact lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns none)
    | (intro z hz; simp only [PyCore.writeAt, Std.HashMap.getElem?_erase, beq_iff_eq]; rw [ite_ne]; intro e
       exact hz (congrArg Prod.snd e).symm)

end Store

/-! ## One iteration's start in PyCore

From the loop's condition (`.g l`, true) to the core's `next` on the iterator (in `iv`): every node on the
way is made for the loop `l`. -/

theorem cv_next : Py.constVal I "$next" = .next := by simp [Py.constVal]

theorem loop_iter (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (l : Label)
    (iv : Name) (B U' : PS) (K : List (PyCore.Kont σ)) {it : Val}
    (hg : rdOf t f' (fresh "g" l) = some (.bool true)) (hi : rdOf t f' iv = some it) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .ev (.name (sub l 13) (fresh "g" l) none),
        kont := .whileS (.name (sub l 13) (fresh "g" l) none) [tryS l iv B] U' :: K } :: fs' }
      { t with stack := { f' with
        ctrl := .val it,
        kont := .callA .next :: nextK l iv B U' K } :: fs' } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l := by
  let ce : PE := .name (sub l 13) (fresh "g" l) none
  let ec : PE := .call (sub l 16) (.const (sub l 17) "$next") (.name (sub l 18) iv none)
  let Kv : List (PyCore.Kont σ) := .assign (fresh "v" l) :: .seq [] :: .tryE [stopH l] B :: .seq [] :: loopK l iv B U' :: K
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ := fun c k => { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  have r1 : PyCore.readName I (mk (.ev ce) (.whileS ce [tryS l iv B] U' :: K))
      { f' with ctrl := .ev ce, kont := .whileS ce [tryS l iv B] U' :: K } (fresh "g" l) none = .ok (.bool true) :=
    readName_rd hg
  have r2 : PyCore.readName I (mk (.ev (.name (sub l 18) iv none)) (.callA .next :: Kv))
      { f' with ctrl := .ev (.name (sub l 18) iv none), kont := .callA .next :: Kv } iv none = .ok it :=
    readName_rd hi
  have s1 : PyCore.step I (mk (.ev ce) (.whileS ce [tryS l iv B] U' :: K)) =
      some (mk (.val (.bool true)) (.whileS ce [tryS l iv B] U' :: K)) := by
    simp only [mk, PyCore.step, PyCore.evalStep, ce]; rw [r1]; rfl
  have s2 : PyCore.step I (mk (.val (.bool true)) (.whileS ce [tryS l iv B] U' :: K)) =
      some (mk (.val (.bool true)) (.whileT ce [tryS l iv B] U' :: K)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.tst, PyCore.top]
  have s3 : PyCore.step I (mk (.val (.bool true)) (.whileT ce [tryS l iv B] U' :: K)) =
      some (mk (.exec [tryS l iv B]) (.loop ce [tryS l iv B] U' :: K)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
  have s4 : PyCore.step I (mk (.exec [tryS l iv B]) (.loop ce [tryS l iv B] U' :: K)) =
      some (mk (.exec [.assign (sub l 15) (fresh "v" l) ec]) (.tryE [stopH l] B :: .seq [] :: loopK l iv B U' :: K)) := by
    simp [mk, PyCore.step, PyCore.execStep, PyCore.top, tryS, loopK, ce, ec]
  have s5 : PyCore.step I (mk (.exec [.assign (sub l 15) (fresh "v" l) ec]) (.tryE [stopH l] B :: .seq [] ::
      loopK l iv B U' :: K)) = some (mk (.ev ec) Kv) := by
    simp [mk, PyCore.step, PyCore.execStep, PyCore.top, Kv]
  have s6 : PyCore.step I (mk (.ev ec) Kv) =
      some (mk (.ev (.const (sub l 17) "$next")) (.callF (.name (sub l 18) iv none) :: Kv)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, ec]
  have s7 : PyCore.step I (mk (.ev (.const (sub l 17) "$next")) (.callF (.name (sub l 18) iv none) :: Kv)) =
      some (mk (.val .next) (.callF (.name (sub l 18) iv none) :: Kv)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, cv_next]
  have s8 : PyCore.step I (mk (.val .next) (.callF (.name (sub l 18) iv none) :: Kv)) =
      some (mk (.ev (.name (sub l 18) iv none)) (.callA .next :: Kv)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
  have s9 : PyCore.step I (mk (.ev (.name (sub l 18) iv none)) (.callA .next :: Kv)) =
      some (mk (.val it) (.callA .next :: Kv)) := by
    simp only [mk, PyCore.step, PyCore.evalStep]; rw [r2]; rfl
  refine ⟨_, .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.cons s6 (.cons s7 (.cons s8 (.cons s9 (.nil _))))))))),
    by simp, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mk, PyCore.focus, PyCore.Expr.label, PyCore.Stmt.label, ec, tryS] at hx <;>
    (rw [← hx]; exact sub_div _ _ (by omega))

/-! ## Signals passing PyCore items -/

/-- PyCore items an exception passes in one step. -/
def rPlain : PyCore.Kont σ → Bool
  | .tryE (_ :: _) _ | .catchS .. | .yfGot _ | .handler .. | .native _ => false
  | _ => true

/-- PyCore items a return passes in one step. -/
def vPlain : PyCore.Kont σ → Bool
  | .handler .. => false
  | _ => true

/-- PyCore items a `break` or `continue` passes in one step. -/
def bPlain : PyCore.Kont σ → Bool
  | .loop .. | .handler .. => false
  | _ => true

/-- The items a signal passes in one step. -/
def sPlain : PyCore.Ctrl σ → PyCore.Kont σ → Bool
  | .raise _ => rPlain
  | .retv _ => vPlain
  | .brk | .cont => bPlain
  | _ => fun _ => false

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem t_conf {c : PyCore.Ctrl σ} {K : List (PyCore.Kont σ)} (ht : t.stack = f' :: fs') (hc : f'.ctrl = c)
    (hk : f'.kont = K) : t = { t with stack := { f' with ctrl := c, kont := K } :: fs' } := by
  subst hc; subst hk; exact (t_eta ht).symm

/-- PyCore passes the items `P`, each in one step evaluating no node. -/
theorem ppop {c : PyCore.Ctrl σ} (Q : PyCore.Kont σ → Bool) (t : PyCore.Config σ) (f' : PyCore.Frame σ)
    (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    (hs : ∀ k R, Q k = true → PyCore.step I { t with stack := { f' with ctrl := c, kont := k :: R } :: fs' } =
      some { t with stack := { f' with ctrl := c, kont := R } :: fs' })
    (hf : ∀ R, PyCore.focus { t with stack := { f' with ctrl := c, kont := R } :: fs' } = none ∨
      ∃ k R', R = k :: R' ∧ Q k = false) :
    ∀ P : List (PyCore.Kont σ), P.all Q = true →
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c, kont := P ++ K } :: fs' }
      { t with stack := { f' with ctrl := c, kont := K } :: fs' } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none
  | [], _ => ⟨[], .nil _, rfl, by simp⟩
  | k :: P, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ys, py, hl, hy⟩ := ppop Q t f' fs' K hs hf P h.2
    refine ⟨_ :: ys, .cons (hs k (P ++ K) h.1) py, by simp [hl], ?_⟩
    intro y hy'
    rcases List.mem_cons.1 hy' with rfl | hy'
    · rcases hf (k :: (P ++ K)) with h' | ⟨k', R', e, hq⟩
      · exact h'
      · simp only [List.cons.injEq] at e; rw [e.1] at h; rw [h.1] at hq; cases hq
    · exact hy y hy'

theorem ppop_raise (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (v : Val)
    (K : List (PyCore.Kont σ)) (P : List (PyCore.Kont σ)) (h : P.all rPlain = true) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .raise v, kont := P ++ K } :: fs' }
      { t with stack := { f' with ctrl := .raise v, kont := K } :: fs' } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none := by
  refine ppop rPlain t f' fs' K (fun k R hk => ?_) (fun R => ?_) P h
  · cases k <;> simp [rPlain] at hk <;> try simp [PyCore.step, PyCore.raiseStep, PyCore.top]
    rename_i hs u; cases hs <;> simp at hk; simp
  · rcases R with _ | ⟨k, R⟩
    · exact .inl (by simp [PyCore.focus])
    · cases hq : rPlain k
      · exact .inr ⟨k, R, rfl, hq⟩
      · refine .inl ?_
        cases k <;> simp [rPlain] at hq <;> try simp [PyCore.focus]
        rename_i hs u; cases hs <;> simp at hq; simp

theorem ppop_ret (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (v : Val)
    (K : List (PyCore.Kont σ)) (P : List (PyCore.Kont σ)) (h : P.all vPlain = true) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .retv v, kont := P ++ K } :: fs' }
      { t with stack := { f' with ctrl := .retv v, kont := K } :: fs' } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none := by
  refine ppop vPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
  cases k <;> simp [vPlain] at hk <;> simp [PyCore.step, PyCore.retStep, PyCore.top]

theorem ppop_sig {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (hs : CSig i C U c c') (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ))
    (K P : List (PyCore.Kont σ)) (h : P.all (sPlain c') = true) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c', kont := P ++ K } :: fs' }
      { t with stack := { f' with ctrl := c', kont := K } :: fs' } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none := by
  rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact ppop_raise t f' fs' v K P h
  · exact ppop_ret t f' fs' v K P h
  · refine ppop bPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
    cases k <;> simp [bPlain] at hk <;> simp [PyCore.step, PyCore.brkStep, PyCore.top]
  · refine ppop bPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
    cases k <;> simp [bPlain] at hk <;> simp [PyCore.step, PyCore.contStep, PyCore.top]

/-- A signal passes the PyCore items `P` and the Surf item on top, to related configurations (at index
`false`: the rest of the loop's block). -/
theorem sig_popP (A : At p H s t f fs f' fs') {U U' : Label → Prop} {i : Bool} (hs : CSig i f.chain U f.ctrl f'.ctrl)
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (P : List (PyCore.Kont σ)) (hP : P ≠ [])
    (hk : KRel A.x U' false K0 K0') (hp : P.all (sPlain f'.ctrl) = true) (hK' : f'.kont = P ++ K0')
    (e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs }) (he : EnterSub K0 f.kont := by esub) :
    Goal I p H s t := by
  obtain ⟨ys, py, hl, hy⟩ := ppop_sig (I := I) hs t f' fs' K0' P hp
  have e := t_conf (c := f'.ctrl) A.ht rfl hK'
  have hr := crelI_seen (H := H) (zs := [s]) (A.set (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := K0')
    (csig_cr hs (fun _ => rfl) U') hk he)
  have hs' : { s with stack := { f with ctrl := f.ctrl, kont := K0 } :: fs } = { s with stack := { f with kont := K0 } :: fs } := rfl
  rw [hs'] at hr
  exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [e]; exact py)
    (by rintro rfl; exact hP (List.eq_nil_of_length_eq_zero hl.symm)) hr (cover_none hy)

end

/-! ## The loop's steps

These lemmas take the item they produce as a hypothesis (`hmk`); `val_loop`, `done_loop` and `sig_loop`
give it. -/

section Iter
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The iterator is made: PyCore stores it and the flag, enters the `while` and holds the iterator with
the call of `next`, where Surf calls `next` on it (`PendRel`). -/
theorem val_forStart' (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label}
    {tg : Expr} {b u : List Stmt} {Kb : List (Sem.Kont σ)} {Kt : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .forStart tg b u :: Kb)
    (hK' : f'.kont = .assign (fresh "i" l) ::
      .seq (forLoop l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg)) (trB f.chain b) (trB f.chain u)) :: Kt)
    (hH : H l) (hU : U l) (hf : FOks f.chain l ["i", "g", "v", "s"])
    (hmk : ∀ (rd own : Name → Option Val) (H' : Label → Prop), Agree U A.x.rd A.x.own rd own →
      (∀ l, H l → H' l) → rd (fresh "i" l) = some v → rd (fresh "g" l) = some (.bool true) →
      KRel ⟨p, f.chain, rd, own, H'⟩ (Rm U l) true (.forNext tg v b u :: Kb)
        (nextK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) (.seq [] :: Kt))) :
    Goal I p H s t := by
  let C := f.chain
  let B := trT C (forSrc l) tg (trE C tg) ++ trB C b
  let U' := trB C u
  let iv := fresh "i" l
  let ce : PE := .name (sub l 13) (fresh "g" l) none
  let W0 : PyCore.Stmt := .while (sub l 12) ce [tryS l iv B] U'
  let G0 : PyCore.Stmt := .assign (sub l 10) (fresh "g" l) (.const (sub l 11) "$true")
  obtain ⟨t1, g1, e1', A1, hg1c, hg1k, hr1, hp1⟩ :=
    pstore1 A.zero (by decide) (hf "i" (by simp)) v (.exec []) (.seq [G0, W0] :: Kt)
  have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e1'
  have hs1 := A1.ht
  let t2 : PyCore.Config σ := { t1 with stack := { g1 with ctrl := .exec [G0, W0], kont := Kt } :: fs' }
  have st2 : PyCore.step I t1 = some t2 := by
    rw [pstep_done hs1 hg1c]; simp [PyCore.doneStep, hg1k, PyCore.top, t2]
  let t3 : PyCore.Config σ := { t1 with stack := { g1 with
    ctrl := .ev (.const (sub l 11) "$true"), kont := .assign (fresh "g" l) :: .seq [W0] :: Kt } :: fs' }
  have st3 : PyCore.step I t2 = some t3 := by simp [t2, t3, PyCore.step, PyCore.execStep, PyCore.top, G0]
  let t4 : PyCore.Config σ := { t1 with stack := { g1 with
    ctrl := .val (.bool true), kont := .assign (fresh "g" l) :: .seq [W0] :: Kt } :: fs' }
  have st4 : PyCore.step I t3 = some t4 := by
    simp [t3, t4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  have A4 := A1.updT (.val (.bool true)) (.assign (fresh "g" l) :: .seq [W0] :: Kt)
  obtain ⟨t5, g5, e5, A5, hg5c, hg5k, hr5, hp5⟩ :=
    pstore1 A4 (by decide) (hf "g" (by simp)) (.bool true) (.exec []) (.seq [W0] :: Kt)
  have st5 : PyCore.step I t4 = some t5 := by rw [pstep_val rfl rfl]; exact e5
  let t6 : PyCore.Config σ := { t5 with stack := { g5 with ctrl := .exec [W0], kont := Kt } :: fs' }
  have st6 : PyCore.step I t5 = some t6 := by
    rw [pstep_done A5.ht hg5c]; simp [PyCore.doneStep, hg5k, PyCore.top, t6]
  let t7 : PyCore.Config σ := { t5 with stack := { g5 with
    ctrl := .ev ce, kont := .whileS ce [tryS l iv B] U' :: .seq [] :: Kt } :: fs' }
  have st7 : PyCore.step I t6 = some t7 := by simp [t6, t7, PyCore.step, PyCore.execStep, PyCore.top, W0]
  have hrg : rdOf t5 g5 (fresh "g" l) = some (.bool true) := hr5
  have hri : rdOf t5 g5 iv = some v := by rw [(hp5 _ (fresh_ig l)).1]; exact hr1
  obtain ⟨ys, py, hys, hfoc⟩ := loop_iter (I := I) t5 g5 fs' l iv B U' (.seq [] :: Kt) hrg hri
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .call .next [v] [], kont := .forNext tg v b u :: Kb } :: fs } := by
    simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
  have hH' : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have A8 := ((A5.updT (.val v) (.callA .next :: nextK l iv B U' (.seq [] :: Kt))).updS (.call .next [v] [])
    (.forNext tg v b u :: Kb)).mono_H hH'
  refine goal_b (.cons e1 (.nil _)) (by simp)
    (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 py))))))) (by simp)
    (pend_callA A8 (.inl rfl) rfl rfl rfl (hmk _ _ _ ?_ hH' hri hrg)) ?_
  · intro tag l' htag hl'
    have hne : l' ≠ l := fun e => hl' (e ▸ hU)
    obtain ⟨a5, b5⟩ := hp5 _ (fresh_ne htag (by decide) hne)
    obtain ⟨a1, b1⟩ := hp1 _ (fresh_ne htag (by decide) hne)
    exact ⟨a5.trans a1, b5.trans b1⟩
  · intro y hy x hx
    have hx' := pfocus_le hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx'
    · simp [PyCore.focus, hs1, hg1c] at hx'
    · simp [t2, PyCore.focus, G0, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
    · simp [t3, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
    · simp [t4, PyCore.focus] at hx'
    · simp [PyCore.focus, A5.ht, hg5c] at hx'
    · simp [t6, PyCore.focus, W0, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
    · rw [hfoc y hy x hx']; exact .inl hH

/-- The body ended, or `continue`: the loop's next iteration, PyCore holding the iterator with the call of
`next` (`PendRel`). -/
theorem next_forLoop' (A : At p H s t f fs f' fs') {U : Label → Prop} {it : Val} {l : Label}
    {tg : Expr} {b u : List Stmt} {Kb : List (Sem.Kont σ)} {Kt : List (PyCore.Kont σ)}
    (hc : (f.ctrl = .exec [] ∧ f'.ctrl = .exec []) ∨ (f.ctrl = .cont ∧ f'.ctrl = .cont))
    (hK : f.kont = .forLoop tg it b u :: Kb)
    (hK' : f'.kont = .seq [] ::
      loopK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) :: Kt)
    (hH : H l) (hi : A.x.rd (fresh "i" l) = some it) (hg : A.x.rd (fresh "g" l) = some (.bool true))
    (hmk : ∀ H' : Label → Prop, (∀ l, H l → H' l) →
      KRel ⟨p, f.chain, A.x.rd, A.x.own, H'⟩ U true (.forNext tg it b u :: Kb)
        (nextK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) Kt)) :
    Goal I p H s t := by
  let C := f.chain
  let B := trT C (forSrc l) tg (trE C tg) ++ trB C b
  let U' := trB C u
  let iv := fresh "i" l
  let ce : PE := .name (sub l 13) (fresh "g" l) none
  let c0 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev ce, kont := .whileS ce [tryS l iv B] U' :: Kt } :: fs' }
  have p0 : ∃ ys0, Path (PyCore.step I) t c0 ys0 ∧ ys0 ≠ [] ∧ ∀ y ∈ ys0, PyCore.focus y = none := by
    rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩
    · let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .exec [], kont := loopK l iv B U' :: Kt } :: fs' }
      exact ⟨[t, c1], .cons (by rw [pstep_done A.ht h2]; simp [PyCore.doneStep, hK', PyCore.top, c1, iv, B, U', C])
        (.cons (by simp [c1, c0, ce, PyCore.step, PyCore.doneStep, loopK, PyCore.top]) (.nil _)), by simp,
        by simp [PyCore.focus, A.ht, h2, c1]⟩
    · let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .cont, kont := loopK l iv B U' :: Kt } :: fs' }
      exact ⟨[t, c1], .cons (by rw [pstep_cont A.ht h2]; simp [PyCore.contStep, hK', PyCore.top, c1, h2, iv, B, U', C])
        (.cons (by simp [c1, c0, ce, PyCore.step, PyCore.contStep, loopK, PyCore.top]) (.nil _)), by simp,
        by simp [PyCore.focus, A.ht, h2, c1]⟩
  obtain ⟨ys0, p0, hys0, hf0⟩ := p0
  obtain ⟨ys, py, hys, hfoc⟩ := loop_iter (I := I) t f' fs' l iv B U' Kt hg hi
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .call .next [it] [], kont := .forNext tg it b u :: Kb } :: fs } := by
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · simp [Sem.step, A.hs, h1, hK, Sem.doneStep, Sem.setC]
    · simp [Sem.step, A.hs, h1, hK, Sem.contStep, Sem.setC]
  have hH' : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have A8 := ((A.zero.updT (.val it) (.callA .next :: nextK l iv B U' Kt)).updS (.call .next [it] [])
    (.forNext tg it b u :: Kb)).mono_H hH'
  refine goal_b (.cons e1 (.nil _)) (by simp) (p0.append py) (by simp [hys0])
    (pend_callA A8 (.inl rfl) rfl rfl rfl (hmk _ hH')) ?_
  intro y hy x hx
  have hx' := pfocus_le hx
  rcases List.mem_append.1 hy with hy | hy
  · rw [hf0 y hy] at hx'; cases hx'
  · rw [hfoc y hy x hx']; exact .inl hH

/-- The iterator's next item: PyCore keeps it in `.v l` and leaves the `try`; both store it into the
target, then run the body. -/
theorem val_forNext' (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v it : Val} {l : Label}
    {tg : Expr} {b u : List Stmt} {Kb : List (Sem.Kont σ)} {Kt : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .forNext tg it b u :: Kb)
    (hK' : f'.kont = nextK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) Kt)
    (hU : ¬ U l) (hn : NoCompH f.chain) (hfv : FOk f.chain (fresh "v" l))
    (g1 : GoodE p f.chain U tg) (g2 : GoodB p f.chain U b)
    (hT : SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain (forSrc l) tg (trE f.chain tg))) (PI p))
    (hmk : ∀ (rd own : Name → Option Val) (H' : Label → Prop), (∀ l, H l → H' l) →
      (∀ y, y ≠ fresh "v" l → rd y = A.x.rd y ∧ own y = A.x.own y) →
      KRel ⟨p, f.chain, rd, own, H'⟩ U false (.forLoop tg it b u :: Kb)
        (.seq [] :: loopK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) :: Kt)) :
    Goal I p H s t := by
  let C := f.chain
  let B := trT C (forSrc l) tg (trE C tg) ++ trB C b
  let Kl : List (PyCore.Kont σ) := .seq [] :: loopK l (fresh "i" l) B (trB C u) :: Kt
  obtain ⟨t1, g1', e1', A1, hg1c, hg1k, hr1, hp1⟩ :=
    pstore1 A.zero (by decide) hfv v (.exec []) (.seq [] :: .tryE [stopH l] B :: Kl)
  have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e1'
  let t2 : PyCore.Config σ := { t1 with stack := { g1' with ctrl := .exec [], kont := .tryE [stopH l] B :: Kl } :: fs' }
  have st2 : PyCore.step I t1 = some t2 := by
    rw [pstep_done A1.ht hg1c]; simp [PyCore.doneStep, hg1k, PyCore.top, t2]
  let t3 : PyCore.Config σ := { t1 with stack := { g1' with ctrl := .exec B, kont := Kl } :: fs' }
  have st3 : PyCore.step I t2 = some t3 := by simp [t2, t3, PyCore.step, PyCore.doneStep, PyCore.top]
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .store tg v, kont := .seq b :: .forLoop tg it b u :: Kb } :: fs } := by
    simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
  have hH' : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have A3 := ((A1.updT (.exec B) Kl).updS (.store tg v) (.seq b :: .forLoop tg it b u :: Kb)).mono_H hH'
  refine SimStep.pre e1 (.cons st1 (.cons st2 (.cons st3 (.nil _)))) (by simp) ?_
    (store_sim tg A3 W rfl rfl g1 hT (.name (by omega) (by decide) hU hr1)
      (.core (.seq (pre := []) (fun _ => hn) (.inl rfl) g2 (hmk _ _ _ hH' hp1))))
  intro y hy x hx
  have hx' := pfocus_le hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · simp [PyCore.focus, A.ht, hc'] at hx'
  · simp [PyCore.focus, A1.ht, hg1c] at hx'
  · simp [t2, PyCore.focus] at hx'

/-- The iterator is exhausted: PyCore's handler clears the flag, the `while` ends and runs the loop's
`else` block, inside the statement's block (`Kt`, which `hmk` relates to the rest). -/
theorem stop_forNext' (A : At p H s t f fs f' fs') {U0 : Label → Prop} {v it : Val} {l : Label}
    {tg : Expr} {b u : List Stmt} {Kb : List (Sem.Kont σ)} {Kt : List (PyCore.Kont σ)}
    (hc : f.ctrl = .raise v) (hc' : f'.ctrl = .raise v) (hst : Py.isStop v = true)
    (hK : f.kont = .forNext tg it b u :: Kb)
    (hK' : f'.kont = nextK l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg) ++ trB f.chain b) (trB f.chain u) Kt)
    (hH : H l) (hU : U0 l) (hn : NoCompH f.chain) (hf : FOks f.chain l ["g", "v", "s"])
    (g3 : GoodB p f.chain U0 u)
    (hmk : ∀ (rd own : Name → Option Val) (H' : Label → Prop), Agree U0 A.x.rd A.x.own rd own →
      (∀ l, H l → H' l) → KRel ⟨p, f.chain, rd, own, H'⟩ U0 false Kb Kt) :
    Goal I p H s t := by
  let C := f.chain
  let B := trT C (forSrc l) tg (trE C tg) ++ trB C b
  let U' := trB C u
  let iv := fresh "i" l
  let ce : PE := .name (sub l 13) (fresh "g" l) none
  let Kl : List (PyCore.Kont σ) := .seq [] :: loopK l iv B U' :: Kt
  let hb : PS := [.assign (sub l 21) (fresh "g" l) (.const (sub l 22) "$false")]
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise v, kont := .tryE [stopH l] B :: Kl } :: fs' }
  let c3 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev (.const (sub l 20) "$stop"), kont := .catchS v (fresh "s" l) hb [] B :: Kl } :: fs' }
  let c4 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .val (.bool true), kont := .catchT v (fresh "s" l) hb [] B :: Kl } :: fs' }
  obtain ⟨ys1, p1, -, hy1⟩ := ppop_raise (I := I) t f' fs' v (.tryE [stopH l] B :: Kl) [.assign (fresh "v" l), .seq []] rfl
  have hst' : PyCore.isStop v = true := by simpa [PyCore.isStop] using hst
  have s3 : PyCore.step I c2 = some c3 := by simp [c2, c3, PyCore.step, PyCore.raiseStep, PyCore.top, stopH, hb]
  have s4 : PyCore.step I c3 = some c4 := by
    simp [c3, c4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, hst']
  -- the handler's name
  obtain ⟨t5, g5, e5, A5, hg5c, hg5k, -, hp5⟩ := pstore1 (A.zero.updT (.val (.bool true))
    (.catchT v (fresh "s" l) hb [] B :: Kl)) (by decide) (hf "s" (by simp)) v (.exec hb) (.handler (fresh "s" l) v :: Kl)
  have s5 : PyCore.step I c4 = some t5 := by rw [pstep_val rfl rfl]; exact e5
  let Kh : List (PyCore.Kont σ) := .handler (fresh "s" l) v :: Kl
  let c6 : PyCore.Config σ := { t5 with stack := { g5 with
    ctrl := .ev (.const (sub l 22) "$false"), kont := .assign (fresh "g" l) :: .seq [] :: Kh } :: fs' }
  have s6 : PyCore.step I t5 = some c6 := by
    rw [pstep_exec A5.ht (by rw [hg5c])]; simp [PyCore.execStep, PyCore.top, hg5k, c6, Kh]
  let c7 : PyCore.Config σ := { t5 with stack := { g5 with
    ctrl := .val .no, kont := .assign (fresh "g" l) :: .seq [] :: Kh } :: fs' }
  have s7 : PyCore.step I c6 = some c7 := by
    simp [c6, c7, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  -- the flag cleared
  obtain ⟨t8, g8, e8, A8, hg8c, hg8k, hr8, hp8⟩ := pstore1 (A5.updT (.val .no)
    (.assign (fresh "g" l) :: .seq [] :: Kh)) (by decide) (hf "g" (by simp)) .no (.exec []) (.seq [] :: Kh)
  have s8 : PyCore.step I c7 = some t8 := by rw [pstep_val rfl rfl]; exact e8
  let c9 : PyCore.Config σ := { t8 with stack := { g8 with ctrl := .exec [], kont := Kh } :: fs' }
  have s9 : PyCore.step I t8 = some c9 := by rw [pstep_done A8.ht hg8c]; simp [PyCore.doneStep, hg8k, PyCore.top, c9]
  -- the handler's exit
  obtain ⟨t10, g10, e10, A10, hg10c, hg10k, hp10⟩ :=
    punset1 (A8.updT (.exec []) Kh) (by decide) (hf "s" (by simp)) (.exec []) Kl
  have s10 : PyCore.step I c9 = some t10 := by
    rw [pstep_done rfl rfl]; simp only [PyCore.doneStep, Kh]; exact e10
  let c11 : PyCore.Config σ := { t10 with stack := { g10 with ctrl := .exec [], kont := loopK l iv B U' :: Kt } :: fs' }
  have s11 : PyCore.step I t10 = some c11 := by
    rw [pstep_done A10.ht hg10c]; simp [PyCore.doneStep, hg10k, PyCore.top, c11, Kl]
  let c12 : PyCore.Config σ := { t10 with stack := { g10 with
    ctrl := .ev ce, kont := .whileS ce [tryS l iv B] U' :: Kt } :: fs' }
  have s12 : PyCore.step I c11 = some c12 := by simp [c11, c12, PyCore.step, PyCore.doneStep, PyCore.top, loopK, ce]
  have hrg : rdOf t10 g10 (fresh "g" l) = some .no := by rw [(hp10 _ (fresh_gs l)).1]; exact hr8
  let c13 : PyCore.Config σ := { t10 with stack := { g10 with
    ctrl := .val .no, kont := .whileS ce [tryS l iv B] U' :: Kt } :: fs' }
  have s13 : PyCore.step I c12 = some c13 := by
    have r : PyCore.readName I c12 { g10 with ctrl := .ev ce, kont := .whileS ce [tryS l iv B] U' :: Kt }
      (fresh "g" l) none = .ok .no := readName_rd hrg
    simp only [c12, c13, PyCore.step, PyCore.evalStep, ce]; rw [r]; rfl
  let c14 : PyCore.Config σ := { t10 with stack := { g10 with
    ctrl := .val (.bool false), kont := .whileT ce [tryS l iv B] U' :: Kt } :: fs' }
  have s14 : PyCore.step I c13 = some c14 := by simp [c13, c14, PyCore.step, PyCore.valStep, PyCore.tst, PyCore.top]
  have s15 : PyCore.step I c14 = some { t10 with stack := { g10 with ctrl := .exec U', kont := Kt } :: fs' } := by
    simp [c14, PyCore.step, PyCore.valStep, PyCore.top]
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec u, kont := Kb } :: fs } := by
    simp [Sem.step, A.hs, hc, hK, Sem.raiseStep, Sem.setC, hst]
  have hH' : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have A15 := ((A10.updT (.exec U') Kt).updS (.exec u) Kb).mono_H hH'
  have e := t_conf (c := .raise v) A.ht hc' hK'
  have hag : Agree U0 A.x.rd A.x.own (rdOf t10 g10) (ownOf t10 g10) := by
    intro tag l' htag hl'
    have hne : l' ≠ l := fun e => hl' (e ▸ hU)
    obtain ⟨a10, b10⟩ := hp10 _ (fresh_ne htag (by decide) hne)
    obtain ⟨a8, b8⟩ := hp8 _ (fresh_ne htag (by decide) hne)
    obtain ⟨a5, b5⟩ := hp5 _ (fresh_ne htag (by decide) hne)
    exact ⟨a10.trans (a8.trans a5), b10.trans (b8.trans b5)⟩
  refine goal_b (.cons e1 (.nil _)) (by simp)
    (by rw [e]; exact p1.append (.cons s3 (.cons s4 (.cons s5 (.cons s6 (.cons s7 (.cons s8 (.cons s9 (.cons s10
      (.cons s11 (.cons s12 (.cons s13 (.cons s14 (.cons s15 (.nil _)))))))))))))))
    (by simp) (.inl (A15.crel (U := U0) (i := false) (.exec g3 fun _ => hn) (hmk _ _ _ hag hH'))) ?_
  intro y hy x hx
  have hx' := pfocus_le hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hy1 y hy] at hx'; cases hx'
  · simp [PyCore.focus, stopH] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · simp [c3, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · simp [c4, PyCore.focus] at hx'
  · simp [PyCore.focus, A5.ht, hg5c, hb, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · simp [c6, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · simp [c7, PyCore.focus] at hx'
  · simp [PyCore.focus, A8.ht, hg8c] at hx'
  · simp [c9, PyCore.focus] at hx'
  · simp [PyCore.focus, A10.ht, hg10c] at hx'
  · simp [c11, PyCore.focus] at hx'
  · simp [c12, PyCore.focus, PyCore.Expr.label, ce] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · simp [c13, PyCore.focus] at hx'
  · simp [c14, PyCore.focus] at hx'

/-- Any other exception meets the loop's `next`: it passes the loop's handler and the loop. -/
theorem raise_forNext (A : At p H s t f fs f' fs') {U : Label → Prop} {K0 : List (Sem.Kont σ)}
    {Kt : List (PyCore.Kont σ)} {l : Label} {tg : Expr} {it v : Val} {b u : List Stmt}
    (hK : f.kont = .forNext tg it b u :: K0)
    (hK' : f'.kont = nextK l (fresh "i" l) (trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b) (trB A.x.C u) Kt)
    (h1 : f.ctrl = .raise v) (h2 : f'.ctrl = .raise v) (hst : Py.isStop v = false) (hH : A.x.H l)
    (k : KRel A.x U false K0 Kt) : Goal I p H s t := by
  let B := trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b
  let Kl : List (PyCore.Kont σ) := .seq [] :: loopK l (fresh "i" l) B (trB A.x.C u) :: Kt
  let hb : PS := [.assign (sub l 21) (fresh "g" l) (.const (sub l 22) "$false")]
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise v, kont := .tryE [stopH l] B :: Kl } :: fs' }
  let c3 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev (.const (sub l 20) "$stop"), kont := .catchS v (fresh "s" l) hb [] B :: Kl } :: fs' }
  let c4 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .val (.bool false), kont := .catchT v (fresh "s" l) hb [] B :: Kl } :: fs' }
  let c5 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise v, kont := .tryE [] B :: Kl } :: fs' }
  obtain ⟨ys1, p1, -, hy1⟩ := ppop_raise (I := I) t f' fs' v (.tryE [stopH l] B :: Kl) [.assign (fresh "v" l), .seq []] rfl
  obtain ⟨ys2, p2, -, hy2⟩ := ppop_raise (I := I) t f' fs' v Kt [.tryE [] B, .seq [],
    loopK l (fresh "i" l) B (trB A.x.C u)] rfl
  have hst' : PyCore.isStop v = false := by simpa [PyCore.isStop] using hst
  have s3 : PyCore.step I c2 = some c3 := by simp [c2, c3, PyCore.step, PyCore.raiseStep, PyCore.top, stopH, hb]
  have s4 : PyCore.step I c3 = some c4 := by
    simp [c3, c4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, hst']
  have s5 : PyCore.step I c4 = some c5 := by simp [c4, c5, PyCore.step, PyCore.valStep, PyCore.top]
  have e := t_conf (c := .raise v) A.ht h2 hK'
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise v, kont := K0 } :: fs } := by
    simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC, hst]
  refine goal_b (.cons e1 (.nil _)) (by simp)
    (by rw [e]; exact p1.append (.cons s3 (.cons s4 (.cons s5 p2)))) (by simp)
    (crelI_seen (A.set .raise k (esub_cons hK))) ?_
  intro y hy x hx
  simp only [List.mem_append, List.mem_cons] at hy
  have hx' := pfocus_le hx
  rcases hy with hy | hy | hy | hy | hy
  · rw [hy1 y hy] at hx'; cases hx'
  · subst hy; simp [PyCore.focus, stopH] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · subst hy; simp [c3, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact .inl hH
  · subst hy; simp [c4, PyCore.focus] at hx'
  · rw [hy2 y hy] at hx'; cases hx'

/-- `break` leaves the loop: its `else` block is skipped. -/
theorem brk_forLoop (A : At p H s t f fs f' fs') {U : Label → Prop} {K0 : List (Sem.Kont σ)}
    {Kt : List (PyCore.Kont σ)} {l : Label} {tg : Expr} {it : Val} {b u : List Stmt}
    (hK : f.kont = .forLoop tg it b u :: K0)
    (hK' : f'.kont = .seq [] :: loopK l (fresh "i" l) (trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b) (trB A.x.C u) :: Kt)
    (h1 : f.ctrl = .brk) (h2 : f'.ctrl = .brk) (k : KRel A.x U false K0 Kt) : Goal I p H s t := by
  let Kl : List (PyCore.Kont σ) := loopK l (fresh "i" l) (trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b) (trB A.x.C u) :: Kt
  let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .brk, kont := Kl } :: fs' }
  have s1 : PyCore.step I t = some c1 := by rw [pstep_brk A.ht h2]; simp [PyCore.brkStep, hK', PyCore.top, c1, Kl, h2]
  have s2 : PyCore.step I c1 = some { t with stack := { f' with ctrl := .exec [], kont := Kt } :: fs' } := by
    simp [c1, Kl, PyCore.step, PyCore.brkStep, loopK, PyCore.top]
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
    simp [Sem.step, A.hs, h1, hK, Sem.brkStep, Sem.setC]
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons s1 (.cons s2 (.nil _))) (by simp)
    (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) k)) (cover_none fun y hy => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, h2, c1]

end Iter

set_option hygiene false in
macro "loop_spop" : tactic => `(tactic| (rcases hsig with ⟨_, h1, -⟩ | ⟨_, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩ <;>
  simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]))
set_option hygiene false in
macro "loop_splain" : tactic => `(tactic| (rcases hsig with ⟨_, -, h2⟩ | ⟨_, -, h2⟩ | ⟨_, _, -, h2⟩ | ⟨_, _, -, h2⟩ <;>
  rw [h2] <;> rfl))

end Loop

open Loop

theorem exec_for (l tg it b u) : ExecCase I p (.for l tg it b u) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hn : NoCompH f.chain := hnc (by simp)
  obtain ⟨hlt, hlb⟩ := for_lbl hg
  have htg : tgtOk tg = true := by
    have := hg.ok; simp only [okB, okS, Bool.and_eq_true] at this; exact this.1.1.1.1.2
  have g1 : GoodE p f.chain U it := by loop_ge
  have g2 : GoodE p f.chain (Rm U l) tg := GoodE.rm (GoodB.e hg (by loop_gs)
    (fun x hx => by have := tgt_items (C := f.chain) tg (forSrc l) htg x hx; loop_gs0) (by gso) (by gsl)
    (by gsnd) (by gst)) hlt
  have g3 : GoodB p f.chain (Rm U l) b := GoodB.rm (by loop_gb) hlb
  have g4 : GoodB p f.chain U u := by loop_gb
  have hUl : U l := hg.u l (by simp [labelsB, labelsS])
  -- the PyCore items of the target's store
  have hT : SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain (forSrc l) tg (trE f.chain tg))) (PI p) :=
    fun x hx => hg.t x (by simp [trB, trS, blk, forLoop, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs, pitemsB_app, hx])
  have hfo : FOks f.chain l ["i", "g", "v", "s"] := by
    intro tag htag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htag
    rcases htag with rfl | rfl | rfl | rfl
    · exact fok_of W (L := sub l 1) (hg.t _ (by loop_pin)) ⟨_, _, rfl⟩ (not_cmp l 1 (by omega) (by omega) (by omega))
    · exact fok_of W (L := sub l 10) (hg.t _ (by loop_pin)) ⟨_, _, rfl⟩ (not_cmp l 10 (by omega) (by omega) (by omega))
    · exact fok_of W (L := sub l 15) (hg.t _ (by loop_pin)) ⟨_, _, rfl⟩ (not_cmp l 15 (by omega) (by omega) (by omega))
    · exact fok_of W (L := sub l 19) (hg.t _ (by loop_pin)) ⟨_, _, rfl⟩ (not_cmp l 19 (by omega) (by omega) (by omega))
  let C := f.chain
  let FL := forLoop l (fresh "i" l) (trT C (forSrc l) tg (trE C tg)) (trB C b) (trB C u)
  let A1 : PyCore.Stmt := .assign (sub l 1) (fresh "i" l) (cc l 2 "$op:iter" [trE C it])
  let K2 : List (PyCore.Kont σ) := .assign (fresh "i" l) :: .seq FL :: .tryE [] [] :: .seq (trB C ss) :: f'.kont
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 2) "$op:iter" (trE C it) [] K2
  rw [kc_iter I] at pc
  have hc2 : f'.ctrl = .exec (blk l (A1 :: FL) :: trB C ss) := by rw [hc']; rfl
  have st1 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .exec (A1 :: FL), kont := .tryE [] [] :: .seq (trB C ss) :: f'.kont } :: fs' } := by
    rw [pstep_exec A.ht hc2]; rfl
  have st2 : PyCore.step I { t with stack := { f' with
      ctrl := .exec (A1 :: FL), kont := .tryE [] [] :: .seq (trB C ss) :: f'.kont } :: fs' } =
      some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) "$op:iter" [trE C it]), kont := K2 } :: fs' } := by
    rw [pstep_exec rfl rfl]; rfl
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .ev it, kont := .forIt tg b u :: .seq ss :: f.kont } :: fs } := by estep
  have ht : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  have hH : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 pc)) (by simp)
    (.inl (((A.zero.upd (.ev it) (.forIt tg b u :: .seq ss :: f.kont) (.ev (trE C it))
      (recK [] [] (.callA (.op .iter) :: K2))).mono_H hH).crel (U := U) (i := true) (.ev g1)
      (.loop (.forIt hn (seen_s (by simp) ht) hUl hfo g2 htg hT g3 g4 hg.tail (KRel.ext ⟨hH, Agree.refl _ _ _⟩ hk)))))
    (cover_of (l := l) (by simp) ht ?_)
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A.ht, hc2, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A1, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

theorem val_loop : KCase I p true LoopK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @forIt U K0 K0' l tg b u ss hn hH hU hf g1 ho hT g2 g3 g4 k =>
    let K1' : List (PyCore.Kont σ) := .assign (fresh "i" l) ::
      .seq (forLoop l (fresh "i" l) (trT f.chain (forSrc l) tg (trE f.chain tg)) (trB f.chain b) (trB f.chain u)) :: .tryE [] [] ::
      .seq (trB f.chain ss) :: K0'
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op .iter [v], kont := .forStart tg b u :: .seq ss :: K0 } :: fs } := by sstep
    have st1 : PyCore.step I t = some { t with stack := { f' with
        ctrl := .val (.data "$args" [v]), kont := .callA (.op .iter) :: K1' } :: fs' } := by
      rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', recK, PyCore.top, K1']
    have st2 : PyCore.step I { t with stack := { f' with
        ctrl := .val (.data "$args" [v]), kont := .callA (.op .iter) :: K1' } :: fs' } =
        some { t with stack := { f' with ctrl := .op .iter [v], kont := K1' } :: fs' } := by
      simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
      (crelI_seen (A.set .op (.loop (.forStart hn hH hU hf g1 ho hT g2 g3 g4 k))))
      (cover_none fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc'])
  | @forStart U K0 K0' l tg b u ss hn hH hU hf g1 ho hT g2 g3 g4 k =>
    exact val_forStart' A hc hc' hK hK' hH hU hf fun rd own H' ha hH' hri hrg =>
      .loop (.forNext hn (hH' l hH) hU hri hrg (fun tag ht => hf tag (List.mem_cons_of_mem _ ht)) g1 ho hT g2 g3 g4
        (KRel.ext ⟨hH', ha⟩ k))
  | @forNext U K0 K0' l tg it b u ss hn hH hU hi hg hf g1 ho hT g2 g3 g4 k =>
    exact val_forNext' A W hc hc' hK hK' (rm_self U l) hn (hf "v" (by simp)) g1 g2 hT
      fun rd own H' hH' hrd =>
      .loop (.forLoop hn (hH' l hH) hU ((hrd _ (fresh_iv l)).1.trans hi) ((hrd _ (fresh_gv l)).1.trans hg) hf g1 ho hT g2 g3 g4
        (KRel.ext ⟨hH', fun tag l' htag hl' => hrd _ (fresh_ne htag (by decide) fun e => hl' (e ▸ hU))⟩ k))

theorem done_loop : KCase I p false LoopK CDone := by
  intro H s t f fs f' fs' U A W ⟨hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @forLoop U K0 K0' l tg it b u ss hn hH hU hi hg hf g1 ho hT g2 g3 g4 k =>
    exact next_forLoop' A (.inl ⟨hc, hc'⟩) hK hK' hH hi hg fun H' hH' =>
      .loop (.forNext hn (hH' l hH) hU hi hg hf g1 ho hT g2 g3 g4 (KRel.ext ⟨hH', Agree.refl _ _ _⟩ k))

theorem sig_loop {i : Bool} : KCase I p i LoopK CSig := by
  intro H s t f fs f' fs' U A W hsig hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @forIt U K0 K0' l tg b u ss hn hH hU hf g1 ho hT g2 g3 g4 k =>
    let P : List (PyCore.Kont σ) := [.binR "," (.data "$args" []), .callA (.op .iter), .assign (fresh "i" l),
      .seq (forLoop l (fresh "i" l) (trT A.x.C (forSrc l) tg (trE A.x.C tg)) (trB A.x.C b) (trB A.x.C u))]
    exact sig_popP A hsig P (by simp [P]) (.core (.seq (pre := [.tryE [] []]) (fun _ => hn) (.inr (.inl rfl)) g4 k))
      (by loop_splain) (by rw [hK']; rfl) (by loop_spop)
  | @forStart U K0 K0' l tg b u ss hn hH hU hf g1 ho hT g2 g3 g4 k =>
    let P : List (PyCore.Kont σ) := [.assign (fresh "i" l),
      .seq (forLoop l (fresh "i" l) (trT A.x.C (forSrc l) tg (trE A.x.C tg)) (trB A.x.C b) (trB A.x.C u))]
    exact sig_popP A hsig P (by simp [P]) (.core (.seq (pre := [.tryE [] []]) (fun _ => hn) (.inr (.inl rfl)) g4 k))
      (by loop_splain) (by rw [hK']; rfl) (by loop_spop)
  | @forNext U K0 K0' l tg it b u ss hn hH hU hi hg hf g1 ho hT g2 g3 g4 k =>
    let B := trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b
    have k' : KRel A.x U false (.seq ss :: K0) (.seq [] :: .tryE [] [] :: .seq (trB A.x.C ss) :: K0') :=
      .core (.seq (pre := [.seq [], .tryE [] []]) (fun _ => hn) (.inr (.inr rfl)) g4 k)
    rcases hsig with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨hi', -⟩ | ⟨hi', -⟩
    · cases hst : Py.isStop v
      · exact raise_forNext A hK hK' h1 h2 hst hH k'
      · exact stop_forNext' A h1 h2 hst hK hK' hH hU hn hf g3 fun rd own H' ha hH' => KRel.ext ⟨hH', ha⟩ k'
    · let P : List (PyCore.Kont σ) := [.assign (fresh "v" l), .seq [], .tryE [stopH l] B, .seq [],
        loopK l (fresh "i" l) B (trB A.x.C u)]
      exact sig_popP A (i := true) (U := UAll) (.inr (.inl ⟨v, h1, h2⟩)) P (by simp [P]) k' (by rw [h2]; rfl)
        (by rw [hK']; rfl) (by simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC])
    · cases hi'
    · cases hi'
  | @forLoop U K0 K0' l tg it b u ss hn hH hU hi hg hf g1 ho hT g2 g3 g4 k =>
    let B := trT A.x.C (forSrc l) tg (trE A.x.C tg) ++ trB A.x.C b
    have k' : KRel A.x U false (.seq ss :: K0) (.seq [] :: .tryE [] [] :: .seq (trB A.x.C ss) :: K0') :=
      .core (.seq (pre := [.seq [], .tryE [] []]) (fun _ => hn) (.inr (.inr rfl)) g4 k)
    let P : List (PyCore.Kont σ) := [.seq [], loopK l (fresh "i" l) B (trB A.x.C u)]
    rcases hsig with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩
    · exact sig_popP A (i := false) (U := UAll) (.inl ⟨v, h1, h2⟩) P (by simp [P]) k' (by rw [h2]; rfl)
        (by rw [hK']; rfl) (by simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC])
    · exact sig_popP A (i := false) (U := UAll) (.inr (.inl ⟨v, h1, h2⟩)) P (by simp [P]) k' (by rw [h2]; rfl)
        (by rw [hK']; rfl) (by simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC])
    · exact brk_forLoop A hK hK' h1 h2 k'
    · exact next_forLoop' A (.inr ⟨h1, h2⟩) hK hK' hH hi hg fun H' hH' =>
        .loop (.forNext hn (hH' l hH) hU hi hg hf g1 ho hT g2 g3 g4 (KRel.ext ⟨hH', Agree.refl _ _ _⟩ k))

end Surf.T2
