/-
(T2), assignments (chained, attribute, subscript and unpacking targets), augmented assignments,
annotated assignments, `del`.

The helpers are in `Surf.T2.Asg`; the group's lemmas in `Surf.T2`.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Asg

/-! ## Fresh names of one node -/

theorem fresh_tag_ne {a b : String} (l : Label) (h : a ≠ b) :
    fresh a l ≠ fresh b l := by
  intro e
  have := congrArg String.toList e
  simp only [fresh, String.toList_append, List.append_assoc, List.append_cancel_left_eq,
    List.append_cancel_right_eq] at this
  exact h (String.toList_inj.1 this)

/-- The top item of a continuation replaced by one that is no `enterK`. -/
theorem esub_top {a b : Sem.Kont σ} {k K : List (Sem.Kont σ)} (h : K = a :: k)
    (hb : ∀ o bb kx, b ≠ .enterK o bb kx := by intro _ _ _ h; cases h) : EnterSub (b :: k) K := by
  intro o bb kx hm
  rcases List.mem_cons.1 hm with e | hm
  · exact absurd e.symm (hb o bb kx)
  · rw [h]; exact List.mem_cons_of_mem _ hm

theorem esub_top2 {a b c : Sem.Kont σ} {k K : List (Sem.Kont σ)} (h : K = a :: k)
    (hb : ∀ o bb kx, b ≠ .enterK o bb kx := by intro _ _ _ h; cases h)
    (hc : ∀ o bb kx, c ≠ .enterK o bb kx := by intro _ _ _ h; cases h) : EnterSub (b :: c :: k) K := by
  intro o bb kx hm
  rcases List.mem_cons.1 hm with e | hm
  · exact absurd e.symm (hb o bb kx)
  · exact esub_top h hc o bb kx hm

theorem top_kc {k : Sem.FKind} {C : List Scope} (h : KC k C) : isTop C = true ↔ (k = .mod ∨ k = .cls) := by
  cases k <;> rcases C with _ | ⟨S, C⟩ <;> (try cases S) <;> simp_all [KC, isTop]

/-! ## Signals passing PyCore items -/

def rPlain : PyCore.Kont σ → Bool
  | .tryE (_ :: _) _ | .catchS .. | .yfGot _ | .handler .. | .native _ => false
  | _ => true

def vPlain : PyCore.Kont σ → Bool
  | .handler .. => false
  | _ => true

def bPlain : PyCore.Kont σ → Bool
  | .loop .. | .handler .. => false
  | _ => true

def sPlain : PyCore.Ctrl σ → PyCore.Kont σ → Bool
  | .raise _ => rPlain
  | .retv _ => vPlain
  | .brk | .cont => bPlain
  | _ => fun _ => false

/-- Items every signal passes. -/
def aPlain : PyCore.Kont σ → Bool
  | .tryE (_ :: _) _ | .catchS .. | .yfGot _ | .handler .. | .native _ | .loop .. => false
  | _ => true

theorem aPlain_s {c : PyCore.Ctrl σ} (hc : (∃ v, c = .raise v) ∨ (∃ v, c = .retv v) ∨ c = .brk ∨ c = .cont)
    {P : List (PyCore.Kont σ)} (h : P.all aPlain = true) : P.all (sPlain c) = true := by
  simp only [List.all_eq_true] at h ⊢
  intro k hk
  have := h k hk
  revert this
  rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> (cases k with
    | tryE hs u => cases hs <;> simp [aPlain, sPlain, rPlain, vPlain, bPlain]
    | _ => simp [aPlain, sPlain, rPlain, vPlain, bPlain])

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem t_conf {c : PyCore.Ctrl σ} {K : List (PyCore.Kont σ)} (ht : t.stack = f' :: fs') (hc : f'.ctrl = c)
    (hk : f'.kont = K) : t = { t with stack := { f' with ctrl := c, kont := K } :: fs' } := by
  subst hc; subst hk; exact (t_eta ht).symm

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

theorem ppop_sig {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (hs : CSig i C U c c') (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ))
    (K P : List (PyCore.Kont σ)) (h : P.all (sPlain c') = true) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c', kont := P ++ K } :: fs' }
      { t with stack := { f' with ctrl := c', kont := K } :: fs' } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none := by
  rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · refine ppop rPlain t f' fs' K (fun k R hk => ?_) (fun R => ?_) P h
    · cases k <;> simp [rPlain] at hk <;> try simp [PyCore.step, PyCore.raiseStep, PyCore.top]
      rename_i hs u; cases hs <;> simp at hk; simp
    · rcases R with _ | ⟨k, R⟩
      · exact .inl (by simp [PyCore.focus])
      · cases hq : rPlain k
        · exact .inr ⟨k, R, rfl, hq⟩
        · refine .inl ?_
          cases k <;> simp [rPlain] at hq <;> try simp [PyCore.focus]
          rename_i hs u; cases hs <;> simp at hq; simp
  · refine ppop vPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
    cases k <;> simp [vPlain] at hk <;> simp [PyCore.step, PyCore.retStep, PyCore.top]
  · refine ppop bPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
    cases k <;> simp [bPlain] at hk <;> simp [PyCore.step, PyCore.brkStep, PyCore.top]
  · refine ppop bPlain t f' fs' K (fun k R hk => ?_) (fun R => .inl (by simp [PyCore.focus])) P h
    cases k <;> simp [bPlain] at hk <;> simp [PyCore.step, PyCore.contStep, PyCore.top]

theorem csig_any {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (hs : CSig i C U c c') : (∃ v, c' = .raise v) ∨ (∃ v, c' = .retv v) ∨ c' = .brk ∨ c' = .cont := by
  rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact .inl ⟨v, rfl⟩
  · exact .inr (.inl ⟨v, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

/-- A signal passes the Surf item on top and the PyCore items `P`, to related configurations. -/
theorem sig_popP (A : At p H s t f fs f' fs') {U U' : Label → Prop} {i : Bool} (hs : CSig i f.chain U f.ctrl f'.ctrl)
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (P : List (PyCore.Kont σ)) (hK' : f'.kont = P ++ K0')
    (hk : KRel A.x U' false K0 K0') (e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs })
    (hP : P ≠ []) (hp : P.all aPlain = true) (he : EnterSub K0 f.kont) : Goal I p H s t := by
  obtain ⟨ys, py, hl, hy⟩ := ppop_sig (I := I) hs t f' fs' K0' P (aPlain_s (csig_any hs) hp)
  have e := t_conf (c := f'.ctrl) A.ht rfl hK'
  have hr := crelI_seen (H := H) (zs := [s]) (A.set (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := K0')
    (csig_cr hs (fun _ => rfl) U') hk he)
  have hs' : { s with stack := { f with ctrl := f.ctrl, kont := K0 } :: fs } = { s with stack := { f with kont := K0 } :: fs } := rfl
  rw [hs'] at hr
  exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [e]; exact py)
    (by rintro rfl; exact hP (List.eq_nil_of_length_eq_zero hl.symm)) hr (cover_none hy)

theorem delSeg_pre {C : List Scope} {ts : List Expr} {Kp K' : List (PyCore.Kont σ)} (h : DelSeg C ts Kp K') :
    ∃ P, P ≠ [] ∧ P.all aPlain = true ∧ Kp = P ++ K' := by
  induction h with
  | base => exact ⟨[_], by simp, by simp [aPlain], rfl⟩
  | @nest es ts K1 K' _ ih =>
    obtain ⟨P, -, hP, e⟩ := ih
    exact ⟨.seq (trDs C es) :: .tryE [] [] :: P, by simp, by simp [aPlain, hP], by rw [e]; rfl⟩

end

/-! ## Stores of fresh names that keep the readings of the others -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- `pstore0`, and the frame's readings of the other names stay. -/
theorem pstore1 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (v : Val) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ t1 g', PyCore.store t { f' with kont := k' } fs' (fresh tag l) v c' = some t1 ∧
      At0 p H s t1 f fs g' fs' ∧ g'.ctrl = c' ∧ g'.kont = k' ∧ rdOf t1 g' (fresh tag l) = some v ∧
      Agree (· = l) (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') ∧
      ∀ y, y ≠ fresh tag l → rdOf t1 g' y = rdOf t f' y := by
  obtain ⟨q, hq, A1, hr, ha⟩ := pwrite0 A htag hfo (some v) c' k'
  refine ⟨_, _, ?_, A1, rfl, rfl, hr, ha, fun y hy => ?_⟩
  · unfold PyCore.store; rw [pplace_kont, hq]; cases q <;> rfl
  rcases fok_place A hfo with ⟨hq', -, -⟩ | ⟨hq', -, -⟩ | ⟨hq', -, -⟩ <;> rw [hq'] at hq <;> cases hq <;>
    refine (rd_same (P := (· = fresh tag l)) (t := t) (h := f') ?_ ?_ ?_ ?_ ?_ ?_ y hy).1 <;> (try rfl) <;>
    first
    | (intro _ _; rfl) | (intro _ _ _; rfl)
    | (intro _ z hz; simp only [PyCore.writeAt, pglob_ins]; simp [Ne.symm hz]; done)
    | (intro _ z hz; exact lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns (some v))
    | (intro z hz; simp only [PyCore.writeAt, Std.HashMap.getElem?_insert, beq_iff_eq]
       rw [if_neg]; intro e; exact hz (congrArg Prod.snd e).symm)

end

/-! ## A target's items (as in the loop group's helpers)

The items of a target's translation as an expression are items of its store. -/

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

theorem disp_items {C : List Scope} {lt : Label} {g : Py.Gadget} {ts : List Expr} {x : PyCore.Item}
    (hx : x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 g (trA C ts ++ ts.map starMark))) :
    ∃ t ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar t)) := by
  simp only [gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
    items_foldl, List.nil_append, trA_eq, List.flatMap_append, List.mem_append, List.mem_flatMap, List.mem_map] at hx
  rcases hx with ⟨_, ⟨t, ht, rfl⟩, hx⟩ | ⟨_, ⟨t, ht, rfl⟩, hx⟩
  · exact ⟨t, ht, hx⟩
  · cases t <;> simp [starMark, PyCore.itemsE] at hx

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

theorem trTs_items {C : List Scope} {src : Label → PE} {x : PyCore.Item} {t : Expr} :
    ∀ {ts : List Expr}, t ∈ ts → x ∈ PyCore.itemsB R0 (trChain C) (trT C src t (trE C t)) →
      x ∈ PyCore.itemsB R0 (trChain C) (trTs C src ts)
  | [], h, _ => by simp at h
  | a :: ts, h, hx => by
    simp only [trTs, pitemsB_app, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl hx
    · exact .inr (trTs_items h hx)

theorem okE_tgt {ts : List Expr} {t : Expr} (hok : okAs ts = true) (ht : t ∈ ts) (htg : tgtOk t = true) :
    okE t = true := by
  have := okAs_mem hok ht; cases t <;> simp_all [tgtOk, unstar]

/-- An assignment's target, at the budget without the statement's node. -/
theorem goodE_asg {C : List Scope} {U : Label → Prop} {l : Label} {ts : List Expr} {e : Expr} {ss : List Stmt}
    (hg : GoodB p C U (.assign l ts e :: ss)) {t : Expr} (ht : t ∈ ts) : GoodE p C (Rm U l) t := by
  have hok : okS (.assign l ts e) = true := by have := hg.ok; simp only [okB, Bool.and_eq_true] at this; exact this.1
  simp only [okS, Bool.and_eq_true, List.all_eq_true] at hok
  have htg := hok.1.2 t ht
  have hnd : (labelsS (.assign l ts e)).Nodup := by
    have := hg.nd; simp only [labelsB, List.nodup_append] at this; exact this.1
  simp only [labelsS] at hnd
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.1 hnd
  have hn3 := (List.nodup_append.1 hn2).1
  refine GoodE.rm (GoodB.e hg (fun x hx => ?_) (fun x hx => ?_) (fun _ => okE_tgt hok.1.1 ht htg)
    (fun l' hl' => ?_) (fun _ => nodup_labelsEs ht hn3) (fun x hx => by simp [touchS, touchEs_mem ht hx]))
    (fun h => hn1 (List.mem_append_left _ (labelsEs_mem ht h)))
  · simp [itemsS, itemsEs_mem ht hx]
  · have := trTs_items (src := nameSrc "t" l) ht (tgt_items t (nameSrc "t" l) htg x hx)
    simp [trS, blk, PyCore.itemsS, PyCore.itemsB, this]
  · simp [labelsS, labelsEs_mem ht hl']

theorem touch_exec {s : Sem.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {st : Stmt} {ss : List Stmt} (hs : s.stack = f :: fs) (hc : f.ctrl = .exec (st :: ss)) :
    Touch p s st.label := .inl (by simp [Sem.focus, hs, hc]; cases st <;> rfl)

/-! ## Paths of PyCore -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore at `$stuck`: five steps, then none. -/
theorem pstuck (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (r : Label) (rest : PS)
    (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g' with ctrl := .exec (stuckAt r :: rest), kont := K } :: gs' }
      { t with stack := { g' with
        ctrl := .val (.data "$args" []), kont := .callA (.prim "$stuck") :: .exprS :: .seq rest :: K } :: gs' } ys ∧
      PyCore.step I { t with stack := { g' with
        ctrl := .val (.data "$args" []), kont := .callA (.prim "$stuck") :: .exprS :: .seq rest :: K } :: gs' } = none ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  let K1 : List (PyCore.Kont σ) := .exprS :: .seq rest :: K
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { g' with ctrl := c, kont := k } :: gs' }
  have s1 : PyCore.step I (mk (.exec (stuckAt r :: rest)) K) =
      some (mk (.ev (.call r (.const r "$stuck") (.const r "$args"))) K1) := by
    simp [mk, K1, stuckAt, ccR, recR, PyCore.step, PyCore.execStep, PyCore.top, Gadget.name]
  have s2 : PyCore.step I (mk (.ev (.call r (.const r "$stuck") (.const r "$args"))) K1) =
      some (mk (.ev (.const r "$stuck")) (.callF (.const r "$args") :: K1)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top]
  have s3 : PyCore.step I (mk (.ev (.const r "$stuck")) (.callF (.const r "$args") :: K1)) =
      some (mk (.val (.prim "$stuck")) (.callF (.const r "$args") :: K1)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, kc_stuck]
  have s4 : PyCore.step I (mk (.val (.prim "$stuck")) (.callF (.const r "$args") :: K1)) =
      some (mk (.ev (.const r "$args")) (.callA (.prim "$stuck") :: K1)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
  have s5 : PyCore.step I (mk (.ev (.const r "$args")) (.callA (.prim "$stuck") :: K1)) =
      some (mk (.val (.data "$args" [])) (.callA (.prim "$stuck") :: K1)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
  have s6 : PyCore.step I (mk (.val (.data "$args" [])) (.callA (.prim "$stuck") :: K1)) = none := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, gad_stuck', PyCore.gadgetStep]
  refine ⟨_, .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.nil _))))), s6, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [mk, PyCore.focus, PyCore.Expr.label, PyCore.Stmt.label, stuckAt] at hx <;>
    exact hx.symm

/-- Surf is stuck; PyCore steps (`pre`) to a statement `$stuck` and is stuck there. -/
theorem goal_stuck (A : At0 p H s t f fs f' fs') (e0 : Sem.step I s = none) {g' : PyCore.Frame σ} {r : Label}
    {rest : PS} {K : List (PyCore.Kont σ)} {ys0 : List (PyCore.Config σ)}
    (pre : Path (PyCore.step I) t { t with stack := { g' with ctrl := .exec (stuckAt r :: rest), kont := K } :: fs' } ys0)
    (hcov : ∀ y ∈ ys0 ++ [{ t with stack := { g' with ctrl := .exec (stuckAt r :: rest), kont := K } :: fs' }],
      ∀ x, PyCore.focus y = some x → Touch p s (x / 64))
    (hr : Touch p s (r / 64)) : Goal I p H s t := by
  obtain ⟨ys, pth, hst, hfoc⟩ := pstuck (I := I) t g' fs' r rest K
  refine .inl ⟨s, _, [], ys0 ++ ys, .nil _, e0, pre.append pth, hst, ?_, ?_⟩
  · simp [Fin, Sem.outcome, PyCore.outcome, A.hs, OCorr, A.out, A.st]
  · intro y hy x hx
    have hx := pfocus_le hx
    refine .inr ⟨s, by simp, ?_⟩
    simp only [List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · simp [PyCore.focus] at hx
    · exact hcov y (by simp [hy]) x hx
    · cases ys with
      | nil => simp at hy
      | cons y0 ys' =>
        cases pth with
        | cons e p' =>
          rcases List.mem_cons.1 hy with rfl | hy'
          · exact hcov _ (by simp) x hx
          · rw [hfoc y (by simp [hy']) x hx]; exact hr

theorem curExc_top {gl cs} {g : Sem.Frame σ} {g' : PyCore.Frame σ} {gs : List (Sem.Frame σ)}
    {gs' : List (PyCore.Frame σ)}
    (hfs : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') gs gs')
    (he : PyCore.kontExc g'.kont = Sem.kontExc g.kont) : PyCore.curExc (g' :: gs') = Sem.curExc (g :: gs) := by
  simp only [PyCore.curExc, Sem.curExc, he, curExc_rel hfs]
  cases Sem.kontExc g.kont <;> rfl

theorem resCtrl_top {gl cs} {g : Sem.Frame σ} {g' : PyCore.Frame σ} {gs : List (Sem.Frame σ)}
    {gs' : List (PyCore.Frame σ)}
    (hfs : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') gs gs')
    (he : PyCore.kontExc g'.kont = Sem.kontExc g.kont) {C : List Scope} {U : Label → Prop} (r : Except Val Val) :
    CR p C U true (Sem.resCtrl (g :: gs) r) (PyCore.resCtrl (g' :: gs') r) := by
  cases r with
  | ok v => exact .val
  | error v =>
    simp only [Sem.resCtrl, PyCore.resCtrl, Sem.raiseNew, PyCore.raiseNew, curExc_top hfs he, withCtx_eq]
    exact .raise

end

theorem item_fok (W : WF p) {C : List Scope} {L : Label} {tag : String} {l : Label}
    (hi : PyCore.Item.occ L (fresh tag l) (trChain C) ∈ PI p) (hL : ¬ IsCmp L) :
    FOk C (fresh tag l) :=
  fok_of W hi ⟨_, _, rfl⟩ hL

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore passes a branch that never runs. -/
theorem dead_path (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (r : Label) (ss rest : PS)
    (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g' with ctrl := .exec (dead r ss :: rest), kont := K } :: gs' }
      { t with stack := { g' with ctrl := .exec rest, kont := K } :: gs' } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { g' with ctrl := c, kont := k } :: gs' }
  have s1 : PyCore.step I (mk (.exec (dead r ss :: rest)) K) =
      some (mk (.ev (.const r "$false")) (.ifS ss [] :: .seq rest :: K)) := by
    simp [mk, dead, PyCore.step, PyCore.execStep, PyCore.top]
  have s2 : PyCore.step I (mk (.ev (.const r "$false")) (.ifS ss [] :: .seq rest :: K)) =
      some (mk (.val .no) (.ifS ss [] :: .seq rest :: K)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  have s3 : PyCore.step I (mk (.val .no) (.ifS ss [] :: .seq rest :: K)) =
      some (mk (.val (.bool false)) (.ifT ss [] :: .seq rest :: K)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.tst, PyCore.top]
  have s4 : PyCore.step I (mk (.val (.bool false)) (.ifT ss [] :: .seq rest :: K)) =
      some (mk (.exec []) (.seq rest :: K)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
  have s5 : PyCore.step I (mk (.exec []) (.seq rest :: K)) = some (mk (.exec rest) K) := by
    simp [mk, PyCore.step, PyCore.doneStep, PyCore.top]
  refine ⟨_, .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.nil _))))), by simp, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [mk, PyCore.focus, PyCore.Expr.label, PyCore.Stmt.label, dead] at hx <;>
    exact hx.symm

/-- PyCore ends a block (`exec []` through `seq []`-free items: `seq`, `tryE`). -/
theorem done_seq (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (ss : PS)
    (K : List (PyCore.Kont σ)) :
    PyCore.step I { t with stack := { g' with ctrl := .exec [], kont := .seq ss :: K } :: gs' } =
      some { t with stack := { g' with ctrl := .exec ss, kont := K } :: gs' } := by
  simp [PyCore.step, PyCore.doneStep, PyCore.top]

theorem done_try (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ))
    (K : List (PyCore.Kont σ)) :
    PyCore.step I { t with stack := { g' with ctrl := .exec [], kont := .tryE [] [] :: K } :: gs' } =
      some { t with stack := { g' with ctrl := .exec [], kont := K } :: gs' } := by
  simp [PyCore.step, PyCore.doneStep, PyCore.top]

end

end Asg

open Asg

set_option hygiene false in
macro "asg_spop" : tactic => `(tactic| (rcases hsig with ⟨_, h1, -⟩ | ⟨_, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩ <;>
  simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]))

set_option hygiene false in
macro "asg_sig" P:term : tactic => `(tactic| exact sig_popP A hsig $P (by rw [hK']; rfl) ‹_› (by asg_spop) (by simp)
  (by simp [aPlain]) (esub_cons hK))

theorem sig_asg {i : Bool} : KCase I p i AsgK CSig := by
  intro H s t f fs f' fs' U A W hsig hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | assignK _ _ _ _ k => asg_sig [_, _, _]
  | stManyT _ _ _ k => asg_sig [_, _]
  | stAttr _ _ k => asg_sig [_, _, _, _]
  | stSubL _ _ _ k => asg_sig [_, _, _, _, _]
  | stSubR _ _ k => asg_sig [_, _, _, _]
  | stUnpack _ _ _ _ _ k => asg_sig [_, _, _, _]
  | stManyU _ _ _ _ k => asg_sig [_, _]
  | augN _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augAttr _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augAttrV _ _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augSubL _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augSubI _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augSubV _ _ _ _ _ _ _ k => asg_sig [_, _, _]
  | augR _ _ _ _ _ k => asg_sig [_, _, _, _]
  | augW _ _ _ _ _ k => asg_sig [_, _, _]
  | annK _ _ _ _ _ _ _ k => asg_sig [_, _, _]
  | exprBlk _ k => asg_sig [_, _, _]
  | annA _ _ _ _ _ k => asg_sig [_, _]
  | annV _ _ _ _ _ k => asg_sig [_, _, _]
  | annE _ _ _ _ _ _ k => asg_sig [_, _, _]
  | evsDrop1 k => asg_sig [_]
  | @evsDropR _ _ _ lt rest acc ps _ _ k =>
    exact sig_popP A hsig (.binR "," (.data "$args" acc.reverse) :: ps.map (.binL ",") ++ [.exprS])
      (by rw [hK']; simp [recK]) k (by asg_spop) (by simp) (by simp [aPlain]) (esub_cons hK)
  | delMany _ _ hd k =>
    obtain ⟨P, hP, hp, e⟩ := delSeg_pre hd
    exact sig_popP A hsig (P ++ [.tryE [] []]) (by rw [hK', e]; simp) k (by asg_spop) (by simp)
      (by simp [hp, aPlain]) (esub_cons hK)
  | delAttr k => asg_sig [_, _, _]
  | delSubL _ k => asg_sig [_, _, _, _]
  | delSubR k => asg_sig [_, _, _]


theorem exec_assign (l ts e) : ExecCase I p (.assign l ts e) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hU : U l := hg.u l (by simp [labelsB, labelsS])
  have hf : FOk f.chain (fresh "t" l) := fok_of W (L := sub l 1)
    (hg.t _ (by simp [trB, trS, blk, PyCore.itemsB, PyCore.itemsS])) ⟨_, _, rfl⟩
    (not_cmp _ _ (by omega) (by omega) (by omega))
  have he : GoodE p f.chain U e := by gse
  let K' : List (PyCore.Kont σ) := .seq (trB f.chain ss) :: f'.kont
  let t1 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .exec (.assign (sub l 1) (fresh "t" l) (trE f.chain e) :: trTs f.chain (nameSrc "t" l) ts),
    kont := .tryE [] [] :: K' } :: fs' }
  let t2 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev (trE f.chain e),
    kont := .assign (fresh "t" l) :: .seq (trTs f.chain (nameSrc "t" l) ts) :: .tryE [] [] :: K' } :: fs' }
  have st1 : PyCore.step I t = some t1 := by
    simp [PyCore.step, A.ht, hc', trB, trS, blk, PyCore.execStep, PyCore.top, t1, K']
  have st2 : PyCore.step I t1 = some t2 := by simp [t1, t2, PyCore.step, PyCore.execStep, PyCore.top]
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .ev e, kont := .assignK ts :: .seq ss :: f.kont } :: fs } := by estep
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
    (crelI_seen (A.set (.ev he) (.asg (.assignK hU hf (fun t ht => goodE_asg hg ht)
      (fun x hx => hg.t x (by simp [trB, trS, blk, PyCore.itemsB, PyCore.itemsS, hx]))
      (krel_seq (hnc (by simp)) hg.tail hk))))) (cover_of (l := l) (by simp) (touch_exec A.hs hc) ?_)
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)

set_option hygiene false in
macro "aug_it" : tactic => `(tactic| (refine hg.t _ ?_; simp [trB, trS, trAug, blk, augUpd, PyCore.itemsB, PyCore.itemsS,
  PyCore.itemsE]))

set_option hygiene false in
macro "aug_ge" : tactic => `(tactic| exact GoodB.e hg (by intro x hx; simp [itemsS, itemsE, hx])
  (by intro x hx; simp [trS, trAug, blk, PyCore.itemsS, PyCore.itemsB, PyCore.itemsE, cc, ccR, recR, hx])
  (by intro h; simp_all [okS, okE]) (by intro x hx; simp [labelsS, labelsE, hx])
  (by intro h; simp_all [labelsS, labelsE, List.nodup_cons, List.nodup_append])
  (by intro x hx; simp [touchS, touchE, hx]))

theorem exec_augassign (l tg op e) : ExecCase I p (.augassign l tg op e) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hU : U l := hg.u l (by simp [labelsB, labelsS])
  have hnd : (labelsS (.augassign l tg op e)).Nodup := by
    have := hg.nd; simp only [labelsB, List.nodup_append] at this; exact this.1
  simp only [labelsS] at hnd
  obtain ⟨hn1, hn2⟩ := List.nodup_cons.1 hnd
  have he : GoodE p f.chain (Rm U l) e :=
    GoodE.rm (GoodB.e hg (by intro x hx; simp [itemsS, hx]) (by intro x hx; cases tg <;>
      simp [trS, trAug, blk, augUpd, PyCore.itemsS, PyCore.itemsB, PyCore.itemsE, nm, hx])
      (by intro h; simp_all [okS]) (by intro x hx; simp [labelsS, hx])
      (by intro h; simp_all [labelsS, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, hx]))
      (fun h => hn1 (by simp [h]))
  have hkq := krel_seq (hnc (by simp)) hg.tail hk
  have hTl : Touch p s l := touch_exec A.hs hc
  have hTt : Touch p s tg.label := .inr (by rw [A.hs]; simp [TouchF, hc, lbl_eq])
  have hH : ∀ {zs : List (Sem.Config σ)}, s ∈ zs → ∀ l', Touch p s l' → Seen (Touch p) H zs l' :=
    fun hz _ h => .inr ⟨s, hz, h⟩
  have hHH : ∀ {zs : List (Sem.Config σ)} l', H l' → Seen (Touch p) H zs l' := fun _ h => .inl h
  have hcov : ∀ (ys : List (PyCore.Config σ)) {zs : List (Sem.Config σ)}, s ∈ zs →
      (∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l ∨ x / 64 = tg.label) →
      Cover (Touch p) pfocus H zs ys := by
    intro ys zs hz h y hy x hx
    rcases h y hy x (pfocus_le hx) with h | h <;> rw [h]
    · exact hH hz _ hTl
    · exact hH hz _ hTt
  let K' : List (PyCore.Kont σ) := .seq (trB f.chain ss) :: f'.kont
  by_cases hsh : (∃ lt x, tg = .name lt x) ∨ (∃ lt o a, tg = .attr lt o a) ∨ (∃ lt o i, tg = .sub lt o i)
  case neg =>
    have e0 : Sem.step I s = none := by
      cases tg <;> simp_all [Sem.step, A.hs, hc, Sem.execStep]
    have htr : trAug f.chain l tg (trT f.chain deadSrc tg (trE f.chain tg)) =
        ([stuckAt (sub tg.label 55), dead (sub tg.label 54) (trT f.chain deadSrc tg (trE f.chain tg))], []) := by
      cases tg <;> simp_all [trAug]
    let rest : PS := [dead (sub tg.label 54) (trT f.chain deadSrc tg (trE f.chain tg)),
      .assign (sub l 1) (fresh "v" l) (.bin (sub l 2) (op ++ "=") (nm l 3 (fresh "g" l)) (trE f.chain e))]
    have st1 : PyCore.step I t = some { t with stack := { f' with
        ctrl := .exec (stuckAt (sub tg.label 55) :: rest), kont := .tryE [] [] :: K' } :: fs' } := by
      have htB : trB f.chain (.augassign l tg op e :: ss) = blk l (stuckAt (sub tg.label 55) :: rest) ::
          trB f.chain ss := by simp [trB, trS, htr, rest, nm]
      rw [pstep_exec A.ht (by rw [hc', htB])]
      simp [PyCore.execStep, PyCore.top, rest, K', blk]
    refine goal_stuck A.zero e0 (.cons st1 (.nil _)) ?_ (by rw [sub_div _ _ (by omega)]; exact hTt)
    intro y hy x hx
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hTl
    · simp [PyCore.focus, PyCore.Stmt.label, stuckAt] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hTt
  rcases hsh with ⟨lt, x, rfl⟩ | ⟨lt, o, a, rfl⟩ | ⟨lt, o, i, rfl⟩
  · -- name
    have hx : ¬ Dot (mangle (priv f.chain) x) := W.nodot lt _ f.chain (hg.s _ (by simp [itemsB, itemsS, itemsE]))
    have hfg : FOk f.chain (fresh "g" l) := item_fok W (L := sub lt 0) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfv : FOk f.chain (fresh "v" l) := item_fok W (L := sub l 1) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    let x' := mangle (priv f.chain) x
    let Kg : List (PyCore.Kont σ) := .assign (fresh "g" l) :: .seq [augUpd f.chain l op e, wrN l lt x'] :: .tryE [] [] :: K'
    let g2 : PyCore.Frame σ := { f' with ctrl := .ev (.name (sub lt 1) x' none), kont := Kg }
    let t1 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .exec [.assign (sub lt 0) (fresh "g" l) (.name (sub lt 1) x' none), augUpd f.chain l op e, wrN l lt x'],
      kont := .tryE [] [] :: K' } :: fs' }
    let t2 : PyCore.Config σ := { t with stack := g2 :: fs' }
    let Ks : List (Sem.Kont σ) := .augN (Sem.mg f x) op e :: .seq ss :: f.kont
    let f1 : Sem.Frame σ := { f with ctrl := .ev (.name lt x), kont := Ks }
    let s1 : Sem.Config σ := { s with stack := f1 :: fs }
    have st1 : PyCore.step I t = some t1 := by
      simp [PyCore.step, A.ht, hc', trB, trS, trAug, blk, PyCore.execStep, PyCore.top, t1, K', augUpd, wrN, x']
    have st2 : PyCore.step I t1 = some t2 := by simp [t1, t2, g2, Kg, PyCore.step, PyCore.execStep, PyCore.top]
    have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC, s1, f1, Ks]
    have hr : PyCore.readName I t2 g2 x' none = Sem.readName I s1 f1 (Sem.mg f1 x) :=
      readName_eq (p := p) (H := H) ⟨A.hf.toFRel0.upd _ _ _ _, A.r.cells, A.r.glob⟩ hx
    have st3 : PyCore.step I t2 = some { t with stack := { f' with
        ctrl := PyCore.resCtrl (g2 :: fs') (Sem.readName I s1 f1 (Sem.mg f1 x)), kont := Kg } :: fs' } := by
      rw [← hr]; rfl
    have e2 : Sem.step I s1 = some { s with stack := { f with
        ctrl := Sem.resCtrl (f1 :: fs) (Sem.readName I s1 f1 (Sem.mg f1 x)), kont := Ks } :: fs } := by
      simp [Sem.step, s1, f1, Sem.evalStep, Sem.setC]
    have hst := A.stk
    have hex : PyCore.kontExc g2.kont = Sem.kontExc f1.kont := by
      simp only [g2, f1, Kg, Ks, K', PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk
    refine goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 (.cons st2 (.cons st3 (.nil _)))) (by simp)
      (.inl ((A.mono (hHH (zs := [s, s1]))).set (resCtrl_top hst.2 hex _)
        (.asg (.augN (lt := lt) (hH (by simp) _ hTl) (hH (by simp) _ hTt) hU
          (by intro tag ht; simp at ht; rcases ht with rfl | rfl <;> assumption) hx he
          (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkq))) (by intro _ _ _ hm; simp [Ks] at hm; exact hm))) (hcov _ (by simp) ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; left; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; right; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [t2, g2, PyCore.focus, PyCore.Expr.label] at hx; right; rw [← hx]; exact sub_div _ _ (by omega)
  · -- attribute
    have hfo : FOk f.chain (fresh "o" l) := item_fok W (L := sub lt 4) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfg : FOk f.chain (fresh "g" l) := item_fok W (L := sub lt 5) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfv : FOk f.chain (fresh "v" l) := item_fok W (L := sub l 1) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have ho : GoodE p f.chain U o := by aug_ge
    have hna : ':' ∉ (mangle (priv f.chain) a).toList := by
      have := hg.ok; simp only [okB, okS, okE, Bool.and_eq_true] at this
      exact nc_mangle_pv ho.pv (nc_ok this.1.1.2.1)
    let a' := mangle (priv f.chain) a
    let t1 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .exec [.assign (sub lt 4) (fresh "o" l) (trE f.chain o), getA l lt a', augUpd f.chain l op e, wrA l lt a'],
      kont := .tryE [] [] :: K' } :: fs' }
    let t2 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .ev (trE f.chain o),
      kont := .assign (fresh "o" l) :: .seq [getA l lt a', augUpd f.chain l op e, wrA l lt a'] :: .tryE [] [] :: K' } :: fs' }
    have st1 : PyCore.step I t = some t1 := by
      simp [PyCore.step, A.ht, hc', trB, trS, trAug, blk, PyCore.execStep, PyCore.top, t1, K', augUpd, getA, wrA, a']
    have st2 : PyCore.step I t1 = some t2 := by simp [t1, t2, PyCore.step, PyCore.execStep, PyCore.top]
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev o, kont := .augAttr (Sem.mg f a) op e :: .seq ss :: f.kont } :: fs } := by
      simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
      (.inl ((A.mono (hHH (zs := [s]))).set (.ev ho)
        (.asg (.augAttr (lt := lt) (hH (by simp) _ hTl) (hH (by simp) _ hTt) hU
          (by intro tag ht; simp at ht; rcases ht with rfl | rfl | rfl <;> assumption) hna he
          (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkq))))) (hcov _ (by simp) ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; left; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; right; rw [← hx]; exact sub_div _ _ (by omega)
  · -- subscript
    have hfo : FOk f.chain (fresh "o" l) := item_fok W (L := sub lt 4) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfk : FOk f.chain (fresh "k" l) := item_fok W (L := sub lt 5) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfg : FOk f.chain (fresh "g" l) := item_fok W (L := sub lt 6) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have hfv : FOk f.chain (fresh "v" l) := item_fok W (L := sub l 1) (by aug_it) (not_cmp _ _ (by omega) (by omega) (by omega))
    have ho : GoodE p f.chain U o := by aug_ge
    have hi : GoodE p f.chain (Rm U l) i := GoodE.rm (by aug_ge) (fun h => hn1 (by simp [labelsE, h]))
    let t1 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .exec [.assign (sub lt 4) (fresh "o" l) (trE f.chain o), keyS f.chain l lt i, getI l lt,
        augUpd f.chain l op e, wrI l lt],
      kont := .tryE [] [] :: K' } :: fs' }
    let t2 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .ev (trE f.chain o),
      kont := .assign (fresh "o" l) :: .seq [keyS f.chain l lt i, getI l lt, augUpd f.chain l op e, wrI l lt] ::
        .tryE [] [] :: K' } :: fs' }
    have st1 : PyCore.step I t = some t1 := by
      simp [PyCore.step, A.ht, hc', trB, trS, trAug, blk, PyCore.execStep, PyCore.top, t1, K', augUpd, keyS, getI, wrI]
    have st2 : PyCore.step I t1 = some t2 := by simp [t1, t2, PyCore.step, PyCore.execStep, PyCore.top]
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev o, kont := .augSubL i op e :: .seq ss :: f.kont } :: fs } := by
      simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
      (.inl ((A.mono (hHH (zs := [s]))).set (.ev ho)
        (.asg (.augSubL (lt := lt) (hH (by simp) _ hTl) (hH (by simp) _ hTt) hU
          (by intro tag ht; simp at ht; rcases ht with rfl | rfl | rfl | rfl <;> assumption) hi he
          (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkq))))) (hcov _ (by simp) ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; left; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; right; rw [← hx]; exact sub_div _ _ (by omega)
theorem exec_annassign (l tg a v) : ExecCase I p (.annassign l tg a v) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hU : U l := hg.u l (by simp [labelsB, labelsS])
  have hok : okS (.annassign l tg a v) = true := by
    have := hg.ok; simp only [okB, Bool.and_eq_true] at this; exact this.1
  have hnd : (labelsS (.annassign l tg a v)).Nodup := by
    have := hg.nd; simp only [labelsB, List.nodup_append] at this; exact this.1
  have hkq := krel_seq (hnc (by simp)) hg.tail hk
  have hTl : Touch p s l := touch_exec A.hs hc
  have hH : ∀ {zs : List (Sem.Config σ)}, s ∈ zs → ∀ l', Touch p s l' → Seen (Touch p) H zs l' :=
    fun hz _ h => .inr ⟨s, hz, h⟩
  have hHH : ∀ {zs : List (Sem.Config σ)} l', H l' → Seen (Touch p) H zs l' := fun _ h => .inl h
  have hsh : (∃ lt y, tg = .name lt y) ∨ (∃ lt o b, tg = .attr lt o b) ∨ (∃ lt o i, tg = .sub lt o i) := by
    cases tg <;> simp [okS] at hok <;> simp
  have hpv : ∀ c, priv f.chain = some c → okName c = true := hg.pv (List.cons_ne_nil _ _)
  have hga : GoodE p f.chain U a := GoodB.e hg (by intro x hx; simp [itemsS, hx])
    (by intro x hx; cases v <;> cases hT : isTop f.chain <;>
      simp [trS, blk, dead, PyCore.itemsS, PyCore.itemsB, pitemsB_app, PyCore.itemsE, hx, hT])
    (by intro h; simp_all [okS]) (by intro x hx; simp [labelsS, hx])
    (by intro h; simp_all [labelsS, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, hx])
  have hfn : isTop f.chain = true → FOk f.chain (fresh "n" l) := fun hT =>
    item_fok W (L := sub l 6) (hg.t _ (by cases v <;>
      simp [trB, trS, blk, PyCore.itemsS, PyCore.itemsB, pitemsB_app, hT])) (not_cmp _ _ (by omega) (by omega) (by omega))
  have hao : AnnOk A.x U l tg a := ⟨hU, hfn, hga, by simp only [okS, Bool.and_eq_true] at hok; exact hok.1.1.2,
    fun l' hl' => hg.u l' (by simp [labelsB, labelsS, hl']), fun lt y e => by
      subst e; simp only [okS, Bool.and_eq_true] at hok; exact nc_mangle_pv hpv (nc_ok hok.1.1.1)⟩
  have htop := top_kc A.hf.kc
  let K' : List (PyCore.Kont σ) := .seq (trB f.chain ss) :: f'.kont
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  have c0 : ∀ x, PyCore.focus t = some x → x / 64 = l := by
    intro x hx; simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx
    cases v <;> simp at hx <;> (rw [← hx]; exact sub_div _ _ (by omega))
  cases v with
  | some e =>
    have he : GoodE p f.chain U e := GoodB.e hg (by intro x hx; simp [itemsS, itemsO, hx])
      (by intro x hx; simp [trS, blk, PyCore.itemsS, PyCore.itemsB, pitemsB_app, hx])
      (by intro h; simp_all [okS, okO]) (by intro x hx; simp [labelsS, labelsO, hx])
      (by intro h; simp_all [labelsS, labelsO, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, touchO, hx])
    have htgo : tgtOk tg = true := by rcases hsh with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hgt : GoodE p f.chain (Rm U l) tg := by
      refine GoodE.rm (GoodB.e hg (by intro x hx; simp [itemsS, hx]) (fun x hx => ?_)
        (by intro h; simp_all [okS]) (by intro x hx; simp [labelsS, hx])
        (by intro h; simp_all [labelsS, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, hx]))
        (fun h => by simp only [labelsS, List.cons_append, List.nodup_cons] at hnd; exact hnd.1 (by simp [h]))
      have := tgt_items tg (nameSrc "t" l) htgo x hx
      simp [trS, blk, PyCore.itemsS, PyCore.itemsB, pitemsB_app, this]
    have hf : FOk f.chain (fresh "t" l) := item_fok W (L := sub l 1)
      (hg.t _ (by simp [trB, trS, blk, PyCore.itemsB, PyCore.itemsS])) (not_cmp _ _ (by omega) (by omega) (by omega))
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev e,
        kont := .annK tg (if isTop f.chain then some a else none) :: .seq ss :: f.kont } :: fs } := by
      cases hk : f.kind <;> simp_all [Sem.step, A.hs, Sem.execStep, Sem.setC]
    let t1 := mk (.exec (.assign (sub l 1) (fresh "t" l) (trE f.chain e) ::
      (trT f.chain (nameSrc "t" l) tg (trE f.chain tg) ++ annS f.chain l tg a))) (.tryE [] [] :: K')
    have st1 : PyCore.step I t = some t1 := by
      simp [PyCore.step, A.ht, hc', trB, trS, blk, PyCore.execStep, PyCore.top, t1, mk, K', annS]
    have st2 : PyCore.step I t1 = some (mk (.ev (trE f.chain e)) (.assign (fresh "t" l) ::
        .seq (trT f.chain (nameSrc "t" l) tg (trE f.chain tg) ++ annS f.chain l tg a) :: .tryE [] [] :: K')) := by
      simp [t1, mk, PyCore.step, PyCore.execStep, PyCore.top]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
      (.inl ((A.mono (hHH (zs := [s]))).set (.ev he)
        (.asg (.annK (hH (by simp) _ hTl) hU hf hgt hsh rfl hao (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkq)))))
      (cover_of (l := l) (by simp) hTl ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact c0 x hx
    · simp [t1, mk, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  | none =>
    have hTt : Touch p s (Sem.Expr.lbl tg) := .inr (by rw [A.hs]; simp [TouchF, hc])
    let rest : PS := annS f.chain l tg a ++ [dead (sub l 9) (annBind f.chain tg)]
    -- `annA`'s budget: `U` or `Rm U l`
    obtain ⟨UA, hann, hUA⟩ : ∃ UA, KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) UA false
        (.annA tg (if isTop f.chain then some a else none) :: .seq ss :: f.kont) (.seq rest :: .tryE [] [] :: K') ∧
        ∀ l', Rm U l l' → UA l' :=
      ⟨_, .asg (.annA (hH (by simp) _ hTl) (hH (by simp) _ hTt) rfl hao (.inr rfl) (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkq)),
        fun _ h => by first | exact h | exact h.1⟩
    have hlt : ∀ {e : Expr}, (∀ l', l' ∈ labelsE e → l' ∈ labelsE tg) → GoodE p f.chain U e → GoodE p f.chain UA e :=
      fun he hg' => { hg' with u := fun l' hl' => hUA l' ⟨hg'.u l' hl', fun e => by
        subst e; simp only [labelsS, List.cons_append, List.nodup_cons] at hnd; exact hnd.1 (by simp [he _ hl'])⟩ }
    rcases hsh with ⟨lt, y, rfl⟩ | ⟨lt, o, b, rfl⟩ | ⟨lt, o, i, rfl⟩
    · -- a bare name
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .exec [],
          kont := .annA (.name lt y) (if isTop f.chain then some a else none) :: .seq ss :: f.kont } :: fs } := by
        cases hk : f.kind <;> simp_all [Sem.step, A.hs, Sem.execStep, Sem.setC]
      have st1 : PyCore.step I t = some (mk (.exec (.expr (sub lt 62) (.const (sub lt 62) "$none") :: rest))
          (.tryE [] [] :: K')) := by
        simp [PyCore.step, A.ht, hc', trB, trS, blk, annBare, PyCore.execStep, PyCore.top, mk, K', rest, annS]
      have st2 : PyCore.step I (mk (.exec (.expr (sub lt 62) (.const (sub lt 62) "$none") :: rest)) (.tryE [] [] :: K')) =
          some (mk (.ev (.const (sub lt 62) "$none")) (.exprS :: .seq rest :: .tryE [] [] :: K')) := by
        simp [mk, PyCore.step, PyCore.execStep, PyCore.top]
      have st3 : PyCore.step I (mk (.ev (.const (sub lt 62) "$none")) (.exprS :: .seq rest :: .tryE [] [] :: K')) =
          some (mk (.val .none) (.exprS :: .seq rest :: .tryE [] [] :: K')) := by
        simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
      have st4 : PyCore.step I (mk (.val .none) (.exprS :: .seq rest :: .tryE [] [] :: K')) =
          some (mk (.exec []) (.seq rest :: .tryE [] [] :: K')) := by
        simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.nil _))))) (by simp)
        (.inl ((A.mono (hHH (zs := [s]))).set (.exec (goodB_nil _ UA) (by simp)) hann (by esub))) ?_
      intro y' hy x hx
      have hx := pfocus_le hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hH (by simp) _ (by rw [c0 x hx]; exact hTl)
      · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; exact hH (by simp) _ (by rw [← hx, sub_div _ _ (by omega)]; exact hTt)
      · simp [mk, PyCore.focus, PyCore.Expr.label] at hx; exact hH (by simp) _ (by rw [← hx, sub_div _ _ (by omega)]; exact hTt)
      · simp [mk, PyCore.focus] at hx
    · -- a bare attribute: its object, evaluated and dropped
      have ho : GoodE p f.chain U o := GoodB.e hg (by intro x hx; simp [itemsS, itemsE, hx])
        (by intro x hx; simp [trS, blk, annBare, PyCore.itemsS, PyCore.itemsB, pitemsB_app, hx])
        (by intro h; simp_all [okS, okE]) (by intro x hx; simp [labelsS, labelsE, hx])
        (by intro h; simp_all [labelsS, labelsE, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, touchE, hx])
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .ev o,
          kont := .evs [] [] .drop :: .annA (.attr lt o b) (if isTop f.chain then some a else none) :: .seq ss ::
            f.kont } :: fs } := by
        cases hk : f.kind <;> simp_all [Sem.step, A.hs, Sem.execStep, Sem.setC, Sem.startEvs]
      have st1 : PyCore.step I t = some (mk (.exec (.expr (sub lt 62) (trE f.chain o) :: rest)) (.tryE [] [] :: K')) := by
        simp [PyCore.step, A.ht, hc', trB, trS, blk, annBare, PyCore.execStep, PyCore.top, mk, K', rest, annS]
      have st2 : PyCore.step I (mk (.exec (.expr (sub lt 62) (trE f.chain o) :: rest)) (.tryE [] [] :: K')) =
          some (mk (.ev (trE f.chain o)) (.exprS :: .seq rest :: .tryE [] [] :: K')) := by
        simp [mk, PyCore.step, PyCore.execStep, PyCore.top]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
        (.inl ((A.mono (hHH (zs := [s]))).set (.ev (hlt (by intro l' h; simp [labelsE, h]) ho)) (.asg (.evsDrop1 hann))
          (by esub))) ?_
      intro y' hy x hx
      have hx := pfocus_le hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hH (by simp) _ (by rw [c0 x hx]; exact hTl)
      · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; exact hH (by simp) _ (by rw [← hx, sub_div _ _ (by omega)]; exact hTt)
    · -- a bare subscript: its object and index, evaluated and dropped
      have ho : GoodE p f.chain U o := GoodB.e hg (by intro x hx; simp [itemsS, itemsE, hx])
        (by intro x hx; simp [trS, blk, annBare, recR, PyCore.itemsS, PyCore.itemsB, pitemsB_app, PyCore.itemsE, hx])
        (by intro h; simp_all [okS, okE]) (by intro x hx; simp [labelsS, labelsE, hx])
        (by intro h; simp_all [labelsS, labelsE, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, touchE, hx])
      have hi : GoodE p f.chain U i := GoodB.e hg (by intro x hx; simp [itemsS, itemsE, hx])
        (by intro x hx; simp [trS, blk, annBare, recR, PyCore.itemsS, PyCore.itemsB, pitemsB_app, PyCore.itemsE, hx])
        (by intro h; simp_all [okS, okE]) (by intro x hx; simp [labelsS, labelsE, hx])
        (by intro h; simp_all [labelsS, labelsE, List.nodup_cons, List.nodup_append]) (by intro x hx; simp [touchS, touchE, hx])
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .ev o,
          kont := .evs [some i] [] .drop :: .annA (.sub lt o i) (if isTop f.chain then some a else none) :: .seq ss ::
            f.kont } :: fs } := by
        cases hk : f.kind <;> simp_all [Sem.step, A.hs, Sem.execStep, Sem.setC, Sem.startEvs]
      let r := sub lt 62
      let Ke : List (PyCore.Kont σ) := .exprS :: .seq rest :: .tryE [] [] :: K'
      have st1 : PyCore.step I t = some (mk (.exec (.expr r (recR r [trE f.chain o, trE f.chain i]) :: rest))
          (.tryE [] [] :: K')) := by
        simp [PyCore.step, A.ht, hc', trB, trS, blk, annBare, PyCore.execStep, PyCore.top, mk, K', rest, annS, r]
      have st2 : PyCore.step I (mk (.exec (.expr r (recR r [trE f.chain o, trE f.chain i]) :: rest)) (.tryE [] [] :: K')) =
          some (mk (.ev (recR r [trE f.chain o, trE f.chain i])) Ke) := by
        simp [mk, Ke, PyCore.step, PyCore.execStep, PyCore.top]
      obtain ⟨ys3, p3, hf3⟩ := rec_path (I := I) t f' fs' r [trE f.chain i] (.bin r "," (.const r "$args") (trE f.chain o)) Ke
      have st4 : PyCore.step I (mk (.ev (.bin r "," (.const r "$args") (trE f.chain o))) (.binL "," (trE f.chain i) :: Ke)) =
          some (mk (.ev (.const r "$args")) (.binL "," (trE f.chain o) :: .binL "," (trE f.chain i) :: Ke)) := by
        simp [mk, PyCore.step, PyCore.evalStep, PyCore.top]
      have st5 : PyCore.step I (mk (.ev (.const r "$args")) (.binL "," (trE f.chain o) :: .binL "," (trE f.chain i) :: Ke)) =
          some (mk (.val (.data "$args" [])) (.binL "," (trE f.chain o) :: .binL "," (trE f.chain i) :: Ke)) := by
        simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
      have st6 : PyCore.step I (mk (.val (.data "$args" [])) (.binL "," (trE f.chain o) :: .binL "," (trE f.chain i) :: Ke)) =
          some (mk (.ev (trE f.chain o)) (recK [] [trE f.chain i] Ke)) := by
        simp [mk, recK, PyCore.step, PyCore.valStep, PyCore.top]
      refine goal_b (.cons e1 (.nil _)) (by simp)
        (.cons st1 (.cons st2 (p3.append (.cons st4 (.cons st5 (.cons st6 (.nil _))))))) (by simp)
        (.inl ((A.mono (hHH (zs := [s]))).set (.ev (hlt (by intro l' h; simp [labelsE, h]) ho))
          (.asg (.evsDropR (hH (by simp) _ hTt) ⟨⟨hlt (by intro l' h; simp [labelsE, h]) hi, rfl⟩, trivial⟩ hann))
          (by esub))) ?_
      intro y' hy x hx
      have hx := pfocus_le hx
      have hr : ∀ {zs : List (Sem.Config σ)}, s ∈ zs → ∀ x, x = r → Seen (Touch p) H zs (x / 64) :=
        fun hz x e => hH hz _ (by rw [e, sub_div _ _ (by omega)]; exact hTt)
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | hy | rfl | rfl | rfl
      · exact hH (by simp) _ (by rw [c0 x hx]; exact hTl)
      · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; exact hr (by simp) x hx.symm
      · exact hr (by simp) x (hf3 y' hy x hx)
      · simp [mk, PyCore.focus, PyCore.Expr.label] at hx; exact hr (by simp) x hx.symm
      · simp [mk, PyCore.focus, PyCore.Expr.label] at hx; exact hr (by simp) x hx.symm
      · simp [mk, PyCore.focus] at hx

namespace Asg

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore adds a value to an argument record and moves to the record's next expression. -/
theorem rec_next (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (v : Val) (done : List Val)
    (pe : PE) (ps : List PE) (K : List (PyCore.Kont σ)) :
    Path (PyCore.step I) { t with stack := { g' with ctrl := .val v, kont := recK done (pe :: ps) K } :: gs' }
      { t with stack := { g' with ctrl := .ev pe, kont := recK (done ++ [v]) ps K } :: gs' }
      [{ t with stack := { g' with ctrl := .val v, kont := recK done (pe :: ps) K } :: gs' },
       { t with stack := { g' with
         ctrl := .val (.data "$args" (done ++ [v])), kont := .binL "," pe :: ps.map (.binL ",") ++ K } :: gs' }] :=
  .cons (by simp [recK, PyCore.step, PyCore.valStep, PyCore.top])
    (.cons (by simp [recK, PyCore.step, PyCore.valStep, PyCore.top]) (.nil _))

/-- PyCore adds the last value to an argument record and performs the operation. -/
theorem rec_end (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (v : Val) (done : List Val)
    (o : Py.Op) (K : List (PyCore.Kont σ)) :
    Path (PyCore.step I) { t with stack := { g' with ctrl := .val v, kont := recK done [] (.callA (.op o) :: K) } :: gs' }
      { t with stack := { g' with ctrl := .op o (done ++ [v]), kont := K } :: gs' }
      [{ t with stack := { g' with ctrl := .val v, kont := recK done [] (.callA (.op o) :: K) } :: gs' },
       { t with stack := { g' with
         ctrl := .val (.data "$args" (done ++ [v])), kont := .callA (.op o) :: K } :: gs' }] :=
  .cons (by simp [recK, PyCore.step, PyCore.valStep, PyCore.top])
    (.cons (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top]) (.nil _))

/-- PyCore adds a value and a target's source (`SrcR`) to an argument record and performs the operation. -/
theorem rec_src (A : At p H s t f fs f' fs') {U : Label → Prop} {lt : Label} {src : PE} {w : Val}
    (hs : SrcR A.x U lt src w) (v : Val) (done : List Val) (o : Py.Op) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .val v, kont := recK done [src] (.callA (.op o) :: K) } :: fs' }
      { t with stack := { f' with ctrl := .op o (done ++ [v, w]), kont := K } :: fs' } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = lt := by
  obtain ⟨ys, py, -, hf⟩ := srcR_eval (I := I) (t := t) (f' := f') (fs' := fs') rfl hs (recK (done ++ [v]) [] (.callA (.op o) :: K))
  have p2 := rec_end (I := I) t f' fs' w (done ++ [v]) o K
  simp only [List.append_assoc, List.cons_append, List.nil_append] at p2
  refine ⟨_, (rec_next (I := I) t f' fs' v done src [] (.callA (.op o) :: K)).append (py.append p2), by simp, ?_⟩
  intro y hy x hx
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.nil_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | hy | rfl | rfl
  · simp [PyCore.focus] at hx
  · simp [PyCore.focus] at hx
  · exact hf y hy x hx
  · simp [PyCore.focus] at hx
  · simp [PyCore.focus] at hx

/-- PyCore reads a fresh name. -/
theorem pread (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) {r : Label} {x : Name} {v : Val}
    (K : List (PyCore.Kont σ)) (h : rdOf t g' x = some v) :
    PyCore.step I { t with stack := { g' with ctrl := .ev (.name r x none), kont := K } :: gs' } =
      some { t with stack := { g' with ctrl := .val v, kont := K } :: gs' } := by
  have hr : PyCore.readName I { t with stack := { g' with ctrl := .ev (.name r x none), kont := K } :: gs' }
      { g' with ctrl := .ev (.name r x none), kont := K } x none = .ok v := readName_rd h
  simp only [PyCore.step, PyCore.evalStep]; rw [hr]; rfl

/-- The update of an augmented assignment: PyCore reads `.g l` and enters the right operand. -/
theorem aug_upd (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (C : List Scope) (l : Label)
    (op : String) (e : Expr) (w : PyCore.Stmt) (K : List (PyCore.Kont σ)) {old : Val}
    (h : rdOf t g' (fresh "g" l) = some old) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g' with ctrl := .exec [], kont := .seq [augUpd C l op e, w] :: K } :: gs' }
      { t with stack := { g' with
        ctrl := .ev (trE C e), kont := .binR (op ++ "=") old :: .assign (fresh "v" l) :: .seq [w] :: K } :: gs' } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l := by
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { g' with ctrl := c, kont := k } :: gs' }
  let Kv : List (PyCore.Kont σ) := .assign (fresh "v" l) :: .seq [w] :: K
  have s1 := done_seq (I := I) t g' gs' [augUpd C l op e, w] K
  have s2 : PyCore.step I (mk (.exec [augUpd C l op e, w]) K) =
      some (mk (.ev (.bin (sub l 2) (op ++ "=") (nm l 3 (fresh "g" l)) (trE C e))) Kv) := by
    simp [mk, Kv, augUpd, PyCore.step, PyCore.execStep, PyCore.top]
  have s3 : PyCore.step I (mk (.ev (.bin (sub l 2) (op ++ "=") (nm l 3 (fresh "g" l)) (trE C e))) Kv) =
      some (mk (.ev (nm l 3 (fresh "g" l))) (.binL (op ++ "=") (trE C e) :: Kv)) := by
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top]
  have s4 : PyCore.step I (mk (.ev (nm l 3 (fresh "g" l))) (.binL (op ++ "=") (trE C e) :: Kv)) =
      some (mk (.val old) (.binL (op ++ "=") (trE C e) :: Kv)) := pread t g' gs' _ h
  have s5 : PyCore.step I (mk (.val old) (.binL (op ++ "=") (trE C e) :: Kv)) =
      some (mk (.ev (trE C e)) (.binR (op ++ "=") old :: Kv)) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
  refine ⟨_, .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.nil _))))), by simp, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    simp [mk, PyCore.focus, PyCore.Expr.label, PyCore.Stmt.label, augUpd, nm] at hx <;>
    (rw [← hx]; exact sub_div _ _ (by omega))

theorem binop_ne (op : String) : op ++ "=" ≠ "," := by
  intro h; have := congrArg (fun s => s.toList.getLast?) h; simp at this

/-- `__annotations__` as both runs read it. -/
theorem annRead_eq {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {g' : PyCore.Frame σ}
    (hk : g'.kind = fk f.kind) (hns : PyCore.dropReserved g'.ns = f.ns)
    (hgl : ∀ x, ¬ Dot x → pGlob t x = sGlob s x) : PyCore.annRead I t g' = Sem.annRead I s f := by
  have hd : ¬ Dot "__annotations__" := by decide
  have hl : g'.ns.lookup "__annotations__" = f.ns.lookup "__annotations__" := by
    rw [← hns, PyCore.dropReserved, lookup_drop _ hd]
  simp only [PyCore.annRead, Sem.annRead, hk, hl, lookupGlobal_eq hgl hd]
  cases f.kind <;> cases List.lookup "__annotations__" f.ns <;> rfl

/-- PyCore reads fresh names (`x0`, then `ns`) into an argument record and performs `o`. -/
theorem reads_op (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (o : Py.Op)
    (K : List (PyCore.Kont σ)) (P : Label → Prop) :
    ∀ (ns : List (Label × Name × Val)) (done : List Val) (r0 : Label) (x0 : Name) (v0 : Val),
    rdOf t g' x0 = some v0 → (∀ n ∈ ns, rdOf t g' n.2.1 = some n.2.2) → P r0 → (∀ n ∈ ns, P n.1) →
    ∃ ys, Path (PyCore.step I)
      { t with stack := { g' with
        ctrl := .ev (.name r0 x0 none),
        kont := recK done (ns.map fun n => PyCore.Expr.name n.1 n.2.1 none) (.callA (.op o) :: K) } :: gs' }
      { t with stack := { g' with ctrl := .op o (done ++ v0 :: ns.map (·.2.2)), kont := K } :: gs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → P x
  | [], done, r0, x0, v0, h0, _, hr, _ => by
    have s1 := pread (I := I) t g' gs' (r := r0) (recK done [] (.callA (.op o) :: K)) h0
    refine ⟨_, .cons s1 (rec_end (I := I) t g' gs' v0 done o K), ?_⟩
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [PyCore.focus, PyCore.Expr.label] at hx
    rw [← hx]; exact hr
  | n :: ns, done, r0, x0, v0, h0, hv, hr, hn => by
    have s1 := pread (I := I) t g' gs' (r := r0)
      (recK done ((n :: ns).map fun n => PyCore.Expr.name n.1 n.2.1 none) (.callA (.op o) :: K)) h0
    have p2 := rec_next (I := I) t g' gs' v0 done (.name n.1 n.2.1 none) (ns.map fun n => PyCore.Expr.name n.1 n.2.1 none)
      (.callA (.op o) :: K)
    obtain ⟨ys, p3, hf3⟩ := reads_op t g' gs' o K P ns (done ++ [v0]) n.1 n.2.1 n.2.2 (hv n (by simp))
      (fun n' h => hv n' (by simp [h])) (hn n (by simp)) (fun n' h => hn n' (by simp [h]))
    have e : done ++ [v0] ++ n.2.2 :: ns.map (·.2.2) = done ++ v0 :: (n :: ns).map (·.2.2) := by simp
    rw [e] at p3
    refine ⟨_, .cons s1 (p2.append p3), ?_⟩
    intro y hy x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | (rfl | rfl) | hy
    · simp [PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact hr
    · simp [PyCore.focus] at hx
    · simp [PyCore.focus] at hx
    · exact hf3 y hy x hx

/-- PyCore calls an operation on fresh names it reads. -/
theorem cc_reads (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (r : Label) (g : String)
    (o : Py.Op) (hg : Py.constVal I g = .op o) (K : List (PyCore.Kont σ)) (P : Label → Prop)
    (n0 : Label × Name × Val) (ns : List (Label × Name × Val))
    (hv : ∀ n ∈ n0 :: ns, rdOf t g' n.2.1 = some n.2.2) (hr : P r) (hn : ∀ n ∈ n0 :: ns, P n.1) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { g' with
        ctrl := .ev (ccR r g ((n0 :: ns).map fun n => PyCore.Expr.name n.1 n.2.1 none)), kont := K } :: gs' }
      { t with stack := { g' with ctrl := .op o ((n0 :: ns).map (·.2.2)), kont := K } :: gs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → P x := by
  obtain ⟨ys1, p1, -, hf1⟩ := cc_enter (I := I) t g' gs' r g (.name n0.1 n0.2.1 none)
    (ns.map fun n => PyCore.Expr.name n.1 n.2.1 none) K
  rw [hg] at p1
  obtain ⟨ys2, p2, hf2⟩ := reads_op (I := I) t g' gs' o K P ns [] n0.1 n0.2.1 n0.2.2 (hv n0 (by simp))
    (fun n h => hv n (by simp [h])) (hn n0 (by simp)) (fun n h => hn n (by simp [h]))
  refine ⟨_, p1.append p2, ?_⟩
  intro y hy x hx
  rcases List.mem_append.1 hy with hy | hy
  · rw [hf1 y hy x hx]; exact hr
  · exact hf2 y hy x hx

end

end Asg

open Asg in
theorem val_asg : KCase I p true AsgK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  cases hk with
  | @assignK U K0 K0' l ts hU hf g hI k =>
    obtain ⟨t1, g', e2, A1, hgc, hgk, hrd, hag⟩ := pstore0 A.zero (tag := "t") (by decide) hf v (.exec [])
      (.seq (trTs f.chain (nameSrc "t" l) ts) :: .tryE [] [] :: K0')
    refine goal11 (A1.updS (.exec []) (.stMany (ts.map (·, v)) :: K0))
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC])
      (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2) (U := Rm U l) (i := false) ?_ ?_ hfoc
    · rw [hgc]; exact .exec (goodB_nil _ _) (by simp)
    · rw [hgk]; exact .asg (.stManyT hrd g hI (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k))
  | @stAttr U K0 K0' lt a w src hH hs k =>
    obtain ⟨ys, py, hys, hf⟩ := rec_src (I := I) A hs v [] (.setattr a) (.exprS :: K0')
    simp only [List.nil_append] at py
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op (.setattr a) [v, w], kont := .exprS :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    exact goal_b (.cons e1 (.nil _)) (by simp)
      (by rw [t_conf A.ht hc' hK']; exact py) hys (crelI_seen (A.set .op (.core (.exprS k))))
      (fun y hy x hx => .inl (by rw [hf y hy x (pfocus_le hx)]; exact hH))
  | @stSubL U K0 K0' lt i w src hH hg hs k =>
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev i, kont := .stSubR v w :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    have py := rec_next (I := I) t f' fs' v [] (trE f.chain i) [src] (.callA (.op .setitem) :: .exprS :: K0')
    simp only [List.nil_append] at py
    exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py) (by simp)
      (crelI_seen (A.set (.ev hg) (.asg (.stSubR hH hs k))))
      (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus])
  | @stSubR U K0 K0' lt o w src hH hs k =>
    obtain ⟨ys, py, hys, hf⟩ := rec_src (I := I) A hs v [o] .setitem (.exprS :: K0')
    simp only [List.cons_append, List.nil_append] at py
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op .setitem [o, v, w], kont := .exprS :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    exact goal_b (.cons e1 (.nil _)) (by simp)
      (by rw [t_conf A.ht hc' hK']; exact py) hys (crelI_seen (A.set .op (.core (.exprS k))))
      (fun y hy x hx => .inl (by rw [hf y hy x (pfocus_le hx)]; exact hH))
  | @delAttr U K0 K0' a k =>
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op (.delattr a) [v], kont := .exprS :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    have py := rec_end (I := I) t f' fs' v [] (.delattr a) (.exprS :: K0')
    simp only [List.nil_append] at py
    exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py) (by simp)
      (crelI_seen (A.set .op (.core (.exprS k))))
      (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus])
  | @delSubL U K0 K0' i hg k =>
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev i, kont := .delSubR v :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    have py := rec_next (I := I) t f' fs' v [] (trE f.chain i) [] (.callA (.op .delitem) :: .exprS :: K0')
    simp only [List.nil_append] at py
    exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py) (by simp)
      (crelI_seen (A.set (.ev hg) (.asg (.delSubR k))))
      (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus])
  | @delSubR U K0 K0' o k =>
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op .delitem [o, v], kont := .exprS :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    have py := rec_end (I := I) t f' fs' v [o] .delitem (.exprS :: K0')
    simp only [List.cons_append, List.nil_append] at py
    exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py) (by simp)
      (crelI_seen (A.set .op (.core (.exprS k))))
      (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus])
  | @augR U0 K0 K0' l lt op old tg w h1 h2 hU hf ha k =>
    have e2 : PyCore.step I t = some { t with stack := { f' with
        ctrl := .op (.binop (op ++ "=")) [old, v],
        kont := .assign (fresh "v" l) :: .seq [w] :: .tryE [] [] :: K0' } :: fs' } := by
      rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']
      split
      · rename_i h; exact absurd h (binop_ne op)
      · rfl
    exact A.go11 (c := .op (.binop (op ++ "=")) [old, v]) (k := .augW tg :: K0) (U := Rm U0 l)
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]) e2 .op (.asg (.augW h1 h2 hU hf ha k))
      (cov_none A hfoc)
  | @stUnpack U K0 K0' lt ts hH hU hf g hI k =>
    by_cases hv : ∃ vs, v = .tuple vs ∧ vs.length = ts.length
    · obtain ⟨vs, rfl, hl⟩ := hv
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .exec [], kont := .stMany ((ts.map unstar).zip vs) :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, hl]
      let Ka : List (PyCore.Kont σ) := .seq (trItems f.chain lt 0 ts) :: .tryE [] [] :: K0'
      have st1 : PyCore.step I t = some { t with stack := { f' with
          ctrl := .val (.tuple vs), kont := .assign (fresh "u" lt) :: Ka } :: fs' } := by
        rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', PyCore.top, hl, Ka]
      obtain ⟨t2, g', e2, A2, hgc, hgk, hrd, hag⟩ :=
        pstore0 (A.zero.updT (.val (.tuple vs)) (.assign (fresh "u" lt) :: Ka)) (tag := "u") (by decide) hf (.tuple vs)
          (.exec []) Ka
      have st2 : PyCore.step I { t with stack := { f' with
          ctrl := .val (.tuple vs), kont := .assign (fresh "u" lt) :: Ka } :: fs' } = some t2 := by
        rw [pstep_val rfl rfl]; exact e2
      have hk1 := AsgK.stManyU (i := 0) (x := cx p H (rdOf t2 g') (ownOf t2 g') f) hrd hl g hI
        (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k)
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
        (crelI_seen ((A2.updS (.exec []) (.stMany ((ts.map unstar).zip vs) :: K0)).crel (U := Rm U lt) (i := false)
          (by rw [hgc]; exact .exec (goodB_nil _ _) (by simp)) (by rw [hgk]; exact .asg hk1)))
        (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc'])
    · have e1 : Sem.step I s = none := by
        simp only [Sem.step, A.hs, hc, hK, Sem.valStep]
        split
        · rename_i vs; rw [ite_eq_right_iff]; intro h; exact absurd ⟨vs, rfl, by simpa using h⟩ hv
        · rfl
      have e2 : PyCore.step I t = none := by
        rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']
        split
        · rename_i vs; rw [ite_eq_right_iff]; intro h; exact absurd ⟨vs, rfl, h⟩ hv
        · rfl
      exact fin_stuck A e1 e2 (cov_none A hfoc)
  | @augN U K0 K0' l lt y op e h1 h2 hU hf hy g k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag⟩ := pstore0 A.zero (tag := "g") (by decide) (hf "g" (by simp)) v (.exec [])
      (.seq [augUpd f.chain l op e, wrN l lt y] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    obtain ⟨ys, py, hys, hfy⟩ := aug_upd (I := I) t1 g1 fs' f.chain l op e (wrN l lt y) (.tryE [] [] :: K0') hrd
    have py' := py
    rw [← t_conf A1.ht hgc hgk] at py'
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev e, kont := .augR op v (.name y) :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 py') (by simp)
      (crelI_seen (((A1.updT _ _).updS (.ev e) (.augR op v (.name y) :: K0)).crel (U := Rm U l) (i := true) (.ev g)
        (.asg (.augR h1 h2 hU (hf "v" (by simp)) ⟨hy, rfl⟩ (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k)))))
      (fun y' hy' x hx => ?_)
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact absurd (pfocus_le hx) (by simp [PyCore.focus, A.ht, hc'])
    · exact .inl (by rw [hfy y' hy' x (pfocus_le hx)]; exact h1)
  | @augSubL U K0 K0' l lt i op e h1 h2 hU hf hi he k =>
    let Ks : PS := [keyS f.chain l lt i, getI l lt, augUpd f.chain l op e, wrI l lt]
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag⟩ := pstore0 A.zero (tag := "o") (by decide) (hf "o" (by simp)) v (.exec [])
      (.seq Ks :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let t2 : PyCore.Config σ := { t1 with stack := { g1 with ctrl := .exec Ks, kont := .tryE [] [] :: K0' } :: fs' }
    have st2 : PyCore.step I t1 = some t2 := by rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    let Kt : List (PyCore.Kont σ) :=
      .assign (fresh "k" l) :: .seq [getI l lt, augUpd f.chain l op e, wrI l lt] :: .tryE [] [] :: K0'
    have st3 : PyCore.step I t2 = some { t1 with stack := { g1 with ctrl := .ev (trE f.chain i), kont := Kt } :: fs' } := by
      simp [t2, Ks, Kt, keyS, PyCore.step, PyCore.execStep, PyCore.top]
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev i, kont := .augSubI v op e :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 (.nil _)))) (by simp)
      (crelI_seen (((A1.updT _ _).updS (.ev i) (.augSubI v op e :: K0)).crel (U := Rm U l) (i := true) (.ev hi)
        (.asg (.augSubI h1 h2 hU hrd (fun tag ht => hf tag (List.mem_cons_of_mem _ ht))
          he (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k)))))
      (fun y' hy' x hx => ?_)
    have hx := pfocus_le hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy'
    rcases hy' with rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc'] at hx
    · simp [PyCore.focus, A1.ht, hgc] at hx
    · simp [t2, Ks, keyS, PyCore.focus, PyCore.Stmt.label] at hx
      exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
  | @evsDrop1 U K0 K0' k =>
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .val (.tuple [v]), kont := .evsEnd .drop :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
    have e2 : Sem.step I { s with stack := { f with ctrl := .val (.tuple [v]), kont := .evsEnd .drop :: K0 } :: fs } =
        some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
      simp [Sem.step, Sem.valStep, Sem.finish, Sem.setC]
    have st1 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } := by
      rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', PyCore.top]
    exact goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 (.nil _)) (by simp)
      (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) k))
      (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)
  | @evsDropR U K0 K0' lt rest acc ps hH hr k =>
    rcases rest with _ | ⟨_ | e, rest'⟩ <;> rcases ps with _ | ⟨pe, ps'⟩ <;> simp only [PartsR] at hr
    case nil.nil =>
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .val (.tuple (v :: acc).reverse), kont := .evsEnd .drop :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
      have e2 : Sem.step I { s with stack := { f with
          ctrl := .val (.tuple (v :: acc).reverse), kont := .evsEnd .drop :: K0 } :: fs } =
          some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
        simp [Sem.step, Sem.valStep, Sem.finish, Sem.setC]
      let t1 : PyCore.Config σ := { t with stack := { f' with
        ctrl := .val (.data "$args" (acc.reverse ++ [v])), kont := .exprS :: K0' } :: fs' }
      have st1 : PyCore.step I t = some t1 := by
        rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', PyCore.top, recK, t1]
      have st2 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } := by
        simp [t1, PyCore.step, PyCore.valStep, PyCore.top]
      exact goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
        (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) k))
        (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc', t1])
    case cons.some.cons =>
      obtain ⟨⟨hg, rfl⟩, hr'⟩ := hr
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .ev e, kont := .evs rest' (v :: acc) .drop :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
      have py := rec_next (I := I) t f' fs' v acc.reverse (trE f.chain e) ps' (.exprS :: K0')
      have hrev : acc.reverse ++ [v] = (v :: acc).reverse := by simp
      rw [hrev] at py
      exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py) (by simp)
        (crelI_seen (A.set (.ev hg) (.asg (.evsDropR hH hr' k)) (esub_top hK)))
        (cover_none fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus])
    case cons.none.cons =>
      obtain ⟨⟨k6, hk6, rfl⟩, hr'⟩ := hr
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .val .none, kont := .evs rest' (v :: acc) .drop :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
      have py := rec_next (I := I) t f' fs' v acc.reverse (.const (sub lt k6) "$none") ps' (.exprS :: K0')
      have hrev : acc.reverse ++ [v] = (v :: acc).reverse := by simp
      rw [hrev] at py
      let Kr : List (PyCore.Kont σ) := recK (v :: acc).reverse ps' (.exprS :: K0')
      have st3 : PyCore.step I { t with stack := { f' with ctrl := .ev (.const (sub lt k6) "$none"), kont := Kr } :: fs' } =
          some { t with stack := { f' with ctrl := .val .none, kont := Kr } :: fs' } := by
        simp [PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal, Kr, recK]
      refine goal_b (.cons e1 (.nil _)) (by simp) (by rw [t_conf A.ht hc' hK']; exact py.append (.cons st3 (.nil _)))
        (by simp) (crelI_seen (A.set .val (.asg (.evsDropR hH hr' k)) (esub_top hK))) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with (rfl | rfl) | rfl
      · simp [PyCore.focus] at hx
      · simp [PyCore.focus] at hx
      · simp [PyCore.focus, PyCore.Expr.label] at hx; exact .inl (by rw [← hx, sub_div _ _ hk6]; exact hH)
  | @exprBlk U K0 K0' tail htl k =>
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t with stack := { f' with ctrl := c, kont := k } :: fs' }
    have st1 : PyCore.step I t = some (mk (.exec []) (.seq tail :: .tryE [] [] :: K0')) := by
      rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', PyCore.top, mk]
    have st2 := done_seq (I := I) t f' fs' tail (.tryE [] [] :: K0')
    obtain ⟨ys3, p3, hf3⟩ : ∃ ys3, Path (PyCore.step I) (mk (.exec tail) (.tryE [] [] :: K0')) (mk (.exec []) K0') ys3 ∧
        ∀ y ∈ ys3, ∀ x, PyCore.focus y = some x → H (x / 64) := by
      rcases htl with rfl | ⟨l, tg, hl, rfl⟩
      · exact ⟨_, .cons (done_try t f' fs' K0') (.nil _), by intro y hy x hx; simp at hy; subst hy; simp [mk, PyCore.focus] at hx⟩
      · obtain ⟨ys4, p4, -, hf4⟩ := dead_path (I := I) t f' fs' (sub l 9) (annBind f.chain tg) [] (.tryE [] [] :: K0')
        refine ⟨_, p4.append (.cons (done_try t f' fs' K0') (.nil _)), ?_⟩
        intro y hy x hx
        rcases List.mem_append.1 hy with hy | hy
        · rw [hf4 y hy x hx, sub_div _ _ (by omega)]; exact hl
        · simp at hy; subst hy; simp [mk, PyCore.focus] at hx
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 p3)) (by simp)
      (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) k (esub_cons hK))) (fun y hy x hx => ?_)
    have hx := pfocus_le hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    · simp [mk, PyCore.focus] at hx
    · exact .inl (hf3 y hy x hx)
  | @annE U K0 K0' l tg A0 tail h1 h2 hi hn ho htl k =>
    have hT : annT f.chain l tg = [.expr (sub tg.label 58) (.const (sub tg.label 58) "$none")] := by
      cases tg with
      | name lt y => exact absurd rfl (hn lt y)
      | _ => rfl
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag⟩ := pstore0 A.zero (tag := "n") (by decide) (ho.2.1 hi) v (.exec [])
      (.seq (annT f.chain l tg ++ tail) :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let r := sub tg.label 58
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
    have st2 : PyCore.step I t1 = some (mk (.exec (.expr r (.const r "$none") :: tail)) (.tryE [] [] :: K0')) := by
      rw [t_conf A1.ht hgc hgk, hT]; exact done_seq t1 g1 fs' _ _
    have st3 : PyCore.step I (mk (.exec (.expr r (.const r "$none") :: tail)) (.tryE [] [] :: K0')) =
        some (mk (.ev (.const r "$none")) (.exprS :: .seq tail :: .tryE [] [] :: K0')) := by
      simp [mk, PyCore.step, PyCore.execStep, PyCore.top]
    have st4 : PyCore.step I (mk (.ev (.const r "$none")) (.exprS :: .seq tail :: .tryE [] [] :: K0')) =
        some (mk (.val .none) (.exprS :: .seq tail :: .tryE [] [] :: K0')) := by
      simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
    have st5 : PyCore.step I (mk (.val .none) (.exprS :: .seq tail :: .tryE [] [] :: K0')) =
        some (mk (.exec []) (.seq tail :: .tryE [] [] :: K0')) := by
      simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
    have st6 := done_seq (I := I) t1 g1 fs' tail (.tryE [] [] :: K0')
    obtain ⟨ys3, p3, hf3⟩ : ∃ ys3, Path (PyCore.step I) (mk (.exec tail) (.tryE [] [] :: K0')) (mk (.exec []) K0') ys3 ∧
        ∀ y ∈ ys3, ∀ x, PyCore.focus y = some x → x / 64 = l := by
      rcases htl with rfl | rfl
      · exact ⟨_, .cons (done_try t1 g1 fs' K0') (.nil _), by intro y hy x hx; simp at hy; subst hy; simp [mk, PyCore.focus] at hx⟩
      · obtain ⟨ys4, p4, -, hf4⟩ := dead_path (I := I) t1 g1 fs' (sub l 9) (annBind f.chain tg) [] (.tryE [] [] :: K0')
        refine ⟨_, p4.append (.cons (done_try t1 g1 fs' K0') (.nil _)), ?_⟩
        intro y hy x hx
        rcases List.mem_append.1 hy with hy | hy
        · rw [hf4 y hy x hx]; exact sub_div _ _ (by omega)
        · simp at hy; subst hy; simp [mk, PyCore.focus] at hx
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp)
      (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 p3)))))) (by simp)
      (crelI_seen (((A1.updT (.exec []) K0').updS (.exec []) K0).crel (U := U) (i := false) (.exec (goodB_nil _ U) (by simp))
        (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ ho.1⟩ k))) (fun y hy x hx => ?_)
    have hx := pfocus_le hx
    have hlr : r / 64 = tg.label := sub_div _ _ (by omega)
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    · simp [PyCore.focus, A1.ht, hgc] at hx
    · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; exact .inl (by rw [← hx, hlr, ← lbl_eq]; exact h2)
    · simp [mk, PyCore.focus, PyCore.Expr.label] at hx; exact .inl (by rw [← hx, hlr, ← lbl_eq]; exact h2)
    · simp [mk, PyCore.focus] at hx
    · simp [mk, PyCore.focus] at hx
    · exact .inl (by rw [hf3 y hy x hx]; exact h1)
  | @augAttr U K0 K0' l lt a op e h1 h2 hU hf hna he k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, -⟩ := pstore1 A.zero (tag := "o") (by decide) (hf "o" (by simp)) v
      (.exec []) (.seq [getA l lt a, augUpd f.chain l op e, wrA l lt a] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
    let Kg : List (PyCore.Kont σ) := .assign (fresh "g" l) :: .seq [augUpd f.chain l op e, wrA l lt a] :: .tryE [] [] :: K0'
    have st2 : PyCore.step I t1 = some (mk (.exec [getA l lt a, augUpd f.chain l op e, wrA l lt a]) (.tryE [] [] :: K0')) := by
      rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    have st3 : PyCore.step I (mk (.exec [getA l lt a, augUpd f.chain l op e, wrA l lt a]) (.tryE [] [] :: K0')) =
        some (mk (.ev (cc lt 6 ("$op:getattr:" ++ a) [nm lt 7 (fresh "o" l)])) Kg) := by
      simp [mk, Kg, getA, PyCore.step, PyCore.execStep, PyCore.top]
    obtain ⟨ys4, p4, hf4⟩ := cc_reads (I := I) t1 g1 fs' (sub lt 6) _ (.getattr a) (kc_getattr I hna) Kg
      (fun x => x / 64 = lt) (sub lt 7, fresh "o" l, v) [] (by simpa using hrd) (sub_div _ _ (by omega))
      (by simp; exact sub_div _ _ (by omega))
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op (.getattr a) [v], kont := .augAttrV v a op e :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 p4))) (by simp)
      (crelI_seen (((A1.updT (.op (.getattr a) [v]) Kg).updS (.op (.getattr a) [v]) (.augAttrV v a op e :: K0)
        (esub_top hK)).crel (U := Rm U l) (i := true) .op
        (.asg (.augAttrV h1 h2 hU hrd (fun tag ht => hf tag (List.mem_cons_of_mem _ ht)) hna he
          (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k))))) (fun y hy x hx => ?_)
    have hx := pfocus_le hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    · simp [PyCore.focus, A1.ht, hgc] at hx
    · simp [mk, PyCore.focus, PyCore.Stmt.label, getA] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
    · exact .inl (by rw [hf4 y hy x hx]; exact h2)
  | @augAttrV U K0 K0' l lt ob a op e h1 h2 hU hro hf hna he k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, hoth⟩ := pstore1 A.zero (tag := "g") (by decide) (hf "g" (by simp)) v
      (.exec []) (.seq [augUpd f.chain l op e, wrA l lt a] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    obtain ⟨ys, py, hys, hfy⟩ := aug_upd (I := I) t1 g1 fs' f.chain l op e (wrA l lt a) (.tryE [] [] :: K0') hrd
    have py' := py
    rw [← t_conf A1.ht hgc hgk] at py'
    have hro' : rdOf t1 g1 (fresh "o" l) = some ob := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hro
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev e, kont := .augR op v (.attr ob a) :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 py') (by simp)
      (crelI_seen (((A1.updT _ _).updS (.ev e) (.augR op v (.attr ob a) :: K0) (esub_top hK)).crel (U := Rm U l)
        (i := true) (.ev he)
        (.asg (.augR h1 h2 hU (hf "v" (by simp)) ⟨hro', hna, rfl⟩ (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k)))))
      (fun y' hy' x hx => ?_)
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact absurd (pfocus_le hx) (by simp [PyCore.focus, A.ht, hc'])
    · exact .inl (by rw [hfy y' hy' x (pfocus_le hx)]; exact h1)
  | @augSubI U K0 K0' l lt ob op e h1 h2 hU hro hf he k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, hoth⟩ := pstore1 A.zero (tag := "k") (by decide) (hf "k" (by simp)) v
      (.exec []) (.seq [getI l lt, augUpd f.chain l op e, wrI l lt] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    have hro' : rdOf t1 g1 (fresh "o" l) = some ob := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hro
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
    let Kg : List (PyCore.Kont σ) := .assign (fresh "g" l) :: .seq [augUpd f.chain l op e, wrI l lt] :: .tryE [] [] :: K0'
    have st2 : PyCore.step I t1 = some (mk (.exec [getI l lt, augUpd f.chain l op e, wrI l lt]) (.tryE [] [] :: K0')) := by
      rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    have st3 : PyCore.step I (mk (.exec [getI l lt, augUpd f.chain l op e, wrI l lt]) (.tryE [] [] :: K0')) =
        some (mk (.ev (cc lt 7 "$op:getitem" [nm lt 8 (fresh "o" l), nm lt 9 (fresh "k" l)])) Kg) := by
      simp [mk, Kg, getI, PyCore.step, PyCore.execStep, PyCore.top]
    obtain ⟨ys4, p4, hf4⟩ := cc_reads (I := I) t1 g1 fs' (sub lt 7) _ .getitem (kc_getitem I) Kg
      (fun x => x / 64 = lt) (sub lt 8, fresh "o" l, ob) [(sub lt 9, fresh "k" l, v)]
      (by simp; exact ⟨hro', hrd⟩) (sub_div _ _ (by omega))
      (by simp; exact ⟨sub_div _ _ (by omega), sub_div _ _ (by omega)⟩)
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .op .getitem [ob, v], kont := .augSubV ob v op e :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 p4))) (by simp)
      (crelI_seen (((A1.updT (.op .getitem [ob, v]) Kg).updS (.op .getitem [ob, v]) (.augSubV ob v op e :: K0)
        (esub_top hK)).crel (U := Rm U l) (i := true) .op
        (.asg (.augSubV h1 h2 hU hro' hrd (fun tag ht => hf tag (List.mem_cons_of_mem _ ht)) he
          (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k))))) (fun y hy x hx => ?_)
    have hx := pfocus_le hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    · simp [PyCore.focus, A1.ht, hgc] at hx
    · simp [mk, PyCore.focus, PyCore.Stmt.label, getI] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
    · exact .inl (by rw [hf4 y hy x hx]; exact h2)
  | @augSubV U K0 K0' l lt ob iv op e h1 h2 hU hro hri hf he k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, hoth⟩ := pstore1 A.zero (tag := "g") (by decide) (hf "g" (by simp)) v
      (.exec []) (.seq [augUpd f.chain l op e, wrI l lt] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    obtain ⟨ys, py, hys, hfy⟩ := aug_upd (I := I) t1 g1 fs' f.chain l op e (wrI l lt) (.tryE [] [] :: K0') hrd
    have py' := py
    rw [← t_conf A1.ht hgc hgk] at py'
    have hro' : rdOf t1 g1 (fresh "o" l) = some ob := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hro
    have hri' : rdOf t1 g1 (fresh "k" l) = some iv := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hri
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .ev e, kont := .augR op v (.item ob iv) :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
    refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 py') (by simp)
      (crelI_seen (((A1.updT _ _).updS (.ev e) (.augR op v (.item ob iv) :: K0) (esub_top hK)).crel (U := Rm U l)
        (i := true) (.ev he)
        (.asg (.augR h1 h2 hU (hf "v" (by simp)) ⟨hro', hri', rfl⟩
          (KRel.ext ⟨fun _ h => h, hag.mono fun _ h => h ▸ hU⟩ k)))))
      (fun y' hy' x hx => ?_)
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact absurd (pfocus_le hx) (by simp [PyCore.focus, A.ht, hc'])
    · exact .inl (by rw [hfy y' hy' x (pfocus_le hx)]; exact h1)
  | @augW U K0 K0' l lt tg w h1 h2 hU hf ha k =>
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, hoth⟩ := pstore1 A.zero (tag := "v") (by decide) hf v
      (.exec []) (.seq [w] :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
    have st2 : PyCore.step I t1 = some (mk (.exec [w]) (.tryE [] [] :: K0')) := by
      rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    have hag' : Agree U (rdOf t f') (ownOf t f') (rdOf t1 g1) (ownOf t1 g1) := hag.mono fun _ h => h ▸ hU
    have c0 : PyCore.focus t = none := hfoc
    have c1 : PyCore.focus t1 = none := by simp [PyCore.focus, A1.ht, hgc]
    cases tg with
    | name y =>
      obtain ⟨hy, rfl⟩ := ha
      let Ka : List (PyCore.Kont σ) := .assign y :: .seq [] :: .tryE [] [] :: K0'
      have st3 : PyCore.step I (mk (.exec [wrN l lt y]) (.tryE [] [] :: K0')) = some (mk (.ev (nm lt 3 (fresh "v" l))) Ka) := by
        simp [mk, Ka, wrN, nm, PyCore.step, PyCore.execStep, PyCore.top]
      have st4 : PyCore.step I (mk (.ev (nm lt 3 (fresh "v" l))) Ka) = some (mk (.val v) Ka) := pread t1 g1 fs' Ka hrd
      obtain ⟨s1, t3, g, g', e1, e3, A3, hch, hgk3, hgk3', hcc, ha3⟩ :=
        store0 (A1.updT (.val v) Ka) hy v (.exec []) K0 (.exec []) (.seq [] :: .tryE [] [] :: K0')
          (by rw [hK]; simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k) (esub_cons hK)
      have st5 : PyCore.step I (mk (.val v) Ka) = some t3 := by rw [pstep_val rfl rfl]; exact e3
      have e1' : Sem.step I s = some s1 := by simp only [Sem.step, A.hs, hc, hK, Sem.valStep]; exact e1
      have hkm : KRel (cx p H (rdOf t3 g') (ownOf t3 g') g) U false g.kont K0' := by
        rw [hgk3]; exact krel_move k hch (hag'.trans (ha3.mono fun _ h => h.elim)) fun _ h => h
      obtain ⟨ys6, p6, hf6, cr⟩ : ∃ ys6, Path (PyCore.step I) t3 { t3 with stack := { g' with kont := K0' } :: fs' } ys6 ∧
          (∀ y ∈ ys6, PyCore.focus y = none) ∧ CR p g.chain U false g.ctrl g'.ctrl := by
        rcases hcc with ⟨hc1, hc2⟩ | ⟨ex, hc1, hc2⟩
        · have q1 := done_seq (I := I) t3 g' fs' [] (.tryE [] [] :: K0')
          have q2 := done_try (I := I) t3 g' fs' K0'
          rw [← hc2, ← hgk3', t_eta A3.ht] at q1
          rw [← hc2] at q2
          refine ⟨_, .cons q1 (.cons q2 (.nil _)), ?_, by rw [hc1, hc2]; exact .exec (goodB_nil _ U) (by simp)⟩
          intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> simp [PyCore.focus, A3.ht, hc2]
        · obtain ⟨ys, py, -, hy⟩ := ppop_sig (I := I) (i := false) (C := f.chain) (U := U) (c := .raise ex)
            (.inl ⟨ex, rfl, rfl⟩) t3 g' fs' K0' [.seq [], .tryE [] []] (by simp [sPlain, rPlain])
          simp only [List.cons_append, List.nil_append] at py
          rw [← hc2, ← hgk3', t_eta A3.ht] at py
          exact ⟨ys, py, hy, by rw [hc1, hc2]; exact .raise⟩
      refine goal_b (.cons e1' (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 p6)))))
        (by simp) (crelI_seen ((A3.updT g'.ctrl K0').crel cr hkm)) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | hy
      · rw [c0] at hx; cases hx
      · rw [c1] at hx; cases hx
      · simp [mk, PyCore.focus, PyCore.Stmt.label, wrN] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
      · simp [mk, PyCore.focus, PyCore.Expr.label, nm] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
      · simp [mk, PyCore.focus] at hx
      · rw [hf6 y hy] at hx; cases hx
    | attr ob a =>
      obtain ⟨hro, hna, rfl⟩ := ha
      have hro' : rdOf t1 g1 (fresh "o" l) = some ob := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hro
      let Ke : List (PyCore.Kont σ) := .exprS :: .seq [] :: .tryE [] [] :: K0'
      have st3 : PyCore.step I (mk (.exec [wrA l lt a]) (.tryE [] [] :: K0')) =
          some (mk (.ev (cc lt 9 ("$op:setattr:" ++ a) [nm lt 10 (fresh "o" l), nm lt 11 (fresh "v" l)])) Ke) := by
        simp [mk, Ke, wrA, PyCore.step, PyCore.execStep, PyCore.top]
      obtain ⟨ys4, p4, hf4⟩ := cc_reads (I := I) t1 g1 fs' (sub lt 9) _ (.setattr a) (kc_setattr I hna) Ke
        (fun x => x / 64 = lt) (sub lt 10, fresh "o" l, ob) [(sub lt 11, fresh "v" l, v)]
        (by simp; exact ⟨hro', hrd⟩) (sub_div _ _ (by omega))
        (by simp; exact ⟨sub_div _ _ (by omega), sub_div _ _ (by omega)⟩)
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .op (.setattr a) [ob, v], kont := .exprS :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 p4))) (by simp)
        (crelI_seen (((A1.updT (.op (.setattr a) [ob, v]) Ke).updS (.op (.setattr a) [ob, v]) (.exprS :: K0)
          (esub_top hK)).crel (U := U) (i := true) .op
          (.asg (.exprBlk (.inl rfl) (KRel.ext ⟨fun _ h => h, hag'⟩ k))))) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · rw [c0] at hx; cases hx
      · rw [c1] at hx; cases hx
      · simp [mk, PyCore.focus, PyCore.Stmt.label, wrA] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
      · exact .inl (by rw [hf4 y hy x hx]; exact h2)
    | item ob i =>
      obtain ⟨hro, hri, rfl⟩ := ha
      have hro' : rdOf t1 g1 (fresh "o" l) = some ob := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hro
      have hri' : rdOf t1 g1 (fresh "k" l) = some i := by rw [hoth _ (fresh_tag_ne l (by decide))]; exact hri
      let Ke : List (PyCore.Kont σ) := .exprS :: .seq [] :: .tryE [] [] :: K0'
      have st3 : PyCore.step I (mk (.exec [wrI l lt]) (.tryE [] [] :: K0')) =
          some (mk (.ev (cc lt 10 "$op:setitem" [nm lt 11 (fresh "o" l), nm lt 12 (fresh "k" l), nm lt 13 (fresh "v" l)]))
            Ke) := by
        simp [mk, Ke, wrI, PyCore.step, PyCore.execStep, PyCore.top]
      obtain ⟨ys4, p4, hf4⟩ := cc_reads (I := I) t1 g1 fs' (sub lt 10) _ .setitem (kc_setitem I) Ke
        (fun x => x / 64 = lt) (sub lt 11, fresh "o" l, ob) [(sub lt 12, fresh "k" l, i), (sub lt 13, fresh "v" l, v)]
        (by simp; exact ⟨hro', hri', hrd⟩) (sub_div _ _ (by omega))
        (by simp; exact ⟨sub_div _ _ (by omega), sub_div _ _ (by omega), sub_div _ _ (by omega)⟩)
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .op .setitem [ob, i, v], kont := .exprS :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.cons st3 p4))) (by simp)
        (crelI_seen (((A1.updT (.op .setitem [ob, i, v]) Ke).updS (.op .setitem [ob, i, v]) (.exprS :: K0)
          (esub_top hK)).crel (U := U) (i := true) .op
          (.asg (.exprBlk (.inl rfl) (KRel.ext ⟨fun _ h => h, hag'⟩ k))))) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · rw [c0] at hx; cases hx
      · rw [c1] at hx; cases hx
      · simp [mk, PyCore.focus, PyCore.Stmt.label, wrI] at hx; exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact h2)
      · exact .inl (by rw [hf4 y hy x hx]; exact h2)
  | @annK U K0 K0' l tg A0 a h1 hU hf hg hsh ha ho k =>
    -- The entry the store's continuation needs: `annA` at the store's budget `Rm U l` (the store's source
    -- `.t l` is outside it), its annotation at `U`. `AsgK.annA` concludes at `U`, which `AnnOk` makes contain `l`.
    have mkA : ∀ {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l : Label}
        {t A : Expr} {a : Option Expr} {tail : PS}, x.H l → x.H (Sem.Expr.lbl t) →
        a = (if isTop x.C then some A else none) → AnnOk x U l t A →
        (tail = [] ∨ tail = [dead (sub l 9) (annBind x.C t)]) → KRel x U false K K' →
        KRel x (Rm U l) false (.annA t a :: K) (.seq (annS x.C l t A ++ tail) :: .tryE [] [] :: K') :=
      fun h1 h2 ha ho ht k => .asg (.annA h1 h2 ha ho ht k)
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag⟩ := pstore0 A.zero (tag := "t") (by decide) hf v (.exec [])
      (.seq (trT f.chain (nameSrc "t" l) tg (trE f.chain tg) ++ annS f.chain l tg A0) :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let c2 : PyCore.Ctrl σ := .exec (trT f.chain (nameSrc "t" l) tg (trE f.chain tg) ++ annS f.chain l tg A0)
    have st2 : PyCore.step I t1 = some { t1 with stack := { g1 with ctrl := c2, kont := .tryE [] [] :: K0' } :: fs' } := by
      rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .store tg v, kont := .annA tg a :: K0 } :: fs }
    have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, s1]
    have A2 := (((A1.updT c2 (.tryE [] [] :: K0')).updS (.store tg v) (.annA tg a :: K0) (esub_top hK)).mono_H
      (fun _ h => seen_of (zs := [s]) (p := p) h)).mono_H (fun _ h => seen_of (zs := [s1]) (p := p) h)
    have hT1 : Touch p s1 (Sem.Expr.lbl tg) := by rw [lbl_eq]; exact touch_store (s := s1) rfl rfl
    have hkA := mkA (x := cx p (Seen (Touch p) (Seen (Touch p) H [s]) [s1]) (rdOf t1 g1) (ownOf t1 g1) f) (tail := [])
      (.inl (.inl h1)) (.inr ⟨s1, by simp, hT1⟩) ha ho (.inl rfl)
      (KRel.ext ⟨fun _ h => .inl (.inl h), hag.mono fun _ h => h ▸ hU⟩ k)
    rw [List.append_nil] at hkA
    have hsrc : ∀ {lt : Label}, SrcR (cx p (Seen (Touch p) (Seen (Touch p) H [s]) [s1]) (rdOf t1 g1) (ownOf t1 g1) f)
        (Rm U l) lt (nameSrc "t" l lt) v := .name (k := 63) (by omega) (by decide) (rm_self U l) hrd
    refine SimStep.pre e1 (.cons st1 (.cons st2 (.nil _))) (by simp) (cover_none ?_) ?_
    · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hfoc
      · simp [PyCore.focus, A1.ht, hgc]
    rcases hsh with ⟨lt, y, rfl⟩ | ⟨lt, o, b, rfl⟩ | ⟨lt, o, i, rfl⟩
    · exact (store_name A2 rfl rfl (W.nodot lt _ f.chain (hg.s _ (by simp [itemsE]))) hsrc hkA).unseen.goal
    · have hb : okName b = true := by have := hg.ok; simp only [okE, Bool.and_eq_true] at this; exact this.1
      exact (store_attr A2 rfl rfl hg hsrc hkA (kc_setattr I (nc_mangle_pv hg.pv (nc_ok hb)))).unseen.goal
    · exact (store_sub A2 rfl rfl hg hsrc hkA (kc_setitem I)).unseen.goal
  | @annV U K0 K0' l lt y A0 tail h1 h2 hT ho htl k =>
    have hny : ':' ∉ (mangle (priv f.chain) y).toList := ho.2.2.2.2.2 lt y rfl
    obtain ⟨t1, g1, e2, A1, hgc, hgk, hrd, hag, -⟩ := pstore1 A.zero (tag := "n") (by decide) (ho.2.1 hT) v
      (.exec []) (.seq (annT f.chain l (.name lt y) ++ tail) :: .tryE [] [] :: K0')
    have st1 : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
    let Ke : List (PyCore.Kont σ) := .exprS :: .seq tail :: .tryE [] [] :: K0'
    let ca : PE := ccR (sub lt 58) (Gadget.annot (mangle (priv f.chain) y)).name [nm l 7 (fresh "n" l)]
    let Kc : List (PyCore.Kont σ) := recK [] [] (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke)
    have st2 : PyCore.step I t1 = some (mk (.exec (.expr (sub lt 58) ca :: tail)) (.tryE [] [] :: K0')) := by
      rw [t_conf A1.ht hgc hgk]; exact done_seq t1 g1 fs' _ _
    have st3 : PyCore.step I (mk (.exec (.expr (sub lt 58) ca :: tail)) (.tryE [] [] :: K0')) = some (mk (.ev ca) Ke) := by
      simp [mk, Ke, PyCore.step, PyCore.execStep, PyCore.top]
    obtain ⟨ys4, p4, -, hf4⟩ := cc_enter (I := I) t1 g1 fs' (sub lt 58) (Gadget.annot (mangle (priv f.chain) y)).name
      (nm l 7 (fresh "n" l)) [] Ke
    rw [kc_gad I (.annot _) hny] at p4
    have st5 : PyCore.step I (mk (.ev (nm l 7 (fresh "n" l))) Kc) = some (mk (.val v) Kc) := pread t1 g1 fs' Kc hrd
    have st6 : PyCore.step I (mk (.val v) Kc) =
        some (mk (.val (.data "$args" [v])) (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke)) := by
      simp [mk, Kc, recK, PyCore.step, PyCore.valStep, PyCore.top]
    have hA : PyCore.annRead I (mk (.val (.data "$args" [v]))
        (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke))
        { g1 with ctrl := .val (.data "$args" [v]), kont := Ke } = Sem.annRead I s f :=
      annRead_eq A1.hf.kind A1.hf.ns A1.glob
    have hag' : Agree U (rdOf t f') (ownOf t f') (rdOf t1 g1) (ownOf t1 g1) := hag.mono fun _ h => h ▸ ho.1
    have cov : ∀ y ∈ t :: t1 :: mk (.exec (.expr (sub lt 58) ca :: tail)) (.tryE [] [] :: K0') :: (ys4 ++
        [mk (.ev (nm l 7 (fresh "n" l))) Kc, mk (.val v) Kc]), ∀ x, PyCore.focus y = some x → A.x.H (x / 64) := by
      intro y hy x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | hy | rfl | rfl
      · simp [PyCore.focus, A.ht, hc'] at hx
      · simp [PyCore.focus, A1.ht, hgc] at hx
      · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact h2
      · rw [hf4 y hy x hx, sub_div _ _ (by omega)]; exact h2
      · simp [mk, PyCore.focus, PyCore.Expr.label, nm] at hx; rw [← hx, sub_div _ _ (by omega)]; exact h1
      · simp [mk, PyCore.focus] at hx
    have pre : Path (PyCore.step I) t (mk (.val (.data "$args" [v]))
        (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke))
        (t :: t1 :: mk (.exec (.expr (sub lt 58) ca :: tail)) (.tryE [] [] :: K0') :: (ys4 ++
          [mk (.ev (nm l 7 (fresh "n" l))) Kc, mk (.val v) Kc])) :=
      .cons st1 (.cons st2 (.cons st3 (p4.append (.cons st5 (.cons st6 (.nil _))))))
    cases hR : Sem.annRead I s f with
    | ok d =>
      have st7 : PyCore.step I (mk (.val (.data "$args" [v]))
          (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke)) =
          some (mk (.op .setitem [d, .str (mangle (priv f.chain) y), v]) Ke) := by
        rw [hR] at hA
        simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, gad_name (.annot (mangle (priv f.chain) y)) hny, PyCore.gadgetStep, PyCore.argList, hA,
          PyCore.top]
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .op .setitem [d, .str (mangle (priv f.chain) y), v], kont := .exprS :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, hR, Sem.doOp, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (pre.append (.cons st7 (.nil _))) (by simp)
        (crelI_seen (((A1.updT (.op .setitem [d, .str (mangle (priv f.chain) y), v]) Ke).updS
          (.op .setitem [d, .str (mangle (priv f.chain) y), v]) (.exprS :: K0) (esub_top hK)).crel (U := U) (i := true) .op
          (.asg (.exprBlk (htl.imp id fun h => ⟨l, _, h1, h⟩) (KRel.ext ⟨fun _ h => h, hag'⟩ k))))) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      rcases List.mem_append.1 hy with hy | hy
      · exact .inl (cov y hy x hx)
      · simp at hy; subst hy; simp [mk, PyCore.focus] at hx
    | error ex =>
      have hex : PyCore.kontExc Ke = Sem.kontExc f.kont := by
        rw [hK]; simp only [Ke, PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
      have hrn := raiseNew_top (g' := { g1 with ctrl := .val (.data "$args" [v]), kont := Ke }) A1.hfs hex ex
      have st7 : PyCore.step I (mk (.val (.data "$args" [v]))
          (.callA (.prim (Gadget.annot (mangle (priv f.chain) y)).name) :: Ke)) =
          some (mk (.raise (exc (f :: fs) ex)) Ke) := by
        rw [hR] at hA
        simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, gad_name (.annot (mangle (priv f.chain) y)) hny, PyCore.gadgetStep, PyCore.argList, hA,
          PyCore.top, hrn]
      obtain ⟨ys8, p8, -, hf8⟩ := ppop_sig (I := I) (i := false) (C := f.chain) (U := U) (c := .raise (exc (f :: fs) ex))
        (.inl ⟨_, rfl, rfl⟩) t1 { g1 with ctrl := .raise (exc (f :: fs) ex) } fs' K0' [.exprS, .seq tail, .tryE [] []]
        (by simp [sPlain, rPlain])
      simp only [List.cons_append, List.nil_append] at p8
      have e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise (exc (f :: fs) ex), kont := K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.valStep, hR, Sem.setC, raiseNew_s]
      refine goal_b (.cons e1 (.nil _)) (by simp) (pre.append (.cons st7 p8)) (by simp)
        (crelI_seen (((A1.updT (.raise (exc (f :: fs) ex)) K0').updS (.raise (exc (f :: fs) ex)) K0 (esub_cons hK)).crel
          (U := U) (i := false) .raise (KRel.ext ⟨fun _ h => h, hag'⟩ k))) (fun y hy x hx => ?_)
      have hx := pfocus_le hx
      rcases List.mem_append.1 hy with hy | hy
      · exact .inl (cov y hy x hx)
      · rcases List.mem_cons.1 hy with rfl | hy
        · simp [mk, PyCore.focus] at hx
        · rw [hf8 y hy] at hx; cases hx

namespace Asg

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A statement's code ended with an empty block left in PyCore (`seq []`, then the `blk`'s `try`). -/
theorem done_blkEnd (A : At p H s t f fs f' fs') {U : Label → Prop} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc' : f'.ctrl = .exec []) (hK' : f'.kont = .seq [] :: .tryE [] [] :: K0')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs })
    (k : KRel A.x U false K0 K0') (he : EnterSub K0 f.kont) : Goal I p H s t := by
  have e := t_conf A.ht hc' hK'
  refine goal_b (.cons e1 (.nil _)) (by simp)
    (.cons (by rw [e]; exact done_seq (I := I) t f' fs' [] (.tryE [] [] :: K0')) (.cons (done_try t f' fs' K0') (.nil _)))
    (by simp)
    (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) k he)) (cover_none ?_)
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc']

/-- The store of the next target of `stMany`: Surf enters it, PyCore enters the target's code. -/
theorem done_store (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {tg : Expr} {v : Val}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {src : Label → PE} {rest : PS}
    (hc' : f'.ctrl = .exec []) (hK' : f'.kont = .seq (trT f.chain src tg (trE f.chain tg) ++ rest) :: K0')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .store tg v, kont := K0 } :: fs })
    (hg : GoodE p f.chain U tg)
    (hT : SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain src tg (trE f.chain tg))) (PI p))
    (hs : SrcR A.x U tg.label (src tg.label) v)
    (hk : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U false K0 (.seq rest :: K0'))
    (he : EnterSub K0 f.kont) : Goal I p H s t := by
  have st1 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .exec (trT f.chain src tg (trE f.chain tg) ++ rest), kont := K0' } :: fs' } := by
    rw [t_conf A.ht hc' hK']; exact done_seq (I := I) t f' fs' _ K0'
  have A1 := (A.zero.upd (.store tg v) K0 (.exec (trT f.chain src tg (trE f.chain tg) ++ rest)) K0' he).mono_H
    (fun _ h => seen_of (zs := [s]) (p := p) h)
  refine SimStep.pre e1 (.cons st1 (.nil _)) (by simp) (cover_none ?_)
    (store_sim tg A1 W rfl rfl hg hT (srcR_ext ⟨fun _ h => seen_of h, Agree.refl _ _ _⟩ hs) hk)
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp [PyCore.focus, A.ht, hc']

end

theorem goodEs_tail {C : List Scope} {U : Label → Prop} {e : Expr} {es : List Expr} (h : GoodEs p C U (e :: es)) :
    GoodEs p C U es := fun x hx => h x (List.mem_cons_of_mem _ hx)

end Asg

namespace Asg

theorem GoodE.up {C : List Scope} {U : Label → Prop} {e : Expr} {l : Label} (h : GoodE p C (Rm U l) e) :
    GoodE p C U e := { h with u := fun l' hl' => (h.u l' hl').1 }

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore's steps before a simulation step: they evaluate no node and shorten the continuation. -/
theorem goal_ppre {t0 : PyCore.Config σ} {ys : List (PyCore.Config σ)}
    (pb : Path (PyCore.step I) t0 t ys) (hys : ys ≠ []) (hcov : ∀ y ∈ ys, PyCore.focus y = none)
    (hμ : μ s t ≤ μ s t0) (h : Goal I p H s t) : Goal I p H s t0 := by
  have cv : ∀ {zs : List (Sem.Config σ)}, Cover (Touch p) pfocus H zs ys := cover_none hcov
  rcases h with ⟨a', b', xs, ys2, pa, ha, pb2, hb, hf, hc⟩ | ⟨a', b', xs, ys2, pa, hxs, pb2, hys2, hr, hc⟩ |
      ⟨a', xs, pa, hxs, hr, hlt⟩ | ⟨b', ys2, pb2, hys2, hr, hlt, hc⟩
  · refine .inl ⟨a', b', xs, ys ++ ys2, pa, ha, pb.append pb2, hb, hf, ?_⟩
    intro y hy; rcases List.mem_cons.1 hy with rfl | hy
    · exact hc _ List.mem_cons_self
    · rcases List.mem_append.1 hy with hy | hy
      · exact cv y hy
      · exact hc y (List.mem_cons_of_mem _ hy)
  · exact .inr (.inl ⟨a', b', xs, ys ++ ys2, pa, hxs, pb.append pb2, by simp [hys], hr, cv.append hc⟩)
  · exact .inr (.inl ⟨a', t, xs, ys, pa, hxs, pb, hys, hr, cv⟩)
  · exact .inr (.inr (.inr ⟨b', ys ++ ys2, pb.append pb2, by simp [hys], hr, by omega, cv.append hc⟩))

/-- PyCore enters the next target of a `del` through its blocks. -/
theorem del_strip {C : List Scope} {ts : List Expr} {Kp K'' : List (PyCore.Kont σ)} (h : DelSeg C ts Kp K'')
    (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) :
    (ts = [] → ∃ ys, Path (PyCore.step I) { t with stack := { g' with ctrl := .exec [], kont := Kp } :: gs' }
      { t with stack := { g' with ctrl := .exec [], kont := K'' } :: gs' } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, PyCore.focus y = none) ∧
    (∀ tg ts', ts = tg :: ts' → ∃ ys rest Krest, Path (PyCore.step I)
      { t with stack := { g' with ctrl := .exec [], kont := Kp } :: gs' }
      { t with stack := { g' with ctrl := .exec (trD C tg (trT C deadSrc tg (trE C tg)) ++ rest), kont := Krest } :: gs' }
      ys ∧ ys ≠ [] ∧ (∀ y ∈ ys, PyCore.focus y = none) ∧ Krest.length < Kp.length ∧
      DelSeg C ts' (.seq rest :: Krest) K'') := by
  induction h with
  | @base ts K'' =>
    refine ⟨fun e => ?_, fun tg ts' e => ?_⟩
    · subst e
      exact ⟨_, .cons (done_seq t g' gs' [] K'') (.nil _), by simp, by intro y hy; simp at hy; subst hy; simp [PyCore.focus]⟩
    · subst e
      exact ⟨_, trDs C ts', K'', .cons (done_seq t g' gs' _ K'') (.nil _), by simp,
        by intro y hy; simp at hy; subst hy; simp [PyCore.focus], by simp, .base⟩
  | @nest es ts K1 K'' hd ih =>
    cases es with
    | nil =>
      have p0 : Path (PyCore.step I) { t with stack := { g' with ctrl := .exec [], kont := .seq (trDs C []) :: .tryE [] [] :: K1 } :: gs' }
          { t with stack := { g' with ctrl := .exec [], kont := K1 } :: gs' } _ :=
        .cons (done_seq t g' gs' [] _) (.cons (done_try t g' gs' K1) (.nil _))
      have hf0 : ∀ y ∈ [{ t with stack := { g' with ctrl := .exec [], kont := .seq (trDs C []) :: .tryE [] [] :: K1 } :: gs' },
          { t with stack := { g' with ctrl := .exec [], kont := .tryE [] [] :: K1 } :: gs' }], PyCore.focus y = none := by
        intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [PyCore.focus]
      refine ⟨fun e => ?_, fun tg ts' e => ?_⟩
      · obtain ⟨ys, py, -, hf⟩ := ih.1 e
        exact ⟨_, p0.append py, by simp, fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hf0 y hy
          · exact hf y hy⟩
      · obtain ⟨ys, rest, Krest, py, -, hf, hl, hd'⟩ := ih.2 tg ts' e
        exact ⟨_, rest, Krest, p0.append py, by simp, fun y hy => by
          rcases List.mem_append.1 hy with hy | hy
          · exact hf0 y hy
          · exact hf y hy, by simp at hl ⊢; omega, hd'⟩
    | cons e0 es0 =>
      refine ⟨fun e => by simp at e, fun tg ts' e => ?_⟩
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, trDs C es0, .tryE [] [] :: K1, .cons (done_seq t g' gs' _ _) (.nil _), by simp,
        by intro y hy; simp at hy; subst hy; simp [PyCore.focus], by simp, .nest hd⟩

theorem delOks_mem : ∀ {es : List Expr}, delOks es = true → ∀ {e}, e ∈ es → delOk e = true
  | [], _, _, h => by simp at h
  | a :: es, h, e, he => by
    simp only [delOks, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact delOks_mem h.2 he

theorem delOks_append : ∀ (a b : List Expr), delOks (a ++ b) = (delOks a && delOks b)
  | [], _ => by simp [delOks]
  | x :: a, b => by simp [delOks, delOks_append a b, Bool.and_assoc]

theorem unstar_delOk {e : Expr} (h : delOk e = true) : unstar e = e := by
  cases e <;> simp_all [delOk, unstar]

theorem del_kexc {C : List Scope} {ts : List Expr} {rest : PS} {Krest K' : List (PyCore.Kont σ)}
    (hd : DelSeg C ts (.seq rest :: Krest) (.tryE [] [] :: K')) : PyCore.kontExc Krest = PyCore.kontExc K' := by
  have := kexc_del hd; simpa [PyCore.kontExc] using this

/-- `del`'s next target: Surf at `delMany (tg :: ts)`, PyCore at the target's code. -/
theorem del_head (W : WF p) : ∀ (n : Nat) (tg : Expr), sizeOf tg < n →
    ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
      {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} {ts : List Expr}
      {K : List (Sem.Kont σ)} {K' Krest : List (PyCore.Kont σ)} {rest : PS},
    At0 p H s t f fs f' fs' → f.ctrl = .exec [] → f.kont = .delMany (tg :: ts) :: K →
    f'.ctrl = .exec (trD f.chain tg (trT f.chain deadSrc tg (trE f.chain tg)) ++ rest) → f'.kont = Krest →
    GoodEs p f.chain U (tg :: ts) → delOks (tg :: ts) = true →
    DelSeg f.chain ts (.seq rest :: Krest) (.tryE [] [] :: K') →
    KRel (cx p H (rdOf t f') (ownOf t f') f) U false K K' → Goal I p H s t := by
  intro n
  induction n with
  | zero => intro tg h; omega
  | succ n ih =>
    intro tg hn H s t f fs f' fs' U ts K K' Krest rest A hc hK hc' hK' hgs hdo hd hk
    simp only [delOks, Bool.and_eq_true] at hdo
    have hg : GoodE p f.chain U tg := hgs tg (by simp)
    have hT : Touch p s tg.label := .inr (by rw [A.hs]; simp [TouchF, hc, hK, lbl_eq])
    have hcv : ∀ (ys : List (PyCore.Config σ)) {zs : List (Sem.Config σ)}, s ∈ zs →
        (∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = tg.label) → Cover (Touch p) pfocus H zs ys :=
      fun ys zs hz h y hy x hx => .inr ⟨s, hz, by rw [h y hy x (pfocus_le hx)]; exact hT⟩
    have hex : PyCore.kontExc f'.kont = Sem.kontExc f.kont := by
      rw [hK', del_kexc hd, hK, KRel.kexc hk]; rfl
    have hdel : KRel (cx p H (rdOf t f') (ownOf t f') f) U false (.delMany ts :: K) (.seq rest :: Krest) :=
      .asg (.delMany (goodEs_tail hgs) hdo.2 hd hk)
    have e0 := t_conf A.ht hc' hK'
    by_cases hsh : (∃ lt y, tg = .name lt y) ∨ (∃ lt o a, tg = .attr lt o a) ∨ (∃ lt o i, tg = .sub lt o i) ∨
      (∃ lt es, tg = .tuple lt es ∨ tg = .list lt es)
    case neg =>
      have e1 : Sem.step I s = none := by
        cases tg <;> first
          | exact absurd (.inl ⟨_, _, rfl⟩) hsh | exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hsh
          | exact absurd (.inr (.inr (.inl ⟨_, _, _, rfl⟩))) hsh
          | exact absurd (.inr (.inr (.inr ⟨_, _, .inl rfl⟩))) hsh
          | exact absurd (.inr (.inr (.inr ⟨_, _, .inr rfl⟩))) hsh
          | simp only [Sem.step, A.hs, hc, hK, Sem.doneStep]
      have htr : trD f.chain tg (trT f.chain deadSrc tg (trE f.chain tg)) =
          [stuckAt (sub tg.label 55), dead (sub tg.label 54) (trT f.chain deadSrc tg (trE f.chain tg))] := by
        cases tg <;> first
          | exact absurd (.inl ⟨_, _, rfl⟩) hsh | exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hsh
          | exact absurd (.inr (.inr (.inl ⟨_, _, _, rfl⟩))) hsh
          | exact absurd (.inr (.inr (.inr ⟨_, _, .inl rfl⟩))) hsh
          | exact absurd (.inr (.inr (.inr ⟨_, _, .inr rfl⟩))) hsh
          | rfl
      rw [htr, List.cons_append] at hc'
      refine goal_stuck A e1 (by rw [t_conf A.ht hc' hK']; exact .nil _) ?_ (by rw [sub_div _ _ (by omega)]; exact hT)
      intro y hy x hx
      simp at hy; subst hy; simp [PyCore.focus, PyCore.Stmt.label, stuckAt] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
    rcases hsh with ⟨lt, y, rfl⟩ | ⟨lt, o, a, rfl⟩ | ⟨lt, o, i, rfl⟩ | ⟨lt, es, htg⟩
    · -- a name
      have hy : ¬ Dot (mangle (priv f.chain) y) := W.nodot lt _ f.chain (hg.s _ (by simp [itemsE]))
      obtain ⟨s1, t1, g, g', e1, e2, A1, hch, hgk, hgk', hcc, ha⟩ := del0 A hy (.delMany ts :: K) (sub lt 0) rest hex (esub_top hK)
      have e1' : Sem.step I s = some s1 := by simp only [Sem.step, A.hs, hc, hK, Sem.doneStep]; exact e1
      have e2' : PyCore.step I t = some t1 := by
        rw [pstep_exec A.ht (by rw [hc']; rfl)]; exact e2
      refine goal_b (.cons e1' (.nil _)) (by simp) (.cons e2' (.nil _)) (by simp)
        (crelI_seen (A1.crel (U := U) (i := false) ?_ ?_)) (hcv _ (by simp) ?_)
      · rcases hcc with ⟨h1, h2⟩ | ⟨e, h1, h2⟩ <;> rw [h1, h2]
        · exact .exec (goodB_nil _ U) (by simp)
        · exact .raise
      · rw [hgk, hgk', hK']; exact krel_move hdel hch (ha.mono fun _ h => h.elim) fun _ h => h
      · intro y hy x hx; simp at hy; subst hy
        simp [PyCore.focus, A.ht, hc', trD, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · -- an attribute
      have ha : okName a = true := by have := hg.ok; simp only [okE, Bool.and_eq_true] at this; exact this.1
      have ho : GoodE p f.chain U o := by clear hcv hex hdel e0 hk hd hgs hT hc' hK' hc hK; subg
      let a' := mangle (priv f.chain) a
      let K1 : List (PyCore.Kont σ) := .exprS :: .seq rest :: Krest
      obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lt 1) ("$op:delattr:" ++ a') (trE f.chain o) [] K1
      rw [kc_delattr I (nc_mangle_pv hg.pv (nc_ok ha))] at pc
      have st1 : PyCore.step I t = some { t with stack := { f' with
          ctrl := .ev (ccR (sub lt 1) ("$op:delattr:" ++ a') [trE f.chain o]), kont := K1 } :: fs' } := by
        rw [e0]; simp [PyCore.step, PyCore.execStep, PyCore.top, trD, K1, a', cc]
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .ev o, kont := .delAttr (Sem.mg f a) :: .delMany ts :: K } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 pc) (by simp)
        (crelI_seen ((A.upd _ _ _ _ (esub_top2 hK)).crel (U := U) (i := true) (.ev ho) (.asg (.delAttr hdel))))
        (hcv _ (by simp) ?_)
      intro y hy x hx
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [PyCore.focus, A.ht, hc', trD, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
      · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
    · -- a subscript
      have ho : GoodE p f.chain U o := by clear hcv hex hdel e0 hk hd hgs hT hc' hK' hc hK; subg
      have hi : GoodE p f.chain U i := by clear hcv hex hdel e0 hk hd hgs hT hc' hK' hc hK ho; subg
      let K1 : List (PyCore.Kont σ) := .exprS :: .seq rest :: Krest
      obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lt 1) "$op:delitem" (trE f.chain o)
        [trE f.chain i] K1
      rw [kc_delitem I] at pc
      have st1 : PyCore.step I t = some { t with stack := { f' with
          ctrl := .ev (ccR (sub lt 1) "$op:delitem" [trE f.chain o, trE f.chain i]), kont := K1 } :: fs' } := by
        rw [e0]; simp [PyCore.step, PyCore.execStep, PyCore.top, trD, K1, cc]
      have e1 : Sem.step I s = some { s with stack := { f with
          ctrl := .ev o, kont := .delSubL i :: .delMany ts :: K } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 pc) (by simp)
        (crelI_seen ((A.upd _ _ _ _ (esub_top2 hK)).crel (U := U) (i := true) (.ev ho) (.asg (.delSubL hi hdel))))
        (hcv _ (by simp) ?_)
      intro y hy x hx
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [PyCore.focus, A.ht, hc', trD, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
      · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
    · -- a tuple or list: its targets first
      have hlt : tg.label = lt := by rcases htg with rfl | rfl <;> rfl
      have htr : trD f.chain tg (trT f.chain deadSrc tg (trE f.chain tg)) = [blk lt (trDs f.chain es)] := by
        rcases htg with rfl | rfl <;> rfl
      have hst : Sem.step I s = some { s with stack := { f with
          ctrl := .exec [], kont := .delMany (es ++ ts) :: K } :: fs } := by
        rcases htg with rfl | rfl <;> simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
      let Kn : List (PyCore.Kont σ) := .tryE [] [] :: .seq rest :: Krest
      let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .exec (trDs f.chain es), kont := Kn } :: fs' }
      have st1 : PyCore.step I t = some t1 := by
        rw [e0, htr]; simp [PyCore.step, PyCore.execStep, PyCore.top, blk, t1, Kn]
      have cv1 : Cover (Touch p) pfocus H [s] [t] := hcv _ (by simp) (by
        intro y hy x hx; simp at hy; subst hy
        simp [PyCore.focus, A.ht, hc', htr, blk, PyCore.Stmt.label] at hx; rw [← hx, hlt]; exact sub_div _ _ (by omega))
      have hdes : delOks es = true := by rcases htg with rfl | rfl <;> exact hdo.1
      have hes : ∀ e ∈ es, GoodE p f.chain U e := fun e he => by
        rw [← unstar_delOk (delOks_mem hdes he)]; exact GoodE.up (goodE_elt htg hg he)
      cases es with
      | nil =>
        have st2 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .exec [], kont := .seq rest :: Krest } :: fs' } :=
          done_try t f' fs' _
        exact goal_b (.cons hst (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
          (crelI_seen ((A.upd _ _ _ _ (esub_top hK)).crel (U := U) (i := false) (.exec (goodB_nil _ U) (by simp)) hdel))
          (by
            intro y hy x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl
            · exact cv1.mono (fun _ h => seen_sub (by simp) _ h) _ (by simp) x hx
            · simp [t1, PyCore.focus, trDs] at hx; have := pfocus_le hx; simp [t1, PyCore.focus, trDs] at this)
      | cons e es' =>
        have he : sizeOf e < n := by
          have h1 : sizeOf e < sizeOf (e :: es') := List.sizeOf_lt_of_mem (by simp)
          rcases htg with rfl | rfl <;> simp at hn <;> omega
        have hgs' : GoodEs p f.chain U (e :: (es' ++ ts)) := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hes x (by simp)
          · rcases List.mem_append.1 hx with hx | hx
            · exact hes x (by simp [hx])
            · exact hgs x (by simp [hx])
        have hdo' : delOks (e :: (es' ++ ts)) = true := by
          rw [← List.cons_append, delOks_append]; simp [hdes, hdo.2]
        have A1 := (A.upd (.exec []) (.delMany ((e :: es') ++ ts) :: K) (.exec (trDs f.chain (e :: es'))) Kn
          (esub_top hK)).mono_H
          (fun _ h => seen_of (zs := [s]) (p := p) h)
        have hg1 := ih e he A1 rfl (by rfl) (by simp [trDs]) rfl hgs' hdo' (.nest hd) (KRel.seen hk)
        exact SimStep.pre hst (.cons st1 (.nil _)) (by simp) cv1 hg1

end

/-- The items of any target's translation as an expression are items of its store. -/
theorem trT_items_all {C : List Scope} : ∀ (n : Nat) (tg : Expr), sizeOf tg < n → ∀ (src : Label → PE) x,
    x ∈ PyCore.itemsE R0 (trChain C) (trE C tg) → x ∈ PyCore.itemsB R0 (trChain C) (trT C src tg (trE C tg)) := by
  intro n
  induction n with
  | zero => intro tg h; omega
  | succ n ih =>
    intro tg hs src x hx
    have hun : ∀ {lt} {ts : List Expr}, sizeOf ts < n →
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "tuple") (trA C ts ++ ts.map starMark)) ∨
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "list") (trA C ts ++ ts.map starMark)) →
        x ∈ PyCore.itemsB R0 (trChain C) [blk lt (.assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) ::
          trItems C lt 0 ts)] := by
      intro lt ts hs hx
      obtain ⟨t, ht, hx⟩ : ∃ t ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar t)) := by
        rcases hx with hx | hx <;> exact disp_items hx
      have hlt : sizeOf (unstar t) < n :=
        Nat.lt_of_le_of_lt (sizeOf_unstar t) (Nat.lt_trans (List.sizeOf_lt_of_mem ht) hs)
      have hi := trItems_items 0 ts t ht fun j => ih (unstar t) hlt (itemSrc lt j) x hx
      simp [blk, PyCore.itemsB, PyCore.itemsS, hi]
    cases tg with
    | name lt y => simp [trE, trT, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS] at hx ⊢; exact .inl hx
    | attr lt o a =>
      simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢; exact .inl hx
    | sub lt o i =>
      simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢
      rcases hx with h | h <;> simp [h]
    | tuple lt ts => exact hun (by simp at hs; omega) (.inl (by simpa [trE] using hx))
    | list lt ts => exact hun (by simp at hs; omega) (.inr (by simpa [trE] using hx))
    | star ls a =>
      have hx' : x ∈ PyCore.itemsE R0 (trChain C) (trE C a) := by
        simp [trE, gad, cc, ccR, recR, PyCore.itemsE] at hx; exact hx
      have := ih a (by simp at hs; omega) src x hx'
      simp [trT, dead, stuckAt, ccR, recR, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, this]
    | _ => simp [trT, dead, stuckAt, ccR, recR, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, hx]

theorem trItems_drop {C : List Scope} {lt : Label} {x : PyCore.Item} : ∀ (j k : Nat) (ts : List Expr),
    x ∈ PyCore.itemsB R0 (trChain C) (trItems C lt (j + k) (ts.drop k)) →
    x ∈ PyCore.itemsB R0 (trChain C) (trItems C lt j ts)
  | _, 0, _, h => h
  | _, _ + 1, [], h => by simp [trItems, PyCore.itemsB] at h
  | j, k + 1, a :: ts, h => by
    rw [trItems_cons, pitemsB_app, List.mem_append]
    exact .inr (trItems_drop (j + 1) k ts (by rw [show j + 1 + k = j + (k + 1) by omega]; simpa using h))

theorem trDs_mem {C : List Scope} {x : PyCore.Item} {t : Expr} :
    ∀ {ts : List Expr}, t ∈ ts → x ∈ PyCore.itemsB R0 (trChain C) (trD C t (trT C deadSrc t (trE C t))) →
      x ∈ PyCore.itemsB R0 (trChain C) (trDs C ts)
  | [], h, _ => by simp at h
  | a :: ts, h, hx => by
    simp only [trDs, pitemsB_app, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl hx
    · exact .inr (trDs_mem h hx)

/-- The items of a `del` target's translation as an expression are items of its deletion. -/
theorem trD_items_all {C : List Scope} : ∀ (n : Nat) (tg : Expr), sizeOf tg < n → ∀ x,
    x ∈ PyCore.itemsE R0 (trChain C) (trE C tg) →
      x ∈ PyCore.itemsB R0 (trChain C) (trD C tg (trT C deadSrc tg (trE C tg))) := by
  intro n
  induction n with
  | zero => intro tg h; omega
  | succ n ih =>
    intro tg hs x hx
    have hun : ∀ {lt} {ts : List Expr}, sizeOf ts < n →
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "tuple") (trA C ts ++ ts.map starMark)) ∨
        x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "list") (trA C ts ++ ts.map starMark)) →
        x ∈ PyCore.itemsB R0 (trChain C) [blk lt (trDs C ts)] := by
      intro lt ts hs hx
      obtain ⟨t, ht, hx⟩ : ∃ t ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar t)) := by
        rcases hx with hx | hx <;> exact disp_items hx
      have hlt : sizeOf t < n := Nat.lt_trans (List.sizeOf_lt_of_mem ht) hs
      have hi : x ∈ PyCore.itemsB R0 (trChain C) (trD C t (trT C deadSrc t (trE C t))) := by
        cases t with
        | star ls a =>
          have := trT_items_all (C := C) _ a (Nat.lt_succ_self _) deadSrc x hx
          simp [trD, trT, dead, stuckAt, ccR, recR, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, this]
        | _ => exact ih _ hlt x hx
      simp [blk, PyCore.itemsB, PyCore.itemsS, trDs_mem ht hi]
    cases tg with
    | name lt y => simp [trE, trD, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS] at hx ⊢; exact hx
    | attr lt o a =>
      simp [trE, trD, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢; exact hx
    | sub lt o i =>
      simp [trE, trD, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢; exact hx
    | tuple lt ts => exact hun (by simp at hs; omega) (.inl (by simpa [trE] using hx))
    | list lt ts => exact hun (by simp at hs; omega) (.inr (by simpa [trE] using hx))
    | _ =>
      have := trT_items_all (C := C) _ _ (Nat.lt_succ_self _) deadSrc x hx
      simp [trD, dead, stuckAt, ccR, recR, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, this]

end Asg

open Asg in
theorem done_asg : KCase I p false AsgK CDone := by
  intro H s t f fs f' fs' U A W ⟨hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @stManyT U0 K0 K0' l ts v hr g hI k =>
    cases ts with
    | nil =>
      exact done_blkEnd A hc' (by rw [hK']; rfl) (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]) k
        (esub_cons hK)
    | cons tg ts' =>
      exact done_store (tg := tg) (v := v) (K0 := .stMany (ts'.map (·, v)) :: K0) A W hc' (by rw [hK']; rfl)
        (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]) (g tg (by simp))
        (fun x hx => hI x (by simp [trTs, pitemsB_app, hx]))
        (.name (k := 63) (by omega) (by decide) (rm_self U0 l) hr)
        (.asg (.stManyT hr (goodEs_tail g) (fun x hx => hI x (by simp [trTs, pitemsB_app, hx])) (KRel.seen k)))
        (esub_top hK)
  | @stManyU U0 K0 K0' lt ts ws i hr hl g hI k =>
    cases hd : ts.drop i with
    | nil =>
      have : ws.drop i = [] := by
        apply List.eq_nil_of_length_eq_zero; have := congrArg List.length hd; simp at this ⊢; omega
      exact done_blkEnd A hc' (by rw [hK', hd]; rfl)
        (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC, hd, this]) k (esub_cons hK)
    | cons t0 rest =>
      obtain ⟨w, wrest, hw⟩ : ∃ w wrest, ws.drop i = w :: wrest := by
        cases h2 : ws.drop i with
        | nil => have := congrArg List.length hd; have h3 := congrArg List.length h2; simp at this h3; omega
        | cons w wrest => exact ⟨w, wrest, rfl⟩
      have hd1 : ts.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hw1 : ws.drop (i + 1) = wrest := by rw [← List.drop_drop, hw]; rfl
      have hwi : ws[i]? = some w := by have := congrArg (·[0]?) hw; simpa using this
      have ht0 : t0 ∈ ts := List.mem_of_mem_drop (by rw [hd]; simp)
      have hk1 := AsgK.stManyU (i := i + 1) (x := cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) hr hl g hI
        (KRel.seen k)
      rw [hd1, hw1] at hk1
      exact done_store (src := itemSrc lt i) (tg := unstar t0) (v := w)
        (K0 := .stMany ((rest.map unstar).zip wrest) :: K0) A W hc'
        (by rw [hK', hd, trItems_cons])
        (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC, hd, hw])
        (g _ (List.mem_map_of_mem ht0))
        (fun x hx => hI x (trItems_drop 0 i ts (by rw [Nat.zero_add, hd, trItems_cons, pitemsB_app]; simp [hx])))
        (.item (rm_self U0 lt) hr hwi) (.asg hk1) (esub_top hK)
  | @annA U0 K0 K0' l tg A0 a tail h1 h2 ha ho htl k =>
    have hcv : ∀ {zs : List (Sem.Config σ)} (ys : List (PyCore.Config σ)),
        (∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l) → Cover (Touch p) pfocus H zs ys :=
      fun ys h y hy x hx => .inl (by rw [h y hy x (pfocus_le hx)]; exact h1)
    change f'.kont = .seq (annS f.chain l tg A0 ++ tail) :: .tryE [] [] :: K0' at hK'
    have e := t_conf A.ht hc' hK'
    cases hT : isTop f.chain
    · -- a function body: the annotation is in a branch that never runs
      have ha' : a = none := by rw [ha]; simp [hT]
      subst ha'
      have hS : annS f.chain l tg A0 = [dead (sub l 6) [.expr (sub l 8) (trE f.chain A0)]] := by simp [annS, hT]
      have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
      have st1 := done_seq (I := I) t f' fs' (annS f.chain l tg A0 ++ tail) (.tryE [] [] :: K0')
      rw [hS] at st1
      obtain ⟨ys2, p2, -, hf2⟩ := dead_path (I := I) t f' fs' (sub l 6) [.expr (sub l 8) (trE f.chain A0)] tail
        (.tryE [] [] :: K0')
      obtain ⟨ys3, p3, hf3⟩ : ∃ ys3, Path (PyCore.step I)
          { t with stack := { f' with ctrl := .exec tail, kont := .tryE [] [] :: K0' } :: fs' }
          { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } ys3 ∧
          ∀ y ∈ ys3, ∀ x, PyCore.focus y = some x → x / 64 = l := by
        rcases htl with rfl | rfl
        · exact ⟨_, .cons (done_try t f' fs' K0') (.nil _), by intro y hy x hx; simp at hy; subst hy; simp [PyCore.focus] at hx⟩
        · obtain ⟨ys4, p4, -, hf4⟩ := dead_path (I := I) t f' fs' (sub l 9) (annBind f.chain tg) [] (.tryE [] [] :: K0')
          refine ⟨_, p4.append (.cons (done_try t f' fs' K0') (.nil _)), ?_⟩
          intro y hy x hx
          rcases List.mem_append.1 hy with hy | hy
          · rw [hf4 y hy x hx]; exact sub_div _ _ (by omega)
          · simp at hy; subst hy; simp [PyCore.focus] at hx
      refine goal_b (.cons e1 (.nil _)) (by simp) (by rw [e, hS]; exact .cons st1 (p2.append p3)) (by simp)
        (crelI_seen (A.set (.exec (goodB_nil _ _) (by simp)) k (esub_cons hK))) (hcv _ ?_)
      intro y hy x hx
      simp only [List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | hy | hy
      · simp [PyCore.focus] at hx
      · rw [hf2 y hy x hx]; exact sub_div _ _ (by omega)
      · exact hf3 y hy x hx
    · -- module or class level: the annotation's value into `.n l`
      have ha' : a = some A0 := by rw [ha]; simp [hT]
      subst ha'
      have hS : annS f.chain l tg A0 = .assign (sub l 6) (fresh "n" l) (trE f.chain A0) :: annT f.chain l tg := by
        simp [annS, hT]
      let t1 : PyCore.Config σ := { t with stack := { f' with
        ctrl := .exec (.assign (sub l 6) (fresh "n" l) (trE f.chain A0) :: (annT f.chain l tg ++ tail)),
        kont := .tryE [] [] :: K0' } :: fs' }
      have st1 : PyCore.step I t = some t1 := by
        rw [e, hS, List.cons_append]; exact done_seq (I := I) t f' fs' _ _
      have st2 : PyCore.step I t1 = some { t with stack := { f' with
          ctrl := .ev (trE f.chain A0),
          kont := .assign (fresh "n" l) :: .seq (annT f.chain l tg ++ tail) :: .tryE [] [] :: K0' } :: fs' } := by
        simp [t1, PyCore.step, PyCore.execStep, PyCore.top]
      have cv : ∀ {zs : List (Sem.Config σ)}, Cover (Touch p) pfocus H zs [t, t1] := hcv _ (by
        intro y hy x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · simp [PyCore.focus, A.ht, hc'] at hx
        · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega))
      by_cases hn : ∃ lt y, tg = .name lt y
      · obtain ⟨lt, y, rfl⟩ := hn
        have e1 : Sem.step I s = some { s with stack := { f with
            ctrl := .ev A0, kont := .annV (mangle (priv f.chain) y) :: K0 } :: fs } := by
          simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC, Sem.mg]
        exact goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
          (crelI_seen (A.set (.ev ho.2.2.1) (.asg (.annV h1 h2 hT ho htl k)) (esub_top hK))) cv
      · have e1 : Sem.step I s = some { s with stack := { f with ctrl := .ev A0, kont := .exprS :: K0 } :: fs } := by
          cases tg with
          | name lt y => exact absurd ⟨lt, y, rfl⟩ hn
          | _ => simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
        exact goal_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
          (crelI_seen (A.set (.ev ho.2.2.1)
            (.asg (.annE h1 h2 hT (fun lt y e => hn ⟨lt, y, e⟩) ho htl k)) (esub_top hK))) cv
  | @delMany U0 K0 K0' ts Kp g hdo hd k =>
    have e := t_conf A.ht hc' hK'
    cases ts with
    | nil =>
      obtain ⟨ys, py, hys, hf⟩ := (del_strip (I := I) hd t f' fs').1 rfl
      have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
      refine goal_b (.cons e1 (.nil _)) (by simp) (by rw [e]; exact py.append (.cons (done_try t f' fs' K0') (.nil _)))
        (by simp) (crelI_seen (A.set (.exec (goodB_nil _ _) (by simp)) k (esub_cons hK))) (cover_none ?_)
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hf y hy
      · simp at hy; subst hy; simp [PyCore.focus]
    | cons tg ts' =>
      obtain ⟨ys, rest, Krest, py, hys, hf, hl, hd'⟩ := (del_strip (I := I) hd t f' fs').2 tg ts' rfl
      have A1 := A.zero.updT (.exec (trD f.chain tg (trT f.chain deadSrc tg (trE f.chain tg)) ++ rest)) Krest
      refine goal_ppre (by rw [e]; exact py) hys hf (by simp [μ, A.hs, A.ht, hK, hK'] at hl ⊢; omega)
        (del_head W _ tg (Nat.lt_succ_self _) A1 hc hK rfl rfl g hdo hd' k)


open Asg in
theorem exec_del (l ts) : ExecCase I p (.del l ts) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hkq := krel_seq (hnc (by simp)) hg.tail hk
  have hTl : Touch p s l := touch_exec A.hs hc
  let K' : List (PyCore.Kont σ) := .seq (trB f.chain ss) :: f'.kont
  let t1 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .exec (trDs f.chain ts), kont := .tryE [] [] :: K' } :: fs' }
  have st1 : PyCore.step I t = some t1 := by
    simp [PyCore.step, A.ht, hc', trB, trS, blk, PyCore.execStep, PyCore.top, t1, K']
  have e1 : Sem.step I s = some { s with stack := { f with
      ctrl := .exec [], kont := .delMany ts :: .seq ss :: f.kont } :: fs } := by estep
  have cv1 : ∀ {zs : List (Sem.Config σ)}, s ∈ zs → Cover (Touch p) pfocus H zs [t] := fun hz =>
    cover_of (l := l) hz hTl (by
      intro y hy x hx; simp at hy; subst hy
      simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega))
  cases ts with
  | nil =>
    have e2 : Sem.step I { s with stack := { f with ctrl := .exec [], kont := .delMany [] :: .seq ss :: f.kont } :: fs } =
        some { s with stack := { f with ctrl := .exec [], kont := .seq ss :: f.kont } :: fs } := by
      simp [Sem.step, Sem.doneStep, Sem.setC]
    exact goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 (.cons (done_try t f' fs' K') (.nil _))) (by simp)
      (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) hkq)) (by
        intro y hy x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact cv1 (by simp) _ (by simp) x hx
        · have := pfocus_le hx; simp [t1, PyCore.focus, trDs] at this)
  | cons tg ts' =>
    have hok : okAs (tg :: ts') = true := by
      have := hg.ok; simp only [okB, okS, Bool.and_eq_true] at this; exact this.1.1
    have hdo : delOks (tg :: ts') = true := by
      have := hg.ok; simp only [okB, okS, Bool.and_eq_true] at this; exact this.1.2
    have hnd : (labelsS (.del l (tg :: ts'))).Nodup := by
      have := hg.nd; simp only [labelsB, List.nodup_append] at this; exact this.1
    have hgs : GoodEs p f.chain U (tg :: ts') := by
      intro e he
      have hoe : okE e = true := by
        have := okAs_mem hok he; rwa [unstar_delOk (delOks_mem hdo he)] at this
      exact GoodB.e hg (fun x hx => by simp [itemsS, itemsEs_mem he hx])
        (fun x hx => by
          have := trDs_mem (C := f.chain) he (trD_items_all _ e (Nat.lt_succ_self _) x hx)
          simp [trS, blk, PyCore.itemsS, PyCore.itemsB, this])
        (fun _ => hoe) (fun l' hl' => by simp [labelsS, labelsEs_mem he hl'])
        (fun h => nodup_labelsEs he (List.nodup_cons.1 h).2) (fun x hx => by simp [touchS, touchEs_mem he hx])
    have A1 := (A.zero.upd (.exec []) (.delMany (tg :: ts') :: .seq ss :: f.kont) (.exec (trDs f.chain (tg :: ts')))
      (.tryE [] [] :: K')).mono_H (fun _ h => seen_of (zs := [s]) (p := p) h)
    exact SimStep.pre e1 (.cons st1 (.nil _)) (by simp) (cv1 (by simp))
      (del_head W _ tg (Nat.lt_succ_self _) A1 rfl rfl (by simp [trDs]) rfl hgs hdo .base (KRel.seen hkq))

end Surf.T2
