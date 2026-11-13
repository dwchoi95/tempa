/-
(T2), comprehensions and generator expressions.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Comp


/-! ## The comprehension's function object -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem cellOf_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.cellOf f' x = Sem.cellOf f x := by
  simp only [PyCore.cellOf, Sem.cellOf, hf.kind, cls_eq hf hx, hf.id, hf.κ x hx]
  cases f.kind <;> rfl

/-- A function object made for a comprehension, related to PyCore's closure of its translated scope. -/
theorem orel_new {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {gl cs} {S : Scope}
    (hS : S.isComp = true) (hH : H S.label) (hp : ∀ q ∈ S.params, H q.label) (hg : GoodSc p f.chain S)
    (hk : KOk (S :: f.chain)) :
    ORel p H gl cs (Sem.mkClo f S [])
      (.clo (trScope f.chain S) (trChain f.chain)
        (Py.memo (trScope f.chain S).names (PyCore.clsOf (trScope f.chain S :: trChain f.chain))).get
        (Py.memo (trScope f.chain S).names (PyCore.capture f' (trScope f.chain S))).get none) := by
  simp only [Sem.mkClo]
  refine ORel.clo (Py.memo_eq _ _) (Py.memo_eq _ _) rfl (fun x hx => ?_) (fun x a h => ?_) hS hH hp hg hk
  · simp only [Py.memo_eq, PyCore.capture, hf.chain]
    rw [show PyCore.clsOf (trScope f.chain S :: trChain f.chain) x = PyCore.clsOf (trChain (S :: f.chain)) x from rfl,
      cls_tr (not_fresh hx), cellOf_eq hf hx]
  · simp only [Py.memo_eq] at h
    split at h
    · simp only [Sem.cellOf] at h
      split at h <;> (try split at h) <;> first | (cases h; rfl) | exact hf.κa x a h
    · cases h

/-- PyCore's frame ids after a closure is allocated at `next`. -/
theorem ids_alloc {t1 : PyCore.Config σ} {g' : PyCore.Frame σ} {ob : PyCore.Obj σ} (h : Ids t)
    (ht : t.stack = f' :: fs') (ht1 : t1.stack = g' :: fs') (ho : t1.objs = t.objs.insert t.next ob)
    (hn : t1.next = t.next + 1) (hid : g'.id = f'.id) (hk : g'.kind = f'.kind) (hob : ∀ g, ob ≠ .gen (.susp g)) :
    Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have ho' : ∀ o, t1.objs[o]? = if t.next = o then some ob else t.objs[o]? := by
    intro o; rw [ho, Std.HashMap.getElem?_insert]; simp [beq_iff_eq]
  refine ⟨by rw [ht1]; simpa [hid] using h1, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_,
    fun g hg o hgo => ?_, fun g hg hm => ?_, fun o g ho1 => ?_⟩
  · rw [ht1, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | hg
    · rw [hid]; have := h2 f' (by simp); omega
    · have := h2 g (by simp [hg]); omega
  · rw [hn]; simp only [pObj, ho'] at hb; split at hb
    · omega
    · have := h3 o b hb; omega
  · simp only [pObj, ho'] at ho1; split at ho1
    · cases ho1; exact absurd rfl (hob g)
    · obtain ⟨e, hne⟩ := h4 o g ho1
      refine ⟨e, fun h hh => ?_⟩
      rw [ht1, List.mem_cons] at hh
      rcases hh with rfl | hh
      · rw [hid]; exact hne _ (by simp)
      · exact hne _ (by simp [hh])
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid]; exact h5 _ (by simp) o (by rw [← hk]; exact hgo)
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid]; exact h6 _ (by simp) (by rw [← hk]; exact hm)
    · exact h6 _ (by simp [hg]) hm
  · simp only [pObj, ho'] at ho1; split at ho1
    · cases ho1; exact absurd rfl (hob g)
    · exact h7 o g ho1

end

/-- Surf's next address is free. -/
theorem sobj_next {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} (A : At p H s t f fs f' fs') : s.objs[s.next]? = none := by
  have h := A.r.objs s.next
  rw [← A.r.next] at h ⊢
  cases ht : t.objs[t.next]? with
  | some b => exact absurd (A.r.ids.obj _ b ht) (Nat.lt_irrefl _)
  | none =>
    simp only [sObj, pObj, ht] at h
    cases hs : s.objs[t.next]? <;> simp_all [PyCore.OptRel]

/-! ## Static facts of a comprehension -/

/-- PyCore's kind of a comprehension's function. -/
theorem kok_comp {C : List Scope} {l k es gs} (hk : KOk C) (h : okE (.comp l k es gs) = true) :
    KOk (.comp l k es gs :: C) :=
  ⟨by
    simp only
    rw [kind_tr _ _ (by
      simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at h
      have hl := h.1.2
      cases k <;> simp_all [Scope.genOk]), comp_kind h], hk⟩

/-! ### Items of a comprehension's parts -/

theorem cpitemsB_app (C : List PyCore.Scope) :
    ∀ a b : PS, PyCore.itemsB R0 C (a ++ b) = PyCore.itemsB R0 C a ++ PyCore.itemsB R0 C b
  | [], _ => rfl
  | _ :: a, b => by simp [PyCore.itemsB, cpitemsB_app C a b]

theorem cfold_items {C : List PyCore.Scope} {r : Label} : ∀ (es : List PE) (init : PE) (x : PyCore.Item),
    x ∈ PyCore.itemsE R0 C (es.foldl (fun acc e => .bin r "," acc e) init) →
    x ∈ PyCore.itemsE R0 C init ∨ ∃ e ∈ es, x ∈ PyCore.itemsE R0 C e
  | [], init, x, h => .inl h
  | e :: es, init, x, h => by
    rcases cfold_items es _ x h with h | ⟨e', he', hx⟩
    · simp [PyCore.itemsE] at h
      rcases h with h | h
      · exact .inl h
      · exact .inr ⟨e, by simp, h⟩
    · exact .inr ⟨e', by simp [he'], hx⟩

theorem ctrA_mem {C : List Scope} {e : PE} : ∀ {es : List Expr}, e ∈ trA C es → ∃ u ∈ es, e = trE C (unstar u)
  | [], h => by simp [trA] at h
  | a :: es, h => by
    have key : e = trE C (unstar a) ∨ e ∈ trA C es := by
      cases a <;> simpa [trA, unstar] using h
    rcases key with rfl | h'
    · exact ⟨a, by simp, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := ctrA_mem h'; exact ⟨u, by simp [hu], rfl⟩

theorem ctgtsOk_mem : ∀ {ts : List Expr} {u : Expr}, tgtsOk ts = true → u ∈ ts → tgtOk (unstar u) = true
  | [], _, _, h => by simp at h
  | a :: ts, u, ho, h => by
    have ho' : tgtOk (unstar a) = true ∧ tgtsOk ts = true := by
      cases a <;> simp_all [tgtsOk, unstar]
    rcases List.mem_cons.1 h with rfl | h
    · exact ho'.1
    · exact ctgtsOk_mem ho'.2 h

theorem csizeOf_unstar (u : Expr) : sizeOf (unstar u) ≤ sizeOf u := by
  cases u <;> simp [unstar] <;> omega

/-- A target's items as an expression are items of its store. -/
theorem ctgt_items {C : List Scope} (tg : Expr) (src : Label → PE) (htg : tgtOk tg = true) (x : PyCore.Item)
    (hx : x ∈ PyCore.itemsE R0 (trChain C) (trE C tg)) :
    x ∈ PyCore.itemsB R0 (trChain C) (trT C src tg (trE C tg)) := by
  have hL : ∀ (lt : Label) (ts : List Expr), sizeOf ts < sizeOf tg → tgtsOk ts = true →
      x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "tuple") (trA C ts ++ ts.map starMark)) ∨
      x ∈ PyCore.itemsE R0 (trChain C) (gad lt 0 (.display "list") (trA C ts ++ ts.map starMark)) →
      ∀ i, x ∈ PyCore.itemsB R0 (trChain C) (trItems C lt i ts) := by
    intro lt ts hs hok hx' i
    have hex : ∃ u ∈ ts, x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar u)) := by
      rcases hx' with hx' | hx' <;>
      · simp only [gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
          List.nil_append] at hx'
        rcases cfold_items _ _ x hx' with h | ⟨e, he, h⟩
        · simp [PyCore.itemsE] at h
        rcases List.mem_append.1 he with he | he
        · obtain ⟨u, hu, rfl⟩ := ctrA_mem he; exact ⟨u, hu, h⟩
        · obtain ⟨u, -, rfl⟩ := List.mem_map.1 he
          cases u <;> simp [starMark, PyCore.itemsE] at h
    have IH : ∀ u ∈ ts, ∀ (src' : Label → PE), x ∈ PyCore.itemsE R0 (trChain C) (trE C (unstar u)) →
        x ∈ PyCore.itemsB R0 (trChain C) (trT C src' (unstar u) (trE C (unstar u))) := fun u hu src' hxu =>
      have hlt : sizeOf (unstar u) < sizeOf tg :=
        Nat.lt_of_le_of_lt (csizeOf_unstar u) (Nat.lt_trans (List.sizeOf_lt_of_mem hu) hs)
      ctgt_items (C := C) (unstar u) src' (ctgtsOk_mem hok hu) x hxu
    clear hx' hs hok
    induction ts generalizing i with
    | nil => simp at hex
    | cons a ts ihl =>
      obtain ⟨u, hu, hxu⟩ := hex
      have e : trItems C lt i (a :: ts) = trT C (itemSrc lt i) (unstar a) (trE C (unstar a)) ++ trItems C lt (i + 1) ts := by
        cases a <;> rfl
      rw [e, cpitemsB_app]
      rcases List.mem_cons.1 hu with rfl | hu
      · exact List.mem_append_left _ (IH u (by simp) _ hxu)
      · exact List.mem_append_right _ (ihl (i + 1) ⟨u, hu, hxu⟩ (fun u' h => IH u' (by simp [h])))
  cases tg with
  | name lt y => simp [trE, trT, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS] at hx ⊢; exact .inl hx
  | attr lt o a =>
    simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢; exact .inl hx
  | sub lt o i =>
    simp [trE, trT, cc, ccR, recR, PyCore.itemsE, PyCore.itemsB, PyCore.itemsS, List.foldl] at hx ⊢
    rcases hx with h | h <;> simp [h]
  | tuple lt ts =>
    have := hL lt ts (by simp; omega) (by simpa [tgtOk] using htg) (.inl hx) 0
    simp [trT, blk, PyCore.itemsB, PyCore.itemsS, this]
  | list lt ts =>
    have := hL lt ts (by simp; omega) (by simpa [tgtOk] using htg) (.inr hx) 0
    simp [trT, blk, PyCore.itemsB, PyCore.itemsS, this]
  | _ => simp [tgtOk] at htg
termination_by sizeOf tg

theorem ifsNest_items {C' : List PyCore.Scope} {x : PyCore.Item} (lg : Label) :
    ∀ (cs : List PE) (body : PS),
      (x ∈ PyCore.itemsB R0 C' body → x ∈ PyCore.itemsB R0 C' (ifsNest lg cs body)) ∧
      (∀ c ∈ cs, x ∈ PyCore.itemsE R0 C' c → x ∈ PyCore.itemsB R0 C' (ifsNest lg cs body))
  | [], body => ⟨id, by simp⟩
  | c :: cs, body => by
    obtain ⟨h1, h2⟩ := ifsNest_items (C' := C') (x := x) lg cs body
    simp only [ifsNest, PyCore.itemsB, PyCore.itemsS, r0_s, Option.isSome_none, Bool.false_eq_true, ite_false,
      List.append_nil, List.mem_append, List.mem_cons]
    refine ⟨fun h => ?_, fun c' hc hx => ?_⟩
    · exact .inr (h1 h)
    · rcases hc with rfl | hc
      · exact .inl hx
      · exact .inr (h2 c' hc hx)

theorem forLoop_items {C' : List PyCore.Scope} {x : PyCore.Item} {l : Label} {iv : Name} {store body u : PS}
    (h : x ∈ PyCore.itemsB R0 C' (store ++ body)) : x ∈ PyCore.itemsB R0 C' (forLoop l iv store body u) := by
  simp only [forLoop, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs, r0_s, Option.isSome_none, Bool.false_eq_true,
    ite_false, List.mem_append, List.mem_cons]
  simp [h]


/-- PyCore's items of a comprehension's clauses: the inner code's, each clause's target's and conditions',
and the iterables' but the first one's when `first`. -/
theorem trGs_items {C : List Scope} {C' : List PyCore.Scope} {it : Name} {x : PyCore.Item} :
    ∀ (first : Bool) (gs : List Gen) (inner : PS),
      (x ∈ PyCore.itemsB R0 C' inner → x ∈ PyCore.itemsB R0 C' (trGs C it first gs inner)) ∧
      ∀ lg t i ifs, Gen.mk lg t i ifs ∈ gs →
        (x ∈ PyCore.itemsB R0 C' (trT C (forSrc lg) t (trE C t)) → x ∈ PyCore.itemsB R0 C' (trGs C it first gs inner)) ∧
        (∀ e ∈ ifs, x ∈ PyCore.itemsE R0 C' (trE C e) → x ∈ PyCore.itemsB R0 C' (trGs C it first gs inner)) ∧
        ((first = false ∨ Gen.mk lg t i ifs ∈ gs.tail) → x ∈ PyCore.itemsE R0 C' (trE C i) →
          x ∈ PyCore.itemsB R0 C' (trGs C it first gs inner))
  | _, [], _ => ⟨id, by simp⟩
  | first, .mk lg0 t0 i0 ifs0 :: gs, inner => by
    obtain ⟨h1, h2⟩ := trGs_items (C := C) (C' := C') (it := it) (x := x) false gs inner
    obtain ⟨n1, n2⟩ := ifsNest_items (C' := C') (x := x) lg0 (trEs C ifs0) (trGs C it false gs inner)
    have hb : x ∈ PyCore.itemsB R0 C' (trT C (forSrc lg0) t0 (trE C t0) ++ ifsNest lg0 (trEs C ifs0) (trGs C it false gs inner)) →
        x ∈ PyCore.itemsB R0 C' (trGs C it first (.mk lg0 t0 i0 ifs0 :: gs) inner) := fun h => by
      simp only [trGs, cpitemsB_app, List.mem_append]; exact .inr (forLoop_items h)
    have hi : first = false → x ∈ PyCore.itemsE R0 C' (trE C i0) →
        x ∈ PyCore.itemsB R0 C' (trGs C it first (.mk lg0 t0 i0 ifs0 :: gs) inner) := fun hf h => by
      subst hf
      simp [trGs, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, cc, ccR, recR, List.foldl, h]
    have hn : x ∈ PyCore.itemsB R0 C' (trGs C it false gs inner) →
        x ∈ PyCore.itemsB R0 C' (trGs C it first (.mk lg0 t0 i0 ifs0 :: gs) inner) := fun h => by
      apply hb; rw [cpitemsB_app]; exact List.mem_append_right _ (n1 h)
    refine ⟨fun h => hn (h1 h), fun lg t i ifs hm => ?_⟩
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      refine ⟨fun h => hb (by rw [cpitemsB_app]; exact List.mem_append_left _ h),
        fun e he h => hb (by rw [cpitemsB_app]; exact List.mem_append_right _ (n2 _ (mem_trEs he) h)), ?_⟩
      rintro (hf | ht) h
      · exact hi hf h
      · exact hn ((h2 _ _ _ _ ht).2.2 (.inl rfl) h)
    · obtain ⟨a, b, c⟩ := h2 _ _ _ _ hm
      exact ⟨fun h => hn (a h), fun e he h => hn (b e he h), fun _ h => hn (c (.inl rfl) h)⟩

theorem itemsGs_sub {C : List Scope} {x : Item} :
    ∀ (first : Bool) (gs : List Gen) lg t i ifs, Gen.mk lg t i ifs ∈ gs →
      (x ∈ itemsE C t → x ∈ itemsGs C first gs) ∧ (∀ e ∈ ifs, x ∈ itemsE C e → x ∈ itemsGs C first gs) ∧
      ((first = false ∨ Gen.mk lg t i ifs ∈ gs.tail) → x ∈ itemsE C i → x ∈ itemsGs C first gs)
  | _, [], _, _, _, _, h => by simp at h
  | first, .mk lg0 t0 i0 ifs0 :: gs, lg, t, i, ifs, hm => by
    have hn : x ∈ itemsGs C false gs → x ∈ itemsGs C first (.mk lg0 t0 i0 ifs0 :: gs) := fun h => by
      simp [itemsGs, h]
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      refine ⟨fun h => by simp [itemsGs, h], fun e he h => by simp [itemsGs, itemsEs_mem he h], ?_⟩
      rintro (hf | ht) h
      · subst hf; simp [itemsGs, h]
      · exact hn ((itemsGs_sub false gs _ _ _ _ ht).2.2 (.inl rfl) h)
    · obtain ⟨a, b, c⟩ := itemsGs_sub (C := C) (x := x) false gs _ _ _ _ hm
      exact ⟨fun h => hn (a h), fun e he h => hn (b e he h), fun _ h => hn (c (.inl rfl) h)⟩

theorem nd_Es {e : Expr} : ∀ {es : List Expr}, e ∈ es → (labelsEs es).Nodup → (labelsE e).Nodup
  | [], h, _ => by simp at h
  | a :: es, h, hn => by
    simp only [labelsEs, List.nodup_append] at hn
    rcases List.mem_cons.1 h with rfl | h
    · exact hn.1
    · exact nd_Es h hn.2.1

theorem nd_Gs {lg t i ifs} : ∀ {gs : List Gen}, Gen.mk lg t i ifs ∈ gs → (labelsGs gs).Nodup →
    (labelsE t).Nodup ∧ (labelsE i).Nodup ∧ (labelsEs ifs).Nodup
  | [], h, _ => by simp at h
  | .mk lg' t' i' ifs' :: gs, h, hn => by
    simp only [labelsGs, List.nodup_cons, List.nodup_append] at hn
    rcases List.mem_cons.1 h with h | h
    · cases h; exact ⟨hn.1.1.1.2, hn.1.1.2.1, hn.1.2.1⟩
    · exact nd_Gs h hn.2.1

theorem okGs_mem {lg t i ifs} : ∀ {gs : List Gen}, Gen.mk lg t i ifs ∈ gs → okGs gs = true →
    okE t = true ∧ tgtOk t = true ∧ okE i = true ∧ okEs ifs = true
  | [], h, _ => by simp at h
  | .mk lg' t' i' ifs' :: gs, h, ho => by
    simp only [okGs, Bool.and_eq_true] at ho
    rcases List.mem_cons.1 h with h | h
    · cases h; exact ⟨ho.1.1.1.1, ho.1.1.1.2, ho.1.1.2, ho.1.2⟩
    · exact okGs_mem h ho.2

theorem compElt_items {C' : List PyCore.Scope} {C : List Scope} {l : Label} {k : CompKind} {es : List Expr}
    (hn : es.length = if k = .dict then 2 else 1) {e : Expr} (he : e ∈ es) {x : PyCore.Item}
    (hx : x ∈ PyCore.itemsE R0 C' (trE C e)) : x ∈ PyCore.itemsB R0 C' (compElt l k (trEs C es)) := by
  rcases k with _ | _ | _ | _ <;> rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, es⟩⟩⟩ <;> simp at hn <;>
    simp at he <;> (try rcases he with rfl | rfl) <;> (try subst he) <;>
    simp [compElt, trEs, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, cc, ccR, recR, nm, List.foldl, hx]

theorem comp_pitems {C : List Scope} {l k es} {gs : List Gen} (hne : gs ≠ []) {x : PyCore.Item}
    (hx : x ∈ PyCore.itemsB R0 (trChain (.comp l k es gs :: C))
      (trGs (.comp l k es gs :: C) (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es)))) :
    x ∈ PyCore.itemsE R0 (trChain C) (trE C (.comp l k es gs)) := by
  cases gs with
  | nil => exact absurd rfl hne
  | cons g rest =>
    simp only [trChain, trScope] at hx
    by_cases hk : k = .gen
    · simp [trE, PyCore.itemsE, compWrap, hk] at hx ⊢; simp [hx]
    · simp [trE, PyCore.itemsE, compWrap, hk, cpitemsB_app, PyCore.itemsB] at hx ⊢; simp [hx]

theorem touchGs_sub {x : Label × Expr} : ∀ {gs : List Gen} {lg t i ifs}, Gen.mk lg t i ifs ∈ gs →
    (x ∈ touchE t → x ∈ touchGs gs) ∧ (∀ e ∈ ifs, x ∈ touchE e → x ∈ touchGs gs) ∧ (x ∈ touchE i → x ∈ touchGs gs)
  | [], _, _, _, _, h => by simp at h
  | .mk lg0 t0 i0 ifs0 :: gs, lg, t, i, ifs, hm => by
    rcases List.mem_cons.1 hm with h | h
    · cases h
      exact ⟨fun hx => by simp [touchGs, hx], fun e he hx => by simp [touchGs, touchEs_mem he hx],
        fun hx => by simp [touchGs, hx]⟩
    · have ih := touchGs_sub (x := x) h
      exact ⟨fun hx => by simp [touchGs, ih.1 hx], fun e he hx => by simp [touchGs, ih.2.1 e he hx],
        fun hx => by simp [touchGs, ih.2.2 hx]⟩

/-- The parts of a comprehension are code of `p` in the comprehension's own scope. -/
theorem goodSc_comp {C : List Scope} {U : Label → Prop} {l k es gs} (W : WF p)
    (hg : GoodE p C U (.comp l k es gs)) : GoodSc p C (.comp l k es gs) := by
  have hok := hg.ok
  simp only [okE, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hes, hgs⟩, hne⟩, hn⟩, -⟩ := hok
  have hnd := hg.nd
  simp only [labelsE, List.nodup_cons, List.nodup_append] at hnd
  obtain ⟨g, rest, rfl⟩ : ∃ g rest, gs = g :: rest := by
    cases gs with
    | nil => simp at hne
    | cons g rest => exact ⟨g, rest, rfl⟩
  have hne' : g :: rest ≠ [] := by simp
  let S := Scope.comp l k es (g :: rest)
  have mk : ∀ e : Expr, (∀ x, x ∈ itemsE (S :: C) e → x ∈ itemsE C (.comp l k es (g :: rest))) →
      (∀ x, x ∈ PyCore.itemsE R0 (trChain (S :: C)) (trE (S :: C) e) →
        x ∈ PyCore.itemsB R0 (trChain (S :: C)) (trGs (S :: C) (fresh "i" l) true (g :: rest)
          (compElt l k (trEs (S :: C) es)))) →
      okE e = true → (labelsE e).Nodup → SubL (touchE e) (touchE (.comp l k es (g :: rest))) →
      GoodE p (S :: C) UAll e :=
    fun e hs ht ho hd hc => ⟨fun x hx => hg.s x (hs x hx), fun x hx => hg.t x (comp_pitems hne' (ht x hx)), ho,
      fun _ _ => trivial, fun c hc => hg.pv c (by simpa [S, priv] using hc), hd, fun x hx => hg.tch x (hc x hx)⟩
  have hcG : ∀ {x}, x ∈ touchGs (g :: rest) → x ∈ touchE (.comp l k es (g :: rest)) := fun hx => by
    simp [touchE, hx]
  have hsI : ∀ x, x ∈ itemsGs (S :: C) true (g :: rest) → x ∈ itemsE C (.comp l k es (g :: rest)) :=
    fun x hx => by simp [itemsE, S] at hx ⊢; simp [hx]
  have clause : ∀ lg t i ifs, Gen.mk lg t i ifs ∈ g :: rest →
      GoodGT p (S :: C) UAll (.mk lg t i ifs) ∧ (Gen.mk lg t i ifs ∈ rest → GoodE p (S :: C) UAll i) := by
    intro lg t i ifs hm
    obtain ⟨o1, o2, o3, o4⟩ := okGs_mem hm hgs
    obtain ⟨d1, d2, d3⟩ := nd_Gs hm hnd.2.1
    have tc : ∀ x, _ := fun x => touchGs_sub (x := x) hm
    refine ⟨⟨trivial, mk t (fun x hx => hsI x ((itemsGs_sub true _ _ _ _ _ hm).1 hx))
      (fun x hx => ((trGs_items true _ _).2 _ _ _ _ hm).1 (ctgt_items t _ o2 x hx)) o1 d1 (fun x hx => hcG ((tc x).1 hx)),
      fun e he => mk e (fun x hx => hsI x ((itemsGs_sub true _ _ _ _ _ hm).2.1 e he hx))
        (fun x hx => ((trGs_items true _ _).2 _ _ _ _ hm).2.1 e he hx) (okEs_mem o4 he) (nd_Es he d3)
        (fun x hx => hcG ((tc x).2.1 e he hx)),
      fun x hx => hg.t x (comp_pitems hne' (((trGs_items true _ _).2 _ _ _ _ hm).1 hx))⟩,
      fun hr => mk i (fun x hx => hsI x ((itemsGs_sub true _ _ _ _ _ hm).2.2 (.inr hr) hx))
        (fun x hx => ((trGs_items true _ _).2 _ _ _ _ hm).2.2 (.inr hr) hx) o3 d2 (fun x hx => hcG ((tc x).2.2 hx))⟩
  refine ⟨⟨hg.s, hg.t, hg.ok, fun _ _ => trivial, hg.pv, hg.nd, hg.tch⟩, fun e he => mk e (fun x hx => by simp [itemsE, S, itemsEs_mem he hx])
    (fun x hx => (trGs_items true _ _).1 (compElt_items hn he hx)) (okEs_mem hes he) (nd_Es he hnd.1.2)
    (fun x hx => by simp [touchE, touchEs_mem he hx]), ?_⟩
  obtain ⟨lg, t, i, ifs⟩ := g
  refine ⟨(clause lg t i ifs (by simp)).1, fun g' hg' => ?_⟩
  obtain ⟨lg', t', i', ifs'⟩ := g'
  have := clause lg' t' i' ifs' (by simp [hg'])
  exact ⟨this.1, this.2 hg'⟩

/-- The fresh names a clause's loop binds (`.g`, `.v`, `.s`), at nodes made for the clause. -/
theorem forLoop_occ {C' : List PyCore.Scope} {lg : Label} {iv : Name} {store body u : PS} :
    ∀ tag ∈ ["g", "v", "s"], ∃ k, k < 64 ∧ k ≠ 49 ∧ k ≠ 52 ∧
      PyCore.Item.occ (sub lg k) (fresh tag lg) C' ∈ PyCore.itemsB R0 C' (forLoop lg iv store body u) := by
  intro tag ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨10, by omega, by omega, by omega, by simp [forLoop, PyCore.itemsB, PyCore.itemsS]⟩
  · exact ⟨15, by omega, by omega, by omega, by simp [forLoop, PyCore.itemsB, PyCore.itemsS]⟩
  · exact ⟨19, by omega, by omega, by omega, by simp [forLoop, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs]⟩

theorem trGs_occ {C : List Scope} {C' : List PyCore.Scope} {it : Name} :
    ∀ (first : Bool) (gs : List Gen) (inner : PS) (g : Gen), g ∈ gs →
      (∀ tag ∈ ["g", "v", "s"], ∃ k, k < 64 ∧ k ≠ 49 ∧ k ≠ 52 ∧
        PyCore.Item.occ (sub g.label k) (fresh tag g.label) C' ∈ PyCore.itemsB R0 C' (trGs C it first gs inner)) ∧
      ((first = false ∨ g ∈ gs.tail) →
        PyCore.Item.occ (sub g.label 0) (fresh "j" g.label) C' ∈ PyCore.itemsB R0 C' (trGs C it first gs inner))
  | _, [], _, _, h => by simp at h
  | first, .mk lg0 t0 i0 ifs0 :: gs, inner, g, hm => by
    have hb : ∀ x, x ∈ PyCore.itemsB R0 C' (forLoop lg0 (if first then it else fresh "j" lg0)
        (trT C (forSrc lg0) t0 (trE C t0)) (ifsNest lg0 (trEs C ifs0) (trGs C it false gs inner)) []) →
        x ∈ PyCore.itemsB R0 C' (trGs C it first (.mk lg0 t0 i0 ifs0 :: gs) inner) := fun x h => by
      simp only [trGs, cpitemsB_app, List.mem_append]; exact .inr h
    have hn : ∀ x, x ∈ PyCore.itemsB R0 C' (trGs C it false gs inner) →
        x ∈ PyCore.itemsB R0 C' (trGs C it first (.mk lg0 t0 i0 ifs0 :: gs) inner) := fun x h =>
      hb x (forLoop_items (by rw [cpitemsB_app]; exact List.mem_append_right _ ((ifsNest_items lg0 _ _).1 h)))
    rcases List.mem_cons.1 hm with rfl | hm
    · refine ⟨fun tag ht => ?_, ?_⟩
      · obtain ⟨k, h1, h2, h3, h4⟩ := forLoop_occ (C' := C') (lg := lg0)
          (iv := if first then it else fresh "j" lg0) (store := trT C (forSrc lg0) t0 (trE C t0))
          (body := ifsNest lg0 (trEs C ifs0) (trGs C it false gs inner)) (u := []) tag ht
        exact ⟨k, h1, h2, h3, hb _ h4⟩
      · rintro (rfl | h)
        · simp [trGs, PyCore.itemsB, PyCore.itemsS, Gen.label]
        · exact hn _ ((trGs_occ (C := C) (C' := C') (it := it) false gs inner _ h).2 (.inl rfl))
    · obtain ⟨a, b⟩ := trGs_occ (C := C) (C' := C') (it := it) false gs inner g hm
      exact ⟨fun tag ht => by obtain ⟨k, h1, h2, h3, h4⟩ := a tag ht; exact ⟨k, h1, h2, h3, hn _ h4⟩,
        fun _ => hn _ (b (.inl rfl))⟩

theorem labelsGs_sub {lg : Label} {t i : Expr} {ifs : List Expr} : ∀ {gs : List Gen}, Gen.mk lg t i ifs ∈ gs → ∀ x,
    (x = lg ∨ x ∈ labelsE t ∨ x ∈ labelsE i ∨ x ∈ labelsEs ifs) → x ∈ labelsGs gs
  | [], h, _, _ => by simp at h
  | .mk lg' t' i' ifs' :: gs, h, x, hx => by
    rcases List.mem_cons.1 h with h | h
    · cases h; simp only [labelsGs, List.mem_cons, List.mem_append]; rcases hx with hx | hx | hx | hx <;> simp [hx]
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (labelsGs_sub h x hx))

theorem goodEs_rm {C : List Scope} {U : Label → Prop} {l : Label} {es : List Expr} (h : GoodEs p C U es)
    (hl : l ∉ labelsEs es) : GoodEs p C (Rm U l) es :=
  fun e he => (h e he).rm (fun hm => hl (labelsEs_mem he hm))

theorem goodGs_rm {C : List Scope} {U : Label → Prop} {l : Label} {gs : List Gen} (h : GoodGs p C U gs)
    (hl : l ∉ labelsGs gs) : GoodGs p C (Rm U l) gs := by
  intro g hg
  obtain ⟨lg, t, i, ifs⟩ := g
  obtain ⟨⟨h1, h2, h3, h5⟩, h4⟩ := h _ hg
  have hs := labelsGs_sub hg
  exact ⟨⟨⟨h1, fun e => hl (hs _ (.inl e.symm))⟩, h2.rm fun hm => hl (hs _ (.inr (.inl hm))),
    goodEs_rm h3 fun hm => hl (hs _ (.inr (.inr (.inr hm)))), h5⟩, h4.rm fun hm => hl (hs _ (.inr (.inr (.inl hm))))⟩

/-- A part's facts at a budget with all its nodes. -/
theorem goodE_bud {C : List Scope} {U V : Label → Prop} {e : Expr} (h : GoodE p C V e) (hU : ∀ y ∈ labelsE e, U y) :
    GoodE p C U e := { h with u := hU }

theorem goodEs_bud {C : List Scope} {U V : Label → Prop} {es : List Expr} (h : GoodEs p C V es)
    (hU : ∀ y ∈ labelsEs es, U y) : GoodEs p C U es :=
  fun e he => goodE_bud (h e he) fun y hy => hU y (labelsEs_mem he hy)

theorem goodGs_bud {C : List Scope} {U V : Label → Prop} {gs : List Gen} (h : GoodGs p C V gs)
    (hU : ∀ y ∈ labelsGs gs, U y) : GoodGs p C U gs := by
  intro g hg
  obtain ⟨lg, t, i, ifs⟩ := g
  obtain ⟨⟨-, h2, h3, h5⟩, h4⟩ := h _ hg
  have hs := labelsGs_sub hg
  exact ⟨⟨hU _ (hs _ (.inl rfl)), goodE_bud h2 fun y hy => hU y (hs _ (.inr (.inl hy))),
    goodEs_bud h3 fun y hy => hU y (hs _ (.inr (.inr (.inr hy)))), h5⟩, goodE_bud h4 fun y hy => hU y (hs _ (.inr (.inr (.inl hy))))⟩

/-- The facts of the clauses after one, each at the budget without the nodes of the clauses before it,
from the comprehension's distinct labels. -/
theorem nextOk_of {C : List Scope} {es : List Expr} (hE : GoodEs p C UAll es) :
    ∀ (rest : List Gen) (U : Label → Prop), GoodGs p C UAll rest → (labelsGs rest ++ labelsEs es).Nodup →
      (∀ y ∈ labelsGs rest ++ labelsEs es, U y) → NextOk p C U es rest
  | [], _, _, _, _ => trivial
  | .mk lg t i ifs :: rest, U, hG, hn, hU => by
    simp only [labelsGs, List.cons_append, List.nodup_cons, List.mem_append, List.append_assoc] at hn
    obtain ⟨hlg, hn⟩ := hn
    obtain ⟨⟨-, ht, hifs, hst⟩, -⟩ := hG (.mk lg t i ifs) (by simp)
    have hrest : GoodGs p C UAll rest := fun g hg => hG g (by simp [hg])
    have hU' : ∀ y, (y ∈ labelsE t ∨ y ∈ labelsE i ∨ y ∈ labelsEs ifs ∨ y ∈ labelsGs rest ∨ y ∈ labelsEs es) →
        Rm U lg y := by
      intro y hy
      refine ⟨hU y (by simp only [labelsGs, List.cons_append, List.mem_cons, List.mem_append]; rcases hy with h | h | h | h | h <;> simp [h]), ?_⟩
      rintro rfl; apply hlg; rcases hy with h | h | h | h | h <;> simp [h]
    have hn' : (labelsGs rest ++ labelsEs es).Nodup :=
      (List.nodup_append.1 (List.nodup_append.1 (List.nodup_append.1 hn).2.1).2.1).2.1
    have hGr : ∀ y ∈ labelsGs rest, Rm U lg y := fun y hy => hU' y (.inr (.inr (.inr (.inl hy))))
    have hEr : ∀ y ∈ labelsEs es, Rm U lg y := fun y hy => hU' y (.inr (.inr (.inr (.inr hy))))
    exact ⟨hU lg (by simp [labelsGs]), ⟨goodE_bud ht fun y hy => hU' y (.inl hy),
      goodEs_bud hifs fun y hy => hU' y (.inr (.inr (.inl hy))), hst⟩, goodGs_bud hrest hGr, goodEs_bud hE hEr,
      nextOk_of hE rest (Rm U lg) hrest hn' fun y hy => (List.mem_append.1 hy).elim (hGr y) (hEr y)⟩

/-- What a comprehension's frame needs of its scope (`compStart`, `genComp`): the fresh names bound there, the
first clause's parts and the other clauses and the elements at the budgets without the comprehension's node and
the first clause's. -/
theorem comp_static (W : WF p) {C : List Scope} {l : Label} {k : CompKind} {es : List Expr} {lg : Label}
    {t i : Expr} {ifs : List Expr} {rest : List Gen} (hg : GoodSc p C (.comp l k es (.mk lg t i ifs :: rest))) :
    FOk (.comp l k es (.mk lg t i ifs :: rest) :: C) (fresh "i" l) ∧
    (k ≠ .gen → FOk (.comp l k es (.mk lg t i ifs :: rest) :: C) (fresh "acc" l)) ∧
    FOks (.comp l k es (.mk lg t i ifs :: rest) :: C) lg ["g", "v", "s"] ∧
    GsFOk (.comp l k es (.mk lg t i ifs :: rest) :: C) rest ∧ lg ≠ l ∧
    GoodGT p (.comp l k es (.mk lg t i ifs :: rest) :: C) UAll (.mk lg t i ifs) ∧
    GoodGs p (.comp l k es (.mk lg t i ifs :: rest) :: C) UAll rest ∧
    GoodEs p (.comp l k es (.mk lg t i ifs :: rest) :: C) UAll es ∧
    GoodGT p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm UAll l) (.mk lg t i ifs) ∧
    GoodGs p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm UAll l) rest ∧
    GoodEs p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm UAll l) es ∧
    GoodGP p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm (Rm UAll l) lg) (.mk lg t i ifs) ∧
    GoodGs p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm (Rm UAll l) lg) rest ∧
    GoodEs p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm (Rm UAll l) lg) es ∧
    NextOk p (.comp l k es (.mk lg t i ifs :: rest) :: C) (Rm (Rm UAll l) lg) es rest := by
  obtain ⟨hE, hEs, hGT, hGs⟩ := hg
  let S := Scope.comp l k es (.mk lg t i ifs :: rest)
  have hT := hE.t
  have hnd := hE.nd
  simp only [labelsE] at hnd
  obtain ⟨hl0, -⟩ := List.nodup_cons.1 hnd
  have hles : l ∉ labelsEs es := fun h => hl0 (List.mem_append_left _ h)
  have hlgs : l ∉ labelsGs (.mk lg t i ifs :: rest) := fun h => hl0 (List.mem_append_right _ h)
  obtain ⟨hl1, hlt, -, hlifs, hlrest, -, hles2⟩ := comp_lbl (pre := []) hE
  have hlgs' : ∀ x, (x = lg ∨ x ∈ labelsE t ∨ x ∈ labelsE i ∨ x ∈ labelsEs ifs) → x ∈ labelsGs (.mk lg t i ifs :: rest) :=
    labelsGs_sub (by simp)
  have hlrest' : l ∉ labelsGs rest := fun hm => hlgs (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
  have fok : ∀ {L : Label} {x : Name}, PyCore.Item.occ L x (trChain (S :: C)) ∈
      PyCore.itemsE R0 (trChain C) (trE C (.comp l k es (.mk lg t i ifs :: rest))) → IsFresh x → ¬ IsCmp L →
      FOk (S :: C) x := fun h hx hL => fok_of W (hT _ h) hx hL
  have hne : (Gen.mk lg t i ifs :: rest) ≠ [] := by simp
  have occ : ∀ (g : Gen), g ∈ (Gen.mk lg t i ifs :: rest) →
      (∀ tag ∈ ["g", "v", "s"], FOk (S :: C) (fresh tag g.label)) ∧
      (g ∈ rest → FOk (S :: C) (fresh "j" g.label)) := by
    intro g hg
    obtain ⟨a, b⟩ := trGs_occ (C := S :: C) (C' := trChain (S :: C)) (it := fresh "i" l) true _
      (compElt l k (trEs (S :: C) es)) g hg
    refine ⟨fun tag ht => ?_, fun hr => ?_⟩
    · obtain ⟨k, h1, h2, h3, h4⟩ := a tag ht
      exact fok (comp_pitems hne h4) ⟨_, _, rfl⟩ (not_cmp _ k h1 h2 h3)
    · exact fok (comp_pitems hne (b (.inr hr))) ⟨_, _, rfl⟩ (not_cmp _ 0 (by omega) (by omega) (by omega))
  obtain ⟨-, hGt, hGifs, hGst⟩ := hGT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fok (L := sub l 1) (by simp [trE, PyCore.itemsE, S, trChain, trScope]) ⟨_, _, rfl⟩ (not_cmp _ 1 (by omega) (by omega) (by omega))
  · intro hk
    exact fok (L := sub l 4) (by simp [trE, PyCore.itemsE, compWrap, hk, PyCore.itemsB, PyCore.itemsS, S, trChain, trScope])
      ⟨_, _, rfl⟩ (not_cmp _ 4 (by omega) (by omega) (by omega))
  · exact fun tag ht => (occ (.mk lg t i ifs) (by simp)).1 tag ht
  · intro g hg tag ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht
    · exact (occ g (by simp [hg])).2 hg
    · exact (occ g (by simp [hg])).1 tag (by simpa using ht)
  · exact fun e => hl1 e.symm
  · exact ⟨trivial, hGt, hGifs, hGst⟩
  · exact hGs
  · exact hEs
  · exact ⟨⟨trivial, hl1.symm⟩, hGt.rm fun hm => hlgs (hlgs' _ (.inr (.inl hm))),
      goodEs_rm hGifs fun hm => hlgs (hlgs' _ (.inr (.inr (.inr hm)))), hGst⟩
  · exact goodGs_rm hGs hlrest'
  · exact goodEs_rm hEs hles
  · exact ⟨(hGt.rm fun hm => hlgs (hlgs' _ (.inr (.inl hm)))).rm hlt,
      goodEs_rm (goodEs_rm hGifs fun hm => hlgs (hlgs' _ (.inr (.inr (.inr hm))))) hlifs, hGst⟩
  · exact goodGs_rm (goodGs_rm hGs hlrest') hlrest
  · exact goodEs_rm (goodEs_rm hEs hles) hles2
  · have hsub : (labelsEs es ++ labelsGs rest).Sublist (labelsEs es ++ labelsGs (.mk lg t i ifs :: rest)) :=
      List.Sublist.append_left (by simp only [labelsGs]; exact (List.sublist_append_right _ _).cons _) _
    have hnd2 : (labelsGs rest ++ labelsEs es).Nodup :=
      List.perm_append_comm.nodup_iff.1 (hsub.nodup (List.nodup_cons.1 hnd).2)
    refine nextOk_of hEs rest _ hGs hnd2 fun y hy => ⟨⟨trivial, ?_⟩, ?_⟩
    · rintro rfl; rcases List.mem_append.1 hy with h | h
      · exact hlrest' h
      · exact hles h
    · rintro rfl; rcases List.mem_append.1 hy with h | h
      · exact hlrest h
      · exact hles2 h

/-! ## Entering a comprehension -/

theorem _root_.Surf.T2.ev_comp (l k es gs) : EvCase I p (.comp l k es gs) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  obtain ⟨g, rest, rfl⟩ : ∃ g rest, gs = g :: rest := by
    cases gs with
    | nil => have := hg.ok; simp [okE] at this
    | cons g rest => exact ⟨g, rest, rfl⟩
  obtain ⟨lg, tg, it, ifs⟩ := g
  let C := f.chain
  let S : Scope := .comp l k es (.mk lg tg it ifs :: rest)
  let body := compWrap l k (trGs (S :: C) (fresh "i" l) true (.mk lg tg it ifs :: rest)
    (compElt l k (trEs (S :: C) es)))
  let S' : PyCore.Scope := .fn (sub l 1) true (fresh "i" l) body
  have hS' : trScope C S = S' := rfl
  let arg := cc l 3 "$op:iter" [trE C it]
  let n := t.next
  have htr : trE C (.comp l k es (.mk lg tg it ifs :: rest)) = .call (sub l 0) (.lam (sub l 1) true (fresh "i" l) body) arg := by
    simp [trE, trG1, body, arg, S, C]
  let K' := f'.kont
  let ob : PyCore.Obj σ := .clo S' f'.chain (Py.memo S'.names (PyCore.clsOf (S' :: f'.chain))).get
    (Py.memo S'.names (PyCore.capture f' S')).get none
  let lamE : PE := .lam (sub l 1) true (fresh "i" l) body
  let g1 : PyCore.Frame σ := { f' with ctrl := .ev lamE, kont := .callF arg :: K' }
  let t1 : PyCore.Config σ := { t with stack := g1 :: fs' }
  let g2 : PyCore.Frame σ := { f' with ctrl := .val (.fn n), kont := .callF arg :: K' }
  let t2 : PyCore.Config σ := { t with stack := g2 :: fs', objs := t.objs.insert n ob, next := n + 1 }
  let g3 : PyCore.Frame σ := { f' with ctrl := .ev arg, kont := .callA (.fn n) :: K' }
  let t3 : PyCore.Config σ := { t2 with stack := g3 :: fs' }
  have st0 : PyCore.step I t = some t1 := by
    rw [pstep_ev A.ht (by rw [hc', htr])]; rfl
  have st1 : PyCore.step I t1 = some t2 := by
    simp only [PyCore.step, t1, PyCore.evalStep, PyCore.close]; rfl
  have st2 : PyCore.step I t2 = some t3 := by
    simp only [PyCore.step, t2, PyCore.valStep]; rfl
  obtain ⟨ys, pc, -, hfoc⟩ := cc_enter (I := I) t2 f' fs' (sub l 3) "$op:iter" (trE C it) [] (.callA (.fn n) :: K')
  rw [kc_iter I] at pc
  -- Surf's step
  have hnx : t.next = s.next := A.r.next
  let f1 : Sem.Frame σ := { f with ctrl := .ev it, kont := .compIt (.fn n) :: f.kont }
  let s1 : Sem.Config σ := { s with stack := f1 :: fs, objs := s.objs.insert n (Sem.mkClo f S []), next := n + 1 }
  have e1 : Sem.step I s = some s1 := by
    simp only [Sem.step, A.hs, hc, Sem.evalStep, s1, f1, n, hnx]; rfl
  have hts : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Expr.lbl])
  have hH : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  have hgi : GoodE p C U it := GoodE.of hg (fun x hx => by simp [itemsE, itemsG1, hx])
    (fun x hx => by rw [htr]; simp [PyCore.itemsE, arg, cc, ccR, recR, hx])
    (fun h => by simp_all [okE, okGs]) (fun x hx => by simp [labelsE, labelsGs, hx])
    (fun h => by simp_all [labelsE, labelsGs, List.nodup_cons, List.nodup_append])
    (fun x hx => by simp [touchE, touchGs, hx])
  let g4 : PyCore.Frame σ := { f' with ctrl := .ev (trE C it), kont := recK [] [] (.callA (.op .iter) :: .callA (.fn n) :: K') }
  let t4 : PyCore.Config σ := { t2 with stack := g4 :: fs' }
  have hob : ORel p (Seen (Touch p) H [s]) t4.glob t4.cells (Sem.mkClo f S []) ob := by
    have := orel_new (H := Seen (Touch p) H [s]) (p := p) (gl := t4.glob) (cs := t4.cells) A.hf.toFRel0
      (S := S) rfl (.inr ⟨s, by simp, hts⟩) (by simp [Scope.params]) (goodSc_comp W hg) (kok_comp A.hf.kok hg.ok)
    rw [hS', ← A.hf.chain] at this; exact this
  have hr : CRel p (Seen (Touch p) H [s]) s1 t4 := by
    have hst := A.r.stack
    rw [A.hs, A.ht] at hst
    refine ⟨⟨⟨A.hf.toFRel0.upd _ _ _ _, fun S0 C0 e => hH _ (A.hf.hl S0 C0 e), U, true, .ev hgi,
        .comp (.compIt (krel_move (rd := rdOf t4 g4) (own := ownOf t4 g4) hk rfl (fun _ _ _ _ => ⟨rfl, rfl⟩) hH))⟩,
      all2_mono (fun _ _ h => h.mono_H hH) hst.2⟩, fun o => ?_, A.r.cells, A.r.glob, A.r.out,
      rfl, A.r.res, A.r.st, fun x hx => A.r.wait x (by rw [A.hs]; exact hx), ?_, ?_⟩
    · simp only [sObj, pObj, s1, t4, t2, Std.HashMap.getElem?_insert, beq_iff_eq]
      split
      · exact hob
      · exact optRel_mono (fun _ _ h => h.mono_H hH) (A.r.objs o)
    · exact ids_alloc A.r.ids A.ht rfl rfl rfl rfl rfl (fun g h => by simp [ob] at h)
    · have hen := A.r.enter; rw [A.hs] at hen
      exact (hen.top _ (k := .compIt (.fn n) :: f.kont) (by esub)).ins (.inl (by simp only [n]; rw [hnx]; exact sobj_next A))
        fun g e => by simp [Sem.mkClo] at e
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st0 (.cons st1 (.cons st2 pc))) (by simp)
    (.inl hr) (cover_of (l := l) (by simp) hts ?_)
  intro y hy x hx
  simp only [List.mem_cons] at hy
  rcases hy with rfl | rfl | rfl | hy
  · simp [PyCore.focus, A.ht, hc', htr, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [PyCore.focus, t1, g1, lamE, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [PyCore.focus, t2, g2] at hx
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

/-! ## Helpers -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A continuation item that is no `enterK` added on top. -/
theorem esub_tail {a : Sem.Kont σ} {k K : List (Sem.Kont σ)} (ha : ∀ o b kx, a ≠ .enterK o b kx)
    (h : EnterSub k K) : EnterSub (a :: k) K := fun o b kx hm =>
  (List.mem_cons.1 hm).elim (fun e => absurd e.symm (ha o b kx)) (h o b kx)

/-- One Surf step and two PyCore steps through nodes evaluating nothing, the top frames' code changed. -/
theorem at_go12 (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)} {t1 : PyCore.Config σ}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (e2 : PyCore.step I t = some t1) (e3 : PyCore.step I t1 = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hf1 : PyCore.focus t = none) (hf2 : PyCore.focus t1 = none)
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k') (he : EnterSub k f.kont := by esub) : Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.cons e3 (.nil _))) (by simp) (crelI_seen (A.set hc hk he))
    (cover_none (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption))

/-- PyCore adds the value to an argument record. -/
theorem pstep_rec (ht : t.stack = f' :: fs') {v : Val} (hc' : f'.ctrl = .val v) {done : List Val}
    {K : List (PyCore.Kont σ)} (hK' : f'.kont = .binR "," (.data "$args" done) :: K) :
    PyCore.step I t = some { t with stack := { f' with ctrl := .val (.data "$args" (done ++ [v])), kont := K } :: fs' } := by
  rw [pstep_val ht hc']; simp only [PyCore.valStep, hK']; rfl

theorem focus_val (ht : t.stack = f' :: fs') {v : Val} (hc' : f'.ctrl = .val v) : PyCore.focus t = none := by
  simp [PyCore.focus, ht, hc']

/-- PyCore leaves `n` blocks that ended. -/
theorem seqs_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ)) :
    ∀ n, ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := .exec [], kont := seqs n ++ K } :: fs' }
      { t with stack := { g with ctrl := .exec [], kont := K } :: fs' } ys ∧ ∀ y ∈ ys, PyCore.focus y = none
  | 0 => ⟨[], .nil _, by simp⟩
  | n + 1 => by
    obtain ⟨ys, py, hy⟩ := seqs_path t g fs' K n
    refine ⟨_ :: ys, .cons (by simp [PyCore.step, PyCore.doneStep, seqs, List.replicate_succ, PyCore.top]) py, ?_⟩
    intro y hy'; rcases List.mem_cons.1 hy' with rfl | hy'
    · simp [PyCore.focus]
    · exact hy y hy'

/-- Fresh names whose tags start with different letters differ. -/
theorem fresh_tag_ne {a b : String} {c d : Char} {as bs : List Char} (ha : a.toList = c :: as)
    (hb : b.toList = d :: bs) (hcd : c ≠ d) (l l' : Label) : fresh a l ≠ fresh b l' := by
  intro e
  have := congrArg String.toList e
  simp [fresh, String.toList_append, ha, hb] at this
  exact hcd this.1

/-- `pstore0` with the reading of every other name kept (a clause's iterator and flag are names of the
same node as its item). -/
theorem cpstore1 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
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
    | (intro _ z hz; simp only [PyCore.writeAt]; exact lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns (some v))
    | (intro z hz; simp only [PyCore.writeAt, Std.HashMap.getElem?_insert, beq_iff_eq]; rw [ite_ne]; intro e
       exact hz (congrArg Prod.snd e).symm)

/-- `punset0` with the reading of every other name kept (the flag of the clause whose handler is left). -/
theorem cpunset1 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
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
    | (intro _ z hz; simp only [PyCore.writeAt]; exact lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns none)
    | (intro z hz; simp only [PyCore.writeAt, Std.HashMap.getElem?_erase, beq_iff_eq]; rw [ite_ne]; intro e
       exact hz (congrArg Prod.snd e).symm)

/-- Readings kept but at the fresh names of `l`, whose node is in the budget `U`. -/
theorem agree_but {U : Label → Prop} {rd own rd' own' : Name → Option Val} {l : Label} (hU : U l)
    (h : ∀ y, (∀ tag, tagOk tag = true → y ≠ fresh tag l) → rd' y = rd y ∧ own' y = own y) :
    Agree U rd own rd' own' :=
  fun tag l' ht hl' => h _ fun tag' ht' e => hl' (by rw [fresh_lab ht ht' e]; exact hU)

end

/-! ## Stuck code, stores into a clause's target -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore runs a statement `.expr L (gad l k .stuck [])` (what the translation gives for a shape CPython
rejects) and is stuck. -/
theorem pstuck (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (L l : Label) (k : Nat)
    (ss : PS) (K : List (PyCore.Kont σ)) :
    ∃ t' ys, Path (PyCore.step I) { t with stack := { g with ctrl := .exec (.expr L (gad l k .stuck []) :: ss), kont := K } :: gs }
      t' ys ∧ ys ≠ [] ∧ PyCore.step I t' = none ∧ t'.out = t.out ∧ t'.st = t.st ∧ t'.stack ≠ [] ∧
      ∀ y ∈ t' :: ys, ∀ x, PyCore.focus y = some x → x = L ∨ x = sub l k := by
  let r := sub l k
  let K1 : List (PyCore.Kont σ) := .exprS :: .seq ss :: K
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ := fun c k => { t with stack := { g with ctrl := c, kont := k } :: gs }
  refine ⟨mk (.val (.data "$args" [])) (.callA (.prim "$stuck") :: K1),
    [mk (.exec (.expr L (gad l k .stuck []) :: ss)) K, mk (.ev (gad l k .stuck [])) K1,
      mk (.ev (.const r "$stuck")) (.callF (.const r "$args") :: K1),
      mk (.val (.prim "$stuck")) (.callF (.const r "$args") :: K1),
      mk (.ev (.const r "$args")) (.callA (.prim "$stuck") :: K1)], ?_, by simp, ?_, rfl, rfl, by simp [mk], ?_⟩
  · refine .cons (by simp [mk, PyCore.step, PyCore.execStep, PyCore.top, K1]) (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))))
    · simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, gad, cc, ccR, recR, Py.Gadget.name, r]
    · simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, kc_stuck I]
    · simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
    · simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
  · simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, gad_stuck', PyCore.gadgetStep]
  · intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mk, PyCore.focus, PyCore.Stmt.label, PyCore.Expr.label, gad, cc, ccR, r] at hx <;>
      first | exact .inl hx.symm | exact .inr hx.symm

theorem ct_conf {c : PyCore.Ctrl σ} {K : List (PyCore.Kont σ)} (ht : t.stack = f' :: fs') (hc : f'.ctrl = c)
    (hk : f'.kont = K) : t = { t with stack := { f' with ctrl := c, kont := K } :: fs' } := by
  subst hc; subst hk; exact (t_eta ht).symm

/-- Both runs are stuck: Surf now, PyCore at the end of `pb` from `t0`. -/
theorem fin_path (A : At0 p H s t f fs f' fs') {t0 t' : PyCore.Config σ} {ys : List (PyCore.Config σ)}
    (h1 : Sem.step I s = none) (pb : Path (PyCore.step I) t0 t' ys) (h2 : PyCore.step I t' = none)
    (hout : t'.out = t.out) (hst : t'.st = t.st) (hne : t'.stack ≠ [])
    (hc : Cover (Touch p) pfocus H [s] (t' :: ys)) : Goal I p H s t0 := by
  refine Or.inl ⟨s, t', [], ys, .nil _, h1, pb, h2, ?_, hc⟩
  obtain ⟨g, gs, hg⟩ : ∃ g gs, t'.stack = g :: gs := by
    cases h : t'.stack with
    | nil => exact absurd h hne
    | cons g gs => exact ⟨g, gs, rfl⟩
  simp [Fin, Sem.outcome, PyCore.outcome, A.hs, hg, OCorr, hout, hst, A.out, A.st]

end

/-! ## A clause's next item: the target's store -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The clause `g` (node `lg`) gets its iterator's next item `v`: PyCore keeps it in `.v lg` and ends the
iteration's `try`; Surf stores it into the target, its conditions and the loop's next iteration waiting. -/
theorem val_cNext (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {ci : Sem.CI} {it : Val}
    {lg : Label} {tg itg : Expr} {ifs : List Expr} {rest : List Gen} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {l : Label} {gs : List Gen} {C0 : List Scope} {iv : Name} {n : Nat}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cNext ci it (.mk lg tg itg ifs) rest :: K0)
    (hK' : f'.kont = nextK lg iv (genLoop f.chain l ci.k ci.es (.mk lg tg itg ifs) rest) [] (seqs n ++ K0'))
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (hiv : iv = fresh "i" l ∨ iv = fresh "j" lg)
    (hr : A.x.rd iv = some it) (hg : A.x.rd (fresh "g" lg) = some (.bool true))
    (ha : ci.k ≠ .gen → A.x.rd (fresh "acc" l) = some ci.acc) (hH : H lg)
    (f1 : FOks f.chain lg ["g", "v", "s"]) (f2 : GsFOk f.chain rest) (hU : U lg)
    (gp : GoodGP p f.chain (Rm U lg) (.mk lg tg itg ifs)) (g2 : GoodGs p f.chain (Rm U lg) rest)
    (g3 : GoodEs p f.chain (Rm U lg) ci.es) (k : KRel A.x U false K0 K0')
    (hT : SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain (forSrc lg) tg (trE f.chain tg))) (PI p))
    (hN : NextOk p f.chain (Rm U lg) ci.es rest) : Goal I p H s t := by
  have gt : GoodE p f.chain (Rm U lg) tg := gp.1
  let B := genLoop f.chain l ci.k ci.es (.mk lg tg itg ifs) rest
  let K3 : List (PyCore.Kont σ) := .seq [] :: loopK lg iv B [] :: seqs n ++ K0'
  obtain ⟨t1, g1, e1, A1, hgc, hgk, hrv, hsame⟩ := cpstore1 A.zero (tag := "v") (l := lg) (by decide)
    (f1 "v" (by simp)) v (.exec []) (.seq [] :: .tryE [stopH lg] B :: K3)
  have hvne : ∀ {a : String} {c : Char} {as : List Char}, a.toList = c :: as → c ≠ 'v' → ∀ l', fresh a l' ≠ fresh "v" lg :=
    fun ha hc l' => fresh_tag_ne ha rfl hc l' lg
  have st1 : PyCore.step I t = some t1 := by
    rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK', nextK]; exact e1
  let g2' : PyCore.Frame σ := { g1 with ctrl := .exec [], kont := .tryE [stopH lg] B :: K3 }
  let g3' : PyCore.Frame σ := { g1 with ctrl := .exec B, kont := K3 }
  have st2 : PyCore.step I t1 = some { t1 with stack := g2' :: fs' } := by
    rw [pstep_done A1.ht hgc]; simp only [PyCore.doneStep, hgk]; rfl
  have st3 : PyCore.step I { t1 with stack := g2' :: fs' } = some { t1 with stack := g3' :: fs' } := by
    simp [PyCore.step, PyCore.doneStep, PyCore.top, g2', g3']
  let Kf : List (Sem.Kont σ) := .cConds ci ifs rest :: .cLoop ci it (.mk lg tg itg ifs) rest :: K0
  let f1s : Sem.Frame σ := { f with ctrl := .store tg v, kont := Kf }
  have es : Sem.step I s = some { s with stack := f1s :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.valStep, hK, Sem.setC, f1s, Kf]
  have hH' : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  refine SimStep.pre es (.cons st1 (.cons st2 (.cons st3 (.nil _)))) (by simp) (cover_none ?_) ?_
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact focus_val A.ht hc'
    · simp [PyCore.focus, A1.ht, hgc]
    · simp [PyCore.focus, g2']
  have A3 := (A1.upd (.store tg v) f1s.kont (.exec B) K3
    (esub_tail (by simp) (esub_tail (by simp) (esub_cons hK)))).mono_H hH'
  -- the readings after the store of `.v lg`
  have r1 : ∀ y, y ≠ fresh "v" lg → rdOf t1 g1 y = rdOf t f' y := fun y hy => (hsame y hy).1
  have hiv' : iv ≠ fresh "v" lg := by
    rcases hiv with rfl | rfl
    · exact hvne rfl (by decide) l
    · exact hvne rfl (by decide) lg
  have hag : Agree U (rdOf t f') (ownOf t f') (rdOf t1 g1) (ownOf t1 g1) :=
    agree_but hU fun y hy => hsame y (hy "v" (by decide))
  have hloop : KRel (cx p (Seen (Touch p) H [s]) (rdOf t1 g1) (ownOf t1 g1) f1s) (Rm U lg) false
      (.cLoop ci it (.mk lg tg itg ifs) rest :: K0) (.seq [] :: loopK lg iv B [] :: seqs n ++ K0') :=
    .comp (.cLoop (U := U) (K := K0) (K' := K0') (l := l) (ci := ci) (it := it) (g := .mk lg tg itg ifs)
      (rest := rest) (gs := gs) (C0 := C0) (iv := iv) (n0 := 1) (n := n) hC hl hiv (by rw [← hr]; exact r1 _ hiv') (by rw [← hg]; exact r1 _ (hvne rfl (by decide) lg))
      (fun h => by rw [← ha h]; exact r1 _ (hvne rfl (by decide) l)) (show Seen (Touch p) H [s] lg from .inl hH) f1 f2 hU gp g2 g3 hN
      (krel_move k rfl hag hH'))
  refine store_sim tg A3 W rfl rfl gt hT (.name (k := 63) (by omega) (by decide) (rm_self U lg) hrv) ?_
  exact .comp (.cConds hC (fun h => hl h.1) (show Seen (Touch p) H [s] lg from .inl hH)
    (fun h => by rw [← ha h]; exact r1 _ (hvne rfl (by decide) l)) f2 gp.2.1 g2 g3 hN hloop)

end

/-! ## A clause's conditions, the next clause, the element -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore reads the accumulator and reaches the first element of the accumulation
`cc l 10 g (nm l 8 acc :: e :: es)`. -/
theorem acc_path (t : PyCore.Config σ) (g' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (l : Label) (nmg : String)
    (e : PE) (es : List PE) (K : List (PyCore.Kont σ)) {acc : Val} (hr : rdOf t g' (fresh "acc" l) = some acc) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { g' with
                          ctrl := .exec [.expr (sub l 9) (cc l 10 nmg (nm l 8 (fresh "acc" l) :: e :: es))],
                          kont := K } :: fs' }
      { t with stack := { g' with
                          ctrl := .ev e,
                          kont := recK [acc] es (.callA (Py.constVal I nmg) :: .exprS :: .seq [] :: K) } :: fs' } ys ∧
      ys ≠ [] ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l := by
  let K1 : List (PyCore.Kont σ) := .exprS :: .seq [] :: K
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { g' with ctrl := c, kont := k } :: fs' }
  let a0 : PE := nm l 8 (fresh "acc" l)
  obtain ⟨ys, pc, -, hfoc⟩ := cc_enter (I := I) t g' fs' (sub l 10) nmg a0 (e :: es) K1
  let K2 := recK [] (e :: es) (.callA (Py.constVal I nmg) :: K1)
  have s0 : PyCore.step I (mk (.exec [.expr (sub l 9) (cc l 10 nmg (a0 :: e :: es))]) K) =
      some (mk (.ev (ccR (sub l 10) nmg (a0 :: e :: es))) K1) := by
    simp [mk, PyCore.step, PyCore.execStep, PyCore.top, K1, cc]
  let gA : PyCore.Frame σ := { g' with ctrl := .ev a0, kont := K2 }
  have s1 : PyCore.step I (mk (.ev a0) K2) = some (mk (.val acc) K2) := by
    rw [pstep_ev (t := mk (.ev a0) K2) (f' := gA) (e := a0) rfl rfl]
    have hrn : PyCore.readName I (mk (.ev a0) K2) gA (fresh "acc" l) none = .ok acc :=
      readName_rd (t := mk (.ev a0) K2) (f' := gA) hr
    show PyCore.top (mk (.ev a0) K2) fs' { gA with ctrl := PyCore.resCtrl (gA :: fs') _ } = _
    rw [hrn]; rfl
  have s2 : PyCore.step I (mk (.val acc) K2) =
      some (mk (.val (.data "$args" [acc])) ((e :: es).map (.binL ",") ++ .callA (Py.constVal I nmg) :: K1)) :=
    pstep_rec (t := mk (.val acc) K2) (f' := { g' with ctrl := .val acc, kont := K2 }) rfl rfl rfl
  have s3 : PyCore.step I (mk (.val (.data "$args" [acc])) ((e :: es).map (.binL ",") ++ .callA (Py.constVal I nmg) :: K1)) =
      some (mk (.ev e) (recK [acc] es (.callA (Py.constVal I nmg) :: K1))) := by
    simp [mk, PyCore.step, PyCore.valStep, PyCore.top, recK]
  refine ⟨mk (.exec [.expr (sub l 9) (cc l 10 nmg (a0 :: e :: es))]) K :: ys ++
      [mk (.ev a0) K2, mk (.val acc) K2, mk (.val (.data "$args" [acc])) ((e :: es).map (.binL ",") ++ .callA (Py.constVal I nmg) :: K1)],
    (Path.cons s0 pc).append (.cons s1 (.cons s2 (.cons s3 (.nil _)))), by simp, ?_⟩
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [mk, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  rcases List.mem_append.1 hy with hy | hy
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · simp [mk, PyCore.focus, a0, nm, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [mk, PyCore.focus] at hx
  · simp [mk, PyCore.focus] at hx

/-- An element of the wrong number for its comprehension (not in the items): both runs are stuck. -/
theorem elt_stuck (A : At0 p H s t f fs f' fs') {t0 : PyCore.Config σ} {ys0 : List (PyCore.Config σ)} {l : Label}
    {K' : List (PyCore.Kont σ)} {ss : PS} (h1 : Sem.step I s = none)
    (hc' : f'.ctrl = .exec (.expr (sub l 9) (gad l 9 .stuck []) :: ss)) (hK' : f'.kont = K')
    (pre : Path (PyCore.step I) t0 t ys0) (hy0 : ∀ y ∈ ys0, PyCore.focus y = none) (hl0 : H l) : Goal I p H s t0 := by
  obtain ⟨t', ys, py, -, h2, ho, hst, hne, hfy⟩ := pstuck (I := I) t f' fs' (sub l 9) l 9 ss K'
  rw [← ct_conf A.ht hc' hK'] at py
  refine fin_path A h1 (pre.append py) h2 ho hst hne fun y hy x hx => ?_
  rcases List.mem_cons.1 hy with rfl | hy
  · rcases hfy _ List.mem_cons_self x (pfocus_le hx) with rfl | rfl <;> exact .inl (by rw [sub_div _ _ (by omega)]; exact hl0)
  rcases List.mem_append.1 hy with hy | hy
  · have := pfocus_le hx; rw [hy0 y hy] at this; cases this
  · rcases hfy _ (List.mem_cons_of_mem _ hy) x (pfocus_le hx) with rfl | rfl <;>
      exact .inl (by rw [sub_div _ _ (by omega)]; exact hl0)

/-- The condition `e` of a clause: Surf at `cConds`, PyCore at the clause's body `genBody` (reached from `t0`
on `pre`, which evaluates no node). -/
theorem conds_cond (A : At0 p H s t f fs f' fs') {U : Label → Prop} {ci : Sem.CI} {e : Expr} {ifs : List Expr}
    {rest : List Gen} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l lg : Label} {gs : List Gen}
    {C0 : List Scope} {m : Nat} {t0 : PyCore.Config σ} {ys0 : List (PyCore.Config σ)}
    (hc : f.ctrl = .exec []) (hK : f.kont = .cConds ci (e :: ifs) rest :: K)
    (hc' : f'.ctrl = .exec (genBody f.chain l ci.k ci.es lg (e :: ifs) rest)) (hK' : f'.kont = seqs m ++ K')
    (pre : Path (PyCore.step I) t0 t ys0) (hy0 : ∀ y ∈ ys0, PyCore.focus y = none)
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (hlg : H lg)
    (ha : ci.k ≠ .gen → rdOf t f' (fresh "acc" l) = some ci.acc) (f2 : GsFOk f.chain rest)
    (g1 : GoodEs p f.chain U (e :: ifs)) (g2 : GoodGs p f.chain U rest) (g3 : GoodEs p f.chain U ci.es)
    (hN : NextOk p f.chain U ci.es rest)
    (k : KRel (cx p H (rdOf t f') (ownOf t f') f) U false K K') : Goal I p H s t0 := by
  let s2 : Sem.Config σ := { s with stack := { f with ctrl := .ev e, kont := .cCond ci ifs rest :: K } :: fs }
  have e1 : Sem.step I s = some s2 := by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC, s2]
  let K2 : List (PyCore.Kont σ) := .ifS (genBody f.chain l ci.k ci.es lg ifs rest) [] :: seqs (m + 1) ++ K'
  have st : PyCore.step I t = some { t with stack := { f' with ctrl := .ev (trE f.chain e), kont := K2 } :: fs' } := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; simp only [PyCore.execStep, hK']; rfl
  refine goal_b (.cons e1 (.nil _)) (by simp) (pre.append (.cons st (.nil _))) (by simp)
    (crelI_seen ((A.upd _ _ _ _).crel (U := U) (i := true) (.ev (g1 e (by simp)))
      (.comp (.cCond (j := m) hC hl hlg ha f2 (fun e' h => g1 e' (by simp [h])) g2 g3 hN k)))) ?_
  refine Cover.append (cover_none hy0) ?_
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
  have hx := pfocus_le hx
  simp [PyCore.focus, A.ht, hc', genBody, ifsNest, trEs, PyCore.Stmt.label] at hx
  exact .inl (by rw [← hx, sub_div _ _ (by omega)]; exact hlg)

/-- The element, when the clauses ended: Surf evaluates it, PyCore its yield or accumulation. -/
theorem conds_elt (A : At0 p H s t f fs f' fs') {U : Label → Prop} {ci : Sem.CI} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} {l lg : Label} {gs : List Gen} {C0 : List Scope} {m : Nat} {t0 : PyCore.Config σ}
    {ys0 : List (PyCore.Config σ)} (hc : f.ctrl = .exec []) (hK : f.kont = .cConds ci [] [] :: K)
    (hc' : f'.ctrl = .exec (genBody f.chain l ci.k ci.es lg [] [])) (hK' : f'.kont = seqs m ++ K')
    (pre : Path (PyCore.step I) t0 t ys0) (hy0 : ∀ y ∈ ys0, PyCore.focus y = none)
    (hC : f.chain = .comp l ci.k ci.es gs :: C0)
    (ha : ci.k ≠ .gen → rdOf t f' (fresh "acc" l) = some ci.acc) (g3 : GoodEs p f.chain U ci.es)
    (k : KRel (cx p H (rdOf t f') (ownOf t f') f) U false K K') : Goal I p H s t0 := by
  have hl0 : H l := A.hl _ _ hC
  have fin : ∀ (e : Expr) (KS : List (Sem.Kont σ)) (K2 : List (PyCore.Kont σ)) (ys : List (PyCore.Config σ)),
      e ∈ ci.es → Sem.step I s = some { s with stack := { f with ctrl := .ev e, kont := KS } :: fs } →
      Path (PyCore.step I) t { t with stack := { f' with ctrl := .ev (trE f.chain e), kont := K2 } :: fs' } ys → ys ≠ [] →
      (∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l) →
      KRel (cx p H (rdOf t f') (ownOf t f') f) U true KS K2 → EnterSub KS f.kont → Goal I p H s t0 := by
    intro e KS K2 ys he e1 py hys hfy hk2 hKS
    refine goal_b (.cons e1 (.nil _)) (by simp) (pre.append py) (by simp [hys])
      (crelI_seen ((A.upd _ _ _ _ hKS).crel (.ev (g3 e he)) hk2))
      (Cover.append (cover_none hy0) fun y hy x hx => .inl ?_)
    rw [hfy y hy x (pfocus_le hx)]; exact hl0
  have stk : ∀ {k' : CompKind} {es : List Expr} {ss : PS}, ci.k = k' → ci.es = es → Sem.step I s = none →
      compElt l k' (trEs f.chain es) = .expr (sub l 9) (gad l 9 .stuck []) :: ss → Goal I p H s t0 :=
    fun h1 h2 h3 h4 => elt_stuck A h3 (by rw [hc', h1, h2]; exact congrArg _ h4) hK' pre hy0 hl0
  obtain ⟨ck, es, acc⟩ := ci
  simp only at hC hc' ha g3 stk fin
  rcases ck with _ | _ | _ | _ <;> rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, es⟩⟩⟩
  all_goals first
    | (apply stk rfl rfl
       · simp [Sem.step, A.hs, hc, Sem.doneStep, hK]
       · simp [compElt, trEs, stuckAt, gad, cc]; rfl)
    | skip
  · -- a list comprehension's element
    obtain ⟨ys, py, hys, hfy⟩ := acc_path (I := I) t f' fs' l "$op:accum:list" (trE f.chain e1) [] (seqs m ++ K')
      (ha (by simp))
    rw [kc_accum_list I] at py
    have hc2 : f'.ctrl = .exec [.expr (sub l 9) (cc l 10 "$op:accum:list" [nm l 8 (fresh "acc" l), trE f.chain e1])] := by
      rw [hc']; rfl
    rw [← ct_conf A.ht hc2 hK'] at py
    exact fin e1 (.cElt .list acc :: K) _ ys (by simp) (by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC])
      py hys hfy (.comp (.cElt (m := m) k)) (by esub)
  · -- a set comprehension's element
    obtain ⟨ys, py, hys, hfy⟩ := acc_path (I := I) t f' fs' l "$op:accum:set" (trE f.chain e1) [] (seqs m ++ K')
      (ha (by simp))
    rw [kc_accum_set I] at py
    have hc2 : f'.ctrl = .exec [.expr (sub l 9) (cc l 10 "$op:accum:set" [nm l 8 (fresh "acc" l), trE f.chain e1])] := by
      rw [hc']; rfl
    rw [← ct_conf A.ht hc2 hK'] at py
    exact fin e1 (.cElt .set acc :: K) _ ys (by simp) (by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC])
      py hys hfy (.comp (.cElt (m := m) k)) (by esub)
  · -- a dictionary comprehension's key and value
    obtain ⟨ys, py, hys, hfy⟩ := acc_path (I := I) t f' fs' l "$op:accum:dict" (trE f.chain e1) [trE f.chain e2]
      (seqs m ++ K') (ha (by simp))
    rw [kc_accum_dict I] at py
    have hc2 : f'.ctrl = .exec [.expr (sub l 9)
        (cc l 10 "$op:accum:dict" [nm l 8 (fresh "acc" l), trE f.chain e1, trE f.chain e2])] := by
      rw [hc']; rfl
    rw [← ct_conf A.ht hc2 hK'] at py
    exact fin e1 (.cKey acc e2 :: K) _ ys (by simp) (by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC])
      py hys hfy
      (.comp (.cKey (m := m) (g3 e2 (by simp)) k)) (by esub)
  · -- a generator expression's element, yielded
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
      fun c k => { t with stack := { f' with ctrl := c, kont := k } :: fs' }
    have s1 : PyCore.step I t = some (mk (.ev (.yield (sub l 10) (trE f.chain e1))) (.exprS :: .seq [] :: seqs m ++ K')) := by
      rw [pstep_exec A.ht (by rw [hc']; rfl)]; simp only [PyCore.execStep, hK']; rfl
    have s2 : PyCore.step I (mk (.ev (.yield (sub l 10) (trE f.chain e1))) (.exprS :: .seq [] :: seqs m ++ K')) =
        some (mk (.ev (trE f.chain e1)) (.yieldS :: .exprS :: .seq [] :: seqs m ++ K')) := by
      simp [mk, PyCore.step, PyCore.evalStep, PyCore.top]
    refine fin e1 (.yieldK :: .exprS :: K) _ [t, mk (.ev (.yield (sub l 10) (trE f.chain e1))) (.exprS :: .seq [] :: seqs m ++ K')]
      (by simp) (by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC]) (.cons s1 (.cons s2 (.nil _))) (by simp) ?_
      (.core (.yieldK (.comp (.cExpr (m := m + 1) k)))) (by esub)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [PyCore.focus, A.ht, hc', genBody, ifsNest, trLs, trGs, compElt, trEs, PyCore.Stmt.label] at hx
      subst hx; exact sub_div _ _ (by omega)
    · simp [mk, PyCore.focus, PyCore.Expr.label] at hx; subst hx; exact sub_div _ _ (by omega)

/-- The iterable of the next clause `g`: Surf evaluates it, PyCore its `iter` (Surf's configuration
touches `g`'s node). `hN`: the facts at `Rm U g.label` that `cIter` needs. -/
theorem conds_iter (A : At0 p H s t f fs f' fs') {U : Label → Prop} {ci : Sem.CI} {g : Gen} {rest : List Gen}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l lg0 : Label} {gs : List Gen} {C0 : List Scope} {m : Nat}
    {t0 : PyCore.Config σ} {ys0 : List (PyCore.Config σ)} (hc : f.ctrl = .exec []) (hK : f.kont = .cConds ci [] (g :: rest) :: K)
    (hc' : f'.ctrl = .exec (genBody f.chain l ci.k ci.es lg0 [] (g :: rest))) (hK' : f'.kont = seqs m ++ K')
    (pre : Path (PyCore.step I) t0 t ys0) (hy0 : ∀ y ∈ ys0, PyCore.focus y = none)
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l)
    (ha : ci.k ≠ .gen → rdOf t f' (fresh "acc" l) = some ci.acc) (f2 : GsFOk f.chain (g :: rest))
    (g2 : GoodGs p f.chain U (g :: rest)) (hN : NextOk p f.chain U ci.es (g :: rest))
    (k : KRel (cx p H (rdOf t f') (ownOf t f') f) U false K K') : Goal I p H s t0 := by
  obtain ⟨lg, tg, itg, ifs⟩ := g
  obtain ⟨hU, gp, g2', g3', hN'⟩ := hN
  have hts : Touch p s lg := .inr (by rw [A.hs]; simp [TouchF, hc, hK, Gen.label])
  have hH' : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  let C := f.chain
  let FL : PS := forLoop lg (fresh "j" lg) (trT C (forSrc lg) tg (trE C tg)) (genBody C l ci.k ci.es lg ifs rest) []
  let K1 : List (PyCore.Kont σ) := .assign (fresh "j" lg) :: .seq FL :: seqs m ++ K'
  have s1 : PyCore.step I t =
      some { t with stack := { f' with ctrl := .ev (ccR (sub lg 1) "$op:iter" [trE C itg]), kont := K1 } :: fs' } := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; simp only [PyCore.execStep, hK']; rfl
  obtain ⟨ys, pc, -, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lg 1) "$op:iter" (trE C itg) [] K1
  rw [kc_iter I] at pc
  let s2 : Sem.Config σ := { s with stack := { f with ctrl := .ev itg, kont := .cIter ci (.mk lg tg itg ifs) rest :: K } :: fs }
  have e1 : Sem.step I s = some s2 := by simp [Sem.step, A.hs, hc, Sem.doneStep, hK, Sem.setC, s2]
  have hit : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U true
      (.cIter ci (.mk lg tg itg ifs) rest :: K) (recK [] [] (.callA (.op .iter) :: K1)) :=
    .comp (.cIter (m := m) hC hl ha (show Seen (Touch p) H [s] lg from .inr ⟨s, by simp, hts⟩)
      hU (f2 (.mk lg tg itg ifs) (by simp)) (fun g' h => f2 g' (by simp [h]))
      gp g2' g3' hN' (KRel.ext ⟨hH', Agree.refl _ _ _⟩ k))
  refine goal_b (.cons e1 (.nil _)) (by simp) (pre.append (.cons s1 pc)) (by simp)
    (.inl (((A.upd _ _ _ _).mono_H hH').crel (U := U) (i := true) (.ev (g2 (.mk lg tg itg ifs) (by simp)).2) hit)) ?_
  refine Cover.append (cover_none hy0) (cover_of (s := s) (l := lg) (by simp) hts ?_)
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A.ht, hc', genBody, ifsNest, trEs, trGs, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

/-- Surf's `cConds` and PyCore's clause body `genBody`. -/
theorem conds_go (A : At0 p H s t f fs f' fs') {U : Label → Prop} {ci : Sem.CI} {ifs : List Expr}
    {rest : List Gen} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l lg : Label} {gs : List Gen}
    {C0 : List Scope} {m : Nat} {t0 : PyCore.Config σ} {ys0 : List (PyCore.Config σ)}
    (hc : f.ctrl = .exec []) (hK : f.kont = .cConds ci ifs rest :: K)
    (hc' : f'.ctrl = .exec (genBody f.chain l ci.k ci.es lg ifs rest)) (hK' : f'.kont = seqs m ++ K')
    (pre : Path (PyCore.step I) t0 t ys0) (hy0 : ∀ y ∈ ys0, PyCore.focus y = none)
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (hlg : H lg)
    (ha : ci.k ≠ .gen → rdOf t f' (fresh "acc" l) = some ci.acc) (f2 : GsFOk f.chain rest)
    (g1 : GoodEs p f.chain U ifs) (g2 : GoodGs p f.chain U rest) (g3 : GoodEs p f.chain U ci.es)
    (hN : NextOk p f.chain U ci.es rest)
    (k : KRel (cx p H (rdOf t f') (ownOf t f') f) U false K K') : Goal I p H s t0 := by
  cases ifs with
  | cons e ifs => exact conds_cond A hc hK hc' hK' pre hy0 hC hl hlg ha f2 g1 g2 g3 hN k
  | nil =>
    cases rest with
    | nil => exact conds_elt A hc hK hc' hK' pre hy0 hC ha g3 k
    | cons g rest => exact conds_iter A hc hK hc' hK' pre hy0 hC hl ha f2 g2 hN k

end

/-! ## Signals passing PyCore's items -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The PyCore items a signal `c'` passes in one step. -/
def popOk : PyCore.Ctrl σ → PyCore.Kont σ → Bool
  | .raise _, .tryE (_ :: _) _ | .raise _, .catchS .. | .raise _, .yfGot _ | .raise _, .native _ => false
  | _, .handler .. => false
  | .brk, .loop .. | .cont, .loop .. => false
  | _, _ => true

theorem cpop1 {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (hs : CSig i C U c c')
    (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (k : PyCore.Kont σ) (K : List (PyCore.Kont σ))
    (hk : popOk c' k = true) :
    PyCore.step I { t with stack := { g with ctrl := c', kont := k :: K } :: gs } =
      some { t with stack := { g with ctrl := c', kont := K } :: gs } := by
  rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> cases k <;>
    simp_all [popOk, PyCore.step, PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top]
  all_goals (rename_i hs0 u; cases hs0 <;> simp_all [popOk, PyCore.step, PyCore.raiseStep, PyCore.top])

theorem cpopn {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (hs : CSig i C U c c')
    (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ)) :
    ∀ P : List (PyCore.Kont σ), P.all (popOk c') = true →
    ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := c', kont := P ++ K } :: gs }
      { t with stack := { g with ctrl := c', kont := K } :: gs } ys ∧ ys.length = P.length ∧
      ∀ y ∈ ys, PyCore.focus y = none
  | [], _ => ⟨[], .nil _, rfl, by simp⟩
  | k :: P, h => by
    have h' : (popOk c' k && P.all (popOk c')) = true := h
    have h1 : popOk c' k = true := by revert h'; cases popOk c' k <;> simp
    have h2 : P.all (popOk c') = true := by revert h'; cases P.all (popOk c') <;> simp
    obtain ⟨ys, py, hl, hy⟩ := cpopn hs t g gs K P h2
    refine ⟨_ :: ys, .cons (cpop1 hs t g gs k (P ++ K) h1) py, by simp [hl], ?_⟩
    intro y hy'
    rcases List.mem_cons.1 hy' with rfl | hy'
    · rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> simp only [PyCore.focus]
      cases k <;> simp_all [popOk]
      rename_i hs0 u; cases hs0 <;> simp_all [popOk]
    · exact hy y hy'

/-- A signal passes the Surf item on top and the PyCore items `P`. -/
theorem csig_popn (A : At p H s t f fs f' fs') {U U' : Label → Prop} {i j : Bool} (hs : CSig i f.chain U f.ctrl f'.ctrl)
    (hij : i = false → j = false)
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (P : List (PyCore.Kont σ)) (hP : P ≠ [])
    (hp : P.all (popOk f'.ctrl) = true) (hK' : f'.kont = P ++ K0') (hk : KRel A.x U' j K0 K0')
    (e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs }) (he : EnterSub K0 f.kont := by esub) :
    Goal I p H s t := by
  obtain ⟨ys, py, hl, hy⟩ := cpopn (I := I) hs t f' fs' K0' P hp
  have e : t = { t with stack := { f' with ctrl := f'.ctrl, kont := P ++ K0' } :: fs' } := ct_conf A.ht rfl hK'
  exact goal_b (.cons e1 (.nil _)) (by simp) (by rw [e]; exact py)
    (by rintro rfl; exact hP (List.eq_nil_of_length_eq_zero hl.symm)) (crelI_seen (A.set (csig_cr hs hij U') hk he))
    (cover_none hy)

theorem all_seqs (q : PyCore.Kont σ → Bool) (h : q (.seq []) = true) : ∀ n, (seqs n : List (PyCore.Kont σ)).all q = true
  | 0 => rfl
  | n + 1 => by simp only [seqs, List.replicate_succ, List.all_cons, h, Bool.true_and]; exact all_seqs q h n

theorem popOk_seq {c' : PyCore.Ctrl σ} (ss : PS) : popOk c' (.seq ss) = true := by
  cases c' <;> rfl

@[simp] theorem all_seqs_popOk (c' : PyCore.Ctrl σ) (n : Nat) : (seqs n : List (PyCore.Kont σ)).all (popOk c') = true :=
  all_seqs _ (popOk_seq []) n

end

/-! ## The cases -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The element's statement after `accum` or `yield`: PyCore leaves its `m` blocks. -/
theorem val_cExpr (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {m : Nat} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .exprS :: K0) (hK' : f'.kont = .exprS :: seqs m ++ K0') (k : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  obtain ⟨ys, py, hy⟩ := seqs_path (I := I) t f' fs' K0' m
  have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec [], kont := seqs m ++ K0' } :: fs' } := by
    rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; rfl
  exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]) (.nil _)) (by simp)
    (.cons e2 py) (by simp) (crelI_seen (A.set (U := U) (.exec (goodB_nil _ U) (by simp)) k))
    (cover_none (by intro y hy'; rcases List.mem_cons.1 hy' with rfl | hy'; exact focus_val A.ht hc'; exact hy y hy'))

/-- The call of the comprehension's function on its first iterator: Surf's step to the call, which PyCore
makes from its `callA` (a pending call). -/
theorem val_compCall (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {o : Nat} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .compCall (.fn o) :: K0) (hK' : f'.kont = .callA (.fn o) :: K0') (k : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .call (.fn o) [v] [], kont := K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, s1]
  have hH : ∀ l, H l → Seen (Touch p) H [s1, s] l := fun _ h => .inl h
  refine Or.inr (Or.inr (Or.inl ⟨s1, [s], .cons e1 (.nil _), by simp, ?_, ?_⟩))
  · exact pend_callA ((A.zero.updS (.call (.fn o) [v] []) K0).mono_H hH) (U := U)
      (.inr ⟨o, rfl⟩) rfl hc' hK' (KRel.ext ⟨hH, Agree.refl _ _ _⟩ k)
  · simp [μ, s1, A.hs, A.ht, hK, hK']

/-- A later clause's iterable's value: its `iter`. -/
theorem val_cIter (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {ci : Sem.CI} {lg : Label} {tg itg : Expr}
    {ifs : List Expr} {rest : List Gen} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {l : Label} {gs : List Gen}
    {C0 : List Scope} {m : Nat} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cIter ci (.mk lg tg itg ifs) rest :: K0)
    (hK' : f'.kont = recK [] [] (.callA (.op .iter) :: .assign (fresh "j" lg) ::
      .seq (forLoop lg (fresh "j" lg) (trT f.chain (forSrc lg) tg (trE f.chain tg)) (genBody f.chain l ci.k ci.es lg ifs rest) []) ::
        seqs m ++ K0'))
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (ha : ci.k ≠ .gen → A.x.rd (fresh "acc" l) = some ci.acc)
    (hH : H lg) (f1 : FOks f.chain lg ["j", "g", "v", "s"]) (f2 : GsFOk f.chain rest)
    (hU : U lg) (gg : GoodGP p f.chain (Rm U lg) (.mk lg tg itg ifs)) (g2 : GoodGs p f.chain (Rm U lg) rest)
    (g3 : GoodEs p f.chain (Rm U lg) ci.es) (g4 : NextOk p f.chain (Rm U lg) ci.es rest) (k : KRel A.x U false K0 K0') :
    Goal I p H s t :=
  at_go12 A (c := .op .iter [v]) (c' := .op .iter [v]) (k := .cIt ci (.mk lg tg itg ifs) rest :: K0)
    (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC])
    (pstep_rec A.ht hc' (by rw [hK']; rfl))
    (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top, Gen.label]) (focus_val A.ht hc')
    (by simp [PyCore.focus]) .op (.comp (.cIt (m := m) hC hl ha hH hU f1 f2 gg g2 g3 g4 k))

end

/-! ## The loops' start: PyCore's code up to a clause's `next` -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem constVal_next : Py.constVal I "$next" = .next := by simp [Py.constVal]

/-- PyCore tests a clause's flag (true) and reaches the core's `next` on the iterator in `iv`; every node on
the way is made for the clause `l`. -/
theorem cloop_iter (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (l : Label)
    (iv : Name) (B U' : PS) (K : List (PyCore.Kont σ)) {it : Val}
    (hg : rdOf t f' (fresh "g" l) = some (.bool true)) (hi : rdOf t f' iv = some it) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .ev (.name (sub l 13) (fresh "g" l) none),
        kont := .whileS (.name (sub l 13) (fresh "g" l) none) [tryS l iv B] U' :: K } :: fs' }
      { t with stack := { f' with
        ctrl := .val it,
        kont := .callA .next :: .assign (fresh "v" l) :: .seq [] :: .tryE [stopH l] B :: .seq [] ::
          loopK l iv B U' :: K } :: fs' } ys ∧ ys ≠ [] ∧
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
    simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_next]
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


/-- The first iterator's `next` after the accumulator is made (`compStart`'s value). The clause's
node is touched by the configuration reached; `gp`, `g2`, `g3`: the clause's facts at
`Rm (Rm U l) lg`. -/
theorem val_compStart (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {ci : Sem.CI} {it : Val}
    {lg : Label} {tg itg : Expr} {ifs : List Expr}
    {rest : List Gen} {l : Label} {gs : List Gen} {C0 : List Scope} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = [.compStart ci it (.mk lg tg itg ifs) rest])
    (hK' : f'.kont = [.assign (fresh "acc" l), .seq (trGs f.chain (fresh "i" l) true (.mk lg tg itg ifs :: rest)
      (compElt l ci.k (trEs f.chain ci.es)) ++ [retAcc l])])
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hU : U l)
    (hr : A.x.rd (fresh "i" l) = some it) (fa : FOk f.chain (fresh "acc" l))
    (f1 : FOks f.chain lg ["g", "v", "s"]) (f2 : GsFOk f.chain rest) (hUg : Rm U l lg)
    (gp : GoodGP p f.chain (Rm (Rm U l) lg) (.mk lg tg itg ifs))
    (g2 : GoodGs p f.chain (Rm (Rm U l) lg) rest) (g3 : GoodEs p f.chain (Rm (Rm U l) lg) ci.es)
    (g4 : NextOk p f.chain (Rm (Rm U l) lg) ci.es rest) : Goal I p H s t := by
  let ci' : Sem.CI := { ci with acc := v }
  let B := genLoop f.chain l ci.k ci.es (.mk lg tg itg ifs) rest
  let iv := fresh "i" l
  let cnd : PE := .name (sub lg 13) (fresh "g" lg) none
  let W0 : PyCore.Stmt := .while (sub lg 12) cnd [tryS lg iv B] []
  let A0 : PyCore.Stmt := .assign (sub lg 10) (fresh "g" lg) (.const (sub lg 11) "$true")
  let Km : List (PyCore.Kont σ) := [.seq [retAcc l]]
  obtain ⟨t1, g1, e1', A1, hgc1, hgk1, hra, hs1⟩ := cpstore1 A.zero (tag := "acc") (l := l) (by decide)
    fa v (.exec []) [.seq (trGs f.chain (fresh "i" l) true (.mk lg tg itg ifs :: rest)
      (compElt l ci.k (trEs f.chain ci.es)) ++ [retAcc l])]
  have st1 : PyCore.step I t = some t1 := by
    rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e1'
  let mk1 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
  have st2 : PyCore.step I t1 = some (mk1 (.exec [A0, W0, retAcc l]) []) := by
    rw [pstep_done A1.ht hgc1]; simp only [PyCore.doneStep, hgk1]; rfl
  have st3 : PyCore.step I (mk1 (.exec [A0, W0, retAcc l]) []) =
      some (mk1 (.ev (.const (sub lg 11) "$true")) (.assign (fresh "g" lg) :: .seq [W0, retAcc l] :: [])) := by
    simp [mk1, PyCore.step, PyCore.execStep, PyCore.top, A0]
  have st4 : PyCore.step I (mk1 (.ev (.const (sub lg 11) "$true")) (.assign (fresh "g" lg) :: .seq [W0, retAcc l] :: [])) =
      some (mk1 (.val (.bool true)) (.assign (fresh "g" lg) :: .seq [W0, retAcc l] :: [])) := by
    simp [mk1, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  obtain ⟨t5, g5, e5, A5, hgc5, hgk5, hrg, hs5⟩ := cpstore1 (A1.updT (.val (.bool true))
    (.assign (fresh "g" lg) :: .seq [W0, retAcc l] :: []))
    (tag := "g") (l := lg) (by decide) (f1 "g" (by simp)) (.bool true) (.exec []) [.seq [W0, retAcc l]]
  have st5 : PyCore.step I (mk1 (.val (.bool true)) (.assign (fresh "g" lg) :: .seq [W0, retAcc l] :: [])) = some t5 := by
    rw [pstep_val rfl rfl]; simp only [PyCore.valStep]; exact e5
  let mk5 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t5 with stack := { g5 with ctrl := c, kont := k } :: fs' }
  have st6 : PyCore.step I t5 = some (mk5 (.exec [W0, retAcc l]) []) := by
    rw [pstep_done A5.ht hgc5]; simp only [PyCore.doneStep, hgk5]; rfl
  have st7 : PyCore.step I (mk5 (.exec [W0, retAcc l]) []) =
      some (mk5 (.ev cnd) (.whileS cnd [tryS lg iv B] [] :: Km)) := by
    simp [mk5, PyCore.step, PyCore.execStep, PyCore.top, W0, Km]
  have hi1 : rdOf t1 g1 iv = some it := by
    rw [(hs1 _ (fresh_tag_ne rfl rfl (by decide) l l)).1]; exact hr
  have hri : rdOf t5 g5 iv = some it := by
    rw [(hs5 _ (fresh_tag_ne rfl rfl (by decide) l lg)).1]; exact hi1
  have hra5 : rdOf t5 g5 (fresh "acc" l) = some v := by
    rw [(hs5 _ (fresh_tag_ne rfl rfl (by decide) l lg)).1]; exact hra
  obtain ⟨ys2, py2, -, hy2⟩ := cloop_iter (I := I) t5 g5 fs' lg iv B [] Km hrg hri
  let f1s : Sem.Frame σ := { f with ctrl := .call .next [it] [], kont := [.cNext ci' it (.mk lg tg itg ifs) rest, .cAcc v] }
  let s1 : Sem.Config σ := { s with stack := f1s :: fs }
  have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.compLoop, Sem.setC, s1, f1s, ci']
  have hT1 : Touch p s1 lg := .inr (by simp [s1, f1s, TouchF, Gen.label])
  have hH' : ∀ l', H l' → Seen (Touch p) H [s1, s] l' := fun _ h => .inl h
  have py := Path.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 py2))))))
  have hacc : CompK (cx p (Seen (Touch p) H [s1, s]) (rdOf t5 g5) (ownOf t5 g5) f1s) (Rm U l) false
      [.cAcc v] (Km : List (PyCore.Kont σ)) := .cAcc (U := U) hC hra5
  have AA : At0 p (Seen (Touch p) H [s1, s]) s1
      { t5 with stack := { g5 with ctrl := .val it, kont := .callA .next :: nextK lg iv B [] (seqs 0 ++ Km) } :: fs' }
      f1s fs { g5 with ctrl := .val it, kont := .callA .next :: nextK lg iv B [] (seqs 0 ++ Km) } fs' :=
    (A5.upd (.call .next [it] []) f1s.kont (.val it) (.callA .next :: nextK lg iv B [] (seqs 0 ++ Km))
      fun _ _ _ hm => by simp [f1s] at hm).mono_H hH'
  have hk1 : KRel (cx p (Seen (Touch p) H [s1, s]) (rdOf t5 g5) (ownOf t5 g5) f1s) (Rm (Rm U l) lg) true f1s.kont
      (nextK lg iv B [] (seqs 0 ++ Km)) :=
    .comp (.cNext (U := Rm U l) (K := [.cAcc v]) (K' := Km) (l := l) (ci := ci') (it := it)
        (g := .mk lg tg itg ifs) (rest := rest) (iv := iv) (n := 0) (gs := gs) (C0 := C0) hC (rm_self U l) (.inl rfl) hri hrg
        (fun _ => hra5) (show Seen (Touch p) H [s1, s] lg from .inr ⟨s1, by simp, hT1⟩) f1 f2 hUg gp g2 g3 g4 (.comp hacc))
  refine goal_t (.cons e1 (.nil _)) (by simp) py (by simp) (pend_callA AA (.inl rfl) rfl rfl rfl hk1) ?_
  have hl' : ∀ k, k < 64 → Seen (Touch p) H [s1, s] (sub lg k / 64) := fun k hk =>
    .inr ⟨s1, by simp, by rw [sub_div _ _ hk]; exact hT1⟩
  intro y hy x hx
  have hx' := pfocus_le hx
  simp only [List.mem_cons] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hy
  · simp [PyCore.focus, A.ht, hc'] at hx'
  · simp [PyCore.focus, A1.ht, hgc1] at hx'
  · simp [mk1, PyCore.focus, A0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 10 (by omega)
  · simp [mk1, PyCore.focus, PyCore.Expr.label] at hx'; subst hx'; exact hl' 11 (by omega)
  · simp [mk1, PyCore.focus] at hx'
  · simp [PyCore.focus, A5.ht, hgc5] at hx'
  · simp [mk5, PyCore.focus, W0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 12 (by omega)
  · rw [hy2 y hy x hx']; exact .inr ⟨s1, by simp, hT1⟩

/-- A later clause's loop starts on its iterator `v`: PyCore keeps it in `.j lg`, sets the flag and
reaches the `next`. -/
theorem val_cIt (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {ci : Sem.CI} {lg : Label}
    {tg itg : Expr} {ifs : List Expr} {rest : List Gen} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    {l : Label} {gs : List Gen} {C0 : List Scope} {m : Nat} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cIt ci (.mk lg tg itg ifs) rest :: K0)
    (hK' : f'.kont = .assign (fresh "j" lg) ::
      .seq (forLoop lg (fresh "j" lg) (trT f.chain (forSrc lg) tg (trE f.chain tg)) (genBody f.chain l ci.k ci.es lg ifs rest) []) ::
        seqs m ++ K0')
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (ha : ci.k ≠ .gen → A.x.rd (fresh "acc" l) = some ci.acc)
    (hH : H lg) (hU : U lg) (f1 : FOks f.chain lg ["j", "g", "v", "s"]) (f2 : GsFOk f.chain rest)
    (gp : GoodGP p f.chain (Rm U lg) (.mk lg tg itg ifs)) (g2 : GoodGs p f.chain (Rm U lg) rest)
    (g3 : GoodEs p f.chain (Rm U lg) ci.es) (g4 : NextOk p f.chain (Rm U lg) ci.es rest) (k : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  let B := genLoop f.chain l ci.k ci.es (.mk lg tg itg ifs) rest
  let cnd : PE := .name (sub lg 13) (fresh "g" lg) none
  let W0 : PyCore.Stmt := .while (sub lg 12) cnd [tryS lg (fresh "j" lg) B] []
  let A0 : PyCore.Stmt := .assign (sub lg 10) (fresh "g" lg) (.const (sub lg 11) "$true")
  let Km : List (PyCore.Kont σ) := seqs m ++ K0'
  obtain ⟨t1, g1, e1', A1, hgc1, hgk1, hrj, hs1⟩ := cpstore1 A.zero (tag := "j") (l := lg) (by decide)
    (f1 "j" (by simp)) v (.exec []) (.seq [A0, W0] :: Km)
  have st1 : PyCore.step I t = some t1 := by
    rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e1'
  let mk1 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t1 with stack := { g1 with ctrl := c, kont := k } :: fs' }
  have st2 : PyCore.step I t1 = some (mk1 (.exec [A0, W0]) Km) := by
    rw [pstep_done A1.ht hgc1]; simp only [PyCore.doneStep, hgk1]; rfl
  have st3 : PyCore.step I (mk1 (.exec [A0, W0]) Km) =
      some (mk1 (.ev (.const (sub lg 11) "$true")) (.assign (fresh "g" lg) :: .seq [W0] :: Km)) := by
    simp [mk1, PyCore.step, PyCore.execStep, PyCore.top, A0]
  have st4 : PyCore.step I (mk1 (.ev (.const (sub lg 11) "$true")) (.assign (fresh "g" lg) :: .seq [W0] :: Km)) =
      some (mk1 (.val (.bool true)) (.assign (fresh "g" lg) :: .seq [W0] :: Km)) := by
    simp [mk1, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  obtain ⟨t5, g5, e5, A5, hgc5, hgk5, hrg, hs5⟩ := cpstore1 (A1.updT (.val (.bool true)) (.assign (fresh "g" lg) :: .seq [W0] :: Km))
    (tag := "g") (l := lg) (by decide) (f1 "g" (by simp)) (.bool true) (.exec []) (.seq [W0] :: Km)
  have st5 : PyCore.step I (mk1 (.val (.bool true)) (.assign (fresh "g" lg) :: .seq [W0] :: Km)) = some t5 := by
    rw [pstep_val rfl rfl]; simp only [PyCore.valStep]; exact e5
  let mk5 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t5 with stack := { g5 with ctrl := c, kont := k } :: fs' }
  have st6 : PyCore.step I t5 = some (mk5 (.exec [W0]) Km) := by
    rw [pstep_done A5.ht hgc5]; simp only [PyCore.doneStep, hgk5]; rfl
  have st7 : PyCore.step I (mk5 (.exec [W0]) Km) =
      some (mk5 (.ev cnd) (.whileS cnd [tryS lg (fresh "j" lg) B] [] :: .seq [] :: Km)) := by
    simp [mk5, PyCore.step, PyCore.execStep, PyCore.top, W0]
  have hjg : fresh "j" lg ≠ fresh "g" lg := fresh_tag_ne rfl rfl (by decide) lg lg
  have hrj5 : rdOf t5 g5 (fresh "j" lg) = some v := by rw [(hs5 _ hjg).1]; exact hrj
  obtain ⟨ys2, py2, -, hy2⟩ := cloop_iter (I := I) t5 g5 fs' lg (fresh "j" lg) B [] (.seq [] :: Km) hrg hrj5
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .call .next [v] [],
                                                       kont := .cNext ci v (.mk lg tg itg ifs) rest :: K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.compLoop, Sem.setC, s1]
  have hH' : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  have hacc : rdOf t5 g5 (fresh "acc" l) = rdOf t f' (fresh "acc" l) :=
    ((hs5 _ (fresh_tag_ne rfl rfl (by decide) l lg)).1).trans ((hs1 _ (fresh_tag_ne rfl rfl (by decide) l lg)).1)
  have hag : Agree U (rdOf t f') (ownOf t f') (rdOf t5 g5) (ownOf t5 g5) :=
    (agree_but hU fun y hy => hs1 y (hy "j" rfl)).trans (agree_but hU fun y hy => hs5 y (hy "g" rfl))
  have py := Path.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 py2))))))
  refine goal_b (.cons e1 (.nil _)) (by simp) py (by simp)
    (pend_callA ((A5.upd (.call .next [v] []) (.cNext ci v (.mk lg tg itg ifs) rest :: K0) (.val v)
      (.callA .next :: nextK lg (fresh "j" lg) B [] (.seq [] :: Km))).mono_H hH') (.inl rfl) rfl rfl rfl
      (.comp (.cNext (n := m + 1) hC hl (.inr rfl) hrj5 hrg (fun h => hacc.trans (ha h)) (hH' _ hH)
        (fun tag h => f1 tag (List.mem_cons_of_mem _ h)) f2 hU gp g2 g3 g4 (KRel.ext ⟨hH', hag⟩ k)))) ?_
  have hl' : ∀ k, k < 64 → Seen (Touch p) H [s1, s] (sub lg k / 64) := fun k hk => .inl (by rw [sub_div _ _ hk]; exact hH)
  intro y hy x hx
  have hx' := pfocus_le hx
  simp only [List.mem_cons] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hy
  · simp [PyCore.focus, A.ht, hc'] at hx'
  · simp [PyCore.focus, A1.ht, hgc1] at hx'
  · simp [mk1, PyCore.focus, A0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 10 (by omega)
  · simp [mk1, PyCore.focus, PyCore.Expr.label] at hx'; subst hx'; exact hl' 11 (by omega)
  · simp [mk1, PyCore.focus] at hx'
  · simp [PyCore.focus, A5.ht, hgc5] at hx'
  · simp [mk5, PyCore.focus, W0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 12 (by omega)
  · exact .inl (by rw [hy2 y hy x hx']; exact hH)

/-- The loop of a clause goes round: PyCore leaves its blocks, tests the flag and reaches the `next`. -/
theorem done_cLoop (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {ci : Sem.CI} {it : Val} {g : Gen}
    {rest : List Gen} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {l : Label} {gs : List Gen}
    {C0 : List Scope} {iv : Name} {n0 n : Nat} (hc : f.ctrl = .exec []) (hc' : f'.ctrl = .exec [])
    (hK : f.kont = .cLoop ci it g rest :: K0)
    (hK' : f'.kont = seqs n0 ++ loopK g.label iv (genLoop f.chain l ci.k ci.es g rest) [] :: seqs n ++ K0')
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hl : ¬ U l) (hiv : iv = fresh "i" l ∨ iv = fresh "j" g.label)
    (hr : A.x.rd iv = some it) (hg : A.x.rd (fresh "g" g.label) = some (.bool true))
    (ha : ci.k ≠ .gen → A.x.rd (fresh "acc" l) = some ci.acc) (hH : H g.label)
    (f1 : FOks f.chain g.label ["g", "v", "s"]) (f2 : GsFOk f.chain rest) (hU : U g.label)
    (gp : GoodGP p f.chain (Rm U g.label) g) (g2 : GoodGs p f.chain (Rm U g.label) rest)
    (g3 : GoodEs p f.chain (Rm U g.label) ci.es) (g4 : NextOk p f.chain (Rm U g.label) ci.es rest)
    (k : KRel A.x U false K0 K0') : Goal I p H s t := by
  let B := genLoop f.chain l ci.k ci.es g rest
  let cnd : PE := .name (sub g.label 13) (fresh "g" g.label) none
  obtain ⟨ys1, py1, hy1⟩ := seqs_path (I := I) t f' fs' (loopK g.label iv B [] :: seqs n ++ K0') n0
  have st : PyCore.step I { t with stack := { f' with ctrl := .exec [], kont := loopK g.label iv B [] :: seqs n ++ K0' } :: fs' } =
      some { t with stack := { f' with ctrl := .ev cnd, kont := .whileS cnd [tryS g.label iv B] [] :: seqs n ++ K0' } :: fs' } := by
    simp [PyCore.step, PyCore.doneStep, PyCore.top, loopK, cnd]
  obtain ⟨ys2, py2, -, hy2⟩ := cloop_iter (I := I) t f' fs' g.label iv B [] (seqs n ++ K0') hg hr
  have e0 : t = { t with stack := { f' with ctrl := .exec [], kont := seqs n0 ++ (loopK g.label iv B [] :: seqs n ++ K0') } :: fs' } :=
    ct_conf A.ht hc' (by rw [hK']; simp [List.append_assoc]; rfl)
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .call .next [it] [], kont := .cNext ci it g rest :: K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.compLoop, Sem.setC, s1]
  have hH' : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  have py := py1.append (.cons st py2)
  rw [← e0] at py
  refine goal_b (.cons e1 (.nil _)) (by simp) py (by simp)
    (pend_callA ((A.zero.upd (.call .next [it] []) (.cNext ci it g rest :: K0) (.val it)
      (.callA .next :: nextK g.label iv B [] (seqs n ++ K0')) (esub_tail (by simp) (esub_cons hK))).mono_H hH') (.inl rfl) rfl rfl rfl
      (.comp (.cNext (n := n) hC hl hiv hr hg ha (hH' _ hH) f1 f2 hU gp g2 g3 g4 (KRel.ext ⟨hH', Agree.refl _ _ _⟩ k)))) ?_
  intro y hy x hx
  rcases List.mem_append.1 hy with hy | hy
  · have := pfocus_le hx; rw [hy1 y hy] at this; cases this
  rcases List.mem_cons.1 hy with rfl | hy
  · have := pfocus_le hx; simp [PyCore.focus] at this
  · exact .inl (by rw [hy2 y hy x (pfocus_le hx)]; exact hH)

/-- A clause's iterator raises: its `StopIteration` ends the clause's loop (PyCore's handler sets the flag
false), any other exception passes. -/
theorem sig_cNext_raise (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {ci : Sem.CI} {it : Val} {g : Gen}
    {rest : List Gen} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {l : Label} {gs : List Gen}
    {C0 : List Scope} {iv : Name} {n : Nat} (hc : f.ctrl = .raise v) (hc' : f'.ctrl = .raise v)
    (hK : f.kont = .cNext ci it g rest :: K0)
    (hK' : f'.kont = nextK g.label iv (genLoop f.chain l ci.k ci.es g rest) [] (seqs n ++ K0'))
    (hC : f.chain = .comp l ci.k ci.es gs :: C0) (hH : H g.label) (f1 : FOks f.chain g.label ["g", "v", "s"])
    (hU : U g.label) (k : KRel A.x U false K0 K0') : Goal I p H s t := by
  let lg := g.label
  let B := genLoop f.chain l ci.k ci.es g rest
  let ce : PE := .name (sub lg 13) (fresh "g" lg) none
  let Kl : List (PyCore.Kont σ) := .seq [] :: loopK lg iv B [] :: seqs n ++ K0'
  let hb : PS := [.assign (sub lg 21) (fresh "g" lg) (.const (sub lg 22) "$false")]
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise v, kont := .tryE [stopH lg] B :: Kl } :: fs' }
  let c3 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev (.const (sub lg 20) "$stop"), kont := .catchS v (fresh "s" lg) hb [] B :: Kl } :: fs' }
  have hsg : CSig false f.chain U (.raise v : Sem.Ctrl σ) (.raise v) := .inl ⟨v, rfl, rfl⟩
  obtain ⟨ys1, p1, -, hy1⟩ := cpopn (I := I) hsg t f' fs' (.tryE [stopH lg] B :: Kl)
    [.assign (fresh "v" lg), .seq []] (by simp [popOk])
  have e0 := ct_conf A.ht hc' (show f'.kont = [.assign (fresh "v" lg), .seq []] ++ (.tryE [stopH lg] B :: Kl) by
    rw [hK']; rfl)
  rw [← e0] at p1
  have s3 : PyCore.step I c2 = some c3 := by simp [c2, c3, PyCore.step, PyCore.raiseStep, PyCore.top, stopH, hb]
  have hH' : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have hfoc : ∀ y, y = c2 ∨ y = c3 → ∀ x, pfocus y = some x → H (x / 64) := by
    rintro y (rfl | rfl) x hx <;> have hx' := pfocus_le hx
    · simp [c2, PyCore.focus, stopH] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hH
    · simp [c3, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hH
  cases hst : Py.isStop v
  · -- any other exception passes the handler and the clause's loop
    have hst' : PyCore.isStop v = false := by simpa [PyCore.isStop] using hst
    let c4 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .val (.bool false), kont := .catchT v (fresh "s" lg) hb [] B :: Kl } :: fs' }
    let c5 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise v, kont := .tryE [] B :: Kl } :: fs' }
    have s4 : PyCore.step I c3 = some c4 := by
      simp [c3, c4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, hst']
    have s5 : PyCore.step I c4 = some c5 := by simp [c4, c5, PyCore.step, PyCore.valStep, PyCore.top]
    obtain ⟨ys2, p2, -, hy2⟩ := cpopn (I := I) hsg t f' fs' K0' (.tryE [] B :: .seq [] :: loopK lg iv B [] :: seqs n)
      (by simp [popOk, loopK, all_seqs_popOk])
    simp only [List.cons_append] at p2
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise v, kont := K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.raiseStep, Sem.setC, hst]
    refine goal_b (.cons e1 (.nil _)) (by simp) (p1.append (.cons s3 (.cons s4 (.cons s5 p2)))) (by simp)
      (crelI_seen (A.set .raise k (esub_cons hK))) ?_
    intro y hy x hx
    simp only [List.mem_append, List.mem_cons] at hy
    have hx' := pfocus_le hx
    rcases hy with hy | hy | hy | hy | hy
    · rw [hy1 y hy] at hx'; cases hx'
    · exact .inl (hfoc y (.inl hy) x hx)
    · exact .inl (hfoc y (.inr hy) x hx)
    · subst hy; simp [c4, PyCore.focus] at hx'
    · rw [hy2 y hy] at hx'; cases hx'
  · -- `StopIteration`: the handler clears the flag, the clause's `while` ends, its blocks are left
    have hst' : PyCore.isStop v = true := by simpa [PyCore.isStop] using hst
    let c4 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .val (.bool true), kont := .catchT v (fresh "s" lg) hb [] B :: Kl } :: fs' }
    have s4 : PyCore.step I c3 = some c4 := by
      simp [c3, c4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, hst']
    -- the handler's name
    obtain ⟨t5, g5, e5, A5, hg5c, hg5k, -, hp5⟩ := cpstore1 (A.zero.updT (.val (.bool true))
      (.catchT v (fresh "s" lg) hb [] B :: Kl)) (by decide) (f1 "s" (by simp)) v (.exec hb)
      (.handler (fresh "s" lg) v :: Kl)
    have s5 : PyCore.step I c4 = some t5 := by rw [pstep_val rfl rfl]; exact e5
    let Kh : List (PyCore.Kont σ) := .handler (fresh "s" lg) v :: Kl
    let c6 : PyCore.Config σ := { t5 with stack := { g5 with
      ctrl := .ev (.const (sub lg 22) "$false"), kont := .assign (fresh "g" lg) :: .seq [] :: Kh } :: fs' }
    have s6 : PyCore.step I t5 = some c6 := by
      rw [pstep_exec A5.ht (by rw [hg5c])]; simp [PyCore.execStep, PyCore.top, hg5k, c6, Kh]
    let c7 : PyCore.Config σ := { t5 with stack := { g5 with
      ctrl := .val .no, kont := .assign (fresh "g" lg) :: .seq [] :: Kh } :: fs' }
    have s7 : PyCore.step I c6 = some c7 := by
      simp [c6, c7, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
    -- the flag cleared
    obtain ⟨t8, g8, e8, A8, hg8c, hg8k, hr8, hp8⟩ := cpstore1 (A5.updT (.val .no)
      (.assign (fresh "g" lg) :: .seq [] :: Kh)) (by decide) (f1 "g" (by simp)) .no (.exec []) (.seq [] :: Kh)
    have s8 : PyCore.step I c7 = some t8 := by rw [pstep_val rfl rfl]; exact e8
    let c9 : PyCore.Config σ := { t8 with stack := { g8 with ctrl := .exec [], kont := Kh } :: fs' }
    have s9 : PyCore.step I t8 = some c9 := by
      rw [pstep_done A8.ht hg8c]; simp [PyCore.doneStep, hg8k, PyCore.top, c9]
    -- the handler's exit
    obtain ⟨t10, g10, e10, A10, hg10c, hg10k, hp10⟩ :=
      cpunset1 (A8.updT (.exec []) Kh) (by decide) (f1 "s" (by simp)) (.exec []) Kl
    have s10 : PyCore.step I c9 = some t10 := by
      rw [pstep_done rfl rfl]; simp only [PyCore.doneStep, Kh]; exact e10
    let c11 : PyCore.Config σ := { t10 with stack := { g10 with ctrl := .exec [], kont := loopK lg iv B [] :: seqs n ++ K0' } :: fs' }
    have s11 : PyCore.step I t10 = some c11 := by
      rw [pstep_done A10.ht hg10c]; simp [PyCore.doneStep, hg10k, PyCore.top, c11, Kl]
    let c12 : PyCore.Config σ := { t10 with stack := { g10 with
      ctrl := .ev ce, kont := .whileS ce [tryS lg iv B] [] :: seqs n ++ K0' } :: fs' }
    have s12 : PyCore.step I c11 = some c12 := by simp [c11, c12, PyCore.step, PyCore.doneStep, PyCore.top, loopK, ce]
    have hrg : rdOf t10 g10 (fresh "g" lg) = some .no := by
      rw [(hp10 _ (fresh_tag_ne rfl rfl (by decide) lg lg)).1]; exact hr8
    let c13 : PyCore.Config σ := { t10 with stack := { g10 with
      ctrl := .val .no, kont := .whileS ce [tryS lg iv B] [] :: seqs n ++ K0' } :: fs' }
    have s13 : PyCore.step I c12 = some c13 := by
      have r : PyCore.readName I c12 { g10 with ctrl := .ev ce, kont := .whileS ce [tryS lg iv B] [] :: seqs n ++ K0' }
        (fresh "g" lg) none = .ok .no := readName_rd hrg
      simp only [c12, c13, PyCore.step, PyCore.evalStep, ce]; rw [r]; rfl
    let c14 : PyCore.Config σ := { t10 with stack := { g10 with
      ctrl := .val (.bool false), kont := .whileT ce [tryS lg iv B] [] :: seqs n ++ K0' } :: fs' }
    have s14 : PyCore.step I c13 = some c14 := by simp [c13, c14, PyCore.step, PyCore.valStep, PyCore.tst, PyCore.top]
    have s15 : PyCore.step I c14 = some { t10 with stack := { g10 with ctrl := .exec [], kont := seqs n ++ K0' } :: fs' } := by
      simp [c14, PyCore.step, PyCore.valStep, PyCore.top]
    obtain ⟨ys3, p3, hy3⟩ := seqs_path (I := I) t10 g10 fs' K0' n
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.raiseStep, Sem.setC, hst]
    have A15 := ((A10.updT (.exec []) K0').updS (.exec []) K0 (esub_cons hK)).mono_H hH'
    have hag : Agree U A.x.rd A.x.own (rdOf t10 g10) (ownOf t10 g10) := by
      refine agree_but hU fun y hy => ?_
      obtain ⟨a10, b10⟩ := hp10 y (hy "s" (by decide))
      obtain ⟨a8, b8⟩ := hp8 y (hy "g" (by decide))
      obtain ⟨a5, b5⟩ := hp5 y (hy "s" (by decide))
      exact ⟨a10.trans (a8.trans a5), b10.trans (b8.trans b5)⟩
    refine goal_b (.cons e1 (.nil _)) (by simp)
      (p1.append (.cons s3 (.cons s4 (.cons s5 (.cons s6 (.cons s7 (.cons s8 (.cons s9 (.cons s10
        (.cons s11 (.cons s12 (.cons s13 (.cons s14 (.cons s15 p3)))))))))))))) (by simp)
      (.inl (A15.crel (U := U) (i := false) (.exec (goodB_nil _ U) (by simp)) (KRel.ext ⟨hH', hag⟩ k))) ?_
    intro y hy x hx
    have hx' := pfocus_le hx
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy
    · rw [hy1 y hy] at hx'; cases hx'
    · exact .inl (hfoc y (.inl hy) x hx)
    · exact .inl (hfoc y (.inr hy) x hx)
    all_goals first
      | (rw [hy3 y hy] at hx'; cases hx')
      | (subst hy; first
          | (simp [c4, c7, c9, c11, c13, c14, PyCore.focus, A5.ht, A8.ht, A10.ht, hg5c, hg8c, hg10c] at hx'; done)
          | (simp [PyCore.focus, A5.ht, hg5c, hb, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)];
             exact .inl hH)
          | (simp [c6, c12, ce, PyCore.focus, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)];
             exact .inl hH))

end

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The readings of a frame other than the one whose cell `(n, x)` is made. -/
theorem agree_ins {t t1 : PyCore.Config σ} {h : PyCore.Frame σ} {n : Nat} {x : Name} {v : Val}
    (hc : t1.cells = t.cells.insert (n, x) v) (hg : t1.glob = t.glob) (hn : h.id ≠ n) :
    Agree (fun _ => False) (rdOf t h) (ownOf t h) (rdOf t1 h) (ownOf t1 h) :=
  agree_of (P := fun _ => False) (fun _ _ _ _ h => h)
    (rd_same rfl rfl rfl (fun _ y _ => by rw [hg]) (fun y _ => by
      rw [hc, Std.HashMap.getElem?_insert]; simp [Ne.symm hn]) fun _ _ _ => rfl)

theorem initCells_one (cs : Std.HashMap PyCore.Addr Val) (n : Nat) (x : Name) (v : Val) :
    PyCore.initCells cs n [(x, v)] = cs.insert (n, x) v := rfl


/-- PyCore's frame ids after a call pushes a frame with the next id (the caller waiting). -/
theorem ids_push {t t1 : PyCore.Config σ} {f' g' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} (h : Ids t)
    (ht : t.stack = f' :: fs') (ht1 : t1.stack = g' :: { f' with ctrl := .wait } :: fs') (ho : t1.objs = t.objs)
    (hn : t1.next = t.next + 1) (hid : g'.id = t.next) (hk : g'.kind = .fn) : Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have hlt : ∀ g ∈ f' :: fs', g.id < t.next := h2
  refine ⟨?_, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_, fun g hg o hgo => ?_, fun g hg hm => ?_,
    fun o g ho1 => ?_⟩
  · rw [ht1]; simp only [List.map_cons, List.nodup_cons] at h1 ⊢
    refine ⟨?_, h1⟩
    intro hm; simp only [List.mem_cons, List.mem_map] at hm
    rcases hm with e | ⟨g, hg, e⟩
    · have := hlt f' (by simp); omega
    · have := hlt g (by simp [hg]); omega
  · rw [ht1] at hg; rw [hn]; simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · omega
    · have := hlt f' (by simp); exact Nat.lt_succ_of_lt this
    · have := hlt g (by simp [hg]); omega
  · rw [hn]; simp only [pObj, ho] at hb; have := h3 o b hb; omega
  · simp only [pObj, ho] at ho1
    obtain ⟨e, hne⟩ := h4 o g ho1
    have hob := h3 o _ ho1
    refine ⟨e, fun h hh => ?_⟩
    rw [ht1] at hh; simp only [List.mem_cons] at hh
    rcases hh with rfl | rfl | hh
    · omega
    · exact hne f' (by simp)
    · exact hne _ (by simp [hh])
  · rw [ht1] at hg; simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · rw [hk] at hgo; cases hgo
    · exact h5 f' (by simp) o hgo
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1] at hg; simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · rw [hk] at hm; cases hm
    · exact h6 f' (by simp) hm
    · exact h6 _ (by simp [hg]) hm
  · simp only [pObj, ho] at ho1; exact h7 o g ho1


/-- PyCore's frame ids after a generator object with a frame of the next id is made. -/
theorem ids_gen {t t1 : PyCore.Config σ} {f' g' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {c : PyCore.Ctrl σ}
    (h : Ids t) (ht : t.stack = f' :: fs') (ht1 : t1.stack = { f' with ctrl := c } :: fs')
    (ho : t1.objs = t.objs.insert t.next (.gen (.susp g'))) (hn : t1.next = t.next + 1) (hid : g'.id = t.next)
    (hk : g'.kind = .gen t.next) : Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have hlt : ∀ g ∈ f' :: fs', g.id < t.next := h2
  have ho' : ∀ o, t1.objs[o]? = if t.next = o then some (.gen (.susp g')) else t.objs[o]? := by
    intro o; rw [ho, Std.HashMap.getElem?_insert]; simp [beq_iff_eq]
  refine ⟨by rw [ht1]; simpa using h1, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_,
    fun g hg o hgo => ?_, fun g hg hm => ?_, fun o g ho1 => ?_⟩
  · rw [ht1, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | hg
    · have := hlt f' (by simp); exact Nat.lt_succ_of_lt this
    · have := hlt g (by simp [hg]); omega
  · rw [hn]; simp only [pObj, ho'] at hb; split at hb
    · omega
    · have := h3 o b hb; omega
  · simp only [pObj, ho'] at ho1; split at ho1
    · rename_i e; cases ho1; subst e
      refine ⟨hid, fun h hh => ?_⟩
      rw [ht1, List.mem_cons] at hh
      rcases hh with rfl | hh
      · have := hlt f' (by simp); exact Nat.ne_of_lt this
      · have := hlt h (by simp [hh]); exact Nat.ne_of_lt this
    · obtain ⟨e, hne⟩ := h4 o g ho1
      refine ⟨e, fun h hh => ?_⟩
      rw [ht1, List.mem_cons] at hh
      rcases hh with rfl | hh
      · exact hne f' (by simp)
      · exact hne _ (by simp [hh])
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact h5 f' (by simp) o hgo
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact h6 f' (by simp) hm
    · exact h6 _ (by simp [hg]) hm
  · simp only [pObj, ho'] at ho1; split at ho1
    · rename_i e; cases ho1; subst e; exact hk
    · exact h7 o g ho1

end

/-! ## The comprehension's function object called, a generator expression resumed -/

/-- A call of a comprehension's function object (on its first iterable's iterator): the frame of a
list, set or dictionary comprehension up to its accumulator's `display`, or the generator. -/
theorem _root_.Surf.T2.call_comp {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} {args : List Val} {kws : List (Name × Val)}
    (hc : f.ctrl = .call (.fn o) args kws) (hc' : f'.ctrl = .call (.fn o) args kws)
    (hk : KRel A.x U true f.kont f'.kont) {S : Scope} {C : List Scope} {cl κ kd dflt}
    (ho : sObj s o = some (.clo S C cl κ kd dflt)) (hS : S.isComp = true) : GoalB I p H s t := by
  have hob := A.r.objs o
  rw [ho] at hob
  cases hp : pObj t o with
  | none => rw [hp] at hob; exact hob.elim
  | some b =>
  rw [hp] at hob
  simp only [PyCore.OptRel] at hob
  cases hob with
  | @clo _ _ _ cl' _ κ' _ _ sg h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
  cases S with
  | fn => simp [Scope.isComp] at hS
  | lam => simp [Scope.isComp] at hS
  | cl => simp [Scope.isComp] at hS
  | comp l k es gs =>
  cases gs with
  | nil => exact h9.2.2.elim
  | cons g rest =>
  obtain ⟨lg, tg, itg, ifs⟩ := g
  have hsg : sg = none := by cases sg with | none => rfl | some x => exact (h6.2).elim
  subst hsg
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  simp only [sObj] at ho
  simp only [pObj] at hp
  cases args with
  | nil =>
    exact call_raise A hk (Py.err "TypeError")
      (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.setC, ho])
      (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, PyCore.errType, hp, trScope]) hfoc
  | cons it args =>
  cases args with
  | cons a2 args =>
    exact call_raise A hk (Py.err "TypeError")
      (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.setC, ho])
      (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, PyCore.errType, hp, trScope]) hfoc
  | nil =>
  obtain ⟨fi, facc, f1, f2, hne, gT, gGs, gEs, gT1, gGs1, gEs1, gp, g2, g3, gN⟩ := comp_static W h9
  let S := Scope.comp l k es (.mk lg tg itg ifs :: rest)
  let n := t.next
  have hn : t.next = s.next := A.r.next
  have hl : H l := h7
  have hH : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
  let loops := trGs (S :: C) (fresh "i" l) true (.mk lg tg itg ifs :: rest) (compElt l k (trEs (S :: C) es))
  -- the readings of the frames below (their ids are below `n`)
  have hlt : ∀ h ∈ t.stack, h.id ≠ n := fun h hh => Nat.ne_of_lt (A.r.ids.lt h hh)
  by_cases hkg : k = .gen
  · subst hkg
    have e := h10.1
    simp only [trScope, ite_true] at e
    let body : PS := loops
    let fr' : PyCore.Frame σ := { id := n, chain := trScope C S :: trChain C, kind := .gen n, cls := cl', κ := κ',
                                  ns := [], ctrl := .exec loops, kont := [] }
    let tE : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.gen n) } :: fs'
                                         objs := t.objs.insert n (.gen (.susp fr'))
                                         cells := t.cells.insert (n, fresh "i" l) it
                                         next := n + 1 }
    have st1 : PyCore.step I t = some tE := by
      simp only [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, hp, trScope, PyCore.enter, e]
      simp only [tE, fr', initCells_one, n, Option.some.injEq]
      rfl
    let frg : Sem.Frame σ := { id := s.next, chain := S :: C, kind := .gen s.next, cls := cl, κ := κ, ns := [],
                               ctrl := .call .next [it] [], kont := [.cNext ⟨.gen, es, .none⟩ it (.mk lg tg itg ifs) rest] }
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .val (.gen s.next) } :: fs
                                      objs := s.objs.insert s.next (.gen (.susp frg))
                                      next := s.next + 1 }
    have e1 : Sem.step I s = some s1 := by
      simp [Sem.step, A.hs, hc, Sem.callStep, ho, s1, frg, S]
    have hcells : tE.cells = t.cells.insert (n, fresh "i" l) it := rfl
    have hglob : tE.glob = t.glob := rfl
    have hag : ∀ h ∈ t.stack, Agree (fun _ => False) (rdOf t h) (ownOf t h) (rdOf tE h) (ownOf tE h) :=
      fun h hh => agree_ins hcells hglob (hlt h hh)
    have fi' : cl' (fresh "i" l) = .loc := by rw [h2]; exact fi
    have hri : rdAt tE.glob tE.cells fr' (fresh "i" l) = some it := by
      simp [rdAt, fr', fi', tE]
    have hoi : ownAt tE.cells fr' (fresh "i" l) = some it := by
      simp [ownAt, fr', tE]
    have hst := A.r.stack
    rw [A.hs, A.ht] at hst
    have hr : CRel p (Seen (Touch p) H [s]) s1 tE := by
      refine ⟨⟨⟨A.hf.toFRel0.upd _ f.kont _ f'.kont, fun S0 C0 e => hH _ (A.hf.hl S0 C0 e), U, true,
          (by show CR p f.chain U true (.val (.gen s.next)) (.val (.gen t.next)); rw [hn]; exact .val),
          KRel.ext ⟨hH, (hag f' (by simp [A.ht])).mono fun _ h => h.elim⟩ hk⟩,
        all2_agree (all2_mono (fun _ _ h => h.mono_H hH) hst.2) fun h hh => hag h (by rw [A.ht]; simp [hh])⟩,
        fun o => ?_, fun a ha => ?_, A.r.glob, A.r.out, by simp [tE, s1, hn, n], A.r.res, A.r.st, ?_, ?_, ?_⟩
      · show PyCore.OptRel (ORel p (Seen (Touch p) H [s]) tE.glob tE.cells) (s.objs.insert s.next (.gen (.susp frg)))[o]?
          (t.objs.insert n (.gen (.susp fr')))[o]?
        rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
        by_cases ho' : n = o
        · have ho2 : s.next = o := hn ▸ ho'
          simp only [ho', ho2, beq_self_eq_true, ite_true, PyCore.OptRel]
          refine .gen (.special ⟨hn, rfl, h1, h2, by simp [fr', frg, fk, n, hn], trivial, h4, h5, rfl, h10⟩
            (fun S0 C0 e => by cases e; exact hH _ hl) ?_)
          exact .genComp (C0 := C) rfl (hH _ hl) hne gp g2 g3 gN hri hoi f1 f2 gT gGs gEs
        · have ho2 : ¬ s.next = o := hn ▸ ho'
          simp only [beq_iff_eq, ho', ho2, ite_false]
          have := A.r.objs o
          simp only [sObj, pObj] at this
          cases h1o : s.objs[o]? <;> cases h2o : t.objs[o]? <;> rw [h1o, h2o] at this <;>
            simp only [PyCore.OptRel] at this ⊢
          refine (this.mono_H hH).agree fun h' e => agree_ins hcells hglob ?_
          have hs := A.r.ids.susp o h' (by simp [pObj, h2o, e])
          have hb := A.r.ids.obj o _ h2o
          rw [hs.1]; exact Nat.ne_of_lt hb
      · simp only [pCell, sCell]; rw [hcells, Std.HashMap.getElem?_insert]
        have : ¬ ((n, fresh "i" l) == a) = true := by
          intro e; simp only [beq_iff_eq] at e; subst e; exact ha (dot_fresh _ _)
        simp only [this, Bool.false_eq_true, ite_false]; exact A.r.cells a ha
      · intro g hg
        simp only [s1, List.tail_cons] at hg
        exact A.r.wait g (by rw [A.hs]; exact hg)
      · exact ids_gen A.r.ids A.ht rfl rfl rfl rfl rfl
      · have hen := A.r.enter; rw [A.hs] at hen
        exact (hen.ctrl _).ins (insOk_gen _) fun g e => by cases e; exact fun _ _ _ hm => by simp [frg] at hm
    exact goalB_b (.cons e1 (.nil _)) (by simp) (.cons st1 (.nil _)) (by simp) (.inl hr)
      (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)
  · have hkind : (trScope C S).kind = .plain := by rw [h10.1]; simp [hkg]
    let nmacc := "$op:display:" ++ accName k ++ ":"
    let r := sub l 5
    let body : PS := .assign (sub l 4) (fresh "acc" l) (cc l 5 nmacc []) :: (loops ++ [retAcc l])
    have hbody : compWrap l k loops = body := by simp [compWrap, hkg, body, retAcc, nmacc]
    let fr' : PyCore.Frame σ :=
      { id := n, chain := trScope C S :: trChain C, kind := .fn, cls := cl', κ := κ', ns := [], ctrl := .exec body, kont := [] }
    let fw' : PyCore.Frame σ := { f' with ctrl := .wait }
    let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ := fun c kk =>
      { t with stack := { fr' with ctrl := c, kont := kk } :: fw' :: fs'
               cells := t.cells.insert (n, fresh "i" l) it
               next := n + 1 }
    let KA : List (PyCore.Kont σ) := [.assign (fresh "acc" l), .seq (loops ++ [retAcc l])]
    have st1 : PyCore.step I t = some (mk (.exec body) []) := by
      have e := h10.1
      simp only [trScope, hkg, ite_false] at e
      simp only [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, hp, trScope, PyCore.enter, e]
      simp only [mk, fr', fw', initCells_one, n, Option.some.injEq]
      rw [← hbody]; rfl
    have st2 : PyCore.step I (mk (.exec body) []) = some (mk (.ev (cc l 5 nmacc [])) KA) := by
      simp [mk, PyCore.step, PyCore.execStep, PyCore.top, body, KA]
    have st3 : PyCore.step I (mk (.ev (cc l 5 nmacc [])) KA) =
        some (mk (.ev (.const r nmacc)) (.callF (.const r "$args") :: KA)) := by
      simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, cc, ccR, recR, r]
    have st4 : PyCore.step I (mk (.ev (.const r nmacc)) (.callF (.const r "$args") :: KA)) =
        some (mk (.val (Py.constVal I nmacc)) (.callF (.const r "$args") :: KA)) := by
      simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK]
    have st5 : PyCore.step I (mk (.val (Py.constVal I nmacc)) (.callF (.const r "$args") :: KA)) =
        some (mk (.ev (.const r "$args")) (.callA (Py.constVal I nmacc) :: KA)) := by
      simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
    have st6 : PyCore.step I (mk (.ev (.const r "$args")) (.callA (Py.constVal I nmacc) :: KA)) =
        some (mk (.val (.data "$args" [])) (.callA (Py.constVal I nmacc) :: KA)) := by
      simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
    let accD : Py.Disp := match k with | .set => .set [] | .dict => .dict [] | _ => .list []
    have hca : Py.constVal I nmacc = .op (.display accD) := by
      simp only [nmacc]; rw [kc_acc I k]; cases k <;> rfl
    have st7 : PyCore.step I (mk (.val (.data "$args" [])) (.callA (Py.constVal I nmacc) :: KA)) =
        some (mk (.op (.display accD) []) KA) := by
      rw [hca]; simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
    -- Surf's step
    let fr : Sem.Frame σ := { id := s.next, chain := S :: C, kind := .fn, cls := cl, κ := κ, ns := [],
                              ctrl := .op (.display accD) [], kont := [.compStart ⟨k, es, .none⟩ it (.mk lg tg itg ifs) rest] }
    let s1 : Sem.Config σ := { s with stack := fr :: { f with ctrl := .wait } :: fs, next := s.next + 1 }
    have e1 : Sem.step I s = some s1 := by
      simp [Sem.step, A.hs, hc, Sem.callStep, ho, hkg, s1, fr, S]
      cases k <;> rfl
    let tE := mk (.op (.display accD) []) KA
    let frE : PyCore.Frame σ := { fr' with ctrl := .op (.display accD) [], kont := KA }
    have hcells : tE.cells = t.cells.insert (n, fresh "i" l) it := rfl
    have hglob : tE.glob = t.glob := rfl
    have hag : ∀ h ∈ t.stack, Agree (fun _ => False) (rdOf t h) (ownOf t h) (rdOf tE h) (ownOf tE h) :=
      fun h hh => agree_ins hcells hglob (hlt h hh)
    have fi' : cl' (fresh "i" l) = .loc := by rw [h2]; exact fi
    have hri : rdOf tE frE (fresh "i" l) = some it := by
      simp [rdOf, rdAt, frE, fr', fi', tE, mk]
    have hoi : ownOf tE frE (fresh "i" l) = some it := by
      simp [ownOf, ownAt, frE, fr', tE, mk]
    have hst := A.r.stack
    rw [A.hs, A.ht] at hst
    have hr : CRel p (Seen (Touch p) H [s]) s1 tE := by
      refine ⟨⟨⟨⟨hn, rfl, h1, h2, rfl, trivial, h4, h5, rfl, h10⟩, fun S0 C0 e => ?_, Rm UAll l, true, .op, ?_⟩,
        ⟨A.hf.toFRel0.upd .wait f.kont .wait f'.kont, fun S0 C0 e => hH _ (A.hf.hl S0 C0 e), U, true, .wait,
          KRel.ext ⟨hH, (hag f' (by simp [A.ht])).mono fun _ h => h.elim⟩ hk⟩,
        all2_agree (all2_mono (fun _ _ h => h.mono_H hH) hst.2) fun h hh => hag h (by rw [A.ht]; simp [hh])⟩,
        fun o => ?_, fun a ha => ?_, A.r.glob, A.r.out, by simp [tE, mk, s1, hn, n], A.r.res, A.r.st, ?_, ?_, ?_⟩
      · cases e; exact hH _ hl
      · exact .comp (.compStart (U := UAll) (gs := .mk lg tg itg ifs :: rest) (C0 := C) rfl hkg rfl (hH _ hl) trivial
          hoi hri (facc hkg) f1 f2 gT1 gGs1 gEs1 hne gp g2 g3 gN)
      · have := A.r.objs o
        show PyCore.OptRel (ORel p (Seen (Touch p) H [s]) tE.glob tE.cells) s.objs[o]? t.objs[o]?
        simp only [sObj, pObj] at this
        cases h1o : s.objs[o]? <;> cases h2o : t.objs[o]? <;> rw [h1o, h2o] at this <;>
          simp only [PyCore.OptRel] at this ⊢
        refine (this.mono_H hH).agree fun h' e => agree_ins hcells hglob ?_
        have hs := A.r.ids.susp o h' (by simp [pObj, h2o, e])
        have hb := A.r.ids.obj o _ h2o
        rw [hs.1]; exact Nat.ne_of_lt hb
      · simp only [pCell, sCell]; rw [hcells, Std.HashMap.getElem?_insert]
        have : ¬ ((n, fresh "i" l) == a) = true := by
          intro e; simp only [beq_iff_eq] at e; subst e; exact ha (dot_fresh _ _)
        simp only [this, Bool.false_eq_true, ite_false]; exact A.r.cells a ha
      · intro g hg
        simp only [s1, List.tail_cons, List.mem_cons] at hg
        rcases hg with rfl | hg
        · rfl
        · exact A.r.wait g (by rw [A.hs]; exact hg)
      · exact ids_push A.r.ids A.ht rfl rfl rfl rfl rfl
      · have hen := A.r.enter; rw [A.hs] at hen
        refine ⟨fun g hg => ?_, hen.2⟩
        simp only [s1, List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · exact fun _ _ _ hm => by simp [fr] at hm
        · exact hen.1 f List.mem_cons_self
        · exact hen.1 g (List.mem_cons_of_mem _ hg)
    refine goalB_b (.cons e1 (.nil _)) (by simp)
      (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 (.nil _)))))))) (by simp) (.inl hr) ?_
    intro y hy x hx
    have hx' := pfocus_le hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    refine .inl ?_
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc'] at hx'
    · simp [mk, PyCore.focus, body, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [mk, PyCore.focus, cc, ccR, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [mk, PyCore.focus, r, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [mk, PyCore.focus] at hx'
    · simp [mk, PyCore.focus, r, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [mk, PyCore.focus] at hx'


/-- `next` of a generator expression not yet run: PyCore runs its loops' start up to the first
iterator's `next`, as Surf's suspended frame starts with. -/
theorem _root_.Surf.T2.resume_genComp {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} (hc : f.ctrl = .call .next [.gen o] [])
    (hc' : f'.ctrl = .call .next [.gen o] []) (hk : KRel A.x U true f.kont f'.kont)
    {g : Sem.Frame σ} {g' : PyCore.Frame σ} (ho : sObj s o = some (.gen (.susp g)))
    (ho' : pObj t o = some (.gen (.susp g'))) (h0 : FRel0 g g') (hl : ∀ S C, g.chain = S :: C → H S.label)
    {l es gr rest C0 it} (hC : g.chain = .comp l .gen es (gr :: rest) :: C0)
    (hg : g.ctrl = .call .next [it] []) (hgk : g.kont = [.cNext ⟨.gen, es, .none⟩ it gr rest])
    (hg' : g'.ctrl = .exec (trGs g.chain (fresh "i" l) true (gr :: rest) (compElt l .gen (trEs g.chain es))))
    (hgk' : g'.kont = [])
    (hs : Special (cx p H (rdOf t g') (ownOf t g') g) g.ctrl g.kont g'.ctrl g'.kont) : GoalB I p H s t := by
  generalize ec : g.ctrl = c at hs
  generalize ek : g.kont = kk at hs
  generalize ec' : g'.ctrl = c' at hs
  generalize ek' : g'.kont = kk' at hs
  cases hs with
  | genFn hC1 => simp only [hC] at hC1; cases hC1
  | genLam hC1 => simp only [hC] at hC1; cases hC1
  | yf => rw [hg] at ec; cases ec
  | genComp hC1 hH1 hne gp g2 g3 gN hri hoi f1 f2 gT gGs gEs =>
  simp only [hC, List.cons.injEq, Scope.comp.injEq] at hC1
  obtain ⟨⟨rfl, -, rfl, rfl, rfl⟩, rfl⟩ := hC1
  rw [hg] at ec; cases ec
  obtain ⟨lg, tg, itg, ifs⟩ := gr
  have A1 := A.zero.push ho' h0 hl f.kont f'.kont hk ho
  have e1 : Sem.step I s =
      some { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) } := by
    simp only [sObj] at ho
    simp [Sem.step, A.hs, hc, Sem.callStep, ho]
  have e2 : PyCore.step I t =
      some { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) } := by
    simp only [pObj] at ho'
    simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, ho']
  let s1 : Sem.Config σ := { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) }
  let t1 : PyCore.Config σ := { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) }
  let fws : List (PyCore.Frame σ) := { f' with ctrl := .wait, kont := f'.kont } :: fs'
  let iv := fresh "i" l
  let B := genLoop g.chain l .gen es (.mk lg tg itg ifs) rest
  let cnd : PE := .name (sub lg 13) (fresh "g" lg) none
  let W0 : PyCore.Stmt := .while (sub lg 12) cnd [tryS lg iv B] []
  let A0 : PyCore.Stmt := .assign (sub lg 10) (fresh "g" lg) (.const (sub lg 11) "$true")
  have hex : g'.ctrl = .exec [A0, W0] := by rw [hg']; rfl
  let mk1 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c kk => { t1 with stack := { g' with ctrl := c, kont := kk } :: fws }
  have st2 : PyCore.step I t1 = some (mk1 (.ev (.const (sub lg 11) "$true")) [.assign (fresh "g" lg), .seq [W0]]) := by
    rw [pstep_exec A1.ht hex]; simp [PyCore.execStep, hgk', mk1, A0, PyCore.top, t1, fws]
  have st3 : PyCore.step I (mk1 (.ev (.const (sub lg 11) "$true")) [.assign (fresh "g" lg), .seq [W0]]) =
      some (mk1 (.val (.bool true)) [.assign (fresh "g" lg), .seq [W0]]) := by
    simp [mk1, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
  obtain ⟨t4, g4, e4, A4, hgc4, hgk4, hrg, hs4⟩ := cpstore1 (A1.updT (.val (.bool true))
    [.assign (fresh "g" lg), .seq [W0]]) (tag := "g") (l := lg) (by decide) (f1 "g" (by simp)) (.bool true) (.exec [])
    [.seq [W0]]
  have st4 : PyCore.step I (mk1 (.val (.bool true)) [.assign (fresh "g" lg), .seq [W0]]) = some t4 := by
    rw [pstep_val rfl rfl]; simp only [PyCore.valStep]; exact e4
  let mk4 : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c kk => { t4 with stack := { g4 with ctrl := c, kont := kk } :: fws }
  have st5 : PyCore.step I t4 = some (mk4 (.exec [W0]) []) := by
    rw [pstep_done A4.ht hgc4]; simp only [PyCore.doneStep, hgk4]; rfl
  have st6 : PyCore.step I (mk4 (.exec [W0]) []) =
      some (mk4 (.ev cnd) (.whileS cnd [tryS lg iv B] [] :: [.seq []])) := by
    simp [mk4, PyCore.step, PyCore.execStep, PyCore.top, W0]
  have hr1 : rdOf t1 g' iv = some it := hri
  have hri4 : rdOf t4 g4 iv = some it := by
    rw [(hs4 _ (fresh_tag_ne rfl rfl (by decide) l lg)).1]; exact hr1
  obtain ⟨ys2, py2, -, hy2⟩ := cloop_iter (I := I) t4 g4 fws lg iv B [] [.seq []] hrg hri4
  have hT1 : Touch p s1 lg := .inr (by simp [s1, TouchF, hg, hgk, Gen.label])
  have hH' : ∀ l', H l' → Seen (Touch p) H [s1, s] l' := fun _ h => .inl h
  have AA : At0 p (Seen (Touch p) H [s1, s]) s1
      { t4 with stack := { g4 with ctrl := .val it, kont := .callA .next :: nextK lg iv B [] (seqs 1 ++ []) } :: fws }
      g ({ f with ctrl := .wait, kont := f.kont } :: fs) { g4 with ctrl := .val it, kont := .callA .next :: nextK lg iv B [] (seqs 1 ++ []) } fws :=
    ((A4.updT (.val it) (.callA .next :: nextK lg iv B [] (seqs 1 ++ []))).mono_H hH')
  have hk1 : KRel (cx p (Seen (Touch p) H [s1, s]) (rdOf t4 g4) (ownOf t4 g4) g) (Rm (Rm UAll l) lg) true g.kont
      (nextK lg iv B [] (seqs 1 ++ [])) := by
    rw [hgk]
    exact .comp (.cNext (U := Rm UAll l) (K := []) (K' := []) (l := l) (ci := ⟨.gen, es, .none⟩) (it := it)
        (g := .mk lg tg itg ifs) (rest := rest) (iv := iv) (n := 1) (gs := .mk lg tg itg ifs :: rest) (C0 := C0) hC
        (rm_self UAll l) (.inl rfl) hri4 hrg (fun h => (h rfl).elim)
        (show Seen (Touch p) H [s1, s] lg from .inr ⟨s1, List.mem_cons_self, hT1⟩) f1 f2 ⟨trivial, hne⟩ gp g2 g3 gN .nil)
  have py := Path.cons e2 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 py2)))))
  refine goalB_t (.cons e1 (.nil _)) (by simp) py (by simp) (pend_callA AA (.inl rfl) hg rfl rfl hk1) ?_
  have hl' : ∀ k, k < 64 → Seen (Touch p) H [s1, s] (sub lg k / 64) := fun k hk =>
    .inr ⟨s1, List.mem_cons_self, by rw [sub_div _ _ hk]; exact hT1⟩
  intro y hy x hx
  have hx' := pfocus_le hx
  simp only [List.mem_cons] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | hy
  · simp [PyCore.focus, A.ht, hc'] at hx'
  · simp [PyCore.focus, t1, hex, A0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 10 (by omega)
  · simp [mk1, PyCore.focus, PyCore.Expr.label] at hx'; subst hx'; exact hl' 11 (by omega)
  · simp [mk1, PyCore.focus] at hx'
  · simp [PyCore.focus, A4.ht, hgc4] at hx'
  · simp [mk4, PyCore.focus, W0, PyCore.Stmt.label] at hx'; subst hx'; exact hl' 12 (by omega)
  · rw [hy2 y hy x hx']; exact .inr ⟨s1, List.mem_cons_self, hT1⟩


/-! ## The dispatch on the items -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem _root_.Surf.T2.val_comp : KCase I p true CompK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  have hf0 := focus_val A.ht hc'
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @compIt _ K0 K0' o k =>
    exact at_go12 A (c := .op .iter [v]) (c' := .op .iter [v]) (k := .compCall (.fn o) :: K0)
      (k' := .callA (.fn o) :: K0')
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC])
      (pstep_rec A.ht hc' (by rw [hK']; rfl))
      (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top]) hf0 (by simp [PyCore.focus])
      .op (.comp (.compCall k))
  | @compCall _ K0 K0' o k =>
    -- C2: that `o` is a comprehension's function object is no fact of the item (`Cx` sees no objects)
    exact val_compCall A hc hc' hK hK' k
  | @compStart U0 l ci it g rest gs C0 hC hk0 ha0 hH0 hU ho hr fa f1 f2 g1 _ _ _ gp g2 g3 g4 =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact val_compStart A hc hc' hK hK' hC hU hr fa f1 f2 g1.1 gp g2 g3 g4
  | @cNext U0 K0 K0' l ci it g rest gs C0 iv n hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 g4 k =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact val_cNext A W hc hc' hK hK' hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 k gp.2.2 g4
  | @cCond _ K0 K0' l lg ci ifs rest gs C0 j hC hl hlg ha f1 g1 g2 g3 hN k =>
    exact val_tst A (v := v) (by simp [Sem.step, A.hs, hc, hK, Sem.valStep])
      (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK', List.cons_append])
      (.comp (.cCondT (j := j) hC hl hlg ha f1 g1 g2 g3 hN k)) hf0
  | @cCondT _ K0 K0' l lg ci ifs rest gs C0 j hC hl hlg ha f1 g1 g2 g3 hN k =>
    cases v
    case bool b =>
      cases b
      · -- the condition is false: the clause's next item
        obtain ⟨ys, py, hy⟩ := seqs_path (I := I) t f' fs' K0' (j + 1)
        have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec [], kont := seqs (j + 1) ++ K0' } :: fs' } := by
          rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; rfl
        exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]) (.nil _)) (by simp)
          (.cons e2 py) (by simp) (crelI_seen (A.set (U := U) (.exec (goodB_nil _ U) (by simp)) k))
          (cover_none (by intro y hy'; rcases List.mem_cons.1 hy' with rfl | hy'; exact hf0; exact hy y hy'))
      · -- the condition is true: Surf's `cConds`, PyCore's clause body
        have hH' : ∀ l', H l' → Seen (Touch p) H [s] l' := fun _ h => .inl h
        have es : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := .cConds ci ifs rest :: K0 } :: fs } := by
          simp [Sem.step, A.hs, hc, Sem.valStep, hK, Sem.setC]
        let gb := genBody f.chain l ci.k ci.es lg ifs rest
        have st : PyCore.step I t = some { t with stack := { f' with ctrl := .exec gb, kont := seqs (j + 1) ++ K0' } :: fs' } := by
          rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; rfl
        exact SimStep.pre es (.cons st (.nil _)) (by simp) (cover_none (by simp [hf0]))
          (conds_go ((A.zero.upd _ _ _ _).mono_H hH') rfl rfl rfl rfl (.nil _) (by simp) hC hl (hH' _ hlg) ha f1 g1 g2 g3
            hN (KRel.ext ⟨hH', Agree.refl _ _ _⟩ k))
    all_goals
      exact fin_stuck (I := I) A (by simp [Sem.step, A.hs, hc, hK, Sem.valStep])
        (by rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK']) (cov_none A hf0)
  | @cIter _ K0 K0' l ci rest gs C0 m g hC hl ha hH hU f1 f2 gp g2 g3 g4 k =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact val_cIter A hc hc' hK hK' hC hl ha hH f1 f2 hU gp g2 g3 g4 k
  | @cIt _ K0 K0' l ci rest gs C0 m g hC hl ha hH hU f1 f2 gp g2 g3 g4 k =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact val_cIt A W hc hc' hK hK' hC hl ha hH hU f1 f2 gp g2 g3 g4 k
  | @cExpr _ K0 K0' m k => exact val_cExpr A hc hc' hK hK' k
  | @cElt _ K0 K0' ck acc m k =>
    exact at_go12 A (c := .op (.accum ck) [acc, v]) (c' := .op (.accum ck) [acc, v]) (k := .exprS :: K0)
      (k' := .exprS :: seqs (m + 1) ++ K0')
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC])
      (pstep_rec A.ht hc' (by rw [hK']; rfl))
      (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top]) hf0 (by simp [PyCore.focus])
      .op (.comp (.cExpr k))
  | @cVal _ K0 K0' acc kv m k =>
    exact at_go12 A (c := .op (.accum .dict) [acc, kv, v]) (c' := .op (.accum .dict) [acc, kv, v]) (k := .exprS :: K0)
      (k' := .exprS :: seqs (m + 1) ++ K0')
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.doOp, Sem.setC])
      (pstep_rec A.ht hc' (by rw [hK']; rfl))
      (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top]) hf0 (by simp [PyCore.focus])
      .op (.comp (.cExpr k))
  | @cKey _ K0 K0' acc e m hg k =>
    exact at_go12 A (c := .ev e) (c' := .ev (trE f.chain e)) (k := .cVal acc v :: K0)
      (k' := recK [acc, v] [] (.callA (.op (.accum .dict)) :: .exprS :: seqs (m + 1) ++ K0'))
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC])
      (pstep_rec A.ht hc' (by rw [hK']; rfl))
      (by simp [PyCore.step, PyCore.valStep, PyCore.top, recK]) hf0 (by simp [PyCore.focus])
      (.ev hg) (.comp (.cVal k))

theorem _root_.Surf.T2.done_comp : KCase I p false CompK CDone := by
  intro H s t f fs f' fs' U A W ⟨hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @cAcc U0 l ck es gs C0 acc hC hr =>
    -- the loops ended: the accumulator is returned
    have hl : H l := A.hf.hl _ _ hC
    let g1 : PyCore.Frame σ := { f' with ctrl := .exec [retAcc l], kont := [] }
    let g2 : PyCore.Frame σ := { f' with ctrl := .ev (nm l 6 (fresh "acc" l)), kont := [.retS, .seq []] }
    let g3 : PyCore.Frame σ := { f' with ctrl := .val acc, kont := [.retS, .seq []] }
    have st1 : PyCore.step I t = some { t with stack := g1 :: fs' } := by
      rw [pstep_done A.ht hc']; simp [PyCore.doneStep, hK', PyCore.top, g1]
    have st2 : PyCore.step I { t with stack := g1 :: fs' } = some { t with stack := g2 :: fs' } := by
      simp [PyCore.step, g1, g2, retAcc, PyCore.execStep, PyCore.top]
    have st3 : PyCore.step I { t with stack := g2 :: fs' } = some { t with stack := g3 :: fs' } := by
      rw [pstep_ev (e := nm l 6 (fresh "acc" l)) rfl rfl]
      show PyCore.top _ fs' { g2 with ctrl := PyCore.resCtrl _ (PyCore.readName I _ g2 (fresh "acc" l) none) } = _
      rw [readName_rd (t := { t with stack := g2 :: fs' }) (f' := g2) hr]; rfl
    have st4 : PyCore.step I { t with stack := g3 :: fs' } =
        some { t with stack := { f' with ctrl := .retv acc, kont := [.seq []] } :: fs' } := by
      simp [PyCore.step, g3, PyCore.valStep, PyCore.top]
    refine goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]) (.nil _)) (by simp)
      (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.nil _))))) (by simp)
      (crelI_seen (A.set (U := Rm U0 l) (i := false) .retv (.core .seqNil))) ?_
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have hx' := pfocus_le hx
    refine .inl ?_
    rcases hy with rfl | rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc'] at hx'
    · simp [PyCore.focus, g1, retAcc, PyCore.Stmt.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [PyCore.focus, g2, nm, PyCore.Expr.label] at hx'; rw [← hx', sub_div _ _ (by omega)]; exact hl
    · simp [PyCore.focus, g3] at hx'
  | @cLoop U0 K0 K0' l ci it g rest gs C0 iv n0 n hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 g4 k =>
    exact done_cLoop A W hc hc' hK hK' hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 g4 k
  | @cConds _ K0 K0' l lg ci ifs rest gs C0 hC hl hlg ha f2 g1 g2 g3 hN k =>
    let gb := genBody f.chain l ci.k ci.es lg ifs rest
    have st : PyCore.step I t = some { t with stack := { f' with ctrl := .exec gb, kont := K0' } :: fs' } := by
      rw [pstep_done A.ht hc']; simp only [PyCore.doneStep, hK']; rfl
    exact conds_go (A.zero.updT _ K0') hc hK rfl (show K0' = seqs 0 ++ K0' from rfl) (.cons st (.nil _))
      (by simp [PyCore.focus, A.ht, hc']) hC hl hlg ha f2 g1 g2 g3 hN k

set_option hygiene false in
/-- `P.all (popOk f'.ctrl)` for a signal `hf`. -/
macro "cpk" : tactic => `(tactic| (rcases hf with ⟨v, -, h2⟩ | ⟨v, -, h2⟩ | ⟨hi, -, -, h2⟩ | ⟨hi, -, -, h2⟩ <;>
  rw [h2] <;> simp [popOk, all_seqs_popOk]))

theorem _root_.Surf.T2.sig_comp {i : Bool} : KCase I p i CompK CSig := by
  intro H s t f fs f' fs' U A W hc hk
  have hf := hc
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  have nc : ∀ {l k es gs C0}, f.chain = .comp l k es gs :: C0 → ¬ NoCompH f.chain := fun h hn => by
    rw [h] at hn; simp [NoCompH, Scope.isComp] at hn
  cases hk with
  | @compIt _ K0 K0' o k =>
    exact csig_popn A hc (by simp) [.binR "," (.data "$args" []), .callA (.op .iter), .callA (.fn o)] (by simp)
      (by cpk) hK' k (by sige)
  | @compCall _ K0 K0' o k =>
    exact csig_popn A hc (by simp) [.callA (.fn o)] (by simp) (by cpk) hK' k (by sige)
  | @compStart U0 l ci it g rest gs C0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact csig_popn A hc (by simp) [.assign (fresh "acc" l), .seq (trGs f.chain (fresh "i" l) true (g :: rest)
        (compElt l ci.k (trEs f.chain ci.es)) ++ [retAcc l])] (by simp) (by cpk) hK' (.nil (U := U0)) (by sige)
  | @cAcc U0 l ck es gs C0 acc hC hr =>
    exact csig_popn A hc (by simp) [.seq [retAcc l]] (by simp) (by cpk) hK' (.nil (U := U0)) (by sige)
  | @cNext U0 K0 K0' l ci it g rest gs C0 iv n hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 g4 k =>
    rcases hf with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩
    · exact sig_cNext_raise A h1 h2 hK hK' hC hH f1 hU k
    · exact csig_popn A hc (by simp) (nextK g.label iv (genLoop f.chain l ci.k ci.es g rest) [] (seqs n)) (by simp [nextK])
        (by rw [h2]; simp [nextK, popOk, loopK, all_seqs_popOk]) (by rw [hK']; simp [nextK]) k
        (by simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC])
    all_goals exact (nc hC hn).elim
  | @cLoop U0 K0 K0' l ci it g rest gs C0 iv n0 n hC hl hiv hr hg ha hH f1 f2 hU gp g2 g3 g4 k =>
    rcases hf with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩
    · exact csig_popn A hc (by simp) (seqs n0 ++ loopK g.label iv (genLoop f.chain l ci.k ci.es g rest) [] :: seqs n)
        (by simp) (by rw [h2]; simp [popOk, loopK, all_seqs_popOk]) hK' k (by sige)
    · exact csig_popn A hc (by simp) (seqs n0 ++ loopK g.label iv (genLoop f.chain l ci.k ci.es g rest) [] :: seqs n)
        (by simp) (by rw [h2]; simp [popOk, loopK, all_seqs_popOk]) hK' k (by sige)
    all_goals exact (nc hC hn).elim
  | @cConds _ K0 K0' l lg ci ifs rest gs C0 hC hl hlg ha f2 g1 g2 g3 hN k =>
    exact csig_popn A hc (by simp) [.seq (genBody f.chain l ci.k ci.es lg ifs rest)] (by simp) (by cpk)
      hK' k (by sige)
  | @cCond _ K0 K0' l lg ci ifs rest gs C0 j hC hl hlg ha f2 g1 g2 g3 hN k =>
    exact csig_popn A hc (by simp) (.ifS (genBody f.chain l ci.k ci.es lg ifs rest) [] :: seqs (j + 1)) (by simp)
      (by cpk) hK' k (by sige)
  | @cCondT _ K0 K0' l lg ci ifs rest gs C0 j hC hl hlg ha f2 g1 g2 g3 hN k =>
    exact csig_popn A hc (by simp) (.ifT (genBody f.chain l ci.k ci.es lg ifs rest) [] :: seqs (j + 1)) (by simp)
      (by cpk) hK' k (by sige)
  | @cIter _ K0 K0' l ci rest gs C0 m g hC hl ha hH hU f1 f2 gp g2 g3 g4 k =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact csig_popn A hc (by simp) (.binR "," (.data "$args" []) :: .callA (.op .iter) :: .assign (fresh "j" lg) ::
        .seq (forLoop lg (fresh "j" lg) (trT f.chain (forSrc lg) tg (trE f.chain tg)) (genBody f.chain l ci.k ci.es lg ifs rest) []) :: seqs m)
      (by simp)
      (by cpk) hK' k (by sige)
  | @cIt _ K0 K0' l ci rest gs C0 m g hC hl ha hH hU f1 f2 gp g2 g3 g4 k =>
    obtain ⟨lg, tg, itg, ifs⟩ := g
    exact csig_popn A hc (by simp) (.assign (fresh "j" lg) ::
        .seq (forLoop lg (fresh "j" lg) (trT f.chain (forSrc lg) tg (trE f.chain tg)) (genBody f.chain l ci.k ci.es lg ifs rest) []) :: seqs m)
      (by simp)
      (by cpk) hK' k (by sige)
  | @cExpr _ K0 K0' m k =>
    exact csig_popn A hc (by simp) (.exprS :: seqs m) (by simp) (by cpk) hK' k (by sige)
  | @cElt _ K0 K0' ck acc m k =>
    exact csig_popn A hc (by simp) (.binR "," (.data "$args" [acc]) :: .callA (.op (.accum ck)) :: .exprS :: seqs (m + 1))
      (by simp) (by cpk) hK' k (by sige)
  | @cKey _ K0 K0' acc e m hg k =>
    exact csig_popn A hc (by simp) (.binR "," (.data "$args" [acc]) :: .binL "," (trE f.chain e) ::
        .callA (.op (.accum .dict)) :: .exprS :: seqs (m + 1)) (by simp) (by cpk) hK' k (by sige)
  | @cVal _ K0 K0' acc kv m k =>
    exact csig_popn A hc (by simp) (.binR "," (.data "$args" [acc, kv]) :: .callA (.op (.accum .dict)) :: .exprS ::
        seqs (m + 1)) (by simp) (by cpk) hK' k (by sige)

end

end Comp

end Surf.T2
