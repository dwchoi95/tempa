/-
The relation c ~ d of Definition A.1, and the invariant `good` that carries what
part (1), (2) and (3) of the footprint say about the nodes a frame still holds.
-/
import PyCore.Semantics

namespace PyCore

def All2 {α β} (r : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b ∧ All2 r as bs
  | _, _ => False

def OptRel {α β} (r : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => r a b
  | none, none => True
  | _, _ => False

section
variable {σ : Type} (R : Edit) (F : Label → Prop)

def sameKind (S : Scope) : Prop := (editSc R S).kind = S.kind

/-- Every scope of the chain keeps its kind in `q`. -/
def ChainKinds (C : List Scope) : Prop := ∀ S ∈ C, sameKind R S

mutual
/-- Every node of the expression is in `F` or: is no site, has its name
occurrences classified alike in `p` and `q` (in its scope and every enclosing
one), and keeps its kind if it is a function. Nodes under a node in `F` are not
constrained. -/
def goodE (C : List Scope) : Expr → Prop
  | .const l _ => F l ∨ R.e l = none
  | .name l x _ => F l ∨ (R.e l = none ∧ alike R C x = true)
  | .bin l _ a b | .call l a b | .bool l _ a b =>
    F l ∨ (R.e l = none ∧ goodE C a ∧ goodE C b)
  | .lam l k x b =>
    F l ∨ (R.e l = none ∧ sameKind R (.fn l k x b) ∧ goodB (.fn l k x b :: C) b)
  | .walrus l x e => F l ∨ (R.e l = none ∧ alike R C x = true ∧ goodE C e)
  | .yield l e | .yieldFrom l e => F l ∨ (R.e l = none ∧ goodE C e)
  | .cond l c a b => F l ∨ (R.e l = none ∧ goodE C c ∧ goodE C a ∧ goodE C b)
def goodS (C : List Scope) : Stmt → Prop
  | .assign l x e => F l ∨ (R.s l = none ∧ alike R C x = true ∧ goodE C e)
  | .del l x => F l ∨ (R.s l = none ∧ alike R C x = true)
  | .expr l e | .ret l e | .raise l e | .print l e => F l ∨ (R.s l = none ∧ goodE C e)
  | .ite l c t u | .while l c t u => F l ∨ (R.s l = none ∧ goodE C c ∧ goodB C t ∧ goodB C u)
  | .defn l f x b =>
    F l ∨ (R.s l = none ∧ alike R C f = true ∧ sameKind R (.fn l false x b) ∧
      goodB (.fn l false x b :: C) b)
  | .cls l x _ b =>
    F l ∨ (R.s l = none ∧ alike R C x = true ∧
      (∀ y ∈ classImplicit, alike R (.cl l b :: C) y = true) ∧ goodB (.cl l b :: C) b)
  | .glob l _ | .nonloc l _ | .brk l | .cont l => F l ∨ R.s l = none
  | .tryE l b hs u => F l ∨ (R.s l = none ∧ goodB C b ∧ goodHs C hs ∧ goodB C u)
/-- Each handler clause is in `F` or: is no site, keeps its name's classification,
and has good parts. -/
def goodHs (C : List Scope) : List Handler → Prop
  | [] => True
  | .mk lh h x hb :: hs =>
    (F lh ∨ (R.h lh = none ∧ alike R C x = true ∧ goodE C h ∧ goodB C hb)) ∧ goodHs C hs
def goodB (C : List Scope) : List Stmt → Prop
  | [] => True
  | s :: ss => goodS C s ∧ goodB C ss
end

/-- A closure's code is good in its own scope. -/
def goodScope (C : List Scope) : Scope → Prop
  | .fn _ _ _ b => goodB R F C b
  | .cl _ _ => True

def goodCtrl (C : List Scope) : Ctrl σ → Prop
  | .ev e => goodE R F C e
  | .exec ss => goodB R F C ss
  | _ => True

def goodK (C : List Scope) : Kont σ → Prop
  | .binL _ b | .callF b | .boolK _ b | .boolT _ _ b => goodE R F C b
  | .walrus x | .assign x | .handler x _ => alike R C x = true
  | .ifS t u | .ifT t u => goodB R F C t ∧ goodB R F C u
  | .whileS e b u | .whileT e b u | .loop e b u => goodE R F C e ∧ goodB R F C b ∧ goodB R F C u
  | .seq ss => goodB R F C ss
  | .tryE hs u => goodHs R F C hs ∧ goodB R F C u
  | .catchS _ x hb hs u | .catchT _ x hb hs u =>
    alike R C x = true ∧ goodB R F C hb ∧ goodHs R F C hs ∧ goodB R F C u
  | .condK a b | .condT a b => goodE R F C a ∧ goodE R F C b
  | _ => True

def goodFrame (f : Frame σ) : Prop :=
  goodCtrl R F f.chain f.ctrl ∧ ∀ k ∈ f.kont, goodK R F f.chain k

/-! ## Editing a frame's syntax -/

def editCtrl : Ctrl σ → Ctrl σ
  | .ev e => .ev (editE R e)
  | .exec ss => .exec (editB R ss)
  | c => c

def editK : Kont σ → Kont σ
  | .binL op b => .binL op (editE R b)
  | .callF a => .callF (editE R a)
  | .ifS t u => .ifS (editB R t) (editB R u)
  | .ifT t u => .ifT (editB R t) (editB R u)
  | .whileS e b u => .whileS (editE R e) (editB R b) (editB R u)
  | .whileT e b u => .whileT (editE R e) (editB R b) (editB R u)
  | .loop e b u => .loop (editE R e) (editB R b) (editB R u)
  | .seq ss => .seq (editB R ss)
  | .tryE hs u => .tryE (editHs R hs) (editB R u)
  | .catchS v x hb hs u => .catchS v x (editB R hb) (editHs R hs) (editB R u)
  | .catchT v x hb hs u => .catchT v x (editB R hb) (editHs R hs) (editB R u)
  | .condK a b => .condK (editE R a) (editE R b)
  | .condT a b => .condT (editE R a) (editE R b)
  | .boolK o b => .boolK o (editE R b)
  | .boolT o v b => .boolT o v (editE R b)
  | k => k

/-- (a) of Definition A.1 for one pair of frames: corresponding scope and
program point (q's is the edit of p's), equal pending values, the same cached
classification and cells for names classified alike in the frame's scope and those
enclosing it, and the same class namespace. Cells are addressed by frame and name, so β is the
identity and needs no separate statement. -/
structure FrameRel (f g : Frame σ) : Prop where
  id : g.id = f.id
  kind : g.kind = f.kind
  chain : g.chain = f.chain.map (editSc R)
  cls : ∀ x, alike R f.chain x = true → g.cls x = f.cls x
  kinds : ChainKinds R f.chain
  ns : g.ns = f.ns
  ctrl : g.ctrl = editCtrl R f.ctrl
  kont : g.kont = f.kont.map (editK R)
  κ : ∀ x, alike R f.chain x = true → g.κ x = f.κ x
  good : goodFrame R F f

def GRel : GSt σ → GSt σ → Prop
  | .susp f, .susp g => FrameRel R F f g
  | .running, .running => True
  | .done, .done => True
  | _, _ => False

/-- (b): related heap objects. -/
def ObjRel : Option (Obj σ) → Option (Obj σ) → Prop
  | none, none => True
  | some (.clo S C cl κ sg), some (.clo S' C' cl' κ' sg') =>
    S' = editSc R S ∧ C' = C.map (editSc R) ∧
    (∀ x, alike R (S :: C) x = true → cl' x = cl x) ∧
    (∀ x, alike R (S :: C) x = true → κ' x = κ x) ∧ sg' = sg ∧ sameKind R S ∧ ChainKinds R C ∧
    goodScope R F (S :: C) S
  | some (.gen st), some (.gen st') => GRel R F st st'
  | _, _ => False

/-- c ~ d: related stacks and heaps, and the same cells, module dictionary,
output, counter, result, and interpretation state. -/
structure Rel (c d : Config σ) : Prop where
  stack : All2 (FrameRel R F) c.stack d.stack
  objs : ∀ o : Nat, ObjRel R F (c.objs[o]?) (d.objs[o]?)
  cells : d.cells = c.cells
  glob0 : d.glob0 = c.glob0
  globW : d.globW = c.globW
  out : d.out = c.out
  next : d.next = c.next
  res : d.res = c.res
  st : d.st = c.st

end

/-! ## Classification lemmas -/

section
variable {σ : Type} {R : Edit} {F : Label → Prop}

theorem alike_tail {S C x} (h : alike R (S :: C) x = true) : alike R C x = true := by
  simp [alike] at h; exact h.2

theorem alike_cls {C x} (h : alike R C x = true) :
    clsOf (C.map (editSc R)) x = clsOf C x := by
  cases C with
  | nil => rfl
  | cons S C => simp [alike] at h; exact h.1.symm

theorem FrameRel.clsOf_eq {f g : Frame σ} {x} (h : FrameRel R F f g) (hx : alike R f.chain x = true) :
    clsOf g.chain x = clsOf f.chain x := by
  rw [h.chain]; exact alike_cls hx

theorem FrameRel.place {f g : Frame σ} {x} (h : FrameRel R F f g) (hx : alike R f.chain x = true) :
    place g x = place f x := by
  unfold PyCore.place; rw [h.cls x hx, h.kind, h.id, h.κ x hx]

theorem inlinedLocal_go_rel {x} : ∀ {C : List Scope}, alike R C x = true → ChainKinds R C →
    inlinedLocal.go x (C.map (editSc R)) = inlinedLocal.go x C
  | [], _, _ => rfl
  | S :: C, hx, hk => by
    have hS : sameKind R S := hk S (List.mem_cons_self ..)
    have hC : ChainKinds R C := fun S' h' => hk S' (List.mem_cons_of_mem _ h')
    cases S with
    | fn l k y b =>
      cases k
      · have h1 := alike_cls (R := R) (C := .fn l false y b :: C) hx
        simp only [List.map, editSc] at h1 ⊢
        simp only [inlinedLocal.go, h1]
      · simp only [sameKind, editSc] at hS
        simp only [List.map, editSc, inlinedLocal.go, hS, inlinedLocal_go_rel (alike_tail hx) hC]
    | cl l b => simp [List.map, editSc, inlinedLocal.go]

theorem inlinedLocal_rel {x} {C : List Scope} (hx : alike R C x = true) (hk : ChainKinds R C) :
    inlinedLocal (C.map (editSc R)) x = inlinedLocal C x := by
  cases C with
  | nil => rfl
  | cons S C =>
    have hS : sameKind R S := hk S (List.mem_cons_self ..)
    have hC : ChainKinds R C := fun S' h' => hk S' (List.mem_cons_of_mem _ h')
    cases S with
    | fn l k y b =>
      cases k
      · simp [List.map, editSc, inlinedLocal]
      · simp only [sameKind, editSc] at hS
        simp only [List.map, editSc, inlinedLocal, hS, inlinedLocal_go_rel (alike_tail hx) hC]
    | cl l b => simp [List.map, editSc, inlinedLocal]

theorem FrameRel.unboundErr {f g : Frame σ} {x} (h : FrameRel R F f g) (hx : alike R f.chain x = true) :
    PyCore.unboundErr g x = PyCore.unboundErr f x := by
  unfold PyCore.unboundErr; rw [h.cls x hx, h.chain, inlinedLocal_rel hx h.kinds]

theorem FrameRel.cellOf {f g : Frame σ} {x} (h : FrameRel R F f g) (hx : alike R f.chain x = true) :
    PyCore.cellOf g x = PyCore.cellOf f x := by
  unfold PyCore.cellOf; rw [h.cls x hx, h.kind, h.id, h.κ x hx]

theorem FrameRel.capture {f g : Frame σ} {S x} (h : FrameRel R F f g) (hx : alike R (S :: f.chain) x = true) :
    PyCore.capture g (editSc R S) x = PyCore.capture f S x := by
  unfold PyCore.capture
  have h1 : clsOf (editSc R S :: g.chain) x = clsOf (S :: f.chain) x := by
    rw [h.chain]; exact alike_cls (C := S :: f.chain) hx
  rw [h1, h.cellOf (alike_tail hx)]

theorem Rel.glob {c d : Config σ} (h : Rel R F c d) : d.glob = c.glob := by
  funext x; unfold Config.glob; rw [h.glob0, h.globW]

theorem Rel.lookupGlobal {I : Py.Interp σ} {c d : Config σ} {x} (h : Rel R F c d) :
    PyCore.lookupGlobal I d x = PyCore.lookupGlobal I c x := by
  unfold PyCore.lookupGlobal; rw [h.glob]

theorem annRead_rel {I : Py.Interp σ} {c d : Config σ} {f g : Frame σ} (h : Rel R F c d)
    (hfg : FrameRel R F f g) : annRead I d g = annRead I c f := by
  unfold annRead; rw [hfg.kind, hfg.ns, h.lookupGlobal]

theorem readName_rel {I : Py.Interp σ} {c d : Config σ} {f g : Frame σ} {x k} (h : Rel R F c d) (hfg : FrameRel R F f g)
    (hx : alike R f.chain x = true) : readName I d g x k = readName I c f x k := by
  unfold readName
  rw [hfg.place hx, hfg.ns, h.cells, hfg.unboundErr hx]
  simp only [h.lookupGlobal]

theorem isSet_rel {c d : Config σ} {f g : Frame σ} {pl} (h : Rel R F c d) (hfg : FrameRel R F f g) :
    isSet d g pl = isSet c f pl := by
  cases pl <;> simp [isSet, h.glob, h.cells, hfg.ns]

end

end PyCore
