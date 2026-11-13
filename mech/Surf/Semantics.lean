/-
A small-step semantics of Surf, CEK style like PyCore's, written from the
Python language reference (and CPython 3.13 where the reference leaves the order
open), independently of the translation: a deterministic step function on
configurations, over an interpretation `Py.Interp σ` of the values.

The core owns names (classified by `clsOf`, as in PyCore), frames, cells,
function objects with their stored defaults, generators, and class bodies; the
interpretation does every operation on values and may call back into user code
(`Res.call`), which the core performs before handing the outcome to the native
continuation (`Kont.native`). Highlights, each from the reference:

* a comprehension is a function scope of its own: the scope around evaluates the
  first iterable and its `iter`, and calls the comprehension's function on it;
* defaults are evaluated at the `def` (before the annotations, after the
  decorators) and stored with the function object; decorators apply at the
  `def`, innermost first; a class's decorators, bases and keywords are evaluated
  before its body;
* an augmented assignment applies the in-place operator (`Add=`) and assigns its
  result, evaluating the target's subexpressions once;
* `for` catches `StopIteration` from its `next` call only;
* a chained comparison evaluates each middle operand once;
* module- and class-level annotated assignments store into `__annotations__`,
  which every module and class body creates first (CPython's `SETUP_ANNOTATIONS`, which
  CPython emits only in a body with an annotated assignment: a deviation listed in NOTES.md).
-/
import Surf.Syntax
import Common.Interp

namespace Surf.Sem
open Surf
open PyCore (Name Label Cls Kind)
open Py (Val Op Res Interp Disp Acc PK)

abbrev Addr := Nat × Name

/-! ## Labels and syntactic helpers -/

def Expr.lbl : Expr → Label
  | .const l _ | .name l _ | .bin l .. | .unary l .. | .boolop l .. | .compare l .. | .ifexp l ..
  | .call l .. | .attr l .. | .sub l .. | .slice l .. | .star l _ | .list l _ | .tuple l _
  | .set l _ | .dict l _ | .lam l .. | .comp l .. | .walrus l .. | .yield l _ | .yieldFrom l _
  | .fstr l _ | .fmt l .. => l

def Stmt.lbl : Stmt → Label
  | .expr l _ | .assign l .. | .augassign l .. | .annassign l .. | .del l _ | .ite l .. | .while l ..
  | .for l .. | .brk l | .cont l | .pass l | .ret l _ | .defn l .. | .cls l .. | .glob l _
  | .nonloc l _ | .tryE l .. | .raise l .. | .imp l _ | .impFrom l .. | .assert l .. => l

def Handler.lbl : Handler → Label | .mk l .. => l

def occNames (is : List Item) : List Name :=
  is.filterMap fun | .occ _ x _ => some x | _ => none

/-- The (mangled) names occurring in a scope's code, nested scopes included: the
names whose classification and cells a frame of the scope caches. -/
def Scope.names (C : List Scope) (S : Scope) : List Name :=
  match S with
  | .fn _ _ ps b => occNames (paramOccs (S :: C) ps ++ itemsB (S :: C) b)
  | .lam _ ps b => occNames (paramOccs (S :: C) ps ++ itemsE (S :: C) b)
  | .cl _ _ b => "__annotations__" :: PyCore.classImplicit ++ occNames (itemsB (S :: C) b)
  | .comp _ _ es gs => occNames (itemsGs (S :: C) true gs ++ itemsEs (S :: C) es)


/-! ## Configurations -/

inductive FKind where
  | mod
  | fn
  | gen (o : Nat)
  | cls

/-- A target of an augmented assignment, its parts evaluated. -/
inductive ATgt where
  | name (x : Name)
  | attr (o : Val) (a : Name)
  | item (o i : Val)

/-- What follows the evaluation of a list of expressions (`Kont.evs`). -/
inductive Then where
  /-- the operation on the values -/
  | op (o : Op)
  /-- nothing: the values are dropped -/
  | drop
  /-- `[f, args…, kwvals…]`: a call; `stars` marks the starred arguments, `kws` the
  keyword names (`none` for `**m`). -/
  | call (nargs : Nat) (stars : List Bool) (kws : List (Option Name))
  /-- `[decorators…, defaults…, annotations…]`: a `def` -/
  | defn (l : Label) (f : Name) (ps : List Param) (b : List Stmt) (nd nf : Nat)
  /-- `[defaults…]`: a lambda -/
  | lam (l : Label) (ps : List Param) (b : Expr)
  /-- `[decorators…, bases…, kwvals…]`: a class statement -/
  | cls (l : Label) (x : Name) (b : List Stmt) (nd : Nat) (stars : List Bool) (kws : List (Option Name))
  /-- `[e]` or `[e, cause]`: a `raise` -/
  | raise (cause : Bool)

/-- What the arguments of a call or class statement go to, once expanded. -/
inductive ArgsK where
  | call (f : Val)
  | cls (l : Label) (x : Name) (b : List Stmt) (ds : List Val)

/-- A comprehension's form and element expressions, and its accumulator (`none`
for a generator expression). -/
structure CI where
  k : CompKind
  es : List Expr
  acc : Val

/-- What a frame does next. `op o vs` performs an interpretation operation;
`kapp k r` hands the outcome `r` of a callback to the native continuation `k`;
`call f args kws` calls `f`; `store t v` assigns `v` to the target `t` (then
`exec []`); `ns` is a class body's namespace, given to its caller. -/
inductive Ctrl (σ : Type) where
  | ev (e : Expr)
  | val (v : Val)
  | exec (ss : List Stmt)
  | raise (v : Val)
  | retv (v : Val)
  | brk
  | cont
  | wait
  | op (o : Op) (vs : List Val)
  | kapp (k : σ → Except Val Val → Res σ) (r : Except Val Val)
  | call (f : Val) (args : List Val) (kws : List (Name × Val))
  | store (t : Expr) (v : Val)
  | ns (ns : List (Name × Val))

/-- The pending parts of a frame's program point. -/
inductive Kont (σ : Type) where
  | binL (op : String) (b : Expr)
  | binR (op : String) (a : Val)
  | unK (op : String)
  /-- an operand of `and`/`or`, `rest` after it -/
  | boolK (isAnd : Bool) (rest : List Expr)
  /-- the truth of the operand `v` -/
  | boolT (isAnd : Bool) (v : Val) (rest : List Expr)
  /-- the first operand of a comparison -/
  | cmpL (ops : List String) (es : List Expr)
  /-- the right operand of `a op ·` -/
  | cmpR (a : Val) (op : String) (ops : List String) (es : List Expr)
  /-- the result of `· op b`, `ops`/`es` after it -/
  | cmpO (b : Val) (ops : List String) (es : List Expr)
  /-- the truth of the result `r`, before going on with `b` -/
  | cmpT (r b : Val) (ops : List String) (es : List Expr)
  | ifK (a b : Expr)
  | ifT (a b : Expr)
  | evs (rest : List (Option Expr)) (acc : List Val) (t : Then)
  /-- all the values of `evs`, as a tuple -/
  | evsEnd (t : Then)
  | argStar (k : ArgsK) (kws : List (Option Name)) (kwvals : List Val)
  | argKw (k : ArgsK) (args : List Val)
  | attrK (a : Name)
  | subL (i : Expr)
  | subR (v : Val)
  | walrusK (x : Name)
  | yieldK
  | yfK
  | yfIt
  | yfN (sub : Val)
  | yfR (sub : Val)
  | fmtV (c : Int) (spec : Option Expr)
  | fmtC (spec : Option Expr)
  | fmtS (v : Val)
  | compIt (fo : Val)
  | compCall (fo : Val)
  /-- a native continuation awaiting the outcome of a callback -/
  | native (k : σ → Except Val Val → Res σ)
  /-- the `**` parameter's dictionary, before entering the function `o` -/
  | enterK (o : Nat) (bound : List (Name × Val)) (kx : Name)
  | exprS
  | assignK (ts : List Expr)
  | stAttr (a : Name) (v : Val)
  | stSubL (i : Expr) (v : Val)
  | stSubR (o v : Val)
  | stUnpack (ts : List Expr)
  | stMany (tvs : List (Expr × Val))
  | augN (x : Name) (op : String) (e : Expr)
  | augAttr (a : Name) (op : String) (e : Expr)
  | augAttrV (o : Val) (a : Name) (op : String) (e : Expr)
  | augSubL (i : Expr) (op : String) (e : Expr)
  | augSubI (o : Val) (op : String) (e : Expr)
  | augSubV (o i : Val) (op : String) (e : Expr)
  | augR (op : String) (old : Val) (t : ATgt)
  | augW (t : ATgt)
  /-- an annotated assignment's value, to store in `t`, then its annotation if given -/
  | annK (t : Expr) (ann : Option Expr)
  /-- the target is assigned (or its parts evaluated); its annotation is next if given -/
  | annA (t : Expr) (ann : Option Expr)
  /-- the annotation of the simple target `x`, for `__annotations__` -/
  | annV (x : Name)
  /-- `__annotations__`, to store the annotation `a` of `x` in -/
  | annD (x : Name) (a : Val)
  | delMany (ts : List Expr)
  | delAttr (a : Name)
  | delSubL (i : Expr)
  | delSubR (o : Val)
  | ifS (t u : List Stmt)
  | ifST (t u : List Stmt)
  | whileS (c : Expr) (b u : List Stmt)
  | whileT (c : Expr) (b u : List Stmt)
  /-- the body of `while c: b else: u` runs -/
  | loop (c : Expr) (b u : List Stmt)
  | forIt (t : Expr) (b u : List Stmt)
  | forStart (t : Expr) (b u : List Stmt)
  /-- `next` of the loop's iterator runs: the only part `StopIteration` ends the loop from -/
  | forNext (t : Expr) (it : Val) (b u : List Stmt)
  /-- the target is assigned and the body runs -/
  | forLoop (t : Expr) (it : Val) (b u : List Stmt)
  | seq (ss : List Stmt)
  | retS
  | raiseC (cause : Option Val)
  | raiseW (e : Val)
  | tryE (hs : List Handler) (u : List Stmt)
  /-- the handler's expression is evaluated, the exception `v` pending -/
  | catchS (v : Val) (x : Option Name) (hb : List Stmt) (hs : List Handler) (u : List Stmt)
  /-- whether the handler matches -/
  | catchT (v : Val) (x : Option Name) (hb : List Stmt) (hs : List Handler) (u : List Stmt)
  /-- a handler (of `x`) runs, keeping the exception it handles -/
  | handler (x : Option Name) (h : Val)
  /-- the decorators still to apply, innermost first -/
  | decos (ds : List Val)
  | assignN (x : Name)
  /-- a class body runs; its namespace makes the class -/
  | clsEnd (x : Name) (q : String) (bases : List Val) (kws : List (Name × Val)) (ds : List Val)
  /-- the new `__annotations__` of a module or class body -/
  | setAnn
  | impMod (al : List Alias)
  | impNext (mod : Val) (al : List Alias)
  | starStore
  | assertK (msg : Option Expr)
  | assertT (msg : Option Expr)
  | assertM
  /-- a comprehension's accumulator is made -/
  | compStart (ci : CI) (it : Val) (g : Gen) (rest : List Gen)
  /-- the bottom of a list, set or dictionary comprehension's frame -/
  | cAcc (acc : Val)
  | cNext (ci : CI) (it : Val) (g : Gen) (rest : List Gen)
  | cLoop (ci : CI) (it : Val) (g : Gen) (rest : List Gen)
  | cConds (ci : CI) (ifs : List Expr) (rest : List Gen)
  | cCond (ci : CI) (ifs : List Expr) (rest : List Gen)
  | cCondT (ci : CI) (ifs : List Expr) (rest : List Gen)
  | cIter (ci : CI) (g : Gen) (rest : List Gen)
  | cIt (ci : CI) (g : Gen) (rest : List Gen)
  | cElt (k : Acc) (acc : Val)
  | cKey (acc : Val) (v : Expr)
  | cVal (acc k : Val)

/-- A frame: its scope chain, the classification of names (`clsOf chain`, cached
by `Py.memo`), its closure environment, a class body's namespace (in insertion
order), and its program point. -/
structure Frame (σ : Type) where
  id : Nat
  chain : List Scope
  kind : FKind
  cls : Name → Cls
  κ : Name → Option Addr
  ns : List (Name × Val)
  ctrl : Ctrl σ
  kont : List (Kont σ)

inductive GSt (σ : Type) where
  | susp (f : Frame σ)
  | running
  | done

/-- Objects of the core: a function object (scope, chain, cached classification
and cells, kind, the defaults stored at its `def`, one per parameter) or a
generator. -/
inductive Obj (σ : Type) where
  | clo (S : Scope) (C : List Scope) (cls : Name → Cls) (κ : Name → Option Addr) (kind : Kind)
      (dflt : List (Option Val))
  | gen (st : GSt σ)

structure Config (σ : Type) where
  stack : List (Frame σ)
  objs : Std.HashMap Nat (Obj σ)
  cells : Std.HashMap Addr Val
  glob : Std.HashMap Name Val
  st : σ
  next : Nat
  res : Option (Except Val Unit)

/-! ## Names -/

inductive Place where
  | glob (x : Name)
  | ns (x : Name)
  | cell (a : Addr)

variable {σ : Type}

def mg (f : Frame σ) (x : Name) : Name := mangle (priv f.chain) x

def place (f : Frame σ) (x : Name) : Option Place :=
  match f.cls x with
  | .glob => some (.glob x)
  | .loc => match f.kind with
    | .cls => some (.ns x)
    | _ => some (.cell (f.id, x))
  | .free => (f.κ x).map .cell

def lookupGlobal (I : Interp σ) (c : Config σ) (x : Name) : Except Val Val :=
  match c.glob[x]? with
  | some v => .ok v
  | none => match I.builtin x with
    | some v => .ok v
    | none => .error (Py.err "NameError")

def unboundErr (f : Frame σ) (x : Name) : Val :=
  if f.cls x = .loc || inlinedLocal f.chain x then Py.err "UnboundLocalError" else Py.err "NameError"

def readName (I : Interp σ) (c : Config σ) (f : Frame σ) (x : Name) : Except Val Val :=
  match place f x with
  | some (.glob y) => lookupGlobal I c y
  | some (.ns y) => match f.ns.lookup y with
    | some v => .ok v
    | none => lookupGlobal I c y
  | some (.cell a) => match c.cells[a]? with
    | some v => .ok v
    | none => .error (unboundErr f x)
  | none => .error (Py.err "NameError")

/-- `__annotations__` as a module or class body reads it (`LOAD_NAME`: the namespace,
then the module dictionary and the builtins), whatever its classification. -/
def annRead (I : Interp σ) (c : Config σ) (f : Frame σ) : Except Val Val :=
  match f.kind, f.ns.lookup "__annotations__" with
  | .cls, some v => .ok v
  | _, _ => lookupGlobal I c "__annotations__"

def isSet (c : Config σ) (f : Frame σ) : Place → Bool
  | .glob y => c.glob.contains y
  | .ns y => (f.ns.lookup y).isSome
  | .cell a => c.cells.contains a

def nsSet (ns : List (Name × Val)) (x : Name) : Option Val → List (Name × Val)
  | some v => if ns.any (·.1 == x) then ns.map (fun p => if p.1 == x then (x, v) else p) else ns ++ [(x, v)]
  | none => ns.filter (·.1 != x)

def writeAt (c : Config σ) (f : Frame σ) (ov : Option Val) : Place → Config σ × Frame σ
  | .glob y => ({ c with glob := match ov with | some v => c.glob.insert y v | none => c.glob.erase y }, f)
  | .ns y => (c, { f with ns := nsSet f.ns y ov })
  | .cell a => ({ c with cells := match ov with | some v => c.cells.insert a v | none => c.cells.erase a }, f)

def cellOf (f : Frame σ) (x : Name) : Option Addr :=
  match f.kind with
  | .fn | .gen _ => if f.cls x = .loc then some (f.id, x) else f.κ x
  | _ => f.κ x

/-- The exception of the innermost handler running in a frame's continuation. -/
def kontExc : List (Kont σ) → Option Val
  | [] => none
  | .handler _ h :: _ => some h
  | .catchS h .. :: _ => some h
  | .catchT h .. :: _ => some h
  | _ :: ks => kontExc ks

/-- CPython's topmost exception state: the innermost running handler of the stack. -/
def curExc : List (Frame σ) → Option Val
  | [] => none
  | f :: fs => match kontExc f.kont with
    | some h => some h
    | none => curExc fs

def withCtx : Option Val → Val → Val
  | some h, v => v.setCtx h
  | none, v => v

def raiseNew (st : List (Frame σ)) (v : Val) : Ctrl σ := .raise (withCtx (curExc st) v)

def resCtrl (st : List (Frame σ)) : Except Val Val → Ctrl σ
  | .ok v => .val v
  | .error v => raiseNew st v

/-- A function object for the scope `S`, made in frame `f`: its classification of
names and its cells (`capture`, as in PyCore) cached on the names of its code. -/
def mkClo (f : Frame σ) (S : Scope) (dflt : List (Option Val)) : Obj σ :=
  let C := f.chain
  let xs := Scope.names C S
  let cl := (Py.memo xs (clsOf (S :: C))).get
  let κ := (Py.memo xs (fun x => if cl x = .free then cellOf f x else none)).get
  .clo S C cl κ (S.kind C) dflt

/-! ## Steps -/

section
variable (I : Interp σ) (c : Config σ) (f : Frame σ) (fs : List (Frame σ))

def top (f' : Frame σ) : Option (Config σ) := some { c with stack := f' :: fs }

def setC (ctl : Ctrl σ) (ks : List (Kont σ)) : Option (Config σ) :=
  some { c with stack := { f with ctrl := ctl, kont := ks } :: fs }

/-- An interpretation operation on the values `vs`, its result handled next. -/
def doOp (o : Op) (vs : List Val) (ks : List (Kont σ)) : Option (Config σ) :=
  setC c f fs (.op o vs) ks

def retTo (fs : List (Frame σ)) (ctl : Ctrl σ) : Option (Config σ) :=
  match fs with
  | g :: gs => some { c with stack := { g with ctrl := ctl } :: gs }
  | [] => none

def genEnd (fs : List (Frame σ)) (o : Nat) (ctl : Ctrl σ) : Option (Config σ) :=
  match fs with
  | g :: gs => some { c with stack := { g with ctrl := ctl } :: gs, objs := c.objs.insert o (.gen .done) }
  | [] => none

/-- Store `v` in `x`, then continue with `after` and `ks`. -/
def storeName (x : Name) (v : Val) (after : Ctrl σ) (ks : List (Kont σ)) : Option (Config σ) :=
  match place f x with
  | some pl =>
    let r := writeAt c f (some v) pl
    some { r.1 with stack := { r.2 with ctrl := after, kont := ks } :: fs }
  | none => setC c f fs (raiseNew (f :: fs) (Py.err "NameError")) ks

/-- Unset `x` (a handler's exit), then continue with `ctl` and `ks`. -/
def unsetThen (x : Option Name) (ctl : Ctrl σ) (ks : List (Kont σ)) : Option (Config σ) :=
  match x.bind (place f ·) with
  | some pl =>
    let r := writeAt c f none pl
    some { r.1 with stack := { r.2 with ctrl := ctl, kont := ks } :: fs }
  | none => setC c f fs ctl ks

/-- `del x`. -/
def delName (x : Name) (ks : List (Kont σ)) : Option (Config σ) :=
  match place f x with
  | some pl =>
    if isSet c f pl then
      let r := writeAt c f none pl
      some { r.1 with stack := { r.2 with ctrl := .exec [], kont := ks } :: fs }
    else
      let e := match pl with
        | .cell _ => unboundErr f x
        | _ => Py.err "NameError"
      setC c f fs (raiseNew (f :: fs) e) ks
  | none => setC c f fs (raiseNew (f :: fs) (Py.err "NameError")) ks

/-- Allocate a function object and give it. -/
def close (S : Scope) (dflt : List (Option Val)) (ks : List (Kont σ)) : Option (Config σ) :=
  some { c with
    stack := { f with ctrl := .val (.fn c.next), kont := ks } :: fs
    objs := c.objs.insert c.next (mkClo f S dflt)
    next := c.next + 1 }

/-- A truth test of `v`: `Val.no` is false and `bool b` is `b`; any other value goes to the
interpretation. -/
def tst (v : Val) (ks : List (Kont σ)) : Option (Config σ) :=
  match v with
  | .no => setC c f fs (.val (.bool false)) ks
  | .bool b => setC c f fs (.val (.bool b)) ks
  | v => doOp c f fs .truth [v] ks

/-- Begin evaluating a list of expressions (`none` gives `None`). -/
def startEvs (es : List (Option Expr)) (acc : List Val) (t : Then) (ks : List (Kont σ)) :
    Option (Config σ) :=
  match es with
  | [] => setC c f fs (.val (.tuple acc.reverse)) (.evsEnd t :: ks)
  | some e :: es => setC c f fs (.ev e) (.evs es acc t :: ks)
  | none :: es => setC c f fs (.val .none) (.evs es acc t :: ks)

/-- The start of a class body `g` (qualified name `q`): `__module__ = __name__`,
`__qualname__ = q`, as CPython's compiler emits them, through the body's own
classification; then `__annotations__ = {}` unless set (`SETUP_ANNOTATIONS`). -/
def classStart (g : Frame σ) (fs : List (Frame σ)) (q : String) (b : List Stmt) :
    Option (Config σ) :=
  let fail (c' : Config σ) (g' : Frame σ) (e : Val) : Option (Config σ) :=
    some { c' with stack := { g' with ctrl := raiseNew (g :: fs) e } :: fs }
  match readName I c g "__name__" with
  | .error e => fail c g e
  | .ok m => match place g "__module__" with
    | none => fail c g (Py.err "NameError")
    | some p1 =>
      let r1 := writeAt c g (some m) p1
      match place r1.2 "__qualname__" with
      | none => fail r1.1 r1.2 (Py.err "NameError")
      | some p2 =>
        let r2 := writeAt r1.1 r1.2 (some (I.const s!"'{q}'")) p2
        some { r2.1 with stack := { r2.2 with ctrl := .op (.display (.dict [])) [], kont := [.setAnn, .seq b] } :: fs }

/-- Push a class body. -/
def pushClass (l : Label) (x : Name) (b : List Stmt) (ds bases : List Val) (kws : List (Name × Val))
    (ks : List (Kont σ)) : Option (Config σ) :=
  let chain := Scope.cl l x b :: f.chain
  let g : Frame σ :=
    { id := c.next, chain := chain, kind := .cls,
      cls := (Py.memo (Scope.names f.chain (Scope.cl l x b)) (clsOf chain)).get, κ := cellOf f, ns := [],
      ctrl := .exec b, kont := [] }
  classStart I { c with next := c.next + 1 } g
    ({ f with ctrl := .wait, kont := .clsEnd (mg f x) (qualIn f.chain x) bases kws ds :: ks } :: fs)
    (qualIn f.chain x) b

/-- The arguments of a call or class statement are ready. -/
def finishArgs (k : ArgsK) (args : List Val) (kvs : List (Name × Val)) (ks : List (Kont σ)) :
    Option (Config σ) :=
  match k with
  | .call g => setC c f fs (.call g args kvs) ks
  | .cls l x b ds => pushClass I c f fs l x b ds args kvs ks

/-- The keyword phase of a call or class statement (`**m` items expanded). -/
def kwPhase (k : ArgsK) (args : List Val) (kws : List (Option Name)) (kwvals : List Val)
    (ks : List (Kont σ)) : Option (Config σ) :=
  if kws.any Option.isNone then doOp c f fs (.display (.kwargs kws)) kwvals (.argKw k args :: ks)
  else finishArgs I c f fs k args ((kws.filterMap id).zip kwvals) ks

/-- The positional phase (`*e` items expanded). -/
def argPhase (k : ArgsK) (args : List Val) (stars : List Bool) (kws : List (Option Name))
    (kwvals : List Val) (ks : List (Kont σ)) : Option (Config σ) :=
  if stars.any id then doOp c f fs (.display (.tuple stars)) args (.argStar k kws kwvals :: ks)
  else kwPhase I c f fs k args kws kwvals ks

/-- The values of a list of expressions are ready. -/
def finish (t : Then) (vs : List Val) (ks : List (Kont σ)) : Option (Config σ) :=
  match t with
  | .op o => doOp c f fs o vs ks
  | .drop => setC c f fs (.exec []) ks
  | .call n stars kws => match vs with
    | g :: rest => argPhase I c f fs (.call g) (rest.take n) stars kws (rest.drop n) ks
    | [] => none
  | .defn l g ps b nd nf =>
    close c f fs (.fn l g ps b) (Py.alignDefaults (ps.map (·.dflt.isSome)) ((vs.drop nd).take nf))
      (.decos (vs.take nd).reverse :: .assignN (mg f g) :: ks)
  | .lam l ps b => close c f fs (.lam l ps b) (Py.alignDefaults (ps.map (·.dflt.isSome)) vs) ks
  | .cls l x b nd stars kws =>
    let nb := stars.length
    argPhase I c f fs (.cls l x b (vs.take nd)) ((vs.drop nd).take nb) stars kws (vs.drop (nd + nb)) ks
  | .raise hasCause => match vs with
    | [e] => doOp c f fs .mkExc [e] (.raiseC none :: ks)
    | [e, cv] => if hasCause then doOp c f fs .mkExc [e] (.raiseC (some cv) :: ks) else none
    | _ => none

/-- Entering an expression. -/
def evalStep (e : Expr) : Option (Config σ) :=
  let ks := f.kont
  match e with
  | .const _ k => setC c f fs (.val (Py.constVal I k)) ks
  | .name _ x => setC c f fs (resCtrl (f :: fs) (readName I c f (mg f x))) ks
  | .bin _ op a b => setC c f fs (.ev a) (.binL op b :: ks)
  | .unary _ op a => setC c f fs (.ev a) (.unK op :: ks)
  | .boolop _ op (a :: rest) => setC c f fs (.ev a) (.boolK (op == "And") rest :: ks)
  | .boolop _ _ [] => none
  | .compare _ a ops es => setC c f fs (.ev a) (.cmpL ops es :: ks)
  | .ifexp _ cnd a b => setC c f fs (.ev cnd) (.ifK a b :: ks)
  | .call _ g args kws =>
    startEvs c f fs (some g :: (args.map fun a => some (unstar a)) ++ kws.map fun | .mk _ _ v => some v) []
      (.call args.length (args.map isStar) (kws.map fun | .mk _ x _ => x)) ks
  | .attr _ o a => setC c f fs (.ev o) (.attrK (mg f a) :: ks)
  | .sub _ o i => setC c f fs (.ev o) (.subL i :: ks)
  | .slice _ lo hi st => startEvs c f fs [lo, hi, st] [] (.op (.display .slice)) ks
  | .star .. => none
  | .list _ es => startEvs c f fs (es.map fun a => some (unstar a)) [] (.op (.display (.list (es.map isStar)))) ks
  | .tuple _ es => startEvs c f fs (es.map fun a => some (unstar a)) [] (.op (.display (.tuple (es.map isStar)))) ks
  | .set _ es =>
    let d := if es.length > 2 && es.all isConstE then Disp.constSet else Disp.set (es.map isStar)
    startEvs c f fs (es.map fun a => some (unstar a)) [] (.op (.display d)) ks
  | .dict _ kvs =>
    startEvs c f fs (kvs.flatMap fun | .mk (some k) v => [some k, some v] | .mk none v => [some v]) []
      (.op (.display (.dict (kvs.map fun | .mk k _ => k.isNone)))) ks
  | .lam l ps b => startEvs c f fs (ps.filterMap Param.dflt |>.map some) [] (.lam l ps b) ks
  | .comp l k es gs =>
    -- the comprehension's function is made, then the first iterable evaluated around it
    match gs with
    | .mk _ _ it _ :: _ =>
      some { c with
        stack := { f with ctrl := .ev it, kont := .compIt (.fn c.next) :: ks } :: fs
        objs := c.objs.insert c.next (mkClo f (.comp l k es gs) [])
        next := c.next + 1 }
    | [] => none
  | .walrus _ x v => setC c f fs (.ev v) (.walrusK (mg f x) :: ks)
  | .yield _ (some v) => setC c f fs (.ev v) (.yieldK :: ks)
  | .yield _ none => setC c f fs (.val .none) (.yieldK :: ks)
  | .yieldFrom _ v => setC c f fs (.ev v) (.yfK :: ks)
  | .fstr _ parts => startEvs c f fs (parts.map some) [] (.op (.display .fstr)) ks
  | .fmt _ v cv spec => setC c f fs (.ev v) (.fmtV cv spec :: ks)

/-- Entering a statement; the rest of the block waits as `seq`. -/
def execStep (s : Stmt) (ss : List Stmt) : Option (Config σ) :=
  let k := Kont.seq ss :: f.kont
  let isTop := match f.kind with | .mod | .cls => true | _ => false
  match s with
  | .expr _ e => setC c f fs (.ev e) (.exprS :: k)
  | .assign _ ts e => setC c f fs (.ev e) (.assignK ts :: k)
  | .augassign _ t op e => match t with
    | .name l x => setC c f fs (.ev (.name l x)) (.augN (mg f x) op e :: k)
    | .attr _ o a => setC c f fs (.ev o) (.augAttr (mg f a) op e :: k)
    | .sub _ o i => setC c f fs (.ev o) (.augSubL i op e :: k)
    | _ => none
  | .annassign _ t ann v =>
    let a := if isTop then some ann else none
    match v with
    | some e => setC c f fs (.ev e) (.annK t a :: k)
    | none => match t with
      | .name .. => setC c f fs (.exec []) (.annA t a :: k)
      | .attr _ o _ => startEvs c f fs [some o] [] .drop (.annA t a :: k)
      | .sub _ o i => startEvs c f fs [some o, some i] [] .drop (.annA t a :: k)
      | _ => none
  | .del _ ts => setC c f fs (.exec []) (.delMany ts :: k)
  | .ite _ cnd t u => setC c f fs (.ev cnd) (.ifS t u :: k)
  | .while _ cnd b u => setC c f fs (.ev cnd) (.whileS cnd b u :: k)
  | .for _ t it b u => setC c f fs (.ev it) (.forIt t b u :: k)
  | .brk _ => setC c f fs .brk k
  | .cont _ => setC c f fs .cont k
  | .pass _ => setC c f fs (.exec []) k
  | .ret _ (some e) => setC c f fs (.ev e) (.retS :: k)
  | .ret _ none => setC c f fs (.val .none) (.retS :: k)
  | .defn l g ps b ds r =>
    let dfs := ps.filterMap Param.dflt
    startEvs c f fs (ds.map some ++ dfs.map some ++ annOrder ps r) []
      (.defn l g ps b ds.length dfs.length) k
  | .cls l x bs kws b ds =>
    startEvs c f fs (ds.map some ++ bs.map (fun a => some (unstar a)) ++ kws.map fun | .mk _ _ v => some v) []
      (.cls l x b ds.length (bs.map isStar) (kws.map fun | .mk _ x _ => x)) k
  | .glob .. | .nonloc .. => setC c f fs (.exec []) k
  | .tryE _ b hs u => setC c f fs (.exec b) (.tryE hs u :: k)
  | .raise _ none none => match curExc (f :: fs) with
    | some h => setC c f fs (.raise h) k
    | none => setC c f fs (raiseNew (f :: fs) (Py.err "RuntimeError")) k
  | .raise _ (some e) cv => startEvs c f fs (some e :: cv.toList.map some) [] (.raise cv.isSome) k
  | .raise _ none (some _) => none
  | .imp _ [a] =>
    -- `import *` is no Python (the parser rejects it): no step
    if a.name == "*" then none
    else doOp c f fs (.import a.name a.asname.isSome) [] (.assignN (mg f a.bound) :: k)
  | .imp l al => setC c f fs (.exec (al.map fun a => .imp l [a])) k
  | .impFrom _ m al lvl =>
    if lvl > 0 then setC c f fs (raiseNew (f :: fs) (Py.err "ImportError")) k
    else doOp c f fs (.import (m.getD "") true) [] (.impMod al :: k)
  | .assert _ t m => setC c f fs (.ev t) (.assertK m :: k)

/-- Begin a comprehension's loop over the generator `g` and those in `rest`. -/
def compLoop (ci : CI) (it : Val) (g : Gen) (rest : List Gen) (ks : List (Kont σ)) : Option (Config σ) :=
  setC c f fs (.call .next [it] []) (.cNext ci it g rest :: ks)

/-- Enter a function object: bind the arguments, then run its code in a new frame
(or make a generator). -/
def enter (S : Scope) (C : List Scope) (cl : Name → Cls) (κ : Name → Option Addr) (kd : Kind)
    (bound : List (Name × Val)) : Option (Config σ) :=
  let n := c.next
  let (ctl, kk) : Ctrl σ × List (Kont σ) := match S with
    | .lam _ _ b => (.ev b, [.retS])
    | .fn _ _ _ b => (.exec b, [])
    | _ => (.exec [], [])
  let fr : Frame σ :=
    { id := n, chain := S :: C, kind := (if kd = .gen then .gen n else .fn), cls := cl,
      κ := κ, ns := [], ctrl := ctl, kont := kk }
  let cells := bound.foldl (fun m p => m.insert (n, p.1) p.2) c.cells
  if kd = .gen then
    some { c with
      stack := { f with ctrl := .val (.gen n) } :: fs
      objs := c.objs.insert n (.gen (.susp fr)), cells := cells, next := n + 1 }
  else
    some { c with stack := fr :: { f with ctrl := .wait } :: fs, cells := cells, next := n + 1 }

/-- A call; `f` is the caller. -/
def callStep (vf : Val) (args : List Val) (kws : List (Name × Val)) : Option (Config σ) :=
  let ks := f.kont
  let fail (e : String) := setC c f fs (raiseNew (f :: fs) (Py.err e)) ks
  match vf with
  | .fn o => match c.objs[o]? with
    | some (.clo S C cl κ kd dflt) => match S with
      | .comp _ k es (g :: rest) => match args with
        | [it] =>
          let n := c.next
          let fr : Frame σ :=
            { id := n, chain := S :: C, kind := (if k = .gen then .gen n else .fn),
              cls := cl, κ := κ, ns := [], ctrl := .exec [], kont := [] }
          if k = .gen then
            some { c with
              stack := { f with ctrl := .val (.gen n) } :: fs
              next := n + 1
              objs := c.objs.insert n (.gen (.susp
                { fr with ctrl := .call .next [it] [], kont := [.cNext ⟨k, es, .none⟩ it g rest] })) }
          else
            let acc : Disp := match k with | .set => .set [] | .dict => .dict [] | _ => .list []
            some { c with
              stack := { fr with ctrl := .op (.display acc) [],
                                 kont := [.compStart ⟨k, es, .none⟩ it g rest] }
                       :: { f with ctrl := .wait } :: fs
              next := n + 1 }
        | _ => fail "TypeError"
      | .comp _ _ _ [] => none
      | .cl .. => fail "TypeError"
      | .fn _ _ ps _ | .lam _ ps _ =>
        let sig := ps.map fun p => (mangle (priv (S :: C)) p.name, (Param.kind p).pk)
        match Py.bindArgs sig dflt args kws with
        | .error e => setC c f fs (raiseNew (f :: fs) e) ks
        | .ok (bound, none) => enter c f fs S C cl κ kd bound
        | .ok (bound, some (kx, items)) =>
          doOp c f fs (.display (.dict (items.map fun _ => false)))
            (items.flatMap fun p => [.str p.1, p.2]) (.enterK o bound kx :: ks)
    | _ => fail "TypeError"
  | .next => match args, kws with
    | [.gen o], [] => match c.objs[o]? with
      | some (.gen (.susp g)) =>
        some { c with stack := g :: { f with ctrl := .wait } :: fs, objs := c.objs.insert o (.gen .running) }
      | some (.gen .running) => fail "ValueError"
      | some (.gen .done) => setC c f fs (raiseNew (f :: fs) (Py.stopOf .none)) ks
      | _ => fail "TypeError"
    | [it], [] => doOp c f fs .next [it] ks
    | _, _ => fail "TypeError"
  | .op o => if kws.isEmpty then doOp c f fs o args ks else fail "TypeError"
  | _ => doOp c f fs (.call (kws.map (·.1))) (vf :: args ++ kws.map (·.2)) ks

/-- Assign `v` to the target `t`. -/
def storeStep (t : Expr) (v : Val) : Option (Config σ) :=
  let ks := f.kont
  match t with
  | .name _ x => storeName c f fs (mg f x) v (.exec []) ks
  | .attr _ o a => setC c f fs (.ev o) (.stAttr (mg f a) v :: ks)
  | .sub _ o i => setC c f fs (.ev o) (.stSubL i v :: ks)
  | .tuple _ ts | .list _ ts =>
    if (ts.filter isStar).length > 1 then none else
    let (b, st, a) := splitStar ts
    doOp c f fs (.unpack b st a) [v] (.stUnpack (ts.map unstar) :: ks)
  | _ => none

/-- A value delivered to the frame's continuation. -/
def valStep (v : Val) : Option (Config σ) :=
  let set := setC c f fs
  let op := doOp c f fs
  match f.kont with
  | .binL o b :: ks => set (.ev b) (.binR o v :: ks)
  | .binR o a :: ks => op (.binop o) [a, v] ks
  | .unK o :: ks => op (.unop o) [v] ks
  | .boolK _ [] :: ks => set (.val v) ks
  | .boolK isAnd rest :: ks => tst c f fs v (.boolT isAnd v rest :: ks)
  | .boolT isAnd a rest :: ks => match v, rest with
    | .bool b, e :: rest' =>
      if b == isAnd then set (.ev e) (.boolK isAnd rest' :: ks) else set (.val a) ks
    | _, _ => none
  | .cmpL (o :: ops) (e :: es) :: ks => set (.ev e) (.cmpR v o ops es :: ks)
  | .cmpL _ _ :: _ => none
  | .cmpR a o ops es :: ks => op (.binop o) [a, v] (.cmpO v ops es :: ks)
  | .cmpO _ [] _ :: ks => set (.val v) ks
  | .cmpO b ops es :: ks => tst c f fs v (.cmpT v b ops es :: ks)
  | .cmpT r b (o :: ops) (e :: es) :: ks => match v with
    | .bool true => set (.ev e) (.cmpR b o ops es :: ks)
    | .bool false => set (.val r) ks
    | _ => none
  | .cmpT .. :: _ => none
  | .ifK a b :: ks => tst c f fs v (.ifT a b :: ks)
  | .ifT a b :: ks => match v with
    | .bool t => set (.ev (if t then a else b)) ks
    | _ => none
  | .evs es acc t :: ks => startEvs c f fs es (v :: acc) t ks
  | .evsEnd t :: ks => match v with
    | .tuple vs => finish I c f fs t vs ks
    | _ => none
  | .argStar k kws kwvals :: ks => match v with
    | .tuple args => kwPhase I c f fs k args kws kwvals ks
    | _ => none
  | .argKw k args :: ks => match v with
    | .tuple pairs => match Py.kwPairs pairs with
      | some kvs => finishArgs I c f fs k args kvs ks
      | none => none
    | _ => none
  | .attrK a :: ks => op (.getattr a) [v] ks
  | .subL i :: ks => set (.ev i) (.subR v :: ks)
  | .subR o :: ks => op .getitem [o, v] ks
  | .walrusK x :: ks => storeName c f fs x v (.val v) ks
  | .yieldK :: ks => match f.kind, fs with
    | .gen o, g :: gs =>
      some { c with stack := { g with ctrl := .val v } :: gs,
                    objs := c.objs.insert o (.gen (.susp { f with ctrl := .val .none, kont := ks })) }
    | _, _ => none
  | .yfK :: ks => match v with
    | .gen _ => set (.call .next [v] []) (.yfN v :: ks)
    | v => op .iter [v] (.yfIt :: ks)
  | .yfIt :: ks => set (.call .next [v] []) (.yfN v :: ks)
  | .yfN sub :: ks => set (.val v) (.yieldK :: .yfR sub :: ks)
  | .yfR sub :: ks => set (.call .next [sub] []) (.yfN sub :: ks)
  | .fmtV cv spec :: ks =>
    if cv == -1 then set (.val v) (.fmtC spec :: ks) else op (.convert cv) [v] (.fmtC spec :: ks)
  | .fmtC (some s) :: ks => set (.ev s) (.fmtS v :: ks)
  | .fmtC none :: ks => op .format [v] ks
  | .fmtS a :: ks => op .format [a, v] ks
  | .compIt fo :: ks => op .iter [v] (.compCall fo :: ks)
  | .compCall fo :: ks => set (.call fo [v] []) ks
  | .native k :: ks => set (.kapp k (.ok v)) ks
  | .enterK o bound kx :: ks => match c.objs[o]? with
    | some (.clo S C cl κ kd _) => enter c { f with kont := ks } fs S C cl κ kd (bound ++ [(kx, v)])
    | _ => none
  | .exprS :: ks => set (.exec []) ks
  | .assignK ts :: ks => set (.exec []) (.stMany (ts.map (·, v)) :: ks)
  | .stAttr a x :: ks => op (.setattr a) [v, x] (.exprS :: ks)
  | .stSubL i x :: ks => set (.ev i) (.stSubR v x :: ks)
  | .stSubR o x :: ks => op .setitem [o, v, x] (.exprS :: ks)
  | .stUnpack ts :: ks => match v with
    | .tuple vs => if vs.length == ts.length then set (.exec []) (.stMany (ts.zip vs) :: ks) else none
    | _ => none
  | .augN x o e :: ks => set (.ev e) (.augR o v (.name x) :: ks)
  | .augAttr a o e :: ks => op (.getattr a) [v] (.augAttrV v a o e :: ks)
  | .augAttrV ob a o e :: ks => set (.ev e) (.augR o v (.attr ob a) :: ks)
  | .augSubL i o e :: ks => set (.ev i) (.augSubI v o e :: ks)
  | .augSubI ob o e :: ks => op .getitem [ob, v] (.augSubV ob v o e :: ks)
  | .augSubV ob i o e :: ks => set (.ev e) (.augR o v (.item ob i) :: ks)
  | .augR o old t :: ks => op (.binop (o ++ "=")) [old, v] (.augW t :: ks)
  | .augW t :: ks => match t with
    | .name x => storeName c f fs x v (.exec []) ks
    | .attr ob a => op (.setattr a) [ob, v] (.exprS :: ks)
    | .item ob i => op .setitem [ob, i, v] (.exprS :: ks)
  | .annK t a :: ks => set (.store t v) (.annA t a :: ks)
  | .annV x :: ks => match annRead I c f with
    | .ok d => op .setitem [d, .str x, v] (.exprS :: ks)
    | .error e => set (raiseNew (f :: fs) e) ks
  | .delAttr a :: ks => op (.delattr a) [v] (.exprS :: ks)
  | .delSubL i :: ks => set (.ev i) (.delSubR v :: ks)
  | .delSubR o :: ks => op .delitem [o, v] (.exprS :: ks)
  | .ifS t u :: ks => tst c f fs v (.ifST t u :: ks)
  | .ifST t u :: ks => match v with
    | .bool b => set (.exec (if b then t else u)) ks
    | _ => none
  | .whileS cnd b u :: ks => tst c f fs v (.whileT cnd b u :: ks)
  | .whileT cnd b u :: ks => match v with
    | .bool true => set (.exec b) (.loop cnd b u :: ks)
    | .bool false => set (.exec u) ks
    | _ => none
  | .forIt t b u :: ks => op .iter [v] (.forStart t b u :: ks)
  | .forStart t b u :: ks => set (.call .next [v] []) (.forNext t v b u :: ks)
  | .forNext t it b u :: ks => set (.store t v) (.seq b :: .forLoop t it b u :: ks)
  | .retS :: ks => set (.retv v) ks
  | .raiseC none :: ks => set (raiseNew (f :: fs) v) ks
  | .raiseC (some .none) :: ks => set (raiseNew (f :: fs) (Py.setCause v .none)) ks
  | .raiseC (some cv) :: ks => op .mkExc [cv] (.raiseW v :: ks)
  | .raiseW e :: ks => set (raiseNew (f :: fs) (Py.setCause e v)) ks
  | .catchS ex x hb hs u :: ks => op .excMatch [ex, v] (.catchT ex x hb hs u :: ks)
  | .catchT ex x hb hs u :: ks => match v with
    | .bool true => match x with
      | some y => storeName c f fs (mg f y) ex (.exec hb) (.handler (some (mg f y)) ex :: ks)
      | none => set (.exec hb) (.handler none ex :: ks)
    | .bool false => set (.raise ex) (.tryE hs u :: ks)
    | _ => none
  | .decos (d :: ds) :: ks => set (.call d [v] []) (.decos ds :: ks)
  | .decos [] :: ks => set (.val v) ks
  | .assignN x :: ks => storeName c f fs x v (.exec []) ks
  | .setAnn :: ks => match f.kind with
    | .cls => if (f.ns.lookup "__annotations__").isSome then set (.exec []) ks
      else setC c { f with ns := nsSet f.ns "__annotations__" (some v) } fs (.exec []) ks
    | _ => if c.glob.contains "__annotations__" then set (.exec []) ks
      else some { c with glob := c.glob.insert "__annotations__" v,
                         stack := { f with ctrl := .exec [], kont := ks } :: fs }
  | .impMod al :: ks => set (.exec []) (.impNext v al :: ks)
  | .starStore :: ks => match v with
    | .tuple ps => match (Py.kwPairs ps).map (·.filter (!·.1.startsWith ".")), f.kind with
      | some kvs, .mod => some { c with glob := kvs.foldl (fun g p => g.insert p.1 p.2) c.glob,
                                        stack := { f with ctrl := .exec [], kont := ks } :: fs }
      | some kvs, .cls => setC c { f with ns := kvs.foldl (fun n p => nsSet n p.1 (some p.2)) f.ns } fs
                            (.exec []) ks
      | _, _ => none
    | _ => none
  | .assertK m :: ks => tst c f fs v (.assertT m :: ks)
  | .assertT m :: ks => match v, m with
    | .bool true, _ => set (.exec []) ks
    | .bool false, some e => set (.ev e) (.assertM :: ks)
    | .bool false, none => set (raiseNew (f :: fs) (.err "AssertionError" [])) ks
    | _, _ => none
  | .assertM :: ks => set (raiseNew (f :: fs) (.err "AssertionError" [v])) ks
  | .compStart ci it g rest :: ks =>
    compLoop c f fs { ci with acc := v } it g rest (.cAcc v :: ks)
  | .cNext ci it g rest :: ks =>
    match g with
    | .mk _ t _ ifs => set (.store t v) (.cConds ci ifs rest :: .cLoop ci it g rest :: ks)
  | .cCond ci ifs rest :: ks => tst c f fs v (.cCondT ci ifs rest :: ks)
  | .cCondT ci ifs rest :: ks => match v with
    | .bool true => set (.exec []) (.cConds ci ifs rest :: ks)
    | .bool false => set (.exec []) ks
    | _ => none
  | .cIter ci g rest :: ks => op .iter [v] (.cIt ci g rest :: ks)
  | .cIt ci g rest :: ks => compLoop c f fs ci v g rest ks
  | .cElt k acc :: ks => op (.accum k) [acc, v] (.exprS :: ks)
  | .cKey acc e :: ks => set (.ev e) (.cVal acc v :: ks)
  | .cVal acc k :: ks => op (.accum .dict) [acc, k, v] (.exprS :: ks)
  | _ => none

/-- A statement or block has ended (`exec []`). -/
def doneStep : Option (Config σ) :=
  let set := setC c f fs
  match f.kont with
  | .seq ss :: ks => set (.exec ss) ks
  | .loop cnd b u :: ks => set (.ev cnd) (.whileS cnd b u :: ks)
  | .forLoop t it b u :: ks => set (.call .next [it] []) (.forNext t it b u :: ks)
  | .tryE _ u :: ks => set (.exec u) ks
  | .handler x _ :: ks => unsetThen c f fs x (.exec []) ks
  | .stMany ((t, v) :: tvs) :: ks => set (.store t v) (.stMany tvs :: ks)
  | .stMany [] :: ks => set (.exec []) ks
  | .annA t (some a) :: ks => match t with
    | .name _ x => set (.ev a) (.annV (mg f x) :: ks)
    | _ => set (.ev a) (.exprS :: ks)
  | .annA _ none :: ks => set (.exec []) ks
  | .delMany (t :: ts) :: ks => match t with
    | .name _ x => delName c f fs (mg f x) (.delMany ts :: ks)
    | .attr _ o a => set (.ev o) (.delAttr (mg f a) :: .delMany ts :: ks)
    | .sub _ o i => set (.ev o) (.delSubL i :: .delMany ts :: ks)
    | .tuple _ es | .list _ es => set (.exec []) (.delMany (es ++ ts) :: ks)
    | _ => none
  | .delMany [] :: ks => set (.exec []) ks
  | .impNext m (a :: al) :: ks =>
    if a.name == "*" then doOp c f fs .importStar [m] (.starStore :: .impNext m al :: ks)
    else doOp c f fs (.importFrom a.name) [m] (.assignN (mg f a.bound) :: .impNext m al :: ks)
  | .impNext _ [] :: ks => set (.exec []) ks
  | .cAcc acc :: ks => set (.retv acc) ks
  | .cLoop ci it g rest :: ks => compLoop c f fs ci it g rest ks
  | .cConds ci (e :: ifs) rest :: ks => set (.ev e) (.cCond ci ifs rest :: ks)
  | .cConds ci [] (g :: rest) :: ks => match g with
    | .mk _ _ it _ => set (.ev it) (.cIter ci g rest :: ks)
  | .cConds ci [] [] :: ks => match ci.k, ci.es with
    | .gen, [e] => set (.ev e) (.yieldK :: .exprS :: ks)
    | .dict, [k, v] => set (.ev k) (.cKey ci.acc v :: ks)
    | .set, [e] => set (.ev e) (.cElt .set ci.acc :: ks)
    | .list, [e] => set (.ev e) (.cElt .list ci.acc :: ks)
    | _, _ => none
  | [] => match f.kind with
    | .mod => some { c with stack := [], res := some (.ok ()) }
    | .fn => retTo c fs (.val .none)
    | .gen o => genEnd c fs o (raiseNew fs (Py.stopOf .none))
    | .cls => retTo c fs (.ns f.ns)
  | _ => none

/-- An exception meets the frame's continuation. -/
def raiseStep (v : Val) : Option (Config σ) :=
  let set := setC c f fs
  match f.kont with
  | .tryE (.mk _ ty x hb :: hs) u :: ks => match ty with
    | some e => set (.ev e) (.catchS v x hb hs u :: ks)
    | none => set (.exec hb) (.handler none v :: ks)
  | .handler x _ :: ks => unsetThen c f fs x (.raise v) ks
  | .forNext _ _ _ u :: ks => if Py.isStop v then set (.exec u) ks else set (.raise v) ks
  | .cNext .. :: ks => if Py.isStop v then set (.exec []) ks else set (.raise v) ks
  | .yfN _ :: ks => if Py.isStop v then set (.val (Py.stopValue v)) ks else set (.raise v) ks
  | .native k :: ks => set (.kapp k (.error v)) ks
  | _ :: ks => set (.raise v) ks
  | [] => match f.kind with
    | .mod => some { c with stack := [], res := some (.error v) }
    | .fn | .cls => retTo c fs (.raise v)
    | .gen o => genEnd c fs o (.raise (if Py.isStop v then .exn (Py.err "RuntimeError") v v else v))

def retStep (v : Val) : Option (Config σ) :=
  match f.kont with
  | .handler x _ :: ks => unsetThen c f fs x (.retv v) ks
  | _ :: ks => setC c f fs (.retv v) ks
  | [] => match f.kind with
    | .fn => retTo c fs (.val v)
    | .gen o => genEnd c fs o (raiseNew fs (Py.stopOf v))
    | _ => none

def brkStep : Option (Config σ) :=
  match f.kont with
  | .loop .. :: ks | .forLoop .. :: ks => setC c f fs (.exec []) ks
  | .handler x _ :: ks => unsetThen c f fs x .brk ks
  | _ :: ks => setC c f fs .brk ks
  | [] => none

def contStep : Option (Config σ) :=
  match f.kont with
  | .loop cnd b u :: ks => setC c f fs (.ev cnd) (.whileS cnd b u :: ks)
  | .forLoop t it b u :: ks => setC c f fs (.call .next [it] []) (.forNext t it b u :: ks)
  | .handler x _ :: ks => unsetThen c f fs x .cont ks
  | _ :: ks => setC c f fs .cont ks
  | [] => none

/-- An interpretation's result `r`, with the rest of the configuration. -/
def handle (objs : Std.HashMap Nat (Obj σ)) (cells : Std.HashMap Addr Val)
    (glob : Std.HashMap Name Val) (next : Nat) (res : Option (Except Val Unit)) (f : Frame σ)
    (fs : List (Frame σ)) (r : Res σ) : Config σ :=
  let mk (s : σ) (g : Frame σ) : Config σ :=
    { stack := g :: fs, objs := objs, cells := cells, glob := glob, st := s, next := next, res := res }
  match r with
  | .ok s v => mk s { f with ctrl := .val v }
  | .raise s e => mk s { f with ctrl := raiseNew (f :: fs) e }
  | .reraise s e => mk s { f with ctrl := .raise e }
  | .call s g args kws k => mk s { f with ctrl := .call g args kws, kont := .native k :: f.kont }

/-- Perform an operation, or apply a native continuation, on the state (taken out
of the configuration first, so that the interpretation owns it). -/
def opStep (o : Op) (vs : List Val) : Option (Config σ) :=
  match c with
  | { stack := _, objs, cells, glob, st, next, res } =>
    some (handle objs cells glob next res f fs (I.op st o vs))

def kappStep (k : σ → Except Val Val → Res σ) (r : Except Val Val) : Option (Config σ) :=
  match c with
  | { stack := _, objs, cells, glob, st, next, res } =>
    some (handle objs cells glob next res f fs (k st r))

/-- A class body's namespace reaches its caller. -/
def nsStep (ns : List (Name × Val)) : Option (Config σ) :=
  match f.kont with
  | .clsEnd x q bases kws ds :: ks =>
    doOp c f fs (.mkClass x q (kws.map (·.1)) (ns.map (·.1))) (bases ++ kws.map (·.2) ++ ns.map (·.2))
      (.decos ds.reverse :: .assignN x :: ks)
  | _ => none

end

def step (I : Interp σ) (c : Config σ) : Option (Config σ) :=
  match c.stack with
  | [] => none
  | f :: fs =>
    match f.ctrl with
    | .ev e => evalStep I c f fs e
    | .exec [] => doneStep c f fs
    | .exec (s :: ss) => execStep c f fs s ss
    | .val v => valStep I c f fs v
    | .raise v => raiseStep c f fs v
    | .retv v => retStep c f fs v
    | .brk => brkStep c f fs
    | .cont => contStep c f fs
    | .wait => none
    | .op o vs => opStep I c f fs o vs
    | .kapp k r => kappStep c f fs k r
    | .call g args kws => callStep c { f with ctrl := .wait } fs g args kws
    | .store t v => storeStep c f fs t v
    | .ns ns => nsStep c f fs ns

/-- The node a step evaluates when it enters it: an expression or statement, or a
handler clause whose expression `Catch` evaluates. -/
def focus (c : Config σ) : Option Label :=
  match c.stack with
  | f :: _ => match f.ctrl with
    | .ev e => some (Expr.lbl e)
    | .exec (s :: _) => some (Stmt.lbl s)
    | .raise _ => match f.kont with
      | .tryE (h :: _) _ :: _ => some (Handler.lbl h)
      | _ => none
    | _ => none
  | [] => none

/-! ## Executions -/

def run (I : Interp σ) : Nat → Config σ → Config σ
  | 0, c => c
  | n + 1, c => match step I c with
    | some c' => run I n c'
    | none => c

/-- The module frame of `p`, with the module dictionary `glob`. -/
def modFrame (p : List Stmt) : Frame σ :=
  { id := 0, chain := [], kind := .mod, cls := fun _ => .glob, κ := fun _ => none, ns := [],
    ctrl := .op (.display (.dict [])) [], kont := [.setAnn, .seq p] }

def init (p : List Stmt) (glob : Std.HashMap Name Val) (s : σ) : Config σ where
  stack := [modFrame p]
  objs := {}
  cells := {}
  glob := glob
  st := s
  next := 1
  res := none

/-- Run another module on the state an ended run left (a harness's prelude, then
the program, on one module dictionary). -/
def Config.load (c : Config σ) (p : List Stmt) : Config σ :=
  { c with stack := [modFrame p], res := none }

inductive Outcome (σ : Type) where
  | normal (st : σ) (glob : Std.HashMap Name Val)
  | exc (v : Val) (st : σ)
  | stuck (st : σ)

def outcome (c : Config σ) : Outcome σ :=
  match c.stack, c.res with
  | [], some (.ok ()) => .normal c.st c.glob
  | [], some (.error v) => .exc v c.st
  | _, _ => .stuck c.st

def Terminates (I : Interp σ) (c : Config σ) (P : Outcome σ → Prop) : Prop :=
  ∃ n, step I (run I n c) = none ∧ P (outcome (run I n c))

def Diverges (I : Interp σ) (c : Config σ) : Prop := ∀ n, step I (run I n c) ≠ none

end Surf.Sem
