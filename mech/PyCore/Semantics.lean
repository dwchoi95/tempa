/-
The small-step semantics of PyCore (Figure 5 and the appendix's Semantics):
a deterministic step function on configurations ⟨K, μ, ω⟩, over an
interpretation `Py.Interp σ` (`Common/Interp.lean`) with a state of its own.

Beside PyCore's own constructs, the core performs what the translation from Surf
needs without asking the interpretation, so that a translated program asks it for
exactly what the Surf program asks (Surf/Semantics.lean): argument records (`$args`
and `,`), calls with positional, starred and keyword arguments and parameter binding
(`Py.bindArgs`), function objects with signatures and defaults, decorators, class
arguments, annotations, `raise … from …`, unpacking checks, the frame's own cells of
fresh names, and handler clauses matching `StopIteration` or anything (`$stop`,
`$any`): the gadgets of `Py.Gadget`, each a constant whose call the core performs.
-/
import PyCore.Syntax
import Common.Interp

namespace PyCore

/-- Values: `Py.Val`. A closure is `fn o`, a generator `gen o` (objects of the core);
what the interpretation builds (classes among them) is its own. -/
abbrev Val := Py.Val
open Py (Op Res Gadget PK)

def errName : Val := Py.err "NameError"
def errUnbound : Val := Py.err "UnboundLocalError"
def errType : Val := Py.err "TypeError"
def errValue : Val := Py.err "ValueError"
def errRuntime : Val := Py.err "RuntimeError"

/-- A cell is addressed by the frame that allocated it and the name. -/
abbrev Addr := Nat × Name

variable {σ : Type}

/-- The delegate of a `yield from`: a generator object, or an iterator of the
interpretation. -/
inductive Deleg where
  | gen (o : Nat)
  | it (d : Val)

/-- What the arguments a gadget gathers go to: a call of `f`, or the class statement
that follows, with its decorators. -/
inductive ArgsT where
  | call (f : Val)
  | cls (ds : List Val)

/-- What a frame does next: evaluate an expression, deliver a value to its
continuation, execute a block (`exec []` is `f[∘]`), propagate an exception, a
return, a `break` or a `continue`, advance a `yield from`, or await a callee
(`f[•]`); perform an operation of the interpretation (`op`), hand a callback's
outcome to its native continuation (`kapp`), make a call (`call`), or give a class
body's namespace to its caller (`ns`). -/
inductive Ctrl (σ : Type) where
  | ev (e : Expr)
  | val (v : Val)
  | exec (ss : List Stmt)
  | raise (v : Val)
  | retv (v : Val)
  | wait
  | brk
  | cont
  /-- `yield from` asks its delegate for the next value. -/
  | yfStep (d : Deleg)
  | op (o : Op) (vs : List Val)
  | kapp (k : σ → Except Val Val → Res σ) (r : Except Val Val)
  | call (f : Val) (args : List Val) (kws : List (Name × Val))
  | ns (ns : List (Name × Val))

/-- The pending parts of a frame's program point. -/
inductive Kont (σ : Type) where
  | binL (op : String) (b : Expr)
  | binR (op : String) (v : Val)
  | callF (a : Expr)
  | callA (f : Val)
  | walrus (x : Name)
  | assign (x : Name)
  | exprS
  | printS
  | retS
  | raiseS
  /-- the exception `raise` made of its operand (`Op.mkExc`) -/
  | raiseE
  | ifS (t u : List Stmt)
  /-- the truth of an `if`'s condition -/
  | ifT (t u : List Stmt)
  /-- The condition of `while c: b else: u` is being evaluated. -/
  | whileS (c : Expr) (b u : List Stmt)
  | whileT (c : Expr) (b u : List Stmt)
  /-- The body of `while c: b else: u` runs; `break` and `continue` stop here. -/
  | loop (c : Expr) (b u : List Stmt)
  | seq (ss : List Stmt)
  /-- The body of a `try` runs; `hs` are its handlers, `u` its `else` block. -/
  | tryE (hs : List Handler) (u : List Stmt)
  /-- The expression of the handler of `x` is evaluated, with the exception `v`
  pending and the remaining handlers `hs` and `else` block `u` after it. -/
  | catchS (v : Val) (x : Name) (hb : List Stmt) (hs : List Handler) (u : List Stmt)
  /-- whether the handler matches, the exception still pending -/
  | catchT (v : Val) (x : Name) (hb : List Stmt) (hs : List Handler) (u : List Stmt)
  /-- A handler of `x` runs, keeping the exception it handles pending. -/
  | handler (x : Name) (h : Val)
  | yieldS
  /-- `a if · else b` awaits its condition. -/
  | condK (a b : Expr)
  | condT (a b : Expr)
  /-- `· and b` (`isAnd`) or `· or b` awaits its first operand. -/
  | boolK (isAnd : Bool) (b : Expr)
  | boolT (isAnd : Bool) (v : Val) (b : Expr)
  /-- `yield from ·` awaits its delegate. -/
  | yfStart
  /-- `yield from` awaits its delegate's iterator. -/
  | yfIt
  /-- `yield from` awaits the delegate's next value (or its `StopIteration`). -/
  | yfGot (d : Deleg)
  /-- a native continuation awaiting the outcome of a callback -/
  | native (k : σ → Except Val Val → Res σ)
  /-- a class body runs; its namespace makes the class `x` (qualified name `q`) of the
  bases and keywords given, then the decorators apply -/
  | clsEnd (x : Name) (q : String) (bases : List Val) (kws : List (Name × Val)) (ds : List Val)
  /-- the starred arguments expanded (a tuple); the keywords next -/
  | argStar (t : ArgsT) (kws : List (Option Name)) (kwvals : List Val)
  /-- the keyword arguments expanded (a tuple of pairs) -/
  | argKw (t : ArgsT) (args : List Val)
  /-- the `**` parameter's dictionary, before entering the closure `o` -/
  | enterK (o : Nat) (bound : List (Name × Val)) (kx : Name)
  /-- the decorators still to apply, innermost first -/
  | decos (ds : List Val)
  /-- `raise e from c`: the exception made of `e`, the cause `c` next -/
  | raiseC (cause : Val)
  /-- the cause made, for the exception `e` -/
  | raiseW (e : Val)
  /-- an unpacking's result, to be a tuple of `n` items -/
  | unpackK (n : Nat)

inductive FKind where
  | mod
  | fn
  | gen (o : Nat)
  | cls
  deriving DecidableEq

/-- A frame; `cls` is the classification of names in its scope (`clsOf chain`, cached
by `Py.memo`); a class body's namespace `ns` is kept in insertion order. -/
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

/-- A signature: the parameters' names and kinds, and the defaults stored with the
function object, one per parameter. -/
abbrev Sig := List (Name × PK) × List (Option Val)

/-- Objects of the core: a closure (its scope, chain, cached classification and cells,
and, once `$def` gave them, its signature and defaults), or a generator. -/
inductive Obj (σ : Type) where
  | clo (S : Scope) (C : List Scope) (cls : Name → Cls) (κ : Name → Option Addr) (sig : Option Sig)
  | gen (st : GSt σ)

/-- A configuration. The module dictionary is the input `glob0` overlaid by the writes
`globW` (`none` a deletion). -/
structure Config (σ : Type) where
  stack : List (Frame σ)
  objs : Std.HashMap Nat (Obj σ)
  cells : Std.HashMap Addr Val
  glob0 : Name → Option Val
  globW : Std.HashMap Name (Option Val)
  out : List Val
  next : Nat
  res : Option (Except Val Unit)
  st : σ

/-- The module dictionary. -/
def Config.glob (c : Config σ) (x : Name) : Option Val :=
  match c.globW[x]? with
  | some ov => ov
  | none => c.glob0 x

/-- A class namespace with `x` set (in place, or appended) or removed. -/
def nsSet (ns : List (Name × Val)) (x : Name) : Option Val → List (Name × Val)
  | some v => if ns.any (·.1 == x) then ns.map (fun p => if p.1 == x then (x, v) else p) else ns ++ [(x, v)]
  | none => ns.filter (·.1 != x)

/-- The names occurring in a scope's code, nested scopes included: those whose
classification a frame of the scope caches. -/
def Scope.names (S : Scope) : List Name :=
  let occ (is : List Item) : List Name := is.filterMap fun | .occ _ x _ => some x | _ => none
  match S with
  | .fn _ _ x b => x :: occ (itemsB Edit.none [] b)
  | .cl _ b => classImplicit ++ occ (itemsB Edit.none [] b)

/-! ## Names -/

/-- Where `cls_S` sends a name: the module dictionary, the class namespace, or a cell. -/
inductive Place where
  | glob (x : Name)
  | ns (x : Name)
  | cell (a : Addr)

def place (f : Frame σ) (x : Name) : Option Place :=
  match f.cls x with
  | .glob => some (.glob x)
  | .loc => match f.kind with
    | .cls => some (.ns x)
    | _ => some (.cell (f.id, x))
  | .free => (f.κ x).map .cell

def lookupGlobal (I : Py.Interp σ) (c : Config σ) (x : Name) : Except Val Val :=
  match c.glob x with
  | some v => .ok v
  | none => match I.builtin x with
    | some v => .ok v
    | none => .error errName

/-- Whether `x`, read in a frame of the chain `ch`, is a local of the function its
comprehensions are inlined into (PEP 709, as Surf's `inlinedLocal`): walking up through
comprehension functions `λ°` of plain kind (list, set and dictionary comprehensions;
a generator expression's is a generator), the first other scope is a function in
which `x` is local. -/
def inlinedLocal (ch : List Scope) (x : Name) : Bool :=
  match ch with
  | S@(.fn _ true _ _) :: C => S.kind == .plain && go C
  | _ => false
where
  go : List Scope → Bool
    | S@(.fn _ true _ _) :: C => S.kind == .plain && go C
    | S@(.fn _ false _ _) :: C => clsOf (S :: C) x == .loc
    | _ => false

/-- The exception a failing read of an unset cell raises: `UnboundLocalError` for a
local, or a local of the function a comprehension is inlined into; else `NameError`. -/
def unboundErr (f : Frame σ) (x : Name) : Val :=
  if f.cls x = .loc || inlinedLocal f.chain x then errUnbound else errName

/-- `Read`: `UnboundLocalError` for an unset local cell, `NameError` for a failed
global, namespace or free lookup, unless the read node `k` overrides the class. -/
def readName (I : Py.Interp σ) (c : Config σ) (f : Frame σ) (x : Name) (k : Option String) :
    Except Val Val :=
  let r := match place f x with
    | some (.glob y) => lookupGlobal I c y
    | some (.ns y) => match f.ns.lookup y with
      | some v => .ok v
      | none => lookupGlobal I c y
    | some (.cell a) => match c.cells[a]? with
      | some v => .ok v
      | none => .error (unboundErr f x)
    | none => .error errName
  match k, r with
  | some k, .error _ => .error (Py.err k)
  | _, r => r

/-- `__annotations__` as a module or class body reads it (`LOAD_NAME`: the class
namespace, then the module dictionary and the builtins), whatever its classification. -/
def annRead (I : Py.Interp σ) (c : Config σ) (f : Frame σ) : Except Val Val :=
  match f.kind, f.ns.lookup "__annotations__" with
  | .cls, some v => .ok v
  | _, _ => lookupGlobal I c "__annotations__"

/-- `del` of an unset name: `UnboundLocalError` for a local cell, `NameError` for a
free cell, a global (`DELETE_GLOBAL`), or a class namespace entry (`DELETE_NAME`). -/
def delErr (f : Frame σ) (x : Name) : Place → Val
  | .cell _ => unboundErr f x
  | _ => errName

def isSet (c : Config σ) (f : Frame σ) : Place → Bool
  | .glob y => (c.glob y).isSome
  | .ns y => (f.ns.lookup y).isSome
  | .cell a => (c.cells[a]?).isSome

def writeAt (c : Config σ) (f : Frame σ) (ov : Option Val) : Place → Config σ × Frame σ
  | .glob y => ({ c with globW := c.globW.insert y ov }, f)
  | .ns y => (c, { f with ns := nsSet f.ns y ov })
  | .cell a => ({ c with cells := match ov with
                  | some v => c.cells.insert a v
                  | none => c.cells.erase a }, f)

/-- The cell `f` holds for `x`: its own for a local name of a function frame,
else the one its closure environment holds. -/
def cellOf (f : Frame σ) (x : Name) : Option Addr :=
  match f.kind with
  | .fn | .gen _ => if f.cls x = .loc then some (f.id, x) else f.κ x
  | _ => f.κ x

/-- κ of `Close`: `f`'s cells of the free names of the new scope `S`. -/
def capture (f : Frame σ) (S : Scope) : Name → Option Addr :=
  fun x => if clsOf (S :: f.chain) x = .free then cellOf f x else none

/-- The exception of the innermost handler running in a frame's continuation:
one entered (`handler`) or one whose expression is being evaluated or matched
(`catchS`, `catchT`). -/
def kontExc : List (Kont σ) → Option Val
  | [] => none
  | .handler _ h :: _ => some h
  | .catchS h _ _ _ _ :: _ => some h
  | .catchT h _ _ _ _ :: _ => some h
  | _ :: ks => kontExc ks

/-- The exception the innermost running handler of the stack handles: CPython's
topmost exception state. A call shares its caller's; a suspended generator's
handlers stay in its frame and come back with it. -/
def curExc : List (Frame σ) → Option Val
  | [] => none
  | f :: fs => match kontExc f.kont with
    | some h => some h
    | none => curExc fs

/-- An exception raised while `oh` is handled takes it as its `__context__`. -/
def withCtx : Option Val → Val → Val
  | some h, v => v.setCtx h
  | none, v => v

/-- Raise a new exception with the stack `st`. -/
def raiseNew (st : List (Frame σ)) (v : Val) : Ctrl σ := .raise (withCtx (curExc st) v)

def resCtrl (st : List (Frame σ)) : Except Val Val → Ctrl σ
  | .ok v => .val v
  | .error v => raiseNew st v

/-- The cells of a new frame `n`: its bound parameters. -/
def initCells (cs : Std.HashMap Addr Val) (n : Nat) (bound : List (Name × Val)) : Std.HashMap Addr Val :=
  bound.foldl (fun m p => m.insert (n, p.1) p.2) cs

/-- A class's namespace without the names starting with a dot, which no program can
write and the translation reserves for its fresh names. -/
def dropReserved (ns : List (Name × Val)) : List (Name × Val) :=
  ns.filter fun p => !p.1.startsWith "."

/-- The items of an argument record (`$args`); any other argument is one item. -/
def argList : Val → List Val
  | .data "$args" vs => vs
  | v => [v]

/-- The value of a `StopIteration`. -/
def stopVal (v : Val) : Val := Py.stopValue v

def isStop (v : Val) : Bool := Py.isStop v

/-- The class statement's arguments, as `$cls` leaves them in the frame's namespace
under the reserved key `.`. -/
def clsStash (ds args : List Val) (kws : List (Name × Val)) : Val :=
  .data "$cls" [.tuple ds, .tuple args, .tuple (kws.map fun p => .tuple [.str p.1, p.2])]

def clsUnstash : Option Val → List Val × List Val × List (Name × Val)
  | some (.data "$cls" [.tuple ds, .tuple args, .tuple kvs]) => (ds, args, (Py.kwPairs kvs).getD [])
  | _ => ([], [], [])

/-- A constant's value with the continuation it goes to. A handler clause's expression
`$stop` or `$any` matches the pending exception by the core: a `StopIteration`, or
anything. -/
def constK (I : Py.Interp σ) (k : String) : List (Kont σ) → Ctrl σ × List (Kont σ)
  | .catchS ex x hb hs u :: ks =>
    if k = "$stop" then (.val (.bool (isStop ex)), .catchT ex x hb hs u :: ks)
    else if k = "$any" then (.val (.bool true), .catchT ex x hb hs u :: ks)
    else (.val (Py.constVal I k), .catchS ex x hb hs u :: ks)
  | ks => (.val (Py.constVal I k), ks)

/-! ## Steps -/

section
variable (I : Py.Interp σ) (c : Config σ) (f : Frame σ) (fs : List (Frame σ))

def top (f' : Frame σ) : Option (Config σ) := some { c with stack := f' :: fs }

/-- Set the frame's control and continuation. -/
def setC (ctl : Ctrl σ) (ks : List (Kont σ)) : Option (Config σ) :=
  top c fs { f with ctrl := ctl, kont := ks }

/-- A truth test of `v` with continuation `ks`: `Val.no` is false and `bool b` is `b`
by the core semantics; any other value goes to the interpretation. -/
def tst (v : Val) (ks : List (Kont σ)) : Option (Config σ) :=
  match v with
  | .no => top c fs { f with ctrl := .val (.bool false), kont := ks }
  | .bool b => top c fs { f with ctrl := .val (.bool b), kont := ks }
  | v => top c fs { f with ctrl := .op .truth [v], kont := ks }

/-- Give the caller (the next frame) a control. -/
def retTo (fs : List (Frame σ)) (ctl : Ctrl σ) : Option (Config σ) :=
  match fs with
  | g :: gs => some { c with stack := { g with ctrl := ctl } :: gs }
  | [] => none

/-- A generator `o` ends: it is marked ended and its caller gets `ctl`. -/
def genEnd (fs : List (Frame σ)) (o : Nat) (ctl : Ctrl σ) : Option (Config σ) :=
  match fs with
  | g :: gs => some { c with stack := { g with ctrl := ctl } :: gs,
                             objs := c.objs.insert o (.gen .done) }
  | [] => none

/-- `End`: the class body's namespace goes to the caller, which makes the class. -/
def classEnd (fs : List (Frame σ)) (ns : List (Name × Val)) : Option (Config σ) :=
  retTo c fs (.ns (dropReserved ns))

/-- Store `v` in `x`, then continue with `after` (`Store`). -/
def store (x : Name) (v : Val) (after : Ctrl σ) : Option (Config σ) :=
  match place f x with
  | some pl =>
    let r := writeAt c f (some v) pl
    some { r.1 with stack := { r.2 with ctrl := after } :: fs }
  | none => top c fs { f with ctrl := raiseNew (f :: fs) errName }

/-- Unset `x` (a handler's exit), then continue with `ctl` and `ks`. -/
def unsetThen (x : Name) (ctl : Ctrl σ) (ks : List (Kont σ)) : Option (Config σ) :=
  match place f x with
  | some pl =>
    let r := writeAt c f none pl
    some { r.1 with stack := { r.2 with ctrl := ctl, kont := ks } :: fs }
  | none => top c fs { f with ctrl := ctl, kont := ks }

/-- The start of a class body `g` (of qualified name `q`), before its code:
`__module__ = __name__`, then `__qualname__ = 'q'`, each through the body's own
classification, as CPython's compiler emits them; a failed read or store raises
in the body. `fs` holds the caller. -/
def classStart (I : Py.Interp σ) (c : Config σ) (g : Frame σ) (fs : List (Frame σ)) (q : String) :
    Option (Config σ) :=
  let fail (c' : Config σ) (g' : Frame σ) (e : Val) : Option (Config σ) :=
    some { c' with stack := { g' with ctrl := raiseNew (g :: fs) e } :: fs }
  match readName I c g "__name__" none with
  | .error e => fail c g e
  | .ok m => match place g "__module__" with
    | none => fail c g errName
    | some p1 =>
      let r1 := writeAt c g (some m) p1
      match place r1.2 "__qualname__" with
      | none => fail r1.1 r1.2 errName
      | some p2 =>
        let r2 := writeAt r1.1 r1.2 (some (I.const s!"'{q}'")) p2
        some { r2.1 with stack := r2.2 :: fs }

/-- `Close`: allocate the closure of `S` (its classification and cells cached) and
give its reference. -/
def close (S : Scope) (k : List (Kont σ)) : Option (Config σ) :=
  let xs := S.names
  let cl := (Py.memo xs (clsOf (S :: f.chain))).get
  some { c with
    stack := { f with ctrl := .val (.fn c.next), kont := k } :: fs
    objs := c.objs.insert c.next (.clo S f.chain cl ((Py.memo xs (capture f S)).get) none)
    next := c.next + 1 }

/-- Entering an expression. -/
def evalStep : Expr → Option (Config σ)
  | .const _ k => top c fs { f with ctrl := (constK I k f.kont).1, kont := (constK I k f.kont).2 }
  | .name _ x k => top c fs { f with ctrl := resCtrl (f :: fs) (readName I c f x k) }
  | .bin _ op a b => top c fs { f with ctrl := .ev a, kont := .binL op b :: f.kont }
  | .call _ a b => top c fs { f with ctrl := .ev a, kont := .callF b :: f.kont }
  | .lam l k x b => close c f fs (.fn l k x b) f.kont
  | .walrus _ x e => top c fs { f with ctrl := .ev e, kont := .walrus x :: f.kont }
  | .yield _ e => top c fs { f with ctrl := .ev e, kont := .yieldS :: f.kont }
  | .cond _ e a b => top c fs { f with ctrl := .ev e, kont := .condK a b :: f.kont }
  | .bool _ o a b => top c fs { f with ctrl := .ev a, kont := .boolK o b :: f.kont }
  | .yieldFrom _ e => top c fs { f with ctrl := .ev e, kont := .yfStart :: f.kont }

/-- Entering a statement; the rest of the block waits as `seq`. -/
def execStep (s : Stmt) (ss : List Stmt) : Option (Config σ) :=
  let k := Kont.seq ss :: f.kont
  match s with
  | .assign _ x e => top c fs { f with ctrl := .ev e, kont := .assign x :: k }
  | .del _ x => match place f x with
    | some pl =>
      if isSet c f pl then
        let r := writeAt c f none pl
        some { r.1 with stack := { r.2 with ctrl := .exec [], kont := k } :: fs }
      else top c fs { f with ctrl := raiseNew (f :: fs) (delErr f x pl), kont := k }
    | none => top c fs { f with ctrl := raiseNew (f :: fs) errName, kont := k }
  | .expr _ e => top c fs { f with ctrl := .ev e, kont := .exprS :: k }
  | .ite _ e t u => top c fs { f with ctrl := .ev e, kont := .ifS t u :: k }
  | .while _ e b u => top c fs { f with ctrl := .ev e, kont := .whileS e b u :: k }
  | .ret _ e => top c fs { f with ctrl := .ev e, kont := .retS :: k }
  | .defn l g x b => close c f fs (.fn l false x b) (.assign g :: k)
  | .glob _ _ | .nonloc _ _ => top c fs { f with ctrl := .exec [], kont := k }
  | .print _ e => top c fs { f with ctrl := .ev e, kont := .printS :: k }
  | .raise _ e => top c fs { f with ctrl := .ev e, kont := .raiseS :: k }
  | .tryE _ b hs u => top c fs { f with ctrl := .exec b, kont := .tryE hs u :: k }
  | .brk _ => top c fs { f with ctrl := .brk, kont := k }
  | .cont _ => top c fs { f with ctrl := .cont, kont := k }
  -- `Class`: run the body on a fresh namespace, with the arguments `$cls` left (none
  -- if it left none); the class it makes waits to be stored
  | .cls l x q b =>
    let a := clsUnstash (f.ns.lookup ".")
    classStart I { c with next := c.next + 1 }
      { id := c.next, chain := .cl l b :: f.chain, kind := .cls,
        cls := (Py.memo (Scope.cl l b).names (clsOf (.cl l b :: f.chain))).get, κ := cellOf f,
        ns := [], ctrl := .exec b, kont := [] }
      ({ f with ns := nsSet f.ns "." none, ctrl := .wait,
                kont := .clsEnd x q a.2.1 a.2.2 a.1 :: .assign x :: k } :: fs) q

/-- Enter the closure of scope `S`: a frame (or, for a generator, a generator object
holding it) whose cells hold the bound parameters. -/
def enter (S : Scope) (C : List Scope) (cl : Name → Cls) (κ : Name → Option Addr)
    (bound : List (Name × Val)) : Option (Config σ) :=
  match S with
  | .fn _ _ _ b =>
    let fr : Frame σ := { id := c.next, chain := S :: C, kind := .fn, cls := cl, κ := κ, ns := [],
                          ctrl := .exec b, kont := [] }
    match S.kind with
    | .plain =>
      some { c with
        stack := fr :: { f with ctrl := .wait } :: fs
        cells := initCells c.cells c.next bound
        next := c.next + 1 }
    | .gen =>
      -- `Gen`: a generator object holding the new frame, suspended
      some { c with
        stack := { f with ctrl := .val (.gen c.next) } :: fs
        objs := c.objs.insert c.next (.gen (.susp { fr with kind := .gen c.next }))
        cells := initCells c.cells c.next bound
        next := c.next + 1 }
  | .cl _ _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }

/-- A call of the closure `o` (`f` is the caller with the call's continuation popped).
Without a signature it takes one argument as its parameter; with one, the arguments
are bound by `Py.bindArgs` (a `**` parameter's dictionary made first), and a binding
error raises in the caller. -/
def callFn (o : Nat) (args : List Val) (kws : List (Name × Val)) : Option (Config σ) :=
  match c.objs[o]? with
  | some (.clo S C cl κ sg) => match S, sg with
    | .fn _ _ x _, none => match args with
      | [va] => enter c f fs S C cl κ [(x, va)]
      | _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }
    | .fn .., some (sig, dflt) => match Py.bindArgs sig dflt args kws with
      | .error e => top c fs { f with ctrl := raiseNew (f :: fs) e }
      | .ok (bound, none) => enter c f fs S C cl κ bound
      | .ok (bound, some (kx, items)) =>
        top c fs { f with ctrl := .op (.display (.dict (items.map fun _ => false)))
                                    (items.flatMap fun p => [.str p.1, p.2]),
                          kont := .enterK o bound kx :: f.kont }
    | .cl .., _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }
  | _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }

/-- The arguments of a call or class statement are ready. -/
def finishArgs (t : ArgsT) (args : List Val) (kvs : List (Name × Val)) (ks : List (Kont σ)) :
    Option (Config σ) :=
  match t with
  | .call g => top c fs { f with ctrl := .call g args kvs, kont := ks }
  | .cls ds => top c fs { f with ns := nsSet f.ns "." (some (clsStash ds args kvs)),
                                 ctrl := .val .none, kont := ks }

/-- The keyword phase (`**m` items expanded by the interpretation). -/
def kwPhase (t : ArgsT) (args : List Val) (kws : List (Option Name)) (kwvals : List Val)
    (ks : List (Kont σ)) : Option (Config σ) :=
  if kws.any Option.isNone then
    top c fs { f with ctrl := .op (.display (.kwargs kws)) kwvals, kont := .argKw t args :: ks }
  else finishArgs c f fs t args ((kws.filterMap id).zip kwvals) ks

/-- The positional phase (`*e` items expanded by the interpretation). -/
def argPhase (t : ArgsT) (args : List Val) (stars : List Bool) (kws : List (Option Name))
    (kwvals : List Val) (ks : List (Kont σ)) : Option (Config σ) :=
  if stars.any id then
    top c fs { f with ctrl := .op (.display (.tuple stars)) args, kont := .argStar t kws kwvals :: ks }
  else kwPhase c f fs t args kws kwvals ks

/-- `$setup` in a class body: `__annotations__ = d` in its namespace unless set. -/
def setupNs (d : Val) : Option (Config σ) :=
  if (f.ns.lookup "__annotations__").isSome then top c fs { f with ctrl := .val .none }
  else top c fs { f with ns := nsSet f.ns "__annotations__" (some d), ctrl := .val .none }

/-- `$setup` elsewhere: `__annotations__ = d` in the module dictionary unless set. -/
def setupGlob (d : Val) : Option (Config σ) :=
  if (c.glob "__annotations__").isSome then top c fs { f with ctrl := .val .none }
  else some { c with globW := c.globW.insert "__annotations__" (some d),
                     stack := { f with ctrl := .val .none } :: fs }

/-- `from m import *`'s names into the module dictionary (but the reserved ones, with a dot,
which no module can define). -/
def starGlob (kvs : List (Name × Val)) : Option (Config σ) :=
  some { c with globW := (kvs.filter (!·.1.startsWith ".")).foldl (fun g p => g.insert p.1 (some p.2)) c.globW,
                stack := { f with ctrl := .val .none } :: fs }

/-- `from m import *`'s names into a class namespace (but the reserved ones). -/
def starNs (kvs : List (Name × Val)) : Option (Config σ) :=
  top c fs { f with ns := (kvs.filter (!·.1.startsWith ".")).foldl (fun n p => nsSet n p.1 (some p.2)) f.ns,
                    ctrl := .val .none }

/-- A gadget on the items `vs` of its argument record. -/
def gadgetStep (g : Gadget) (vs : List Val) : Option (Config σ) :=
  let ks := f.kont
  let val (v : Val) := top c fs { f with ctrl := .val v }
  match g with
  | .call => match vs with
    | fv :: rest => match (Py.pairs rest).bind Py.splitArgs with
      | some (st, args, kws, kwvals) => argPhase c f fs (.call fv) args st kws kwvals ks
      | none => none
    | [] => none
  | .defn nd np =>
    match vs.getLast?, ((vs.dropLast).drop (vs.length - 1 - np)).mapM Py.markParam with
    | some (.fn o), some sig => match c.objs[o]? with
      | some (.clo S C cl κ _) =>
        let dflt := Py.alignDefaults (sig.map (·.2.2))
          ((vs.drop nd).take (sig.filter (·.2.2)).length)
        some { c with
          objs := c.objs.insert o (.clo S C cl κ (some (sig.map fun p => (p.1, p.2.1), dflt)))
          stack := { f with ctrl := .val (.fn o), kont := .decos (vs.take nd).reverse :: ks } :: fs }
      | _ => none
    | _, _ => none
  | .cls nd => match (Py.pairs (vs.drop nd)).bind Py.splitArgs with
    | some (st, args, kws, kwvals) => argPhase c f fs (.cls (vs.take nd)) args st kws kwvals ks
    | none => none
  | .unpack => match vs with
    | v :: ms => match ms.mapM Py.markStar with
      | some st =>
        if (st.filter id).length > 1 then none else
        top c fs { f with ctrl := .op (.unpack (Py.starShape st).1 (Py.starShape st).2.1
                                        (Py.starShape st).2.2) [v],
                          kont := .unpackK ms.length :: ks }
      | none => none
    | [] => none
  | .display k => match Py.pairs vs with
    | some ps => match ps.mapM (Py.markStar ·.1) with
      | some st =>
        let d : Py.Disp := if k = "list" then .list st else if k = "tuple" then .tuple st
          else if ps.length > 2 && ps.all (Py.markConst ·.1) then .constSet else .set st
        top c fs { f with ctrl := .op (.display d) (ps.map (·.2)) }
      | none => none
    | none => none
  | .cunary op => match vs with
    | [m] => val (.prim (match m with
        | .prim "$c0" => if op == "USub" || op == "UAdd" || op == "Invert" then "$c1" else "$nc"
        | _ => "$nc"))
    | _ => none
  | .ctuple => val (.prim (if vs.all Py.markConst then "$c1" else "$nc"))
  | .setup => match vs with
    | [d] => match f.kind with
      | .cls => setupNs c f fs d
      | _ => setupGlob c f fs d
    | _ => none
  | .annot x => match vs with
    | [a] => match annRead I c f with
      | .ok d => top c fs { f with ctrl := .op .setitem [d, .str x, a] }
      | .error e => top c fs { f with ctrl := raiseNew (f :: fs) e }
    | _ => none
  | .starstore => match vs with
    | [v] => match v with
      | .tuple ps => match Py.kwPairs ps, f.kind with
        | some kvs, .mod => starGlob c f fs kvs
        | some kvs, .cls => starNs c f fs kvs
        | _, _ => none
      | _ => none
    | _ => none
  | .reraise => match curExc (f :: fs) with
    | some h => top c fs { f with ctrl := .raise h }
    | none => top c fs { f with ctrl := raiseNew (f :: fs) errRuntime }
  | .raiseK k => top c fs { f with ctrl := raiseNew (f :: fs) (.err k vs) }
  | .raiseFrom => match vs with
    | [e, cv] => top c fs { f with ctrl := .op .mkExc [e], kont := .raiseC cv :: ks }
    | _ => none
  | .item i => match vs with
    | [v] => match v with
      | .tuple ws => ws[i]?.bind val
      | _ => none
    | _ => none
  | .set x => match vs with
    | [v] => some { c with cells := c.cells.insert (f.id, x) v, stack := { f with ctrl := .val v } :: fs }
    | _ => none
  | .get x => match vs with
    | [] => c.cells[(f.id, x)]?.bind val
    | _ => none
  | .stuck => none

/-- `Call` of `vf` on the argument `va`; `f` is the caller with the call's
continuation popped. A closure gets `va` as its argument; `next` resumes a
generator or asks the interpretation for an iterator's next item; an operation
(`$op:…`) is performed, and a gadget's call by the core, on the items of the
argument record; anything else is the interpretation's call. -/
def callStep (vf va : Val) : Option (Config σ) :=
  match vf with
  | .fn o => callFn c f fs o [va] []
  | .next => match va with
    | .gen o => match c.objs[o]? with
      | some (.gen (.susp g)) =>
        -- `Next`: push the suspended frame, mark the generator running
        some { c with stack := g :: { f with ctrl := .wait } :: fs,
                      objs := c.objs.insert o (.gen .running) }
      | some (.gen .running) => top c fs { f with ctrl := raiseNew (f :: fs) errValue }
      | some (.gen .done) => top c fs { f with ctrl := raiseNew (f :: fs) (Py.stopOf .none) }
      | _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }
    | va => top c fs { f with ctrl := .op .next [va] }
  | .op o => top c fs { f with ctrl := .op o (argList va) }
  | .prim k => match Gadget.ofName k with
    | some g => gadgetStep I c f fs g (argList va)
    | none => top c fs { f with ctrl := .op (.call []) (vf :: argList va) }
  | vf => top c fs { f with ctrl := .op (.call []) (vf :: argList va) }

/-- A call with positional and keyword arguments (a gadget's, a decorator's, or one the
interpretation asked for): a closure binds them, `next` takes one, an operation
takes positional ones; anything else goes to the interpretation. -/
def callArgs (vf : Val) (args : List Val) (kws : List (Name × Val)) : Option (Config σ) :=
  match vf with
  | .fn o => callFn c f fs o args kws
  | .next => match args, kws with
    | [va], [] => callStep I c f fs .next va
    | _, _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }
  | .op o => if kws.isEmpty then top c fs { f with ctrl := .op o args }
    else top c fs { f with ctrl := raiseNew (f :: fs) errType }
  | vf => top c fs { f with ctrl := .op (.call (kws.map (·.1))) (vf :: args ++ kws.map (·.2)) }

/-- A value delivered to the frame's continuation. -/
def valStep (v : Val) : Option (Config σ) :=
  match f.kont with
  | .binL op b :: ks => top c fs { f with ctrl := .ev b, kont := .binR op v :: ks }
  | .binR op v1 :: ks => match op, v1 with
    | ",", .data "$args" vs => top c fs { f with ctrl := .val (.data "$args" (vs ++ [v])), kont := ks }
    | _, _ => top c fs { f with ctrl := .op (.binop op) [v1, v], kont := ks }
  | .callF b :: ks => top c fs { f with ctrl := .ev b, kont := .callA v :: ks }
  | .callA vf :: ks => callStep I c { f with kont := ks } fs vf v
  | .walrus x :: ks => store c { f with kont := ks } fs x v (.val v)
  | .assign x :: ks => store c { f with kont := ks } fs x v (.exec [])
  | .exprS :: ks => top c fs { f with ctrl := .exec [], kont := ks }
  | .printS :: ks =>
    some { c with stack := { f with ctrl := .exec [], kont := ks } :: fs, out := c.out ++ [v] }
  | .ifS t u :: ks => tst c f fs v (.ifT t u :: ks)
  | .ifT t u :: ks => match v with
    | .bool b => top c fs { f with ctrl := .exec (if b then t else u), kont := ks }
    | _ => none
  | .whileS e b u :: ks => tst c f fs v (.whileT e b u :: ks)
  | .whileT e b u :: ks => match v with
    | .bool true => top c fs { f with ctrl := .exec b, kont := .loop e b u :: ks }
    | .bool false => top c fs { f with ctrl := .exec u, kont := ks }
    | _ => none
  | .retS :: ks => top c fs { f with ctrl := .retv v, kont := ks }
  | .raiseS :: ks => top c fs { f with ctrl := .op .mkExc [v], kont := .raiseE :: ks }
  | .raiseE :: ks => top c fs { f with ctrl := raiseNew (f :: fs) v, kont := ks }
  -- the handler's expression gave `v`: ask whether it handles the exception
  | .catchS ex x hb hs u :: ks => top c fs { f with ctrl := .op .excMatch [ex, v], kont := .catchT ex x hb hs u :: ks }
  -- enter on a match, setting `x`, else try the next
  | .catchT ex x hb hs u :: ks => match v with
    | .bool true => store c { f with kont := .handler x ex :: ks } fs x ex (.exec hb)
    | .bool false => top c fs { f with ctrl := .raise ex, kont := .tryE hs u :: ks }
    | _ => none
  | .condK a b :: ks => tst c f fs v (.condT a b :: ks)
  | .condT a b :: ks => match v with
    | .bool t => top c fs { f with ctrl := .ev (if t then a else b), kont := ks }
    | _ => none
  | .boolK o b :: ks => tst c f fs v (.boolT o v b :: ks)
  | .boolT o a b :: ks => match v with
    | .bool t => if t == o then top c fs { f with ctrl := .ev b, kont := ks }
      else top c fs { f with ctrl := .val a, kont := ks }
    | _ => none
  -- `yield from`: a generator object is the delegate itself, anything else is iterated
  | .yfStart :: ks => match v with
    | .gen o => top c fs { f with ctrl := .yfStep (.gen o), kont := ks }
    | v => top c fs { f with ctrl := .op .iter [v], kont := .yfIt :: ks }
  | .yfIt :: ks => match v with
    | .gen o => top c fs { f with ctrl := .yfStep (.gen o), kont := ks }
    | v => top c fs { f with ctrl := .yfStep (.it v), kont := ks }
  -- the delegate gave `v`: yield it; on resumption, ask the delegate again
  | .yfGot d :: ks => match f.kind, fs with
    | .gen o, g :: gs =>
      some { c with stack := { g with ctrl := .val v } :: gs,
                    objs := c.objs.insert o (.gen (.susp { f with ctrl := .yfStep d, kont := ks })) }
    | _, _ => none
  -- `Yield`: the frame goes back to its generator, its pending yield to give None
  | .yieldS :: ks => match f.kind, fs with
    | .gen o, g :: gs =>
      some { c with stack := { g with ctrl := .val v } :: gs,
                    objs := c.objs.insert o (.gen (.susp { f with ctrl := .val .none, kont := ks })) }
    | _, _ => none
  | .native k :: ks => top c fs { f with ctrl := .kapp k (.ok v), kont := ks }
  | .argStar t kws kwvals :: ks => match v with
    | .tuple args => kwPhase c f fs t args kws kwvals ks
    | _ => none
  | .argKw t args :: ks => match v with
    | .tuple pairs => match Py.kwPairs pairs with
      | some kvs => finishArgs c f fs t args kvs ks
      | none => none
    | _ => none
  | .enterK o bound kx :: ks => match c.objs[o]? with
    | some (.clo S C cl κ _) => enter c { f with kont := ks } fs S C cl κ (bound ++ [(kx, v)])
    | _ => none
  | .decos (d :: ds) :: ks => top c fs { f with ctrl := .call d [v] [], kont := .decos ds :: ks }
  | .decos [] :: ks => top c fs { f with ctrl := .val v, kont := ks }
  | .raiseC cv :: ks => match cv with
    | .none => top c fs { f with ctrl := raiseNew (f :: fs) (Py.setCause v .none), kont := ks }
    | cv => top c fs { f with ctrl := .op .mkExc [cv], kont := .raiseW v :: ks }
  | .raiseW e :: ks => top c fs { f with ctrl := raiseNew (f :: fs) (Py.setCause e v), kont := ks }
  | .unpackK n :: ks => match v with
    | .tuple ws => if ws.length = n then top c fs { f with ctrl := .val (.tuple ws), kont := ks } else none
    | _ => none
  | _ => none

/-- A statement or block has ended (`f[∘]`). -/
def doneStep : Option (Config σ) :=
  match f.kont with
  | .seq ss :: ks => top c fs { f with ctrl := .exec ss, kont := ks }
  | .loop e b u :: ks => top c fs { f with ctrl := .ev e, kont := .whileS e b u :: ks }
  -- the body of a `try` ended: its `else` block runs, outside its handlers
  | .tryE _ u :: ks => top c fs { f with ctrl := .exec u, kont := ks }
  | .handler x _ :: ks => unsetThen c f fs x (.exec []) ks
  | [] => match f.kind with
    | .mod => some { c with stack := [], res := some (.ok ()) }
    | .fn => retTo c fs (.val .none)
    | .gen o => genEnd c fs o (raiseNew fs (Py.stopOf .none))
    | .cls => classEnd c fs f.ns
  | _ => none

/-- An exception evaluates the next handler's expression (`Catch`), leaves a
running handler (unsetting its name, and taking the handled exception as its
context), or passes the rest of the frame's continuation, then unwinds (`Unwind`). -/
def raiseStep (v : Val) : Option (Config σ) :=
  match f.kont with
  | .tryE (.mk _ h x hb :: hs) u :: ks =>
    top c fs { f with ctrl := .ev h, kont := .catchS v x hb hs u :: ks }
  | .catchS .. :: ks => top c fs { f with kont := ks }
  -- the delegate's `StopIteration` gives `yield from` its value
  | .yfGot _ :: ks =>
    if isStop v then top c fs { f with ctrl := .val (stopVal v), kont := ks }
    else top c fs { f with kont := ks }
  | .handler x _ :: ks => unsetThen c f fs x (.raise v) ks
  | .native k :: ks => top c fs { f with ctrl := .kapp k (.error v), kont := ks }
  | _ :: ks => top c fs { f with kont := ks }
  | [] => match f.kind with
    | .mod => some { c with stack := [], res := some (.error v) }
    | .fn => retTo c fs (.raise v)
    -- `RuntimeError` takes the `StopIteration` as its context and cause
    | .gen o => genEnd c fs o (.raise (if isStop v then .exn errRuntime v v else v))
    | .cls => retTo c fs (.raise v)

/-- A return passes the frame's continuation, then leaves it (`Return`). -/
def retStep (v : Val) : Option (Config σ) :=
  match f.kont with
  | .handler x _ :: ks => unsetThen c f fs x (.retv v) ks
  | _ :: ks => top c fs { f with kont := ks }
  | [] => match f.kind with
    | .fn => retTo c fs (.val v)
    | .gen o => genEnd c fs o (raiseNew fs (Py.stopOf v))
    | _ => none

/-- `yield from` advances its delegate: a generator by `Next` (the delegating frame
waits for its value or its `StopIteration`), an iterator of the interpretation by
its `next` (a `StopIteration` ends the iteration). -/
def yfStepS (d : Deleg) : Option (Config σ) :=
  match d with
  | .gen o => match c.objs[o]? with
    | some (.gen (.susp g)) =>
      some { c with stack := g :: { f with ctrl := .wait, kont := .yfGot d :: f.kont } :: fs,
                    objs := c.objs.insert o (.gen .running) }
    | some (.gen .running) => top c fs { f with ctrl := raiseNew (f :: fs) errValue }
    | some (.gen .done) => top c fs { f with ctrl := .val .none }
    | _ => top c fs { f with ctrl := raiseNew (f :: fs) errType }
  | .it v => top c fs { f with ctrl := .op .next [v], kont := .yfGot d :: f.kont }

/-- A `break` passes the frame's continuation up to its innermost loop, which it
leaves (skipping the loop's `else`), unsetting the name of each handler it leaves. -/
def brkStep : Option (Config σ) :=
  match f.kont with
  | .loop _ _ _ :: ks => top c fs { f with ctrl := .exec [], kont := ks }
  | .handler x _ :: ks => unsetThen c f fs x .brk ks
  | _ :: ks => top c fs { f with kont := ks }
  | [] => none

/-- A `continue` passes the frame's continuation up to its innermost loop, whose
condition it evaluates again. -/
def contStep : Option (Config σ) :=
  match f.kont with
  | .loop e b u :: ks => top c fs { f with ctrl := .ev e, kont := .whileS e b u :: ks }
  | .handler x _ :: ks => unsetThen c f fs x .cont ks
  | _ :: ks => top c fs { f with kont := ks }
  | [] => none

/-- A class body's namespace reaches its caller, which makes the class; its
decorators apply next. -/
def nsStep (ns : List (Name × Val)) : Option (Config σ) :=
  match f.kont with
  | .clsEnd x q bases kws ds :: ks =>
    top c fs { f with ctrl := .op (.mkClass x q (kws.map (·.1)) (ns.map (·.1)))
                                (bases ++ kws.map (·.2) ++ ns.map (·.2)),
                      kont := .decos ds.reverse :: ks }
  | _ => none

end

/-- An interpretation's result: a value, a new exception (with its context), an
exception passed on, or a call it asks for before its native continuation. The
configuration is taken apart first, so that the interpretation owns its state. -/
def handle (objs : Std.HashMap Nat (Obj σ)) (cells : Std.HashMap Addr Val)
    (glob0 : Name → Option Val) (globW : Std.HashMap Name (Option Val)) (out : List Val) (next : Nat)
    (res : Option (Except Val Unit)) (f : Frame σ) (fs : List (Frame σ)) (r : Res σ) : Config σ :=
  let mk (s : σ) (g : Frame σ) : Config σ :=
    { stack := g :: fs, objs, cells, glob0, globW, out, next, res, st := s }
  match r with
  | .ok s v => mk s { f with ctrl := .val v }
  | .raise s e => mk s { f with ctrl := raiseNew (f :: fs) e }
  | .reraise s e => mk s { f with ctrl := .raise e }
  | .call s g args kws k => mk s { f with ctrl := .call g args kws, kont := .native k :: f.kont }

def step (I : Py.Interp σ) (c : Config σ) : Option (Config σ) :=
  match c.stack with
  | [] => none
  | f :: fs =>
    match f.ctrl with
    | .ev e => evalStep I c f fs e
    | .exec [] => doneStep c f fs
    | .exec (s :: ss) => execStep I c f fs s ss
    | .val v => valStep I c f fs v
    | .raise v => raiseStep c f fs v
    | .retv v => retStep c f fs v
    | .wait => none
    | .brk => brkStep c f fs
    | .cont => contStep c f fs
    | .yfStep d => yfStepS c f fs d
    | .op o vs => match c with
      | { stack := _, objs, cells, glob0, globW, out, next, res, st } =>
        some (handle objs cells glob0 globW out next res f fs (I.op st o vs))
    | .kapp k r => match c with
      | { stack := _, objs, cells, glob0, globW, out, next, res, st } =>
        some (handle objs cells glob0 globW out next res f fs (k st r))
    | .call g args kws => callArgs I c { f with ctrl := .wait } fs g args kws
    | .ns ns => nsStep c f fs ns

/-- The node a step evaluates when it enters it: an expression or statement, or
the handler clause whose expression `Catch` evaluates. Steps that continue a node already
entered evaluate no new node. -/
def focus (c : Config σ) : Option Label :=
  match c.stack with
  | f :: _ => match f.ctrl with
    | .ev e => some e.label
    | .exec (s :: _) => some s.label
    | .raise _ => match f.kont with
      | .tryE (.mk lh _ _ _ :: _) _ :: _ => some lh
      | _ => none
    | _ => none
  | [] => none

/-! ## Executions -/

/-- `n` steps, stopping where the execution ends. -/
def run (I : Py.Interp σ) : Nat → Config σ → Config σ
  | 0, c => c
  | n + 1, c => match step I c with
    | some c' => run I n c'
    | none => c

/-- The module frame of `p`. -/
def modFrame (p : List Stmt) : Frame σ :=
  { id := 0, chain := [], kind := .mod, cls := fun _ => .glob, κ := fun _ => none, ns := [],
    ctrl := .exec p, kont := [] }

/-- The input is the initial module dictionary, and the interpretation's initial state. -/
def init (p : List Stmt) (g : Name → Option Val) (s : σ) : Config σ where
  stack := [modFrame p]
  objs := {}
  cells := {}
  glob0 := g
  globW := {}
  out := []
  next := 1
  res := none
  st := s

/-- What an ended execution shows: its output, final module dictionary (where
a test harness keeps return values) and interpretation state, or its output,
state and uncaught exception. A configuration that cannot step but has frames left
is `stuck`. -/
inductive Outcome (σ : Type) where
  | normal (out : List Val) (glob : Name → Option Val) (st : σ)
  | exc (v : Val) (out : List Val) (st : σ)
  | stuck (out : List Val) (st : σ)

def outcome (c : Config σ) : Outcome σ :=
  match c.stack, c.res with
  | [], some (.ok ()) => .normal c.out c.glob c.st
  | [], some (.error v) => .exc v c.out c.st
  | _, _ => .stuck c.out c.st

def Terminates (I : Py.Interp σ) (c : Config σ) (o : Outcome σ) : Prop :=
  ∃ n, step I (run I n c) = none ∧ outcome (run I n c) = o

def Diverges (I : Py.Interp σ) (c : Config σ) : Prop := ∀ n, step I (run I n c) ≠ none

/-- The execution from `c` evaluates no node whose label is in `F`. -/
def NoReach (I : Py.Interp σ) (F : Label → Prop) (c : Config σ) : Prop :=
  ∀ n l, focus (run I n c) = some l → ¬ F l

end PyCore
