/-
Values and the interpretation interface shared by PyCore and Surf.

The core semantics (PyCore's or Surf's) owns names, frames, cells, closures and
generators; everything else is an interpretation `Interp σ`: constants, the
builtins' namespace, and one entry point `op` for every operation on values
(operators, truth, iteration, attributes, subscripts, calls of what is not a
user function, displays, class creation, imports, exception matching). The
interpretation has a state `σ` (its heap, the output, the input) that every
operation threads. An operation either ends (`Res.ok`, `Res.raise`,
`Res.reraise`) or asks the core to call a value and to hand the outcome to a
native continuation (`Res.call`), which is how `sum(genexp)`,
`sorted(key=lambda …)`, `map(f, xs)`, `__init__` and the special methods of
instances run user code.

Lock step. Every operation is a function: equal states and equal values give
equal results. A value never shows the code of a user function or generator
(`Val.fn o`, `Val.gen o` carry an address only), so an interpretation cannot
tell two runs apart that hold different closures at the same address: two runs
whose states are equal and whose values agree up to the closures' code stay in
lock step through every operation.
-/
import Std.Data.HashMap

namespace Py

abbrev Name := String

/-- The shape of a display. `stars` marks the starred elements (`*e`); in a
dictionary, `true` is a `**m` item (one value) and `false` a `k: v` item (two
values, key first). `kwargs` gathers keyword arguments (`none` for `**m`) into a
tuple of `(name, value)` tuples, raising `TypeError` on a repeated name. -/
inductive Disp where
  | list (stars : List Bool)
  | tuple (stars : List Bool)
  | set (stars : List Bool)
  /-- a set display of three or more constants, which CPython's compiler builds from a
  frozenset constant (an order of the set's table) -/
  | constSet
  | dict (stars : List Bool)
  | slice
  | fstr
  | kwargs (names : List (Option Name))
  deriving BEq, Repr, Hashable

/-- What a comprehension accumulates into. -/
inductive Acc where
  | list | set | dict
  deriving BEq, Repr, Hashable

/-- The operations. Each lists the values it takes. -/
inductive Op where
  /-- `[a, b]`: arithmetic (`Add`, …), comparison (`Eq`, `Lt`, `Is`, `In`, …), in place (`Add=`, …). -/
  | binop (o : String)
  /-- `[a]`: `USub`, `UAdd`, `Invert`, `Not`. -/
  | unop (o : String)
  /-- `[a]`, giving `bool b`. -/
  | truth
  /-- `[a]`: `iter(a)` (the core keeps a user generator's own). -/
  | iter
  /-- `[it]`: the next item of an iterator that is no user generator, or `StopIteration`. -/
  | next
  | getattr (a : Name)
  | setattr (a : Name)
  | delattr (a : Name)
  | getitem
  | setitem
  | delitem
  /-- `[f, args…, kwvals…]`: a call of a value that is no user function. -/
  | call (kws : List Name)
  | display (d : Disp)
  /-- `[acc, v]` or (`dict`) `[acc, k, v]`: a comprehension adds its element. -/
  | accum (k : Acc)
  /-- `[v]`: iterate `v` into `before` values, a list of the rest if `star`, and
  `after` values, as a tuple; `ValueError` if there are too few or too many. -/
  | unpack (before : Nat) (star : Bool) (after : Nat)
  /-- `[v]`: the conversion `!s` (115), `!r` (114), `!a` (97) of an f-string field. -/
  | convert (c : Int)
  /-- `[v]` or `[v, spec]`: `format(v, spec)`. -/
  | format
  /-- `[bases…, kwvals…, nsvals…]`: the class `x` of qualified name `q` from its
  bases, keywords `kws` and the namespace its body built (`ns`, in order). -/
  | mkClass (x : Name) (q : String) (kws : List Name) (ns : List Name)
  /-- `[e]`: the exception `raise e` raises (an instance; a class is instantiated). -/
  | mkExc
  /-- `[exc, ty]`: whether `except ty` handles `exc`, as `bool`. -/
  | excMatch
  /-- `[]`: `import m`, giving the top package (`leaf = false`) or `m` itself. -/
  | import (m : Name) (leaf : Bool)
  /-- `[module]`: `from module import x`. -/
  | importFrom (x : Name)
  /-- `[module]`: `from module import *`, a tuple of `(name, value)` tuples. -/
  | importStar
  deriving BEq, Repr, Hashable

/-- Values (PyCore's, generalized). The scalars and tuples are immutable values without identity;
`fn`, `gen` are objects of the core and `obj` an object of the interpretation's
state, each by address; `data` is an immutable value of the interpretation
(`slice`, `range`, …); `bfun k` is a builtin (function, type, module, method)
named `k`; `meth f self` a bound method; `next` the core's `next`, which resumes
a user generator; `err k args` an instance of the builtin exception class `k`;
`exn v context cause` the exception `v` with its `__context__` and `__cause__`
(`none` when unset), whose class is that of `v` (`Val.base`). -/
inductive Val where
  /-- an abstract constant (an interpretation may use it for what it builds) -/
  | prim (c : String)
  /-- the value of the constant `$false`, false in every interpretation (dead branches) -/
  | no
  | none
  | bool (b : Bool)
  | int (n : Int)
  | float (bits : UInt64)
  | str (s : String)
  | tuple (vs : List Val)
  | data (tag : String) (vs : List Val)
  | fn (o : Nat)
  | gen (o : Nat)
  | obj (o : Nat)
  | bfun (k : String)
  | meth (f self : Val)
  | next
  | err (k : String) (args : List Val)
  | exn (v context cause : Val)
  /-- an operation of the interface as a value: a call of it performs it on the
  arguments (the translation reaches every operation this way, `Op.ofName`) -/
  | op (o : Op)
  deriving BEq, Repr, Inhabited, Hashable

/-- The exception without its context and cause. -/
def Val.base : Val → Val
  | .exn v _ _ => v
  | v => v

/-- Set the `__context__` of an exception. -/
def Val.setCtx (v h : Val) : Val :=
  match v with
  | .exn b _ cs => .exn b h cs
  | b => .exn b h .none

def Val.cause : Val → Val
  | .exn _ _ c => c
  | _ => .none

/-- A builtin exception the core raises (`NameError`, `TypeError`, …). -/
def err (k : String) : Val := .err k []

def isStop (v : Val) : Bool :=
  match v.base with
  | .err "StopIteration" _ => true
  | _ => false

/-- The value a `StopIteration` carries (`yield from`, a generator's `return`). -/
def stopValue (v : Val) : Val :=
  match v.base with
  | .err _ (a :: _) => a
  | _ => .none

/-- `StopIteration(v)` as a generator's `return v` raises it (no argument for `None`). -/
def stopOf (v : Val) : Val :=
  match v with
  | .none => .err "StopIteration" []
  | v => .err "StopIteration" [v]

/-- Set the `__cause__` of an exception (`raise e from c`). -/
def setCause (v c : Val) : Val :=
  match v with
  | .exn b ctx _ => .exn b ctx c
  | b => .exn b .none c

/-- The outcome of an operation: a value, a new exception (the core gives it
its context), an exception from a callback passed on unchanged, or a call the
core makes before handing its outcome to the native continuation `k`. -/
inductive Res (σ : Type) where
  | ok (s : σ) (v : Val)
  | raise (s : σ) (e : Val)
  | reraise (s : σ) (e : Val)
  | call (s : σ) (f : Val) (args : List Val) (kws : List (Name × Val))
      (k : σ → Except Val Val → Res σ)

instance [Inhabited σ] : Inhabited (Res σ) := ⟨.ok default .none⟩

/-- An interpretation: constants (a constant's `repr`), the builtins'
namespace, and the operations. -/
structure Interp (σ : Type) where
  const : String → Val
  builtin : Name → Option Val
  op : σ → Op → List Val → Res σ

/-! ### Parsing constant names

By lists of characters (`List.splitOn`, `List.isPrefixOf`, digit folds), which reduce and
have lemmas. -/

/-- The parts of `k` between `c`s. -/
def splitBy (c : Char) (k : String) : List String := (k.toList.splitOn c).map String.ofList

/-- A decimal numeral's value (digits only, at least one). -/
def natOf (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | cs => cs.foldl (fun acc d => acc.bind fun n =>
      if d.isDigit then some (10 * n + (d.toNat - '0'.toNat)) else none) (some 0)

/-- An integer numeral's value (a `-` and digits, or digits). -/
def intOf (s : String) : Option Int :=
  match s.toList with
  | '-' :: cs => (natOf (String.ofList cs)).map fun n => -(n : Int)
  | _ => (natOf s).map Int.ofNat

/-- `p` is a prefix of `k`. -/
def hasPrefix (p k : String) : Bool := p.toList.isPrefixOf k.toList

/-- `k` without its first `n` characters. -/
def dropChars (n : Nat) (k : String) : String := String.ofList (k.toList.drop n)

/-- The operation the parts after `$op` name. -/
def Op.ofParts (ps : List String) : Option Op :=
  let stars (s : String) : List Bool := s.toList.map (· == '1')
  match ps with
  | ["iter"] => some .iter
  | ["next"] => some .next
  | ["truth"] => some .truth
  | ["getitem"] => some .getitem
  | ["setitem"] => some .setitem
  | ["delitem"] => some .delitem
  | ["getattr", a] => some (.getattr a)
  | ["setattr", a] => some (.setattr a)
  | ["delattr", a] => some (.delattr a)
  | ["binop", o] => some (.binop o)
  | ["unop", o] => some (.unop o)
  | ["mkExc"] => some .mkExc
  | ["excMatch"] => some .excMatch
  | ["format"] => some .format
  | ["convert", c] => (intOf c).map .convert
  | ["accum", "list"] => some (.accum .list)
  | ["accum", "set"] => some (.accum .set)
  | ["accum", "dict"] => some (.accum .dict)
  | ["unpack", b, st, a] => match natOf b, natOf a with
    | some b, some a => some (.unpack b (st == "1") a)
    | _, _ => none
  | ["import", m, leaf] => some (.import m (leaf == "1"))
  | ["importFrom", x] => some (.importFrom x)
  | ["importStar"] => some .importStar
  | ["display", "list", st] => some (.display (.list (stars st)))
  | ["display", "tuple", st] => some (.display (.tuple (stars st)))
  | ["display", "set", st] => some (.display (.set (stars st)))
  | ["display", "constSet"] => some (.display .constSet)
  | ["display", "dict", st] => some (.display (.dict (stars st)))
  | ["display", "slice"] => some (.display .slice)
  | ["display", "fstr"] => some (.display .fstr)
  | ["call"] => some (.call [])
  | ["call", kws] => some (.call (splitBy ',' kws))
  | _ => none

/-- The operation a constant `$op:…` names: `$op:iter`, `$op:getattr:x`,
`$op:binop:Add`, `$op:unpack:2:0:0`, `$op:display:list:010` (the starred items),
`$op:call:k1,k2` (keyword names), … -/
def Op.ofName (k : String) : Option Op :=
  match splitBy ':' k with
  | "$op" :: ps => Op.ofParts ps
  | _ => none

/-- A parameter's kind. -/
inductive PK where
  | posonly | pos | vararg | kwonly | kwarg
  deriving BEq, DecidableEq, Repr

/-! ## Core gadgets

What the translation into PyCore needs the core to do without the interpretation,
named by constants (`Gadget.name`) whose call PyCore's core performs (`Val.prim k`
holds the name; a call of it in any other way goes to the interpretation). Each
takes the items of one argument record (`$args`, extended by `,`). -/

/-- Starred items as `0`/`1`. -/
def starsStr (st : List Bool) : String := String.ofList (st.map fun b => if b then '1' else '0')
def starsOf (s : String) : List Bool := s.toList.map (· == '1')

/-- Keyword names, `*` for `**m`, comma-separated. -/
def kwsStr (kws : List (Option Name)) : String := ",".intercalate (kws.map fun k => k.getD "*")
def kwsOf (s : String) : List (Option Name) :=
  if s.isEmpty then [] else (splitBy ',' s).map fun k => if k == "*" then none else some k

def PK.chr : PK → Char
  | .posonly => 'o' | .pos => 'p' | .vararg => 'v' | .kwonly => 'k' | .kwarg => 'w'
def PK.ofChr : Char → Option PK
  | 'o' => some .posonly | 'p' => some .pos | 'v' => some .vararg | 'k' => some .kwonly
  | 'w' => some .kwarg | _ => none

/-- A signature: each parameter's name, kind, and whether it has a default, as
`<kind><=?><name>`, comma-separated. -/
def sigStr (sig : List (Name × PK × Bool)) : String :=
  ",".intercalate (sig.map fun (x, k, d) => String.ofList [k.chr] ++ (if d then "=" else "") ++ x)
def sigOf (s : String) : Option (List (Name × PK × Bool)) :=
  if s.isEmpty then some [] else (splitBy ',' s).mapM fun p => match p.toList with
    | c :: '=' :: x => (PK.ofChr c).map fun k => (String.ofList x, k, true)
    | c :: x => (PK.ofChr c).map fun k => (String.ofList x, k, false)
    | [] => none

inductive Gadget where
  /-- `[f, values…, markers…]`: the call `f(…)`; each positional argument's marker is `$pos` or
  `$star` (`*e`), each keyword's `$kw:x` or `$kwstar` (`**m`) -/
  | call
  /-- `[decorators (nd)…, defaults…, annotations…, markers (np)…, closure]`: the closure gets
  the signature its parameters' markers `$param:…` give and its defaults; then the
  decorators apply, innermost first -/
  | defn (nd np : Nat)
  /-- `[decorators (nd)…, values…, markers…]`: the arguments of the class statement that
  follows (markers as for `call`) -/
  | cls (nd : Nat)
  /-- `[v, markers…]`: unpack `v` into targets whose markers (`$pos`, `$star`) give the shape -/
  | unpack
  /-- `[values…, markers…]`: a list, tuple or set display (`k`); a set of more than two items
  all marked constant (`$c0`, `$c1`) is a constant set -/
  | display (k : String)
  /-- `[m]`: the constness marker of `op a`, `a`'s marker `m` -/
  | cunary (op : String)
  /-- `[markers…]`: the constness marker of a tuple of items with those markers -/
  | ctuple
  /-- `[d]`: `__annotations__ = d` in the module dictionary or class namespace, unless set -/
  | setup
  /-- `[a]`: `__annotations__['x'] = a`, `__annotations__` read as `LOAD_NAME` reads it -/
  | annot (x : Name)
  /-- `[pairs]`: the names `from m import *` gives -/
  | starstore
  /-- `[]`: a bare `raise` -/
  | reraise
  /-- `[args…]`: raise the builtin exception `k(args…)` -/
  | raiseK (k : String)
  /-- `[e, c]`: `raise e from c` -/
  | raiseFrom
  /-- `[t]`: the `i`-th item of the tuple `t` -/
  | item (i : Nat)
  /-- `[v]`: store `v` in the frame's own cell of the fresh name `x`, giving `v` -/
  | set (x : Name)
  /-- `[]`: the frame's own cell of `x` -/
  | get (x : Name)
  /-- no step (what CPython's compiler rejects) -/
  | stuck

def Gadget.name : Gadget → String
  | .call => "$call"
  | .defn nd np => "$def:" ++ toString nd ++ ":" ++ toString np
  | .cls nd => "$cls:" ++ toString nd
  | .unpack => "$unpack"
  | .display k => "$display:" ++ k
  | .cunary op => "$cunary:" ++ op
  | .ctuple => "$ctuple"
  | .setup => "$setup"
  | .annot x => "$annot:" ++ x
  | .starstore => "$starstore"
  | .reraise => "$reraise"
  | .raiseK k => "$raise:" ++ k
  | .raiseFrom => "$raisefrom"
  | .item i => "$item:" ++ toString i
  | .set x => "$set:" ++ x
  | .get x => "$get:" ++ x
  | .stuck => "$stuck"

def Gadget.ofName (k : String) : Option Gadget :=
  match splitBy ':' k with
  | ["$call"] => some .call
  | ["$def", nd, np] => match natOf nd, natOf np with
    | some nd, some np => some (.defn nd np)
    | _, _ => none
  | ["$cls", nd] => (natOf nd).map .cls
  | ["$unpack"] => some .unpack
  | ["$display", k] => some (.display k)
  | ["$cunary", op] => some (.cunary op)
  | ["$ctuple"] => some .ctuple
  | ["$setup"] => some .setup
  | ["$annot", x] => some (.annot x)
  | ["$starstore"] => some .starstore
  | ["$reraise"] => some .reraise
  | ["$raise", k] => some (.raiseK k)
  | ["$raisefrom"] => some .raiseFrom
  | ["$item", i] => (natOf i).map .item
  | ["$set", x] => some (.set x)
  | ["$get", x] => some (.get x)
  | ["$stuck"] => some .stuck
  | _ => none

/-! ### Markers

A node's marker is a constant made for the node that tells its parent's gadget, when it
runs, what the node is: a positional item (`$pos`; for a set's item its constness, `$c0`
a constant, `$c1` a constant by CPython's folding, `$nc` none) or a starred one (`$star`),
a keyword argument (`$kw:x`, or `$kwstar` for `**m`), a parameter (`$param:<kind><=?><name>`).
Its value is `Val.prim` of its name. -/

def isMarker (k : String) : Bool :=
  k == "$pos" || k == "$star" || k == "$c0" || k == "$c1" || k == "$nc" || k == "$kwstar" ||
    hasPrefix "$kw:" k || hasPrefix "$param:" k

def kwMarker (x : Option Name) : String := match x with
  | some x => "$kw:" ++ x
  | none => "$kwstar"

def paramMarker (x : Name) (k : PK) (d : Bool) : String := "$param:" ++ sigStr [(x, k, d)]

/-- Whether a positional item's marker says it is starred. -/
def markStar : Val → Option Bool
  | .prim "$star" => some true
  | .prim "$pos" | .prim "$c0" | .prim "$c1" | .prim "$nc" => some false
  | _ => none

def markConst : Val → Bool
  | .prim "$c0" | .prim "$c1" => true
  | _ => false

def markKw : Val → Option (Option Name)
  | .prim k => if k == "$kwstar" then some none
    else if hasPrefix "$kw:" k then some (some (dropChars 4 k)) else none
  | _ => none

def markParam : Val → Option (Name × PK × Bool)
  | .prim k => if hasPrefix "$param:" k then (sigOf (dropChars 7 k)).bind List.head? else none
  | _ => none

/-- The values then their markers, as marker–value pairs (the markers come last, so that
the parent's gadget reads them when it runs, after every value). -/
def pairs (vs : List Val) : Option (List (Val × Val)) :=
  if vs.length % 2 = 0 then some ((vs.drop (vs.length / 2)).zip (vs.take (vs.length / 2))) else none

/-- The arguments of a call or class statement from their markers: the positional ones
(their stars and values), then the keywords (their names and values). -/
def splitArgs (ps : List (Val × Val)) :
    Option (List Bool × List Val × List (Option Name) × List Val) :=
  let pos := ps.takeWhile fun p => (markStar p.1).isSome
  let kw := ps.drop pos.length
  match pos.mapM (markStar ·.1), kw.mapM (markKw ·.1) with
  | some st, some ks => some (st, pos.map (·.2), ks, kw.map (·.2))
  | _, _ => none

/-- The positions of a starred target, from the targets' stars. -/
def starShape (st : List Bool) : Nat × Bool × Nat :=
  match st.findIdx? id with
  | some i => (i, true, st.length - i - 1)
  | none => (st.length, false, 0)

/-- The empty argument record: `$args`, which `,` extends by a value. -/
def emptyArgs : Val := .data "$args" []

/-- A constant's value. The core fixes these, whatever the interpretation: `$false`
(`Val.no`), `$true`, `$none`, `$args`, `$next` (the core's `next`), `$op:…` (an
operation), the gadgets' names and the markers (`Val.prim`); any other constant is the
interpretation's. -/
def constVal {σ} (I : Interp σ) (k : String) : Val :=
  if k = "$false" then .no else if k = "$true" then .bool true else if k = "$none" then .none
  else if k = "$args" then emptyArgs else if k = "$next" then .next
  else match Op.ofName k with
    | some o => .op o
    | none => if (Gadget.ofName k).isSome || isMarker k then .prim k else I.const k

/-- `(name, value)` pairs from the tuple `Disp.kwargs` gives. -/
def kwPairs : List Val → Option (List (Name × Val))
  | [] => some []
  | .tuple [.str k, v] :: r => (kwPairs r).map ((k, v) :: ·)
  | _ => none

/-- The defaults stored with a function object, one per parameter (`hasDflt`), from the
values of those given, in order. -/
def alignDefaults : List Bool → List Val → List (Option Val)
  | [], _ => []
  | true :: ds, v :: vs => some v :: alignDefaults ds vs
  | _ :: ds, vs => none :: alignDefaults ds vs

/-! ## Argument binding -/

private def setAt (xs : List (Option Val)) (i : Nat) (v : Val) : List (Option Val) :=
  xs.set i (some v)

/-- Argument binding, CPython's `initialize_locals`: from the parameters (names,
kinds), the defaults stored with the function object (one per parameter), the
positional arguments and the keyword arguments, the value of every parameter but
a `**` one, in order, and the `**` parameter with its items; `TypeError` for an
argument too many or missing, an unexpected keyword, or a parameter given twice.
`*args` is a tuple. -/
def bindArgs (ps : List (Name × PK)) (dflt : List (Option Val)) (args : List Val)
    (kws : List (Name × Val)) :
    Except Val (List (Name × Val) × Option (Name × List (Name × Val))) := do
  let tps := ps.zip dflt
  let pos := tps.filter fun p => p.1.2 == .posonly || p.1.2 == .pos
  let kwo := tps.filter fun p => p.1.2 == .kwonly
  let star := ps.find? (·.2 == .vararg)
  let kwp := ps.find? (·.2 == .kwarg)
  let n := pos.length
  if args.length > n && star.isNone then throw (err "TypeError")
  let pv0 : List (Option Val) := (List.range n).map fun i => args[i]?
  let kv0 : List (Option Val) := kwo.map fun _ => none
  let step (acc : List (Option Val) × List (Option Val) × List (Name × Val)) (kv : Name × Val) :
      Except Val (List (Option Val) × List (Option Val) × List (Name × Val)) :=
    let (pv, kv', rest) := acc
    match pos.findIdx? (fun p => p.1.1 == kv.1 && p.1.2 == .pos) with
    | some i => if (pv[i]?).join.isSome then throw (err "TypeError") else .ok (setAt pv i kv.2, kv', rest)
    | none => match kwo.findIdx? (fun p => p.1.1 == kv.1) with
      | some i => if (kv'[i]?).join.isSome then throw (err "TypeError") else .ok (pv, setAt kv' i kv.2, rest)
      | none =>
        if kwp.isNone || rest.any (·.1 == kv.1) then throw (err "TypeError")
        else .ok (pv, kv', rest ++ [kv])
  let (pv, kv, rest) ← kws.foldlM step (pv0, kv0, [])
  let fill (p : (Name × PK) × Option Val) (o : Option Val) : Except Val (Name × Val) :=
    match o, p.2 with
    | some v, _ => .ok (p.1.1, v)
    | none, some d => .ok (p.1.1, d)
    | none, none => throw (err "TypeError")
  let posB ← (pos.zip pv).mapM fun (p, o) => fill p o
  let kwB ← (kwo.zip kv).mapM fun (p, o) => fill p o
  let starB := match star with
    | some (x, _) => [(x, Val.tuple (args.drop n))]
    | none => []
  return (posB ++ starB ++ kwB, kwp.map fun (x, _) => (x, rest))

/-! ## Memoized functions

The core caches what it computes from syntax alone (a scope's classification of
names, a closure's cells) as `memo xs g`: `g` evaluated once on each of `xs`,
and on demand elsewhere. It is `g` (`memo_eq`). -/

/-- A computed table of `g` (a structure, so that the table is built once: a definition
returning a function would be compiled with the argument added, rebuilding the table at
every application). -/
structure Memo (α : Type) where
  get : Name → α
  /-- the table's size (a second field, so that the structure is not compiled as its function) -/
  size : Nat

@[noinline] def mkMemo {α} (xs : List Name) (g : Name → α) : Memo α :=
  let m : Std.HashMap Name α := xs.foldl (fun m x => if m.contains x then m else m.insert x (g x)) {}
  ⟨fun x => match m[x]? with
    | some a => a
    | none => g x, m.size⟩

/-- `g`, its values on `xs` computed once: use as `(memo xs g).get` (a projection of the
built structure; a definition returning the function would be compiled with the argument
added, rebuilding the table at every application). -/
def memo {α} (xs : List Name) (g : Name → α) : Memo α := mkMemo xs g

private theorem memo_fold {α} (g : Name → α) (xs : List Name) (m : Std.HashMap Name α)
    (h : ∀ y a, m[y]? = some a → a = g y) :
    ∀ y a, (xs.foldl (fun m x => if m.contains x then m else m.insert x (g x)) m)[y]? = some a →
      a = g y := by
  induction xs generalizing m with
  | nil => exact h
  | cons x xs ih =>
    apply ih
    intro y a hy
    simp only at hy
    split at hy
    · exact h y a hy
    rw [Std.HashMap.getElem?_insert] at hy
    split at hy
    · rename_i hxy
      have : x = y := by simpa using hxy
      subst this; simp at hy; exact hy.symm
    · exact h y a hy

theorem memo_eq {α} (xs : List Name) (g : Name → α) : (memo xs g).get = g := by
  funext x
  unfold memo mkMemo
  dsimp only
  split
  · rename_i a ha
    exact memo_fold g xs {} (by intro y a h; simp at h) x a ha
  · rfl

end Py

/-! ## Constant names reduce

Literal names reduce by `rfl` (`constVal I "$op:setitem" = .op .setitem`, `constVal I "$call" =
.prim "$call"`, …). For a family with a part `a` that has no separator, the lemmas below. -/

namespace Py
variable {σ : Type} (I : Interp σ)

/-- Splitting `p ++ c ++ r` at `c`, `p` free of `c`. -/
theorem splitBy_sep {c : Char} {p : String} (hp : c ∉ p.toList) (r : String) :
    splitBy c (p ++ String.singleton c ++ r) = p :: splitBy c r := by
  unfold splitBy
  rw [String.toList_append, String.toList_append, String.toList_singleton, List.append_assoc,
    List.singleton_append, List.splitOn_append_cons_self_of_not_mem hp]
  simp [String.ofList_toList]

theorem splitBy_one {c : Char} {a : String} (ha : c ∉ a.toList) : splitBy c a = [a] := by
  unfold splitBy; rw [List.splitOn_eq_singleton ha]; simp [String.ofList_toList]

/-- A constant naming an operation is that operation. -/
theorem constVal_of_op {k : String} {o : Op} (h : Op.ofName k = some o) : constVal I k = .op o := by
  unfold constVal
  by_cases h1 : k = "$false"
  · subst h1; cases h
  by_cases h2 : k = "$true"
  · subst h2; cases h
  by_cases h3 : k = "$none"
  · subst h3; cases h
  by_cases h4 : k = "$args"
  · subst h4; cases h
  by_cases h5 : k = "$next"
  · subst h5; cases h
  simp only [h1, h2, h3, h4, h5, h, ↓reduceIte]

/-- A constant naming a gadget or a marker (and no operation) is `Val.prim` of its name. -/
theorem constVal_of_prim {k : String} (h : Op.ofName k = none)
    (hg : (Gadget.ofName k).isSome = true ∨ isMarker k = true) : constVal I k = .prim k := by
  unfold constVal
  by_cases h1 : k = "$false"
  · subst h1; exact absurd hg (by decide)
  by_cases h2 : k = "$true"
  · subst h2; exact absurd hg (by decide)
  by_cases h3 : k = "$none"
  · subst h3; exact absurd hg (by decide)
  by_cases h4 : k = "$args"
  · subst h4; exact absurd hg (by decide)
  by_cases h5 : k = "$next"
  · subst h5; exact absurd hg (by decide)
  simp only [h1, h2, h3, h4, h5, h, ↓reduceIte]
  rcases hg with hg | hg <;> simp [hg]

/-- A name whose first part is no `$op` names no operation. -/
theorem ofName_none {k : String} (h : (splitBy ':' k).head? ≠ some "$op") : Op.ofName k = none := by
  unfold Op.ofName; split
  · rename_i ps e; rw [e] at h; exact absurd rfl h
  · rfl

theorem isPrefixOf_self_append (p q : List Char) : p.isPrefixOf (p ++ q) = true := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [ih]

/-- `"$op:f:" ++ a` splits into `$op`, `f`, `a`. -/
theorem splitBy_op2 {f a : String} (hf : ':' ∉ f.toList) (ha : ':' ∉ a.toList) :
    splitBy ':' ("$op" ++ String.singleton ':' ++ (f ++ String.singleton ':' ++ a)) = ["$op", f, a] := by
  rw [splitBy_sep (by decide), splitBy_sep hf, splitBy_one ha]

/-- `"$g:" ++ a` splits into `$g`, `a`. -/
theorem splitBy_g1 {g a : String} (hg : ':' ∉ g.toList) (ha : ':' ∉ a.toList) :
    splitBy ':' (g ++ String.singleton ':' ++ a) = [g, a] := by
  rw [splitBy_sep hg, splitBy_one ha]

section families
variable {a : String} (ha : ':' ∉ a.toList)
include ha

omit ha in
private theorem e2 (f : String) : ("$op:" ++ f ++ ":" ++ a) =
    "$op" ++ String.singleton ':' ++ (f ++ String.singleton ':' ++ a) := by
  simp only [String.append_assoc]; rfl

theorem constVal_getattr : constVal I ("$op:getattr:" ++ a) = .op (.getattr a) :=
  constVal_of_op I (by rw [show "$op:getattr:" ++ a = "$op:" ++ "getattr" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)
theorem constVal_setattr : constVal I ("$op:setattr:" ++ a) = .op (.setattr a) :=
  constVal_of_op I (by rw [show "$op:setattr:" ++ a = "$op:" ++ "setattr" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)
theorem constVal_delattr : constVal I ("$op:delattr:" ++ a) = .op (.delattr a) :=
  constVal_of_op I (by rw [show "$op:delattr:" ++ a = "$op:" ++ "delattr" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)
theorem constVal_binop : constVal I ("$op:binop:" ++ a) = .op (.binop a) :=
  constVal_of_op I (by rw [show "$op:binop:" ++ a = "$op:" ++ "binop" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)
theorem constVal_unop : constVal I ("$op:unop:" ++ a) = .op (.unop a) :=
  constVal_of_op I (by rw [show "$op:unop:" ++ a = "$op:" ++ "unop" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)
theorem constVal_importFrom : constVal I ("$op:importFrom:" ++ a) = .op (.importFrom a) :=
  constVal_of_op I (by rw [show "$op:importFrom:" ++ a = "$op:" ++ "importFrom" ++ ":" ++ a by rfl, e2,
    Op.ofName, splitBy_op2 (by decide) ha]; rfl)

omit ha in
private theorem g1 (g : String) : (g ++ ":" ++ a) = g ++ String.singleton ':' ++ a := rfl

theorem constVal_annot : constVal I ("$annot:" ++ a) = .prim ("$annot:" ++ a) := by
  have hs : splitBy ':' ("$annot:" ++ a) = ["$annot", a] := by
    rw [show "$annot:" ++ a = "$annot" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  exact constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inl (by rw [Gadget.ofName, hs]; rfl))
theorem constVal_set : constVal I ("$set:" ++ a) = .prim ("$set:" ++ a) := by
  have hs : splitBy ':' ("$set:" ++ a) = ["$set", a] := by
    rw [show "$set:" ++ a = "$set" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  exact constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inl (by rw [Gadget.ofName, hs]; rfl))
theorem constVal_get : constVal I ("$get:" ++ a) = .prim ("$get:" ++ a) := by
  have hs : splitBy ':' ("$get:" ++ a) = ["$get", a] := by
    rw [show "$get:" ++ a = "$get" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  exact constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inl (by rw [Gadget.ofName, hs]; rfl))
theorem constVal_raise : constVal I ("$raise:" ++ a) = .prim ("$raise:" ++ a) := by
  have hs : splitBy ':' ("$raise:" ++ a) = ["$raise", a] := by
    rw [show "$raise:" ++ a = "$raise" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  exact constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inl (by rw [Gadget.ofName, hs]; rfl))
theorem constVal_cunary : constVal I ("$cunary:" ++ a) = .prim ("$cunary:" ++ a) := by
  have hs : splitBy ':' ("$cunary:" ++ a) = ["$cunary", a] := by
    rw [show "$cunary:" ++ a = "$cunary" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  exact constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inl (by rw [Gadget.ofName, hs]; rfl))
theorem constVal_kw : constVal I ("$kw:" ++ a) = .prim ("$kw:" ++ a) := by
  have hs : splitBy ':' ("$kw:" ++ a) = ["$kw", a] := by
    rw [show "$kw:" ++ a = "$kw" ++ ":" ++ a by rfl, g1, splitBy_g1 (by decide) ha]
  refine constVal_of_prim I (ofName_none (by rw [hs]; simp)) (.inr ?_)
  have : hasPrefix "$kw:" ("$kw:" ++ a) = true := by
    unfold hasPrefix; rw [String.toList_append]; exact isPrefixOf_self_append _ _
  unfold isMarker; simp [this]
end families

end Py
