/-
The reference interpretation `Ref.interp : Py.Interp Ref.St`: CPython 3.13's
builtin types and the builtins, methods and modules the buggy programs and the
repairs use (`results/checks/lean_sem/census.txt`), concretely: ints of
arbitrary precision, bools, None, IEEE doubles (`Surf/RefFloat.lean`), str,
list, tuple, dict (and `Counter`, `defaultdict`, `OrderedDict`), set,
frozenset, `deque`, range, slices, iterators, user classes (bases, C3 MRO,
instances, attributes, bound methods, `__init__` and special methods as
callbacks), builtin exceptions, `print` and `input` on the state's output and
input. What it lacks raises the marker exception `$Unsupported` (the
differential run counts it as not covered).
-/
import Common.Interp
import Surf.RefFloat

namespace Ref
open Py

/-! ## State -/

/-- A slot of CPython's set table: its hash and normalized key. -/
inductive Slot where
  | empty
  | dummy
  | full (h : UInt64) (k : Val)
  deriving Inhabited

/-- CPython's set table (`setobject.c`): the slots, `mask`, `fill`, `used`, and the
`finger` of `set.pop`. It fixes a set's iteration order. -/
structure CTab where
  slots : Array Slot := Array.replicate 8 .empty
  mask : Nat := 7
  fill : Nat := 0
  used : Nat := 0
  finger : Nat := 0
  deriving Inhabited

/-- A dictionary in insertion order, indexed by the normalized key (`normKey`); a
set (values unused) also keeps CPython's table (`tab`), which orders it. -/
structure PDict where
  ents : Array (Option (Val × Val)) := #[]
  idx : Std.HashMap Val Nat := {}
  size : Nat := 0
  tab : Option CTab := none
  deriving Inhabited

inductive DK where
  | plain
  | counter
  | dflt (factory : Val)
  | ordered
  deriving Inhabited

inductive It where
  | list (o : Nat) (i : Nat)
  | seq (vs : List Val)
  | str (cs : List Char)
  | rng (cur stop step : Int)
  | dict (o : Nat) (i : Nat) (n : Nat) (what : Nat)
  /-- a set's keys in table order, with its size when the iteration began -/
  | setv (o : Nat) (ks : List Val) (n : Nat)
  | enum (it : Val) (n : Int)
  | zip (its : List Val)
  | map (f : Val) (its : List Val)
  | filter (f : Val) (it : Val) (neg : Bool)
  | count (cur step : Int)
  | chain (its : List Val)
  | done
  deriving Inhabited

inductive RObj where
  | list (vs : Array Val)
  | dict (d : PDict) (k : DK)
  | set (d : PDict) (frozen : Bool)
  | deque (vs : Array Val)
  | iter (it : It)
  /-- a user class: name, qualified name, `__module__`, bases, MRO, namespace -/
  | cls (name qual : String) (module : Val) (bases mro : List Val) (dict : List (Name × Val))
  | inst (cls : Val) (attrs : List (Name × Val))
  /-- `functools.lru_cache` around `f` -/
  | cache (f : Val) (memo : PDict)
  /-- `queue.PriorityQueue`, its heap the list object `q` (its `queue` attribute) -/
  | pq (q : Nat)
  deriving Inhabited

/-- The state: the heap, the output (pieces, latest first), the remaining input. -/
structure St where
  heap : Array RObj := #[]
  out : List String := []
  inp : List Char := []
  /-- set when the interpretation lacks something the run needed -/
  unsup : Option String := none
  deriving Inhabited

def St.get (s : St) (o : Nat) : RObj := s.heap[o]!
/-- Heap updates take the state apart first, so that a unique heap is updated in place. -/
def St.put (s : St) (o : Nat) (x : RObj) : St :=
  match s with | ⟨h, out, inp, u⟩ => ⟨h.set! o x, out, inp, u⟩
def St.modify (s : St) (o : Nat) (f : RObj → RObj) : St :=
  match s with | ⟨h, out, inp, u⟩ => ⟨h.modify o f, out, inp, u⟩
def St.alloc (s : St) (x : RObj) : St × Val :=
  match s with | ⟨h, out, inp, u⟩ => (⟨h.push x, out, inp, u⟩, .obj h.size)
def St.emit (s : St) (t : String) : St := { s with out := t :: s.out }
def St.output (s : St) : String := String.join s.out.reverse

def unsup (msg : String) : Val := .err "$Unsupported" [.str msg]
def tErr : Val := .err "TypeError" []
def vErr : Val := .err "ValueError" []

/-! ## The CPS monad -/

/-- Computations that may call back into user code. -/
def M (α : Type) := St → (St → α → Res St) → Res St

instance : Monad M where
  pure a := fun s k => k s a
  bind m f := fun s k => m s (fun s' a => f a s' k)

def M.run (m : M Val) (s : St) : Res St := m s (fun s v => .ok s v)
/-- Raise a new exception; the marker `$Unsupported` is also recorded in the state,
so that a handler catching it cannot hide it. -/
def throwM {α} (e : Val) : M α := fun s _ =>
  match e with
  | .err "$Unsupported" [.str m] => .raise { s with unsup := s.unsup.orElse fun _ => some m } e
  | _ => .raise s e
def reraiseM {α} (e : Val) : M α := fun s _ => .reraise s e
def getS : M St := fun s k => k s s
def setS (s' : St) : M Unit := fun _ k => k s' ()
def modS (f : St → St) : M Unit := fun s k => k (f s) ()
def liftE {α} : Except Val α → M α
  | .ok a => pure a
  | .error e => throwM e
/-- Call back: the core calls `f`; its exception passes on unchanged. -/
def callM (f : Val) (args : List Val) (kws : List (Name × Val) := []) : M Val :=
  fun s k => .call s f args kws (fun s' r => match r with
    | .ok v => k s' v
    | .error e => .reraise s' e)
def tryCallM (f : Val) (args : List Val) : M (Except Val Val) :=
  fun s k => .call s f args [] (fun s' r => k s' r)
/-- Return to the core once (a no-op call), so that long native loops in `M`
do not deepen the stack. -/
def bounce : M Unit := fun s k => .call s (.bfun "$id") [] [] (fun s' _ => k s' ())
def allocM (x : RObj) : M Val := fun s k => match s.alloc x with | (s', v) => k s' v
def modM (o : Nat) (f : RObj → RObj) : M Unit := fun s k => k (s.modify o f) ()
def objM (o : Nat) : M RObj := fun s k => k s (s.get o)
def putM (o : Nat) (x : RObj) : M Unit := fun s k => k (s.put o x) ()

/-! ## Strings -/

def ofChars (cs : List Char) : String := String.ofList cs
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'
  || c.toNat == 0x1c || c.toNat == 0x1d || c.toNat == 0x1e || c.toNat == 0x1f || c.toNat == 0x85
  || c.toNat == 0xa0 || c.toNat == 0x3000
def cUp (c : Char) : Char := if c.isLower then Char.ofNat (c.toNat - 32) else c
def cLow (c : Char) : Char := if c.isUpper then Char.ofNat (c.toNat + 32) else c

/-- Python's `repr` of a str. -/
def strRepr (s : String) : String :=
  let cs := s.toList
  let q := if cs.contains '\'' && !cs.contains '"' then '"' else '\''
  let hex (n : Nat) (w : Nat) : String :=
    let d := Nat.toDigits 16 n
    ofChars (List.replicate (w - d.length) '0' ++ d)
  let esc (c : Char) : String :=
    if c == q || c == '\\' then "\\" ++ c.toString
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 0x20 || c.toNat == 0x7f then "\\x" ++ hex c.toNat 2
    else if 0x80 ≤ c.toNat && c.toNat < 0xa0 then "\\x" ++ hex c.toNat 2
    else c.toString
  q.toString ++ String.join (cs.map esc) ++ q.toString

def splitWs (cs : List Char) : List (List Char) :=
  let rec go (cs : List Char) (cur : List Char) (acc : List (List Char)) : List (List Char) :=
    match cs with
    | [] => (if cur.isEmpty then acc else cur.reverse :: acc).reverse
    | c :: r => if isWs c then go r [] (if cur.isEmpty then acc else cur.reverse :: acc) else go r (c :: cur) acc
  go cs [] []

def isPrefixL (p cs : List Char) : Bool := p.isPrefixOf cs

/-- Split on whitespace at most `n` times. -/
def splitWsMax (cs : List Char) (n : Int) (acc : List (List Char)) (fuel : Nat) : List (List Char) :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    let cs := cs.dropWhile isWs
    if cs.isEmpty then acc.reverse
    else if n == 0 then (((cs.reverse.dropWhile isWs).reverse) :: acc).reverse
    else
      let w := cs.takeWhile (!isWs ·)
      splitWsMax (cs.drop w.length) (n - 1) (w :: acc) fuel

/-- Split on a non-empty separator, at most `max` times (`max < 0`: no limit). -/
def splitSep (cs sep : List Char) (max : Int) : List (List Char) :=
  let rec go (cs : List Char) (cur : List Char) (acc : List (List Char)) (n : Int) (fuel : Nat) : List (List Char) :=
    match fuel with
    | 0 => ((cur.reverse ++ cs) :: acc).reverse
    | fuel + 1 =>
      if n != 0 && isPrefixL sep cs then go (cs.drop sep.length) [] (cur.reverse :: acc) (n - 1) fuel
      else match cs with
        | [] => (cur.reverse :: acc).reverse
        | c :: r => go r (c :: cur) acc n fuel
  go cs [] [] max (cs.length + 1)

def countSub (cs sub : List Char) : Nat :=
  if sub.isEmpty then cs.length + 1 else
  let rec go (cs : List Char) (n : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => if isPrefixL sub cs then go (cs.drop sub.length) (n + 1) fuel
      else match cs with | [] => n | _ :: r => go r n fuel
  go cs 0 (cs.length + 1)

def findSub (cs sub : List Char) : Option Nat :=
  let rec go (cs : List Char) (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 => if isPrefixL sub cs then some i else match cs with | [] => none | _ :: r => go r (i + 1) fuel
  go cs 0 (cs.length + 1)

def rfindSub (cs sub : List Char) : Option Nat :=
  ((List.range (cs.length + 1)).reverse.find? fun i => isPrefixL sub (cs.drop i))

def replaceSub (cs old new : List Char) (max : Int) : List Char :=
  if old.isEmpty then
    -- insert `new` between characters (and at both ends), at most `max` times
    let rec ins (cs : List Char) (n : Int) : List Char :=
      if n == 0 then cs else match cs with
        | [] => new
        | c :: r => new ++ c :: ins r (n - 1)
    ins cs max
  else
  let rec go (cs : List Char) (acc : List Char) (n : Int) (fuel : Nat) : List Char :=
    match fuel with
    | 0 => acc.reverse ++ cs
    | fuel + 1 =>
      if n != 0 && isPrefixL old cs then go (cs.drop old.length) (new.reverse ++ acc) (n - 1) fuel
      else match cs with | [] => acc.reverse | c :: r => go r (c :: acc) n fuel
  go cs [] max (cs.length + 1)

def isCased (c : Char) : Bool := c.isUpper || c.isLower
def titleCs (cs : List Char) : List Char :=
  let rec go (cs : List Char) (prevCased : Bool) : List Char :=
    match cs with
    | [] => []
    | c :: r => (if prevCased then cLow c else cUp c) :: go r (isCased c)
  go cs false
def isTitleCs (cs : List Char) : Bool :=
  let rec go (cs : List Char) (prevCased : Bool) (any : Bool) : Bool :=
    match cs with
    | [] => any
    | c :: r =>
      if c.isUpper then (if prevCased then false else go r true true)
      else if c.isLower then (if prevCased then go r true any else false)
      else go r false any
  go cs false false

/-! ## Values -/

def vInt (n : Int) : Val := .int n
def vStr (s : String) : Val := .str s
def vFloat (b : UInt64) : Val := .float b
def vBool (b : Bool) : Val := .bool b

/-- The builtin exception classes and their bases. -/
def excBase : String → Option String
  | "BaseException" => some "object"
  | "Exception" | "SystemExit" | "KeyboardInterrupt" | "GeneratorExit" => some "BaseException"
  | "ArithmeticError" | "AssertionError" | "AttributeError" | "EOFError" | "ImportError"
  | "LookupError" | "MemoryError" | "NameError" | "OSError" | "RuntimeError" | "StopIteration"
  | "SyntaxError" | "TypeError" | "ValueError" | "BufferError" | "ReferenceError"
  | "Warning" | "StopAsyncIteration" => some "Exception"
  | "ZeroDivisionError" | "OverflowError" | "FloatingPointError" => some "ArithmeticError"
  | "ModuleNotFoundError" => some "ImportError"
  | "IndexError" | "KeyError" => some "LookupError"
  | "UnboundLocalError" => some "NameError"
  | "RecursionError" | "NotImplementedError" => some "RuntimeError"
  | "UnicodeError" => some "ValueError"
  | "IndentationError" => some "SyntaxError"
  | "FileNotFoundError" | "PermissionError" => some "OSError"
  | "$Unsupported" => some "BaseException"
  | _ => none

def isExcName (k : String) : Bool := (excBase k).isSome

/-- The builtin MRO of a builtin type. -/
def builtinMro (k : String) : List String :=
  let rec go (k : String) (fuel : Nat) : List String :=
    match fuel with
    | 0 => [k]
    | fuel + 1 => match excBase k with
      | some "object" => [k, "object"]
      | some b => k :: go b fuel
      | none => if k == "object" then ["object"] else
        match k with
        | "bool" => ["bool", "int", "object"]
        | "Counter" | "defaultdict" | "OrderedDict" => [k, "dict", "object"]
        | _ => [k, "object"]
  go k 10

def builtinTypes : List String :=
  ["int", "float", "str", "bool", "list", "tuple", "dict", "set", "frozenset", "object", "type",
   "range", "NoneType", "function", "generator", "slice", "Counter", "defaultdict", "OrderedDict",
   "deque", "builtin_function_or_method", "method", "enumerate", "map", "filter", "zip",
   "list_iterator", "module", "BaseException"]

def isTypeName (k : String) : Bool := builtinTypes.contains k || isExcName k

/-- The class of a value. -/
def typeOf (s : St) (v : Val) : Val :=
  match v.base with
  | .none => .bfun "NoneType"
  | .no => .bfun "bool"
  | .prim _ => .bfun "object"
  | .bool _ => .bfun "bool"
  | .int _ => .bfun "int"
  | .float _ => .bfun "float"
  | .str _ => .bfun "str"
  | .tuple _ => .bfun "tuple"
  | .data "range" _ => .bfun "range"
  | .data "slice" _ => .bfun "slice"
  | .data k _ => .bfun k
  | .fn _ => .bfun "function"
  | .gen _ => .bfun "generator"
  | .bfun k => if isTypeName k then .bfun "type" else .bfun "builtin_function_or_method"
  | .meth .. => .bfun "method"
  | .next | .op _ => .bfun "builtin_function_or_method"
  | .err k _ => .bfun k
  | .exn .. => .bfun "BaseException"
  | .obj o => match s.get o with
    | .list _ => .bfun "list"
    | .dict _ .plain => .bfun "dict"
    | .dict _ .counter => .bfun "Counter"
    | .dict _ (.dflt _) => .bfun "defaultdict"
    | .dict _ .ordered => .bfun "OrderedDict"
    | .set _ false => .bfun "set"
    | .set _ true => .bfun "frozenset"
    | .deque _ => .bfun "deque"
    | .iter (.enum ..) => .bfun "enumerate"
    | .iter (.map ..) => .bfun "map"
    | .iter (.filter ..) => .bfun "filter"
    | .iter (.zip ..) => .bfun "zip"
    | .iter _ => .bfun "list_iterator"
    | .cls .. => .bfun "type"
    | .inst c _ => c
    | .cache .. => .bfun "functools._lru_cache_wrapper"
    | .pq _ => .bfun "PriorityQueue"

/-- The MRO of a class value. -/
def mroOf (s : St) (c : Val) : List Val :=
  match c with
  | .obj o => match s.get o with
    | .cls _ _ _ _ mro _ => mro
    | _ => []
  | .bfun k => (builtinMro k).map .bfun
  | _ => []

def isSubclass (s : St) (c d : Val) : Bool := (mroOf s c).contains d

def isInstance (s : St) (v c : Val) : Bool :=
  c == .bfun "object" || isSubclass s (typeOf s v) c

/-- Look a name up in a class's MRO. -/
def clsLookup (s : St) (c : Val) (a : Name) : Option Val :=
  (mroOf s c).findSome? fun k => match k with
    | .obj o => match s.get o with
      | .cls _ _ _ _ _ d => d.lookup a
      | _ => none
    | _ => none

/-- A user-defined special method of an instance's class. -/
def special (s : St) (v : Val) (a : Name) : Option Val :=
  match v.base with
  | .obj o => match s.get o with
    | .inst c _ => clsLookup s c a
    | _ => none
  | _ => none

/-! ## Hashing, equality, order -/

def isIntegral (b : UInt64) : Bool :=
  isFinite b && (let (_, m, e) := decomp b; e ≥ 0 || m % pow2 (-e).toNat == 0)

def floatToInt (b : UInt64) : Int :=
  let (neg, m, e) := decomp b
  let n : Nat := if e ≥ 0 then m * pow2 e.toNat else m / pow2 (-e).toNat
  if neg then -(n : Int) else n

/-! ### CPython's hashes and set table -/

def hMod : Nat := 2 ^ 61 - 1
def u64 (n : Int) : UInt64 := (n.toNat % 2 ^ 64 + (if n < 0 then 2 ^ 64 - (-n).toNat % 2 ^ 64 else 0)).toUInt64

def hashInt (n : Int) : Int :=
  let r : Int := if n ≥ 0 then (n.toNat % hMod : Nat) else -((n.natAbs % hMod : Nat) : Int)
  if r == -1 then -2 else r

/-- `hash` of a non-integral double: its exact value modulo 2^61 - 1. -/
def hashFloatBits (b : UInt64) : Int :=
  if isNaN b then 0 else
  if !isFinite b then (if signBit b then -314159 else 314159) else
  let (neg, m, e) := decomp b
  let j := (-e).toNat % 61
  let r := (m % hMod) * (2 ^ ((61 - j) % 61)) % hMod
  let r : Int := if neg then -(r : Int) else r
  if r == -1 then -2 else r

/-- CPython's SipHash-1-3 (`Python/pyhash.c`) with the key `(k0, k1)`. -/
def siphash13 (k0 k1 : UInt64) (bs : List UInt8) : UInt64 :=
  let rotl (x : UInt64) (b : UInt64) : UInt64 := (x <<< b) ||| (x >>> (64 - b))
  let half (a b c d : UInt64) (s t : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
    let a := a + b
    let c := c + d
    let b := rotl b s ^^^ a
    let d := rotl d t ^^^ c
    (rotl a 32, b, c, d)
  let round (v : UInt64 × UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
    let (v0, v1, v2, v3) := v
    let (v0, v1, v2, v3) := half v0 v1 v2 v3 13 16
    let (v2, v1, v0, v3) := half v2 v1 v0 v3 17 21
    (v0, v1, v2, v3)
  let word (ws : List UInt8) : UInt64 :=
    (ws.zip (List.range ws.length)).foldl (fun acc (b, i) => acc ||| (b.toUInt64 <<< (8 * i).toUInt64)) 0
  let rec blocks (bs : List UInt8) (v : UInt64 × UInt64 × UInt64 × UInt64) (fuel : Nat) :
      List UInt8 × (UInt64 × UInt64 × UInt64 × UInt64) :=
    match fuel with
    | 0 => (bs, v)
    | fuel + 1 =>
      if bs.length < 8 then (bs, v) else
      let mi := word (bs.take 8)
      let (v0, v1, v2, v3) := v
      let (v0, v1, v2, v3) := round (v0, v1, v2, v3 ^^^ mi)
      blocks (bs.drop 8) (v0 ^^^ mi, v1, v2, v3) fuel
  let v : UInt64 × UInt64 × UInt64 × UInt64 :=
    (k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d, k0 ^^^ 0x6c7967656e657261, k1 ^^^ 0x7465646279746573)
  let (rest, v) := blocks bs v (bs.length / 8 + 1)
  let b : UInt64 := (bs.length.toUInt64 <<< 56) ||| word rest
  let (v0, v1, v2, v3) := v
  let (v0, v1, v2, v3) := round (v0, v1, v2, v3 ^^^ b)
  let v0 := v0 ^^^ b
  let v2 := v2 ^^^ 0xff
  let (v0, v1, v2, v3) := round (round (round (v0, v1, v2, v3)))
  (v0 ^^^ v1) ^^^ (v2 ^^^ v3)

/-- CPython's hash of a str with `PYTHONHASHSEED=0` (key zero): SipHash-1-3 of its
internal representation (one, two or four bytes a character, little-endian). -/
def strHash (x : String) : UInt64 :=
  let cs := x.toList
  if cs.isEmpty then 0 else
  let w := if cs.all (·.toNat < 256) then 1 else if cs.all (·.toNat < 65536) then 2 else 4
  let bs := cs.flatMap fun c => (List.range w).map fun i => ((c.toNat >>> (8 * i)) % 256).toUInt8
  let h := siphash13 0 0 bs
  if h == 0xFFFFFFFFFFFFFFFF then 0xFFFFFFFFFFFFFFFE else h

/-- CPython's hash of a normalized key (a str's as with `PYTHONHASHSEED=0`); an
object or a frozenset gets a fixed stand-in. -/
partial def chash (k : Val) : UInt64 :=
  match k with
  | .int n => u64 (hashInt n)
  | .float b => u64 (hashFloatBits b)
  | .none => 4238894112
  | .tuple vs =>
    let p1 : UInt64 := 11400714785074694791
    let p2 : UInt64 := 14029467366897019727
    let p5 : UInt64 := 2870177450012600261
    let acc := vs.foldl (fun acc v =>
      let acc := acc + chash v * p2
      let acc := (acc <<< 31) ||| (acc >>> 33)
      acc * p1) p5
    let acc := acc + (vs.length.toUInt64 ^^^ (p5 ^^^ 3527539))
    if acc == 0xFFFFFFFFFFFFFFFF then 1546275796 else acc
  | .str x => strHash x
  | v => hash v

/-- The key a dict or set stores a value under: equal keys are equal values
(`1`, `1.0`, `True`). Unhashable values raise `TypeError`. -/
partial def normKey (s : St) (v : Val) : Except Val Val :=
  match v.base with
  | .bool b => .ok (.int (if b then 1 else 0))
  | .float b => .ok (if isIntegral b then .int (floatToInt b) else if b == 0x8000000000000000 then .int 0 else .float b)
  | .tuple vs => (vs.mapM (normKey s)).map .tuple
  | .obj o => match s.get o with
    | .list _ | .dict .. | .set _ false | .deque _ => .error tErr
    | .set d true => .ok (.data "frozenset" ((d.idx.keys.mergeSort (fun a b => chash a ≤ chash b))))
    | .inst c _ => if (clsLookup s c "__hash__").isSome || (clsLookup s c "__eq__").isSome then
        .error (unsup "__hash__/__eq__ on a key") else .ok (.obj o)
    | _ => .ok (.obj o)
  | .data "slice" _ => .error tErr
  | b => .ok b

namespace CTab
def probe (mask : Nat) (i perturb : UInt64) : UInt64 × UInt64 :=
  let perturb := perturb >>> 5
  ((i * 5 + 1 + perturb) &&& mask.toUInt64, perturb)

/-- The first empty slot of the probe sequence of `h` (`set_insert_clean`). -/
partial def emptySlot (slots : Array Slot) (mask : Nat) (h : UInt64) : Nat :=
  let rec go (i perturb : UInt64) : Nat :=
    let i' := i.toNat
    let isEmpty (j : Nat) : Bool := match slots[j]? with | some .empty => true | _ => false
    if isEmpty i' then i' else
    let lin := if i' + 9 ≤ mask then (List.range 9).find? (fun j => isEmpty (i' + j + 1)) else none
    match lin with
    | some j => i' + j + 1
    | none => let (i, p) := probe mask i perturb; go i p
  go (h &&& mask.toUInt64) h

/-- The slot holding `k`, if any. -/
partial def findSlot (t : CTab) (h : UInt64) (k : Val) : Option Nat :=
  let rec go (i perturb : UInt64) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
    let i' := i.toNat
    let atJ (j : Nat) : Option (Option Nat) := match t.slots[j]? with
      | some .empty => some none
      | some (.full _ k') => if k' == k then some (some j) else none
      | _ => none
    match atJ i' with
    | some r => r
    | none =>
      let lin := if i' + 9 ≤ t.mask then (List.range 9).findSome? (fun j => atJ (i' + j + 1)) else none
      match lin with
      | some r => r
      | none => let (i, p) := probe t.mask i perturb; go i p fuel
  go (h &&& t.mask.toUInt64) h (t.slots.size + 64)

def resize (t : CTab) (minused : Nat) : CTab :=
  let rec size (n : Nat) (fuel : Nat) : Nat := match fuel with
    | 0 => n
    | fuel + 1 => if n ≤ minused then size (2 * n) fuel else n
  let n := size 8 64
  let slots := t.slots.foldl (fun sl s => match s with
    | .full h k => sl.set! (emptySlot sl (n - 1) h) (.full h k)
    | _ => sl) (Array.replicate n .empty)
  { t with slots := slots, mask := n - 1, fill := t.used }

/-- The probe sequence of `h` up to its first empty slot: that slot, and the last
dummy before it (`set_add_entry`, which reuses it). -/
partial def addSlot (slots : Array Slot) (mask : Nat) (h : UInt64) : Nat × Option Nat :=
  let rec go (i perturb : UInt64) (free : Option Nat) : Nat × Option Nat :=
    let i' := i.toNat
    let cands := if i' + 9 ≤ mask then (List.range 10).map (i' + ·) else [i']
    let rec scan (js : List Nat) (free : Option Nat) : Sum (Nat × Option Nat) (Option Nat) :=
      match js with
      | [] => .inr free
      | j :: r => match slots[j]? with
        | some .empty => .inl (j, free)
        | some .dummy => scan r (some j)
        | _ => scan r free
    match scan cands free with
    | .inl r => r
    | .inr free => let (i, p) := probe mask i perturb; go i p free
  go (h &&& mask.toUInt64) h none

/-- `set_add_entry` of a key that is not in the set: into the last dummy its probe
sequence passes before an empty slot, else that empty slot (then a resize if the
table is full enough). Checked against CPython 3.13 on random programs
(`results/checks/lean_sem/setfuzz.py`). -/
def add (t : CTab) (h : UInt64) (k : Val) : CTab :=
  match addSlot t.slots t.mask h with
  | (_, some j) => { t with slots := t.slots.set! j (.full h k), used := t.used + 1 }
  | (i, none) =>
    let t := { t with slots := t.slots.set! i (.full h k), fill := t.fill + 1, used := t.used + 1 }
    if t.fill * 5 < t.mask * 3 then t else t.resize (if t.used > 50000 then t.used * 2 else t.used * 4)

def discard (t : CTab) (h : UInt64) (k : Val) : CTab :=
  match t.findSlot h k with
  | some i => { t with slots := t.slots.set! i .dummy, used := t.used - 1 }
  | none => t

def keys (t : CTab) : List Val := t.slots.toList.filterMap fun | .full _ k => some k | _ => none

/-- `set_merge` of `src` into `t` (keys of `src` not yet in `t`, by `has`). -/
def merge (t src : CTab) (has : Val → Bool) : CTab :=
  if src.used == 0 then t else
  let t := if (t.fill + src.used) * 5 ≥ t.mask * 3 then t.resize ((t.used + src.used) * 2) else t
  if t.fill == 0 && t.mask == src.mask && src.fill == src.used then
    { t with slots := src.slots, fill := src.fill, used := src.used }
  else if t.fill == 0 then
    let slots := src.slots.foldl (fun sl s => match s with
      | .full h k => sl.set! (emptySlot sl t.mask h) (.full h k)
      | _ => sl) t.slots
    { t with slots := slots, fill := src.used, used := src.used }
  else
    src.slots.foldl (fun t s => match s with
      | .full h k => if has k then t else t.add h k
      | _ => t) t

/-- `set.pop`: the next key from the finger. -/
def pop (t : CTab) : Option (Val × CTab) :=
  if t.used == 0 then none else
  let n := t.mask + 1
  let start := t.finger % n
  match (List.range n).find? (fun j => match t.slots[(start + j) % n]! with | .full .. => true | _ => false) with
  | some j =>
    let i := (start + j) % n
    match t.slots[i]! with
    | .full _ k => some (k, { t with slots := t.slots.set! i .dummy, used := t.used - 1, finger := i + 1 })
    | _ => none
  | none => none
end CTab

namespace PDict
def find? (d : PDict) (k : Val) : Option (Val × Val) := d.idx[k]?.bind fun i => d.ents[i]?.join
def insert (d : PDict) (k : Val) (key v : Val) : PDict :=
  match d.idx[k]? with
  | some i => { d with ents := d.ents.set! i (some (((d.ents[i]?).join.map (·.1)).getD key, v)) }
  | none => { d with ents := d.ents.push (some (key, v)), idx := d.idx.insert k d.ents.size, size := d.size + 1,
                     tab := d.tab.map (·.add (chash k) k) }
def erase (d : PDict) (k : Val) : PDict :=
  match d.idx[k]? with
  | some i => { d with ents := d.ents.set! i none, idx := d.idx.erase k, size := d.size - 1,
                       tab := d.tab.map (·.discard (chash k) k) }
  | none => d
/-- The items: a dictionary's in insertion order, a set's in its table's order. -/
def items (d : PDict) : List (Val × Val) :=
  match d.tab with
  | some t => t.keys.filterMap d.find?
  | none => d.ents.toList.filterMap id
def keys (d : PDict) : List Val := d.items.map (·.1)
/-- An empty set. -/
def newSet : PDict := { tab := some {} }
/-- `set_merge`: the elements of the set `e` added to the set `d`. -/
def merge (d e : PDict) : PDict :=
  let base := e.idx.toList.foldl (fun (m : PDict) (nk, i) =>
    if m.idx.contains nk then m else match e.ents[i]? with
      | some (some kv) => { m with ents := m.ents.push (some kv), idx := m.idx.insert nk m.ents.size, size := m.size + 1 }
      | _ => m) d
  { base with tab := match d.tab, e.tab with
    | some t, some u => some (t.merge u d.idx.contains)
    | t, _ => t }
/-- After `difference_update`: if more than a quarter of the table is dummies, resize them away. -/
def compactSet (d : PDict) : PDict :=
  match d.tab with
  | some t => if t.fill - t.used ≤ t.mask / 4 then d
    else { d with tab := some (t.resize (if t.used > 50000 then t.used * 2 else t.used * 4)) }
  | none => d
/-- A copy of a set, as `set(s)` makes it (a merge into an empty set). -/
def copySet (d : PDict) : PDict := newSet.merge d
/-- `set.pop`. -/
def popSet (d : PDict) : Option (Val × PDict) :=
  match d.tab with
  | some t => match t.pop with
    | some (k, t') => match d.find? k with
      | some (key, _) => some (key, { (d.erase k) with tab := some t' })
      | none => none
    | none => none
  | none => none
end PDict

def cmpInt (a b : Int) : Ordering := compare a b

/-- Compare a number with a number exactly (`none` for NaN). -/
def numCmp (a b : Val) : Option Ordering :=
  let rat (v : Val) : Option (Option (Bool × Nat × Nat)) := match v with
    | .int n => some (some (n < 0, n.natAbs, 1))
    | .bool x => some (some (false, if x then 1 else 0, 1))
    | .float f => if isNaN f then none else if !isFinite f then some none else some (some (toRat f))
    | _ => none
  match a, b with
  | .int x, .int y => some (compare x y)
  | _, _ =>
    let inf (v : Val) : Int := match v with | .float f => if signBit f then -1 else 1 | _ => 0
    match rat a, rat b with
    | some (some (na, xa, ya)), some (some (nb, xb, yb)) =>
      let qa : Int := if na then -(xa * yb : Nat) else (xa * yb : Nat)
      let qb : Int := if nb then -(xb * ya : Nat) else (xb * ya : Nat)
      some (compare qa qb)
    | some none, some none => some (compare (inf a) (inf b))
    | some none, some (some _) => some (if inf a > 0 then .gt else .lt)
    | some (some _), some none => some (if inf b > 0 then .lt else .gt)
    | _, _ => none

def isNum (v : Val) : Bool := match v with | .int _ | .bool _ | .float _ => true | _ => false

/-- Equality of builtin values; `none` when it needs a user `__eq__`. -/
partial def eqN (s : St) (a b : Val) : Option Bool :=
  let a := a.base
  let b := b.base
  if isNum a && isNum b then some (numCmp a b == some .eq) else
  match a, b with
  | .none, .none => some true
  | .str x, .str y => some (x == y)
  | .tuple xs, .tuple ys => eqList s xs ys
  | .data "range" xs, .data "range" ys => some (xs == ys)
  | .obj o, .obj p =>
    if o == p then some true else
    match s.get o, s.get p with
    | .list xs, .list ys => eqList s xs.toList ys.toList
    | .deque xs, .deque ys => eqList s xs.toList ys.toList
    | .dict d _, .dict e _ =>
      if d.size != e.size then some false else
      d.items.foldl (fun acc (kv : Val × Val) => match acc with
        | some true => match normKey s kv.1 with
          | .ok k => match e.find? k with
            | some (_, v') => eqN s kv.2 v'
            | none => some false
          | .error _ => some false
        | r => r) (some true)
    | .set d _, .set e _ => some (d.size == e.size && d.idx.keys.all e.idx.contains)
    | .inst c _, _ => if (clsLookup s c "__eq__").isSome then none else some false
    | _, .inst c _ => if (clsLookup s c "__eq__").isSome then none else some false
    | _, _ => some false
  | .obj o, _ => match s.get o with
    | .inst c _ => if (clsLookup s c "__eq__").isSome then none else some false
    | _ => some false
  | _, .obj o => match s.get o with
    | .inst c _ => if (clsLookup s c "__eq__").isSome then none else some false
    | _ => some false
  | x, y => some (x == y)
where
  eqList (s : St) (xs ys : List Val) : Option Bool :=
    if xs.length != ys.length then some false else
    (xs.zip ys).foldl (fun acc (p : Val × Val) => match acc with
      | some true => eqN s p.1 p.2
      | r => r) (some true)

/-- `a < b` for builtin values; `TypeError` if unordered; `$Unsupported` for user `__lt__`. -/
partial def ltN (s : St) (a b : Val) : Except Val Bool :=
  let a := a.base
  let b := b.base
  if isNum a && isNum b then .ok (numCmp a b == some .lt) else
  match a, b with
  | .str x, .str y => .ok (decide (x < y))
  | .tuple xs, .tuple ys => seqLt s xs ys
  | .obj o, .obj p => match s.get o, s.get p with
    | .list xs, .list ys => seqLt s xs.toList ys.toList
    | .set d _, .set e _ => .ok (d.size < e.size && d.idx.keys.all e.idx.contains)
    | .inst .., _ | _, .inst .. => .error (unsup "ordering of instances")
    | _, _ => .error tErr
  | _, _ => .error tErr
where
  seqLt (s : St) (xs ys : List Val) : Except Val Bool :=
    match xs, ys with
    | [], [] => .ok false
    | [], _ => .ok true
    | _, [] => .ok false
    | x :: xs, y :: ys => match eqN s x y with
      | some true => seqLt s xs ys
      | some false => ltN s x y
      | none => .error (unsup "ordering of instances")

/-! ## str and repr of builtin values -/

def reprExcArgs (r : Val → Option String) (k : String) (args : List Val) : Option String := do
  let parts ← args.mapM r
  some (k ++ "(" ++ ", ".intercalate parts ++ ")")

mutual
/-- `repr` of a builtin value; `none` if it needs a user method. -/
partial def reprN (s : St) (v : Val) : Option String :=
  match v.base with
  | .none => some "None"
  | .bool b => some (if b then "True" else "False")
  | .int n => some (toString n)
  | .float b => some (floatRepr b)
  | .str x => some (strRepr x)
  | .tuple [x] => (reprN s x).map fun r => "(" ++ r ++ ",)"
  | .tuple xs => (xs.mapM (reprN s)).map fun rs => "(" ++ ", ".intercalate rs ++ ")"
  | .data "range" [a, b, .int 1] => do some ("range(" ++ (← reprN s a) ++ ", " ++ (← reprN s b) ++ ")")
  | .data "range" [a, b, c] => do some ("range(" ++ (← reprN s a) ++ ", " ++ (← reprN s b) ++ ", " ++ (← reprN s c) ++ ")")
  | .data "slice" [a, b, c] => do some ("slice(" ++ (← reprN s a) ++ ", " ++ (← reprN s b) ++ ", " ++ (← reprN s c) ++ ")")
  | .data "alias" [t, i] => do
    -- `types.GenericAlias` (`list[int]`): a type argument by its name
    let arg (a : Val) : Option String := match a with
      | .bfun k => if isTypeName k then some k else if k == "Ellipsis" then some "..." else reprN s a
      | _ => reprN s a
    let tn ← match t with | .bfun k => some k | _ => none
    let args := match i with | .tuple [] => ["()"] | .tuple xs => xs.filterMap arg | x => (arg x).toList
    some (tn ++ "[" ++ ", ".intercalate args ++ "]")
  | .data "dict_keys" [.obj o] | .data "dict_values" [.obj o] | .data "dict_items" [.obj o] =>
    match s.get o, v.base with
    | .dict d _, .data "dict_keys" _ => (d.keys.mapM (reprN s)).map fun rs => "dict_keys([" ++ ", ".intercalate rs ++ "])"
    | .dict d _, .data "dict_values" _ => (d.items.mapM (reprN s ·.2)).map fun rs => "dict_values([" ++ ", ".intercalate rs ++ "])"
    | .dict d _, _ => (d.items.mapM fun (a, b) => do some ("(" ++ (← reprN s a) ++ ", " ++ (← reprN s b) ++ ")")).map
        fun rs => "dict_items([" ++ ", ".intercalate rs ++ "])"
    | _, _ => none
  | .data "re.Match" [.str m, .int a, .int e] => some ("<re.Match object; span=(" ++ toString a ++ ", " ++ toString e ++ "), match=" ++ strRepr m ++ ">")
  | .bfun k =>
    if isTypeName k then
      some ("<class '" ++ (if ["Counter", "defaultdict", "OrderedDict", "deque"].contains k then "collections." else "") ++ k ++ "'>")
    else if k.startsWith "module:" then some ("<module '" ++ (k.drop 7).toString ++ "'>")
    else some ("<built-in function " ++ k ++ ">")
  | .err k args => reprExcArgs (reprN s) k args
  | .obj o => match s.get o with
    | .list xs => (xs.toList.mapM (reprN s)).map fun rs => "[" ++ ", ".intercalate rs ++ "]"
    | .deque xs => (xs.toList.mapM (reprN s)).map fun rs => "deque([" ++ ", ".intercalate rs ++ "])"
    | .dict d k =>
      let body := (d.items.mapM fun (a, b) => do some ((← reprN s a) ++ ": " ++ (← reprN s b))).map
        fun rs => "{" ++ ", ".intercalate rs ++ "}"
      match k with
      | .plain => body
      | .counter =>
        -- `Counter.__repr__` lists `most_common()`: by count, descending, stable
        let its := d.items.mergeSort (fun x y => match numCmp x.2 y.2 with | some .lt => false | _ => true)
        if its.isEmpty then some "Counter()" else
        (its.mapM fun (a, b) => do some ((← reprN s a) ++ ": " ++ (← reprN s b))).map
          fun rs => "Counter({" ++ ", ".intercalate rs ++ "})"
      | .dflt f => do some ("defaultdict(" ++ (← reprN s f) ++ ", " ++ (← body) ++ ")")
      | .ordered => if d.size == 0 then some "OrderedDict()" else body.map fun b => "OrderedDict(" ++ b ++ ")"
    | .set d fz =>
      if d.size == 0 then some (if fz then "frozenset()" else "set()") else
      (d.keys.mapM (reprN s)).map fun rs => (if fz then "frozenset({" else "{") ++ ", ".intercalate rs ++ (if fz then "})" else "}")
    | .cls _ q m _ _ _ => do
      let mn ← (match m with | .str x => some x | _ => none)
      some ("<class '" ++ (if mn == "builtins" then "" else mn ++ ".") ++ q ++ "'>")
    | .inst c _ => match clsLookup s c "__repr__" with
      | some _ => none
      | none => if isSubclass s c (.bfun "BaseException") then none else none
    | _ => none
  | _ => none

/-- `str` of a builtin value. -/
partial def strN (s : St) (v : Val) : Option String :=
  match v.base with
  | .str x => some x
  | .err _ [] => some ""
  | .err "KeyError" [a] => reprN s a
  | .err _ [a] => strN s a
  | .err _ args => reprN s (.tuple args)
  | .obj o => match s.get o with
    | .inst c _ => match clsLookup s c "__str__", clsLookup s c "__repr__" with
      | none, none => none
      | _, _ => none
    | _ => reprN s v
  | _ => reprN s v
end

/-! ## Numbers -/

def asNum (v : Val) : Option Val :=
  match v.base with
  | .bool b => some (.int (if b then 1 else 0))
  | .int n => some (.int n)
  | .float f => some (.float f)
  | _ => none

def toF (v : Val) : Except Val Float :=
  match v with
  | .int n => let b := intToBits n; if isFinite b then .ok (fOf b) else .error (.err "OverflowError" [])
  | .float f => .ok (fOf f)
  | .bool b => .ok (if b then 1.0 else 0.0)
  | _ => .error tErr

def fV (x : Float) : Val := .float (bOf x)

def zde : Val := .err "ZeroDivisionError" []

def floatFloorMod (x y : UInt64) : Except Val (UInt64 × UInt64) :=
  if (y &&& 0x7FFFFFFFFFFFFFFF) == 0 then .error zde else
  let md := fmodBits x y
  let fy := fOf y
  let fmd := fOf md
  let md' := if fmd != 0.0 then (if (fy < 0.0) != (fmd < 0.0) then bOf (fmd + fy) else md)
             else (if signBit y then 0x8000000000000000 else 0)
  let dv := (fOf x - fOf md') / fy
  let fd := if dv != 0.0 then (let fl := dv.floor; if dv - fl > 0.5 then fl + 1.0 else fl)
            else (if signBit x != signBit y then -0.0 else 0.0)
  .ok (bOf fd, md')

def intPow (a : Int) (b : Nat) : Int := a ^ b

/-- Two's-complement `&`, `|`, `^` on integers. -/
def iand (a b : Int) : Int :=
  match a, b with
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .negSucc x, .ofNat y => .ofNat (y - (y &&& x))
  | .ofNat x, .negSucc y => .ofNat (x - (x &&& y))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)
def ior (a b : Int) : Int :=
  match a, b with
  | .ofNat x, .ofNat y => .ofNat (x ||| y)
  | .negSucc x, .ofNat y => .negSucc (x - (x &&& y))
  | .ofNat x, .negSucc y => .negSucc (y - (y &&& x))
  | .negSucc x, .negSucc y => .negSucc (x &&& y)
def ixor (a b : Int) : Int :=
  match a, b with
  | .ofNat x, .ofNat y => .ofNat (x ^^^ y)
  | .negSucc x, .ofNat y => .negSucc (x ^^^ y)
  | .ofNat x, .negSucc y => .negSucc (x ^^^ y)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

/-- Arithmetic on numbers. -/
def numOp (op : String) (a b : Val) : Option (Except Val Val) :=
  match asNum a, asNum b with
  | some (.int x), some (.int y) => some <| match op with
    | "Add" => .ok (.int (x + y))
    | "Sub" => .ok (.int (x - y))
    | "Mult" => .ok (.int (x * y))
    | "FloorDiv" => if y == 0 then .error zde else .ok (.int (x.fdiv y))
    | "Mod" => if y == 0 then .error zde else .ok (.int (x.fmod y))
    | "Div" => if y == 0 then .error zde else
      let b := ratToBits ((x < 0) != (y < 0)) x.natAbs y.natAbs
      if isFinite b then .ok (.float b) else .error (.err "OverflowError" [])
    | "Pow" => if y ≥ 0 then
        (if y.toNat > 100000 && x.natAbs > 1 then .error (unsup "huge power") else .ok (.int (intPow x y.toNat)))
      else if x == 0 then .error zde
      else .ok (.float (ratToBits (x < 0 && y.natAbs % 2 == 1) 1 (x.natAbs ^ y.natAbs)))
    | "LShift" => if y < 0 then .error vErr else .ok (.int (x * 2 ^ y.toNat))
    | "RShift" => if y < 0 then .error vErr else .ok (.int (x.fdiv (2 ^ y.toNat)))
    | "BitAnd" => .ok (.int (iand x y))
    | "BitOr" => .ok (.int (ior x y))
    | "BitXor" => .ok (.int (ixor x y))
    | _ => .error tErr
  | some x, some y =>
    if op ∈ ["LShift", "RShift", "BitAnd", "BitOr", "BitXor"] then some (.error tErr) else
    some <| do
      let fx ← toF x
      let fy ← toF y
      match op with
      | "Add" => .ok (fV (fx + fy))
      | "Sub" => .ok (fV (fx - fy))
      | "Mult" => .ok (fV (fx * fy))
      | "Div" => if fy == 0.0 then .error zde else .ok (fV (fx / fy))
      | "FloorDiv" => do let (d, _) ← floatFloorMod (bOf fx) (bOf fy); .ok (.float d)
      | "Mod" => do let (_, m) ← floatFloorMod (bOf fx) (bOf fy); .ok (.float m)
      | "Pow" =>
        if fx == 0.0 && fy < 0.0 then .error zde
        else if fx < 0.0 && fy != fy.floor then .error (unsup "complex power")
        else
          let r := Float.pow fx fy
          if r.isInf && !fx.isInf && !fy.isInf then .error (.err "OverflowError" []) else .ok (fV r)
      | _ => .error tErr
  | _, _ => none

/-! ## Constants -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- Unescape the body of a Python string literal (as `repr` writes it). -/
def unescape (cs : List Char) : Option (List Char) :=
  let rec go (cs : List Char) (acc : List Char) (fuel : Nat) : Option (List Char) :=
    match fuel with
    | 0 => some acc.reverse
    | fuel + 1 =>
    match cs with
    | [] => some acc.reverse
    | '\\' :: c :: r =>
      let hexN (n : Nat) : Option (List Char) := do
        let ds := r.take n
        if ds.length < n then none else
        let v ← ds.foldlM (fun a c => (hexVal c).map (a * 16 + ·)) 0
        go (r.drop n) (Char.ofNat v :: acc) fuel
      match c with
      | 'n' => go r ('\n' :: acc) fuel
      | 't' => go r ('\t' :: acc) fuel
      | 'r' => go r ('\r' :: acc) fuel
      | '\\' => go r ('\\' :: acc) fuel
      | '\'' => go r ('\'' :: acc) fuel
      | '"' => go r ('"' :: acc) fuel
      | 'x' => hexN 2
      | 'u' => hexN 4
      | 'U' => hexN 8
      | '0' => go r ('\x00' :: acc) fuel
      | 'a' => go r ('\x07' :: acc) fuel
      | 'b' => go r ('\x08' :: acc) fuel
      | 'f' => go r ('\x0c' :: acc) fuel
      | 'v' => go r ('\x0b' :: acc) fuel
      | _ => none
    | c :: r => go r (c :: acc) fuel
  go cs [] (cs.length + 1)

/-- A constant from its `repr`. -/
def constOf (c : String) : Val :=
  match c with
  | "None" => .none
  | "True" => .bool true
  | "False" => .bool false
  | "Ellipsis" => .bfun "Ellipsis"
  | "inf" => .float posInf
  | _ =>
    let cs := c.toList
    match cs with
    | '\'' :: _ | '"' :: _ =>
      match unescape ((cs.drop 1).dropLast) with
      | some u => .str (ofChars u)
      | none => .err "$Unsupported" [.str "string constant"]
    | _ => match c.toInt? with
      | some n => .int n
      | none => match parseFloat c with
        | some b => .float b
        | none => .err "$Unsupported" [.str ("constant " ++ c)]


/-! ## Indices, slices, sequences -/

def idxNorm (n : Nat) (i : Int) : Option Nat :=
  let j := if i < 0 then i + n else i
  if 0 ≤ j && j < n then some j.toNat else none

def asIndex (v : Val) : Except Val Int :=
  match v.base with
  | .int n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error tErr

/-- `PySlice_AdjustIndices`: start, stop, step and length of a slice of a sequence of length `n`. -/
def sliceAdj (n : Nat) (lo hi st : Val) : Except Val (Int × Int × Int × Nat) := do
  let step ← match st with | .none => pure 1 | v => asIndex v
  if step == 0 then throw vErr
  let n' : Int := n
  let adj (v : Val) (dflt : Int) : Except Val Int := match v with
    | .none => pure dflt
    | v => do
      let i ← asIndex v
      if i < 0 then
        let i := i + n'
        pure (if i < 0 then (if step < 0 then -1 else 0) else i)
      else pure (if i ≥ n' then (if step < 0 then n' - 1 else n') else i)
  let start ← adj lo (if step < 0 then n' - 1 else 0)
  let stop ← adj hi (if step < 0 then -1 else n')
  let cnt : Nat :=
    if step > 0 then (if stop > start then ((stop - start + step - 1) / step).toNat else 0)
    else (if start > stop then ((start - stop - step - 1) / (-step)).toNat else 0)
  pure (start, stop, step, cnt)

/-- The indices a slice selects in a sequence of length `n`. -/
def sliceIdx (n : Nat) (lo hi st : Val) : Except Val (List Nat) := do
  let step ← match st with | .none => pure 1 | v => asIndex v
  if step == 0 then throw vErr
  let n' : Int := n
  let adj (v : Val) (dflt : Int) : Except Val Int := match v with
    | .none => pure dflt
    | v => do
      let i ← asIndex v
      if i < 0 then
        let i := i + n'
        pure (if i < 0 then (if step < 0 then -1 else 0) else i)
      else pure (if i ≥ n' then (if step < 0 then n' - 1 else n') else i)
  let start ← adj lo (if step < 0 then n' - 1 else 0)
  let stop ← adj hi (if step < 0 then -1 else n')
  let cnt : Nat :=
    if step > 0 then (if stop > start then ((stop - start + step - 1) / step).toNat else 0)
    else (if start > stop then ((start - stop - step - 1) / (-step)).toNat else 0)
  pure ((List.range cnt).map fun (k : Nat) => (start + (k : Int) * step).toNat)

def rangeLen (a b c : Int) : Nat :=
  if c > 0 then (if b > a then ((b - a + c - 1) / c).toNat else 0)
  else if c < 0 then (if a > b then ((a - b - c - 1) / (-c)).toNat else 0) else 0

def strChars (x : String) : List Val := x.toList.map fun c => .str c.toString

/-- The items of an iterable that is no iterator, without callbacks. -/
def nativeList (s : St) (v : Val) : Option (List Val) :=
  match v.base with
  | .tuple vs => some vs
  | .str x => some (strChars x)
  | .data "range" [.int a, .int b, .int c] =>
    let n := rangeLen a b c
    if n > 10000000 then none else some ((List.range n).map fun (k : Nat) => .int (a + (k : Int) * c))
  | .data "dict_keys" [.obj o] | .data "dict_values" [.obj o] | .data "dict_items" [.obj o] =>
    match s.get o, v.base with
    | .dict d _, .data "dict_keys" _ => some d.keys
    | .dict d _, .data "dict_values" _ => some (d.items.map (·.2))
    | .dict d _, _ => some (d.items.map fun p => .tuple [p.1, p.2])
    | _, _ => none
  | .obj o => match s.get o with
    | .list vs | .deque vs => some vs.toList
    | .dict d _ | .set d _ => some d.keys
    | _ => none
  | _ => none

def dictFind (ents : Array (Option (Val × Val))) (i : Nat) : Option (Nat × Val × Val) :=
  let rec go (j : Nat) (fuel : Nat) : Option (Nat × Val × Val) :=
    match fuel with
    | 0 => none
    | fuel + 1 => if h : j < ents.size then (match ents[j] with
        | some (k, v) => some (j, k, v)
        | none => go (j + 1) fuel) else none
  go i (ents.size + 1)

def mkSet (s : St) (xs : List Val) : Except Val PDict :=
  xs.foldlM (fun d x => do let k ← normKey s x; pure (d.insert k x .none)) PDict.newSet

/-- CPython's set algebra (`setobject.c`), which fixes the result's table order. -/
def setInsert (s : St) (r : PDict) (key : Val) : PDict :=
  match normKey s key with | .ok nk => r.insert nk key .none | .error _ => r
def setErase (s : St) (r : PDict) (key : Val) : PDict :=
  match normKey s key with | .ok nk => r.erase nk | .error _ => r
def setHas (s : St) (r : PDict) (key : Val) : Bool :=
  match normKey s key with | .ok nk => r.idx.contains nk | .error _ => false
def setUnion (d e : PDict) : PDict := d.copySet.merge e
def setInter (s : St) (d e : PDict) : PDict :=
  let (so, other) := if e.size > d.size then (e, d) else (d, e)
  other.keys.foldl (fun r k => if setHas s so k then setInsert s r k else r) PDict.newSet
def setDiff (s : St) (d e : PDict) : PDict :=
  if d.size / 4 > e.size then (e.keys.foldl (setErase s) d.copySet).compactSet
  else d.keys.foldl (fun r k => if setHas s e k then r else setInsert s r k) PDict.newSet
/-- `symmetric_difference_update`: each key of `e` toggled in `d`. -/
def setSymUpd (s : St) (d e : PDict) : PDict :=
  e.keys.foldl (fun r k => if setHas s r k then setErase s r k else setInsert s r k) d
def setSym (s : St) (d e : PDict) : PDict := setSymUpd s e.copySet d

def mkDict (s : St) (kvs : List (Val × Val)) : Except Val PDict :=
  kvs.foldlM (fun d (k, v) => do let nk ← normKey s k; pure (d.insert nk k v)) {}

/-- A stable merge sort under a fallible `<` (tail-recursive merge). -/
partial def msort {α} (lt : α → α → Except Val Bool) (xs : List α) : Except Val (List α) :=
  match xs with
  | [] | [_] => pure xs
  | _ => do
    let n := xs.length / 2
    let a ← msort lt (xs.take n)
    let b ← msort lt (xs.drop n)
    merge a b []
where
  merge (a b acc : List α) : Except Val (List α) :=
    match a, b with
    | [], b => pure (acc.reverse ++ b)
    | a, [] => pure (acc.reverse ++ a)
    | x :: a', y :: b' => do
      if (← lt y x) then merge a b' (y :: acc) else merge a' b (x :: acc)

/-- `a <= b` for builtin values. -/
def leN (s : St) (a b : Val) : Except Val Bool :=
  if isNum a.base && isNum b.base then .ok (match numCmp a.base b.base with | some .lt | some .eq => true | _ => false)
  else match a.base, b.base with
    | .obj o, .obj p => match s.get o, s.get p with
      | .set d _, .set e _ => .ok (d.idx.keys.all e.idx.contains)
      | _, _ => do let r ← ltN s b a; pure (!r)
    | _, _ => do let r ← ltN s b a; pure (!r)

/-! ## Formatting -/

structure Spec where
  fill : Char := ' '
  align : Option Char := none
  sign : Char := '-'
  alt : Bool := false
  zero : Bool := false
  width : Nat := 0
  group : Option Char := none
  prec : Option Nat := none
  ty : Option Char := none

def parseSpec (sp : String) : Option Spec := do
  let cs := sp.toList
  let isAlign (c : Char) := c == '<' || c == '>' || c == '^' || c == '='
  let (fill, align, cs) := match cs with
    | f :: a :: r => if isAlign a then (f, some a, r) else if isAlign f then (' ', some f, a :: r) else (' ', none, cs)
    | [a] => if isAlign a then (' ', some a, []) else (' ', none, cs)
    | [] => (' ', none, cs)
  let (sign, cs) := match cs with
    | c :: r => if c == '+' || c == '-' || c == ' ' then (c, r) else ('-', cs)
    | [] => ('-', cs)
  let (alt, cs) := match cs with | '#' :: r => (true, r) | _ => (false, cs)
  let (zero, cs) := match cs with | '0' :: r => (true, r) | _ => (false, cs)
  let w := cs.takeWhile Char.isDigit
  let cs := cs.drop w.length
  let width := (String.ofList w).toNat?.getD 0
  let (group, cs) := match cs with | ',' :: r => (some ',', r) | '_' :: r => (some '_', r) | _ => (none, cs)
  let (prec, cs) ← match cs with
    | '.' :: r =>
      let p := r.takeWhile Char.isDigit
      if p.isEmpty then none else some ((String.ofList p).toNat?, r.drop p.length)
    | _ => some (none, cs)
  let ty ← match cs with | [] => some none | [t] => some (some t) | _ => none
  some { fill, align, sign, alt, zero, width, group, prec, ty }

def groupDigits (ds : String) (g : Char) : String :=
  let cs := ds.toList.reverse
  let rec go (cs : List Char) (n : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc
    | c :: r => go r (n + 1) (if n > 0 && n % 3 == 0 then c :: g :: acc else c :: acc)
  String.ofList (go cs 0 [])

def pad (sp : Spec) (body : String) (sgn : String) (numeric : Bool) : String :=
  let len := sgn.length + body.length
  if len ≥ sp.width then sgn ++ body else
  let n := sp.width - len
  let fill := if sp.zero && sp.align.isNone then '0' else sp.fill
  let align := sp.align.getD (if sp.zero then '=' else if numeric then '>' else '<')
  let rep (k : Nat) := String.ofList (List.replicate k fill)
  match align with
  | '<' => sgn ++ body ++ rep n
  | '^' => rep (n / 2) ++ sgn ++ body ++ rep (n - n / 2)
  | '=' => sgn ++ rep n ++ body
  | _ => rep n ++ sgn ++ body

/-- `%g`-style: precision `p` significant digits, trailing zeros stripped unless `alt`. -/
def gStr (b : UInt64) (p : Nat) (alt : Bool) (noneTy : Bool) : String :=
  let p := if p == 0 then 1 else p
  if !isFinite b then floatRepr b else
  let (neg, num, _) := toRat b
  let sgn := if neg then "-" else ""
  if num == 0 then sgn ++ (if alt then "0." ++ String.ofList (List.replicate (p - 1) '0') else (if noneTy then "0.0" else "0")) else
  -- the exponent after rounding to p digits
  let e := expStr (b &&& 0x7FFFFFFFFFFFFFFF) (p - 1)
  let ex := ((e.splitOn "e").getLast!.toInt?).getD 0
  let strip (x : String) : String :=
    if alt || !x.contains '.' then x else
    let y := (x.toList.reverse.dropWhile (· == '0')).reverse
    let y := if y.getLast? == some '.' then (if noneTy then y ++ ['0'] else y.dropLast) else y
    String.ofList y
  if -4 ≤ ex && ex < p then sgn ++ strip (fixedStr (b &&& 0x7FFFFFFFFFFFFFFF) (p - 1 - ex).toNat)
  else
    let m := (e.splitOn "e").head!
    let rest := (e.splitOn "e").getLast!
    sgn ++ strip m ++ "e" ++ rest

def fmtInt (sp : Spec) (n : Int) : Option String := do
  let ty := sp.ty.getD 'd'
  let a := n.natAbs
  let body ← match ty with
    | 'd' | 'n' => some (toString a)
    | 'x' => some ((if sp.alt then "0x" else "") ++ String.ofList (Nat.toDigits 16 a))
    | 'X' => some ((if sp.alt then "0X" else "") ++ (String.ofList (Nat.toDigits 16 a)).toUpper)
    | 'o' => some ((if sp.alt then "0o" else "") ++ String.ofList (Nat.toDigits 8 a))
    | 'b' => some ((if sp.alt then "0b" else "") ++ String.ofList (Nat.toDigits 2 a))
    | 'c' => some (Char.ofNat a).toString
    | _ => none
  let body := match sp.group with | some g => if ty == 'd' then groupDigits body g else body | none => body
  let sgn := if n < 0 then "-" else if sp.sign == '+' then "+" else if sp.sign == ' ' then " " else ""
  some (pad sp body sgn true)

def fmtFloat (sp : Spec) (b : UInt64) : Option String := do
  let neg := signBit b && !isNaN b
  let a := b &&& 0x7FFFFFFFFFFFFFFF
  let body ← match sp.ty with
    | some 'f' | some 'F' => some (fixedStr a (sp.prec.getD 6))
    | some 'e' => some (expStr a (sp.prec.getD 6))
    | some 'E' => some (expStr a (sp.prec.getD 6)).toUpper
    | some '%' => some (fixedStr (bOf (fOf a * 100.0)) (sp.prec.getD 6) ++ "%")
    | some 'g' => some (gStr a (sp.prec.getD 6) sp.alt false)
    | some 'G' => some (gStr a (sp.prec.getD 6) sp.alt false).toUpper
    | none => match sp.prec with
      | some p => some (gStr a p sp.alt true)
      | none => some (floatRepr a)
    | _ => none
  let body := match sp.group with
    | some g => match body.splitOn "." with
      | [ip, fp] => groupDigits ip g ++ "." ++ fp
      | _ => if body.all Char.isDigit then groupDigits body g else body
    | none => body
  let sgn := if neg then "-" else if sp.sign == '+' then "+" else if sp.sign == ' ' then " " else ""
  some (pad sp body sgn true)

def fmtStr (sp : Spec) (x : String) : Option String :=
  if sp.ty.isSome && sp.ty != some 's' then none else
  let x := match sp.prec with | some p => String.ofList (x.toList.take p) | none => x
  some (pad sp x "" false)

/-- `format(v, spec)` of a builtin value. -/
def formatN (s : St) (v : Val) (spec : String) : Option String := do
  if spec.isEmpty then strN s v else
  let sp ← parseSpec spec
  match v.base with
  | .bool b => if sp.ty.isNone then fmtStr sp (if b then "True" else "False") else fmtInt sp (if b then 1 else 0)
  | .int n => match sp.ty with
    | some 'f' | some 'F' | some 'e' | some 'E' | some 'g' | some 'G' | some '%' => fmtFloat sp (intToBits n)
    | _ => fmtInt sp n
  | .float b => fmtFloat sp b
  | .str x => fmtStr sp x
  | _ => match strN s v with
    | some x => if sp.ty.isNone && sp.prec.isNone then some (pad sp x "" false) else none
    | none => none

/-- printf-style `fmt % args` with builtin values. -/
def percentN (s : St) (fmt : String) (args : Val) : Except Val String := do
  let argl : List Val := match args.base with | .tuple vs => vs | v => [v]
  let isMap := match args.base with
    | .obj o => match s.get o with | .dict .. => true | _ => false
    | _ => false
  let rec go (cs : List Char) (as : List Val) (acc : String) (fuel : Nat) : Except Val String :=
    match fuel with
    | 0 => .error (unsup "format")
    | fuel + 1 =>
    match cs with
    | [] => if as.isEmpty || isMap then .ok acc else .error tErr
    | '%' :: '%' :: r => go r as (acc ++ "%") fuel
    | '%' :: r =>
      if r.head? == some '(' then .error (unsup "%(name) format") else
      let flags := r.takeWhile (fun c => c == '-' || c == '+' || c == ' ' || c == '#' || c == '0')
      let r := r.drop flags.length
      let w := r.takeWhile Char.isDigit
      let r := r.drop w.length
      let (prec, r) := match r with
        | '.' :: r' => let p := r'.takeWhile Char.isDigit; (some ((String.ofList p).toNat?.getD 0), r'.drop p.length)
        | _ => (none, r)
      match r with
      | [] => .error vErr
      | t :: r =>
        match as with
        | [] => .error tErr
        | a :: as' =>
          let sp : Spec := { align := if flags.contains '-' then some '<' else none,
                             sign := if flags.contains '+' then '+' else if flags.contains ' ' then ' ' else '-',
                             alt := flags.contains '#', zero := flags.contains '0' && !flags.contains '-',
                             width := (String.ofList w).toNat?.getD 0, prec := prec }
          let res : Except Val String := match t with
            | 's' => match strN s a with
              | some x => .ok (pad { sp with zero := false } (match prec with | some p => String.ofList (x.toList.take p) | none => x) "" false)
              | none => .error (unsup "%s of an object")
            | 'r' => match reprN s a with
              | some x => .ok (pad { sp with zero := false } x "" false)
              | none => .error (unsup "%r of an object")
            | 'd' | 'i' | 'u' => match a.base with
              | .int n => .ok ((fmtInt { sp with ty := some 'd' } n).getD "")
              | .bool b => .ok ((fmtInt { sp with ty := some 'd' } (if b then 1 else 0)).getD "")
              | .float b => if isFinite b then .ok ((fmtInt { sp with ty := some 'd' } (floatToInt b)).getD "") else .error (.err "OverflowError" [])
              | _ => .error tErr
            | 'x' | 'X' | 'o' => match a.base with
              | .int n => .ok ((fmtInt { sp with ty := some t } n).getD "")
              | _ => .error tErr
            | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' => match a.base with
              | .int n => .ok ((fmtFloat { sp with ty := some t, prec := some (prec.getD 6) } (intToBits n)).getD "")
              | .float b => .ok ((fmtFloat { sp with ty := some t, prec := some (prec.getD 6) } b).getD "")
              | .bool x => .ok ((fmtFloat { sp with ty := some t, prec := some (prec.getD 6) } (intToBits (if x then 1 else 0))).getD "")
              | _ => .error tErr
            | 'c' => match a.base with
              | .int n => .ok (pad sp (Char.ofNat n.toNat).toString "" false)
              | .str x => if x.length == 1 then .ok (pad sp x "" false) else .error tErr
              | _ => .error tErr
            | _ => .error vErr
          match res with
          | .ok x => go r as' (acc ++ x) fuel
          | .error e => .error e
    | c :: r => go r as (acc.push c) fuel
  go fmt.toList argl "" (fmt.length + 2)


/-! ## Regular expressions (a subset of `re`) -/

inductive RAtom where
  | lit (c : Char)
  | any
  | cls (neg : Bool) (items : List (Char × Char))

structure RPiece where
  atom : RAtom
  lo : Nat
  hi : Option Nat

/-- A pattern: anchors, and atoms with greedy quantifiers. Groups, alternation,
lazy quantifiers, backreferences and look-around are not covered. -/
structure RPat where
  bol : Bool
  eol : Bool
  pieces : List RPiece

def classEsc (c : Char) : Option (List (Char × Char)) :=
  match c with
  | 'd' => some [('0', '9')]
  | 'w' => some [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]
  | 's' => some [(' ', ' '), ('\t', '\t'), ('\n', '\n'), ('\r', '\r'), ('\x0b', '\x0b'), ('\x0c', '\x0c')]
  | _ => none

/-- The items of a class after `[` (and `^`), up to `]`. -/
partial def parseClass (cs : List Char) (acc : List (Char × Char)) (first : Bool) :
    Option (List (Char × Char) × List Char) :=
  match cs with
  | [] => none
  | ']' :: r => if first then parseClass r ((']', ']') :: acc) false else some (acc.reverse, r)
  | '\\' :: c :: r => match classEsc c with
    | some its => parseClass r (its.reverse ++ acc) false
    | none => if c.isAlphanum then none else parseClass r ((c, c) :: acc) false
  | a :: '-' :: b :: r => if b == ']' then parseClass (b :: r) (('-', '-') :: (a, a) :: acc) false
    else parseClass r ((a, b) :: acc) false
  | c :: r => parseClass r ((c, c) :: acc) false

partial def parsePieces (cs : List Char) (acc : List RPiece) : Option (List RPiece × Bool) :=
  match cs with
  | [] => some (acc.reverse, false)
  | ['$'] => some (acc.reverse, true)
  | c :: r =>
    let atom : Option (RAtom × List Char) := match c, r with
      | '.', r => some (.any, r)
      | '[', '^' :: r => (parseClass r [] true).map fun (its, r) => (.cls true its, r)
      | '[', r => (parseClass r [] true).map fun (its, r) => (.cls false its, r)
      | '\\', d :: r => match classEsc d with
        | some its => some (.cls false its, r)
        | none => if d.isAlphanum then none else some (.lit d, r)
      | c, r => if "()|{}*+?^$".toList.contains c then none else some (.lit c, r)
    match atom with
    | none => none
    | some (a, r) =>
      let digits (cs : List Char) : Option (Nat × List Char) :=
        let ds := cs.takeWhile Char.isDigit
        if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.drop ds.length)
      let q : Option (Nat × Option Nat × List Char) := match r with
        | '?' :: r => some (0, some 1, r)
        | '*' :: r => some (0, none, r)
        | '+' :: r => some (1, none, r)
        | '{' :: r => match digits r with
          | some (m, '}' :: r) => some (m, some m, r)
          | some (m, ',' :: '}' :: r) => some (m, none, r)
          | some (m, ',' :: r) => match digits r with
            | some (n, '}' :: r) => some (m, some n, r)
            | _ => none
          | _ => none
        | r => some (1, some 1, r)
      match q with
      | none => none
      | some (lo, hi, r) =>
        if r.head? == some '?' || r.head? == some '+' then none
        else parsePieces r ({ atom := a, lo := lo, hi := hi } :: acc)

def parsePat (p : String) : Option RPat :=
  let cs := p.toList
  let (bol, cs) := match cs with | '^' :: r => (true, r) | cs => (false, cs)
  (parsePieces cs []).map fun (ps, eol) => { bol := bol, eol := eol, pieces := ps }

def RAtom.ok : RAtom → Char → Bool
  | .lit c, d => c == d
  | .any, d => d != '\n'
  | .cls neg its, d => (its.any fun (a, b) => a ≤ d && d ≤ b) != neg

/-- The end of a greedy match of `ps` from `pos` (backtracking), if any. -/
partial def rmatch (cs : Array Char) (eol full : Bool) : List RPiece → Nat → Option Nat
  | [], pos =>
    let n := cs.size
    if full then (if pos == n then some pos else none)
    else if eol then (if pos == n || (pos + 1 == n && cs[pos]! == '\n') then some pos else none)
    else some pos
  | p :: rest, pos =>
    let rec count (k : Nat) : Nat :=
      if (match p.hi with | some h => k < h | none => true) && pos + k < cs.size && p.atom.ok cs[pos + k]!
      then count (k + 1) else k
    let mx := count 0
    let rec tryK (k : Nat) : Option Nat :=
      if k < p.lo then none else
      match rmatch cs eol full rest (pos + k) with
      | some e => some e
      | none => if k == 0 then none else tryK (k - 1)
    tryK mx

/-- The first match at or after `pos`: its start and end. -/
partial def rsearch (pat : RPat) (cs : Array Char) (pos : Nat) (full : Bool) : Option (Nat × Nat) :=
  if pos > cs.size then none else
  match rmatch cs pat.eol full pat.pieces pos with
  | some e => some (pos, e)
  | none => if pat.bol then none else rsearch pat cs (pos + 1) full

/-- `re.findall` without groups: the non-overlapping matches, left to right. -/
partial def rfindall (pat : RPat) (cs : Array Char) (pos : Nat) (acc : List String) : List String :=
  match rsearch pat cs pos false with
  | some (a, e) =>
    let m := String.ofList ((cs.toList.drop a).take (e - a))
    if pat.bol then (m :: acc).reverse
    else rfindall pat cs (if e == a then e + 1 else e) (m :: acc)
  | none => acc.reverse

/-- `re.sub` with a replacement string without escapes. -/
def rsub (rp : RPat) (cs : Array Char) (r : List Char) (pos : Nat) (acc : List Char) : Nat → List Char
  | 0 => acc
  | fuel + 1 =>
    match rsearch rp cs pos false with
    | some (a, e) =>
      let acc := acc ++ (cs.toList.drop pos).take (a - pos) ++ r
      if e == a then (if a < cs.size then rsub rp cs r (a + 1) (acc ++ [cs[a]!]) fuel else acc)
      else if rp.bol then acc ++ cs.toList.drop e
      else rsub rp cs r e acc fuel
    | none => acc ++ cs.toList.drop pos

/-! ## Operations with callbacks -/

instance {α} : Inhabited (M α) := ⟨fun s _ => .ok s .none⟩

def attrErr : Val := .err "AttributeError" []

/-- The special methods a builtin value has as bound methods, and the operator each is. -/
def dunderNames : List String :=
  ["__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__", "__add__", "__sub__", "__mul__",
   "__truediv__", "__floordiv__", "__mod__", "__pow__", "__contains__", "__getitem__", "__len__",
   "__str__", "__repr__", "__iter__", "__next__", "__bool__", "__neg__", "__abs__"]
def keyErr (k : Val) : Val := .err "KeyError" [k]

def strMethods : List String :=
  ["upper", "lower", "swapcase", "capitalize", "title", "casefold", "isupper", "islower", "istitle",
   "isalpha", "isdigit", "isnumeric", "isdecimal", "isalnum", "isspace", "isascii", "strip", "lstrip",
   "rstrip", "split", "rsplit", "splitlines", "join", "replace", "count", "find", "rfind", "index",
   "rindex", "startswith", "endswith", "zfill", "center", "ljust", "rjust", "format", "partition",
   "rpartition", "translate", "maketrans", "removeprefix", "removesuffix", "encode", "expandtabs",
   "isidentifier", "isprintable"]
def listMethods : List String :=
  ["append", "extend", "insert", "remove", "pop", "index", "count", "sort", "reverse", "copy", "clear"]
def dictMethods : List String :=
  ["keys", "values", "items", "get", "setdefault", "pop", "popitem", "update", "copy", "clear", "fromkeys",
   "most_common", "elements", "subtract", "total", "move_to_end"]
def setMethods : List String :=
  ["add", "remove", "discard", "pop", "clear", "update", "union", "intersection", "difference",
   "symmetric_difference", "issubset", "issuperset", "isdisjoint", "copy", "intersection_update",
   "difference_update", "symmetric_difference_update"]
def dequeMethods : List String :=
  ["append", "appendleft", "pop", "popleft", "extend", "extendleft", "rotate", "clear", "count", "index",
   "copy", "reverse", "remove", "insert"]

/-- Standard modules a program may import without this interpretation having them. -/
def opaqueModules : List String :=
  ["os", "random", "time", "threading", "io", "array", "decimal", "fractions", "statistics", "datetime",
   "math.cmath", "cmath", "struct", "pprint", "abc", "dataclasses", "enum", "numbers", "atexit", "gc"]

/-- The names of the modules this interpretation has, each with its names. -/
def moduleNames : String → Option (List String)
  | "math" => some ["sqrt", "ceil", "floor", "trunc", "gcd", "lcm", "isqrt", "log", "log10", "log2", "exp",
      "fabs", "factorial", "comb", "perm", "modf", "pow", "hypot", "sin", "cos", "tan", "atan", "atan2",
      "asin", "acos", "pi", "e", "inf", "nan", "tau", "isinf", "isnan", "isfinite", "degrees", "radians",
      "prod", "fsum", "copysign", "isclose", "dist"]
  | "sys" => some ["stdin", "stdout", "stderr", "setrecursionlimit", "getrecursionlimit", "exit", "maxsize"]
  | "collections" => some ["Counter", "defaultdict", "deque", "OrderedDict"]
  | "itertools" => some ["permutations", "combinations", "combinations_with_replacement", "product",
      "accumulate", "groupby", "chain", "count"]
  | "functools" => some ["reduce", "lru_cache", "cmp_to_key", "cache"]
  | "heapq" => some ["heappush", "heappop", "heapify", "heappushpop", "heapreplace", "nlargest", "nsmallest"]
  | "bisect" => some ["bisect", "bisect_left", "bisect_right", "insort", "insort_left", "insort_right"]
  | "copy" => some ["copy", "deepcopy"]
  | "string" => some ["ascii_lowercase", "ascii_uppercase", "ascii_letters", "digits", "punctuation",
      "whitespace", "hexdigits", "octdigits", "capwords"]
  | "operator" => some ["itemgetter", "add", "mul", "sub"]
  | "queue" => some ["PriorityQueue"]
  | "typing" => some ["List", "Dict", "Tuple", "Set", "Optional", "Any", "Union"]
  | "fileinput" => some []
  | "re" => some ["findall", "search", "match", "fullmatch", "compile", "sub"]
  | _ => none

/-- A module's attribute. -/
def moduleAttr (m a : String) : Option Val :=
  match moduleNames m with
  | none => none
  | some ns => if !ns.contains a then none else some <| match m, a with
    | "math", "pi" => .float (bOf 3.141592653589793)
    | "math", "e" => .float (bOf 2.718281828459045)
    | "math", "tau" => .float (bOf 6.283185307179586)
    | "math", "inf" => .float posInf
    | "math", "nan" => .float nanBits
    | "sys", "stdin" => .bfun "sys.stdin"
    | "sys", "stdout" => .bfun "sys.stdout"
    | "sys", "stderr" => .bfun "sys.stderr"
    | "sys", "maxsize" => .int 9223372036854775807
    | "string", "ascii_lowercase" => .str "abcdefghijklmnopqrstuvwxyz"
    | "string", "ascii_uppercase" => .str "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    | "string", "ascii_letters" => .str "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    | "string", "digits" => .str "0123456789"
    | "string", "hexdigits" => .str "0123456789abcdefABCDEF"
    | "string", "octdigits" => .str "01234567"
    | "string", "punctuation" => .str "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"
    | "string", "whitespace" => .str " \t\n\r\x0b\x0c"
    | "collections", x => .bfun x
    | "queue", x => .bfun x
    | m, x => .bfun (m ++ "." ++ x)

def isExcClass (s : St) (c : Val) : Bool := isSubclass s c (.bfun "BaseException")
def isClass (s : St) (c : Val) : Bool :=
  match c with
  | .bfun k => isTypeName k
  | .obj o => match s.get o with | .cls .. => true | _ => false
  | _ => false

/-- C3 linearization. -/
partial def c3 (seqs : List (List Val)) (acc : List Val) : Option (List Val) :=
  let seqs := seqs.filter (!·.isEmpty)
  if seqs.isEmpty then some acc.reverse else
  let heads := seqs.filterMap List.head?
  let good := heads.find? fun h => seqs.all fun sq => !(sq.drop 1).contains h
  match good with
  | none => none
  | some h => c3 (seqs.map fun sq => if sq.head? == some h then sq.drop 1 else sq) (h :: acc)

def readLine (s : St) : St × String :=
  let (l, r) := (s.inp.takeWhile (· != '\n'), s.inp.dropWhile (· != '\n'))
  match r with
  | '\n' :: r' => ({ s with inp := r' }, String.ofList (l ++ ['\n']))
  | _ => ({ s with inp := [] }, String.ofList l)

def numPair (a b : Val) : Option (Val × Val) := do
  let x ← asNum a
  let y ← asNum b
  some (x, y)

mutual

partial def strM (v : Val) : M String := do
  let s ← getS
  match strN s v with
  | some x => pure x
  | none => match v.base with
    | .obj o => match s.get o with
      | .inst c attrs => match clsLookup s c "__str__" with
        | some f => do
          let r ← callM f [v]
          match r with | .str x => pure x | _ => throwM tErr
        | none =>
          if isExcClass s c && (clsLookup s c "__repr__").isNone then
            match attrs.lookup "args" with
            | some (.tuple []) => pure ""
            | some (.tuple [a]) => strM a
            | some a => reprM a
            | none => pure ""
          else reprM v
      | _ => reprM v
    | .err _ [a] => strM a
    | _ => reprM v

partial def reprM (v : Val) : M String := do
  let s ← getS
  match reprN s v with
  | some x => pure x
  | none => match v.base with
    | .obj o => match s.get o with
      | .inst c attrs => match clsLookup s c "__repr__" with
        | some f => do
          let r ← callM f [v]
          match r with | .str x => pure x | _ => throwM tErr
        | none =>
          if isExcClass s c then do
            let args := match attrs.lookup "args" with | some (.tuple a) => a | _ => []
            let n := match s.get (match c with | .obj p => p | _ => 0) with | .cls n .. => n | _ => "?"
            let rs ← reprList args
            pure (n ++ "(" ++ ", ".intercalate rs ++ ")")
          else throwM (unsup "repr of an object (its address)")
      | .list xs => do let rs ← reprList xs.toList; pure ("[" ++ ", ".intercalate rs ++ "]")
      | .deque xs => do let rs ← reprList xs.toList; pure ("deque([" ++ ", ".intercalate rs ++ "])")
      | .set d _ => do let rs ← reprList d.keys; pure ("{" ++ ", ".intercalate rs ++ "}")
      | .dict d .plain => do
        let rs ← d.items.mapM fun (a, b) => do pure ((← reprM a) ++ ": " ++ (← reprM b))
        pure ("{" ++ ", ".intercalate rs ++ "}")
      | _ => throwM (unsup "repr")
    | .tuple [x] => do pure ("(" ++ (← reprM x) ++ ",)")
    | .tuple xs => do let rs ← reprList xs; pure ("(" ++ ", ".intercalate rs ++ ")")
    | .fn _ => throwM (unsup "repr of a function (its address)")
    | .gen _ => throwM (unsup "repr of a generator (its address)")
    | .meth .. => throwM (unsup "repr of a method")
    | _ => throwM (unsup "repr")

partial def reprList (xs : List Val) : M (List String) :=
  match xs with
  | [] => pure []
  | x :: r => do let a ← reprM x; let b ← reprList r; pure (a :: b)

partial def truthM (v : Val) : M Bool := do
  let s ← getS
  match v.base with
  | .none | .no => pure false
  | .bool b => pure b
  | .int n => pure (n != 0)
  | .float b => pure ((b &&& 0x7FFFFFFFFFFFFFFF) != 0)
  | .str x => pure (!x.isEmpty)
  | .tuple vs => pure (!vs.isEmpty)
  | .data "range" [.int a, .int b, .int c] => pure (rangeLen a b c > 0)
  | .data "dict_keys" [.obj o] | .data "dict_values" [.obj o] | .data "dict_items" [.obj o] =>
    match s.get o with | .dict d _ => pure (d.size > 0) | _ => pure true
  | .obj o => match s.get o with
    | .list vs | .deque vs => pure (vs.size > 0)
    | .dict d _ | .set d _ => pure (d.size > 0)
    | .inst c _ => match clsLookup s c "__bool__", clsLookup s c "__len__" with
      | some f, _ => do
        let r ← callM f [v]
        match r with | .bool b => pure b | _ => throwM tErr
      | none, some f => do
        let r ← callM f [v]
        match r with | .int n => pure (n != 0) | _ => throwM tErr
      | none, none => pure true
    | _ => pure true
  | _ => pure true

partial def lenM (v : Val) : M Int := do
  let s ← getS
  match v.base with
  | .str x => pure x.length
  | .tuple vs => pure vs.length
  | .data "range" [.int a, .int b, .int c] => pure (rangeLen a b c)
  | .data "dict_keys" [.obj o] | .data "dict_values" [.obj o] | .data "dict_items" [.obj o] =>
    match s.get o with | .dict d _ => pure d.size | _ => throwM tErr
  | .obj o => match s.get o with
    | .list vs | .deque vs => pure vs.size
    | .dict d _ | .set d _ => pure d.size
    | .inst c _ => match clsLookup s c "__len__" with
      | some f => do
        let r ← callM f [v]
        match r with | .int n => pure n | _ => throwM tErr
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

/-- `a == b` as a value (a user `__eq__` may give any). -/
partial def eqV (a b : Val) : M Val := do
  let s ← getS
  match eqN s a b with
  | some r => pure (.bool r)
  | none =>
    let try1 : Option Val := special s a "__eq__"
    match try1 with
    | some f => do
      let r ← callM f [a, b]
      if r == .bfun "NotImplemented" then
        match special s b "__eq__" with
        | some g => do
          let r2 ← callM g [b, a]
          if r2 == .bfun "NotImplemented" then pure (.bool (a.base == b.base)) else pure r2
        | none => pure (.bool (a.base == b.base))
      else pure r
    | none => match special s b "__eq__" with
      | some g => do
        let r2 ← callM g [b, a]
        if r2 == .bfun "NotImplemented" then pure (.bool (a.base == b.base)) else pure r2
      | none => pure (.bool (a.base == b.base))

partial def eqM (a b : Val) : M Bool := do
  let r ← eqV a b
  truthM r

/-- `a < b` (`op` one of Lt, Gt, LtE, GtE) with user methods and `cmp_to_key` keys. -/
partial def cmpV (op : String) (a b : Val) : M Val := do
  let s ← getS
  match a.base, b.base with
  | .data "cmpkey" [f, x], .data "cmpkey" [_, y] => do
    let r ← callV f [x, y] []
    match r.base with
    | .int n => pure (.bool (match op with | "Lt" => n < 0 | "Gt" => n > 0 | "LtE" => n ≤ 0 | _ => n ≥ 0))
    | _ => throwM tErr
  | _, _ =>
    let (m, rm) := match op with
      | "Lt" => ("__lt__", "__gt__") | "Gt" => ("__gt__", "__lt__")
      | "LtE" => ("__le__", "__ge__") | _ => ("__ge__", "__le__")
    match special s a m, special s b rm with
    | some f, _ => do
      let r ← callM f [a, b]
      if r == .bfun "NotImplemented" then
        match special s b rm with
        | some g => callM g [b, a]
        | none => throwM tErr
      else pure r
    | none, some g => callM g [b, a]
    | none, none =>
      match op with
      | "Lt" => (Val.bool ·) <$> liftE (ltN s a b)
      | "Gt" => (Val.bool ·) <$> liftE (ltN s b a)
      | "LtE" => (Val.bool ·) <$> liftE (leN s a b)
      | _ => (Val.bool ·) <$> liftE (leN s b a)

partial def ltM (a b : Val) : M Bool := do
  let s ← getS
  match ltN s a b with
  | .ok r => pure r
  | .error _ => do let r ← cmpV "Lt" a b; truthM r

partial def containsM (a b : Val) : M Bool := do
  let s ← getS
  match b.base with
  | .str y => match a.base with
    | .str x => pure (x.toList.isEmpty || (findSub y.toList x.toList).isSome)
    | _ => throwM tErr
  | .data "range" [.int lo, .int hi, .int st] => match a.base with
    | .int n => pure (if st > 0 then lo ≤ n && n < hi && (n - lo) % st == 0 else hi < n && n ≤ lo && (lo - n) % (-st) == 0)
    | _ => anyEq a ((nativeList s b).getD [])
  | .data "dict_keys" [d] => containsM a d
  | .obj o => match s.get o with
    | .dict d _ | .set d _ => do
      let k ← liftE (normKey s a)
      pure (d.find? k).isSome
    | .list vs | .deque vs => anyEq a vs.toList
    | .inst c _ => match clsLookup s c "__contains__" with
      | some f => do let r ← callM f [b, a]; truthM r
      | none => do let xs ← toListM b; anyEq a xs
    | .iter _ => do let xs ← toListM b; anyEq a xs
    | _ => throwM tErr
  | .tuple vs => anyEq a vs
  | .gen _ => do let xs ← toListM b; anyEq a xs
  | _ => match nativeList s b with
    | some xs => anyEq a xs
    | none => throwM tErr

partial def anyEq (a : Val) (xs : List Val) : M Bool := do
  let s ← getS
  match xs.mapM (fun x => eqN s a x) with
  | some bs => pure (bs.any id)
  | none => go xs
where
  go (xs : List Val) : M Bool := match xs with
    | [] => pure false
    | x :: r => do if (← eqM a x) then pure true else go r

partial def binopM (op : String) (a b : Val) : M Val := do
  let s ← getS
  match op with
  | "Eq" => eqV a b
  | "NotEq" => match eqN s a b with
    | some r => pure (.bool (!r))
    | none => match special s a "__ne__" with
      | some f => callM f [a, b]
      | none => do let r ← eqM a b; pure (.bool (!r))
  | "Lt" | "Gt" | "LtE" | "GtE" => cmpV op a b
  | "Is" => pure (.bool (a.base == b.base))
  | "IsNot" => pure (.bool (a.base != b.base))
  | "In" => (Val.bool ·) <$> containsM a b
  | "NotIn" => (fun r => Val.bool (!r)) <$> containsM a b
  | _ =>
    let inplace := op.endsWith "="
    let o := if inplace then (op.dropEnd 1).toString else op
    -- user special methods
    let dn : String := match o with
      | "Add" => "add" | "Sub" => "sub" | "Mult" => "mul" | "Div" => "truediv" | "FloorDiv" => "floordiv"
      | "Mod" => "mod" | "Pow" => "pow" | "LShift" => "lshift" | "RShift" => "rshift" | "BitAnd" => "and"
      | "BitOr" => "or" | "BitXor" => "xor" | "MatMult" => "matmul" | _ => "?"
    let userA := special s a ("__" ++ dn ++ "__")
    let userI := if inplace then special s a ("__i" ++ dn ++ "__") else none
    let userB := special s b ("__r" ++ dn ++ "__")
    match userI, userA, userB with
    | some f, _, _ => callM f [a, b]
    | none, some f, _ => do
      let r ← callM f [a, b]
      if r == .bfun "NotImplemented" then
        match userB with
        | some g => callM g [b, a]
        | none => throwM tErr
      else pure r
    | none, none, some g => callM g [b, a]
    | none, none, none => match numOp o a b with
      | some r => liftE r
      | none => arith inplace o a b

/-- Arithmetic on builtin non-number values. -/
partial def arith (inplace : Bool) (o : String) (a b : Val) : M Val := do
  let s ← getS
  /- `d |= x`, `d` a dict other than a Counter and `x` not a dict, is `d.update(x)` -/
  if inplace && o == "BitOr" then
    if let .obj oa := a.base then
      if let .dict _ k := s.get oa then
        let ofDict := match b.base with
          | .obj p => match s.get p with | .dict .. => true | _ => false
          | _ => false
        let counter := match k with | .counter => true | _ => false
        if !ofDict && !counter then
          let _ ← dictMethod oa "update" [b] []
          return a
  match o, a.base, b.base with
  | "Add", .str x, .str y => pure (.str (x ++ y))
  | "Mult", .str x, .int n | "Mult", .int n, .str x =>
    if n.toNat * x.utf8ByteSize > 50000000 then throwM (unsup "a repetition over 50 MB") else
    pure (.str (String.join (List.replicate n.toNat x)))
  | "Mult", .str x, .bool t | "Mult", .bool t, .str x => pure (.str (if t then x else ""))
  | "Mod", .str x, _ => (Val.str ·) <$> liftE (percentN s x b)
  | "Add", .tuple xs, .tuple ys => pure (.tuple (xs ++ ys))
  | "Mult", .tuple xs, .int n | "Mult", .int n, .tuple xs =>
    if n.toNat * xs.length > 10000000 then throwM (unsup "a repetition over 10^7 items") else
    pure (.tuple (List.flatten (List.replicate n.toNat xs)))
  | "Add", .obj o, _ => match s.get o with
    | .list xs =>
      if inplace then do
        let ys ← toListM b
        modM o (fun | .list zs => .list (zs ++ ys.toArray) | z => z)
        pure a
      else match b.base with
        | .obj p => match s.get p with
          | .list ys => allocM (.list (xs ++ ys))
          | _ => throwM tErr
        | _ => throwM tErr
    | .dict d .counter => match b.base with
      | .obj p => match s.get p with
        | .dict e .counter => do
          let m := e.items.foldl (fun (m : PDict) (k, v) =>
            match normKey s k with
            | .ok nk => match m.find? nk with
              | some (_, w) => match numOp "Add" w v with | some (.ok r) => m.insert nk k r | _ => m
              | none => m.insert nk k v
            | .error _ => m) d
          let m := (m.items.filter fun (_, v) => match numCmp v (.int 0) with | some .gt => true | _ => false)
          let m ← liftE (mkDict s m)
          allocM (.dict m .counter)
        | _ => throwM tErr
      | _ => throwM tErr
    | .deque xs =>
      if inplace then do
        let ys ← toListM b
        modM o (fun | .deque zs => .deque (zs ++ ys.toArray) | z => z)
        pure a
      else throwM tErr
    | _ => throwM tErr
  | "Mult", .obj o, .int n | "Mult", .int n, .obj o => match s.get o with
    | .list xs =>
      if n.toNat * xs.size > 10000000 then throwM (unsup "a repetition over 10^7 items") else
      let ys := List.flatten (List.replicate n.toNat xs.toList)
      if inplace && a.base == .obj o then do modM o (fun _ => .list ys.toArray); pure a
      else allocM (.list ys.toArray)
    | _ => throwM tErr
  | "Sub", .obj oa, .obj p | "BitOr", .obj oa, .obj p | "BitAnd", .obj oa, .obj p | "BitXor", .obj oa, .obj p =>
    match s.get oa, s.get p with
    | .set d fz, .set e _ => do
      let res : PDict := match o, inplace with
        | "Sub", false => setDiff s d e
        | "Sub", true => (e.keys.foldl (setErase s) d).compactSet
        | "BitAnd", _ => setInter s d e
        | "BitOr", false => setUnion d e
        | "BitOr", true => d.merge e
        | _, false => setSym s d e
        | _, true => setSymUpd s d e
      if inplace then do modM oa (fun _ => .set res fz); pure a
      else allocM (.set res fz)
    | .dict d k, .dict e _ =>
      if o == "BitOr" then do
        let m := e.items.foldl (fun m (kk, v) => match normKey s kk with | .ok nk => m.insert nk kk v | .error _ => m) d
        if inplace then do modM oa (fun _ => .dict m k); pure a else allocM (.dict m k)
      else if o == "Sub" then
        match k with
        | .counter => do
          let m := d.items.foldl (fun (m : PDict) (kk, v) => match normKey s kk with
            | .ok nk => match e.find? nk with
              | some (_, w) => match numOp "Sub" v w with | some (.ok r) => m.insert nk kk r | _ => m
              | none => m.insert nk kk v
            | .error _ => m) {}
          let m := (m.items.filter fun (_, v) => match numCmp v (.int 0) with | some .gt => true | _ => false)
          let m ← liftE (mkDict s m)
          allocM (.dict m .counter)
        | _ => throwM tErr
      else throwM tErr
    | _, _ => throwM tErr
  | _, _, _ => throwM tErr

partial def unopM (op : String) (a : Val) : M Val := do
  let s ← getS
  match op with
  | "Not" => do let t ← truthM a; pure (.bool (!t))
  | _ => match special s a (match op with | "USub" => "__neg__" | "UAdd" => "__pos__" | _ => "__invert__") with
    | some f => callM f [a]
    | none => match op, asNum a with
      | "USub", some (.int n) => pure (.int (-n))
      | "USub", some (.float b) => pure (.float (b ^^^ 0x8000000000000000))
      | "UAdd", some x => pure x
      | "Invert", some (.int n) => pure (.int (-n - 1))
      | _, _ => throwM tErr

partial def iterM (v : Val) : M Val := do
  let s ← getS
  match v.base with
  | .gen _ => pure v
  | .tuple vs => allocM (.iter (.seq vs))
  | .str x => allocM (.iter (.str x.toList))
  | .data "range" [.int a, .int b, .int c] => allocM (.iter (.rng a b c))
  | .data "dict_keys" [.obj o] | .data "dict_values" [.obj o] | .data "dict_items" [.obj o] =>
    match s.get o with
    | .dict d _ => allocM (.iter (.dict o 0 d.size (match v.base with
        | .data "dict_keys" _ => 0 | .data "dict_values" _ => 1 | _ => 2)))
    | _ => throwM tErr
  | .bfun "sys.stdin" => pure v
  | .obj o => match s.get o with
    | .list _ => allocM (.iter (.list o 0))
    | .dict d _ => allocM (.iter (.dict o 0 d.size 0))
    | .set d _ => allocM (.iter (.setv o d.keys d.size))
    | .deque vs => allocM (.iter (.seq vs.toList))
    | .iter _ => pure v
    | .inst c _ => match clsLookup s c "__iter__" with
      | some f => callM f [v]
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

partial def nextM (it : Val) : M (Option Val) := do
  let s ← getS
  match it.base with
  | .gen _ => do
    let r ← tryCallM .next [it]
    match r with
    | .ok v => pure (some v)
    | .error e => if isStop e then pure none else reraiseM e
  | .bfun "sys.stdin" => do
    let (s', l) := readLine s
    setS s'
    pure (if l.isEmpty then none else some (.str l))
  | .obj o => match s.get o with
    | .iter t => match t with
      | .list l i => match s.get l with
        | .list vs =>
          if h : i < vs.size then do putM o (.iter (.list l (i + 1))); pure (some vs[i])
          else do putM o (.iter .done); pure none
        | _ => pure none
      | .seq [] | .str [] | .done => do putM o (.iter .done); pure none
      | .seq (v :: vs) => do putM o (.iter (.seq vs)); pure (some v)
      | .str (c :: cs) => do putM o (.iter (.str cs)); pure (some (.str c.toString))
      | .rng cur stop step =>
        if (step > 0 && cur < stop) || (step < 0 && cur > stop) then do
          putM o (.iter (.rng (cur + step) stop step)); pure (some (.int cur))
        else do putM o (.iter .done); pure none
      | .count cur step => do putM o (.iter (.count (cur + step) step)); pure (some (.int cur))
      | .setv p ks n => match s.get p with
        | .set d _ =>
          if d.size != n then throwM (.err "RuntimeError" []) else
          match ks with
          | k :: r => do putM o (.iter (.setv p r n)); pure (some k)
          | [] => do putM o (.iter .done); pure none
        | _ => pure none
      | .dict d i n w => match s.get d with
        | .dict pd _ | .set pd _ =>
          if pd.size != n then throwM (.err "RuntimeError" []) else
          match dictFind pd.ents i with
          | some (j, k, v) => do
            putM o (.iter (.dict d (j + 1) n w))
            pure (some (match w with | 0 => k | 1 => v | _ => .tuple [k, v]))
          | none => do putM o (.iter .done); pure none
        | _ => pure none
      | .enum inner n => do
        let r ← nextM inner
        match r with
        | some x => do modM o (fun _ => .iter (.enum inner (n + 1))); pure (some (.tuple [.int n, x]))
        | none => pure none
      | .zip its => do
        let r ← nextAll its []
        pure (r.map .tuple)
      | .map f its => do
        let r ← nextAll its []
        match r with
        | some xs => do let y ← callV f xs []; pure (some y)
        | none => pure none
      | .filter f inner neg => filterNext f inner neg
      | .chain [] => pure none
      | .chain (i :: is) => do
        let r ← nextM i
        match r with
        | some x => pure (some x)
        | none => do putM o (.iter (.chain is)); nextM it
    | .inst c _ => match clsLookup s c "__next__" with
      | some f => do
        let r ← tryCallM f [it]
        match r with
        | .ok v => pure (some v)
        | .error e => if isStop e then pure none else reraiseM e
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

partial def nextAll (its acc : List Val) : M (Option (List Val)) :=
  match its with
  | [] => pure (some acc.reverse)
  | i :: is => do
    let r ← nextM i
    match r with
    | some x => nextAll is (x :: acc)
    | none => pure none

partial def filterNext (f inner : Val) (neg : Bool) : M (Option Val) := do
  let r ← nextM inner
  match r with
  | none => pure none
  | some x => do
    let keep ← if f == .none then truthM x else do let y ← callV f [x] []; truthM y
    if keep != neg then pure (some x) else do bounce; filterNext f inner neg

/-- The items of an iterable. -/
partial def toListM (v : Val) : M (List Val) := do
  let s ← getS
  match nativeList s v with
  | some xs => pure xs
  | none => do
    let it ← iterM v
    drain it []

partial def drain (it : Val) (acc : List Val) : M (List Val) := do
  let r ← nextM it
  match r with
  | some x => do bounce; drain it (x :: acc)
  | none => pure acc.reverse

/-- At most `n` items. -/
partial def takeM (it : Val) (n : Nat) (acc : List Val) : M (List Val) :=
  match n with
  | 0 => pure acc.reverse
  | n + 1 => do
    let r ← nextM it
    match r with
    | some x => takeM it n (x :: acc)
    | none => pure acc.reverse

partial def callV (f : Val) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  match f with
  | .fn _ | .gen _ | .next => callM f args kws
  | .meth g self => callV g (self :: args) kws
  | .bfun k => builtinM k args kws
  | .data "cmp_to_key" [g] => match args with
    | [x] => pure (.data "cmpkey" [g, x])
    | _ => throwM tErr
  | .data "itemgetter" is => match args with
    | [x] => match is with
      | [i] => getitemM x i
      | _ => do let r ← is.mapM (getitemM x); pure (.tuple r)
    | _ => throwM tErr
  | .data "lru_cache" _ => match args with
    | [g] => allocM (.cache g {})
    | _ => throwM tErr
  | .obj o => match s.get o with
    | .cls .. => instantiate f args kws
    | .cache g memo => do
      if !kws.isEmpty then throwM (unsup "lru_cache with keywords") else
      let k ← liftE (normKey s (.tuple args))
      match memo.find? k with
      | some (_, r) => pure r
      | none => do
        let r ← callV g args []
        modM o (fun | .cache g' m => .cache g' (m.insert k (.tuple args) r) | z => z)
        pure r
    | .inst c _ => match clsLookup s c "__call__" with
      | some g => callM g (f :: args) kws
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

partial def instantiate (c : Val) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  if (clsLookup s c "__new__").isSome then throwM (unsup "__new__") else
  let exc := isExcClass s c
  let inst ← allocM (.inst c (if exc then [("args", .tuple args)] else []))
  match clsLookup s c "__init__" with
  | some f => do
    let r ← callM f (inst :: args) kws
    if r != .none then throwM tErr else pure inst
  | none => if !exc && (!args.isEmpty || !kws.isEmpty) then throwM tErr else pure inst

partial def getattrM (v : Val) (a : Name) : M Val := do
  let s ← getS
  let meth (ty : String) (ms : List String) : M Val :=
    if ms.contains a then pure (.meth (.bfun (ty ++ "." ++ a)) v) else throwM attrErr
  match v with
  | .exn b ctx cause => match a with
    | "__context__" => pure ctx
    | "__cause__" => pure cause
    | _ => getattrM b a
  | _ =>
  let userObj := match v with
    | .obj o => match s.get o with | .inst .. | .cls .. => true | _ => false
    | _ => false
  -- a special method of a builtin value, bound (`(5).__ne__`, `s.__len__`)
  if dunderNames.contains a && !userObj then pure (.meth (.bfun ("$dunder." ++ a)) v) else
  match v with
  | .obj o => match s.get o with
    | .inst c attrs => match clsLookup s c a with
      | some (.data "property" (g :: _)) => callV g [v] []
      | cv => match attrs.lookup a with
        | some x => pure x
        | none => match cv with
          | some (.fn g) => pure (.meth (.fn g) v)
          | some (.data "staticmethod" [g]) => pure g
          | some (.data "classmethod" [g]) => pure (.meth g c)
          | some x => pure x
          | none => if a == "__class__" then pure c else throwM attrErr
    | .cls name qual m bases _ _ => match a with
      | "__name__" => pure (.str name)
      | "__qualname__" => pure (.str qual)
      | "__module__" => pure m
      | "__bases__" => pure (.tuple bases)
      | _ => match clsLookup s v a with
        | some (.data "classmethod" [g]) => pure (.meth g v)
        | some (.data "staticmethod" [g]) => pure g
        | some x => pure x
        | none => throwM attrErr
    | .list _ => meth "list" listMethods
    -- `fromkeys` is a class method: bound to the instance's class, not to the instance
    | .dict _ k =>
      if a == "fromkeys" then
        pure (.bfun ((match k with | .ordered => "OrderedDict" | .counter => "Counter" | _ => "dict") ++ ".fromkeys"))
      else match k with
        | .dflt fac => if a == "default_factory" then pure fac else meth "dict" dictMethods
        | _ => meth "dict" dictMethods
    | .set _ _ => meth "set" setMethods
    | .deque _ => meth "deque" dequeMethods
    | .pq q => if a == "queue" then pure (.obj q) else meth "pq" ["put", "get", "empty", "qsize", "put_nowait", "get_nowait"]
    | .iter _ => if a == "__next__" then pure (.meth .next v) else throwM attrErr
    | .cache .. => if a == "cache_clear" then pure (.meth (.bfun "cache.cache_clear") v) else throwM attrErr
  | .str _ => meth "str" strMethods
  | .int _ | .bool _ => match a with
    | "real" | "numerator" => pure v
    | "imag" => pure (.int 0)
    | "denominator" => pure (.int 1)
    | _ => meth "int" ["bit_length", "conjugate", "bit_count"]
  | .float _ => match a with
    | "real" => pure v
    | "imag" => pure (.float 0)
    | _ => meth "float" ["is_integer", "conjugate"]
  | .tuple _ => meth "tuple" ["count", "index"]
  | .data "re.Match" _ => meth "re.Match" ["group", "start", "end", "span"]
  | .data "re.Pattern" _ => meth "re.Pattern" ["findall", "search", "match", "fullmatch", "sub"]
  | .data "range" [x, y, z] => match a with
    | "start" => pure x | "stop" => pure y | "step" => pure z
    | _ => meth "range" ["count", "index"]
  | .err k args => match a with
    | "args" => pure (.tuple args)
    | "value" => if k == "StopIteration" then pure (args.headD .none) else throwM attrErr
    | "__class__" => pure (.bfun k)
    | "__context__" | "__cause__" => pure .none
    | _ => throwM attrErr
  | .bfun k =>
    if k.startsWith "module:" then
      let m := (k.drop 7).toString
      match moduleAttr m a with
      | some x => pure x
      | none => throwM (unsup (m ++ "." ++ a))
    else match k, a with
    | "sys.stdin", "readline" | "sys.stdin", "read" | "sys.stdin", "readlines" =>
      pure (.bfun (k ++ "." ++ a))
    | "sys.stdout", "write" | "sys.stdout", "flush" => pure (.bfun (k ++ "." ++ a))
    | "sys.stdin", _ | "sys.stdout", _ => throwM (unsup (k ++ "." ++ a))
    | _, "__name__" => if isTypeName k then pure (.str k) else throwM (unsup "function __name__")
    | "str", _ => if strMethods.contains a then pure (.bfun ("str." ++ a)) else throwM attrErr
    | "list", _ => if listMethods.contains a then pure (.bfun ("list." ++ a)) else throwM attrErr
    | "dict", _ | "OrderedDict", _ | "Counter", _ | "defaultdict", _ =>
      if dictMethods.contains a then pure (.bfun (k ++ "." ++ a)) else throwM attrErr
    | "set", _ => if setMethods.contains a then pure (.bfun ("set." ++ a)) else throwM attrErr
    | "int", _ => if a == "bit_length" then pure (.bfun "int.bit_length") else throwM attrErr
    | "tuple", _ => if ["count", "index"].contains a then pure (.bfun ("tuple." ++ a)) else throwM attrErr
    | _, _ => throwM (unsup ("attribute " ++ a ++ " of " ++ k))
  | .gen _ => if a == "__next__" then pure (.meth .next v) else throwM (unsup ("generator ." ++ a))
  | .fn _ => throwM (unsup ("function attribute " ++ a))
  | _ => throwM attrErr

partial def setattrM (o : Val) (a : Name) (v : Val) : M Unit := do
  let s ← getS
  match o.base with
  | .obj p => match s.get p with
    | .pq _ => match a, v with
      | "queue", .obj q => match s.get q with
        | .list _ => putM p (.pq q)
        | _ => throwM tErr
      | _, _ => throwM attrErr
    | .inst c _ => match clsLookup s c a with
      | some (.data "property" _) => throwM (unsup "property setter")
      | _ => modM p fun
        | .inst c' attrs => .inst c' (if attrs.any (·.1 == a) then attrs.map (fun q => if q.1 == a then (a, v) else q) else attrs ++ [(a, v)])
        | z => z
    | .cls .. => modM p fun
      | .cls n q m b mro d => .cls n q m b mro (if d.any (·.1 == a) then d.map (fun q => if q.1 == a then (a, v) else q) else d ++ [(a, v)])
      | z => z
    | _ => throwM attrErr
  | _ => throwM attrErr

partial def delattrM (o : Val) (a : Name) : M Unit := do
  let s ← getS
  match o.base with
  | .obj p => match s.get p with
    | .inst _ attrs =>
      if attrs.any (·.1 == a) then
        modM p fun
          | .inst c' attrs => .inst c' (attrs.filter (·.1 != a))
          | z => z
      else throwM attrErr
    | _ => throwM attrErr
  | _ => throwM attrErr

partial def getitemM (o i : Val) : M Val := do
  let s ← getS
  let seqGet (xs : Array Val) (mk : List Val → M Val) : M Val :=
    match i.base with
    | .data "slice" [lo, hi, st] => do
      let ix ← liftE (sliceIdx xs.size lo hi st)
      mk (ix.map fun j => xs[j]!)
    | _ => do
      let n ← liftE (asIndex i)
      match idxNorm xs.size n with
      | some j => pure xs[j]!
      | none => throwM (.err "IndexError" [])
  match o.base with
  | .str x => match i.base with
    | .data "slice" [lo, hi, st] => do
      let cs := x.toList.toArray
      let ix ← liftE (sliceIdx cs.size lo hi st)
      pure (.str (String.ofList (ix.map fun j => cs[j]!)))
    | _ => do
      let n ← liftE (asIndex i)
      let len := x.length
      match idxNorm len n with
      | some j => pure (.str (x.toList[j]!).toString)
      | none => throwM (.err "IndexError" [])
  | .tuple vs => seqGet vs.toArray (fun ys => pure (.tuple ys))
  | .data "range" [.int a, .int b, .int c] => match i.base with
    | .data "slice" [lo, hi, st] => do
      let (i, j, k, _) ← liftE (sliceAdj (rangeLen a b c) lo hi st)
      pure (.data "range" [.int (a + i * c), .int (a + j * c), .int (c * k)])
    | _ => do
      let n ← liftE (asIndex i)
      match idxNorm (rangeLen a b c) n with
      | some j => pure (.int (a + j * c))
      | none => throwM (.err "IndexError" [])
  | .obj p => match s.get p with
    | .list xs => seqGet xs (fun ys => allocM (.list ys.toArray))
    | .deque xs => match i.base with
      | .data "slice" .. => throwM tErr
      | _ => seqGet xs (fun _ => throwM tErr)
    | .dict d k => do
      let nk ← liftE (normKey s i)
      match d.find? nk with
      | some (_, v) => pure v
      | none => match k with
        | .counter => pure (.int 0)
        | .dflt fac => if fac == .none then throwM (keyErr i) else do
          let v ← callV fac [] []
          modM p fun | .dict d' k' => .dict (d'.insert nk i v) k' | z => z
          pure v
        | _ => match special s o "__missing__" with
          | some f => callM f [o, i]
          | none => throwM (keyErr i)
    | .inst c _ => match clsLookup s c "__getitem__" with
      | some f => callM f [o, i]
      | none => throwM tErr
    | .cls .. => pure o
    | _ => throwM tErr
  | .bfun k =>
    if isTypeName k then pure (.data "alias" [o, i])
    else if k.startsWith "typing." then pure o else throwM tErr
  | _ => throwM tErr

partial def setitemM (o i v : Val) : M Unit := do
  let s ← getS
  match o.base with
  | .obj p => match s.get p with
    | .list xs => match i.base with
      | .data "slice" [lo, hi, st] => do
        let ys ← toListM v
        let s ← getS
        match st with
        | .none | .int 1 =>
          let ix ← liftE (sliceIdx xs.size lo hi .none)
          let start : Nat := match ix.head? with
            | some j => j
            | none => match lo with
              | .none => 0
              | l => match asIndex l with
                | .ok n => let n := if n < 0 then n + xs.size else n; (max 0 (min n xs.size)).toNat
                | .error _ => 0
          let stop := start + ix.length
          let _ := s
          putM p (.list (xs.extract 0 start ++ ys.toArray ++ xs.extract stop xs.size))
        | _ => do
          let ix ← liftE (sliceIdx xs.size lo hi st)
          if ix.length != ys.length then throwM vErr else
          putM p (.list ((ix.zip ys).foldl (fun a (j, y) => a.set! j y) xs))
      | _ => do
        let n ← liftE (asIndex i)
        match idxNorm xs.size n with
        | some j => modM p fun | .list zs => .list (zs.set! j v) | z => z
        | none => throwM (.err "IndexError" [])
    | .deque xs => do
      let n ← liftE (asIndex i)
      match idxNorm xs.size n with
      | some j => modM p fun | .deque zs => .deque (zs.set! j v) | z => z
      | none => throwM (.err "IndexError" [])
    | .dict _ _ => do
      let nk ← liftE (normKey s i)
      modM p fun | .dict d k => .dict (d.insert nk i v) k | z => z
    | .inst c _ => match clsLookup s c "__setitem__" with
      | some f => do let _ ← callM f [o, i, v]; pure ()
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

partial def delitemM (o i : Val) : M Unit := do
  let s ← getS
  match o.base with
  | .obj p => match s.get p with
    | .list xs => match i.base with
      | .data "slice" [lo, hi, st] => do
        let ix ← liftE (sliceIdx xs.size lo hi st)
        let keep := (List.range xs.size).filter (!ix.contains ·)
        putM p (.list (keep.map fun j => xs[j]!).toArray)
      | _ => do
        let n ← liftE (asIndex i)
        match idxNorm xs.size n with
        | some j => putM p (.list (xs.extract 0 j ++ xs.extract (j + 1) xs.size))
        | none => throwM (.err "IndexError" [])
    | .dict d _ => do
      let nk ← liftE (normKey s i)
      match d.find? nk with
      | some _ => modM p fun | .dict d' k => .dict (d'.erase nk) k | z => z
      | none => throwM (keyErr i)
    | .inst c _ => match clsLookup s c "__delitem__" with
      | some f => do let _ ← callM f [o, i]; pure ()
      | none => throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

/-- The keys of `xs` under `key` (`none`: the items). -/
partial def keysM (key : Val) (xs : List Val) (acc : List Val) : M (List Val) :=
  match xs with
  | [] => pure acc.reverse
  | x :: r => do
    let k ← callV key [x] []
    bounce
    keysM key r (k :: acc)

/-- Sort `xs` by `ks` (stable; `rev` as CPython: reverse, sort, reverse). -/
partial def sortByM (xs ks : List Val) (rev : Bool) : M (List Val) := do
  let s ← getS
  let ps := xs.zip ks
  let ps := if rev then ps.reverse else ps
  let needCb := ks.any fun k => match k.base with
    | .data "cmpkey" _ => true
    | .obj o => match s.get o with | .inst .. => true | _ => false
    | _ => false
  let sorted ← if needCb then msortM ps else liftE (msort (fun a b => ltN s a.2 b.2) ps)
  let sorted := if rev then sorted.reverse else sorted
  pure (sorted.map (·.1))

partial def msortM (xs : List (Val × Val)) : M (List (Val × Val)) :=
  match xs with
  | [] | [_] => pure xs
  | _ => do
    let n := xs.length / 2
    let a ← msortM (xs.take n)
    let b ← msortM (xs.drop n)
    mergeM a b []

partial def mergeM (a b acc : List (Val × Val)) : M (List (Val × Val)) :=
  match a, b with
  | [], b => pure (acc.reverse ++ b)
  | a, [] => pure (acc.reverse ++ a)
  | x :: a', y :: b' => do
    let lt ← ltM y.2 x.2
    bounce
    if lt then mergeM a b' (y :: acc) else mergeM a' b (x :: acc)

/-- `max`/`min` over items with keys. -/
partial def extremeM (isMax : Bool) (xs ks : List Val) (best : Option (Val × Val)) : M (Option Val) :=
  match xs, ks with
  | x :: xr, k :: kr => match best with
    | none => extremeM isMax xr kr (some (x, k))
    | some (bx, bk) => do
      let better ← if isMax then ltM bk k else ltM k bk
      extremeM isMax xr kr (if better then some (x, k) else some (bx, bk))
  | _, _ => pure (best.map (·.1))

partial def formatM (v : Val) (spec : String) : M String := do
  let s ← getS
  match formatN s v spec with
  | some x => pure x
  | none => match special s v "__format__" with
    | some f => do let r ← callM f [v, .str spec]; match r with | .str x => pure x | _ => throwM tErr
    | none =>
      if spec.isEmpty then strM v
      else match parseSpec spec with
        | none => throwM vErr
        | some sp => match v.base with
          | .str _ | .int _ | .float _ | .bool _ => throwM vErr
          | _ =>
            if sp.ty.isNone && sp.prec.isNone then do let x ← strM v; pure (pad sp x "" false)
            else throwM tErr

/-- `str.format`. -/
partial def strFormatM (tmpl : List Char) (args : List Val) (kws : List (Name × Val)) (auto : Nat) (acc : String) :
    M String :=
  match tmpl with
  | [] => pure acc
  | '{' :: '{' :: r => strFormatM r args kws auto (acc ++ "{")
  | '}' :: '}' :: r => strFormatM r args kws auto (acc ++ "}")
  | '{' :: r => do
    let field := r.takeWhile (· != '}')
    let rest := r.drop (field.length + 1)
    if field.contains '{' then throwM (unsup "nested format field") else
    let (nameSpec, spec) := match field.findIdx? (· == ':') with
      | some k => (field.take k, String.ofList (field.drop (k + 1)))
      | none => (field, "")
    let (name, conv) := match nameSpec.findIdx? (· == '!') with
      | some k => (nameSpec.take k, (nameSpec.drop (k + 1)).head?)
      | none => (nameSpec, none)
    let base := name.takeWhile (fun c => c != '.' && c != '[')
    let path := name.drop base.length
    let (v, auto') ← if base.isEmpty then
        (match args[auto]? with | some v => pure (v, auto + 1) | none => throwM (.err "IndexError" []))
      else if base.all Char.isDigit then
        (match args[(String.ofList base).toNat!]? with | some v => pure (v, auto) | none => throwM (.err "IndexError" []))
      else match kws.lookup (String.ofList base) with
        | some v => pure (v, auto)
        | none => throwM (keyErr (.str (String.ofList base)))
    let v ← fieldPath v path
    let v ← match conv with
      | some 'r' => (Val.str ·) <$> reprM v
      | some 's' => (Val.str ·) <$> strM v
      | some 'a' => (Val.str ·) <$> reprM v
      | _ => pure v
    let x ← formatM v spec
    strFormatM rest args kws auto' (acc ++ x)
  | '}' :: _ => throwM vErr
  | c :: r => strFormatM r args kws auto (acc.push c)

partial def fieldPath (v : Val) (path : List Char) : M Val :=
  match path with
  | [] => pure v
  | '.' :: r => do
    let a := r.takeWhile (fun c => c != '.' && c != '[')
    let x ← getattrM v (String.ofList a)
    fieldPath x (r.drop a.length)
  | '[' :: r => do
    let k := r.takeWhile (· != ']')
    let key : Val := if k.all Char.isDigit && !k.isEmpty then .int (String.ofList k).toNat! else .str (String.ofList k)
    let x ← getitemM v key
    fieldPath x (r.drop (k.length + 1))
  | _ => throwM vErr

/-- `int(x)`, `int(x, base)`. -/
partial def toIntM (v : Val) (base : Option Int) : M Val := do
  let s ← getS
  match v.base, base with
  | .int n, none => pure (.int n)
  | .bool b, none => pure (.int (if b then 1 else 0))
  | .float b, none =>
    if isNaN b then throwM vErr else if !isFinite b then throwM (.err "OverflowError" []) else pure (.int (floatToInt b))
  | .str x, _ =>
    let bs := base.getD 10
    let cs := (x.toList.dropWhile isWs).reverse.dropWhile isWs |>.reverse
    let (neg, cs) := match cs with | '-' :: r => (true, r) | '+' :: r => (false, r) | _ => (false, cs)
    let cs := if bs == 16 && (isPrefixL ['0', 'x'] cs || isPrefixL ['0', 'X'] cs) then cs.drop 2
      else if bs == 2 && (isPrefixL ['0', 'b'] cs || isPrefixL ['0', 'B'] cs) then cs.drop 2
      else if bs == 8 && (isPrefixL ['0', 'o'] cs || isPrefixL ['0', 'O'] cs) then cs.drop 2 else cs
    if cs.isEmpty || cs.head? == some '_' || cs.getLast? == some '_' then throwM vErr else
    let digit (c : Char) : Option Nat :=
      if c.isDigit then some (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 55) else none
    let r := cs.foldl (fun (acc : Option Nat) c => match acc with
      | none => none
      | some a => if c == '_' then some a else match digit c with
        | some d => if (d : Int) < bs then some (a * bs.toNat + d) else none
        | none => none) (some 0)
    if (cs.zip cs.tail).any (fun p => p.1 == '_' && p.2 == '_') then throwM vErr else
    match r with
    | some n => pure (.int (if neg then -(n : Int) else n))
    | none => throwM vErr
  | _, none => match special s v "__int__" with
    | some f => callM f [v]
    | none => throwM tErr
  | _, _ => throwM tErr

partial def builtinM (k : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  let kw (n : String) : Option Val := kws.lookup n
  let noKw : M Unit := if kws.isEmpty then pure () else throwM tErr
  if isExcName k && k != "$Unsupported" then do noKw; pure (.err k args) else
  match k, args with
  | "$id", _ => pure .none
  | "print", _ => do
    let sep ← match kw "sep" with | some .none | none => pure " " | some (.str x) => pure x | _ => throwM tErr
    let en ← match kw "end" with | some .none | none => pure "\n" | some (.str x) => pure x | _ => throwM tErr
    match kw "file" with
    | none | some .none | some (.bfun "sys.stdout") => pure ()
    | _ => throwM (unsup "print to a file")
    let ss ← args.mapM strM
    modS (·.emit (sep.intercalate ss ++ en))
    pure .none
  | "input", _ => do
    match args with
    | [p] => do let x ← strM p; modS (·.emit x)
    | _ => pure ()
    let s ← getS
    if s.inp.isEmpty then throwM (.err "EOFError" []) else
    let (s', l) := readLine s
    setS s'
    pure (.str (if l.endsWith "\n" then (l.dropEnd 1).toString else l))
  | "len", [x] => do let n ← lenM x; pure (.int n)
  | "range", _ => do
    let is ← liftE (args.mapM asIndex)
    match is with
    | [b] => pure (.data "range" [.int 0, .int b, .int 1])
    | [a, b] => pure (.data "range" [.int a, .int b, .int 1])
    | [a, b, c] => if c == 0 then throwM vErr else pure (.data "range" [.int a, .int b, .int c])
    | _ => throwM tErr
  | "int", [] => pure (.int 0)
  | "int", [x] => match kw "base" with
    | some b => do let bb ← liftE (asIndex b); toIntM x (some bb)
    | none => toIntM x none
  | "int", [x, b] => do let bb ← liftE (asIndex b); toIntM x (some bb)
  | "float", [] => pure (.float 0)
  | "float", [x] => match x.base with
    | .float b => pure (.float b)
    | .int n => let b := intToBits n; if isFinite b then pure (.float b) else throwM (.err "OverflowError" [])
    | .bool t => pure (.float (if t then bOf 1.0 else 0))
    | .str y => match parseFloat y with
      | some b => pure (.float b)
      | none => throwM vErr
    | _ => throwM tErr
  | "str", [] => pure (.str "")
  | "str", [x] => (Val.str ·) <$> strM x
  | "repr", [x] => (Val.str ·) <$> reprM x
  | "ascii", [x] => (Val.str ·) <$> reprM x
  | "bool", [] => pure (.bool false)
  | "bool", [x] => (Val.bool ·) <$> truthM x
  | "list", [] => allocM (.list #[])
  | "list", [x] => do let xs ← toListM x; allocM (.list xs.toArray)
  | "tuple", [] => pure (.tuple [])
  | "tuple", [x] => do let xs ← toListM x; pure (.tuple xs)
  | "set", [] => allocM (.set PDict.newSet false)
  | "frozenset", [] => allocM (.set PDict.newSet true)
  | "set", [x] | "frozenset", [x] => do
    let s ← getS
    let fz := k == "frozenset"
    match x.base with
    | .obj p => match s.get p with
      | .set e _ => allocM (.set e.copySet fz)
      | _ => do let xs ← toListM x; let s ← getS; let d ← liftE (mkSet s xs); allocM (.set d fz)
    | _ => do let xs ← toListM x; let s ← getS; let d ← liftE (mkSet s xs); allocM (.set d fz)
  | "dict", _ => do
    let d ← dictFrom args
    let s ← getS
    let d ← liftE (kws.foldlM (fun (d : PDict) (n, v) => do let nk ← normKey s (.str n); pure (d.insert nk (.str n) v)) d)
    allocM (.dict d .plain)
  | "OrderedDict", _ => do let d ← dictFrom args; allocM (.dict d .ordered)
  | "Counter", _ => do
    let d ← match args with
      | [] => pure {}
      | [x] => do
        let s ← getS
        match x.base with
        | .obj o => match s.get o with
          | .dict d _ => pure d
          | _ => do let xs ← toListM x; countInto {} xs
        | _ => do let xs ← toListM x; countInto {} xs
      | _ => throwM tErr
    let s ← getS
    let d ← liftE (kws.foldlM (fun (d : PDict) (n, v) => do let nk ← normKey s (.str n); pure (d.insert nk (.str n) v)) d)
    allocM (.dict d .counter)
  | "defaultdict", _ => match args with
    | [] => allocM (.dict {} (.dflt .none))
    | f :: rest => do let d ← dictFrom rest; allocM (.dict d (.dflt f))
  | "deque", _ => match args with
    | [] => allocM (.deque #[])
    | [x] => do let xs ← toListM x; allocM (.deque xs.toArray)
    | _ => throwM (unsup "deque maxlen")
  | "PriorityQueue", _ => do let l ← allocM (.list #[]); match l with
    | .obj q => allocM (.pq q)
    | _ => throwM tErr
  | "enumerate", x :: rest => do
    let n ← match rest, kw "start" with
      | [st], _ | [], some st => liftE (asIndex st)
      | _, _ => pure 0
    let it ← iterM x
    allocM (.iter (.enum it n))
  | "zip", _ => do
    if (kw "strict").isSome then throwM (unsup "zip strict") else
    let its ← args.mapM iterM
    allocM (.iter (.zip its))
  | "map", f :: xs => do
    if xs.isEmpty then throwM tErr else
    let its ← xs.mapM iterM
    allocM (.iter (.map f its))
  | "filter", [f, x] => do let it ← iterM x; allocM (.iter (.filter f it false))
  | "iter", [x] => iterM x
  | "next", [it] => do
    let r ← nextM it
    match r with
    | some v => pure v
    | none => throwM (.err "StopIteration" [])
  | "next", [it, d] => do
    let r ← nextM it
    pure (r.getD d)
  | "reversed", [x] => do
    let s ← getS
    match x.base with
    | .data "range" [.int a, .int b, .int c] =>
      let n := rangeLen a b c
      if n == 0 then allocM (.iter .done) else
      let last := a + ((n - 1 : Nat) : Int) * c
      allocM (.iter (.rng last (a - c) (-c)))
    | .obj _ | .tuple _ | .str _ => match special s x "__reversed__" with
      | some f => callM f [x]
      | none => match nativeList s x with
        | some xs => allocM (.iter (.seq xs.reverse))
        | none => throwM tErr
    | _ => throwM tErr
  | "sorted", [x] => do
    let xs ← toListM x
    let ks ← match kw "key" with | none | some .none => pure xs | some f => keysM f xs []
    let rev ← match kw "reverse" with | none => pure false | some r => truthM r
    let ys ← sortByM xs ks rev
    allocM (.list ys.toArray)
  | "sum", x :: rest => do
    let xs ← toListM x
    let st := match rest, kw "start" with | [st], _ => st | [], some st => st | _, _ => .int 0
    sumM xs st
  | "max", _ | "min", _ => do
    let isMax := k == "max"
    let xs ← match args with
      | [x] => toListM x
      | [] => throwM tErr
      | _ => pure args
    let ks ← match kw "key" with | none | some .none => pure xs | some f => keysM f xs []
    let r ← extremeM isMax xs ks none
    match r, kw "default" with
    | some v, _ => pure v
    | none, some d => pure d
    | none, none => throwM vErr
  | "abs", [x] => match special s x "__abs__" with
    | some f => callM f [x]
    | none => match asNum x with
      | some (.int n) => pure (.int n.natAbs)
      | some (.float b) => pure (.float (b &&& 0x7FFFFFFFFFFFFFFF))
      | _ => throwM tErr
  | "round", [x] => match asNum x with
    | some (.int n) => pure (.int n)
    | some (.float b) =>
      if isNaN b then throwM vErr else if !isFinite b then throwM (.err "OverflowError" []) else
      let (neg, num, den) := toRat b
      let r := roundHalfEven num den
      pure (.int (if neg then -(r : Int) else r))
    | _ => throwM tErr
  | "round", [x, nd] => match asNum x, nd with
    | some (.int n), .none => pure (.int n)
    | some (.float b), .none => builtinM "round" [x] []
    | some (.int n), d => do
      let d ← liftE (asIndex d)
      if d ≥ 0 then pure (.int n) else
      let p : Int := 10 ^ (-d).toNat
      let q := n.fdiv p
      let r := n - q * p
      let q := if 2 * r > p || (2 * r == p && q % 2 == 1) then q + 1 else q
      pure (.int (q * p))
    | some (.float b), d => do let d ← liftE (asIndex d); pure (.float (roundTo b d))
    | _, _ => throwM tErr
  | "divmod", [a, b] => match numOp "FloorDiv" a b, numOp "Mod" a b with
    | some q, some r => do let q ← liftE q; let r ← liftE r; pure (.tuple [q, r])
    | _, _ => throwM tErr
  | "pow", [a, b] => binopM "Pow" a b
  | "pow", [a, b, m] => match asNum a, asNum b, asNum m with
    | some (.int x), some (.int y), some (.int z) =>
      if z == 0 then throwM vErr else if y < 0 then throwM (unsup "modular inverse") else
      let rec pw (b e acc : Int) (fuel : Nat) : Int := match fuel with
        | 0 => acc
        | fuel + 1 => if e == 0 then acc else pw ((b * b).fmod z) (e / 2) (if e % 2 == 1 then (acc * b).fmod z else acc) fuel
      pure (.int (pw (x.fmod z) y (1 % z) 4096))
    | _, _, _ => throwM tErr
  | "ord", [x] => match x.base with
    | .str c => match c.toList with
      | [ch] => pure (.int ch.toNat)
      | _ => throwM tErr
    | _ => throwM tErr
  | "chr", [x] => match x.base with
    | .int n => if 0 ≤ n && n < 0x110000 then pure (.str (Char.ofNat n.toNat).toString) else throwM vErr
    | _ => throwM tErr
  | "hex", [x] | "oct", [x] | "bin", [x] => match x.base with
    | .int n =>
      let (b, p) := match k with | "hex" => (16, "0x") | "oct" => (8, "0o") | _ => (2, "0b")
      pure (.str ((if n < 0 then "-" else "") ++ p ++ String.ofList (Nat.toDigits b n.natAbs)))
    | _ => throwM tErr
  | "isinstance", [x, c] => do
    let cs := match c with | .tuple cs => cs | c => [c]
    let s ← getS
    if cs.any (!isClass s ·) then throwM tErr else
    pure (.bool (cs.any (isInstance s x ·)))
  | "issubclass", [x, c] => do
    let cs := match c with | .tuple cs => cs | c => [c]
    let s ← getS
    pure (.bool (cs.any (isSubclass s x ·)))
  | "type", [x] => pure (typeOf s x)
  | "callable", [x] => pure (.bool (match x.base with
    | .fn _ | .meth .. | .next => true
    | .bfun k => !k.startsWith "module:"
    | .obj o => match s.get o with | .cls .. | .cache .. => true | .inst c _ => (clsLookup s c "__call__").isSome | _ => false
    | .data "cmp_to_key" _ | .data "itemgetter" _ => true
    | _ => false))
  | "all", [x] => do let xs ← toListM x; allM xs
  | "any", [x] => do let xs ← toListM x; anyM xs
  | "hash", [x] => do
    let key ← liftE (normKey s x)
    match key with
    | .int n => pure (.int n)
    | _ => throwM (unsup "hash")
  | "format", [x] => (Val.str ·) <$> formatM x ""
  | "format", [x, .str sp] => (Val.str ·) <$> formatM x sp
  | "exit", _ | "quit", _ | "sys.exit", _ => throwM (.err "SystemExit" args)
  | "getattr", [o, .str a] => getattrM o a
  | "getattr", [o, .str a, d] => do
    let s0 ← getS
    -- only AttributeError falls back to the default; evaluate without callbacks
    match (getattrM o a).run s0 with
    | .ok s1 v => do setS s1; pure v
    | .raise _ (.err "AttributeError" _) => pure d
    | _ => getattrM o a
  | "hasattr", [o, .str a] => do
    let s0 ← getS
    match (getattrM o a).run s0 with
    | .ok _ _ => pure (.bool true)
    | .raise _ (.err "AttributeError" _) => pure (.bool false)
    | _ => throwM (unsup "hasattr")
  | "setattr", [o, .str a, v] => do setattrM o a v; pure .none
  | "object", [] => throwM (unsup "object()")
  | "id", _ => throwM (unsup "id (an address)")
  | "vars", _ | "locals", _ | "globals", _ | "eval", _ | "exec", _ | "open", _ | "super", _ | "dir", _ =>
    throwM (unsup k)
  | "staticmethod", [f] => pure (.data "staticmethod" [f])
  | "classmethod", [f] => pure (.data "classmethod" [f])
  | "property", f :: _ => pure (.data "property" [f])
  | _, _ =>
    match (k.splitOn ".").reverse with
    | m :: ty :: rest => methodM (".".intercalate (ty :: rest).reverse) m args kws
    | _ => throwM (unsup ("builtin " ++ k))

partial def dictFrom (args : List Val) : M PDict := do
  match args with
  | [] => pure {}
  | [x] => do
    let s ← getS
    match x.base with
    | .obj o => match s.get o with
      | .dict d _ => pure d
      | _ => pairsInto {} x
    | _ => pairsInto {} x
  | _ => throwM tErr

partial def pairsInto (d : PDict) (x : Val) : M PDict := do
  let xs ← toListM x
  let s ← getS
  xs.foldlM (fun (d : PDict) p => do
    let ps ← toListM p
    match ps with
    | [k, v] => do let nk ← liftE (normKey s k); pure (d.insert nk k v)
    | _ => throwM vErr) d

partial def countInto (d : PDict) (xs : List Val) : M PDict := do
  let s ← getS
  liftE (xs.foldlM (fun (d : PDict) x => do
    let nk ← normKey s x
    match d.find? nk with
    | some (_, .int n) => pure (d.insert nk x (.int (n + 1)))
    | _ => pure (d.insert nk x (.int 1))) d)

partial def sumM (xs : List Val) (acc : Val) : M Val :=
  match xs with
  | [] => pure acc
  | x :: r => match numOp "Add" acc x with
    | some (.ok v) => sumM r v
    | _ => do let v ← binopM "Add" acc x; bounce; sumM r v

partial def allM (xs : List Val) : M Val :=
  match xs with
  | [] => pure (.bool true)
  | x :: r => do if (← truthM x) then allM r else pure (.bool false)

partial def anyM (xs : List Val) : M Val :=
  match xs with
  | [] => pure (.bool false)
  | x :: r => do if (← truthM x) then pure (.bool true) else anyM r

/-- Methods (`self` first) and module functions. -/
partial def methodM (ty m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  let kw (n : String) : Option Val := kws.lookup n
  match ty, args with
  | "str", (.str x) :: rest => strMethod x m rest kws
  | "list", (.obj o) :: rest => listMethod o m rest kws
  | "dict", rest | "OrderedDict", rest | "Counter", rest =>
    if m == "fromkeys" then
      let kind : DK := if ty == "OrderedDict" then .ordered else .plain
      if ty == "Counter" then throwM (.err "NotImplementedError" []) else
      match rest with
      | [ks] => do let xs ← toListM ks; let s ← getS; let d ← liftE (mkDict s (xs.map (·, .none))); allocM (.dict d kind)
      | [ks, v] => do let xs ← toListM ks; let s ← getS; let d ← liftE (mkDict s (xs.map (·, v))); allocM (.dict d kind)
      | _ => throwM tErr
    else match rest with
      | (.obj o) :: rest => dictMethod o m rest kws
      | _ => throwM tErr
  | "set", (.obj o) :: rest => setMethod o m rest
  | "deque", (.obj o) :: rest => dequeMethod o m rest
  | "pq", (.obj o) :: rest =>
    let q := match s.get o with | .pq q => q | _ => o
    let vs := match s.get q with | .list vs => vs | _ => #[]
    match m, rest with
    | "put", [x] | "put_nowait", [x] => do
      let vs ← heapPush vs x
      putM q (.list vs); pure .none
    | "get", [] | "get_nowait", [] => do
      if vs.isEmpty then throwM (unsup "blocking get on an empty queue") else
      let (x, vs) ← heapPop vs
      putM q (.list vs); pure x
    | "empty", [] => pure (.bool vs.isEmpty)
    | "qsize", [] => pure (.int vs.size)
    | _, _ => throwM tErr
  | "tuple", (.tuple xs) :: rest => match m, rest with
    | "count", [v] => do let n ← countEq v xs 0; pure (.int n)
    | "index", [v] => do
      let r ← findEq v xs 0
      match r with | some i => pure (.int i) | none => throwM vErr
    | _, _ => throwM tErr
  | "range", (.data "range" [.int a, .int b, .int c]) :: rest => match m, rest with
    | "count", [v] => do let r ← containsM v (.data "range" [.int a, .int b, .int c]); pure (.int (if r then 1 else 0))
    | "index", [.int n] =>
      if (if c > 0 then a ≤ n && n < b else b < n && n ≤ a) && (n - a) % c == 0 then pure (.int ((n - a) / c))
      else throwM vErr
    | _, _ => throwM tErr
  | "int", x :: rest => match asNum x, m, rest with
    | some (.int n), "bit_length", [] => pure (.int n.natAbs.log2.succ |> fun v => if n == 0 then .int 0 else v)
    | some (.int n), "bit_count", [] => pure (.int ((Nat.toDigits 2 n.natAbs).filter (· == '1')).length)
    | some v, "conjugate", [] => pure v
    | _, _, _ => throwM tErr
  | "float", (.float b) :: rest => match m, rest with
    | "is_integer", [] => pure (.bool (isIntegral b))
    | _, _ => throwM tErr
  | "cache", (.obj o) :: _ =>
    if m == "cache_clear" then do
      modM o fun | .cache g _ => .cache g {} | z => z
      pure .none
    else throwM tErr
  | "sys.stdin", [] => match m with
    | "readline" => do let (s', l) := readLine s; setS s'; pure (.str l)
    | "read" => do setS { s with inp := [] }; pure (.str (String.ofList s.inp))
    | "readlines" => do
      setS { s with inp := [] }
      let ls := splitSep s.inp ['\n'] (-1)
      let ls := if s.inp.getLast? == some '\n' then ls.dropLast else ls
      let ls := ls.map (fun l => .str (String.ofList (l ++ ['\n'])))
      let ls := if s.inp.getLast? == some '\n' || ls.isEmpty then ls else
        ls.dropLast ++ [match s.inp.reverse.takeWhile (· != '\n') with | l => .str (String.ofList l.reverse)]
      allocM (.list ls.toArray)
    | _ => throwM tErr
  | "sys.stdout", [x] => match m with
    | "write" => match x with
      | .str t => do modS (·.emit t); pure (.int t.length)
      | _ => throwM tErr
    | _ => throwM tErr
  | "sys.stdout", [] => if m == "flush" then pure .none else throwM tErr
  | "sys", _ => match m, args with
    | "setrecursionlimit", [_] => pure .none
    | "getrecursionlimit", [] => pure (.int 20000)
    | "exit", _ => throwM (.err "SystemExit" args)
    | _, _ => throwM (unsup ("sys." ++ m))
  | "math", _ => mathFn m args
  | "heapq", h :: rest => match h.base with
    | .obj o => match s.get o with
      | .list vs => match m, rest with
        | "heappush", [x] => do let vs ← heapPush vs x; putM o (.list vs); pure .none
        | "heappop", [] => if vs.isEmpty then throwM (.err "IndexError" []) else do
          let (x, vs) ← heapPop vs; putM o (.list vs); pure x
        | "heapify", [] => do
          let xs ← liftE (msort (fun a b => ltN s a b) vs.toList)
          putM o (.list xs.toArray); pure .none
        | "heappushpop", [x] => do
          let vs ← heapPush vs x
          let (y, vs) ← heapPop vs
          putM o (.list vs); pure y
        | "heapreplace", [x] => if vs.isEmpty then throwM (.err "IndexError" []) else do
          let (y, vs) ← heapPop vs
          let vs ← heapPush vs x
          putM o (.list vs); pure y
        | _, _ => heapqN m args kws
      | _ => heapqN m args kws
    | _ => heapqN m args kws
  | "bisect", a :: x :: rest => match a.base with
    | .obj o => match s.get o with
      | .list vs => do
        if (kw "key").isSome then throwM (unsup "bisect key") else
        let lo ← match rest with | lo :: _ => liftE (asIndex lo) | [] => pure 0
        let hi ← match rest with | [_, hi] => liftE (asIndex hi) | _ => pure vs.size
        let right := m == "bisect" || m == "bisect_right" || m == "insort" || m == "insort_right"
        let rec go (lo hi : Nat) (fuel : Nat) : Except Val Nat := match fuel with
          | 0 => .ok lo
          | fuel + 1 =>
            if lo < hi then
              let mid := (lo + hi) / 2
              match (if right then ltN s x vs[mid]! else ltN s vs[mid]! x) with
              | .ok b => if right then (if b then go lo mid fuel else go (mid + 1) hi fuel)
                         else (if b then go (mid + 1) hi fuel else go lo mid fuel)
              | .error e => .error e
            else .ok lo
        let i ← liftE (go lo.toNat hi.toNat 200)
        if m.startsWith "insort" then do
          putM o (.list (vs.extract 0 i ++ #[x] ++ vs.extract i vs.size)); pure .none
        else pure (.int i)
      | _ => throwM tErr
    | _ => throwM tErr
  | "itertools", _ => itertoolsFn m args kws
  | "functools", _ => match m, args with
    | "reduce", f :: it :: rest => do
      let xs ← toListM it
      let (acc, xs) ← match rest, xs with
        | [i], xs => pure (i, xs)
        | [], x :: xs => pure (x, xs)
        | _, _ => throwM tErr
      reduceM f acc xs
    | "cmp_to_key", [f] => pure (.data "cmp_to_key" [f])
    | "lru_cache", [] | "cache", [] => pure (.data "lru_cache" [])
    | "lru_cache", [f] | "cache", [f] => match f with
      | .fn _ => allocM (.cache f {})
      | _ => pure (.data "lru_cache" [])
    | _, _ => throwM (unsup ("functools." ++ m))
  | "copy", [x] => if m == "copy" then shallowCopy x else deepCopy x
  | "string", [x] =>
    if m == "capwords" then match x with
      | .str t => pure (.str (" ".intercalate ((splitWs t.toList).map fun w => match w with
          | c :: r => String.ofList (cUp c :: r.map cLow)
          | [] => "")))
      | _ => throwM tErr
    else throwM tErr
  | "operator", _ => match m, args with
    | "itemgetter", is => pure (.data "itemgetter" is)
    | "add", [a, b] => binopM "Add" a b
    | "sub", [a, b] => binopM "Sub" a b
    | "mul", [a, b] => binopM "Mult" a b
    | _, _ => throwM tErr
  | "typing", _ => throwM (unsup ("typing." ++ m))

  | "$dunder", self :: rest => match m, rest with
    | "__eq__", [b] => binopM "Eq" self b
    | "__ne__", [b] => binopM "NotEq" self b
    | "__lt__", [b] => binopM "Lt" self b
    | "__le__", [b] => binopM "LtE" self b
    | "__gt__", [b] => binopM "Gt" self b
    | "__ge__", [b] => binopM "GtE" self b
    | "__add__", [b] => binopM "Add" self b
    | "__sub__", [b] => binopM "Sub" self b
    | "__mul__", [b] => binopM "Mult" self b
    | "__truediv__", [b] => binopM "Div" self b
    | "__floordiv__", [b] => binopM "FloorDiv" self b
    | "__mod__", [b] => binopM "Mod" self b
    | "__pow__", [b] => binopM "Pow" self b
    | "__contains__", [b] => (Val.bool ·) <$> containsM b self
    | "__getitem__", [i] => getitemM self i
    | "__len__", [] => (Val.int ·) <$> lenM self
    | "__str__", [] => (Val.str ·) <$> strM self
    | "__repr__", [] => (Val.str ·) <$> reprM self
    | "__iter__", [] => iterM self
    | "__next__", [] => do
      let r ← nextM self
      match r with | some v => pure v | none => throwM (.err "StopIteration" [])
    | "__bool__", [] => (Val.bool ·) <$> truthM self
    | "__neg__", [] => unopM "USub" self
    | "__abs__", [] => builtinM "abs" [self] []
    | _, _ => throwM tErr
  | "re", _ | "re.Pattern", _ => do
    -- `re.f(pattern, string)` or `compiled.f(string)`
    let (pat, rest) ← match ty, args with
      | "re.Pattern", .data "re.Pattern" [.str p] :: rest => pure (p, rest)
      | "re", .str p :: rest => pure (p, rest)
      | _, _ => throwM (unsup ("re." ++ m))
    if !kws.isEmpty then throwM (unsup "re flags") else
    match parsePat pat with
    | none => throwM (unsup ("regular expression " ++ pat))
    | some rp =>
      let mobj (cs : Array Char) (r : Option (Nat × Nat)) : Val := match r with
        | some (a, e) => .data "re.Match" [.str (String.ofList ((cs.toList.drop a).take (e - a))), .int a, .int e]
        | none => .none
      match m, rest with
      | "compile", [] => pure (.data "re.Pattern" [.str pat])
      | "findall", [.str x] =>
        let cs := x.toList.toArray
        allocM (.list ((rfindall rp cs 0 []).map Val.str).toArray)
      | "search", [.str x] => let cs := x.toList.toArray; pure (mobj cs (rsearch rp cs 0 false))
      | "match", [.str x] =>
        let cs := x.toList.toArray
        pure (mobj cs ((rmatch cs rp.eol false rp.pieces 0).map (0, ·)))
      | "fullmatch", [.str x] =>
        let cs := x.toList.toArray
        pure (mobj cs ((rmatch cs rp.eol true rp.pieces 0).map (0, ·)))
      | "sub", [.str r, .str x] =>
        if r.contains '\\' then throwM (unsup "re.sub with escapes") else
        let cs := x.toList.toArray
        pure (.str (String.ofList (rsub rp cs r.toList 0 [] (cs.size + 2))))
      | _, _ => throwM (unsup ("re." ++ m))
  | "re.Match", (.data "re.Match" [g, a, e]) :: rest => match m, rest with
    | "group", [] | "group", [.int 0] => pure g
    | "start", [] => pure a
    | "end", [] => pure e
    | "span", [] => pure (.tuple [a, e])
    | _, _ => throwM (unsup ("re.Match." ++ m))
  | _, _ => throwM (unsup ("method " ++ ty ++ "." ++ m))

partial def heapqN (m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  match m, args with
  | "nlargest", [n, it] | "nsmallest", [n, it] => do
    let n ← liftE (asIndex n)
    let xs ← toListM it
    let ks ← match kws.lookup "key" with | none | some .none => pure xs | some f => keysM f xs []
    let ys ← sortByM xs ks (m == "nlargest")
    allocM (.list (ys.take n.toNat).toArray)
  | _, _ => throwM tErr

partial def heapPush (vs : Array Val) (x : Val) : M (Array Val) := do
  let s ← getS
  let vs := vs.push x
  let rec up (vs : Array Val) (i : Nat) (fuel : Nat) : Except Val (Array Val) := match fuel with
    | 0 => .ok vs
    | fuel + 1 =>
      if i == 0 then .ok vs else
      let p := (i - 1) / 2
      match ltN s vs[i]! vs[p]! with
      | .ok true => up ((vs.set! i vs[p]!).set! p vs[i]!) p fuel
      | .ok false => .ok vs
      | .error e => .error e
  liftE (up vs (vs.size - 1) 64)

partial def heapPop (vs : Array Val) : M (Val × Array Val) := do
  let s ← getS
  let top := vs[0]!
  let last := vs.back!
  let vs := vs.pop
  if vs.isEmpty then pure (top, vs) else
  let vs := vs.set! 0 last
  let n := vs.size
  let rec down (vs : Array Val) (i : Nat) (fuel : Nat) : Except Val (Array Val) := match fuel with
    | 0 => .ok vs
    | fuel + 1 =>
      let l := 2 * i + 1
      let r := 2 * i + 2
      if l ≥ n then .ok vs else
      match (if r < n then ltN s vs[r]! vs[l]! else .ok false) with
      | .error e => .error e
      | .ok rl =>
        let c := if rl then r else l
        match ltN s vs[c]! vs[i]! with
        | .ok true => down ((vs.set! i vs[c]!).set! c vs[i]!) c fuel
        | .ok false => .ok vs
        | .error e => .error e
  let vs ← liftE (down vs 0 64)
  pure (top, vs)

partial def reduceM (f acc : Val) (xs : List Val) : M Val :=
  match xs with
  | [] => pure acc
  | x :: r => do let a ← callV f [acc, x] []; bounce; reduceM f a r

partial def countEq (v : Val) (xs : List Val) (n : Nat) : M Nat :=
  match xs with
  | [] => pure n
  | x :: r => do let e ← eqM x v; countEq v r (if e then n + 1 else n)

partial def findEq (v : Val) (xs : List Val) (i : Nat) : M (Option Nat) :=
  match xs with
  | [] => pure none
  | x :: r => do let e ← eqM x v; if e then pure (some i) else findEq v r (i + 1)

partial def shallowCopy (x : Val) : M Val := do
  let s ← getS
  match x.base with
  | .obj o => match s.get o with
    | .list vs => allocM (.list vs)
    | .dict d k => allocM (.dict d k)
    | .set d f => allocM (.set d.copySet f)
    | .deque vs => allocM (.deque vs)
    | _ => throwM (unsup "copy of an object")
  | _ => pure x

partial def deepCopy (x : Val) : M Val := do
  let s ← getS
  match x.base with
  | .tuple vs => do let ys ← vs.mapM deepCopy; pure (.tuple ys)
  | .obj o => match s.get o with
    | .list vs => do let ys ← vs.toList.mapM deepCopy; allocM (.list ys.toArray)
    | .dict d k => do
      let its ← d.items.mapM fun (a, b) => do pure (a, ← deepCopy b)
      let s ← getS
      let d ← liftE (mkDict s its)
      allocM (.dict d k)
    | .set d f => allocM (.set d.copySet f)
    | .deque vs => do let ys ← vs.toList.mapM deepCopy; allocM (.deque ys.toArray)
    | _ => throwM (unsup "deepcopy of an object")
  | _ => pure x

partial def mathFn (m : String) (args : List Val) : M Val := do
  let fl (x : Val) : M Float := liftE (match asNum x with | some v => toF v | none => .error tErr)
  let toInt (x : Float) : M Val :=
    let b := bOf x
    if isNaN b then throwM vErr else if !isFinite b then throwM (.err "OverflowError" []) else pure (.int (floatToInt b))
  match m, args with
  | "sqrt", [x] => do
    let f ← fl x
    if f < 0.0 then throwM vErr else pure (fV f.sqrt)
  | "isqrt", [x] => match asNum x with
    | some (.int n) => if n < 0 then throwM vErr else pure (.int n.toNat.sqrt)
    | _ => throwM tErr
  | "ceil", [x] => match asNum x with
    | some (.int n) => pure (.int n)
    | _ => do let f ← fl x; toInt f.ceil
  | "floor", [x] => match asNum x with
    | some (.int n) => pure (.int n)
    | _ => do let f ← fl x; toInt f.floor
  | "trunc", [x] => match asNum x with
    | some (.int n) => pure (.int n)
    | _ => do let f ← fl x; toInt (if f < 0.0 then f.ceil else f.floor)
  | "gcd", xs => do
    let ns ← liftE (xs.mapM asIndex)
    pure (.int (ns.foldl (fun a b => Int.ofNat (Nat.gcd a.natAbs b.natAbs)) 0))
  | "lcm", xs => do
    let ns ← liftE (xs.mapM asIndex)
    pure (.int (ns.foldl (fun a b => Int.ofNat (Nat.lcm a.natAbs b.natAbs)) 1))
  | "factorial", [x] => match asNum x with
    | some (.int n) => if n < 0 then throwM vErr else pure (.int ((List.range n.toNat).foldl (fun a i => a * (i + 1)) 1 : Nat))
    | _ => throwM tErr
  | "comb", [a, b] => match asNum a, asNum b with
    | some (.int n), some (.int k) => if n < 0 || k < 0 then throwM vErr else
      pure (.int (if k > n then 0 else
        ((List.range k.toNat).foldl (fun acc i => acc * (n.toNat - i)) 1 / (List.range k.toNat).foldl (fun acc i => acc * (i + 1)) 1 : Nat)))
    | _, _ => throwM tErr
  | "perm", [a, b] => match asNum a, asNum b with
    | some (.int n), some (.int k) => if n < 0 || k < 0 then throwM vErr else
      pure (.int (if k > n then 0 else ((List.range k.toNat).foldl (fun acc i => acc * (n.toNat - i)) 1 : Nat)))
    | _, _ => throwM tErr
  | "log", [x] => do let f ← fl x; if f ≤ 0.0 then throwM vErr else pure (fV f.log)
  | "log", [x, b] => do
    let f ← fl x
    let g ← fl b
    if f ≤ 0.0 || g ≤ 0.0 then throwM vErr else pure (fV (f.log / g.log))
  | "log10", [x] => do let f ← fl x; if f ≤ 0.0 then throwM vErr else pure (fV f.log10)
  | "log2", [x] => do let f ← fl x; if f ≤ 0.0 then throwM vErr else pure (fV f.log2)
  | "exp", [x] => do let f ← fl x; pure (fV f.exp)
  | "fabs", [x] => do let f ← fl x; pure (fV f.abs)
  | "pow", [x, y] => do let f ← fl x; let g ← fl y; pure (fV (Float.pow f g))
  | "hypot", [x, y] => do let f ← fl x; let g ← fl y; pure (fV (Float.sqrt (f * f + g * g)))
  | "sin", [x] => do let f ← fl x; pure (fV f.sin)
  | "cos", [x] => do let f ← fl x; pure (fV f.cos)
  | "tan", [x] => do let f ← fl x; pure (fV f.tan)
  | "atan", [x] => do let f ← fl x; pure (fV f.atan)
  | "asin", [x] => do let f ← fl x; pure (fV f.asin)
  | "acos", [x] => do let f ← fl x; pure (fV f.acos)
  | "atan2", [x, y] => do let f ← fl x; let g ← fl y; pure (fV (Float.atan2 f g))
  | "degrees", [x] => do let f ← fl x; pure (fV (f * (180.0 / 3.141592653589793)))
  | "radians", [x] => do let f ← fl x; pure (fV (f * (3.141592653589793 / 180.0)))
  | "isinf", [x] => do let f ← fl x; pure (.bool f.isInf)
  | "isnan", [x] => do let f ← fl x; pure (.bool f.isNaN)
  | "isfinite", [x] => do let f ← fl x; pure (.bool f.isFinite)
  | "modf", [x] => do
    let f ← fl x
    let ip := if f < 0.0 then f.ceil else f.floor
    pure (.tuple [fV (f - ip), fV ip])
  | "copysign", [x, y] => do
    let f ← fl x
    let g ← fl y
    pure (.float ((bOf f &&& 0x7FFFFFFFFFFFFFFF) ||| (bOf g &&& 0x8000000000000000)))
  | "prod", [x] => do
    let xs ← toListM x
    xs.foldlM (fun a b => binopM "Mult" a b) (.int 1)
  | _, _ => throwM (unsup ("math." ++ m))

partial def itertoolsFn (m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  match m, args with
  | "permutations", it :: rest => do
    let xs ← toListM it
    let r ← match rest, kws.lookup "r" with
      | [r], _ | [], some r => (fun n => n.toNat) <$> liftE (asIndex r)
      | _, _ => pure xs.length
    let rec perms (xs : List (Nat × Val)) (r : Nat) : List (List Val) := match r with
      | 0 => [[]]
      | r + 1 => xs.flatMap fun (i, x) => (perms (xs.filter (·.1 != i)) r).map (x :: ·)
    let ps := perms ((List.range xs.length).zip xs) r
    allocM (.iter (.seq (ps.map .tuple)))
  | "combinations", [it, r] => do
    let xs ← toListM it
    let r ← liftE (asIndex r)
    let rec combs (xs : List Val) (r : Nat) : List (List Val) := match r, xs with
      | 0, _ => [[]]
      | _, [] => []
      | r + 1, x :: rest => (combs rest r).map (x :: ·) ++ combs rest (r + 1)
    allocM (.iter (.seq ((combs xs r.toNat).map .tuple)))
  | "combinations_with_replacement", [it, r] => do
    let xs ← toListM it
    let r ← liftE (asIndex r)
    let rec combsR (xs : List Val) (r : Nat) : List (List Val) := match r, xs with
      | 0, _ => [[]]
      | _, [] => []
      | r + 1, x :: rest => (combsR (x :: rest) r).map (x :: ·) ++ combsR rest (r + 1)
    allocM (.iter (.seq ((combsR xs r.toNat).map .tuple)))
  | "product", its => do
    let rep ← match kws.lookup "repeat" with | some r => (fun n => n.toNat) <$> liftE (asIndex r) | none => pure 1
    let pools ← its.mapM toListM
    let pools := List.flatten (List.replicate rep pools)
    let res := pools.foldl (fun acc pool => acc.flatMap fun p => pool.map fun x => p ++ [x]) [[]]
    allocM (.iter (.seq (res.map .tuple)))
  | "accumulate", it :: rest => do
    let xs ← toListM it
    let f := match rest, kws.lookup "func" with | [f], _ => some f | [], some f => some f | _, _ => none
    let init := kws.lookup "initial"
    let xs := match init with | some i => i :: xs | none => xs
    match xs with
    | [] => allocM (.iter (.seq []))
    | x :: r => do
      let ys ← accumM f r x [x]
      allocM (.iter (.seq ys))
  | "groupby", it :: rest => do
    let xs ← toListM it
    let key := match rest, kws.lookup "key" with | [k], _ => k | [], some k => k | _, _ => .none
    let ks ← if key == .none then pure xs else keysM key xs []
    let groups ← groupM (xs.zip ks) none [] []
    let gs ← groups.mapM fun (k, g) => do let i ← allocM (.iter (.seq g)); pure (Val.tuple [k, i])
    allocM (.iter (.seq gs))
  | "chain", its => do let is ← its.mapM iterM; allocM (.iter (.chain is))
  | "count", rest => do
    let st ← match rest with | st :: _ => liftE (asIndex st) | [] => pure 0
    let sp ← match rest with | [_, sp] => liftE (asIndex sp) | _ => pure 1
    allocM (.iter (.count st sp))
  | _, _ => throwM (unsup ("itertools." ++ m))

partial def accumM (f : Option Val) (xs : List Val) (acc : Val) (out : List Val) : M (List Val) :=
  match xs with
  | [] => pure out.reverse
  | x :: r => do
    let a ← match f with | some g => callV g [acc, x] [] | none => binopM "Add" acc x
    accumM f r a (a :: out)

partial def groupM (ps : List (Val × Val)) (cur : Option Val) (g : List Val) (out : List (Val × List Val)) :
    M (List (Val × List Val)) :=
  match ps with
  | [] => pure (match cur with | some k => (out ++ [(k, g.reverse)]) | none => out)
  | (x, k) :: r => match cur with
    | none => groupM r (some k) [x] out
    | some c => do
      let same ← eqM c k
      if same then groupM r cur (x :: g) out else groupM r (some k) [x] (out ++ [(c, g.reverse)])

partial def strMethod (x : String) (m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let cs := x.toList
  let str (cs : List Char) : M Val := pure (.str (String.ofList cs))
  let argStr (v : Val) : M (List Char) := match v with | .str y => pure y.toList | _ => throwM tErr
  let stripSet (v : Option Val) : M (Char → Bool) := match v with
    | none | some .none => pure isWs
    | some (.str y) => pure (fun c => y.toList.contains c)
    | _ => throwM tErr
  match m, args with
  | "upper", [] => str (cs.map cUp)
  | "lower", [] | "casefold", [] => str (cs.map cLow)
  | "swapcase", [] => str (cs.map fun c => if c.isUpper then cLow c else if c.isLower then cUp c else c)
  | "capitalize", [] => str (match cs with | c :: r => cUp c :: r.map cLow | [] => [])
  | "title", [] => str (titleCs cs)
  | "isupper", [] => pure (.bool (cs.any Char.isUpper && !cs.any Char.isLower))
  | "islower", [] => pure (.bool (cs.any Char.isLower && !cs.any Char.isUpper))
  | "istitle", [] => pure (.bool (isTitleCs cs))
  | "isalpha", [] => pure (.bool (!cs.isEmpty && cs.all Char.isAlpha))
  | "isdigit", [] | "isnumeric", [] | "isdecimal", [] => pure (.bool (!cs.isEmpty && cs.all Char.isDigit))
  | "isalnum", [] => pure (.bool (!cs.isEmpty && cs.all Char.isAlphanum))
  | "isspace", [] => pure (.bool (!cs.isEmpty && cs.all isWs))
  | "isascii", [] => pure (.bool (cs.all (·.toNat < 128)))
  | "isidentifier", [] => pure (.bool (match cs with
      | c :: r => (c.isAlpha || c == '_') && r.all (fun d => d.isAlphanum || d == '_')
      | [] => false))
  | "strip", _ => do let p ← stripSet args.head?; str ((cs.dropWhile p).reverse.dropWhile p |>.reverse)
  | "lstrip", _ => do let p ← stripSet args.head?; str (cs.dropWhile p)
  | "rstrip", _ => do let p ← stripSet args.head?; str ((cs.reverse.dropWhile p).reverse)
  | "split", _ | "rsplit", _ => do
    let sep := match args, kws.lookup "sep" with | sp :: _, _ => sp | [], some sp => sp | _, _ => .none
    let mx ← match args, kws.lookup "maxsplit" with
      | [_, n], _ | [_], some n => liftE (asIndex n)
      | _, _ => pure (-1)
    match sep with
    | .none =>
      if mx >= 0 && m == "split" then
        allocM (.list ((splitWsMax cs mx [] (cs.length + 2)).map (fun w => Val.str (String.ofList w))).toArray)
      else if mx >= 0 then throwM (unsup "rsplit maxsplit")
      else allocM (.list ((splitWs cs).map (fun w => Val.str (String.ofList w))).toArray)
    | .str sp =>
      if sp.isEmpty then throwM vErr else
      if m == "rsplit" && mx >= 0 then
        let parts := (splitSep cs.reverse sp.toList.reverse mx).reverse.map List.reverse
        allocM (.list (parts.map (fun w => Val.str (String.ofList w))).toArray)
      else allocM (.list ((splitSep cs sp.toList mx).map (fun w => Val.str (String.ofList w))).toArray)
    | _ => throwM tErr
  | "splitlines", [] =>
    let ls := splitSep cs ['\n'] (-1)
    let ls := if cs.getLast? == some '\n' then ls.dropLast else ls
    allocM (.list (ls.map (fun l => Val.str (String.ofList (if l.getLast? == some '\r' then l.dropLast else l)))).toArray)
  | "join", [it] => do
    let xs ← toListM it
    let ss ← xs.mapM fun v => match v.base with | .str y => pure y | _ => throwM tErr
    pure (.str (x.intercalate ss))
  | "replace", o :: n :: rest => do
    let o ← argStr o
    let n ← argStr n
    let mx ← match rest with | [c] => liftE (asIndex c) | _ => pure (-1)
    str (replaceSub cs o n mx)
  | "count", sub :: rest => do
    let sub ← argStr sub
    let ix ← liftE (sliceIdx cs.length (rest.headD .none) (rest.getD 1 .none) .none)
    let part := match ix.head? with | some i => (cs.drop i).take ix.length | none => []
    let ok := match rest with | [] => true | _ => !ix.isEmpty || sub.isEmpty
    pure (.int (if ok then countSub part sub else 0))
  | "find", sub :: rest | "index", sub :: rest | "rfind", sub :: rest | "rindex", sub :: rest => do
    let sub ← argStr sub
    let st : Int ← match rest with | st :: _ => (match st with | .none => pure 0 | v => liftE (asIndex v)) | [] => pure 0
    let en : Int ← match rest with
      | [_, en] => (match en with | .none => pure (cs.length : Int) | v => liftE (asIndex v))
      | _ => pure (cs.length : Int)
    let n : Int := cs.length
    let st := if st < 0 then max 0 (st + n) else min st n
    let en := if en < 0 then max 0 (en + n) else min en n
    let part := (cs.take en.toNat).drop st.toNat
    let r := if st > en then none else if m.startsWith "r" then rfindSub part sub else findSub part sub
    match r with
    | some i => pure (.int (i + st))
    | none => if m == "index" || m == "rindex" then throwM vErr else pure (.int (-1))
  | "startswith", [p] | "endswith", [p] => do
    let ps ← match p with
      | .tuple vs => vs.mapM argStr
      | v => (fun y => [y]) <$> argStr v
    pure (.bool (ps.any fun p => if m == "startswith" then isPrefixL p cs else isPrefixL p.reverse cs.reverse))
  | "zfill", [w] => do
    let w ← liftE (asIndex w)
    let n := w.toNat
    if cs.length ≥ n then str cs else
    let z := List.replicate (n - cs.length) '0'
    match cs with
    | c :: r => if c == '-' || c == '+' then str (c :: z ++ r) else str (z ++ cs)
    | [] => str z
  | "center", w :: rest | "ljust", w :: rest | "rjust", w :: rest => do
    let w ← liftE (asIndex w)
    let fc ← match rest with | [f] => (do let f ← argStr f; match f with | [c] => pure c | _ => throwM tErr) | _ => pure ' '
    let n := w.toNat
    if cs.length ≥ n then str cs else
    let k := n - cs.length
    match m with
    | "ljust" => str (cs ++ List.replicate k fc)
    | "rjust" => str (List.replicate k fc ++ cs)
    | _ =>
      let left := k / 2 + (if k % 2 == 1 && cs.length % 2 == 1 then 1 else 0)
      str (List.replicate left fc ++ cs ++ List.replicate (k - left) fc)
  | "format", _ => (Val.str ·) <$> strFormatM cs args kws 0 ""
  | "partition", [sp] | "rpartition", [sp] => do
    let sp ← argStr sp
    let r := if m == "partition" then findSub cs sp else rfindSub cs sp
    match r with
    | some i => pure (.tuple [.str (String.ofList (cs.take i)), .str (String.ofList sp), .str (String.ofList (cs.drop (i + sp.length)))])
    | none => if m == "partition" then pure (.tuple [.str x, .str "", .str ""]) else pure (.tuple [.str "", .str "", .str x])
  | "removeprefix", [p] => do let p ← argStr p; str (if isPrefixL p cs then cs.drop p.length else cs)
  | "removesuffix", [p] => do
    let p ← argStr p
    str (if isPrefixL p.reverse cs.reverse && !p.isEmpty then cs.take (cs.length - p.length) else cs)
  | "maketrans", [.str y] | "maketrans", [.str y, .str _] => do
    -- `str.maketrans(x, y[, z])` (called on the type: `x` is the first argument)
    let zs := match args with | [_, .str z] => z.toList | _ => []
    if cs.length != y.length then throwM vErr else
    let s ← getS
    let d ← liftE (mkDict s ((cs.zip y.toList).map (fun (a, b) => (Val.int a.toNat, Val.int b.toNat)) ++
      zs.map fun c => (Val.int c.toNat, Val.none)))
    allocM (.dict d .plain)
  | "translate", [t] => do
    let s ← getS
    match t.base with
    | .obj o => match s.get o with
      | .dict d _ => do
        let out ← cs.foldlM (fun (acc : List Char) c => match d.find? (.int c.toNat) with
          | none => pure (c :: acc)
          | some (_, .none) => pure acc
          | some (_, .str r) => pure (r.toList.reverse ++ acc)
          | some (_, .int n) => pure (Char.ofNat n.toNat :: acc)
          | some _ => throwM tErr) []
        str out.reverse
      | _ => throwM (unsup "str.translate with a table that is no dict")
    | _ => throwM (unsup "str.translate with a table that is no dict")
  | "expandtabs", [] => str (cs.flatMap fun c => if c == '\t' then List.replicate 8 ' ' else [c])
  | _, _ => throwM (unsup ("str." ++ m))

partial def listMethod (o : Nat) (m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  let xs := match s.get o with | .list xs => xs | _ => #[]
  match m, args with
  | "append", [v] => do modM o (fun | .list zs => .list (zs.push v) | z => z); pure .none
  | "extend", [it] => do
    let ys ← toListM it
    modM o (fun | .list zs => .list (zs ++ ys.toArray) | z => z); pure .none
  | "insert", [i, v] => do
    let i ← liftE (asIndex i)
    let n : Int := xs.size
    let j := if i < 0 then max 0 (i + n) else min i n
    putM o (.list (xs.extract 0 j.toNat ++ #[v] ++ xs.extract j.toNat xs.size)); pure .none
  | "remove", [v] => do
    let r ← findEq v xs.toList 0
    match r with
    | some j => do putM o (.list (xs.extract 0 j ++ xs.extract (j + 1) xs.size)); pure .none
    | none => throwM vErr
  | "pop", rest => do
    let i ← match rest with | [i] => liftE (asIndex i) | _ => pure (-1)
    if xs.isEmpty then throwM (.err "IndexError" []) else
    match idxNorm xs.size i with
    | some j => do putM o (.list (xs.extract 0 j ++ xs.extract (j + 1) xs.size)); pure xs[j]!
    | none => throwM (.err "IndexError" [])
  | "index", v :: rest => do
    let st ← match rest with | st :: _ => liftE (asIndex st) | [] => pure 0
    let n : Int := xs.size
    let st := if st < 0 then max 0 (st + n) else min st n
    let r ← findEq v (xs.toList.drop st.toNat) 0
    match r with
    | some j => pure (.int (j + st))
    | none => throwM vErr
  | "count", [v] => do let n ← countEq v xs.toList 0; pure (.int n)
  | "sort", [] => do
    let ys := xs.toList
    let ks ← match kws.lookup "key" with | none | some .none => pure ys | some f => keysM f ys []
    let rev ← match kws.lookup "reverse" with | none => pure false | some r => truthM r
    let zs ← sortByM ys ks rev
    putM o (.list zs.toArray); pure .none
  | "reverse", [] => do putM o (.list xs.reverse); pure .none
  | "copy", [] => allocM (.list xs)
  | "clear", [] => do putM o (.list #[]); pure .none
  | _, _ => throwM tErr

partial def dictMethod (o : Nat) (m : String) (args : List Val) (kws : List (Name × Val)) : M Val := do
  let s ← getS
  let (d, k) := match s.get o with | .dict d k => (d, k) | _ => ({}, .plain)
  let isCounter := match k with | .counter => true | _ => false
  match m, args with
  | "keys", [] => pure (.data "dict_keys" [.obj o])
  | "values", [] => pure (.data "dict_values" [.obj o])
  | "items", [] => pure (.data "dict_items" [.obj o])
  | "get", key :: rest => do
    let nk ← liftE (normKey s key)
    match d.find? nk with
    | some (_, v) => pure v
    | none => pure (rest.headD .none)
  | "setdefault", key :: rest => do
    let nk ← liftE (normKey s key)
    match d.find? nk with
    | some (_, v) => pure v
    | none => do
      let v := rest.headD .none
      putM o (.dict (d.insert nk key v) k); pure v
  | "pop", key :: rest => do
    let nk ← liftE (normKey s key)
    match d.find? nk with
    | some (_, v) => do putM o (.dict (d.erase nk) k); pure v
    | none => match rest with
      | [dv] => pure dv
      | _ => throwM (keyErr key)
  | "popitem", [] => match d.items.getLast? with
    | some (a, b) => do
      let nk ← liftE (normKey s a)
      putM o (.dict (d.erase nk) k); pure (.tuple [a, b])
    | none => throwM (keyErr .none)
  | "update", rest => do
    if isCounter then
      let xs ← match rest with
        | [x] => (do
          let s ← getS
          match x.base with
          | .obj p => match s.get p with
            | .dict e _ => pure (some e)
            | _ => pure none
          | _ => pure none)
        | _ => pure none
      match xs, rest with
      | some e, _ => do
        let s ← getS
        let d' := e.items.foldl (fun (m : PDict) (kk, v) => match normKey s kk with
          | .ok nk => match m.find? nk with
            | some (_, w) => match numOp "Add" w v with | some (.ok r) => m.insert nk kk r | _ => m
            | none => m.insert nk kk v
          | .error _ => m) d
        putM o (.dict d' k); pure .none
      | none, [x] => do
        let ys ← toListM x
        let d' ← countInto d ys
        putM o (.dict d' k); pure .none
      | _, _ => pure .none
    else do
      let e ← dictFrom rest
      let s ← getS
      let d' := e.items.foldl (fun (m : PDict) (kk, v) => match normKey s kk with | .ok nk => m.insert nk kk v | .error _ => m) d
      let d' ← liftE (kws.foldlM (fun (m : PDict) (n, v) => do let nk ← normKey s (.str n); pure (m.insert nk (.str n) v)) d')
      putM o (.dict d' k); pure .none
  | "copy", [] => allocM (.dict d k)
  | "clear", [] => do putM o (.dict {} k); pure .none
  | "most_common", rest => do
    let its := d.items.mergeSort (fun x y => match numCmp x.2 y.2 with | some .lt => false | _ => true)
    let its := match rest with | [.int n] => its.take n.toNat | _ => its
    allocM (.list (its.map fun (a, b) => Val.tuple [a, b]).toArray)
  | "elements", [] =>
    let ys := d.items.flatMap fun (a, b) => match b with | .int n => List.replicate n.toNat a | _ => []
    allocM (.iter (.seq ys))
  | "total", [] => sumM (d.items.map (·.2)) (.int 0)
  | "subtract", [x] => do
    let ys ← toListM x
    let s ← getS
    let d' ← liftE (ys.foldlM (fun (m : PDict) y => do
      let nk ← normKey s y
      match m.find? nk with
      | some (_, .int n) => pure (m.insert nk y (.int (n - 1)))
      | _ => pure (m.insert nk y (.int (-1)))) d)
    putM o (.dict d' k); pure .none
  | "move_to_end", key :: _ => do
    let nk ← liftE (normKey s key)
    match d.find? nk with
    | some (a, v) => do putM o (.dict ((d.erase nk).insert nk a v) k); pure .none
    | none => throwM (keyErr key)
  | _, _ => throwM tErr

partial def setMethod (o : Nat) (m : String) (args : List Val) : M Val := do
  let s ← getS
  let (d, fz) := match s.get o with | .set d f => (d, f) | _ => (PDict.newSet, false)
  let ins (d : PDict) (x : Val) : M PDict := do let nk ← liftE (normKey s x); pure (d.insert nk x .none)
  /- the argument as a set: a set itself, else its items in a new set -/
  let asSet (it : Val) : M (PDict × Bool) := do
    let s ← getS
    match it.base with
    | .obj p => match s.get p with
      | .set e _ => pure (e, true)
      | _ => do let xs ← toListM it; let s ← getS; let e ← liftE (mkSet s xs); pure (e, false)
    | _ => do let xs ← toListM it; let s ← getS; let e ← liftE (mkSet s xs); pure (e, false)
  match m, args with
  | "add", [x] => do let d' ← ins d x; putM o (.set d' fz); pure .none
  | "remove", [x] => do
    let nk ← liftE (normKey s x)
    if d.idx.contains nk then do putM o (.set (d.erase nk) fz); pure .none else throwM (keyErr x)
  | "discard", [x] => do
    let nk ← liftE (normKey s x)
    putM o (.set (d.erase nk) fz); pure .none
  | "pop", [] => match d.popSet with
    | some (x, d') => do putM o (.set d' fz); pure x
    | none => throwM (keyErr .none)
  | "clear", [] => do putM o (.set PDict.newSet fz); pure .none
  | "copy", [] => allocM (.set d.copySet fz)
  | "update", its | "union", its => do
    let d' ← its.foldlM (fun (acc : PDict) it => do
      let s ← getS
      match it.base with
      | .obj p => match s.get p with
        | .set e _ => pure (acc.merge e)
        | _ => do let xs ← toListM it; xs.foldlM ins acc
      | _ => do let xs ← toListM it; xs.foldlM ins acc) (if m == "union" then d.copySet else d)
    if m == "union" then allocM (.set d' fz) else do putM o (.set d' fz); pure .none
  | "intersection", [it] | "intersection_update", [it] => do
    let (e, isSet) ← asSet it
    let s ← getS
    let r := if isSet then setInter s d e
      else e.keys.foldl (fun r k => if setHas s d k then setInsert s r k else r) PDict.newSet
    if m.endsWith "_update" then do putM o (.set r fz); pure .none else allocM (.set r fz)
  | "difference", [it] | "difference_update", [it] => do
    let (e, isSet) ← asSet it
    let s ← getS
    let r := if isSet && m == "difference" then setDiff s d e
      else (e.keys.foldl (setErase s) (if m == "difference" then d.copySet else d)).compactSet
    if m.endsWith "_update" then do putM o (.set r fz); pure .none else allocM (.set r fz)
  | "symmetric_difference", [it] | "symmetric_difference_update", [it] => do
    let (e, _) ← asSet it
    let s ← getS
    let r := if m.endsWith "_update" then setSymUpd s d e else setSym s d e
    if m.endsWith "_update" then do putM o (.set r fz); pure .none else allocM (.set r fz)
  | "issubset", [it] => do
    let (e, _) ← asSet it
    pure (.bool (d.idx.keys.all e.idx.contains))
  | "issuperset", [it] => do
    let (e, _) ← asSet it
    pure (.bool (e.idx.keys.all d.idx.contains))
  | "isdisjoint", [it] => do
    let (e, _) ← asSet it
    pure (.bool (!e.idx.keys.any d.idx.contains))
  | _, _ => throwM tErr

partial def dequeMethod (o : Nat) (m : String) (args : List Val) : M Val := do
  let s ← getS
  let xs := match s.get o with | .deque xs => xs | _ => #[]
  match m, args with
  | "append", [v] => do modM o (fun | .deque zs => .deque (zs.push v) | z => z); pure .none
  | "appendleft", [v] => do putM o (.deque (#[v] ++ xs)); pure .none
  | "pop", [] => if xs.isEmpty then throwM (.err "IndexError" []) else do putM o (.deque xs.pop); pure xs.back!
  | "popleft", [] => if xs.isEmpty then throwM (.err "IndexError" []) else do
    putM o (.deque (xs.extract 1 xs.size)); pure xs[0]!
  | "extend", [it] => do let ys ← toListM it; putM o (.deque (xs ++ ys.toArray)); pure .none
  | "extendleft", [it] => do let ys ← toListM it; putM o (.deque (ys.reverse.toArray ++ xs)); pure .none
  | "rotate", rest => do
    let n ← match rest with | [n] => liftE (asIndex n) | _ => pure 1
    if xs.isEmpty then pure .none else
    let k := (n.fmod xs.size).toNat
    putM o (.deque (xs.extract (xs.size - k) xs.size ++ xs.extract 0 (xs.size - k))); pure .none
  | "clear", [] => do putM o (.deque #[]); pure .none
  | "count", [v] => do let n ← countEq v xs.toList 0; pure (.int n)
  | "reverse", [] => do putM o (.deque xs.reverse); pure .none
  | "copy", [] => allocM (.deque xs)
  | "remove", [v] => do
    let r ← findEq v xs.toList 0
    match r with
    | some j => do putM o (.deque (xs.extract 0 j ++ xs.extract (j + 1) xs.size)); pure .none
    | none => throwM vErr
  | "index", [v] => do
    let r ← findEq v xs.toList 0
    match r with | some j => pure (.int j) | none => throwM vErr
  | _, _ => throwM tErr

end

/-! ## The operations -/

/-- A display's elements, the starred ones expanded. -/
def expand (stars : List Bool) (vs : List Val) : M (List Val) :=
  let rec go (ps : List (Bool × Val)) (acc : List Val) : M (List Val) :=
    match ps with
    | [] => pure acc
    | (true, v) :: r => do let xs ← toListM v; go r (acc ++ xs)
    | (false, v) :: r => go r (acc ++ [v])
  go (stars.zip vs) []

def dictDisplay (stars : List Bool) (vs : List Val) : M Val := do
  let rec go (ps : List Bool) (vs : List Val) (d : PDict) : M PDict := match ps, vs with
    | [], _ => pure d
    | false :: ps, k :: v :: vs => do
      let s ← getS
      let nk ← liftE (normKey s k)
      go ps vs (d.insert nk k v)
    | true :: ps, m :: vs => do
      let s ← getS
      match m.base with
      | .obj o => match s.get o with
        | .dict e _ => go ps vs (e.items.foldl (fun dd (kk, v) => match normKey s kk with
            | .ok nk => dd.insert nk kk v | .error _ => dd) d)
        | _ => throwM (unsup "** of a non-dict")
      | _ => throwM tErr
    | _, _ => throwM tErr
  let d ← go stars vs {}
  allocM (.dict d .plain)

def kwargsDisplay (names : List (Option Name)) (vs : List Val) : M Val := do
  let rec go (ns : List (Option Name)) (vs : List Val) (acc : List (Name × Val)) : M (List (Name × Val)) :=
    match ns, vs with
    | [], _ => pure acc
    | some n :: ns, v :: vs => if acc.any (·.1 == n) then throwM tErr else go ns vs (acc ++ [(n, v)])
    | none :: ns, m :: vs => do
      let s ← getS
      match m.base with
      | .obj o => match s.get o with
        | .dict e _ => do
          let ps ← e.items.mapM fun (kk, v) => match kk with
            | .str n => pure (n, v)
            | _ => throwM tErr
          if ps.any (fun p => acc.any (·.1 == p.1)) then throwM tErr else go ns vs (acc ++ ps)
        | _ => throwM (unsup "** of a non-dict")
      | _ => throwM tErr
    | _, _ => throwM tErr
  let ps ← go names vs []
  pure (.tuple (ps.map fun (n, v) => .tuple [.str n, v]))

def unpackM (before : Nat) (star : Bool) (after : Nat) (v : Val) : M Val := do
  let s ← getS
  let xs ← match nativeList s v with
    | some xs => pure xs
    | none => do
      let it ← iterM v
      if star then drain it [] else takeM it (before + 1) []
  if !star then
    if xs.length == before then pure (.tuple xs) else throwM vErr
  else
    if xs.length < before + after then throwM vErr else
    let mid := (xs.drop before).take (xs.length - before - after)
    let l ← allocM (.list mid.toArray)
    pure (.tuple (xs.take before ++ [l] ++ xs.drop (xs.length - after)))

def mkClassM (x : Name) (q : String) (kws : List Name) (ns : List Name) (vs : List Val) : M Val := do
  let s ← getS
  if !kws.isEmpty then throwM (unsup "class keywords") else
  let nb := vs.length - kws.length - ns.length
  let bases := vs.take nb
  let nsv := ns.zip (vs.drop (nb + kws.length))
  if bases.any (!isClass s ·) then throwM tErr else
  if bases.any (fun b => match b with
      | .bfun k => !(k == "object" || isExcName k)
      | _ => false) then throwM (unsup "subclass of a builtin type") else
  let bases' := if bases.isEmpty then [.bfun "object"] else bases
  let o := s.heap.size
  match c3 (bases'.map (mroOf s) ++ [bases']) [] with
  | none => throwM tErr
  | some mro =>
    let m := (nsv.lookup "__module__").getD (.str "builtins")
    allocM (.cls x q m bases' (.obj o :: mro) (nsv.filter (·.1 != "__qualname__")))

def mkExcM (e : Val) : M Val := do
  let s ← getS
  match e with
  | .exn .. => pure e
  | .err .. => pure e
  | .bfun k => if isExcName k then pure (.err k []) else throwM tErr
  | .obj o => match s.get o with
    | .cls .. =>
      if isExcClass s e then do
        let i ← callV e [] []
        pure i
      else throwM tErr
    | .inst c _ => if isExcClass s c then pure e else throwM tErr
    | _ => throwM tErr
  | _ => throwM tErr

def excMatchM (exc ty : Val) : M Val := do
  let s ← getS
  let tys := match ty with | .tuple ts => ts | t => [t]
  if tys.any (fun t => !isExcClass s t) then throwM tErr else
  pure (.bool (tys.any (isInstance s exc ·)))

def opM (o : Op) (vs : List Val) : M Val :=
  match vs.find? (fun v => match v with | .err "$Unsupported" _ => true | _ => false) with
  | some e => throwM e
  | none =>
  match o, vs with
  | .binop op, [a, b] => binopM op a b
  | .unop op, [a] => unopM op a
  | .truth, [a] => (Val.bool ·) <$> truthM a
  | .iter, [a] => iterM a
  | .next, [it] => do
    let r ← nextM it
    match r with
    | some v => pure v
    | none => throwM (.err "StopIteration" [])
  | .getattr a, [v] => getattrM v a
  | .setattr a, [v, x] => do setattrM v a x; pure .none
  | .delattr a, [v] => do delattrM v a; pure .none
  | .getitem, [v, i] => getitemM v i
  | .setitem, [v, i, x] => do setitemM v i x; pure .none
  | .delitem, [v, i] => do delitemM v i; pure .none
  | .call kws, f :: rest =>
    let n := rest.length - kws.length
    callV f (rest.take n) (kws.zip (rest.drop n))
  | .display (.list stars), vs => do let xs ← expand stars vs; allocM (.list xs.toArray)
  | .display (.tuple stars), vs => do let xs ← expand stars vs; pure (.tuple xs)
  | .display (.set stars), vs => do
    let xs ← expand stars vs
    let s ← getS
    let d ← liftE (mkSet s xs)
    allocM (.set d false)
  | .display .constSet, vs => do
    -- the compiler's frozenset, rebuilt from its own order when constants are merged, then
    -- merged into a new set (`BUILD_SET`, `SET_UPDATE`)
    let s ← getS
    let d ← liftE (mkSet s vs)
    let d ← liftE (mkSet s d.keys)
    allocM (.set d.copySet false)
  | .display (.dict stars), vs => dictDisplay stars vs
  | .display .slice, [a, b, c] => pure (.data "slice" [a, b, c])
  | .display .fstr, vs => do
    let ss ← vs.mapM fun v => match v with | .str x => pure x | _ => throwM tErr
    pure (.str (String.join ss))
  | .display (.kwargs ns), vs => kwargsDisplay ns vs
  | .accum .list, [acc, v] => match acc with
    | .obj p => do modM p (fun | .list zs => .list (zs.push v) | z => z); pure .none
    | _ => throwM tErr
  | .accum .set, [acc, v] => match acc with
    | .obj p => do
      let s ← getS
      let nk ← liftE (normKey s v)
      modM p (fun | .set d f => .set (d.insert nk v .none) f | z => z); pure .none
    | _ => throwM tErr
  | .accum .dict, [acc, k, v] => do setitemM acc k v; pure .none
  | .unpack b st a, [v] => unpackM b st a v
  | .convert c, [v] => match c with
    | 114 | 97 => (Val.str ·) <$> reprM v
    | _ => (Val.str ·) <$> strM v
  | .format, [v] => (Val.str ·) <$> formatM v ""
  | .format, [v, .str sp] => (Val.str ·) <$> formatM v sp
  | .mkClass x q kws ns, vs => mkClassM x q kws ns vs
  | .mkExc, [e] => mkExcM e
  | .excMatch, [e, t] => excMatchM e t
  | .import m leaf, [] => match moduleNames m with
    | some _ => pure (.bfun ("module:" ++ m))
    | none =>
      -- a standard module this interpretation lacks: importing it is fine, using it is not covered
      let _ := leaf
      if opaqueModules.contains m then pure (.bfun ("module:" ++ m)) else throwM (unsup ("module " ++ m))
  | .importFrom x, [m] => do
    let s0 ← getS
    match (getattrM m x).run s0 with
    | .ok s1 v => do setS s1; pure v
    | .raise _ (.err "AttributeError" _) => throwM (.err "ImportError" [])
    | _ => getattrM m x
  | .importStar, [m] => match m with
    | .bfun k => match moduleNames (k.drop 7).toString with
      | some ns => pure (.tuple (ns.filterMap fun n =>
          (moduleAttr (k.drop 7).toString n).map fun v => .tuple [.str n, v]))
      | none => throwM (unsup "import *")
    | _ => throwM tErr
  | _, _ => throwM tErr

/-- The builtins' namespace. -/
def builtinNames : List String :=
  ["print", "input", "len", "range", "int", "float", "str", "repr", "ascii", "bool", "list", "tuple", "set",
   "frozenset", "dict", "enumerate", "zip", "map", "filter", "iter", "next", "reversed", "sorted", "sum",
   "max", "min", "abs", "round", "divmod", "pow", "ord", "chr", "hex", "oct", "bin", "isinstance",
   "issubclass", "type", "callable", "all", "any", "hash", "format", "exit", "quit", "getattr", "hasattr",
   "setattr", "object", "id", "vars", "locals", "globals", "eval", "exec", "open", "super", "dir",
   "staticmethod", "classmethod", "property"]

def builtin (x : Name) : Option Val :=
  if builtinNames.contains x || (isExcName x && x != "$Unsupported") then some (.bfun x)
  else match x with
    | "__name__" => some (.str "builtins")
    | "NotImplemented" => some (.bfun "NotImplemented")
    | "Ellipsis" => some (.bfun "Ellipsis")
    | _ => none

def interp : Interp St where
  const := constOf
  builtin := builtin
  op := fun s o vs => (opM o vs).run s

/-! ## For the harness: values in and out -/

/-- The canonical text of a value for comparing outcomes: `repr`, with a set's
elements sorted. -/
partial def canon (s : St) (v : Val) : String :=
  match v.base with
  | .tuple [x] => "(" ++ canon s x ++ ",)"
  | .tuple xs => "(" ++ ", ".intercalate (xs.map (canon s)) ++ ")"
  | .obj o => match s.get o with
    | .list xs => "[" ++ ", ".intercalate (xs.toList.map (canon s)) ++ "]"
    | .dict d .plain => "{" ++ ", ".intercalate (d.items.map fun (a, b) => canon s a ++ ": " ++ canon s b) ++ "}"
    | .set d _ => if d.size == 0 then "set()" else
      "{" ++ ", ".intercalate ((d.keys.map (canon s)).mergeSort (fun a b => decide (a ≤ b))) ++ "}"
    | _ => (reprN s v).getD "<object>"
  | _ => (reprN s v).getD "<object>"

/-- The class name of an exception. -/
def excName (s : St) (v : Val) : String :=
  match v.base with
  | .err k _ => k
  | .obj o => match s.get o with
    | .inst (.obj c) _ => match s.get c with | .cls n .. => n | _ => "?"
    | _ => "?"
  | _ => "?"

end Ref
