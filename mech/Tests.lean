/-
Runs of the executable semantics on the paper's witnesses (Proposition 6) and
on an edit the footprint clears; `lake build Tests` fails if a check fails.
-/
import PyCore
import PyCore.Cli
open PyCore

/-- A toy interpretation given by pure functions. Its state holds the iterators it
made (`obj i` is the `i`-th, the items it has left); `items v` lists what `iter v`
iterates; a class is `class C`. -/
structure Toy where
  const : String → Val
  binop : String → Val → Val → Except Val Val
  truthy : Val → Bool
  builtin : Name → Option Val
  callB : String → Val → Except Val Val
  isInst : Val → Val → Bool
  items : Val → Option (List Val) := fun _ => none

def Toy.res (s : List (List Val)) : Except Val Val → Py.Res (List (List Val))
  | .ok v => .ok s v
  | .error e => .raise s e

def Toy.interp (T : Toy) : Py.Interp (List (List Val)) where
  const := T.const
  builtin := T.builtin
  op s o vs := match o, vs with
    | .binop op, [a, b] => Toy.res s (T.binop op a b)
    | .truth, [v] => .ok s (.bool (T.truthy v))
    | .call [], [.bfun k, v] => Toy.res s (T.callB k v)
    | .excMatch, [e, c] => .ok s (.bool (T.isInst e.base c))
    | .mkExc, [e] => .ok s e
    | .iter, [v] => match T.items v with
      | some xs => .ok (s ++ [xs]) (.obj s.length)
      | none => .raise s errType
    | .next, [.obj i] => match s[i]? with
      | some (x :: r) => .ok (s.set i r) x
      | some [] => .raise s (Py.stopOf .none)
      | none => .raise s errType
    | .mkClass x _ _ _, _ => .ok s (.prim ("class " ++ x))
    | _, _ => .raise s errType

def testT : Toy where
  const c := if c = "None" then .none else .prim c
  binop op a b := if op = "==" then .ok (.prim (if a == b then "True" else "False")) else .ok (.prim "?")
  truthy v := match v with
    | .prim "False" | .prim "0" | .none => false
    | _ => true
  builtin x := if x = "Exception" then some (.prim "Exception")
    else if x = "next" then some .next
    else if x = "StopIteration" then some (.bfun "StopIteration") else none
  callB k v := if k = "StopIteration" then .ok (Py.stopOf v) else .ok v
  isInst _ _ := true

def testI := testT.interp

/-- A module dictionary has `__name__`, as CPython's `__main__` does. -/
def main0 : Name → Option Val := fun x => if x = "__name__" then some (.prim "'__main__'") else none

def summary (c : Config (List (List Val))) : String :=
  match outcome c with
  | .normal out _ _ => s!"normal {repr out}"
  | .exc v out _ => s!"exc {repr v} {repr out}"
  | .stuck out _ => s!"stuck {repr out}"

/-- The first step, up to `n`, whose node is in the footprint. -/
def firstReach (R : Edit) (p : List Stmt) (σ : Name → Option Val) (n : Nat) : Option (Nat × Label) :=
  (List.range n).findSome? fun k =>
    match focus (run testI k (init p σ [])) with
    | some l =>
      let inF := match footprint? R p with
        | some L => L.contains l
        | none => (labelsB p).contains l
      if inF then some (k, l) else none
    | none => none

def check (src : String) (σ : Name → Option Val) : String × String × Option (Nat × Label) :=
  match Cli.parsePair src with
  | .ok (p, R) =>
    (summary (run testI 1000 (init p σ [])), summary (run testI 1000 (init (editB R p) σ [])),
     firstReach R p σ 1000)
  | .error e => (e, e, none)

def witness2 := "(pair (module (assign 1 out (const 2 5))
  (def 3 f c ((if 4 (name 5 c) ((expr 6 (bin 7 == (name 8 out) (const 9 \"[]\")))) ())
    (return 10 (name 11 out UnboundLocalError))))
  (print 12 (call 13 (name 14 f) (name 15 inp))))
 (sites (stmts 6 ((assign 6 out (const 9 \"[]\"))))))"

def witness3 := "(pair (module
  (def 1 g x ((if 2 (const 3 False) ((expr 4 (const 5 None))) ()) (return 6 (const 7 1))))
  (print 8 (call 9 (name 10 g) (const 11 None))))
 (sites (stmts 4 ((expr 4 (yield 5 (const 12 0)))))))"

/-- An edit in a branch the input does not take, with a closure and a loop. -/
def cleared := "(pair (module
  (assign 1 n (const 2 3))
  (def 3 mk a ((return 4 (lambda 5 b ((return 40 (bin 6 + (name 7 a) (name 8 b))))))))
  (assign 9 add (call 10 (name 11 mk) (const 12 1)))
  (while 13 (name 14 n) ((print 15 (call 16 (name 17 add) (name 18 n))) (assign 19 n (const 20 0))))
  (if 21 (name 22 flag) ((print 23 (const 24 a))) ((print 25 (const 26 b)))))
 (sites (stmts 23 ((assign 23 n (const 27 9)) (print 28 (name 29 n))))))"

def inp (v : String) : Name → Option Val := fun x => if x = "inp" then some (.prim v) else main0 x
def flag (v : String) : Name → Option Val := fun x => if x = "flag" then some (.prim v) else main0 x

-- part (2): p prints 5 on input 0, q raises; p reaches the footprint at `return out` (11)
#guard check witness2 (inp "0") ==
  ("normal [Py.Val.prim \"5\"]", "exc Py.Val.err \"UnboundLocalError\" [] []", some (20, 11))
-- on input 1, p reaches the site itself (6)
#guard (check witness2 (inp "1")).2.2 == some (18, 6)
-- part (3): F is all of p, reached at the first step
#guard (check witness3 (fun _ => none)).1 == "normal [Py.Val.prim \"1\"]"
#guard (check witness3 (fun _ => none)).2.2 == some (0, 1)
-- footprint cleared: p never reaches it, and q has the same outcome
#guard check cleared (flag "False") ==
  ("normal [Py.Val.prim \"?\", Py.Val.prim \"b\"]",
   "normal [Py.Val.prim \"?\", Py.Val.prim \"b\"]", none)
-- on the other input p reaches the site (23) and the outputs differ
#guard check cleared (flag "True") ==
  ("normal [Py.Val.prim \"?\", Py.Val.prim \"a\"]",
   "normal [Py.Val.prim \"?\", Py.Val.prim \"9\"]", some (58, 23))

/-- An exception caught by a handler that sets and then unsets its name; the edit is
in the handler, which only runs when `y` is unset. -/
def handled := "(pair (module
  (try 1 ((print 2 (name 3 y))) 4 (name 5 Exception) e ((print 6 (name 7 e))))
  (print 8 (name 9 e)))
 (sites (stmts 6 ((print 6 (const 10 changed))))))"

def yv (v : String) : Name → Option Val := fun x => if x = "y" then some (.prim v) else main0 x

-- y unset: the handler runs (prints the NameError), then `e` is unset again
#guard (check handled (fun _ => none)).1 ==
  "exc Py.Val.err \"NameError\" [] [Py.Val.err \"NameError\" []]"
#guard (check handled (fun _ => none)).2.2 == some (10, 6)
-- y set: the handler never runs, the footprint is not reached, the outcomes agree
#guard check handled (yv "1") ==
  ("exc Py.Val.err \"NameError\" [] [Py.Val.prim \"1\"]",
   "exc Py.Val.err \"NameError\" [] [Py.Val.prim \"1\"]", none)

/-- A generator driven by `next` until its `return` raises StopIteration; the edit is
in a branch the generator does not take when `flag` is false. -/
def generator := "(pair (module
  (def 1 gen n ((expr 2 (yield 3 (name 4 n)))
                (if 5 (name 6 flag) ((expr 7 (yield 8 (const 9 0)))) ())
                (return 10 (const 11 7))))
  (assign 12 it (call 13 (name 14 gen) (const 15 1)))
  (print 16 (call 17 (name 18 next) (name 19 it)))
  (try 20 ((print 21 (call 22 (name 23 next) (name 24 it)))) 25 (name 26 Exception) e
    ((print 27 (name 28 e)))))
 (sites (stmts 7 ((print 7 (const 29 99))))))"

-- part (3): q's g is a generator, so q prints the generator object (step counts below
-- count the truth tests and operations the interpretation performs as steps of their own)
#guard (check witness3 (fun _ => none)).2.1 == "normal [Py.Val.gen 2]"
-- flag false: 1, then StopIteration(7) caught and printed; q agrees; F not reached
#guard check generator (flag "False") ==
  ("normal [Py.Val.prim \"1\", Py.Val.err \"StopIteration\" [Py.Val.prim \"7\"]]",
   "normal [Py.Val.prim \"1\", Py.Val.err \"StopIteration\" [Py.Val.prim \"7\"]]", none)
-- flag true: the generator reaches the site (7)
#guard (check generator (flag "True")).2.2.map (·.2) == some 7

/-- A class body is no function scope: `m` reads `f`'s `x`, the body its own. The edit
replaces a statement of the class body that runs only when `flag` is true. -/
def classes := "(pair (module
  (def 1 f u
    ((assign 2 x (const 3 fx))
     (class 4 C
       ((assign 5 x (const 6 cx))
        (def 7 m w ((return 8 (name 9 x))))
        (print 10 (call 11 (name 12 m) (const 13 0)))
        (print 14 (name 15 x))
        (if 16 (name 17 flag) ((print 18 (const 19 dead))) ())))
     (return 20 (name 21 C))))
  (print 22 (call 23 (name 24 f) (const 25 0))))
 (sites (stmts 18 ((assign 18 x (const 26 changed))))))"

#guard check classes (flag "False") ==
  ("normal [Py.Val.prim \"fx\", Py.Val.prim \"cx\", Py.Val.prim \"class C\"]",
   "normal [Py.Val.prim \"fx\", Py.Val.prim \"cx\", Py.Val.prim \"class C\"]", none)
#guard (check classes (flag "True")).2.2.map (·.2) == some 18

/-- The output of a program that ends normally on the empty input. -/
def outOf (src : String) : Option (List Val) :=
  match (do let (sx, _) ← Cli.parseSx (← Cli.tokenize src.toList); Cli.program sx) with
  | .ok p => match outcome (run testI 1000 (init p main0 [])) with
    | .normal out _ _ => some out
    | _ => none
  | .error _ => none

/-- Exception context as in CPython: an exception raised while a handler runs takes
the handled exception, also when a nested `try` inside the handler catches it, also
when a callee raises it; a generator keeps its own handled exception across
suspension, and a suspended one does not leak into its caller. -/
def contexts := "(module
  (try 1 ((raise 2 (const 3 A))) 4 (name 5 Exception) a
    ((try 6 ((raise 7 (const 8 B))) 9 (name 10 Exception) b ((print 11 (name 12 b))))))
  (def 13 g u
    ((try 14 ((raise 15 (const 16 A))) 17 (name 18 Exception) a
       ((expr 19 (yield 20 (const 21 1))) (raise 22 (const 23 C))))))
  (assign 24 it (call 25 (name 26 g) (const 27 None)))
  (try 28 ((raise 29 (const 30 B))) 31 (name 32 Exception) b
    ((expr 33 (call 34 (name 35 next) (name 36 it)))
     (try 37 ((raise 38 (const 39 D))) 40 (name 41 Exception) d ((print 42 (name 43 d))))))
  (try 44 ((expr 45 (call 46 (name 47 next) (name 48 it)))) 49 (name 50 Exception) c
    ((print 51 (name 52 c))))
  (def 53 f u ((raise 54 (const 55 D))))
  (try 56 ((raise 57 (const 58 A))) 59 (name 60 Exception) a
    ((try 61 ((expr 62 (call 63 (name 64 f) (const 65 None)))) 66 (name 67 Exception) d
       ((print 68 (name 69 d)))))))"

-- CPython 3.13: B's context is A, D's is B, C's is A (whose own is B), D's is A
#guard outOf contexts == some [.exn (.prim "B") (.prim "A") .none, .exn (.prim "D") (.prim "B") .none,
  .exn (.prim "C") (.exn (.prim "A") (.prim "B") .none) .none, .exn (.prim "D") (.prim "A") .none]

/-- A StopIteration raised while a handler runs in a generator still leaves it as
RuntimeError, whose cause and context are that StopIteration (with context A). -/
def stopInHandler := "(module
  (def 1 g u
    ((try 2 ((raise 3 (const 4 A))) 5 (name 6 Exception) a
       ((raise 7 (call 8 (name 9 StopIteration) (const 10 None)))))
     (expr 11 (yield 12 (const 13 1)))))
  (try 14 ((expr 15 (call 16 (name 17 next) (call 18 (name 19 g) (const 20 None)))))
    21 (name 22 Exception) r ((print 23 (name 24 r)))))"

-- CPython 3.13: RuntimeError, __cause__ is __context__ is StopIteration(None), whose context is A()
#guard outOf stopInHandler ==
  some [.exn errRuntime (.exn (Py.stopOf .none) (.prim "A") .none) (.exn (Py.stopOf .none) (.prim "A") .none)]

/-- Read and `del` errors: an unset local cell raises UnboundLocalError, a failed
global lookup NameError, an annotated read its own class on every failing path, a
`del` of an unset class-local NameError; a class body starts with `__module__` and
`__qualname__`. -/
def lookups := "(module
  (def 1 f u
    ((try 2 ((print 3 (name 4 y))) 5 (name 6 Exception) e ((print 7 (name 8 e))))
     (assign 9 y (const 10 1))))
  (expr 11 (call 12 (name 13 f) (const 14 None)))
  (try 15 ((print 16 (name 17 zz))) 18 (name 19 Exception) e ((print 20 (name 21 e))))
  (try 22 ((print 23 (name 24 zz Custom))) 25 (name 26 Exception) e ((print 27 (name 28 e))))
  (class 29 C
    ((try 30 ((del 31 qq)) 32 (name 33 Exception) e ((print 34 (name 35 e))))
     (assign 36 qq (const 37 1))
     (print 38 (name 39 __module__))
     (print 40 (name 41 __qualname__)))))"

-- CPython 3.13: UnboundLocalError, NameError, (the override), NameError, '__main__', 'C'
#guard outOf lookups == some [errUnbound, errName, Py.err "Custom", errName, .prim "'__main__'",
  .prim "'C'"]


/-! The constructs added for Lemma A.3: conditional expressions, a lambda with
a block body, `break`, `continue`, `while … else`, and `try` with several handlers
and `else`. Each program's output is CPython 3.13's for the Python program in its
comment. -/

/-- Numerals with `+` and `<`, and exception classes matched by name (`Exception`
matches all). -/
def numT : Toy where
  const c := if c = "None" then .none else .prim c
  binop op a b := match op, a, b with
    | "==", a, b => .ok (.prim (if a == b then "True" else "False"))
    | "+", .prim x, .prim y => match x.toNat?, y.toNat? with
      | some m, some n => .ok (.prim (toString (m + n)))
      | _, _ => .error errType
    | "<", .prim x, .prim y => match x.toNat?, y.toNat? with
      | some m, some n => .ok (.prim (if m < n then "True" else "False"))
      | _, _ => .error errType
    | _, _, _ => .error errType
  truthy v := match v with
    | .prim "False" | .prim "0" | .none => false
    | _ => true
  builtin x := if x = "next" then some .next
    else if x ∈ ["Exception", "ValueError", "TypeError", "NameError"] then some (.prim x) else none
  callB _ v := .ok v
  isInst e c := c == .prim "Exception" || e == c || match e with
    | .err k _ => c == .prim k
    | _ => false
  -- a comma-separated list iterates over its items
  items v := match v with
    | .prim xs => some ((xs.splitOn ",").map .prim)
    | _ => none

def numI := numT.interp

/-- The output and, if any, the uncaught exception of a run that ends. -/
def runNum (src : String) : Option (List Val × Option Val) :=
  match (do let (sx, _) ← Cli.parseSx (← Cli.tokenize src.toList); Cli.program sx) with
  | .ok p => match outcome (run numI 2000 (init p main0 [])) with
    | .normal out _ _ => some (out, none)
    | .exc v out _ => some (out, some v)
    | .stuck _ _ => none
  | .error _ => none

def ps (xs : List String) : List Val := xs.map .prim

-- def f(x): print(x); return x
-- print(f(0) and f(1)); print(f(0) or f(2)); print(f(3) if f(0) else f(4))
def condExprs := "(module
  (def 1 f x ((print 2 (name 3 x)) (return 4 (name 5 x))))
  (print 6 (and 7 (call 8 (name 9 f) (const 10 0)) (call 11 (name 12 f) (const 13 1))))
  (print 14 (or 15 (call 16 (name 17 f) (const 18 0)) (call 19 (name 20 f) (const 21 2))))
  (print 22 (ifexp 23 (call 24 (name 25 f) (const 26 0)) (call 27 (name 28 f) (const 29 3))
    (call 30 (name 31 f) (const 32 4)))))"

-- CPython 3.13: 0 0 0 2 2 0 4 4
#guard runNum condExprs == some (ps ["0", "0", "0", "2", "2", "0", "4", "4"], none)

-- i = 0
-- while i < 5:
--     i = i + 1
--     if i == 2: continue
--     if i == 4: break
--     print(i)
-- else: print(99)
-- print(i)
-- j = 0
-- while j < 2: j = j + 1
-- else: print(100)
def loops := "(module
  (assign 1 i (const 2 0))
  (while 3 (bin 4 < (name 5 i) (const 6 5))
    ((assign 7 i (bin 8 + (name 9 i) (const 10 1)))
     (if 11 (bin 12 == (name 13 i) (const 14 2)) ((continue 15)) ())
     (if 16 (bin 17 == (name 18 i) (const 19 4)) ((break 20)) ())
     (print 21 (name 22 i)))
    ((print 23 (const 24 99))))
  (print 25 (name 26 i))
  (assign 27 j (const 28 0))
  (while 29 (bin 30 < (name 31 j) (const 32 2))
    ((assign 33 j (bin 34 + (name 35 j) (const 36 1))))
    ((print 37 (const 38 100)))))"

-- CPython 3.13: 1 3 4 100
#guard runNum loops == some (ps ["1", "3", "4", "100"], none)

-- while True:
--     try: raise Exception
--     except Exception as e: break
-- try: print(e)
-- except NameError as n: print("unset")
def breakInHandler := "(module
  (while 1 (const 2 True)
    ((try 3 ((raise 4 (name 5 Exception))) 6 (name 7 Exception) e ((break 8)))))
  (try 9 ((print 10 (name 11 e))) 12 (name 13 NameError) n ((print 14 (const 15 unset)))))"

-- CPython 3.13: unset (a `break` out of a handler unsets its name)
#guard runNum breakInHandler == some (ps ["unset"], none)

-- def g(x):
--     try:
--         if x: raise ValueError
--     except TypeError as t: print("T")
--     except ValueError as v: print("V")
--     else: print("else")
-- g(True); g(False)
-- try: raise ValueError
-- except ValueError as v: print("first")
-- except Undefined as u: print("never")
def handlers := "(module
  (def 1 g x
    ((try 2 ((if 3 (name 4 x) ((raise 5 (name 6 ValueError))) ()))
       ((handler 7 (name 8 TypeError) t ((print 9 (const 10 T))))
        (handler 11 (name 12 ValueError) v ((print 13 (const 14 V)))))
       ((print 15 (const 16 else))))))
  (expr 17 (call 18 (name 19 g) (const 20 True)))
  (expr 21 (call 22 (name 23 g) (const 24 False)))
  (try 25 ((raise 26 (name 27 ValueError)))
    ((handler 28 (name 29 ValueError) v ((print 30 (const 31 first))))
     (handler 32 (name 33 Undefined) u ((print 34 (const 35 never)))))
    ()))"

-- CPython 3.13: V else first (the second handler's expression is never evaluated)
#guard runNum handlers == some (ps ["V", "else", "first"], none)

-- h = (lambda x: (yield x)); it = h(5); print(next(it))
-- try: pass
-- except ValueError as v: print("h")
-- else: raise ValueError
def lambdaElse := "(module
  (assign 1 h (lambda 2 x ((return 3 (yield 4 (name 5 x))))))
  (assign 6 it (call 7 (name 8 h) (const 9 5)))
  (print 10 (call 11 (name 12 next) (name 13 it)))
  (try 14 () ((handler 15 (name 16 ValueError) v ((print 17 (const 18 h)))))
    ((raise 19 (name 20 ValueError)))))"

-- CPython 3.13: 5, then ValueError raised in the else block, which the handler does not catch
#guard runNum lambdaElse == some (ps ["5"], some (.prim "ValueError"))

/-- An edit in the operand `and` skips: F is that operand, which p never reaches. -/
def shortCircuit := "(pair (module
  (assign 1 c (const 2 False))
  (print 3 (and 4 (name 5 c) (call 6 (name 7 f) (const 8 1)))))
 (sites (expr 6 (lambda 9 x ((return 10 (const 11 2)))))))"

#guard check shortCircuit (fun _ => none) ==
  ("normal [Py.Val.prim \"False\"]", "normal [Py.Val.prim \"False\"]", none)

/-- An edit in the `else` block of a loop that a `break` leaves. -/
def loopElse := "(pair (module
  (while 1 (const 2 True) ((break 3)) ((print 4 (const 5 else))))
  (print 6 (const 7 after)))
 (sites (stmts 4 ((print 4 (const 8 changed))))))"

#guard check loopElse (fun _ => none) ==
  ("normal [Py.Val.prim \"after\"]", "normal [Py.Val.prim \"after\"]", none)

/-! `yield from` (delegation through `next`), comprehension functions, and the
core's `$false`. -/

-- def inner(x): yield 1; yield 2; return 3
-- def outer(x): r = yield from inner(x); yield r
-- g = outer(None); print(next(g)) ×3; then StopIteration
-- def h(x): yield from x
-- it = h(["a", "b"]); print(next(it)) ×2; then StopIteration
-- def f(a): [y := i for i in [5]]; return y
-- print(f(None))
def yieldFrom := "(module
  (def 1 inner x ((expr 2 (yield 3 (const 4 1))) (expr 5 (yield 6 (const 7 2))) (return 8 (const 9 3))))
  (def 10 outer x ((assign 11 r (yieldfrom 12 (call 13 (name 14 inner) (name 15 x))))
                   (expr 16 (yield 17 (name 18 r)))))
  (assign 19 g (call 20 (name 21 outer) (const 22 None)))
  (print 23 (call 24 (name 25 next) (name 26 g)))
  (print 27 (call 28 (name 29 next) (name 30 g)))
  (print 31 (call 32 (name 33 next) (name 34 g)))
  (try 35 ((expr 36 (call 37 (name 38 next) (name 39 g)))) 40 (name 41 Exception) e
    ((print 42 (const 43 stop))))
  (def 44 h x ((expr 45 (yieldfrom 46 (name 47 x)))))
  (assign 48 it (call 49 (name 50 h) (const 51 \"a,b\")))
  (print 52 (call 53 (name 54 next) (name 55 it)))
  (print 56 (call 57 (name 58 next) (name 59 it)))
  (try 60 ((expr 61 (call 62 (name 63 next) (name 64 it)))) 65 (name 66 Exception) e
    ((print 67 (const 68 stop))))
  (def 69 f a ((expr 70 (call 71 (complambda 72 i ((expr 73 (walrus 74 y (name 75 i))))) (const 76 5)))
               (return 77 (name 78 y))))
  (print 79 (call 80 (name 81 f) (const 82 None))))"

-- CPython 3.13: 1 2 3 stop a b stop 5 (a comprehension's walrus target is f's local, set
-- through the comprehension function's free cell; a list here is iterated by `$next n`)
#guard runNum yieldFrom == some (ps ["1", "2", "3", "stop", "a", "b", "stop", "5"], none)

-- `$false` is false whatever the interpretation (here every other constant is true)
#guard runNum "(module (print 1 (ifexp 2 (const 3 $false) (const 4 dead) (const 5 live))))" ==
  some (ps ["live"], none)

-- a constant `$op:…` is an operation of the interface, whatever the interpretation:
-- calling it performs the operation (here `truth`, which the toy makes `bool false` of 0)
#guard runNum "(module (print 1 (call 2 (const 3 $op:truth) (const 4 0))))" ==
  some ([.bool false], none)
