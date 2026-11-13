/-
`pycore run`: run Surf programs on test inputs with the reference
interpretation, as the test harness (`src/runner/_child.py`) runs them, and print
each test's outcome as one JSON line. Input, one or more jobs:

  job   := (job MODE FUEL (prelude PROG?) PROG (tests test*))
  MODE  := stdio | call
  test  := (stdin "text") | (call "entry" (val*)) | (skip)
  val   := (int "n") | (float "bits") | (str "s") | (none) | (bool 0|1)
         | (list val*) | (tuple val*) | (set val*) | (dict (val val)*)

`stdio`: every test runs the program on a fresh module dictionary
`{__name__: '__main__'}` with the test's standard input; its outcome is the output
and the uncaught exception's class (`SystemExit` ends normally). `call`: the
prelude and the program run once on an empty module dictionary; then each test
calls the entry with its arguments on the state the earlier tests left, and its
outcome is the returned value (`Ref.canon`), the output, or the exception's class.
FUEL bounds the steps of each run. `(skip)` reports a test as not run (a test CPython did not
finish); in `call` mode the tests after it are not run either.
-/
import Surf.Semantics
import Surf.Ref
import Surf.Cli

namespace Surf.Run
open PyCore.Cli (Sx tokenize parseSx)
open Py (Val)

abbrev C := Surf.Sem.Config Ref.St

def jsonStr (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      let d := Nat.toDigits 16 c.toNat
      "\\u" ++ String.ofList (List.replicate (4 - d.length) '0' ++ d)
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- Why a run stopped. -/
inductive Stop where
  | done
  | fuel
  | depth

/-- Step until the run ends, the fuel is spent, or the stack is deeper than CPython's
recursion limit allows (checked every 1024 steps). -/
def drive (c : C) : Nat → C × Stop
  | 0 => (c, .fuel)
  | fuel + 1 =>
    if fuel % 1024 == 0 && c.stack.length > 19900 then (c, .depth) else
    match Surf.Sem.step Ref.interp c with
    | some c' => drive c' fuel
    | none => (c, .done)

/-- The reason the reference interpretation gave up, if it did. -/
def unsupOf (v : Val) : Option String :=
  match v.base with
  | .err "$Unsupported" [.str m] => some m
  | _ => none

mutual
partial def allocVal (s : Ref.St) : Sx → Except String (Ref.St × Val)
  | .list [.atom "int", .atom n] => match n.toInt? with
    | some i => .ok (s, .int i)
    | none => .error "bad int"
  | .list [.atom "float", .atom b] => match b.toNat? with
    | some i => .ok (s, .float i.toUInt64)
    | none => .error "bad float"
  | .list [.atom "str", .atom x] => .ok (s, .str x)
  | .list [.atom "none"] => .ok (s, .none)
  | .list [.atom "bool", .atom b] => .ok (s, .bool (b == "1"))
  | .list (.atom "list" :: xs) => do
    let (s, vs) ← allocVals s xs
    let (s, v) := s.alloc (.list vs.toArray)
    .ok (s, v)
  | .list (.atom "tuple" :: xs) => do
    let (s, vs) ← allocVals s xs
    .ok (s, .tuple vs)
  | .list (.atom "set" :: xs) => do
    let (s, vs) ← allocVals s xs
    match Ref.mkSet s vs with
    | .ok d => .ok (s.alloc (.set d false))
    | .error _ => .error "unhashable"
  | .list (.atom "dict" :: kvs) => do
    let (s, ps) ← kvs.foldlM (fun (acc : Ref.St × List (Val × Val)) kv => match kv with
      | .list [k, v] => do
        let (s, a) ← allocVal acc.1 k
        let (s, b) ← allocVal s v
        .ok (s, acc.2 ++ [(a, b)])
      | _ => .error "bad dict item") (s, [])
    match Ref.mkDict s ps with
    | .ok d => .ok (s.alloc (.dict d .plain))
    | .error _ => .error "unhashable"
  | _ => .error "bad value"
partial def allocVals (s : Ref.St) : List Sx → Except String (Ref.St × List Val)
  | [] => .ok (s, [])
  | x :: xs => do
    let (s, v) ← allocVal s x
    let (s, vs) ← allocVals s xs
    .ok (s, v :: vs)
end

/-- One test's outcome as JSON. -/
def report (i : Nat) (st : String) (out : String) (extra : List (String × String)) : String :=
  "{\"i\": " ++ toString i ++ ", \"st\": " ++ jsonStr st ++ ", \"out\": " ++ jsonStr out ++
    String.join (extra.map fun (k, v) => ", " ++ jsonStr k ++ ": " ++ jsonStr v) ++ "}"

def stdinOf (x : String) : List Char := x.toList

/-- The outcome of an ended module run. -/
def modOutcome (c : C) (stop : Stop) : String × List (String × String) :=
  match stop with
  | .fuel => ("fuel", [])
  | .depth => ("depth", [])
  | .done => match c.st.unsup with
    | some m => ("unsup", [("why", m)])
    | none => match c.stack, c.res with
      | [], some (.ok ()) => ("ok", [])
      | [], some (.error v) => match unsupOf v with
        | some m => ("unsup", [("why", m)])
        | none => ("exc", [("exc", Ref.excName c.st v)])
      | _, _ => ("stuck", [])

def runJob (sx : Sx) : Except String (List String) := do
  match sx with
  | .list [.atom "job", .atom mode, .atom fuel, .list pre, prog, .list (.atom "tests" :: tests)] =>
    let fuel := fuel.toNat!
    let prelude ← match pre with
      | [.atom "prelude"] => pure none
      | [.atom "prelude", p] => some <$> Surf.Cli.program p
      | _ => throw "bad prelude"
    let p ← Surf.Cli.program prog
    if mode == "stdio" then
      let mut lines := #[]
      let mut i := 0
      for t in tests do
        match t with
        | .list [.atom "stdin", .atom x] =>
          let g : Std.HashMap Py.Name Val := ({} : Std.HashMap Py.Name Val).insert "__name__" (.str "__main__")
          let c := Surf.Sem.init p g { inp := stdinOf x }
          let (c, stop) := drive c fuel
          let (st, extra) := modOutcome c stop
          let (st, extra) := if st == "exc" && extra == [("exc", "SystemExit")] then ("ok", []) else (st, extra)
          lines := lines.push (report i st c.st.output extra)
        | .list [.atom "skip"] => lines := lines.push (report i "skip" "" [])
        | _ => throw "bad stdio test"
        i := i + 1
      return lines.toList
    else
      -- call mode: the prelude and the program once, then the tests on the state left
      let c0 := Surf.Sem.init (prelude.getD []) {} {}
      let (c, stop) := drive c0 fuel
      let (st, extra) := modOutcome c stop
      if st != "ok" then return [report 0 ("module-" ++ st) c.st.output extra] else
      let c := Surf.Sem.Config.load c p
      let (c, stop) := drive c fuel
      let (st, extra) := modOutcome c stop
      if st != "ok" then return [report 0 ("module-" ++ st) c.st.output extra] else
      let mut c := c
      let mut lines := #[]
      let mut i := 0
      let mut dead := false
      for t in tests do
        if dead then
          lines := lines.push (report i "after-fuel" "" [])
        else
        match t with
        | .list [.atom "call", .atom entry, .list args] =>
          match c.glob[entry]? with
          | none => lines := lines.push (report i "noentry" "" [])
          | some f =>
            let st0 : Ref.St := { c.st with out := [] }
            match allocVals st0 args with
            | .error e => throw e
            | .ok (s, vs) =>
              let fr : Surf.Sem.Frame Ref.St := { (Surf.Sem.modFrame [] : Surf.Sem.Frame Ref.St) with ctrl := .call f vs [], kont := [] }
              let c1 : C := { c with stack := [fr], st := s, res := none }
              let (c2, stop) := drive c1 fuel
              let out := c2.st.output
              match stop with
              | .fuel => lines := lines.push (report i "fuel" out []); dead := true
              | .depth => lines := lines.push (report i "depth" out []); dead := true
              | .done =>
                match c2.st.unsup with
                | some m => lines := lines.push (report i "unsup" out [("why", m)]); dead := true
                | none =>
                match c2.stack, c2.res with
                | [g], _ => match g.ctrl with
                  | .val v => lines := lines.push (report i "ok" out [("val", Ref.canon c2.st v)])
                  | _ => lines := lines.push (report i "stuck" out []); dead := true
                | [], some (.error v) => match unsupOf v with
                  | some m => lines := lines.push (report i "unsup" out [("why", m)]); dead := true
                  | none => lines := lines.push (report i "exc" out [("exc", Ref.excName c2.st v)])
                | _, _ => lines := lines.push (report i "stuck" out []); dead := true
              c := { c2 with stack := [], res := none }
        | .list [.atom "skip"] => lines := lines.push (report i "skip" "" []); dead := true
        | _ => throw "bad call test"
        i := i + 1
      return lines.toList
  | _ => throw "bad job"

/-- Run a Surf program (an s-expression) as a script on `stdin`: its output, then
`!` and the class of an uncaught exception (`SystemExit` ends normally), or why the
run was not covered. For `#guard` tests. -/
def runSrc (src : String) (stdin : String) (fuel : Nat := 2000000) : String :=
  match tokenize src.toList >>= parseSx with
  | .error e => "!parse " ++ e
  | .ok (sx, _) => match Surf.Cli.program sx with
    | .error e => "!parse " ++ e
    | .ok p =>
      let g : Std.HashMap Py.Name Val := ({} : Std.HashMap Py.Name Val).insert "__name__" (.str "__main__")
      let (c, stop) := drive (Surf.Sem.init p g { inp := stdin.toList }) fuel
      let (st, extra) := modOutcome c stop
      c.st.output ++ match st, extra with
        | "ok", _ => ""
        | "exc", [("exc", "SystemExit")] => ""
        | "exc", [("exc", k)] => "!" ++ k
        | "unsup", [("why", m)] => "!$Unsupported " ++ m
        | st, _ => "!" ++ st

/-- Every job of the input, each reported between `job` and `end`. -/
partial def runAll (input : String) : Except String (List String) := do
  let rec go (ts : List String) (acc : Array String) : Except String (Array String) :=
    if ts.isEmpty then .ok acc else
    match parseSx ts with
    | .error e => .error e
    | .ok (sx, rest) =>
      let lines := match runJob sx with
        | .ok ls => ls
        | .error e => ["{\"error\": " ++ jsonStr e ++ "}"]
      go rest ((acc.push "job" ++ lines.toArray).push "end")
  return (← go (← tokenize input.toList) #[]).toList

end Surf.Run
