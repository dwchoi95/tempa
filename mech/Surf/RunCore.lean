/-
`pycore runcore`: run each test of a job (as `pycore run` takes them) twice under the
reference interpretation with a trace, by Surf.Sem on the Surf program and by PyCore on
its translation ⌊p⌋ (`Surf.tr`), and compare. The trace is a hash of every operation
the interpretation is asked for (with its arguments, closures and generators by
address) and of every callback outcome it is handed; with the object counter at the
end, equal traces mean the same calls in the same order and the same allocations.
Each test's line gives Surf's outcome and `core`: `agree`, `mismatch` (with both
sides), or `nc` (Surf's run is not covered: fuel, depth, unsupported, or PyCore ran out
of its fuel, eight times Surf's).
-/
import Surf.Run
import Surf.Translate
import PyCore.Semantics

namespace Surf.RunCore
open PyCore.Cli (Sx tokenize parseSx)
open Py (Val Res)
open Surf.Run (jsonStr report stdinOf allocVals unsupOf)

/-- The reference interpretation's state with the trace so far. -/
abbrev TSt := Ref.St × UInt64

def hashR : Except Val Val → UInt64
  | .ok v => mixHash 1 (hash v)
  | .error e => mixHash 2 (hash e)

partial def wrapRes (h : UInt64) : Res Ref.St → Res TSt
  | .ok s v => .ok (s, h) v
  | .raise s e => .raise (s, h) e
  | .reraise s e => .reraise (s, h) e
  | .call s g args kws k =>
    .call (s, mixHash h (hash (g, args, kws))) g args kws fun st r =>
      match st with
      | (s', h') => wrapRes (mixHash h' (hashR r)) (k s' r)

def tInterp : Py.Interp TSt where
  const := Ref.interp.const
  builtin := Ref.interp.builtin
  op := fun st o vs => match st with
    | (s, h) => wrapRes (mixHash h (hash (o, vs))) (Ref.interp.op s o vs)

abbrev SC := Surf.Sem.Config TSt
abbrev PC := PyCore.Config TSt

inductive Stop where
  | done | fuel | depth
  deriving BEq

def driveS (c : SC) : Nat → SC × Stop
  | 0 => (c, .fuel)
  | fuel + 1 =>
    if fuel % 1024 == 0 && c.stack.length > 19900 then (c, .depth) else
    match Surf.Sem.step tInterp c with
    | some c' => driveS c' fuel
    | none => (c, .done)

def driveP (c : PC) : Nat → PC × Stop
  | 0 => (c, .fuel)
  | fuel + 1 =>
    if fuel % 1024 == 0 && c.stack.length > 19900 then (c, .depth) else
    match PyCore.step tInterp c with
    | some c' => driveP c' fuel
    | none => (c, .done)

/-- A side's outcome of one run: status, output, extra fields, trace, object counter. -/
structure Side where
  st : String
  out : String
  extra : List (String × String)
  trace : UInt64
  next : Nat
  deriving BEq

def Side.covered (s : Side) : Bool := !["fuel", "depth", "unsup"].contains s.st

def sideJson (s : Side) : String :=
  "{\"st\": " ++ jsonStr s.st ++ ", \"out\": " ++ jsonStr s.out ++
    String.join (s.extra.map fun (k, v) => ", " ++ jsonStr k ++ ": " ++ jsonStr v) ++
    ", \"trace\": \"" ++ toString s.trace ++ "\", \"next\": " ++ toString s.next ++ "}"

/-- An ended module run's outcome. -/
def modSide (st : TSt) (stack0 : Bool) (res : Option (Except Val Unit)) (next : Nat) (stop : Stop) : Side :=
  let mk (s : String) (ex : List (String × String)) : Side := ⟨s, st.1.output, ex, st.2, next⟩
  match stop with
  | .fuel => mk "fuel" []
  | .depth => mk "depth" []
  | .done => match st.1.unsup with
    | some m => mk "unsup" [("why", m)]
    | none => match stack0, res with
      | true, some (.ok ()) => mk "ok" []
      | true, some (.error v) => match unsupOf v with
        | some m => mk "unsup" [("why", m)]
        | none =>
          let k := Ref.excName st.1 v
          if k == "SystemExit" then mk "ok" [] else mk "exc" [("exc", k)]
      | _, _ => mk "stuck" []

def sSide (c : SC) (stop : Stop) : Side := modSide c.st c.stack.isEmpty c.res c.next stop
def pSide (c : PC) (stop : Stop) : Side := modSide c.st c.stack.isEmpty c.res c.next stop

/-- A call test's outcome: the returned value, or the exception. -/
def callSide (st : TSt) (top : Option Val) (stack0 : Bool) (res : Option (Except Val Unit)) (next : Nat)
    (stop : Stop) : Side :=
  let mk (s : String) (ex : List (String × String)) : Side := ⟨s, st.1.output, ex, st.2, next⟩
  match stop with
  | .fuel => mk "fuel" []
  | .depth => mk "depth" []
  | .done => match st.1.unsup with
    | some m => mk "unsup" [("why", m)]
    | none => match top, stack0, res with
      | some v, _, _ => mk "ok" [("val", Ref.canon st.1 v)]
      | none, true, some (.error v) => match unsupOf v with
        | some m => mk "unsup" [("why", m)]
        | none => mk "exc" [("exc", Ref.excName st.1 v)]
      | _, _, _ => mk "stuck" []

def line (i : Nat) (s p : Side) : String :=
  let verdict := if !s.covered || !p.covered then "nc" else if s == p then "agree" else "mismatch"
  "{\"i\": " ++ toString i ++ ", \"st\": " ++ jsonStr s.st ++ ", \"core\": " ++ jsonStr verdict ++
    (if verdict == "mismatch" then ", \"surf\": " ++ sideJson s ++ ", \"pycore\": " ++ sideJson p
     else if verdict == "nc" then ", \"why\": " ++ jsonStr (if s.covered then "pycore-" ++ p.st else s.st)
     else "") ++ "}"

def mainGlob : Std.HashMap Py.Name Val := ({} : Std.HashMap Py.Name Val).insert "__name__" (.str "__main__")

def runJob (sx : Sx) : Except String (List String) := do
  match sx with
  | .list [.atom "job", .atom mode, .atom fuel, .list pre, prog, .list (.atom "tests" :: tests)] =>
    let fuel := fuel.toNat!
    let pfuel := 8 * fuel
    let prelude ← match pre with
      | [.atom "prelude"] => pure []
      | [.atom "prelude", p] => Surf.Cli.program p
      | _ => throw "bad prelude"
    let p ← Surf.Cli.program prog
    let q := Surf.tr p
    if mode == "stdio" then
      let mut lines := #[]
      let mut i := 0
      for t in tests do
        match t with
        | .list [.atom "stdin", .atom x] =>
          let s0 : TSt := ({ inp := stdinOf x }, 0)
          let (cs, ss) := driveS (Surf.Sem.init p mainGlob s0) fuel
          let a := sSide cs ss
          -- a run Surf does not finish is not covered: PyCore's is not run
          if !a.covered then lines := lines.push (line i a a) else
          let (cp, sp) := driveP (PyCore.init q (fun y => mainGlob[y]?) s0) pfuel
          lines := lines.push (line i a (pSide cp sp))
        | .list [.atom "skip"] => lines := lines.push (report i "skip" "" [])
        | _ => throw "bad stdio test"
        i := i + 1
      return lines.toList
    else
      let s0 : TSt := ({}, 0)
      let (cs, ss) := driveS (Surf.Sem.init prelude {} s0) fuel
      let (cp, sp) := driveP (PyCore.init (Surf.tr prelude) (fun _ => none) s0) pfuel
      let (a, b) := (sSide cs ss, pSide cp sp)
      if a.st != "ok" || b.st != "ok" then return [line 0 { a with st := "module-" ++ a.st } { b with st := "module-" ++ b.st }] else
      let (cs, ss) := driveS (Surf.Sem.Config.load cs p) fuel
      let (cp, sp) := driveP { cp with stack := [PyCore.modFrame q], res := none } pfuel
      let (a, b) := (sSide cs ss, pSide cp sp)
      if a.st != "ok" || b.st != "ok" then return [line 0 { a with st := "module-" ++ a.st } { b with st := "module-" ++ b.st }] else
      let mut cs := cs
      let mut cp := cp
      let mut lines := #[]
      let mut i := 0
      let mut dead := false
      for t in tests do
        if dead then
          lines := lines.push (report i "after-fuel" "" [("core", "nc")])
        else
        match t with
        | .list [.atom "call", .atom entry, .list args] =>
          match cs.glob[entry]?, cp.glob entry with
          | some fS, some fP =>
            let stS : Ref.St := { cs.st.1 with out := [] }
            let stP : Ref.St := { cp.st.1 with out := [] }
            match allocVals stS args, allocVals stP args with
            | .ok (sS, vsS), .ok (sP, vsP) =>
              let frS : Surf.Sem.Frame TSt := { (Surf.Sem.modFrame [] : Surf.Sem.Frame TSt) with ctrl := .call fS vsS [], kont := [] }
              let frP : PyCore.Frame TSt := { (PyCore.modFrame [] : PyCore.Frame TSt) with ctrl := .call fP vsP [], kont := [] }
              let (cs2, ss) := driveS { cs with stack := [frS], st := (sS, cs.st.2), res := none } fuel
              let (cp2, sp) := if ss == .done then
                  driveP { cp with stack := [frP], st := (sP, cp.st.2), res := none } pfuel
                else (cp, ss)
              let topS := match cs2.stack with
                | [g] => match g.ctrl with | .val v => some v | _ => none
                | _ => none
              let topP := match cp2.stack with
                | [g] => match g.ctrl with | .val v => some v | _ => none
                | _ => none
              let a := callSide cs2.st topS cs2.stack.isEmpty cs2.res cs2.next ss
              let b := callSide cp2.st topP cp2.stack.isEmpty cp2.res cp2.next sp
              lines := lines.push (line i a b)
              if !a.covered || !b.covered || a.st == "stuck" || b.st == "stuck" then dead := true
              cs := { cs2 with stack := [], res := none }
              cp := { cp2 with stack := [], res := none }
            | _, _ => throw "bad args"
          | none, none => lines := lines.push (report i "noentry" "" [("core", "agree")])
          | _, _ => lines := lines.push (report i "noentry" "" [("core", "mismatch")])
        | .list [.atom "skip"] => lines := lines.push (report i "skip" "" []); dead := true
        | _ => throw "bad call test"
        i := i + 1
      return lines.toList
  | _ => throw "bad job"

/-- Profiling: run a script by one semantics only (`which` = "surf" or "pycore"). -/
def oneSrc (which : String) (src : String) (stdin : String) (fuel : Nat := 20000000) : String :=
  match tokenize src.toList >>= parseSx with
  | .error e => "!parse " ++ e
  | .ok (sx, _) => match Surf.Cli.program sx with
    | .error e => "!parse " ++ e
    | .ok p =>
      let s0 : TSt := ({ inp := stdin.toList }, 0)
      if which == "surf" then
        let (cs, ss) := driveS (Surf.Sem.init p mainGlob s0) fuel
        sideJson (sSide cs ss)
      else
        let (cp, sp) := driveP (PyCore.init (Surf.tr p) (fun y => mainGlob[y]?) s0) (8 * fuel)
        sideJson (pSide cp sp)

/-- Run a Surf program (an s-expression) as a script on `stdin` by both semantics, and
say whether they agree (on outcome, output, trace and object counter), for `#guard` tests. -/
def coreSrc (src : String) (stdin : String) (fuel : Nat := 2000000) : String :=
  match tokenize src.toList >>= parseSx with
  | .error e => "!parse " ++ e
  | .ok (sx, _) => match Surf.Cli.program sx with
    | .error e => "!parse " ++ e
    | .ok p =>
      let s0 : TSt := ({ inp := stdin.toList }, 0)
      let (cs, ss) := driveS (Surf.Sem.init p mainGlob s0) fuel
      let (cp, sp) := driveP (PyCore.init (Surf.tr p) (fun y => mainGlob[y]?) s0) (8 * fuel)
      let (a, b) := (sSide cs ss, pSide cp sp)
      if !a.covered then "nc " ++ a.st else if a == b then "agree" else
        "mismatch " ++ sideJson a ++ " " ++ sideJson b

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

end Surf.RunCore
