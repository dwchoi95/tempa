/-
Reading Surf programs as s-expressions (one constructor per node of CPython's
`ast`, as `export_surf.py` writes them), and printing the classification of every
occurrence and the kind of every function, computed on Surf directly and through
the translation. The format is documented in NOTES.md.
-/
import PyCore.Cli
import Surf.Translate

namespace Surf.Cli
open PyCore.Cli (Sx tokenize parseSx label name clsStr kindStr)
open Surf

def opt {α} (f : Sx → Except String α) : Sx → Except String (Option α)
  | .list [] => .ok none
  | s => some <$> f s

def list {α} (f : Sx → Except String α) : Sx → Except String (List α)
  | .list xs => xs.mapM f
  | _ => .error "expected a list"

def int (s : Sx) : Except String Int :=
  match s with
  | .atom a => match a.toInt? with
    | some n => .ok n
    | none => .error s!"expected an integer, got {a}"
  | _ => .error "expected an integer"

def pkind : String → Except String PKind
  | "posonly" => .ok .posonly | "pos" => .ok .pos | "vararg" => .ok .vararg
  | "kwonly" => .ok .kwonly | "kwarg" => .ok .kwarg
  | k => .error s!"bad parameter kind {k}"

mutual
partial def expr (s : Sx) : Except String Expr := do
  match s with
  | .list [.atom "Constant", l, c] => return .const (← label l) (← name c)
  | .list [.atom "Name", l, x] => return .name (← label l) (← name x)
  | .list [.atom "BinOp", l, op, a, b] => return .bin (← label l) (← name op) (← expr a) (← expr b)
  | .list [.atom "UnaryOp", l, op, a] => return .unary (← label l) (← name op) (← expr a)
  | .list [.atom "BoolOp", l, op, es] => return .boolop (← label l) (← name op) (← list expr es)
  | .list [.atom "Compare", l, a, ops, es] =>
    return .compare (← label l) (← expr a) (← list name ops) (← list expr es)
  | .list [.atom "IfExp", l, c, a, b] => return .ifexp (← label l) (← expr c) (← expr a) (← expr b)
  | .list [.atom "Call", l, f, args, kws] =>
    return .call (← label l) (← expr f) (← list expr args) (← list kw kws)
  | .list [.atom "Attribute", l, e, a] => return .attr (← label l) (← expr e) (← name a)
  | .list [.atom "Subscript", l, e, i] => return .sub (← label l) (← expr e) (← expr i)
  | .list [.atom "Slice", l, a, b, c] =>
    return .slice (← label l) (← opt expr a) (← opt expr b) (← opt expr c)
  | .list [.atom "Starred", l, e] => return .star (← label l) (← expr e)
  | .list [.atom "List", l, es] => return .list (← label l) (← list expr es)
  | .list [.atom "Tuple", l, es] => return .tuple (← label l) (← list expr es)
  | .list [.atom "Set", l, es] => return .set (← label l) (← list expr es)
  | .list [.atom "Dict", l, kvs] => return .dict (← label l) (← list ditem kvs)
  | .list [.atom "Lambda", l, ps, b] => return .lam (← label l) (← list param ps) (← expr b)
  | .list [.atom "DictComp", l, k, v, gs] =>
    return .comp (← label l) .dict [← expr k, ← expr v] (← list gen gs)
  | .list [.atom "ListComp", l, e, gs] => return .comp (← label l) .list [← expr e] (← list gen gs)
  | .list [.atom "SetComp", l, e, gs] => return .comp (← label l) .set [← expr e] (← list gen gs)
  | .list [.atom "GeneratorExp", l, e, gs] => return .comp (← label l) .gen [← expr e] (← list gen gs)
  | .list [.atom "NamedExpr", l, x, e] => return .walrus (← label l) (← name x) (← expr e)
  | .list [.atom "Yield", l, e] => return .yield (← label l) (← opt expr e)
  | .list [.atom "YieldFrom", l, e] => return .yieldFrom (← label l) (← expr e)
  | .list [.atom "JoinedStr", l, es] => return .fstr (← label l) (← list expr es)
  | .list [.atom "FormattedValue", l, e, c, sp] =>
    return .fmt (← label l) (← expr e) (← int c) (← opt expr sp)
  | .list (.atom c :: _) => throw s!"bad expression {c}"
  | _ => throw "bad expression"
partial def kw (s : Sx) : Except String Kw := do
  match s with
  | .list [.atom "keyword", l, x, e] => return .mk (← label l) (← opt name x) (← expr e)
  | _ => throw "bad keyword"
partial def ditem (s : Sx) : Except String DItem := do
  match s with
  | .list [k, v] => return .mk (← opt expr k) (← expr v)
  | _ => throw "bad dictionary item"
partial def param (s : Sx) : Except String Param := do
  match s with
  | .list [.atom "arg", l, x, .atom k, d, a] =>
    return .mk (← label l) (← name x) (← pkind k) (← opt expr d) (← opt expr a)
  | _ => throw "bad parameter"
partial def gen (s : Sx) : Except String Gen := do
  match s with
  | .list [.atom "comprehension", l, t, i, ifs] =>
    return .mk (← label l) (← expr t) (← expr i) (← list expr ifs)
  | _ => throw "bad generator"
end

def alias (s : Sx) : Except String Alias := do
  match s with
  | .list [.atom "alias", l, x, a] => return { l := ← label l, name := ← name x, asname := ← opt name a }
  | _ => throw "bad alias"

mutual
partial def stmt (s : Sx) : Except String Stmt := do
  match s with
  | .list [.atom "Expr", l, e] => return .expr (← label l) (← expr e)
  | .list [.atom "Assign", l, ts, e] => return .assign (← label l) (← list expr ts) (← expr e)
  | .list [.atom "AugAssign", l, t, op, e] =>
    return .augassign (← label l) (← expr t) (← name op) (← expr e)
  | .list [.atom "AnnAssign", l, t, a, v] =>
    return .annassign (← label l) (← expr t) (← expr a) (← opt expr v)
  | .list [.atom "Delete", l, ts] => return .del (← label l) (← list expr ts)
  | .list [.atom "If", l, c, t, u] => return .ite (← label l) (← expr c) (← block t) (← block u)
  | .list [.atom "While", l, c, b, u] =>
    return .while (← label l) (← expr c) (← block b) (← block u)
  | .list [.atom "For", l, t, it, b, u] =>
    return .for (← label l) (← expr t) (← expr it) (← block b) (← block u)
  | .list [.atom "Break", l] => return .brk (← label l)
  | .list [.atom "Continue", l] => return .cont (← label l)
  | .list [.atom "Pass", l] => return .pass (← label l)
  | .list [.atom "Return", l, e] => return .ret (← label l) (← opt expr e)
  | .list [.atom "FunctionDef", l, f, ps, b, ds, r] =>
    return .defn (← label l) (← name f) (← list param ps) (← block b) (← list expr ds) (← opt expr r)
  | .list [.atom "ClassDef", l, x, bs, ks, b, ds] =>
    return .cls (← label l) (← name x) (← list expr bs) (← list kw ks) (← block b) (← list expr ds)
  | .list [.atom "Global", l, xs] => return .glob (← label l) (← list name xs)
  | .list [.atom "Nonlocal", l, xs] => return .nonloc (← label l) (← list name xs)
  | .list [.atom "Try", l, b, hs, u] =>
    return .tryE (← label l) (← block b) (← list handler hs) (← block u)
  | .list [.atom "Raise", l, e, c] => return .raise (← label l) (← opt expr e) (← opt expr c)
  | .list [.atom "Import", l, al] => return .imp (← label l) (← list alias al)
  | .list [.atom "ImportFrom", l, m, al, .atom lvl] =>
    return .impFrom (← label l) (← opt name m) (← list alias al) lvl.toNat!
  | .list [.atom "Assert", l, t, m] => return .assert (← label l) (← expr t) (← opt expr m)
  | .list (.atom c :: _) => throw s!"bad statement {c}"
  | _ => throw "bad statement"
partial def handler (s : Sx) : Except String Handler := do
  match s with
  | .list [.atom "ExceptHandler", l, ty, x, b] =>
    return .mk (← label l) (← opt expr ty) (← opt name x) (← block b)
  | _ => throw "bad handler"
partial def block (s : Sx) : Except String (List Stmt) := list stmt s
end

def program (s : Sx) : Except String (List Stmt) :=
  match s with
  | .list (.atom "Module" :: ss) => ss.mapM stmt
  | _ => .error "expected (Module ...)"

def scopeLabel : List Scope → String
  | [] => "module"
  | S :: _ => toString S.label

def pScopeLabel : List PyCore.Scope → String
  | [] => "module"
  | .fn l _ _ _ :: _ | .cl l _ :: _ => toString (l / 64)

/-- `socc`/`sfn` lines from Surf's own analysis; `tocc`/`tfn` lines from PyCore's
analysis of the translation, with each label and scope mapped back to the Surf
node (`l / 64`) and fresh names left out. -/
def report (p : List Stmt) : List String :=
  let s := (itemsB [] p).map fun
    | .occ l x C => s!"socc {l} {x} {scopeLabel C} {clsStr (clsOf C x)}"
    | .fn l C S => s!"sfn {l} {kindStr (S.kind C)}"
  let t := (PyCore.itemsB PyCore.Edit.none [] (tr p)).filterMap fun
    | .occ l x C => if x.startsWith "." then none
      else some s!"tocc {l / 64} {x} {pScopeLabel C} {clsStr (PyCore.clsOf C x)}"
    | .fn l S => some s!"tfn {l / 64} {kindStr S.kind}"
  s ++ t

/-- Every `(Module ...)` of the input, each reported between `prog` and `end`. -/
partial def runAll (input : String) : Except String (List String) := do
  let rec go (ts : List String) (acc : Array String) : Except String (Array String) :=
    if ts.isEmpty then .ok acc else
    match parseSx ts with
    | .error e => .error e
    | .ok (sx, rest) =>
      let lines := match program sx with
        | .ok p => report p
        | .error e => [s!"error {e}"]
      go rest (acc.push "prog" ++ lines.toArray |>.push "end")
  return (← go (← tokenize input.toList) #[]).toList

end Surf.Cli
