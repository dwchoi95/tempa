/-
Reading PyCore programs and edits as s-expressions, and printing the
classification of every name occurrence, the kind of every function, and the
footprint. The format is documented in NOTES.md.
-/
import PyCore.Syntax

namespace PyCore.Cli
open PyCore

inductive Sx where
  | atom (s : String)
  | list (xs : List Sx)
  deriving Inhabited

/-- Tokens: `(`, `)`, atoms, and double-quoted strings (with `\"` and `\\`). -/
partial def tokenize (cs : List Char) (acc : List String := []) : Except String (List String) :=
  match cs with
  | [] => .ok acc.reverse
  | c :: rest =>
    if c == '(' || c == ')' then tokenize rest (c.toString :: acc)
    else if c.isWhitespace then tokenize rest acc
    else if c == ';' then tokenize (rest.dropWhile (· != '\n')) acc
    else if c == '"' then
      let rec str (cs : List Char) (out : List Char) : Except String (List Char × List Char) :=
        match cs with
        | [] => .error "unterminated string"
        | '\\' :: d :: r => str r (d :: out)
        | '"' :: r => .ok (out.reverse, r)
        | d :: r => str r (d :: out)
      match str rest [] with
      | .ok (s, r) => tokenize r (("\"" ++ String.ofList s) :: acc)
      | .error e => .error e
    else
      let a := cs.takeWhile fun d => !(d.isWhitespace || d == '(' || d == ')')
      tokenize (cs.drop a.length) (String.ofList a :: acc)

partial def parseSx : List String → Except String (Sx × List String)
  | [] => .error "unexpected end of input"
  | "(" :: rest =>
    let rec items (ts : List String) (acc : List Sx) : Except String (List Sx × List String) :=
      match ts with
      | ")" :: r => .ok (acc.reverse, r)
      | [] => .error "missing )"
      | _ => match parseSx ts with
        | .ok (x, r) => items r (x :: acc)
        | .error e => .error e
    match items rest [] with
    | .ok (xs, r) => .ok (.list xs, r)
    | .error e => .error e
  | ")" :: _ => .error "unexpected )"
  | t :: rest => .ok (.atom (if t.startsWith "\"" then t.drop 1 |>.toString else t), rest)

def label (s : Sx) : Except String Label :=
  match s with
  | .atom a => match a.toNat? with
    | some n => .ok n
    | none => .error s!"expected a label, got {a}"
  | _ => .error "expected a label"

def name (s : Sx) : Except String Name :=
  match s with
  | .atom a => .ok a
  | _ => .error "expected a name"

mutual
partial def expr (s : Sx) : Except String Expr := do
  match s with
  | .list [.atom "const", l, c] => return .const (← label l) (← name c)
  | .list [.atom "name", l, x] => return .name (← label l) (← name x) none
  | .list [.atom "name", l, x, k] => return .name (← label l) (← name x) (some (← name k))
  | .list [.atom "bin", l, op, a, b] => return .bin (← label l) (← name op) (← expr a) (← expr b)
  | .list [.atom "call", l, a, b] => return .call (← label l) (← expr a) (← expr b)
  | .list [.atom "lambda", l, x, b] => return .lam (← label l) false (← name x) (← block b)
  | .list [.atom "complambda", l, x, b] => return .lam (← label l) true (← name x) (← block b)
  | .list [.atom "walrus", l, x, e] => return .walrus (← label l) (← name x) (← expr e)
  | .list [.atom "yield", l, e] => return .yield (← label l) (← expr e)
  | .list [.atom "yieldfrom", l, e] => return .yieldFrom (← label l) (← expr e)
  | .list [.atom "ifexp", l, c, a, b] => return .cond (← label l) (← expr c) (← expr a) (← expr b)
  | .list [.atom "and", l, a, b] => return .bool (← label l) true (← expr a) (← expr b)
  | .list [.atom "or", l, a, b] => return .bool (← label l) false (← expr a) (← expr b)
  | _ => throw "bad expression"
partial def stmt (s : Sx) : Except String Stmt := do
  match s with
  | .list [.atom "assign", l, x, e] => return .assign (← label l) (← name x) (← expr e)
  | .list [.atom "del", l, x] => return .del (← label l) (← name x)
  | .list [.atom "expr", l, e] => return .expr (← label l) (← expr e)
  | .list [.atom "if", l, e, t, u] => return .ite (← label l) (← expr e) (← block t) (← block u)
  | .list [.atom "while", l, e, b] => return .while (← label l) (← expr e) (← block b) []
  | .list [.atom "while", l, e, b, u] =>
    return .while (← label l) (← expr e) (← block b) (← block u)
  | .list [.atom "return", l, e] => return .ret (← label l) (← expr e)
  | .list [.atom "def", l, f, x, b] => return .defn (← label l) (← name f) (← name x) (← block b)
  | .list [.atom "class", l, x, b] => return .cls (← label l) (← name x) (← name x) (← block b)
  | .list [.atom "class", l, x, q, b] =>
    return .cls (← label l) (← name x) (← name q) (← block b)
  | .list [.atom "global", l, x] => return .glob (← label l) (← name x)
  | .list [.atom "nonlocal", l, x] => return .nonloc (← label l) (← name x)
  | .list [.atom "try", l, b, lh, h, x, hb] =>
    return .tryE (← label l) (← block b) [.mk (← label lh) (← expr h) (← name x) (← block hb)] []
  | .list [.atom "try", l, b, .list hs, u] =>
    return .tryE (← label l) (← block b) (← hs.mapM handler) (← block u)
  | .list [.atom "raise", l, e] => return .raise (← label l) (← expr e)
  | .list [.atom "print", l, e] => return .print (← label l) (← expr e)
  | .list [.atom "break", l] => return .brk (← label l)
  | .list [.atom "continue", l] => return .cont (← label l)
  | _ => throw "bad statement"
partial def handler (s : Sx) : Except String Handler := do
  match s with
  | .list [.atom "handler", lh, h, x, hb] =>
    return .mk (← label lh) (← expr h) (← name x) (← block hb)
  | _ => throw "bad handler"
partial def block (s : Sx) : Except String (List Stmt) :=
  match s with
  | .list xs => xs.mapM stmt
  | _ => .error "expected a block"
end

def program (s : Sx) : Except String (List Stmt) :=
  match s with
  | .list (.atom "module" :: ss) => ss.mapM stmt
  | _ => .error "expected (module ...)"

/-- The statement of `p` with label `l`. -/
partial def findStmt (l : Label) : List Stmt → Option Stmt
  | [] => none
  | s :: ss =>
    if s.label = l then some s else
    let inner := match s with
      | .ite _ _ t u | .while _ _ t u => findStmt l t <|> findStmt l u
      | .defn _ _ _ b | .cls _ _ _ b => findStmt l b
      | .tryE _ b hs u =>
        findStmt l b <|> hs.firstM (fun | .mk _ _ _ hb => findStmt l hb) <|> findStmt l u
      | _ => none
    inner <|> findStmt l ss

/-- Sites: `(stmts L (s ...))` replaces the statement at L by the list,
`(before L (s ...))` / `(after L (s ...))` insert around it, `(expr L e)`
replaces an expression, `(handler L e x (s ...))` a handler clause. -/
def edit (p : List Stmt) (sites : List Sx) : Except String Edit := do
  let mut ss : List (Label × List Stmt) := []
  let mut es : List (Label × Expr) := []
  let mut hs : List (Label × Handler) := []
  for site in sites do
    match site with
    | .list [.atom "stmts", l, b] => ss := (← label l, ← block b) :: ss
    | .list [.atom "before", l, b] =>
      let l ← label l
      let some s := findStmt l p | throw s!"no statement {l}"
      ss := (l, (← block b) ++ [s]) :: ss
    | .list [.atom "after", l, b] =>
      let l ← label l
      let some s := findStmt l p | throw s!"no statement {l}"
      ss := (l, s :: (← block b)) :: ss
    | .list [.atom "expr", l, e] => es := (← label l, ← expr e) :: es
    | .list [.atom "handler", l, e, x, b] =>
      let l ← label l
      hs := (l, .mk l (← expr e) (← name x) (← block b)) :: hs
    | _ => throw "bad site"
  return { s := fun l => ss.lookup l, e := fun l => es.lookup l, h := fun l => hs.lookup l }

def clsStr : Cls → String
  | .loc => "local" | .free => "free" | .glob => "global"

def kindStr : Kind → String
  | .plain => "plain" | .gen => "generator"

def scopeLabel : List Scope → String
  | [] => "module"
  | .fn l _ _ _ :: _ | .cl l _ :: _ => toString l

/-- One line per occurrence (`occ L x SCOPE CLS`, and `CLS_Q` for a pair) and per
function (`fn L KIND`, and `KIND_Q`). -/
def report (R : Edit) (pair : Bool) (p : List Stmt) : List String :=
  (itemsB Edit.none [] p).map fun
    | .occ l x C =>
      let base := s!"occ {l} {x} {scopeLabel C} {clsStr (clsOf C x)}"
      if pair then base ++ s!" {clsStr (clsOf (C.map (editSc R)) x)}" else base
    | .fn l S =>
      let base := s!"fn {l} {kindStr S.kind}"
      if pair then base ++ s!" {kindStr (editSc R S).kind}" else base

def sortDedup (xs : List Nat) : List Nat :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).mergeSort

def footprintLines (R : Edit) (p : List Stmt) : List String :=
  let show_ (xs : List Nat) := " ".intercalate ((sortDedup xs).map toString)
  [s!"part1 {show_ (part1B R p)}", s!"part2 {show_ (part2 R p)}",
   s!"part3 {show_ (kindChanges R p)}",
   match footprint? R p with
   | some L => s!"footprint {show_ L}"
   | none => "footprint ALL"]

/-- A pair `(pair (module ...) (sites ...))` as `p` and its edit. -/
def parsePair (input : String) : Except String (List Stmt × Edit) := do
  let (sx, _) ← parseSx (← tokenize input.toList)
  match sx with
  | .list [.atom "pair", prog, .list (.atom "sites" :: sites)] =>
    let p ← program prog
    return (p, ← edit p sites)
  | _ => throw "expected (pair ...)"

def runInput (input : String) : Except String (List String) := do
  let (sx, rest) ← parseSx (← tokenize input.toList)
  unless rest.isEmpty do throw "trailing input"
  match sx with
  | .list [.atom "pair", prog, .list (.atom "sites" :: sites)] =>
    let p ← program prog
    let R ← edit p sites
    return report R true p ++ footprintLines R p
  | _ =>
    let p ← program sx
    return report Edit.none false p

end PyCore.Cli
