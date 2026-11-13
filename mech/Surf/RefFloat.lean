/-
IEEE doubles for the reference interpretation, computed exactly with integers:
correctly rounded conversion of a rational to a double (`ratToFloat`), Python's
shortest repr (`floatRepr`, the shortest digit string that converts back, the
closest of those), fixed-point formatting rounded half-even on the exact binary
value (`fixedStr`), `float(s)` parsing, and `fmod`.
-/
namespace Ref

def fOf (b : UInt64) : Float := Float.ofBits b
def bOf (x : Float) : UInt64 := x.toBits

/-- A finite double as (negative, m, e) with |x| = m * 2^e. -/
def decomp (b : UInt64) : Bool × Nat × Int :=
  let neg := (b >>> 63) == 1
  let ex := ((b >>> 52) &&& 0x7FF).toNat
  let frac := (b &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0 then (neg, frac, -1074) else (neg, frac + 2 ^ 52, (ex : Int) - 1075)

def isFinite (b : UInt64) : Bool := ((b >>> 52) &&& 0x7FF) != 0x7FF
def isNaN (b : UInt64) : Bool := !isFinite b && (b &&& 0xFFFFFFFFFFFFF) != 0
def signBit (b : UInt64) : Bool := (b >>> 63) == 1
def posInf : UInt64 := 0x7FF0000000000000
def negInf : UInt64 := 0xFFF0000000000000
def nanBits : UInt64 := 0x7FF8000000000000

def pow2 (e : Nat) : Nat := 2 ^ e

/-- `num / den` (den > 0) as `num' / den'` both natural, scaled by `2^e`:
`num * 2^-e / den` for an integer `e`. -/
private def scaled (num den : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (num, den * pow2 e.toNat) else (num * pow2 (-e).toNat, den)

/-- The double nearest to `num / den` (ties to even), negated if `neg`. -/
def ratToBits (neg : Bool) (num den : Nat) : UInt64 :=
  let sgn : UInt64 := if neg then 0x8000000000000000 else 0
  if num == 0 then sgn else
  -- e with 2^52 ≤ num / den / 2^e < 2^53
  let e0 : Int := (num.log2 : Int) - (den.log2 : Int) - 52
  let fix (e : Int) : Int :=
    let (a, b) := scaled num den e
    let q := a / b
    if q ≥ pow2 53 then e + 1 else if q < pow2 52 then e - 1 else e
  let e := fix (fix (fix e0))
  let e := if e < -1074 then -1074 else e
  let (a, b) := scaled num den e
  let q := a / b
  let r := a % b
  let q := if 2 * r > b || (2 * r == b && q % 2 == 1) then q + 1 else q
  let (q, e) := if q == pow2 53 then (pow2 52, e + 1) else (q, e)
  if e > 971 then sgn ||| posInf
  else if q < pow2 52 then sgn ||| q.toUInt64
  else sgn ||| ((e + 1075).toNat.toUInt64 <<< 52) ||| (q - pow2 52).toUInt64

/-- The exact value of a finite double as `(neg, num, den)`. -/
def toRat (b : UInt64) : Bool × Nat × Nat :=
  let (neg, m, e) := decomp b
  if e ≥ 0 then (neg, m * pow2 e.toNat, 1) else (neg, m, pow2 (-e).toNat)

def intToBits (n : Int) : UInt64 := ratToBits (n < 0) n.natAbs 1

/-- `10^k` as a rational `(num, den)`. -/
private def p10 (k : Int) : Nat × Nat := if k ≥ 0 then (10 ^ k.toNat, 1) else (1, 10 ^ (-k).toNat)

/-- `⌊log10 (num / den)⌋` for a positive rational. -/
def ilog10 (num den : Nat) : Int :=
  let est : Int := (((num.log2 : Int) - (den.log2 : Int)) * 30103) / 100000
  -- adjust until 10^E ≤ num/den < 10^(E+1)
  let le (k : Int) : Bool := let (a, b) := p10 k; a * den ≤ num * b
  let rec up (k : Int) (fuel : Nat) : Int := match fuel with
    | 0 => k
    | n + 1 => if le (k + 1) then up (k + 1) n else k
  let rec down (k : Int) (fuel : Nat) : Int := match fuel with
    | 0 => k
    | n + 1 => if le k then k else down (k - 1) n
  up (down est 10) 10

/-- Python's `repr` of a double. -/
def floatRepr (b : UInt64) : String :=
  if isNaN b then "nan"
  else if !isFinite b then (if signBit b then "-inf" else "inf")
  else
    let (neg, num, den) := toRat b
    let sgn := if neg then "-" else ""
    if num == 0 then sgn ++ "0.0" else
    let E := ilog10 num den
    -- the shortest p and digits D with D * 10^(E - p + 1) converting back to b
    let target := b &&& 0x7FFFFFFFFFFFFFFF
    let conv (D : Nat) (k : Int) : UInt64 :=  -- D * 10^k
      if k ≥ 0 then ratToBits false (D * 10 ^ k.toNat) 1 else ratToBits false D (10 ^ (-k).toNat)
    let dist (D : Nat) (k : Int) : Nat :=      -- |D * 10^k - num/den| scaled by den * 10^-k
      if k ≥ 0 then (Int.natAbs ((D * 10 ^ k.toNat * den : Nat) - (num : Int)))
      else Int.natAbs ((D * den : Nat) - ((num * 10 ^ (-k).toNat : Nat) : Int))
    let rec search (p : Nat) (fuel : Nat) : Nat × Int :=
      let k : Int := E - (p : Int) + 1
      let lo := if k ≥ 0 then num / (den * 10 ^ k.toNat) else (num * 10 ^ (-k).toNat) / den
      let hi := lo + 1
      let okLo := lo > 0 && conv lo k == target
      let okHi := conv hi k == target
      match fuel with
      | 0 => (lo, k)
      | fuel + 1 =>
        if okLo && okHi then
          (if dist hi k < dist lo k || (dist hi k == dist lo k && hi % 2 == 0) then (hi, k) else (lo, k))
        else if okLo then (lo, k) else if okHi then (hi, k) else search (p + 1) fuel
    let (D, k) := search 1 17
    let ds0 := toString D
    -- strip trailing zeros, moving them into the exponent
    let ds := (ds0.toList.reverse.dropWhile (· == '0')).reverse
    let ds := if ds.isEmpty then ['0'] else ds
    let decpt : Int := (ds0.length : Int) + k      -- value = 0.ds * 10^decpt
    let n := ds.length
    let body :=
      if -4 < decpt && decpt ≤ 16 then
        if decpt ≤ 0 then "0." ++ String.ofList (List.replicate (-decpt).toNat '0') ++ String.ofList ds
        else if decpt.toNat ≥ n then String.ofList ds ++ String.ofList (List.replicate (decpt.toNat - n) '0') ++ ".0"
        else String.ofList (ds.take decpt.toNat) ++ "." ++ String.ofList (ds.drop decpt.toNat)
      else
        let x := decpt - 1
        let mant := if n == 1 then String.ofList ds else String.ofList (ds.take 1) ++ "." ++ String.ofList (ds.drop 1)
        let es := toString x.natAbs
        mant ++ "e" ++ (if x < 0 then "-" else "+") ++ (if es.length < 2 then "0" ++ es else es)
    sgn ++ body

/-- `num/den` rounded half-even to an integer. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q

/-- `%.{p}f` of a finite double: rounded half-even on the exact value. -/
def fixedStr (b : UInt64) (p : Nat) : String :=
  if isNaN b then "nan" else if !isFinite b then (if signBit b then "-inf" else "inf") else
  let (neg, num, den) := toRat b
  let R := roundHalfEven (num * 10 ^ p) den
  let ds := toString R
  let ds := if ds.length ≤ p then String.ofList (List.replicate (p + 1 - ds.length) '0') ++ ds else ds
  let ip := ds.take (ds.length - p)
  let fp := ds.drop (ds.length - p)
  (if neg then "-" else "") ++ ip.toString ++ (if p == 0 then "" else "." ++ fp.toString)

/-- `%.{p}e` of a finite double. -/
def expStr (b : UInt64) (p : Nat) : String :=
  if isNaN b then "nan" else if !isFinite b then (if signBit b then "-inf" else "inf") else
  let (neg, num, den) := toRat b
  let sgn := if neg then "-" else ""
  if num == 0 then sgn ++ "0" ++ (if p == 0 then "" else "." ++ String.ofList (List.replicate p '0')) ++ "e+00" else
  let E := ilog10 num den
  let k : Int := E - p
  let R := if k ≥ 0 then roundHalfEven num (den * 10 ^ k.toNat) else roundHalfEven (num * 10 ^ (-k).toNat) den
  let (R, E) := if R ≥ 10 ^ (p + 1) then (R / 10, E + 1) else (R, E)
  let ds := toString R
  let mant := if p == 0 then ds.take 1 |>.toString else (ds.take 1).toString ++ "." ++ (ds.drop 1).toString
  let es := toString E.natAbs
  sgn ++ mant ++ "e" ++ (if E < 0 then "-" else "+") ++ (if es.length < 2 then "0" ++ es else es)

/-- `round(x, n)`: the exact value rounded half-even to `n` decimal places, back to a double. -/
def roundTo (b : UInt64) (n : Int) : UInt64 :=
  if !isFinite b then b else
  let (neg, num, den) := toRat b
  if n ≥ 0 then
    let R := roundHalfEven (num * 10 ^ n.toNat) den
    let r := ratToBits neg R (10 ^ n.toNat)
    if R == 0 then (if neg then 0x8000000000000000 else 0) else r
  else
    let R := roundHalfEven num (den * 10 ^ (-n).toNat)
    if R == 0 then (if neg then 0x8000000000000000 else 0) else ratToBits neg (R * 10 ^ (-n).toNat) 1

/-- Parse a decimal literal (digits, optional point, optional exponent), as `float()` does. -/
def parseFloat (s : String) : Option UInt64 :=
  let s := s.trimAscii.toString
  let (neg, s) := if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString) else (false, s)
  let low := s.toLower
  if low == "inf" || low == "infinity" then some (if neg then negInf else posInf)
  else if low == "nan" then some nanBits
  else
    let cs := s.toList
    let (mant, ex) := match cs.findIdx? (fun c => c == 'e' || c == 'E') with
      | some i => (cs.take i, some (cs.drop (i + 1)))
      | none => (cs, none)
    let (ip, fp) := match mant.findIdx? (· == '.') with
      | some i => (mant.take i, (mant.drop (i + 1)))
      | none => (mant, [])
    let digitsOk (xs : List Char) := xs.all Char.isDigit
    let clean (xs : List Char) : Option (List Char) :=
      -- underscores only between digits
      if xs.head? == some '_' || xs.getLast? == some '_' then none
      else if (xs.zip xs.tail).any (fun p => p.1 == '_' && p.2 == '_') then none
      else some (xs.filter (· != '_'))
    match clean ip, clean fp with
    | some ip, some fp =>
      if !(digitsOk ip && digitsOk fp) || (ip.isEmpty && fp.isEmpty) then none else
      let e : Option Int := match ex with
        | none => some 0
        | some xs => match xs with
          | '+' :: ys => if ys.isEmpty || !digitsOk ys then none else (String.ofList ys).toInt?
          | '-' :: ys => if ys.isEmpty || !digitsOk ys then none else ((String.ofList ys).toInt?).map (- ·)
          | ys => if ys.isEmpty || !digitsOk ys then none else (String.ofList ys).toInt?
      match e with
      | none => none
      | some e =>
        let D := (String.ofList (ip ++ fp)).toNat?.getD 0
        let k : Int := e - fp.length
        some (if k ≥ 0 then ratToBits neg (D * 10 ^ k.toNat) 1 else ratToBits neg D (10 ^ (-k).toNat))
    | _, _ => none

/-- C's `fmod` (exact: the result is representable). -/
def fmodBits (x y : UInt64) : UInt64 :=
  if !isFinite x || isNaN y then nanBits
  else if !isFinite y then x
  else
    let (nx, mx, ex) := decomp x
    let (_, my, ey) := decomp y
    if my == 0 then nanBits else
    let e := min ex ey
    let X := mx * pow2 (ex - e).toNat
    let Y := my * pow2 (ey - e).toNat
    let R := X % Y
    let r := if e ≥ 0 then ratToBits nx (R * pow2 e.toNat) 1 else ratToBits nx R (pow2 (-e).toNat)
    if R == 0 then (if nx then 0x8000000000000000 else 0) else r

end Ref
