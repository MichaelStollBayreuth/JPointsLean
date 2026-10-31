/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Double

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Double

/-!
# The output of `printf`

What `printf` of glibc and `gmp_printf` of GMP print for the conversions that `j-points` uses
beyond the plain `%ld` and `%s` (which print `toString` of an integer and the string itself): `%g`
of a double, which prints the constants of the cost model (`JPoints.Double.printGeneral`, beside
`JPoints.Double.printFixed` for `%f`, `%.2f` and `%.3f`), and the conversions of the format of the
points, which the option `-f` sets: `%[flags][width][.precision]ld` of a `long`, as `printf` prints
it (`JPoints.Printf.printLong`), and `%[flags][width][.precision]Zd` of an `mpz_t`, as `gmp_printf`
prints it (`JPoints.Printf.printMpz`). The program prints a point with `printf` when its
coordinates are `long`s (`JPoints.Printf.emitPoint`) and with `gmp_printf` when they are not
(`JPoints.Printf.printfMpz`), after `printf_mpz` has made each `%…ld` of the format a `%…Zd`
(`JPoints.Printf.rewriteFormat`). And the text of a polynomial, as `print_poly` prints the curve in
the messages (`JPoints.Printf.printPoly`).

## Main definitions

* `JPoints.Double.printGeneral`: a double as `printf` prints it under `%.pg`.
* `JPoints.Printf.Conversion`, `JPoints.Printf.Piece`: the conversions and the pieces of a format
  of the points.
* `JPoints.Printf.parseFormat`: the format of the points, when it is admitted.
* `JPoints.Printf.printLong`, `JPoints.Printf.printMpz`: a conversion of a `long` as glibc prints
  it, and of an `mpz_t` as GMP prints it.
* `JPoints.Printf.render`: a format with its arguments.
* `JPoints.Printf.rewriteFormat`: the format that `printf_mpz` gives `gmp_printf`.
* `JPoints.Printf.emitPoint`, `JPoints.Printf.printfMpz`: the text of a point.
* `JPoints.Printf.printPoly`: the text of a polynomial.

## Implementation notes

`j-points` passes the format of `-f` to `printf` as it is, which the C language defines only for a
format whose conversions take a `long` each, and `printf_mpz` makes each conversion
`%[-+ #'0-9.]*ld` of it a `%…Zd` by a scan of its own. The model admits the formats whose
conversions are all `%[flags][width][.precision]ld`, in this order, with the flags `-`, `+`, ` `,
`#`, `'` and `0`, a width and a precision of at most `JPoints.Printf.maxField`, at most four of
them, and `%%`, and the program refuses the others: these are formats that `printf` of glibc reads
as it documents them (as the C language defines them, but for the flag `#`, whose effect on `d` the
C language leaves undefined and glibc ignores, and the flag `'` of POSIX), that the scan of
`printf_mpz` reads the same way (it makes exactly their `l`s `Z`s), and that `gmp_printf` then
reads with the same pieces. Others the two read differently: `printf` reads `%l%ld` as `%l%` and
the text `ld`, which the scan makes `%l%Zd`.

On the admitted formats `printf` of glibc and `gmp_printf` of GMP 6.3 print alike but for four
departures of GMP from the C language, which `JPoints.Printf.printMpz` follows: of the flags `+`
and ` ` the last one counts (`%+ ld` prints `+12`, `%+ Zd` prints ` 12`), a `.` without digits is
no precision (`%.ld` prints nothing for `0`, `%.Zd` prints `0`), the flag `0` pads with zeros also
with a precision (`%08.3ld` prints `     012`, `%08.3Zd` prints `00000012`), and under the flags
`-` and `0` together the padding after the digits is of zeros (`%-05ld` prints `12   `, `%-05Zd`
prints `12000`). So a point is printed under such a format in one way when its coordinates are
`long`s and in another when they are not. The flags `#` and `'` change nothing in either:
`j-points` calls no `setlocale`, and in the C locale the thousands' separator of `'` is empty.

`printf` rounds the exact value of a double to the digits it prints, to nearest with ties to even
(glibc rounds in the rounding mode, which `j-points` leaves at its default).
-/

@[expose] public section

namespace JPoints

namespace Printf

/-! ### Rounding and digits -/

/-- The quotient `a / b` of natural numbers, `b ≠ 0`, rounded to the nearest integer, ties to even,
as `printf` of glibc rounds the exact value of a double to the digits it prints. -/
def roundDiv (a b : Nat) : Nat :=
  let q := a / b
  let r := a % b
  if b < 2 * r ∨ 2 * r = b ∧ q % 2 = 1 then q + 1 else q

/-- The decimal exponent `⌊log₁₀ (a / b)⌋` of a fraction with `a, b ≠ 0`: for `b ≤ a` the number of
digits of `a / b` less one, and otherwise minus the least `k` with `b ≤ a 10 ^ k`, which is the
number of digits of `⌈b / a⌉ - 1`. -/
def decimalExponent (a b : Nat) : Int :=
  if b ≤ a then ((Nat.toDigits 10 (a / b)).length : Int) - 1
  else -((Nat.toDigits 10 ((b + a - 1) / a - 1)).length : Int)

/-- The fraction `a / b`, `a, b ≠ 0`, rounded to `P ≥ 1` significant decimal digits, to nearest
with ties to even, as `printf` of glibc rounds the exact value of a double under `%e` and `%g`: the
integer `N` of `P` digits and the exponent `X` with `a / b ≈ N 10 ^ (X - P + 1)`, `X` the decimal
exponent of `a / b` (`JPoints.Printf.decimalExponent`), or one more when the rounding carries to
`10 ^ P`. -/
def roundSignificant (P a b : Nat) : Nat × Int :=
  let X := decimalExponent a b
  let t : Int := P - 1 - X
  let N := if 0 ≤ t then roundDiv (a * 10 ^ t.toNat) b else roundDiv a (b * 10 ^ (-t).toNat)
  if N = 10 ^ P then (10 ^ (P - 1), X + 1) else (N, X)

/-- The digits `whole` of an integer part and `frac` of a fractional part as `%g` prints them: the
fractional part without its trailing zeros, after a point unless nothing remains of it. -/
def trimFraction (whole frac : List Char) : String :=
  let frac := (frac.reverse.dropWhile (· == '0')).reverse
  String.ofList whole ++ if frac.isEmpty then "" else "." ++ String.ofList frac

end Printf

namespace Double

/-- What `printf` of glibc prints for the double `x` under the conversion `%.pg`, of which `%g` is
`%.6g`: for `P = max p 1` and the exact value of `x` rounded to `P` significant digits, ties to
even, with the exponent `X` (`JPoints.Printf.roundSignificant`), the style `f` with `P - 1 - X`
places after the point for `-4 ≤ X < P`, and otherwise the style `e`, one digit before the point and
an exponent of at least two digits after `e+` or `e-`; in both the trailing zeros of the fractional
part removed, and the point when nothing remains after it. A zero prints `0`, an infinity `inf` and
a NaN `nan`, each after a `-` when the sign bit is set: `-0`, and `-nan` for the default NaN. -/
def printGeneral (p : Nat) (x : Double) : String :=
  let sign := if x.signBit then "-" else ""
  if x.isNaN then sign ++ "nan"
  else if x.isInf then sign ++ "inf"
  else if x.isZero then sign ++ "0"
  else
    let P := max p 1
    let (m, e) := x.toDyadic
    let (a, b) := if 0 ≤ e then (m.natAbs * 2 ^ e.toNat, 1) else (m.natAbs, 2 ^ (-e).toNat)
    let (N, X) := Printf.roundSignificant P a b
    let ds := Nat.toDigits 10 N
    sign ++ if -4 ≤ X ∧ X < P then
      if 0 ≤ X then Printf.trimFraction (ds.take (X.toNat + 1)) (ds.drop (X.toNat + 1))
      else Printf.trimFraction ['0'] (List.replicate ((-X).toNat - 1) '0' ++ ds)
    else
      Printf.trimFraction (ds.take 1) (ds.drop 1) ++ (if X < 0 then "e-" else "e+") ++
        (if X.natAbs < 10 then "0" else "") ++ toString X.natAbs

end Double

namespace Printf

/-! ### The conversions of a `long` and of an `mpz_t` -/

/-- A conversion `%[flags][width][.precision]ld` of an admitted format of the points
(`JPoints.Printf.parseFormat`), or the `%[flags][width][.precision]Zd` that `printf_mpz` makes of
it, as the format writes it. -/
structure Conversion where
  /-- The flags, each one of `-`, `+`, ` `, `#`, `'` and `0`, in the order of the format, repeats
  included. -/
  flags : List Char
  /-- The width, `0` when the format gives none (a width never starts with `0`, which is a flag). -/
  width : Nat
  /-- The precision as the format writes it: `none` without a `.`, `some none` for a `.` without
  digits, and `some (some n)` for a `.` followed by the digits of `n`. -/
  precision : Option (Option Nat)
  deriving Inhabited, Repr, DecidableEq

/-- What `printf` of glibc prints for the `long` `n` under the conversion `c`: the decimal digits of
`|n|`, with zeros in front up to the precision (a `.` without digits being the precision `0`, under
which `0` has no digits at all); before them `-` for `n < 0`, else `+` under the flag `+`, else a
space under the flag ` `; and, when that is shorter than the width, spaces after it under the flag
`-`, else zeros between the sign and the digits under the flag `0` when there is no precision, else
spaces before it. The flag `#` is no flag of `d`, which glibc ignores, and `'` groups the digits by
the thousands' separator of the locale, which is empty in the C locale of `j-points`. -/
def printLong (c : Conversion) (n : Int) : String :=
  let prec := c.precision.map (·.getD 0)
  let ds := Nat.toDigits 10 n.natAbs
  let ds := match prec with
    | none => ds
    | some p => if p = 0 ∧ n = 0 then [] else List.replicate (p - ds.length) '0' ++ ds
  let sign := if n < 0 then ['-'] else if '+' ∈ c.flags then ['+']
    else if ' ' ∈ c.flags then [' '] else []
  let pad := c.width - (sign.length + ds.length)
  String.ofList <|
    if '-' ∈ c.flags then sign ++ ds ++ List.replicate pad ' '
    else if '0' ∈ c.flags ∧ prec.isNone then sign ++ List.replicate pad '0' ++ ds
    else List.replicate pad ' ' ++ sign ++ ds

/-- What `gmp_printf` of GMP 6.3 prints for the integer `n` under the conversion `c` with the type
`Z`: the decimal digits of `|n|` (none for `n = 0` under the precision `0`), zeros in front of them
up to the precision, a `.` without digits being no precision; before them `-` for `n < 0`, else the
last of the flags `+` and ` `; and, when that is shorter than the width, a padding up to the width,
of zeros under the flag `0` and of spaces otherwise, after the digits under the flag `-`, else
between the sign and the digits under the flag `0`, else before the sign. The flags `#`, which
shows no base in base 10, and `'` change nothing. Unlike `printf` (`JPoints.Printf.printLong`),
the last of `+` and ` ` counts, a `.` alone is no precision, and the flag `0` pads with zeros also
with a precision and after the digits under `-`. -/
def printMpz (c : Conversion) (n : Int) : String :=
  let prec := c.precision.join
  let ds := if prec = some 0 ∧ n = 0 then [] else Nat.toDigits 10 n.natAbs
  let zeros := List.replicate (prec.getD 0 - ds.length) '0'
  let sign := if n < 0 then ['-'] else (c.flags.reverse.find? (· ∈ ['+', ' '])).toList
  let fill := if '0' ∈ c.flags then '0' else ' '
  let pad := List.replicate (c.width - (sign.length + zeros.length + ds.length)) fill
  String.ofList <|
    if '-' ∈ c.flags then sign ++ zeros ++ ds ++ pad
    else if '0' ∈ c.flags then sign ++ zeros ++ pad ++ ds
    else pad ++ sign ++ zeros ++ ds

/-! ### The formats of the points -/

/-- A piece of an admitted format of the points (`JPoints.Printf.parseFormat`). -/
inductive Piece where
  /-- A character that the format prints as it is: a character other than `%`, or the `%` of
  `%%`. -/
  | char (ch : Char)
  /-- A conversion, which prints the next argument. -/
  | conv (c : Conversion)
  deriving Inhabited, Repr, DecidableEq

/-- The largest width and the largest precision of a conversion of an admitted format, `4095`, the
number of characters of a single conversion that the C language requires every implementation to
support (under the precision `4095` a sign makes one character more, which glibc and GMP print as
well): a bound of the model, well below the limits of `printf` of glibc, which fails beyond
`INT_MAX` characters in one call, and of `gmp_printf`, which reads a width and a precision into an
`int`. -/
def maxField : Nat := 4095

/-- The flags of a conversion. -/
def flagChars : List Char := ['-', '+', ' ', '#', '\'', '0']

/-- Where the reading of a format stands (`JPoints.Printf.readFormat`). -/
inductive ReadState where
  /-- Outside the conversions. -/
  | text
  /-- In the flags of the conversion `c` read so far, or right after its `%` when `c` has none. -/
  | flags (c : Conversion)
  /-- In the width of the conversion `c` read so far. -/
  | width (c : Conversion)
  /-- In the precision of the conversion `c` read so far, after its `.`. -/
  | precision (c : Conversion)
  /-- After the length modifier of the conversion `c`. -/
  | length (c : Conversion)
  deriving Inhabited, Repr

/-- The step of the reading of a format at the character `ch` after the flags of the conversion `c`
or in its width: a digit of the width, the `.` that starts the precision, or the length modifier
`len`; `none` for any other character. -/
def readWidth (len : Char) (c : Conversion) (ch : Char) : Option (ReadState × List Piece) :=
  if ch.isDigit then some (.width { c with width := 10 * c.width + (ch.toNat - '0'.toNat) }, [])
  else if ch = '.' then some (.precision { c with precision := some none }, [])
  else if ch = len then some (.length c, [])
  else none

/-- The step of the reading of a format whose conversions end in the length modifier `len` and `d`
(`l` for `printf`, `Z` for the format that `printf_mpz` gives `gmp_printf`) at the character `ch`
in the state `st`: the next state and the pieces that `ch` completes, or `none` when `ch` cannot
come there. A `%` starts a conversion, or the `%%` that prints `%` when the next character is `%`;
a conversion is its flags, a width whose first digit is not `0` (a `0` there is a flag), a `.` with
the digits of the precision, both optional, `len`, and `d`, with a width and a precision of at most
`JPoints.Printf.maxField`. -/
def readChar (len : Char) (st : ReadState) (ch : Char) : Option (ReadState × List Piece) :=
  match st with
  | .text => some (if ch = '%' then (.flags ⟨[], 0, none⟩, []) else (.text, [.char ch]))
  | .flags c =>
    if ch = '%' ∧ c.flags = [] then some (.text, [.char '%'])
    else if ch ∈ flagChars then some (.flags { c with flags := c.flags ++ [ch] }, [])
    else readWidth len c ch
  | .width c => readWidth len c ch
  | .precision c =>
    if ch.isDigit then
      let p := 10 * c.precision.join.getD 0 + (ch.toNat - '0'.toNat)
      some (.precision { c with precision := some (some p) }, [])
    else if ch = len then some (.length c, [])
    else none
  | .length c =>
    if ch = 'd' ∧ c.width ≤ maxField ∧ c.precision.join.getD 0 ≤ maxField then
      some (.text, [.conv c])
    else none

/-- The pieces of the characters `s` of a format read from the state `st`
(`JPoints.Printf.readChar`), or `none` when they are no admitted format or end inside a
conversion. -/
def readFormat (len : Char) : ReadState → List Char → Option (List Piece)
  | .text, [] => some []
  | _, [] => none
  | st, ch :: s => do
    let (st, ps) ← readChar len st ch
    return ps ++ (← readFormat len st s)

/-- The format `s` of the points as `printf` reads it (`len = 'l'`), or as `gmp_printf` reads the
format that `printf_mpz` makes of it (`len = 'Z'`), when it is admitted: its pieces
(`JPoints.Printf.readFormat`), of which at most four are conversions, the four arguments that the
program passes; `none` for any other format, which the program refuses. -/
def parseFormat (len : Char) (s : String) : Option (List Piece) := do
  let ps ← readFormat len .text s.toList
  if (ps.filter (· matches .conv _)).length ≤ 4 then some ps else none

/-- What `printf` prints under the pieces `f` of a format for the arguments `xs`, each conversion
printed by `conv` with the next argument: `JPoints.Printf.printLong` for `printf` of glibc,
`JPoints.Printf.printMpz` for `gmp_printf` of GMP. Arguments left over are ignored, as the C
language prescribes; a conversion without an argument prints nothing, which no admitted format
meets in the program. -/
def render (conv : Conversion → Int → String) : List Piece → List Int → String
  | [], _ => ""
  | .char ch :: f, xs => ch.toString ++ render conv f xs
  | .conv c :: f, x :: xs => conv c x ++ render conv f xs
  | .conv _ :: f, [] => render conv f []

/-- The characters that the scan of `printf_mpz` passes over after a `%`. -/
def scanChars : List Char := "-+ #'0123456789.".toList

/-- The format that `printf_mpz` gives `gmp_printf`: the format `format` with the `l` of each
conversion `%[-+ #'0-9.]*ld` made a `Z`, by the scan of the C code: at each `%` that does not start
a `%%` (which is passed over), the characters of `JPoints.Printf.scanChars` after it are passed
over, an `l` followed by `d` there becomes `Z`, and the scan resumes after the character that ended
the run (so that it passes over `%5%` whole). On an admitted format it makes exactly the `l` of each
conversion a `Z`, and `gmp_printf` reads the result with the same pieces:
`JPoints.Printf.parseFormat 'Z'` of it is `JPoints.Printf.parseFormat 'l' format`.

C: `j-points.c:2039`, `j-points.c:2042-2049`

Deviation: the characters of a string for the bytes of the C string, which the scan treats alike,
since the characters it looks for are ASCII and no byte of a character beyond ASCII in UTF-8 is;
the end of the string for its NUL, the string having none inside (an argument of the command line
has none); an array of characters for the copy `fmt`. -/
def rewriteFormat (format : String) : Id String := do
  let mut fmt := format.toList.toArray
  let l := fmt.size
  let mut i := 0
  while i < l do
    if fmt[i]! = '%' then
      if fmt.getD (i + 1) '\x00' = '%' then
        i := i + 1
      else
        let mut k := i + 1
        while k < l ∧ fmt[k]! ∈ scanChars do
          k := k + 1
        if fmt.getD k '\x00' = 'l' ∧ fmt.getD (k + 1) '\x00' = 'd' then
          fmt := fmt.set! k 'Z'
        i := k
    i := i + 1
  return String.ofList fmt.toList

/-! ### The text of a point -/

/-- What `emit_point` prints for the point `(a : b : c : d)` found on the curve searched, with
coordinates that are `long`s: the point of the curve given, `a` and `c` swapped when the search
reversed the curve and `b` negated when it negated it, then all four negated when the first nonzero
of `a, b, c` is negative, under the format `format` by `printf` (`JPoints.Printf.printLong`), which
reads it at each call (`JPoints.Printf.parseFormat 'l'`).

C: `j-points.c:2082-2083`, `j-points.c:2085-2090`, `j-points.c:2095`

Deviation: nothing printed for a format that is not admitted (the C code passes any format to
`printf`), which the program refuses before the search; `Bool`s for the flags `reversed` and
`negated`, and arguments for these globals and for `print_format`; integers for the `long`s, which
are at most `MAX_HEIGHT` in absolute value, so that the negations stay in range; the text, which the
caller writes to `stdout`; the path of one thread. -/
def emitPoint (reversed negated : Bool) (format : String) (a b c d : Int) : String :=
  let (a, c) := if reversed then (c, a) else (a, c)
  let b := if negated then -b else b
  let (a, b, c, d) :=
    if a < 0 ∨ a = 0 ∧ (b < 0 ∨ b = 0 ∧ c < 0) then (-a, -b, -c, -d) else (a, b, c, d)
  match parseFormat 'l' format with
  | some f => render printLong f [a, b, c, d]
  | none => ""

/-- What `printf_mpz` prints for the point `(a : b : c : d)` found on the curve searched, with
coordinates that need not be `long`s: the format `format` with each `%…ld` made a `%…Zd`
(`JPoints.Printf.rewriteFormat`); the point of the curve given, `a` and `c` swapped when the search
reversed the curve and `b` negated when it negated it, then, when it did either, all four negated
when the first nonzero of `a, b, c` is negative; and the point under the rewritten format by
`gmp_printf` (`JPoints.Printf.printMpz`), which reads it with the type `Z`
(`JPoints.Printf.parseFormat 'Z'`). For an admitted format, whose pieces are
`JPoints.Printf.parseFormat 'l' format = some f`, that reading succeeds, with the same pieces `f`:
the point is printed under the conversions that `printf` reads in `format`.

C: `j-points.c:2035-2036`, `j-points.c:2050-2056`, `j-points.c:2064`

Deviation: nothing printed for a rewritten format that `gmp_printf` does not read as an admitted one
(the C code passes it to `gmp_printf` whatever it is), which no admitted format gives; `Bool`s for
the flags `reversed` and `negated`, and arguments for these globals; the coordinates by value, which
the C code negates in place in the variables of its caller, which sets them anew before each call;
the text, which the caller writes to `stdout`; the path of one thread. -/
def printfMpz (reversed negated : Bool) (format : String) (a b c d : Int) : Id String := do
  let fmt ← rewriteFormat format
  let (a, c) := if reversed then (c, a) else (a, c)
  let b := if negated then -b else b
  let (a, b, c, d) :=
    if (reversed || negated) ∧ (a < 0 ∨ a = 0 ∧ (b < 0 ∨ b = 0 ∧ c < 0)) then (-a, -b, -c, -d)
    else (a, b, c, d)
  return match parseFormat 'Z' fmt with
    | some f => render printMpz f [a, b, c, d]
    | none => ""

/-! ### The text of a polynomial -/

/-- What `print_poly` prints for the polynomial `∑ coeffs[i] xⁱ` of degree at most `degree`: its
nonzero terms from `x ^ degree` down to the constant term, `n x^i`, `n x` and `n` with the absolute
value `n` of the coefficient, which is left out before `x^i` and `x` when it is `1`, each after
` + ` or ` - ` by its sign, the first after nothing or `- `; then a newline. A zero polynomial
prints the newline alone.

C: `j-points.c:2264-2293`

Deviation: the text returned, which the caller writes to `stdout`, and of which the flush of
`stdout` at the end changes nothing; natural numbers for the `long` `degree` and the `int` index
`i`; the steps of the loop counted up, for the index `i` that counts down from `degree`; a local for
the scratch integer `tmp3`. -/
def printPoly (coeffs : Array Int) (degree : Nat) : Id String := do
  let mut s := ""
  let mut flag := false
  for j in [0:degree + 1] do
    let i := degree - j
    let mut tmp3 := coeffs[i]!
    if tmp3 != 0 then
      if tmp3 > 0 then
        s := s ++ if flag then " + " else ""
      else
        s := s ++ if flag then " - " else "- "
        tmp3 := -tmp3
      flag := true
      match i with
      | 0 => s := s ++ toString tmp3
      | 1 => s := s ++ if tmp3 == 1 then "x" else s!"{tmp3} x"
      | _ => s := s ++ if tmp3 == 1 then s!"x^{i}" else s!"{tmp3} x^{i}"
  return s ++ "\n"

/-! ### Examples

The conversions on their edge cases, against what C programs compiled with `gcc -O2` and linked with
glibc and GMP 6.3 on x86-64 print for them: `printf` for `%g` and `%ld`, `gmp_printf` for `%Zd`,
and copies of the scan, of `emit_point` and of `printf_mpz` of `j-points.c`. -/

-- `%g` and `%.pg`: both zeros, the infinities, NaNs (`-nan` for the default NaN), the constants of
-- the cost model, the change of style at `10 ^ 6` and at `10 ^ (-4)`, also by the rounding
-- (`999999.5`), ties to even (`1234565`, `2.5`, `15`, `0.25`), subnormals, the largest double,
-- `2 ^ 63`, `MAX_HEIGHT`, and the precisions `0`, `1`, `2`, `3`, `4`, `16`, `17`, `25`, `40`.
#guard ([(0x0000000000000000, 6, "0"), (0x8000000000000000, 6, "-0"),
    (0x7ff0000000000000, 6, "inf"), (0xfff0000000000000, 6, "-inf"), (0x7ff8000000000000, 6, "nan"),
    (0xfff8000000000000, 6, "-nan"), (0x7ff0000000000001, 6, "nan"), (0x3ff0000000000000, 6, "1"),
    (0xbff0000000000000, 6, "-1"), (0x3fb999999999999a, 6, "0.1"), (0x3fe428f5c28f5c29, 6, "0.63"),
    (0x4087a00000000000, 6, "756"), (0x4016666666666666, 6, "5.6"), (0x4094500000000000, 6, "1300"),
    (0x405b800000000000, 6, "110"), (0x40f86a0000000000, 6, "100000"),
    (0x412e847e00000000, 6, "999999"), (0x412e847f00000000, 6, "1e+06"),
    (0x412e847ecccccccd, 6, "999999"), (0x412e848000000000, 6, "1e+06"),
    (0x419d6f3454000000, 6, "1.23457e+08"), (0x4132d68500000000, 6, "1.23456e+06"),
    (0x4132d68f00000000, 6, "1.23458e+06"), (0x3f1a36e2eb1c432d, 6, "0.0001"),
    (0x3f1a36e2eb1c432c, 6, "0.0001"), (0x3ee4f8b588e368f1, 6, "1e-05"),
    (0x3f202e85be111841, 6, "0.000123457"), (0x3f1a36e20acf5dfe, 6, "9.99999e-05"),
    (0x3f1a36e2139b2abe, 6, "0.0001"), (0x54b249ad2594c37d, 6, "1e+100"),
    (0x000012688b70e62b, 6, "1e-310"), (0x0000000000000001, 6, "4.94066e-324"),
    (0x7fefffffffffffff, 6, "1.79769e+308"), (0x0010000000000000, 6, "2.22507e-308"),
    (0x43e0000000000000, 6, "9.22337e+18"), (0x41e6a09e66600000, 6, "3.037e+09"),
    (0xbfe0000000000000, 6, "-0.5"), (0x3e8421f5f40d8376, 6, "1.5e-07"),
    (0x3fe0000000000000, 0, "0.5"), (0x4004000000000000, 1, "2"), (0x400c000000000000, 1, "4"),
    (0x3fd0000000000000, 1, "0.2"), (0x402e000000000000, 1, "2e+01"),
    (0x4057c00000000000, 1, "1e+02"), (0x3fb999999999999a, 17, "0.10000000000000001"),
    (0x3fb999999999999a, 40, "0.1000000000000000055511151231257827021182"),
    (0x3fd5555555555555, 17, "0.33333333333333331"),
    (0x44b52d02c7e14af6, 17, "9.9999999999999992e+22"),
    (0x44b52d02c7e14af6, 25, "99999999999999991611392"), (0x405edd2f1a9fbe77, 2, "1.2e+02"),
    (0x405edd2f1a9fbe77, 3, "123"), (0x405edd2f1a9fbe77, 4, "123.5"),
    (0x0000000000000001, 17, "4.9406564584124654e-324"),
    (0x7fefffffffffffff, 17, "1.7976931348623157e+308"),
    (0x430c6bf526340000, 17, "1000000000000000"), (0x4341c37937e08000, 16, "1e+16"),
    (0x4341c37937e08000, 17, "10000000000000000"),
    (0x0010000000000000, 25, "2.225073858507201383090233e-308"), (0x4059000000000000, 2, "1e+02"),
    (0x4059000000000000, 3, "100"), (0x0000000000000000, 0, "0"), (0x8000000000000000, 3, "-0")] :
    List (UInt64 × Nat × String)).all fun (x, p, r) ↦ (Double.mk x).printGeneral p == r

-- `%g`, `%.1g` and `%.17g` of 256 doubles spread over all bit patterns, and `%g` and `%.3g` of
-- `n / 2 ^ k` for `n = 0, 7, …, 994` and `k = 0, 3, 10`, by the FNV-1a hash of the texts, each
-- followed by a newline, which the C program computes in the same way.
#guard
  let fnv (l : List (Double × Nat)) : UInt64 := l.foldl (fun h (x, p) ↦
    ((x.printGeneral p).push '\n').toUTF8.foldl (fun h b ↦ (h ^^^ b.toUInt64) * 0x100000001b3) h)
    0xcbf29ce484222325
  let xs := (List.range 256).map fun i ↦ Double.mk (i.toUInt64 * 0x9e3779b97f4a7c15)
  let ys := (List.range 143).flatMap fun n ↦
    [0, 3, 10].map fun k ↦ Double.ofDyadic false (7 * n) (-k)
  fnv (xs.flatMap fun x ↦ [6, 1, 17].map (x, ·)) == 0xc5bc8cb0bd70dbee &&
    fnv (ys.flatMap fun y ↦ [6, 3].map (y, ·)) == 0x472981d26213e180

-- `%…ld` of `printf` and `%…Zd` of `gmp_printf`, as `"%" ++ s ++ "ld"` reads: the precision `0`
-- and a `.` alone for `0`, the four departures of GMP (`-` with `0`, `0` with a precision, `+`
-- before ` `, a `.` alone), `'` and `#`, the least and the largest `long`.
#guard ([("", 0, "0", "0"), (".0", 0, "", ""), (".", 0, "", "0"), ("+.0", 0, "+", "+"),
    ("5.0", 0, "     ", "     "), ("5.", 0, "     ", "    0"), ("05.", 3, "    3", "00003"),
    ("-05", 12, "12   ", "12000"), ("0-5", -12, "-12  ", "-1200"),
    ("08.3", 12, "     012", "00000012"), ("08.3", -12, "    -012", "-0000012"),
    ("+ ", 12, "+12", " 12"), (" +", 12, "+12", "+12"), ("+ ", -12, "-12", "-12"),
    ("'", 1234567, "1234567", "1234567"), ("'010", -1234567, "-001234567", "-001234567"),
    ("#", 5, "5", "5"), (".05", 3, "00003", "00003"), ("+", 0, "+0", "+0"), (" ", -3, "-3", "-3"),
    ("", -9223372036854775808, "-9223372036854775808", "-9223372036854775808"),
    ("+25", 9223372036854775807, "     +9223372036854775807", "     +9223372036854775807"),
    ("-25.20", -7, "-00000000000000000007    ", "-00000000000000000007    "),
    ("010", -42, "-000000042", "-000000042"), ("-+8", 42, "+42     ", "+42     "),
    (".00", 0, "", ""), ("3", 12345, "12345", "12345"),
    (".19", -9223372036854775808, "-9223372036854775808", "-9223372036854775808")] :
    List (String × Int × String × String)).all fun (s, n, r, r') ↦
  match parseFormat 'l' ("%" ++ s ++ "ld") with
  | some [.conv c] => printLong c n == r && printMpz c n == r'
  | _ => false

-- `%…Zd` of integers beyond the `long`s.
#guard ([("", 100000000000000000000, "100000000000000000000"),
    (".25", -100000000000000000000, "-0000100000000000000000000"),
    ("+30", 9223372036854775808, "          +9223372036854775808"),
    ("-030", -9223372036854775809, "-92233720368547758090000000000"),
    ("08.25", 123456789012345678901234567890, "123456789012345678901234567890")] :
    List (String × Int × String)).all fun (s, n, r) ↦
  match parseFormat 'l' ("%" ++ s ++ "ld") with
  | some [.conv c] => printMpz c n == r
  | _ => false

-- Both conversions under every string of at most two flags, the widths none and `6` and the
-- precisions none, `.`, `.0` and `.3`, of `0`, `7`, `-7` and `12345`, by the FNV-1a hash of the
-- texts, each followed by a newline, which the C program computes in the same way.
#guard
  let fl : List (List Char) := [[]] ++ flagChars.map ([·]) ++
    flagChars.flatMap fun a ↦ flagChars.map ([a, ·])
  let cs := fl.flatMap fun f ↦ ["", "6"].flatMap fun w ↦ ["", ".", ".0", ".3"].filterMap fun p ↦
    match parseFormat 'l' ("%" ++ String.ofList f ++ w ++ p ++ "ld") with
    | some [.conv c] => some c
    | _ => none
  let fnv (pr : Conversion → Int → String) : UInt64 := cs.foldl (fun h c ↦ [0, 7, -7, 12345].foldl
    (fun h n ↦ ((pr c n).push '\n').toUTF8.foldl (fun h b ↦ (h ^^^ b.toUInt64) * 0x100000001b3) h)
    h) 0xcbf29ce484222325
  cs.length == 344 && fnv printLong == 0x114ea2a37bbaaacd && fnv printMpz == 0xd4ddc5b9caf9a5cf

-- The admitted formats: the default one, `%%`, the widest conversions, all flags, leading zeros,
-- four conversions, text beyond ASCII; and the pieces of one of them.
#guard ["", "%%", "(%ld, %ld, %ld, %ld)\n", "%4095.4095ld", "%.ld", "%-+ #'0ld", "%%%ld",
  "%000012.0003ld", "%ld%ld%ld%ld", "é%ld→"].all fun s ↦ (parseFormat 'l' s).isSome
#guard parseFormat 'l' "%-05.ld%%x" ==
  some [.conv ⟨['-', '0'], 5, some none⟩, .char '%', .char 'x']

-- Formats that are not admitted: other conversions and length modifiers, flags after the width,
-- two precisions, a `%` ending the format or inside a conversion, five conversions, a width or a
-- precision beyond `JPoints.Printf.maxField`.
#guard ["%5%", "%l%ld", "%1-ld", "%.3.4ld", "%lld", "%d", "%s", "%1$ld", "%ld%ld%ld%ld%ld",
  "%4096ld", "%.4096ld", "%", "%ld%", "%-", "%*ld", "%hd", "%Zd", "%-%", "%ld %i", "%l", "%.-3ld",
  "%5.3-ld", "%ld%"].all fun s ↦ (parseFormat 'l' s).isNone

-- The widest conversions.
#guard (parseFormat 'l' "%4095.4095ld|%-4095ld|%.0ld").map (fun f ↦
  let r := "-" ++ "".pushn '0' 4094 ++ "5|7" ++ "".pushn ' ' 4094 ++ "|"
  render printLong f [-5, 7, 0, 0] == r && render printMpz f [-5, 7, 0, 0] == r) == some true

-- The scan of `printf_mpz`, on admitted formats and on others (`%l%ld`, `%5%`, `%1$ld`, …); on the
-- admitted ones `gmp_printf` reads the result with the pieces that `printf` reads.
#guard ([("(%ld, %ld, %ld, %ld)\n", "(%Zd, %Zd, %Zd, %Zd)\n"), ("%l%ld", "%l%Zd"),
    ("%5%|%ld", "%5%|%Zd"), ("%1-ld|%.3.4ld|%lld", "%1-Zd|%.3.4Zd|%lld"),
    ("%%ld|%%%ld", "%%ld|%%%Zd"), ("%", "%"), ("%ld%", "%Zd%"),
    ("%-ld %+ld % ld %#ld %'ld %0ld", "%-Zd %+Zd % Zd %#Zd %'Zd %0Zd"), ("%%%%ld", "%%%%ld"),
    ("%-+ #'0123456789.ld", "%-+ #'0123456789.Zd"), ("%hd%ld", "%hd%Zd"), ("%1$ld", "%1$ld"),
    ("%ldd%l", "%Zdd%l"), ("%-", "%-"), ("é%ld→", "é%Zd→"),
    ("%4095.4095ld", "%4095.4095Zd"), ("", "")] : List (String × String)).all fun (s, r) ↦
  Id.run (rewriteFormat s) == r &&
    ((parseFormat 'l' s).isNone || parseFormat 'Z' (Id.run (rewriteFormat s)) == parseFormat 'l' s)

-- The conversions of at most two flags, the widths none, `6` and `12` and the precisions none, `.`,
-- `.0` and `.3`, in a format with text, `%%` and a second conversion, all admitted: `gmp_printf`
-- reads the rewritten format with the pieces that `printf` reads.
#guard
  let fl : List (List Char) := [[]] ++ flagChars.map ([·]) ++
    flagChars.flatMap fun a ↦ flagChars.map ([a, ·])
  let fs := fl.flatMap fun f ↦ ["", "6", "12"].flatMap fun w ↦ ["", ".", ".0", ".3"].map fun p ↦
    "<%%%" ++ String.ofList f ++ w ++ p ++ "ld|%ld>\n"
  fs.length == 516 && fs.all fun s ↦
    (parseFormat 'l' s).isSome && parseFormat 'Z' (Id.run (rewriteFormat s)) == parseFormat 'l' s

-- `emit_point` and `printf_mpz` on points with `long` coordinates: the curve reversed, negated,
-- both or neither, the signs made positive (by `emit_point` also without a transformation, by
-- `printf_mpz` only after one), the four departures of GMP, `%%`, a tab, fewer conversions than
-- coordinates, a format without conversions, the empty format, a backslash.
#guard ([
    (false, false, 1, -2, 3, 4, "(%ld, %ld, %ld, %ld)\n", "(1, -2, 3, 4)\n", "(1, -2, 3, 4)\n"),
    (true, false, 1, -2, 3, 4, "(%ld, %ld, %ld, %ld)\n", "(3, -2, 1, 4)\n", "(3, -2, 1, 4)\n"),
    (false, true, 1, -2, 3, 4, "(%ld, %ld, %ld, %ld)\n", "(1, 2, 3, 4)\n", "(1, 2, 3, 4)\n"),
    (true, true, 1, -2, 3, 4, "(%ld, %ld, %ld, %ld)\n", "(3, 2, 1, 4)\n", "(3, 2, 1, 4)\n"),
    (true, false, -5, 2, 0, -7, "(%ld, %ld, %ld, %ld)\n", "(0, 2, -5, -7)\n", "(0, 2, -5, -7)\n"),
    (true, true, 0, 2, 3, -7, "(%ld, %ld, %ld, %ld)\n", "(3, -2, 0, -7)\n", "(3, -2, 0, -7)\n"),
    (false, true, 0, 2, 3, -7, "(%ld, %ld, %ld, %ld)\n", "(0, 2, -3, 7)\n", "(0, 2, -3, 7)\n"),
    (false, true, 0, 0, 3, -7, "(%ld, %ld, %ld, %ld)\n", "(0, 0, 3, -7)\n", "(0, 0, 3, -7)\n"),
    (true, false, -1, 0, 0, 0, "(%ld, %ld, %ld, %ld)\n", "(0, 0, 1, 0)\n", "(0, 0, 1, 0)\n"),
    (false, false, -1, 2, 3, 4, "(%ld, %ld, %ld, %ld)\n", "(1, -2, -3, -4)\n", "(-1, 2, 3, 4)\n"),
    (false, false, 12, -3, 0, 4, "[%-05ld|%08.3ld|%+ ld|%.ld]\n", "[12   |    -003|+0|4]\n",
      "[12000|-0000003| 0|4]\n"),
    (false, false, 0, 0, 0, 0, "[%-05ld|%08.3ld|%+ ld|%.ld]\n", "[0    |     000|+0|]\n",
      "[00000|00000000| 0|0]\n"),
    (false, false, 12, 3, 5, 4, "%+'#5.3ld;%% %ld%%%ld\t%ld!", " +012;% 3%5\t4!",
      " +012;% 3%5\t4!"),
    (false, false, 1, 2, 3, 4, "", "", ""), (false, false, 1, 2, 3, 4, "%ld,%ld", "1,2", "1,2"),
    (true, false, -2, 7, -1, 5, "(%ld : %ld : %ld : %ld)\n", "(1 : -7 : 2 : -5)\n",
      "(1 : -7 : 2 : -5)\n"),
    (false, false, 0, 1, -1, 9223372036854775807, "%ld %ld %ld %ld", "0 1 -1 9223372036854775807",
      "0 1 -1 9223372036854775807"),
    (false, false, 3, 1, 1, 2, "a\\b %-+5ld|%5ld|%-5ld|%05ld", "a\\b +3   |    1|1    |00002",
      "a\\b +3   |    1|1    |00002")] :
    List (Bool × Bool × Int × Int × Int × Int × String × String × String)).all
  fun (rev, neg, a, b, c, d, s, r, r') ↦ (parseFormat 'l' s).isSome &&
    emitPoint rev neg s a b c d == r && Id.run (printfMpz rev neg s a b c d) == r'

-- `printf_mpz` on points beyond the `long`s.
#guard ([(false, false, 2, -3, 1, 99999999999999999999999, "(%ld, %ld, %ld, %ld)\n",
      "(2, -3, 1, 99999999999999999999999)\n"),
    (true, true, 2, -3, 1, 99999999999999999999999, "(%ld, %ld, %ld, %ld)\n",
      "(1, 3, 2, 99999999999999999999999)\n"),
    (false, true, 0, 3, 1, -99999999999999999999999, "(%ld, %ld, %ld, %ld)\n",
      "(0, 3, -1, 99999999999999999999999)\n"),
    (false, false, 0, 1, -1, 9223372036854775808, "%ld %ld %ld %ld",
      "0 1 -1 9223372036854775808")] :
    List (Bool × Bool × Int × Int × Int × Int × String × String)).all
  fun (rev, neg, a, b, c, d, s, r) ↦
    (parseFormat 'l' s).isSome && Id.run (printfMpz rev neg s a b c d) == r

-- Formats that are not admitted print nothing (the program refuses them before the search).
#guard ["%d", "%lld", "%s", "%5%", "%ld%ld%ld%ld%ld"].all fun s ↦
  emitPoint false false s 1 2 3 4 == "" && Id.run (printfMpz true true s 1 2 3 4) == ""

-- `print_poly`: the signs, the coefficient `1` left out before `x^i` and `x` but not as the
-- constant term, zero coefficients left out, the zero polynomial, the degrees `0`, `2`, `5` (with
-- `f₆` not printed) and `6`, coefficients beyond the `long`s.
#guard ([
    (6, #[-1, 0, 3, 0, 0, 0, 1], "x^6 + 3 x^2 - 1\n"),
    (5, #[-7, 2, 0, 0, 0, -1, 0], "- x^5 + 2 x - 7\n"),
    (6, #[1, 1, 1, 1, 1, 1, 1], "x^6 + x^5 + x^4 + x^3 + x^2 + x + 1\n"),
    (6, #[-1, -1, -1, -1, -1, -1, -1], "- x^6 - x^5 - x^4 - x^3 - x^2 - x - 1\n"),
    (5, #[0, 0, 0, 0, 0, 0, 0], "\n"), (6, #[5, 0, 0, 0, 0, 0, 0], "5\n"),
    (6, #[-5, 0, 0, 0, 0, 0, 0], "- 5\n"),
    (5, #[1, 178, 817, -274, 16, 1, 0], "x^5 + 16 x^4 - 274 x^3 + 817 x^2 + 178 x + 1\n"),
    (5, #[1, 2, 3, 4, 5, 6, 7], "6 x^5 + 5 x^4 + 4 x^3 + 3 x^2 + 2 x + 1\n"),
    (6, #[0, 1, 0, 0, 0, 0, 0], "x\n"), (6, #[0, -1, 0, 0, 0, 0, 0], "- x\n"),
    (6, #[0, -2, 0, 0, 0, 0, 0], "- 2 x\n"),
    (6, #[3, -1, 2, 5, -4, 1, 4], "4 x^6 + x^5 - 4 x^4 + 5 x^3 + 2 x^2 - x + 3\n"),
    (6, #[0, 0, 1, 0, 0, 0, -12], "- 12 x^6 + x^2\n"),
    (6, #[-123456789012345678901, 2, -3, 1, 4, -1, 98765432109876543210],
      "98765432109876543210 x^6 - x^5 + 4 x^4 + x^3 - 3 x^2 + 2 x - 123456789012345678901\n"),
    (6, #[0, 0, 0, 0, 0, 0, 0], "\n"), (0, #[7, 1, 1, 1, 1, 1, 1], "7\n"),
    (2, #[0, 0, -1, 1, 1, 1, 1], "- x^2\n"), (6, #[1, 0, 0, 0, 0, 0, 0], "1\n"),
    (6, #[0, 0, 0, 0, 0, 0, 1], "x^6\n"), (6, #[0, 0, 0, 0, 0, 0, -1], "- x^6\n")] :
    List (Nat × Array Int × String)).all fun (d, cs, r) ↦ (printPoly cs d).run == r

end Printf

end JPoints

end
