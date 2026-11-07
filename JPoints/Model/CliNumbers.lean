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
# The numbers of the command line of `j-points`

`j-points` reads three kinds of numbers on its command line: the coefficients of the curve, which
`scan_mpz` reads one after the other from the first argument, integers of any size; the height
bound and the values of the options, C `long`s that `scan_long` reads with `strtol` of the C
library; and the constants of the cost model of the option `-c`, doubles that `set_costs` reads
with `strtod`. This file models `scan_long`, and the two functions of glibc as they behave in the C
locale, in which `j-points` runs: `strtol` in base 10, and `strtod` with its whole grammar (decimal
and hexadecimal constants, infinities, NaNs with their payloads), its rounding to nearest, the
number of characters that it reads and the cases in which it sets `ERANGE`, which `set_costs` uses.
`scan_mpz`, which exits through `error(3)` on a malformed integer, is modeled with the errors of
`read_input` (`JPoints.Cli.scanMpz`).

## Main definitions

* `JPoints.Cli.isSpace`: white space for `isspace` in the C locale.
* `JPoints.Cli.strtol`, `JPoints.Cli.scanLong`: a C `long` at the start of a string, as `strtol`
  reads it in base 10 and as `scan_long` takes it.
* `JPoints.Cli.strtod`: the double at the start of a string as `strtod` reads it, the number of
  characters that it reads and whether it sets `ERANGE` (`JPoints.Cli.underflows`).

## Implementation notes

A C string is a list of characters, the rest of the string from the pointer, and its terminating
NUL the end of the list: the arguments of a command line contain no NUL. The functions of the C
library examine only ASCII characters (white space, signs, digits, letters, the point and the
parentheses), and none of them reads past another character, so that the characters of a list
correspond to the bytes of the C string as far as either is read. A pointer that a function
returns is the rest of the string from it (`JPoints.Cli.scanMpz`), and the end pointer of `strtol`
and `strtod` is the number of characters read from the start. The double that `strtod` reads is the
double nearest to the exact value of the constant (`JPoints.Double.ofRatio`, and
`JPoints.Double.ofDyadic` for a hexadecimal constant), which glibc computes, with the size decided
by bounds before a power of 10 or 2 is expanded, so that a constant with a huge exponent costs no
more than another; whether it sets `ERANGE` is decided on the same exact value.

## References

Adapted from `Ratpoints/Model/CliNumbers.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

namespace JPoints

namespace Cli

/-! ### Characters and digits -/

/-- Whether `ch` is white space for `isspace` in the C locale: a space, or a character from the tab
`\t` to the carriage return `\r` (tab, line feed, vertical tab, form feed, carriage return). Core's
`Char.isWhitespace` leaves out the vertical tab and the form feed. -/
def isSpace (ch : Char) : Bool := ch == ' ' || '\t' ≤ ch && ch ≤ '\r'

/-- The value of the hexadecimal digit `ch`: `0` to `9` for the decimal digits, and `10` to `15`
for `a` to `f` and for `A` to `F`. -/
def digitValue (ch : Char) : Nat :=
  if ch.isDigit then ch.toNat - '0'.toNat
  else if 'a' ≤ ch && ch ≤ 'f' then ch.toNat - 'a'.toNat + 10
  else ch.toNat - 'A'.toNat + 10

/-- The natural number that the digits `ds` give in the base `b`. -/
def natOfDigitsIn (b : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun n ch ↦ b * n + digitValue ch) 0

/-- The optional sign at the start of `s`, as `strtol` and `strtod` read it: whether it is `-`, the
characters after it, and its length, `1` for a sign `-` or `+` and `0` for none. -/
def splitSign (s : List Char) : Bool × List Char × Nat :=
  match s with
  | '-' :: r => (true, r, 1)
  | '+' :: r => (false, r, 1)
  | r => (false, r, 0)

/-! ### Integers -/

/-- What `strtol` of glibc does with the string `s` in base 10, in the C locale: it reads C white
space (`JPoints.Cli.isSpace`), an optional sign (`JPoints.Cli.splitSign`) and the maximal run of
decimal digits after it, and returns the integer that they denote clamped to the range of a `long`,
`-2⁶³` to `2⁶³ - 1`, the number of characters that it read (the end pointer minus `s`), and whether
it set `errno` to `ERANGE`, which it does when it clamps. Without a digit it reads nothing: the
value `0`, no character, no error. `j-points.c` defines `_GNU_SOURCE`, so that `j-points` calls it
as `__isoc23_strtol` of glibc, which reads a prefix `0b` in the bases 0 and 2 only and is `strtol`
in base 10. -/
def strtol (s : List Char) : Int × Nat × Bool :=
  let w := (s.takeWhile isSpace).length
  let (neg, t, g) := splitSign (s.drop w)
  let ds := t.takeWhile Char.isDigit
  if ds.isEmpty then (0, 0, false)
  else
    let n : Int := natOfDigitsIn 10 ds
    let v := if neg then -n else n
    let l := w + g + ds.length
    if v < -2 ^ 63 then (-2 ^ 63, l, true)
    else if 2 ^ 63 ≤ v then (2 ^ 63 - 1, l, true)
    else (v, l, false)

/-- `scan_long` of `j-points.c`: the `long` at the start of `s` that `strtol` reads in base 10
(`JPoints.Cli.strtol`), when it reads a number (the end pointer is not `s`) and does not set
`ERANGE`; the rest of `s` is ignored, so that `"100x"` is `100` and `"1e3"` is `1`.

C: `j-points.c:548-554`

Deviation: `some v` for the return value `1` with the `long` `v` written through the pointer, and
`none` for the return value `0`, on which every caller exits, so that the `long` written then is
never read; the flag of `JPoints.Cli.strtol` for `errno`, which `scan_long` clears before the call;
an `Int` for the `long`. -/
def scanLong (s : List Char) : Option Int :=
  let (v, n, erange) := strtol s
  if n != 0 && !erange then some v else none

/-! ### Doubles -/

/-- The mantissa of a floating constant at the start of `s`, as `strtod` reads it, its digits those
that satisfy `isDigit`: a maximal run of digits, then optionally a point and a maximal run of
digits; the digits without the point, the number of those after the point, and the number of
characters, the point included. -/
def floatMantissa (isDigit : Char → Bool) (s : List Char) : List Char × Nat × Nat :=
  let a := s.takeWhile isDigit
  match s.drop a.length with
  | '.' :: r =>
    let b := r.takeWhile isDigit
    (a ++ b, b.length, a.length + 1 + b.length)
  | _ => (a, 0, a.length)

/-- The exponent of a floating constant at the start of `s`, as `strtod` reads it: a character of
`marks` (`e` and `E`, or `p` and `P`), an optional sign and a nonempty maximal run of decimal
digits, the integer that they denote and the number of characters; `(0, 0)` when `s` does not start
with one: then `strtod` reads no exponent, not even its character of `marks`. -/
def floatExponent (marks : List Char) (s : List Char) : Int × Nat :=
  match s with
  | x :: r =>
    let (neg, t, g) := splitSign r
    let ds := t.takeWhile Char.isDigit
    if marks.contains x && !ds.isEmpty then
      let e : Int := natOfDigitsIn 10 ds
      (if neg then -e else e, 1 + g + ds.length)
    else (0, 0)
  | [] => (0, 0)

/-- Whether the positive fraction `n / d` underflows when glibc's `strtod` rounds it to a double,
so that it sets `errno` to `ERANGE`: the value is tiny, below `2 ^ (-1022)` even when it is rounded
to 53 bits with an unbounded exponent, which holds below `2 ^ (-1022) - 2 ^ (-1076)`, and the
rounding is inexact, the value not a multiple of `2 ^ (-1074)`, the last place of the subnormals.
This is the test of `round_and_return` in `stdlib/strtod_l.c` of glibc, which decides tininess after
rounding on x86-64 (`TININESS_AFTER_ROUNDING` of `sysdeps/x86/tininess.h`): a value from
`2 ^ (-1022) - 2 ^ (-1075)` up to below `2 ^ (-1022) - 2 ^ (-1076)` underflows although it rounds to
the normal double `2 ^ (-1022)`, while an exact subnormal does not. -/
def underflows (n d : Nat) : Bool :=
  n * 2 ^ 1076 < (2 ^ 54 - 1) * d && n * 2 ^ 1074 % d != 0

/-- The double nearest to `±m 2 ^ t`, the sign `-` for `neg`, and whether `strtod` sets `ERANGE`
for it: its size decided first by the length of `m` in bits, an infinity when `m 2 ^ t ≥ 2 ^ 1024`
and a zero when `m 2 ^ t < 2 ^ (-1075)`, both with `ERANGE`, and otherwise the rounding of
`JPoints.Double.ofDyadic`, whose shift is then bounded by the length of `m` and the range of the
doubles, with `ERANGE` for an infinity and for an underflow (`JPoints.Cli.underflows`). -/
def nearestBinary (neg : Bool) (m : Nat) (t : Int) : Double × Bool :=
  if m = 0 then (.ofRatio neg 0 1, false)
  else if 1024 ≤ m.log2 + t then (if neg then Double.huge.neg else Double.huge, true)
  else if m.log2 + 1 + t ≤ -1075 then (.ofRatio neg 0 1, true)
  else
    let x := Double.ofDyadic neg m t
    (x, x.isInf || underflows (m * 2 ^ t.toNat) (2 ^ (-t).toNat))

/-- The double nearest to `±m 10 ^ t`, the sign `-` for `neg` (`JPoints.Double.ofRatio`), and
whether `strtod` sets `ERANGE` for it, with two shortcuts by the bounds `2 ^ (log₂ m) ≤ m` and
`2 ^ (3 u) ≤ 10 ^ u`: for `t ≥ 0` an infinity when they put `m 10 ^ t` at or above `2 ^ 1024`, for
`t < 0` a zero when they put it below `2 ^ (-1075)`, both with `ERANGE`. Otherwise the power of 10
is expanded and the quotient rounded by `JPoints.Double.ofRatio`, which also gives the infinities
and the zeros that the shortcuts miss, with `ERANGE` for an infinity and for an underflow
(`JPoints.Cli.underflows`); the exponent is then bounded by the length of `m` in bits and the range
of the doubles. -/
def nearestDecimal (neg : Bool) (m : Nat) (t : Int) : Double × Bool :=
  if m = 0 then (.ofRatio neg 0 1, false)
  else if 0 ≤ t then
    if 1024 ≤ m.log2 + 3 * t then (if neg then Double.huge.neg else Double.huge, true)
    else
      let x := Double.ofRatio neg (m * 10 ^ t.toNat) 1
      (x, x.isInf)
  else if m.log2 + 1076 ≤ 3 * -t then (.ofRatio neg 0 1, true)
  else
    let x := Double.ofRatio neg m (10 ^ (-t).toNat)
    (x, x.isInf || underflows m (10 ^ (-t).toNat))

/-- The floating constant at the start of `t`, after its sign and, for a hexadecimal one (`hex`),
after its prefix `0x`, as `strtod` reads it: the mantissa (`JPoints.Cli.floatMantissa`) in decimal
or hexadecimal digits, which must have a digit, then optionally the exponent
(`JPoints.Cli.floatExponent`), `e` or `E` and a power of 10, or `p` or `P` and a power of 2. The
double nearest to its exact value `±m 10 ^ (e - k)`, or `±m 2 ^ (e - 4 k)` for a hexadecimal
constant, of the digits `m` of the mantissa, the number `k` of them after the point and the
exponent `e`, with ties to even (`JPoints.Cli.nearestDecimal`, `JPoints.Cli.nearestBinary`), the
sign `-` for `neg`, the number of characters of the constant, and whether `strtod` sets `ERANGE` for
it; none when the mantissa has no digit. -/
def floatConstant (hex neg : Bool) (t : List Char) : Option (Double × Nat × Bool) :=
  let (ds, k, l) := floatMantissa (if hex then Char.isHexDigit else Char.isDigit) t
  if ds.isEmpty then none
  else
    let (e, el) := floatExponent (if hex then ['p', 'P'] else ['e', 'E']) (t.drop l)
    let (x, erange) := if hex then nearestBinary neg (natOfDigitsIn 16 ds) (e - 4 * k)
      else nearestDecimal neg (natOfDigitsIn 10 ds) (e - k)
    some (x, l + el, erange)

/-- The payload that glibc gives to the NaN of `nan(n)`: the number that `strtoull` reads from the
characters `n` in base 0 when it reads all of them (decimal digits, octal digits after a `0`,
hexadecimal ones after `0x` or `0X`), `2⁶⁴ - 1` when that number is larger, and `0` (the payload
of the default NaN) when `strtoull` stops before the end of `n`. -/
def nanPayload (n : List Char) : Nat :=
  let v : Option Nat :=
    match n with
    | '0' :: x :: r =>
      if x == 'x' || x == 'X' then
        if !r.isEmpty && r.all Char.isHexDigit then some (natOfDigitsIn 16 r) else none
      else if (x :: r).all fun ch ↦ '0' ≤ ch && ch ≤ '7' then some (natOfDigitsIn 8 (x :: r))
      else none
    | _ => if n.all Char.isDigit then some (natOfDigitsIn 10 n) else none
  min (v.getD 0) (2 ^ 64 - 1)

/-- The NaN that `strtod` of glibc reads from `nan` and the characters `s` after it: for `(n)`,
with `n` a run of ASCII letters, digits and `_`, the quiet NaN `0x7ff8000000000000` with the low
51 bits of the payload of `n` (`JPoints.Cli.nanPayload`) in its fraction, and the length of `(n)`;
for anything else the quiet NaN itself, and `0`, as `strtod` then reads only `nan`. -/
def nanSuffix (s : List Char) : Double × Nat :=
  let quiet : UInt64 := 0x7ff8000000000000
  match s with
  | '(' :: r =>
    let n := r.takeWhile fun ch ↦ ch.isAlphanum || ch == '_'
    if (r.drop n.length).head? == some ')' then
      (⟨quiet ||| (UInt64.ofNat (nanPayload n) &&& 0x7ffffffffffff)⟩, n.length + 2)
    else (⟨quiet⟩, 0)
  | _ => (⟨quiet⟩, 0)

/-- The number at the start of `t`, the string after the white space and the sign (`-` for `neg`),
as `strtod` of glibc reads it: the longest of `inf` and `infinity` (in any case), `nan` and
`nan(n)` (in any case, `JPoints.Cli.nanSuffix`), a decimal floating constant, and `0x` or `0X` with
a hexadecimal one (`JPoints.Cli.floatConstant`); its double, negated for the sign `-` (also an
infinity, a NaN or a zero), the number of characters read, and whether `strtod` sets `ERANGE`,
which only a floating constant can make it do; for `0x` without a hexadecimal constant after it, the
zero of the sign and the one character `0`; none when `t` does not start with a number. -/
def strtodAfterSign (neg : Bool) (t : List Char) : Option (Double × Nat × Bool) :=
  let low := (t.take 8).map Char.toLower
  if low.take 3 == "inf".toList then
    some (if neg then Double.huge.neg else Double.huge, if low == "infinity".toList then 8 else 3,
      false)
  else if low.take 3 == "nan".toList then
    let (x, n) := nanSuffix (t.drop 3)
    some (if neg then x.neg else x, 3 + n, false)
  else
    let hex := match t with
      | '0' :: x :: _ => x == 'x' || x == 'X'
      | _ => false
    if hex then
      match floatConstant true neg (t.drop 2) with
      | some (x, n, erange) => some (x, 2 + n, erange)
      | none => some (if neg then Double.zero.neg else Double.zero, 1, false)
    else floatConstant false neg t

/-- What `strtod` of glibc does with the string `s` in the C locale: it reads C white space
(`JPoints.Cli.isSpace`), an optional sign (`JPoints.Cli.splitSign`) and a number
(`JPoints.Cli.strtodAfterSign`), and returns the double of the number, the number of characters
that it read (the end pointer minus `s`) and whether it set `errno` to `ERANGE`. The double of a
floating constant is the double nearest to its exact value, ties to even, so that a value of at
least `2 ^ 1024 - 2 ^ 970`, halfway between the largest double and `2 ^ 1024`, gives an infinity
and a tiny one a subnormal or a zero; `strtod` sets `ERANGE` for a constant that it rounds to an
infinity and for one that underflows (`JPoints.Cli.underflows`), and leaves `errno` alone
otherwise, also for `inf` and `nan`. Without a number it reads nothing: the double `+0.0`, no
character and no error, also after white space or a sign. -/
def strtod (s : List Char) : Double × Nat × Bool :=
  let w := (s.takeWhile isSpace).length
  let (neg, t, g) := splitSign (s.drop w)
  match strtodAfterSign neg t with
  | some (x, n, erange) => (x, w + g + n, erange)
  | none => (Double.zero, 0, false)

/-! ### Examples

The expected values are those that a test program prints for glibc's `strtol` and `strtod` and for
`scan_long` of `j-points.c`: the double that `strtod` reads by its bits, the end pointers as the
numbers of characters read, and whether `errno` is `ERANGE` after the call. -/

-- `isspace` in the C locale: the bytes 9 to 13 and 32.
#guard (List.range 256).filter (fun n ↦ isSpace (Char.ofNat n)) == [9, 10, 11, 12, 13, 32]

-- `strtol` in base 10: the white space, the sign, the digits and nothing after them, no
-- conversion, the bounds of a `long` and `ERANGE` beyond them, and characters that are not ASCII.
#guard ([
    ("", 0, 0, false), (" ", 0, 0, false), ("+", 0, 0, false), ("-", 0, 0, false),
    ("0", 0, 1, false), ("-0", 0, 2, false), ("+0", 0, 2, false),
    (" \t\n\x0b\x0c\r42", 42, 8, false), ("42x", 42, 2, false), ("1e3", 1, 1, false),
    ("0x10", 0, 1, false), ("5.", 5, 1, false),
    ("9223372036854775807", 9223372036854775807, 19, false),
    ("9223372036854775808", 9223372036854775807, 19, true),
    ("-9223372036854775808", -9223372036854775808, 20, false),
    ("-9223372036854775809", -9223372036854775808, 20, true),
    ("99999999999999999999999", 9223372036854775807, 23, true),
    ("-99999999999999999999999", -9223372036854775808, 24, true), ("00012", 12, 5, false),
    ("+-1", 0, 0, false), ("- 1", 0, 0, false), ("1 2", 1, 1, false), ("\u0661\u0662", 0, 0, false),
    ("\u00a01", 0, 0, false), ("-1e400", -1, 2, false)] :
    List (String × Int × Nat × Bool)).all fun (s, v, n, e) ↦ strtol s.toList == (v, n, e)

-- `scan_long`: the same strings.
#guard ([
    ("", none), (" ", none), ("+", none), ("-", none), ("0", some 0), ("-0", some 0),
    ("+0", some 0), (" \t\n\x0b\x0c\r42", some 42), ("42x", some 42), ("1e3", some 1),
    ("0x10", some 0), ("5.", some 5), ("9223372036854775807", some 9223372036854775807),
    ("9223372036854775808", none), ("-9223372036854775808", some (-9223372036854775808)),
    ("-9223372036854775809", none), ("99999999999999999999999", none),
    ("-99999999999999999999999", none), ("00012", some 12), ("+-1", none), ("- 1", none),
    ("1 2", some 1), ("\u0661\u0662", none), ("\u00a01", none), ("-1e400", some (-1))] :
    List (String × Option Int)).all fun (s, v) ↦ scanLong s.toList == v

-- `strtod`, the grammar and the end pointer: signs, points, exponents without digits, the prefix
-- `0x` without a hexadecimal constant, zeros, white space, and what follows a constant; no
-- `ERANGE`.
#guard ([
    ("", 0x0000000000000000, 0), (" ", 0x0000000000000000, 0), ("+", 0x0000000000000000, 0),
    ("-", 0x0000000000000000, 0), (".", 0x0000000000000000, 0), ("-.", 0x0000000000000000, 0),
    ("+.5", 0x3fe0000000000000, 3), ("-.5", 0xbfe0000000000000, 3), ("5.", 0x4014000000000000, 2),
    ("1.e5", 0x40f86a0000000000, 4), (".e5", 0x0000000000000000, 0), ("1e", 0x3ff0000000000000, 1),
    ("1e+", 0x3ff0000000000000, 1), ("1ex", 0x3ff0000000000000, 1), ("1E-5", 0x3ee4f8b588e368f1, 4),
    ("0x", 0x0000000000000000, 1), ("-0x", 0x8000000000000000, 2), ("0x.", 0x0000000000000000, 1),
    ("0x.8", 0x3fe0000000000000, 4), ("0xg", 0x0000000000000000, 1), ("0x0", 0x0000000000000000, 3),
    ("0x0.", 0x0000000000000000, 4), ("0x0p", 0x0000000000000000, 3),
    ("0x0p5", 0x0000000000000000, 5), ("0xp5", 0x0000000000000000, 1),
    ("0x.p5", 0x0000000000000000, 1), ("0x1p", 0x3ff0000000000000, 3),
    ("0x1p-1", 0x3fe0000000000000, 6), ("0x1.8p1", 0x4008000000000000, 7),
    ("0x1e5", 0x407e500000000000, 5), ("0x0x1", 0x0000000000000000, 3),
    ("-0xz", 0x8000000000000000, 2), ("0x00z", 0x0000000000000000, 4),
    ("0x.0", 0x0000000000000000, 4), ("0x1.p1", 0x4000000000000000, 6),
    ("-0x1.8P-1", 0xbfe8000000000000, 9), ("00", 0x0000000000000000, 2),
    ("-0", 0x8000000000000000, 2), ("-00x", 0x8000000000000000, 3), ("0e5", 0x0000000000000000, 3),
    ("0e", 0x0000000000000000, 1), ("00.5e1", 0x4014000000000000, 6),
    ("0.e5", 0x0000000000000000, 4), ("0.0e+1x", 0x0000000000000000, 6),
    ("12.34.56", 0x4028ae147ae147ae, 5), (" +1", 0x3ff0000000000000, 3),
    ("+-1", 0x0000000000000000, 0), ("- 1", 0x0000000000000000, 0), ("1,5", 0x3ff0000000000000, 1),
    ("1.5,AND=2", 0x3ff8000000000000, 3), ("\t\n\x0b\x0c\r 1", 0x3ff0000000000000, 7),
    ("é1", 0x0000000000000000, 0), ("\u00a01", 0x0000000000000000, 0)] :
    List (String × UInt64 × Nat)).all fun (s, b, n) ↦
  let (x, m, e) := strtod s.toList
  x.bits == b && m == n && !e

-- `strtod`, the infinities and the NaNs: the longest word read, any case, the signs, and the
-- payloads of `nan(n)` (decimal, octal, hexadecimal, clamped, masked to 51 bits, or none); no
-- `ERANGE`.
#guard ([
    ("inf", 0x7ff0000000000000, 3), ("INF", 0x7ff0000000000000, 3),
    ("infinity", 0x7ff0000000000000, 8), ("INFINITY", 0x7ff0000000000000, 8),
    ("infinit", 0x7ff0000000000000, 3), ("infinityx", 0x7ff0000000000000, 8),
    ("-inf", 0xfff0000000000000, 4), ("+Infinity", 0x7ff0000000000000, 9),
    ("in", 0x0000000000000000, 0), (" -iNfInItY", 0xfff0000000000000, 10),
    ("infinity(", 0x7ff0000000000000, 8), ("nan", 0x7ff8000000000000, 3),
    ("NAN", 0x7ff8000000000000, 3), ("-nan", 0xfff8000000000000, 4),
    ("nan(", 0x7ff8000000000000, 3), ("nan()", 0x7ff8000000000000, 5),
    ("nan(0x5)", 0x7ff8000000000005, 8), ("nan(5)", 0x7ff8000000000005, 6),
    ("nan(017)", 0x7ff800000000000f, 8), ("nan(08)", 0x7ff8000000000000, 7),
    ("nan(0x)", 0x7ff8000000000000, 7), ("nan(abc)", 0x7ff8000000000000, 8),
    ("nan(_)", 0x7ff8000000000000, 6), ("nan(1_2)", 0x7ff8000000000000, 8),
    ("nan(0b101)", 0x7ff8000000000000, 10), ("nan(18446744073709551616)", 0x7fffffffffffffff, 25),
    ("nan(0x7ffffffffffff)", 0x7fffffffffffffff, 20),
    ("nan(0x8000000000000)", 0x7ff8000000000000, 20), ("nan( 1)", 0x7ff8000000000000, 3),
    ("nan(-1)", 0x7ff8000000000000, 3), ("nan(1", 0x7ff8000000000000, 3),
    ("-nan(7)", 0xfff8000000000007, 7), ("+nan(0X1f)", 0x7ff800000000001f, 10),
    ("nan(0xAbC)", 0x7ff8000000000abc, 10), ("NaN(zz)", 0x7ff8000000000000, 7),
    ("nan(1)x", 0x7ff8000000000001, 6), ("nAn(0XfFfFfFfFfFfFfFfF)", 0x7fffffffffffffff, 23),
    ("nan(02000000000000000000000)", 0x7fffffffffffffff, 28)] :
    List (String × UInt64 × Nat)).all fun (s, b, n) ↦
  let (x, m, e) := strtod s.toList
  x.bits == b && m == n && !e

-- `strtod`, the rounding and `ERANGE`: ties to even, the boundaries of the subnormals, of the
-- normal doubles and of the infinities with the numbers on either side, the values just below
-- `2 ^ (-1022)` that round to it with and without `ERANGE`, exact subnormals without it, huge
-- exponents, hexadecimal constants.
#guard ([
    ("0.1", 0x3fb999999999999a, 3, false), ("1e400", 0x7ff0000000000000, 5, true),
    ("-1e400", 0xfff0000000000000, 6, true), ("1e-400", 0x0000000000000000, 6, true),
    ("-1e-400", 0x8000000000000000, 7, true),
    ("2.4703282292062327e-324", 0x0000000000000000, 23, true),
    ("2.4703282292062328e-324", 0x0000000000000001, 23, true),
    ("4.9406564584124654e-324", 0x0000000000000001, 23, true),
    ("7.4109846876186982e-324", 0x0000000000000002, 23, true),
    ("1e-320", 0x00000000000007e8, 6, true),
    ("2.2250738585072011e-308", 0x000fffffffffffff, 23, true),
    ("2.2250738585072012e-308", 0x0010000000000000, 23, true),
    ("2.225073858507201e-308", 0x000fffffffffffff, 22, true),
    ("2.2250738585072013e-308", 0x0010000000000000, 23, false),
    ("2.2250738585072014e-308", 0x0010000000000000, 23, false),
    ("0x1.fffffffffffffp-1023", 0x0010000000000000, 23, true),
    ("0x1.fffffffffffff4p-1023", 0x0010000000000000, 24, true),
    ("0x1.fffffffffffff8p-1023", 0x0010000000000000, 24, false),
    ("0x1.fffffffffffffcp-1023", 0x0010000000000000, 24, false),
    ("0x1p-1022", 0x0010000000000000, 9, false), ("0x1p-1030", 0x0000100000000000, 9, false),
    ("1.7976931348623158e308", 0x7fefffffffffffff, 22, false),
    ("1.7976931348623159e308", 0x7ff0000000000000, 22, true),
    ("1.797693134862315807937289714053e308", 0x7fefffffffffffff, 36, false),
    ("1.797693134862315807937289714054e308", 0x7ff0000000000000, 36, true),
    ("9007199254740993", 0x4340000000000000, 16, false),
    ("9007199254740995", 0x4340000000000002, 16, false),
    ("123456789012345678901234567890e-30", 0x3fbf9add3746f65f, 34, false),
    ("1e99999999999999999999999999", 0x7ff0000000000000, 28, true),
    ("1e-99999999999999999999999999", 0x0000000000000000, 29, true),
    ("0e99999999999999999999", 0x0000000000000000, 22, false),
    ("-0e-99999999999999999999", 0x8000000000000000, 24, false),
    ("1e0000000000000000000000000001", 0x4024000000000000, 30, false),
    ("0.000000000000000000000000000001e330", 0x7e37e43c8800759c, 36, false),
    ("0x1.fffffffffffff8p1023", 0x7ff0000000000000, 23, true),
    ("0x1.fffffffffffff7p1023", 0x7fefffffffffffff, 23, false),
    ("0x1p-1075", 0x0000000000000000, 9, true),
    ("0x1.0000000000001p-1075", 0x0000000000000001, 23, true),
    ("0x1p-1074", 0x0000000000000001, 9, false), ("0x1p1024", 0x7ff0000000000000, 8, true),
    ("0x.00000000000000000000001p0", 0x3a30000000000000, 28, false),
    ("0x1p99999999999999999999", 0x7ff0000000000000, 24, true),
    ("0x1p-99999999999999999999", 0x0000000000000000, 25, true),
    ("0x0p99999999999999999999", 0x0000000000000000, 24, false),
    ("0x10000000000000000000000001p-50", 0x4310000000000000, 32, false),
    ("0x1.000000000000080000000000000000001p0", 0x3ff0000000000001, 39, false),
    ("0x1.00000000000008p0", 0x3ff0000000000000, 20, false),
    ("0x1.00000000000018p0", 0x3ff0000000000002, 20, false),
    ("0x.8p-1074", 0x0000000000000000, 10, true),
    ("0x.8000001p-1074", 0x0000000000000001, 16, true),
    ("0xffffffffffffffffffffp-80", 0x3ff0000000000000, 26, false),
    ("1e999", 0x7ff0000000000000, 5, true)] :
    List (String × UInt64 × Nat × Bool)).all fun (s, b, n, e) ↦
  let (x, m, r) := strtod s.toList
  x.bits == b && m == n && r == e

-- `strtod`, long mantissas: 400 zeros after the point, or after a digit; `ERANGE` for the zero.
#guard
  let z := String.ofList (List.replicate 400 '0')
  ([("0." ++ z ++ "1e400", 0x3fb999999999999a, 407), ("0." ++ z ++ "1e-1", 0x0000000000000000, 406),
      ("1" ++ z ++ "e-400", 0x3ff0000000000000, 406)] : List (String × UInt64 × Nat)).all
    fun (s, b, n) ↦
      let (x, m, e) := strtod s.toList
      x.bits == b && m == n && e == (b == 0)

end Cli

end JPoints

end
