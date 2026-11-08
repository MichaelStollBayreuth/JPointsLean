/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The doubles of the C code

The C code of `j-points` computes with `double`s where they decide what is searched: the analysis of
the tube of the bound on the fourth coordinate, the excluded ranges of the real region, the ends of
the intervals of the Sturm step, two reciprocals of the index arithmetic of the sieve and the counts
of some loops; and its cost model computes with them, which the model does in Lean's `Float`
(`JPoints.Double.toFloat`, `JPoints.Double.ofFloat`). The model holds a double as its IEEE 754
binary64 bits (`JPoints.Double`), with the operations as functions on the bits.

## Main definitions

* `JPoints.Double`: a C `double`, by its bits.
* `JPoints.Double.isNaN`, `JPoints.Double.isInf`, `JPoints.Double.isFinite`,
  `JPoints.Double.isNormal`: the NaNs, the infinities, the finite doubles and the normal ones.
* `JPoints.Double.lt`, `JPoints.Double.le`, `JPoints.Double.beq`: the comparisons `<`, `<=`
  and `==` of the C language on doubles.
* `JPoints.Double.neg`, `JPoints.Double.fabs`: the negation and the absolute value.
* `JPoints.Double.toDyadic`, `JPoints.Double.ofDyadic`: the exact value of a finite double, and
  the double nearest to a dyadic number.
* `JPoints.Double.toRat`, `JPoints.Double.ofRatio`: the exact value of a finite double as a
  rational number, and the double nearest to a fraction.
* `JPoints.Double.assemble`, `JPoints.Double.ofSignificand`: the double of a significand and
  the exponent of its last place, the last step of both roundings.
* `JPoints.Double.toInt64`: the conversion `(long)x` of a double.
* `JPoints.Double.ldexp`, `JPoints.Double.nextUp`, `JPoints.Double.nextDown`: the functions of the
  C library.
* `JPoints.Double.toFloat`, `JPoints.Double.ofFloat`: a double as a value of Lean's `Float`, for
  the cost model, and back.
* `JPoints.Double.printFixed`: a double as `printf` prints it under `%.pf`.

## Implementation notes

Each operation does what the operation of the C language or the C library does to a double on the
platforms of `j-points` (IEEE 754 binary64 with rounding to nearest, ties to even, as gcc and glibc
implement them): the comparisons, in which a NaN is unordered and `-0.0` equals `0.0`, the negation
and `fabs`, which act on the sign bit, the conversions, `ldexp` and `nextafter` towards `±HUGE_VAL`,
but for a signalling NaN, which glibc's `ldexp` and `nextafter` return quieted and the model as it
is (no operation of the program makes a signalling NaN). The exact value of a finite double is
`m 2 ^ e` for the integers of `JPoints.Double.toDyadic`, and a dyadic number is rounded to a double,
to nearest with ties to even, by `JPoints.Double.ofDyadic`, a fraction by `JPoints.Double.ofRatio`
(for `strtod`, which the program uses).

## References

Adapted from `Ratpoints/Model/Double.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

namespace JPoints

/-- A C `double`, by its IEEE 754 binary64 bits: the sign bit (bit 63), the biased exponent (bits 52
to 62) and the fraction (bits 0 to 51). Equality of the bits is not the `==` of the C language,
under which `-0.0` equals `0.0` and a NaN equals nothing; that is `JPoints.Double.beq`. -/
structure Double where
  /-- The 64 bits of the double. -/
  bits : UInt64
  deriving Inhabited, Repr

namespace Double

/-- `0.0`. -/
def zero : Double := ⟨0⟩

/-- `HUGE_VAL` of `math.h`, which is `+∞` for the doubles of IEEE 754. -/
def huge : Double := ⟨0x7ff0000000000000⟩

/-- The double `x` as a value of Lean's `Float`, the IEEE 754 binary64 type with the arithmetic of
the platform, by its bits: the doubles of the model enter the arithmetic of the cost model so. A NaN
becomes the one NaN of Lean's `Float`, whose bits `JPoints.Double.ofFloat` gives as
`0x7ff8000000000000`: its sign and its payload are lost. -/
def toFloat (x : Double) : Float := Float.ofBits x.bits

/-- The value `x` of Lean's `Float` as a double, by its bits: a double of the cost model where the
model needs it as a double. Every NaN becomes `0x7ff8000000000000`, as Lean's `Float` has one NaN.
-/
def ofFloat (x : Float) : Double := ⟨x.toBits⟩

/-- The sign bit. -/
def signBit (x : Double) : Bool := x.bits >>> 63 == 1

/-- The biased exponent, from `0` (zeros and subnormals) to `2047` (infinities and NaNs). -/
def expField (x : Double) : Nat := ((x.bits >>> 52) &&& 0x7ff).toNat

/-- The fraction, the 52 low bits. -/
def fracField (x : Double) : Nat := (x.bits &&& 0xfffffffffffff).toNat

/-- Whether `x` is a NaN, as `isnan` of `math.h` decides it: the largest exponent and a fraction
that is not zero. -/
def isNaN (x : Double) : Bool := x.expField == 2047 && x.fracField != 0

/-- Whether `x` is `+∞` or `-∞`, as `isinf` of `math.h` decides it: the largest exponent and the
fraction zero. -/
def isInf (x : Double) : Bool := x.expField == 2047 && x.fracField == 0

/-- Whether `x` is `0.0` or `-0.0`. -/
def isZero (x : Double) : Bool := x.bits &&& 0x7fffffffffffffff == 0

/-- Whether `x` is finite, as `isfinite` of `math.h` decides it: an exponent below the largest, so
neither an infinity nor a NaN. -/
def isFinite (x : Double) : Bool := x.expField != 2047

/-- Whether `x` is a normal double, as `isnormal` of `math.h` decides it: an exponent neither the
smallest nor the largest, so neither a zero, a subnormal, an infinity nor a NaN. -/
def isNormal (x : Double) : Bool := x.expField != 0 && x.expField != 2047

/-- The key of a double that is not a NaN in the order of the values: the bits without the sign
bit, negated when the sign bit is set, which increase with the value for doubles of either sign,
the infinities included, and are `0` for both zeros. -/
def orderValue (x : Double) : Int :=
  let a : Int := (x.bits &&& 0x7fffffffffffffff).toNat
  if x.signBit then -a else a

/-- `x < y` of the C language on doubles: false when either is a NaN, and otherwise the order of
the values, in which `-0.0` and `0.0` are equal. -/
def lt (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue < y.orderValue

/-- `x <= y` of the C language on doubles: false when either is a NaN, and otherwise the order of
the values, in which `-0.0` and `0.0` are equal. -/
def le (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue ≤ y.orderValue

/-- `x == y` of the C language on doubles: false when either is a NaN, and otherwise the equality
of the values, under which `-0.0` and `0.0` are equal. -/
def beq (x y : Double) : Bool := !x.isNaN && !y.isNaN && x.orderValue == y.orderValue

/-- The negation `-x` of the C language on a double: the sign bit flipped, also for a zero, an
infinity and a NaN. -/
def neg (x : Double) : Double := ⟨x.bits ^^^ 0x8000000000000000⟩

/-- `fabs` of `math.h`: the sign bit cleared. -/
def fabs (x : Double) : Double := ⟨x.bits &&& 0x7fffffffffffffff⟩

/-- The exact value `m 2 ^ e` of a finite double `x`, as the pair `(m, e)`: for a normal `x` the
significand `2 ^ 52 + f` of the fraction `f` with the exponent less `1075`, for a subnormal `x` or a
zero the fraction with `e = -1074`, and `m` negated when the sign bit is set (`m = 0` for both
zeros). Not meant for infinities and NaNs. -/
def toDyadic (x : Double) : Int × Int :=
  let (m, e) : Nat × Int :=
    if x.expField = 0 then (x.fracField, -1074) else (x.fracField + 2 ^ 52, x.expField - 1075)
  (if x.signBit then -(m : Int) else m, e)

/-- The exact value of a finite double `x` as a rational number, `m 2 ^ e` for the pair `(m, e)` of
`JPoints.Double.toDyadic`, as `mpq_set_d` of GMP sets it: `0` for both zeros. Not meant for
infinities and NaNs. -/
def toRat (x : Double) : Rat :=
  let (m, e) := x.toDyadic
  if 0 ≤ e then ((m * 2 ^ e.toNat : Int) : Rat) else mkRat m (2 ^ (-e).toNat)

/-- `m / 2 ^ k` rounded to the nearest integer, ties to even, and `m 2 ^ (-k)` for `k ≤ 0`. -/
def roundShift (m : Nat) (k : Int) : Nat :=
  if k ≤ 0 then m <<< (-k).toNat
  else
    let q := m >>> k.toNat
    let r := m % 2 ^ k.toNat
    let half := 2 ^ (k.toNat - 1)
    if half < r ∨ r = half ∧ q % 2 = 1 then q + 1 else q

/-- The quotient `a / b` of natural numbers, `b ≠ 0`, rounded to the nearest integer, ties to even,
as `JPoints.Double.ofRatio` rounds its quotient and `printf` of glibc rounds the exact value of a
double to the digits it prints. -/
def roundDiv (a b : Nat) : Nat :=
  if b < 2 * (a % b) ∨ 2 * (a % b) = b ∧ (a / b) % 2 = 1 then a / b + 1 else a / b

/-- The double with the sign `-` for `neg` that IEEE 754 encodes by a significand `M < 2 ^ 53` and
the exponent `q` of its last place: a subnormal or a zero with the fraction `M` for `M < 2 ^ 52`
(whose last place is `2 ^ (-1074)`), an infinity when the exponent field `q + 1075` would reach
`2047`, and otherwise a normal double with the exponent field `q + 1075` and the fraction
`M - 2 ^ 52`. -/
def assemble (neg : Bool) (M : Nat) (q : Int) : Double :=
  let s : UInt64 := if neg then 0x8000000000000000 else 0
  if M < 2 ^ 52 then ⟨s ||| M.toUInt64⟩
  else if 2047 ≤ q + 1075 then ⟨s ||| 0x7ff0000000000000⟩
  else ⟨s ||| ((q + 1075).toNat.toUInt64 <<< 52) ||| (M - 2 ^ 52).toUInt64⟩

/-- The double with the sign `-` for `neg` of a rounded significand `M ≤ 2 ^ 53` and the exponent
`q` of its last place, the last step of `JPoints.Double.ofDyadic` and `JPoints.Double.ofRatio`:
the significand `2 ^ 53`, which rounding up can reach, carried into the next exponent as `2 ^ 52`,
then the bits of `JPoints.Double.assemble`. -/
def ofSignificand (neg : Bool) (M : Nat) (q : Int) : Double :=
  let (M, q) := if M = 2 ^ 53 then (2 ^ 52, q + 1) else (M, q)
  assemble neg M q

/-- The double nearest to `±m 2 ^ e`, the sign `-` for `neg`, with ties to even, as the operations
of IEEE 754 round their exact results in the rounding mode to nearest: a signed zero for `m = 0`;
otherwise the last place `2 ^ q` of the result, `q = max (E - 52) (-1074)` for the exponent `E` with
`2 ^ E ≤ m 2 ^ e < 2 ^ (E + 1)`; `M`, the value divided by `2 ^ q` and rounded, carried into the
next exponent at `2 ^ 53`; a subnormal or a zero below `2 ^ 52`; and an infinity beyond the largest
finite double (`JPoints.Double.ofSignificand`). The proofs show that a finite result is within half
a unit in the last place of the value, the error bound of rounding to nearest
(`JPoints.Double.isRounding_ofDyadic`), and for `m ≠ 0` that the value lies strictly between the
neighbors of the result (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`); which of the two
nearest doubles a tie gives, they do not show. -/
def ofDyadic (neg : Bool) (m : Nat) (e : Int) : Double :=
  if m = 0 then ⟨if neg then 0x8000000000000000 else 0⟩
  else
    let q : Int := max (m.log2 + e - 52) (-1074)
    ofSignificand neg (roundShift m (q - e)) q

/-- The double nearest to `±n / d` for `d ≠ 0`, the sign `-` for `neg`, with ties to even, as IEEE
754 rounds an exact result in the rounding mode to nearest: a signed zero for `n = 0`; otherwise the
exponent `E` with `2 ^ E ≤ n / d < 2 ^ (E + 1)`, which the lengths of `n` and `d` in bits fix up to
one, the last place `2 ^ q` of the result, `q = max (E - 52) (-1074)`, the quotient `n / (d 2 ^ q)`
rounded to the nearest integer (`JPoints.Double.roundDiv`), carried into the next exponent at
`2 ^ 53`, a subnormal or a zero below `2 ^ 52`, and an infinity beyond the largest finite double
(`JPoints.Double.ofSignificand`). The proofs show that a finite result is within half a unit in the
last place of the value, the error bound of rounding to nearest
(`JPoints.Double.isRounding_ofRatio`), and for `n ≠ 0` that the value lies strictly between the
neighbors of the result (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`); which of the two
nearest doubles a tie gives, they do not show. -/
def ofRatio (neg : Bool) (n d : Nat) : Double :=
  if n = 0 then ⟨if neg then 0x8000000000000000 else 0⟩
  else
    let e : Int := (n.log2 : Int) - d.log2
    let atLeast : Bool := if 0 ≤ e then d * 2 ^ e.toNat ≤ n else d ≤ n * 2 ^ (-e).toNat
    let q : Int := max ((if atLeast then e else e - 1) - 52) (-1074)
    let (a, b) := if 0 ≤ q then (n, d * 2 ^ q.toNat) else (n * 2 ^ (-q).toNat, d)
    ofSignificand neg (roundDiv a b) q

/-- The conversion `(long)x` of a double `x` to a `long`, as gcc compiles it on the platforms of
`j-points`, by the instruction `cvttsd2si` of SSE2: the value truncated towards zero when the
truncation is a `long` (the finite doubles with `-2 ^ 63 ≤ x < 2 ^ 63`, the only ones for which the
C language defines the conversion), and `-2 ^ 63` (`0x8000000000000000`, the "integer indefinite"
of Intel's manuals) for all others, the infinities and the NaNs included. -/
def toInt64 (x : Double) : Int64 :=
  if x.isFinite then
    let (m, e) := x.toDyadic
    let a := if 0 ≤ e then m.natAbs <<< e.toNat else m.natAbs >>> (-e).toNat
    let t : Int := if m < 0 then -(a : Int) else a
    if -2 ^ 63 ≤ t ∧ t < 2 ^ 63 then Int64.ofInt t else Int64.minValue
  else Int64.minValue

/-- `ldexp(x, n)` of `math.h`, `x 2 ^ n`: a zero, an infinity and a NaN as they are, as glibc
returns them, but for a signalling NaN, which glibc returns quieted (by `x + x`; the program
makes no signalling NaN); otherwise the exact value of `x` times `2 ^ n` rounded to a double
(`JPoints.Double.ofDyadic`), which is exact unless it leaves the normal range, an infinity on
overflow and rounded to nearest in the subnormal range, as glibc computes it. -/
def ldexp (x : Double) (n : Int) : Double :=
  if x.isNaN || x.isInf || x.isZero then x
  else
    let (m, e) := x.toDyadic
    ofDyadic x.signBit m.natAbs (e + n)

/-- `nextafter(x, HUGE_VAL)` of `math.h`: the least double above `x`; the least subnormal for both
zeros, `+∞` for `+∞` and the largest finite double, a NaN as it is (glibc returns a signalling NaN
quieted, by `x + y`; the program makes no signalling NaN), and for a negative `x` the double towards
zero, `-0.0` above `-2 ^ (-1074)`. -/
def nextUp (x : Double) : Double :=
  if x.isNaN || x.bits == huge.bits then x
  else if x.isZero then ⟨1⟩
  else if x.signBit then ⟨x.bits - 1⟩
  else ⟨x.bits + 1⟩

/-- `nextafter(x, -HUGE_VAL)` of `math.h`: the greatest double below `x`; the least subnormal
negated for both zeros, `-∞` for `-∞` and the least finite double, a NaN as it is (glibc returns a
signalling NaN quieted, by `x + y`; the program makes no signalling NaN), and for a positive `x` the
double towards zero, `0.0` below `2 ^ (-1074)`. -/
def nextDown (x : Double) : Double :=
  if x.isNaN || x.bits == huge.neg.bits then x
  else if x.isZero then ⟨0x8000000000000001⟩
  else if x.signBit then ⟨x.bits + 1⟩
  else ⟨x.bits - 1⟩

/-- What `printf` of glibc prints for the double `x` under the conversion `%.pf`, of which `%f` and
`%lf` are `%.6f`: the exact value of `x` rounded to `p` places after the point, ties to even, in
full however large it is, without the point for `p = 0`, after a `-` whenever the sign bit is set,
also for `-0.0` and for a negative value that rounds to `0`; `inf` for an infinity and `nan` for a
NaN, after a `-` when the sign bit is set. -/
def printFixed (p : Nat) (x : Double) : String :=
  let sign := if x.signBit then "-" else ""
  if x.isNaN then sign ++ "nan"
  else if x.isInf then sign ++ "inf"
  else
    let (m, e) := x.toDyadic
    let n := roundShift (m.natAbs * 10 ^ p) (-e)
    let f := toString (n % 10 ^ p)
    sign ++ toString (n / 10 ^ p) ++ if p = 0 then "" else "." ++ "".pushn '0' (p - f.length) ++ f

/-! ### Examples

The operations on the edge cases that matter (both zeros, the subnormals, the largest finite
doubles, the infinities, a NaN, `2 ^ 53` and `2 ^ 63` with their neighbors, ties of the rounding),
against what a C program compiled with gcc and linked with glibc on the platform of `j-points`
prints for them, as bits. -/

-- `x < y`, `x <= y` and `x == y` for every pair of 21 doubles: for each `x`, the masks of the `y`
-- for which the comparison is true, bit `j` for the `j`-th double (so a NaN, the nineteenth, is
-- unordered, and `-0.0` equals `0.0`).
#guard
  let xs : List UInt64 := [0x0000000000000000, 0x8000000000000000, 0x0000000000000001,
    0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000, 0x3ff0000000000000,
    0xbff0000000000000, 0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000,
    0xfff0000000000000, 0x43e0000000000000, 0x43dfffffffffffff, 0xc3e0000000000000,
    0x3fe8000000000000, 0x0008000000000000, 0x4340000000000001, 0x7ff8000000000000,
    0x3cb0000000000000, 0x000123456789abcd]
  let masks : List (Nat × Nat × Nat) := [(1815924, 1815927, 3), (1815924, 1815927, 3),
    (1815920, 1815924, 4), (1815927, 1815935, 8), (701792, 701808, 16), (701760, 701792, 32),
    (144640, 144704, 64), (1815935, 1816063, 128), (1024, 1280, 256), (1832447, 1832959, 512),
    (0, 1024, 1024), (1832959, 1835007, 2048), (1280, 5376, 4096), (5376, 13568, 8192),
    (1816063, 1832447, 16384), (144704, 177472, 32768), (701808, 767344, 65536),
    (13568, 144640, 131072), (0, 0, 0), (177472, 701760, 524288), (767344, 1815920, 1048576)]
  let mask (f : Double → Double → Bool) (x : UInt64) : Nat :=
    (xs.zipIdx.filter fun (y, _) ↦ f ⟨x⟩ ⟨y⟩).foldl (fun m (_, j) ↦ m + 2 ^ j) 0
  (xs.zip masks).all fun (x, l, e, q) ↦ mask lt x == l && mask le x == e && mask beq x == q

-- `isnormal(x)`: the zeros, the subnormals, the infinities and the NaNs are not normal.
#guard ([(0x0000000000000000, false), (0x8000000000000000, false), (0x0000000000000001, false),
    (0x8000000000000001, false), (0x000fffffffffffff, false), (0x0008000000000000, false),
    (0x0010000000000000, true), (0x8010000000000000, true), (0x3ff0000000000000, true),
    (0xbff0000000000000, true), (0x7fefffffffffffff, true), (0xffefffffffffffff, true),
    (0x7ff0000000000000, false), (0xfff0000000000000, false), (0x7ff8000000000000, false),
    (0xfff8000000000001, false)] : List (UInt64 × Bool)).all fun (x, r) ↦ isNormal ⟨x⟩ == r

-- `-x` and `fabs(x)`.
#guard ([(0x0000000000000000, 0x8000000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x0000000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x8000000000000001, 0x0000000000000001),
    (0x8000000000000001, 0x0000000000000001, 0x0000000000000001),
    (0x000fffffffffffff, 0x800fffffffffffff, 0x000fffffffffffff),
    (0x7fefffffffffffff, 0xffefffffffffffff, 0x7fefffffffffffff),
    (0xffefffffffffffff, 0x7fefffffffffffff, 0x7fefffffffffffff),
    (0x7ff0000000000000, 0xfff0000000000000, 0x7ff0000000000000),
    (0xfff0000000000000, 0x7ff0000000000000, 0x7ff0000000000000),
    (0x43dfffffffffffff, 0xc3dfffffffffffff, 0x43dfffffffffffff),
    (0xc3e0000000000000, 0x43e0000000000000, 0x43e0000000000000),
    (0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000000000000)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, n, f) ↦
  (neg ⟨x⟩).bits == n && (fabs ⟨x⟩).bits == f

-- `nextafter` towards `±HUGE_VAL`.
#guard ([(0x0000000000000000, 0x0000000000000001, 0x8000000000000001),
    (0x8000000000000000, 0x0000000000000001, 0x8000000000000001),
    (0x0000000000000001, 0x0000000000000002, 0x0000000000000000),
    (0x8000000000000001, 0x8000000000000000, 0x8000000000000002),
    (0x000fffffffffffff, 0x0010000000000000, 0x000ffffffffffffe),
    (0x7fefffffffffffff, 0x7ff0000000000000, 0x7feffffffffffffe),
    (0xffefffffffffffff, 0xffeffffffffffffe, 0xfff0000000000000),
    (0x7ff0000000000000, 0x7ff0000000000000, 0x7fefffffffffffff),
    (0xfff0000000000000, 0xffefffffffffffff, 0xfff0000000000000),
    (0x43dfffffffffffff, 0x43e0000000000000, 0x43dffffffffffffe),
    (0xc3e0000000000000, 0xc3dfffffffffffff, 0xc3e0000000000001),
    (0x7ff8000000000000, 0x7ff8000000000000, 0x7ff8000000000000)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, u, d) ↦
  (nextUp ⟨x⟩).bits == u && (nextDown ⟨x⟩).bits == d

-- `ldexp`: exact, rounded into the subnormals (ties to even), overflow to `+∞`, and `ldexp(f, 53)`
-- for `1/2 ≤ f < 1`.
#guard ([(0x3ff0000000000000, 53, 0x4340000000000000), (0x3ff0000000000000, -1074, 1),
    (0x3ff0000000000000, -1075, 0), (0x3ff8000000000000, -1075, 1), (0x3ff0000000000000, -1076, 0),
    (0x3ff8000000000000, -1074, 2), (0x4004000000000000, -1074, 2), (0x400c000000000000, -1074, 4),
    (0x3ff0000000000000, 1023, 0x7fe0000000000000), (0x3ff0000000000000, 1024, 0x7ff0000000000000),
    (0xc340000000000000, -55, 0xbfd0000000000000), (0x43e0000000000000, 0, 0x43e0000000000000),
    (0xc3e0000000000000, -3, 0xc3b0000000000000), (0x4340000000000000, -60, 0x3f80000000000000),
    (0x0000000000000001, 1074, 0x3ff0000000000000), (0x0000000000000003, -1, 2),
    (0x0000000000000003, 1, 6), (0x8000000000000000, 5, 0x8000000000000000),
    (0x7ff0000000000000, -5, 0x7ff0000000000000), (0x3fe0000000000000, 53, 0x4330000000000000),
    (0x3fefffffffffffff, 53, 0x433fffffffffffff), (0x433fffffffffffff, -30, 0x415fffffffffffff),
    (0xc32fffffffffffff, -1100, 0x8000000004000000)] :
    List (UInt64 × Int × UInt64)).all fun (x, n, y) ↦ (ldexp ⟨x⟩ n).bits == y

-- `(long)x`, truncated towards zero, and `-2 ^ 63` beyond the range of a `long` (`2 ^ 63`, the
-- double below `-2 ^ 63`, `2 ^ 64`, the largest double), for the infinities and for the NaNs, a
-- signalling one included.
#guard ([(0x3ff0000000000000, 1), (0x3fe0000000000000, 0), (0xbfe0000000000000, 0),
    (0x4340000000000000, 9007199254740992), (0x433fffffffffffff, 9007199254740991),
    (0x43dfffffffffffff, 9223372036854774784), (0xc3dfffffffffffff, -9223372036854774784),
    (0x400c000000000000, 3), (0xc00c000000000000, -3), (0x0000000000000001, 0),
    (0x8000000000000000, 0), (0xbfefffffffffffff, 0), (0xc3e0000000000000, -9223372036854775808),
    (0x43e0000000000000, -9223372036854775808), (0xc3e0000000000001, -9223372036854775808),
    (0x43f0000000000000, -9223372036854775808), (0x7fefffffffffffff, -9223372036854775808),
    (0x7ff0000000000000, -9223372036854775808), (0xfff0000000000000, -9223372036854775808),
    (0x7ff8000000000000, -9223372036854775808), (0xfff8000000000000, -9223372036854775808),
    (0x7ff0000000000001, -9223372036854775808)] :
    List (UInt64 × Int)).all fun (x, n) ↦ (toInt64 ⟨x⟩).toInt == n

-- `printf` of glibc under `%.0f`, `%.1f` and `%.2f`: ties to even at the last place (`0.5`, `1.5`,
-- `2.5`, `0.25`, `0.75`, `0.125`, `0.375`), `-` on the sign bit also for `-0.0` and for negative
-- values that round to `0`, the double nearest to `0.715` and to `1.005`, which lie below the ties,
-- a large value in full, and no point for `%.0f`.
#guard ([(0x3fe0000000000000, "0", "0.5", "0.50"), (0x3ff8000000000000, "2", "1.5", "1.50"),
    (0x4004000000000000, "2", "2.5", "2.50"), (0xbfe0000000000000, "-0", "-0.5", "-0.50"),
    (0x3fd0000000000000, "0", "0.2", "0.25"), (0x3fe8000000000000, "1", "0.8", "0.75"),
    (0x3fc0000000000000, "0", "0.1", "0.12"), (0x3fd8000000000000, "0", "0.4", "0.38"),
    (0xbfa47ae147ae147b, "-0", "-0.0", "-0.04"), (0x3fe6e147ae147ae1, "1", "0.7", "0.71"),
    (0x3ff0147ae147ae14, "1", "1.0", "1.00"), (0x4050000000000000, "64", "64.0", "64.00"),
    (0x4450000000000000, "1180591620717411303424", "1180591620717411303424.0",
      "1180591620717411303424.00"), (0xfff0000000000000, "-inf", "-inf", "-inf")] :
    List (UInt64 × String × String × String)).all fun (x, s0, s1, s2) ↦
  (Double.mk x).printFixed 0 == s0 && (Double.mk x).printFixed 1 == s1 &&
    (Double.mk x).printFixed 2 == s2

end Double

end JPoints

end
