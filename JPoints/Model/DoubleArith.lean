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
# The arithmetic of the doubles

The operations on doubles that `j-points` applies to the doubles that decide what is searched,
beyond those of `JPoints.Model.Double`: the four operations `+`, `-`, `*` and `/` of the C language,
`sqrt` and `floor` of `math.h`, the conversion `(double)` of a `long`, the conversions `mpz_get_d`
and `mpq_get_d` of GMP, the floating literals of the C code, and instances for the operations and
the comparisons `<`, `<=`, `>` and `>=`, so that the model reads like the C code. Each does to the
bits what the code that gcc makes of it does on x86-64, with the C library glibc and GMP.

## Main definitions

* `JPoints.Double.add`, `JPoints.Double.sub`, `JPoints.Double.mul`, `JPoints.Double.div`: the
  four operations, with the instances `Add`, `Sub`, `Mul`, `Div` and `Neg`.
* `JPoints.Double.sqrt`, `JPoints.Double.floor`: the functions of `math.h`.
* `JPoints.Double.ofInt`: the conversion `(double)` of a `long`, given as an integer.
* `JPoints.Double.mpzGetD`, `JPoints.Double.mpqGetD`: the conversions of GMP, which truncate.
* `JPoints.Double.ofRatioTrunc`: a fraction truncated to a double, as GMP's `mpn_get_d` does it.
* `JPoints.Double.defaultNaN`, `JPoints.Double.quiet`, `JPoints.Double.propagateNaN`: the NaNs
  that the operations return.
* `JPoints.Double.ofScientific`: a floating literal of the C code, rounded as gcc rounds it.

## Implementation notes

The default build compiles with `gcc -O2` for x86-64 without `-march`, so that an operation on
doubles is a scalar instruction of SSE2 (`addsd`, `subsd`, `mulsd`, `divsd`, `sqrtsd`) in the
rounding mode to nearest with ties to even, and no product is contracted with a sum into a fused
multiply-add, which SSE2 does not have. The exact result of an operation on finite doubles is a
dyadic number, or a fraction for `/`, which `JPoints.Double.ofDyadic` and `JPoints.Double.ofRatio`
round as IEEE 754 prescribes, an infinity on overflow and a subnormal or a signed zero on underflow;
the signs of zeros, the infinities and the invalid operations follow IEEE 754.

A NaN result is the one SSE2 gives: for an operand that is a NaN, the first NaN operand with its
quiet bit (bit 51) set, the first operand being the one in the destination register of the
instruction; for an invalid operation without a NaN operand (`∞ - ∞`, `0 * ∞`, `0 / 0`, `∞ / ∞`,
`sqrt` of a negative number) the default NaN `0xfff8000000000000`. The doubles of the program never
start as NaNs (the conversions give none), so its NaNs are the default NaN and what `fabs` and `-`
make of it, and no decision depends on the sign or the fraction of a NaN, since every comparison
treats all NaNs alike.

GMP's `mpz_get_d` and `mpq_get_d` truncate the value towards zero to a double (GMP 6.3,
`mpn_get_d`), where the C conversions round to nearest; a value of at least `2 ^ 1024` in absolute
value becomes an infinity, and a value below `2 ^ (-1074)` in absolute value the zero `0.0`, also
for a negative value.
-/

@[expose] public section

namespace JPoints

namespace Double

/-! ### NaNs -/

/-- The default NaN of SSE2 (the "real indefinite" of Intel's manuals), `0xfff8000000000000`, which
an invalid operation without a NaN operand returns: `∞ - ∞`, `0 * ∞`, `0 / 0`, `∞ / ∞` and the
square root of a negative number. -/
def defaultNaN : Double := ⟨0xfff8000000000000⟩

/-- The NaN `x` with its quiet bit, bit 51, set: what SSE2 makes of a signalling NaN operand, and
a quiet NaN as it is. -/
def quiet (x : Double) : Double := ⟨x.bits ||| 0x0008000000000000⟩

/-- The result of an operation of SSE2 on two doubles of which one is a NaN: the first operand
quieted when it is a NaN, else the second quieted. -/
def propagateNaN (x y : Double) : Double := if x.isNaN then x.quiet else y.quiet

/-! ### The four operations -/

/-- `x + y` of the C language on doubles: a NaN for a NaN operand (`JPoints.Double.propagateNaN`),
the default NaN for `∞ + (-∞)`, an infinity for an infinite operand, and otherwise the exact sum
rounded to nearest, ties to even (`JPoints.Double.ofDyadic`), an infinity on overflow; an exact sum
`0` is `-0.0` when both operands are `-0.0` and `0.0` otherwise. Of two NaN operands the result is
`x` quieted, as gcc's code for `x + y` gives it with `x` in the destination register; gcc may swap
the operands of `+`, which changes only the sign and the fraction of a NaN result of two NaNs, on
which nothing in the program depends. -/
def add (x y : Double) : Double :=
  if x.isNaN || y.isNaN then propagateNaN x y
  else if x.isInf then if y.isInf && x.signBit != y.signBit then defaultNaN else x
  else if y.isInf then y
  else
    let (mx, ex) := x.toDyadic
    let (my, ey) := y.toDyadic
    let e := min ex ey
    let s := mx * 2 ^ (ex - e).toNat + my * 2 ^ (ey - e).toNat
    if s = 0 then ⟨if x.signBit && y.signBit then 0x8000000000000000 else 0⟩
    else ofDyadic (s < 0) s.natAbs e

/-- `x - y` of the C language on doubles: a NaN for a NaN operand (`JPoints.Double.propagateNaN`,
`y` not negated), and otherwise `x + (-y)` (`JPoints.Double.add`), which IEEE 754 makes it: the
default NaN for `∞ - ∞`, and an exact difference `0` is `-0.0` only for `-0.0 - 0.0`. -/
def sub (x y : Double) : Double :=
  if x.isNaN || y.isNaN then propagateNaN x y else add x y.neg

/-- `x * y` of the C language on doubles: a NaN for a NaN operand (`JPoints.Double.propagateNaN`),
the default NaN for `0 * ∞` and `∞ * 0`, an infinity for an infinite operand otherwise, and
otherwise the exact product rounded to nearest, ties to even (`JPoints.Double.ofDyadic`), an
infinity on overflow and a zero on underflow; the sign of the result, also of a zero or an infinity,
is the exclusive or of the signs. Of two NaN operands the result is `x` quieted, as gcc's code for
`x * y` gives it with `x` in the destination register; gcc may swap the operands of `*`, which
changes only the sign and the fraction of a NaN result of two NaNs, on which nothing in the program
depends. -/
def mul (x y : Double) : Double :=
  if x.isNaN || y.isNaN then propagateNaN x y
  else
    let neg := x.signBit != y.signBit
    if x.isInf || y.isInf then
      if x.isZero || y.isZero then defaultNaN else if neg then huge.neg else huge
    else
      let (mx, ex) := x.toDyadic
      let (my, ey) := y.toDyadic
      ofDyadic neg (mx.natAbs * my.natAbs) (ex + ey)

/-- `x / y` of the C language on doubles: a NaN for a NaN operand (`JPoints.Double.propagateNaN`),
the default NaN for `∞ / ∞` and `0 / 0`, an infinity for an infinite `x` or a finite `x ≠ 0` over
a zero, a zero for an infinite `y`, and otherwise the exact quotient rounded to nearest, ties to
even (`JPoints.Double.ofRatio`), an infinity on overflow and a zero on underflow; the sign of the
result, also of a zero or an infinity, is the exclusive or of the signs. -/
def div (x y : Double) : Double :=
  if x.isNaN || y.isNaN then propagateNaN x y
  else
    let neg := x.signBit != y.signBit
    if x.isInf then if y.isInf then defaultNaN else if neg then huge.neg else huge
    else if y.isInf then ⟨if neg then 0x8000000000000000 else 0⟩
    else if y.isZero then if x.isZero then defaultNaN else if neg then huge.neg else huge
    else
      let (mx, ex) := x.toDyadic
      let (my, ey) := y.toDyadic
      let k := ex - ey
      if 0 ≤ k then ofRatio neg (mx.natAbs * 2 ^ k.toNat) my.natAbs
      else ofRatio neg mx.natAbs (my.natAbs * 2 ^ (-k).toNat)

instance : Add Double := ⟨add⟩

instance : Sub Double := ⟨sub⟩

instance : Mul Double := ⟨mul⟩

instance : Div Double := ⟨div⟩

instance : Neg Double := ⟨neg⟩

/-- `x < y` of the C language, `JPoints.Double.lt`: false when either is a NaN; `x > y` is
`y < x`. -/
instance : LT Double := ⟨fun x y ↦ x.lt y = true⟩

/-- `x <= y` of the C language, `JPoints.Double.le`: false when either is a NaN; `x >= y` is
`y ≤ x`. -/
instance : LE Double := ⟨fun x y ↦ x.le y = true⟩

instance (x y : Double) : Decidable (x < y) := inferInstanceAs (Decidable (x.lt y = true))

instance (x y : Double) : Decidable (x ≤ y) := inferInstanceAs (Decidable (x.le y = true))

/-! ### The functions of `math.h` -/

/-- `sqrt(x)` of `math.h`, which gcc compiles to the instruction `sqrtsd` (glibc's `sqrt` gives
the same bits): the square root rounded to nearest (a tie cannot occur), from the integer square
root of the significand scaled to between `2 ^ 104` and `2 ^ 106`, the remainder deciding the
rounding; a zero and `+∞` as they are, so that `sqrt(-0.0)` is `-0.0`; a NaN quieted; the default
NaN for a negative `x`, `-∞` included. -/
def sqrt (x : Double) : Double :=
  if x.isNaN then x.quiet
  else if x.isZero then x
  else if x.signBit then defaultNaN
  else if x.isInf then x
  else
    let (m, e) := x.toDyadic
    let q : Int := ((m.toNat.log2 : Int) + e) / 2 - 52
    let n := m.toNat * 2 ^ (e - 2 * q).toNat
    let s := n.sqrt
    ofSignificand false (if s < n - s * s then s + 1 else s) q

/-- `floor(x)` of `math.h`, as glibc computes it: the greatest integer not above `x`, as a double;
a zero, an infinity and a finite `x` with `|x| ≥ 2 ^ 52`, which is an integer, as they are; a NaN
quieted; `0.0` for `0 < x < 1` and `-1.0` for `-1 < x < 0`. -/
def floor (x : Double) : Double :=
  if x.isNaN then x.quiet
  else if !x.isFinite || x.isZero then x
  else
    let (m, e) := x.toDyadic
    if 0 ≤ e then x
    else
      let f : Int := m / 2 ^ (-e).toNat
      ofDyadic (f < 0) f.natAbs 0

/-! ### Conversions -/

/-- The conversion `(double)n` of a `long` `n`, given as an integer: the double nearest to `n`,
ties to even, by `JPoints.Double.ofDyadic` (exact for `|n| ≤ 2 ^ 53`); also `(double)u` of an
`unsigned long` `u`, which gcc rounds the same way. -/
def ofInt (n : Int) : Double := ofDyadic (n < 0) n.natAbs 0

/-- The double of `±n / d` for `d ≠ 0`, the sign `-` for `neg`, truncated towards zero, as GMP's
`mpn_get_d` computes it for `mpz_get_d` and `mpq_get_d`: the exponent `E` with
`2 ^ E ≤ n / d < 2 ^ (E + 1)` as in `JPoints.Double.ofRatio`, an infinity for `E ≥ 1024`, and
otherwise the quotient `n / (d 2 ^ q)` rounded down for the last place `2 ^ q`,
`q = max (E - 52) (-1074)`, a subnormal below `2 ^ 52` (`JPoints.Double.assemble`), and `0.0`
whatever `neg` is when that quotient is `0` or `n = 0`. -/
def ofRatioTrunc (neg : Bool) (n d : Nat) : Double :=
  if n = 0 then zero
  else
    let e : Int := (n.log2 : Int) - d.log2
    let atLeast : Bool := if 0 ≤ e then d * 2 ^ e.toNat ≤ n else d ≤ n * 2 ^ (-e).toNat
    let E : Int := if atLeast then e else e - 1
    if 1024 ≤ E then if neg then huge.neg else huge
    else
      let q : Int := max (E - 52) (-1074)
      let M := if 0 ≤ q then n / (d * 2 ^ q.toNat) else n * 2 ^ (-q).toNat / d
      if M = 0 then zero else assemble neg M q

/-- `mpz_get_d(n)` of GMP: the integer `n` truncated towards zero to a double
(`JPoints.Double.ofRatioTrunc`), an infinity for `|n| ≥ 2 ^ 1024`. -/
def mpzGetD (n : Int) : Double := ofRatioTrunc (n < 0) n.natAbs 1

/-- `mpq_get_d(r)` of GMP: the rational number `r` truncated towards zero to a double
(`JPoints.Double.ofRatioTrunc`), an infinity for `|r| ≥ 2 ^ 1024`, and `0.0`, also for a negative
`r`, for `|r| < 2 ^ (-1074)`. -/
def mpqGetD (r : Rat) : Double := ofRatioTrunc (r.num < 0) r.num.natAbs r.den

/-- The floating literal `m e±k` of the C code (`OfScientific`, the literal `m * 10 ^ (±k)` of
Lean): the double nearest to its value, ties to even (`JPoints.Double.ofRatio`), as gcc rounds a
decimal literal, `+∞` beyond the largest double. A negative literal of the C code, such as `-4.0`,
is the negation of the literal. -/
def ofScientific (m : Nat) (neg : Bool) (k : Nat) : Double :=
  if neg then ofRatio false m (10 ^ k) else ofRatio false (m * 10 ^ k) 1

instance : OfScientific Double := ⟨ofScientific⟩

/-! ### Examples

The operations on the edge cases (both zeros, the subnormals and the underflow to them, the
overflow to the infinities, ties of the rounding, the infinities and NaNs, the conversions of
large and negative values) against what a C program compiled with `gcc -O2` and linked with glibc
and GMP 6.3 on x86-64 prints for them, as bits. -/

-- `x + y`: ties to even (`1 + 2 ^ (-53)`, `(1 + 2 ^ (-52)) + 2 ^ (-53)`, `2 ^ 53 + 1`,
-- `2 ^ 53 + 3`), above a tie, the overflow at the largest double plus half its last place (a tie)
-- and below it, for either sign, a subnormal sum, `0.1 + 0.2`, the signs of exact zeros, the
-- infinities and the NaNs (the first NaN operand quieted, a signalling one included).
#guard ([(0x3ff0000000000000, 0x3ca0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000001, 0x3ca0000000000000, 0x3ff0000000000002),
    (0x3ff0000000000000, 0x3ca0000000000001, 0x3ff0000000000001),
    (0x4340000000000000, 0x3ff0000000000000, 0x4340000000000000),
    (0x4340000000000000, 0x4008000000000000, 0x4340000000000002),
    (0x7fefffffffffffff, 0x7c90000000000000, 0x7ff0000000000000),
    (0x7fefffffffffffff, 0x7c8fffffffffffff, 0x7fefffffffffffff),
    (0xffefffffffffffff, 0xfc90000000000000, 0xfff0000000000000),
    (0x0010000000000000, 0x8000000000000001, 0x000fffffffffffff),
    (0x3fb999999999999a, 0x3fc999999999999a, 0x3fd3333333333334),
    (0x3ff0000000000000, 0xbff0000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x8000000000000001, 0x0000000000000000),
    (0x8000000000000000, 0x8000000000000000, 0x8000000000000000),
    (0x0000000000000000, 0x8000000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x0000000000000000, 0x0000000000000000),
    (0x7ff0000000000000, 0xfff0000000000000, 0xfff8000000000000),
    (0xfff0000000000000, 0xfff0000000000000, 0xfff0000000000000),
    (0x7ff0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000),
    (0x7fefffffffffffff, 0xfff0000000000000, 0xfff0000000000000),
    (0x7ff8000000000000, 0x3ff0000000000000, 0x7ff8000000000000),
    (0x3ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000001),
    (0x7ff0000000000001, 0xfff8000000000123, 0x7ff8000000000001),
    (0xfff8000000000123, 0x7ff0000000000001, 0xfff8000000000123)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, y, r) ↦ (Double.mk x + Double.mk y).bits == r

-- `x - y`: the signs of exact zeros, `∞ - ∞`, a NaN as the second operand (not negated), the tie
-- `1 - 2 ^ (-54)`, subnormal differences, the overflow to `-∞`.
#guard ([(0x3ff0000000000000, 0x3ff0000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x0000000000000000, 0x8000000000000000),
    (0x0000000000000000, 0x0000000000000000, 0x0000000000000000),
    (0x8000000000000000, 0x8000000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x8000000000000000, 0x0000000000000000),
    (0x7ff0000000000000, 0x7ff0000000000000, 0xfff8000000000000),
    (0x7ff0000000000000, 0xfff0000000000000, 0x7ff0000000000000),
    (0x3ff0000000000000, 0xfff8000000000123, 0xfff8000000000123),
    (0x3ff0000000000000, 0x3c90000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x3ca0000000000000, 0x3fefffffffffffff),
    (0x0010000000000000, 0x0000000000000001, 0x000fffffffffffff),
    (0x0018000000000000, 0x0010000000000000, 0x0008000000000000),
    (0xffefffffffffffff, 0x7fefffffffffffff, 0xfff0000000000000)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, y, r) ↦ (Double.mk x - Double.mk y).bits == r

-- `x * y`: the underflow to a signed zero and ties in the subnormals, a tie up to the least normal
-- double, `0 * ∞`, the overflow to `±∞`, `(1/3) * 3`, the rounding of `(1 + 2 ^ (-52)) ^ 2`, NaNs.
#guard ([(0x0000000000000001, 0x3fe0000000000000, 0x0000000000000000),
    (0x0000000000000003, 0x3fe0000000000000, 0x0000000000000002),
    (0x8000000000000001, 0x3fe0000000000000, 0x8000000000000000),
    (0x0010000000000000, 0x3fefffffffffffff, 0x0010000000000000),
    (0xbff0000000000000, 0x0000000000000000, 0x8000000000000000),
    (0x0000000000000000, 0xfff0000000000000, 0xfff8000000000000),
    (0x7ff0000000000000, 0x0000000000000000, 0xfff8000000000000),
    (0xfff0000000000000, 0xc000000000000000, 0x7ff0000000000000),
    (0x7fefffffffffffff, 0x4000000000000000, 0x7ff0000000000000),
    (0xffefffffffffffff, 0x4000000000000000, 0xfff0000000000000),
    (0x1a70000000000000, 0x1a70000000000000, 0x0000000000000000),
    (0x9a70000000000000, 0x1a70000000000000, 0x8000000000000000),
    (0x3fd5555555555555, 0x4008000000000000, 0x3ff0000000000000),
    (0x3ff0000000000001, 0x3ff0000000000001, 0x3ff0000000000002),
    (0x3ff0000000000001, 0x3fefffffffffffff, 0x3ff0000000000000),
    (0xfff8000000000123, 0x7ff8000000000000, 0xfff8000000000123),
    (0x3ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000001)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, y, r) ↦ (Double.mk x * Double.mk y).bits == r

-- `x / y`: `1/3`, `2/3`, `1/10`, division by a signed zero, `0 / 0`, `∞ / ∞`, by and of an
-- infinity, the underflow (a tie to `0`, a subnormal quotient), the overflow, NaNs.
#guard ([(0x3ff0000000000000, 0x4008000000000000, 0x3fd5555555555555),
    (0x4000000000000000, 0x4008000000000000, 0x3fe5555555555555),
    (0x3ff0000000000000, 0x0000000000000000, 0x7ff0000000000000),
    (0xbff0000000000000, 0x0000000000000000, 0xfff0000000000000),
    (0x3ff0000000000000, 0x8000000000000000, 0xfff0000000000000),
    (0x0000000000000000, 0x0000000000000000, 0xfff8000000000000),
    (0x7ff0000000000000, 0x7ff0000000000000, 0xfff8000000000000),
    (0x3ff0000000000000, 0x7ff0000000000000, 0x0000000000000000),
    (0xbff0000000000000, 0x7ff0000000000000, 0x8000000000000000),
    (0x0000000000000000, 0xbff0000000000000, 0x8000000000000000),
    (0x0000000000000001, 0x4000000000000000, 0x0000000000000000),
    (0x0000000000000003, 0x4000000000000000, 0x0000000000000002),
    (0x7fefffffffffffff, 0x3fe0000000000000, 0x7ff0000000000000),
    (0x3ff0000000000000, 0x7fefffffffffffff, 0x0004000000000000),
    (0x0000000000000001, 0x7fefffffffffffff, 0x0000000000000000),
    (0xfff0000000000000, 0x0000000000000000, 0xfff0000000000000),
    (0x0000000000000000, 0xfff0000000000000, 0x8000000000000000),
    (0xfff0000000000000, 0x4000000000000000, 0xfff0000000000000),
    (0x3ff0000000000000, 0x4024000000000000, 0x3fb999999999999a),
    (0x7ff8000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x0000000000000000, 0x7ff0000000000001, 0x7ff8000000000001)] :
    List (UInt64 × UInt64 × UInt64)).all fun (x, y, r) ↦ (Double.mk x / Double.mk y).bits == r

-- All four operations on every ordered pair of 24 doubles (both zeros, the least subnormal and its
-- negation, the largest subnormal, the least normal double, `±1`, `3/2`, `3`, `0.1`, `1/3`,
-- `1 + 2 ^ (-52)`, `2 ^ (-53)`, `2 ^ 53`, `±` the largest double, `2 ^ 1023`, `2 ^ (-1023)`,
-- `±∞`, a quiet NaN, a negative quiet NaN with a payload, a signalling NaN), by the FNV-1a hash of
-- the bits of the results in the order of the pairs, which the C program computes in the same
-- way.
#guard
  let xs : List UInt64 := [0x0000000000000000, 0x8000000000000000, 0x0000000000000001,
    0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000, 0x3ff0000000000000,
    0xbff0000000000000, 0x3ff8000000000000, 0x4008000000000000, 0x3fb999999999999a,
    0x3fd5555555555555, 0x3ff0000000000001, 0x3ca0000000000000, 0x4340000000000000,
    0x7fefffffffffffff, 0xffefffffffffffff, 0x7fe0000000000000, 0x0008000000000000,
    0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000123,
    0x7ff0000000000001]
  let hash (f : Double → Double → Double) : UInt64 :=
    xs.foldl (fun h x ↦ xs.foldl (fun h y ↦ (h ^^^ (f ⟨x⟩ ⟨y⟩).bits) * 0x100000001b3) h)
      0xcbf29ce484222325
  hash (· + ·) == 0x6d7fe6c85f70090f && hash (· - ·) == 0x7a6a3f1db042ecbb &&
    hash (· * ·) == 0x37ca635d4728a23d && hash (· / ·) == 0xc4471bd0cf738d8a

-- `sqrt(x)`: both zeros, subnormals, the least normal double, `1`, `2`, `4`, `1/2`, the neighbours
-- of `1`, the largest double, `±∞`, negative numbers, NaNs.
#guard ([(0x0000000000000000, 0x0000000000000000), (0x8000000000000000, 0x8000000000000000),
    (0x0000000000000001, 0x1e60000000000000), (0x000fffffffffffff, 0x1fffffffffffffff),
    (0x0010000000000000, 0x2000000000000000), (0x3ff0000000000000, 0x3ff0000000000000),
    (0x4000000000000000, 0x3ff6a09e667f3bcd), (0x4010000000000000, 0x4000000000000000),
    (0x3fe0000000000000, 0x3fe6a09e667f3bcd), (0x3ff0000000000001, 0x3ff0000000000000),
    (0x3fefffffffffffff, 0x3fefffffffffffff), (0x7fefffffffffffff, 0x5fefffffffffffff),
    (0x7ff0000000000000, 0x7ff0000000000000), (0xfff0000000000000, 0xfff8000000000000),
    (0xbff0000000000000, 0xfff8000000000000), (0x8000000000000001, 0xfff8000000000000),
    (0x7ff8000000000000, 0x7ff8000000000000), (0x7ff0000000000001, 0x7ff8000000000001),
    (0xfff8000000000123, 0xfff8000000000123)] :
    List (UInt64 × UInt64)).all fun (x, r) ↦ (sqrt ⟨x⟩).bits == r

-- `floor(x)`: both zeros, `±1/2`, `±3/2`, `±3`, `±` the least subnormal, the neighbours of `±1`
-- towards `0`, `±(2 ^ 52 - 1/2)`, integers from `2 ^ 52` on, `±∞`, NaNs.
#guard ([(0x0000000000000000, 0x0000000000000000), (0x8000000000000000, 0x8000000000000000),
    (0x3fe0000000000000, 0x0000000000000000), (0xbfe0000000000000, 0xbff0000000000000),
    (0x3ff8000000000000, 0x3ff0000000000000), (0xbff8000000000000, 0xc000000000000000),
    (0x4008000000000000, 0x4008000000000000), (0xc008000000000000, 0xc008000000000000),
    (0x0000000000000001, 0x0000000000000000), (0x8000000000000001, 0xbff0000000000000),
    (0x3fefffffffffffff, 0x0000000000000000), (0xbfefffffffffffff, 0xbff0000000000000),
    (0x432fffffffffffff, 0x432ffffffffffffe), (0xc32fffffffffffff, 0xc330000000000000),
    (0x4330000000000001, 0x4330000000000001), (0x43b0000000000000, 0x43b0000000000000),
    (0x7fefffffffffffff, 0x7fefffffffffffff), (0x7ff0000000000000, 0x7ff0000000000000),
    (0xfff0000000000000, 0xfff0000000000000), (0x7ff8000000000000, 0x7ff8000000000000),
    (0x7ff0000000000001, 0x7ff8000000000001)] :
    List (UInt64 × UInt64)).all fun (x, r) ↦ (floor ⟨x⟩).bits == r

-- `(double)n` of a `long` and of an `unsigned long`, the ties to even included.
#guard ([(0, 0x0000000000000000), (2 ^ 53 + 1, 0x4340000000000000),
    (-(2 ^ 53 + 3), 0xc340000000000002), (-2 ^ 63, 0xc3e0000000000000),
    (2 ^ 63, 0x43e0000000000000), (2 ^ 63 + 1024, 0x43e0000000000000),
    (2 ^ 63 + 1025, 0x43e0000000000001), (2 ^ 64 - 1, 0x43f0000000000000)] :
    List (Int × UInt64)).all fun (n, r) ↦ (ofInt n).bits == r

-- `(double)n` of a `long`: exact up to `2 ^ 53`, ties to even above it, `±(2 ^ 63 - 1)` and
-- `-2 ^ 63` to `±2 ^ 63`, and the neighbours of `2 ^ 63 - 512`, the tie between the largest double
-- below `2 ^ 63` and `2 ^ 63`.
#guard ([(0, 0x0000000000000000), (1, 0x3ff0000000000000), (-1, 0xbff0000000000000),
    (3, 0x4008000000000000), (2 ^ 52, 0x4330000000000000), (2 ^ 53, 0x4340000000000000),
    (2 ^ 53 + 1, 0x4340000000000000), (2 ^ 53 + 2, 0x4340000000000001),
    (2 ^ 53 + 3, 0x4340000000000002), (-(2 ^ 53 + 1), 0xc340000000000000),
    (-(2 ^ 53 + 3), 0xc340000000000002), (2 ^ 62 + 2 ^ 9, 0x43d0000000000000),
    (2 ^ 62 + 2 ^ 10 + 2 ^ 9, 0x43d0000000000002), (2 ^ 62 + 2 ^ 9 + 1, 0x43d0000000000001),
    (2 ^ 63 - 1, 0x43e0000000000000), (-(2 ^ 63 - 1), 0xc3e0000000000000),
    (-2 ^ 63, 0xc3e0000000000000), (2 ^ 63 - 1025, 0x43dfffffffffffff),
    (2 ^ 63 - 512, 0x43e0000000000000), (2 ^ 63 - 513, 0x43dfffffffffffff),
    (2 ^ 63 - 514, 0x43dfffffffffffff), (123456789012345, 0x42dc12218377de40),
    (-987654321098765432, 0xc3ab69b4be93f169), (2 ^ 54 + 2, 0x4350000000000000),
    (2 ^ 54 + 6, 0x4350000000000002), (2 ^ 54 + 3, 0x4350000000000001)] :
    List (Int × UInt64)).all fun (n, b) ↦ (ofInt n).bits == b

-- `mpz_get_d(n)`: truncated (`2 ^ 53 + 3`, `2 ^ 63 - 1`, `2 ^ 1024 - 1`), and `±∞` from `2 ^ 1024`
-- on, also for integers of 1100 bits.
#guard ([(0, 0x0000000000000000), (1, 0x3ff0000000000000), (-1, 0xbff0000000000000),
    (2 ^ 53 + 1, 0x4340000000000000), (2 ^ 53 + 3, 0x4340000000000001),
    (-(2 ^ 53 + 3), 0xc340000000000001), (-(2 ^ 60 + 1), 0xc3b0000000000000),
    (2 ^ 63 - 1, 0x43dfffffffffffff), (2 ^ 1024 - 1, 0x7fefffffffffffff),
    (2 ^ 1024, 0x7ff0000000000000), (-2 ^ 1024, 0xfff0000000000000),
    (2 ^ 1100 - 1, 0x7ff0000000000000), (-(2 ^ 1099 + 1), 0xfff0000000000000),
    (3 ^ 600, 0x7b5f813b8e393477), (-3 ^ 600, 0xfb5f813b8e393477), (10 ^ 308, 0x7fe1ccf385ebc89f)] :
    List (Int × UInt64)).all fun (n, r) ↦ (mpzGetD n).bits == r

-- `mpq_get_d(n / d)`: truncated (`1/3`, `-2/3`, `±1/10`), `±∞` from `2 ^ 1024` on, the subnormals
-- truncated, and `0.0`, also for a negative value, below the least subnormal.
#guard ([((1, 3), 0x3fd5555555555555), ((-2, 3), 0xbfe5555555555555),
    ((10 ^ 400, 3), 0x7ff0000000000000), ((-10 ^ 400, 7), 0xfff0000000000000),
    ((1, 10), 0x3fb9999999999999), ((-1, 10), 0xbfb9999999999999),
    ((1, 2 ^ 1074), 0x0000000000000001), ((1, 2 ^ 1075), 0x0000000000000000),
    ((-1, 2 ^ 1075), 0x0000000000000000), ((3, 2 ^ 1075), 0x0000000000000001),
    ((-3, 2 ^ 1075), 0x8000000000000001), ((3, 2 ^ 1076), 0x0000000000000000),
    ((2 ^ 1025 - 1, 2), 0x7fefffffffffffff), ((2 ^ 1024 - 1, 1), 0x7fefffffffffffff),
    ((2 ^ 1024, 1), 0x7ff0000000000000), ((1, 10 ^ 400), 0x0000000000000000),
    ((0, 1), 0x0000000000000000), ((1, 3 * 2 ^ 1022), 0x0005555555555555),
    ((-(2 ^ 2000 + 1), 2 ^ 1000), 0xfe70000000000000), ((2 ^ 53 + 1, 1), 0x4340000000000000)] :
    List ((Int × Nat) × UInt64)).all fun ((n, d), r) ↦ (mpqGetD (mkRat n d)).bits == r

-- The literals of the C code and hard cases of the rounding of decimal literals (`0.1`, `1e23`, the
-- largest subnormal, the least subnormal and half of it on either side, the largest double and the
-- overflow beyond it, ties at `2 ^ 53`, and beyond the range), against the bits gcc gives them.
#guard ([((0.5 : Double), 0x3fe0000000000000), (1.0, 0x3ff0000000000000), (2.0, 0x4000000000000000),
    (4.0, 0x4010000000000000), (32.0, 0x4040000000000000), (1.0e-9, 0x3e112e0be826d695),
    (1.5e-5, 0x3eef75104d551d69), (1.0e300, 0x7e37e43c8800759c), (4.0e9, 0x41edcd6500000000),
    (9223372036854775808.0, 0x43e0000000000000), (0.1, 0x3fb999999999999a),
    (0.3, 0x3fd3333333333333), (1e23, 0x44b52d02c7e14af6),
    (2.2250738585072011e-308, 0x000fffffffffffff), (4.9406564584124654e-324, 0x0000000000000001),
    (2.4703282292062327e-324, 0x0000000000000000), (2.4703282292062328e-324, 0x0000000000000001),
    (1.7976931348623157e308, 0x7fefffffffffffff), (1.7976931348623158e308, 0x7fefffffffffffff),
    (1.7976931348623159e308, 0x7ff0000000000000), (9007199254740993.0, 0x4340000000000000),
    (9007199254740995.0, 0x4340000000000002), (0.0, 0x0000000000000000),
    (1e400, 0x7ff0000000000000), (1e-400, 0x0000000000000000)] :
    List (Double × UInt64)).all fun (x, r) ↦ x.bits == r

-- The uses in `j-points`: `1.0 / (double)p` for the 53 odd primes up to 251 (`init_sift`, by the
-- FNV-1a hash of the bits, and for `3` and `251`); `floor(sqrt((double)h))` (`find_double_points`,
-- `find_points`), whose value for these `h` (heights around squares, and the largest height) is
-- the integer square root of `h`; `(long)((double)d * invp[n])` (`row_setup`), whose value for
-- these `d` and `p` (among them the largest `d`) is the quotient `d / p` rounded down; and
-- `0.5*ldexp(1.0, -40)` (`sturm_isolate`).
#guard
  let ps := (List.range 252).filter fun p ↦ 3 ≤ p && (List.range p).all fun q ↦ q < 2 || p % q != 0
  let inv (p : Nat) : Double := 1.0 / ofInt p
  ps.length == 53 && (inv 3).bits == 0x3fd5555555555555 && (inv 251).bits == 0x3f705197f7d73404 &&
    ps.foldl (fun h p ↦ (h ^^^ (inv p).bits) * 0x100000001b3) 0xcbf29ce484222325 ==
      0x9eca3f7050f2d93a
#guard [1, 2, 3, 4, 8, 9, 15, 16, 3036891663, 3036891664, 3037000499].all fun (h : Nat) ↦
  (floor (sqrt (ofInt h))).toInt64.toInt == h.sqrt
#guard ([(6074000998, 3), (6074000998, 251), (6074000997, 127), (250, 251), (251, 251), (5, 3)] :
    List (Nat × Nat)).all fun (d, p) ↦ (ofInt d * (1.0 / ofInt p)).toInt64.toInt == d / p
#guard ((0.5 : Double) * ldexp 1.0 (-40)).bits == 0x3d60000000000000

end Double

end JPoints

end
