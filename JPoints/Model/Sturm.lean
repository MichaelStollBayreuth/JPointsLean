/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants
public import JPoints.Model.DoubleArith

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.DoubleArith

/-!
# The real roots

The real roots of the polynomial `f` of the curve searched, as `real_roots_init` of `j-points.c`
finds them by Sturm's theorem in exact arithmetic, for condition (3) of the analysis of the real
region: the chain `p₀ = f`, `p₁ = f'` and `pᵢ = -(pᵢ₋₂ mod pᵢ₋₁)` over `ℚ`
(`JPoints.realRootsStart`, `JPoints.realRootsChain`, with the division `JPoints.realRootsReduce`);
the number of its sign changes at a rational number (`JPoints.sturmChanges`), whose differences
count the roots in a half-open interval `(x, y]`; the Cauchy bound `B` of the roots in integers
(`JPoints.realRootsBound`); the isolation of the roots by bisection of `(-B, B]`, each isolating
interval `(lo, hi]` refined until `hi - lo` is at most about `2 ^ (-41) (|lo| + |hi| + 1)`, by a
test in doubles (`JPoints.sturmIsolate`, `JPoints.sturmRefine`); and the open intervals between
consecutive roots on which `f` is negative, its sign alternating from the sign at `+∞`, with their
ends as doubles, shrunk by the isolating intervals at their ends (`JPoints.realRootsRecord`). The
whole is `JPoints.realRootsInit`, which leaves the intervals in the globals `num_neg`,
`neg_shrunk_lo` and `neg_shrunk_hi` (`JPoints.NegativeIntervals`). For a bound `B` of more than
`ROOT_BITS` bits it records no interval, and the real region is then every row whole.

## Main definitions

* `JPoints.SturmChain`, `JPoints.RootIntervals`: the static Sturm chain and the static isolating
  intervals of `j-points.c`.
* `JPoints.NegativeIntervals`: the globals of the open intervals on which `f` is negative.
* `JPoints.sturmChanges`: the number of sign changes of the chain at a rational number.
* `JPoints.sturmRefine`, `JPoints.sturmIsolate`: the refinement of an isolating interval, and the
  isolation of the roots in a half-open interval.
* `JPoints.sturmIsolateFuel`: a depth of the recursion of `JPoints.sturmIsolate` that suffices.
* `JPoints.realRootsStart`, `JPoints.realRootsReduce`, `JPoints.realRootsChain`: the Sturm chain.
* `JPoints.realRootsBound`: the Cauchy bound of the roots.
* `JPoints.realRootsRecord`: the intervals on which `f` is negative, from the isolating intervals.
* `JPoints.realRootsInit`: the real roots and the intervals on which `f` is negative.

## Implementation notes

The rationals `mpq_t` of the C code are core's `Rat`, the integers `mpz_t` are `Int`s, and the
doubles of the test of the refinement and of the ends of the intervals are `JPoints.Double`s, by the
operations of `JPoints.Model.DoubleArith`: `mpq_get_d` truncates towards zero
(`JPoints.Double.mpqGetD`), and `nextafter` towards `±HUGE_VAL` is `JPoints.Double.nextUp` and
`JPoints.Double.nextDown`. The array `sturm[7][7]` of the chain is one flat array of 49 rationals,
the coefficient of `x ^ k` of `pᵢ` at `7 i + k`, as the C code keeps it, and the arrays of the
isolating intervals hold six rationals each; they start at `0`, which `mpq_init` gives them, and the
entries that the C code never sets are never read. These statics live only during `real_roots_init`,
which initializes them at its start and clears them at its end; the model keeps them as the values
that the functions pass on.

The recursion of `sturm_isolate` ends because the counts of `sturm_changes` are those of Sturm's
theorem and the roots of the squarefree `f` are distinct: an interval that holds two roots is at
least as wide as their distance. The model gives it a fuel, the depth that it may still descend,
`JPoints.sturmIsolateFuel`, which Mahler's bound on the distance of two roots of a squarefree
integer polynomial makes sufficient (its docstring has the argument); were the fuel to run out, the
model records no interval, as for a bound `B` beyond `2 ^ ROOT_BITS`. The loop of the refinement
ends on the data: the width of the interval halves at each step, and the test in doubles holds once
it is at most `2 ^ (-43)` (`JPoints.Double.mpqGetD_sub_mpqGetD_le`), a width that the bisections
reach from `2 B < 2 ^ (ROOT_BITS + 1)` after at most `ROOT_BITS + 44` of them in all, those of the
recursion included.
-/

@[expose] public section

namespace JPoints

/-! ### The statics and the globals -/

/-- The Sturm chain of `real_roots_init`, the statics `sturm`, `sturm_deg` and `sturm_len` of
`j-points.c`: the polynomials `p₀, …, p_(len-1)`, of the degrees `deg[i]`, with the coefficient of
`x ^ k` of `pᵢ` at `sturm[7 i + k]`.

C: `j-points.c:1497-1498`

Deviation: one flat array for the array `sturm[7][7]` of `mpq_t`s, rationals, which start at `0` as
`mpq_init` sets them; natural numbers for the `long`s `sturm_deg[i]` and `sturm_len`, which the C
code keeps nonnegative, starting at `0` as the static storage does. -/
structure SturmChain where
  /-- `sturm`, the coefficients of the polynomials of the chain, `7 i + k` for `sturm[i][k]`. -/
  sturm : Array Rat := .replicate 49 0
  /-- `sturm_deg`, the degrees of the polynomials of the chain. -/
  deg : Array Nat := .replicate 7 0
  /-- `sturm_len`, the number of the polynomials of the chain. -/
  len : Nat := 0
  deriving DecidableEq, Repr

/-- The isolating intervals `(root_lo[i], root_hi[i]]` of the real roots, in increasing order, the
statics `root_lo`, `root_hi` and `num_roots` of `j-points.c`.

C: `j-points.c:1499-1500`

Deviation: arrays of six rationals for the arrays of `mpq_t`s, which start at `0` as `mpq_init`
sets them; a natural number for the `long` `num_roots`, which the C code keeps nonnegative. -/
structure RootIntervals where
  /-- `root_lo`, the lower ends of the isolating intervals. -/
  rootLo : Array Rat := .replicate 6 0
  /-- `root_hi`, the upper ends of the isolating intervals. -/
  rootHi : Array Rat := .replicate 6 0
  /-- `num_roots`, the number of the isolating intervals. -/
  numRoots : Nat := 0
  deriving DecidableEq, Repr

/-- The open intervals on which the polynomial `f` of the curve searched is negative, the globals
`num_neg`, `neg_shrunk_lo` and `neg_shrunk_hi` of `j-points.c`: the `i`-th for `i < numNeg` shrunk
by the isolating intervals of the roots at its ends, on `(shrunkLo[i], shrunkHi[i])`, which it
holds, so that `f` is negative there for sure; `±∞` for an end at `±∞`. The real region
(`row_region` of `j-sift.c`) reads them.

C: `j-points.c:241-242`

Deviation: a natural number for the `long` `num_neg`, which the C code keeps nonnegative; the
arrays of eight doubles start at `0.0`, as the static storage does. -/
structure NegativeIntervals where
  /-- `num_neg`, the number of the intervals. -/
  numNeg : Nat := 0
  /-- `neg_shrunk_lo`, the lower ends of the shrunk intervals. -/
  shrunkLo : Array Double := .replicate 8 Double.zero
  /-- `neg_shrunk_hi`, the upper ends of the shrunk intervals. -/
  shrunkHi : Array Double := .replicate 8 Double.zero
  deriving Repr

/-! ### The sign changes and the isolation -/

/-- `sturm_changes` of `j-points.c`: the number of the sign changes of the chain `ch` at the
rational number `x`, the polynomials evaluated exactly by Horner's rule from their degrees, the
zeros skipped. For a squarefree `f`, the number of the roots in `(x, y]` is that at `x` less that
at `y`, also when `x` or `y` is a root.

C: `j-points.c:1506-1510`, `j-points.c:1512-1522`, `j-points.c:1524-1525`

Deviation: the statics of the chain as an argument; rationals for the `mpq_t`s; a natural number
for the `long` count, an integer for the `int`s `s` and `last`; the steps of the loop of Horner's
rule counted up, for the index `k` that counts down from `deg[i] - 1`. -/
def sturmChanges (ch : SturmChain) (x : Rat) : Id Nat := do
  let mut changes := 0
  let mut last : Int := 0
  for i in [0:ch.len] do
    let d := ch.deg[i]!
    let mut v := ch.sturm[i * 7 + d]!
    for j in [0:d] do
      v := v * x + ch.sturm[i * 7 + (d - 1 - j)]!
    let s := v.num.sign
    if s != 0 then
      if last != 0 && s != last then
        changes := changes + 1
      last := s
  return changes

/-- The refinement of the isolating interval `(lo, hi]` of one root in `sturm_isolate` of
`j-points.c`, with the count `nlo` of `JPoints.sturmChanges` at its lower end: until the difference
`d` of the doubles of the ends is at most `2 ^ (-41) (s + 1)`, `s` the sum of their absolute values,
all in doubles, the interval halved at its midpoint, the half that holds the root kept. The interval
refined. The loop ends on the data: the width halves at each step, and the test holds once the width
is at most `2 ^ (-43)` (`JPoints.Double.mpqGetD_sub_mpqGetD_le`), as `JPoints.Double.mpqGetD`
truncates a rational by less than a unit in the last place.

C: `j-points.c:1536-1543`

Deviation: the ends by value and returned, for the rationals that the C code refines in place; the
doubles by their bits (`JPoints.Model.DoubleArith`); natural numbers for the `long` counts, and
`nlo - nmid == 1` as `nlo = nmid + 1`, which is the same for integers. -/
def sturmRefine (ch : SturmChain) (lo hi : Rat) (nlo : Nat) : Id (Rat × Rat) := do
  let mut lo := lo
  let mut hi := hi
  let mut nlo := nlo
  repeat
    let d := Double.mpqGetD hi - Double.mpqGetD lo
    let s := (Double.mpqGetD lo).fabs + (Double.mpqGetD hi).fabs
    if d ≤ 0.5 * Double.ldexp 1.0 (-40) * (s + 1.0) then break
    let mid := (lo + hi) / 2
    let nmid ← sturmChanges ch mid
    if nlo == nmid + 1 then
      hi := mid
    else
      lo := mid
      nlo := nmid
  return (lo, hi)

/-- `sturm_isolate` of `j-points.c`: the `nlo - nhi` roots in `(lo, hi]`, for the counts `nlo` and
`nhi` of `JPoints.sturmChanges` at its ends, isolated and refined, their intervals appended to
`roots` in increasing order: nothing for `nlo = nhi`; for one root the interval refined
(`JPoints.sturmRefine`) and recorded if fewer than six are; and otherwise the interval halved at
its midpoint, the lower half first. The recursion descends while `fuel` lasts; none when it runs
out.

C: `j-points.c:1528-1532`, `j-points.c:1534-1535`, `j-points.c:1544-1545`, `j-points.c:1547-1551`,
`j-points.c:1553-1556`, `j-points.c:1558`, `j-points.c:1560-1561`

Deviation: the fuel, the depth that the recursion may still descend, of which
`JPoints.sturmIsolateFuel` suffices whenever `f` is squarefree, for a recursion that the C code
ends by Sturm's theorem; none when it runs out, for which the caller records no interval; the
statics as arguments and the isolating intervals returned; the ends by value, for the rationals
`l2` and `h2` that the C code sets to the halves; natural numbers for the `long` counts, and
`nlo - nhi == 1` as `nlo = nhi + 1`, which is the same for integers. -/
def sturmIsolate (ch : SturmChain) (fuel : Nat) (lo hi : Rat) (nlo nhi : Nat)
    (roots : RootIntervals) : Id (Option RootIntervals) := do
  if nlo == nhi then return some roots
  if nlo == nhi + 1 then
    let (lo, hi) ← sturmRefine ch lo hi nlo
    if roots.numRoots < 6 then
      return some { rootLo := roots.rootLo.set! roots.numRoots lo,
                    rootHi := roots.rootHi.set! roots.numRoots hi, numRoots := roots.numRoots + 1 }
    return some roots
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let mid := (lo + hi) / 2
    let nmid ← sturmChanges ch mid
    let some roots ← sturmIsolate ch fuel lo mid nlo nmid roots | return none
    sturmIsolate ch fuel mid hi nmid nhi roots

/-- The fuel that `JPoints.realRootsInit` gives `JPoints.sturmIsolate` for the polynomial `f` with
the coefficients `coeffs` of degree `d`: `ROOT_BITS + 19 + (d - 1) h`, for the number of bits `h`
of the largest `|fₖ|`. It suffices for a squarefree `f` of degree `2 ≤ d ≤ 6` whose bound `B` has
at most `ROOT_BITS` bits. A call at the depth `j` has an interval of the width `2 B / 2 ^ j`, and
one that halves its interval holds two distinct roots of `f` (Sturm's theorem), whose distance is
then below that width; by Mahler's bound (with `|disc f| ≥ 1`) it is above
`√3 d ^ (-(d+2)/2) ‖f‖₂ ^ (-(d-1))`, where `‖f‖₂ ≤ √(d+1) 2 ^ h` and
`d ^ ((d+2)/2) (d+1) ^ ((d-1)/2) < 2 ^ 18`. With `2 B < 2 ^ (ROOT_BITS + 1)` that gives
`2 ^ j < 2 ^ (ROOT_BITS + 19 + (d - 1) h)`, so that every call that halves its interval has a depth
below the fuel, and fuel left. -/
def sturmIsolateFuel (coeffs : Array Int) (degree : Nat) : Nat :=
  let H := (List.range (degree + 1)).foldl (fun m k ↦ max m coeffs[k]!.natAbs) 0
  rootBits + 19 + (degree - 1) * (H.log2 + 1)

/-! ### The Sturm chain and the bound -/

/-- The start of the Sturm chain in `real_roots_init` of `j-points.c`, for the polynomial `f` with
the coefficients `coeffs` of degree `degree ≥ 1`: `p₀ = f` and `p₁ = f'`, the derivative.

C: `j-points.c:1572-1579`

Deviation: the globals `coeffs` and `degree` as arguments, and the chain returned, from the statics
as they start (`0`); a natural number for the `long` `degree`; the product `k fₖ` by the rational
`k`, as the C code makes it with the scratch `q`. -/
def realRootsStart (coeffs : Array Int) (degree : Nat) : Id SturmChain := do
  let mut sturm : Array Rat := .replicate 49 0
  for k in [0:degree + 1] do
    sturm := sturm.set! k coeffs[k]!
  for k in [1:degree + 1] do
    let q : Rat := k
    sturm := sturm.set! (7 + (k - 1)) (coeffs[k]! * q)
  return { sturm, deg := #[degree, degree - 1, 0, 0, 0, 0, 0], len := 2 }

/-- The remainder in `real_roots_init` of `j-points.c` of the polynomial `p_i2` of the chain `ch`,
of degree `d`, modulo `p_i1`: while `d` is at least the degree of `p_i1`, the multiple
`q x ^ (d - deg p_i1) p_i1` that cancels the term of `x ^ d` subtracted from `p_i2`, and `d` lowered
past the zero coefficients, down to `-1` for the zero polynomial. The chain with the remainder for
`p_i2`, and its degree.

C: `j-points.c:1585-1588`, `j-points.c:1590-1591`, `j-points.c:1593-1596`

Deviation: the chain by value and returned; an integer for the `long` `d`, which reaches `-1`;
the scratch rational `t` of each step a local. -/
def realRootsReduce (ch : SturmChain) (i1 i2 : Nat) (d : Int) : Id (SturmChain × Int) := do
  let mut sturm := ch.sturm
  let mut d := d
  let d1 := ch.deg[i1]!
  while d ≥ d1 do
    let q := sturm[i2 * 7 + d.toNat]! / sturm[i1 * 7 + d1]!
    for k in [0:d1 + 1] do
      let t := q * sturm[i1 * 7 + k]!
      sturm := sturm.set! (i2 * 7 + (k + d.toNat - d1)) (sturm[i2 * 7 + (k + d.toNat - d1)]! - t)
    d := d - 1
    while d ≥ 0 && sturm[i2 * 7 + d.toNat]! == 0 do
      d := d - 1
  return ({ ch with sturm }, d)

/-- The Sturm chain in `real_roots_init` of `j-points.c`, from its start `p₀ = f`, `p₁ = f'`
(`JPoints.realRootsStart`): while the last polynomial has a positive degree, the next is the
negated remainder of the one before it modulo it (`JPoints.realRootsReduce`); a zero remainder,
which a squarefree `f` does not give, ends the chain.

C: `j-points.c:1581-1584`, `j-points.c:1597-1601`

Deviation: the chain by value and returned. -/
def realRootsChain (ch : SturmChain) : Id SturmChain := do
  let mut ch := ch
  while ch.deg[ch.len - 1]! > 0 do
    let (i0, i1, i2) := (ch.len - 2, ch.len - 1, ch.len)
    for k in [0:7] do
      ch := { ch with sturm := ch.sturm.set! (i2 * 7 + k) ch.sturm[i0 * 7 + k]! }
    let (ch', d) ← realRootsReduce ch i1 i2 ch.deg[i0]!
    ch := ch'
    if d < 0 then break
    for k in [0:d.toNat + 1] do
      ch := { ch with sturm := ch.sturm.set! (i2 * 7 + k) (-ch.sturm[i2 * 7 + k]!) }
    ch := { ch with deg := ch.deg.set! i2 d.toNat, len := ch.len + 1 }
  return ch

/-- The Cauchy bound in `real_roots_init` of `j-points.c` of the roots of the polynomial `f` with
the coefficients `coeffs` of degree `d = degree`, with `f_d ≠ 0`: `B = 2 + max ⌈|fₖ| / |f_d|⌉` over
`k < d`, the maximum from `0`, so that every root lies in `(-B, B)`.

C: `j-points.c:1604-1610`

Deviation: the globals `coeffs` and `degree` as arguments, and the bound returned; integers for
the GMP integers `B`, `t` and `fd`, `B` from `0` as `mpz_init` sets it; the quotient rounded up,
as `mpz_cdiv_q` does, as `-(-t / fd)` with Lean's `/`, which rounds down for the positive `fd`. -/
def realRootsBound (coeffs : Array Int) (degree : Nat) : Id Int := do
  let mut B : Int := 0
  let fd : Int := coeffs[degree]!.natAbs
  for k in [0:degree] do
    let t : Int := coeffs[k]!.natAbs
    let t := -(-t / fd)
    if t > B then B := t
  return B + 2

/-! ### The intervals on which `f` is negative -/

/-- The intervals on which the polynomial `f` with the coefficients `coeffs` of degree `degree` is
negative, as `real_roots_init` of `j-points.c` records them from the isolating intervals `roots`:
the sign of `f` on the interval from the root `i - 1` to the root `i` (from `-∞` for `i = 0`, to
`+∞` after the last root) is the sign of its leading coefficient for an even number of roots above
it, and its negative otherwise; each negative interval is appended to `neg`, shrunk by the doubles
of the isolating intervals at its ends, rounded inwards.

C: `j-points.c:1621-1633`

Deviation: the globals `coeffs` and `degree` and the statics of the isolating intervals as
arguments, and the intervals returned; the steps of the loop counted up, for the index `i` that
counts down from `num_roots`; an integer for the `long`s `sgn_inf` and `s`. -/
def realRootsRecord (coeffs : Array Int) (degree : Nat) (roots : RootIntervals)
    (neg : NegativeIntervals) : Id NegativeIntervals := do
  let sgnInf := coeffs[degree]!.sign
  let n := roots.numRoots
  let mut neg := neg
  for j in [0:n + 1] do
    let i := n - j
    let s := if (n - i) % 2 == 0 then sgnInf else -sgnInf
    if s < 0 then
      let slo := if i == 0 then -Double.huge else (Double.mpqGetD roots.rootHi[i - 1]!).nextUp
      let shi := if i == n then Double.huge else (Double.mpqGetD roots.rootLo[i]!).nextDown
      let k := neg.numNeg
      neg := { numNeg := k + 1, shrunkLo := neg.shrunkLo.set! k slo,
               shrunkHi := neg.shrunkHi.set! k shi }
  return neg

/-- `real_roots_init` of `j-points.c`: the open intervals on which the polynomial `f` of the curve
searched, with the coefficients `coeffs` of degree `degree`, is negative. The Sturm chain
(`JPoints.realRootsStart`, `JPoints.realRootsChain`) and the bound `B` (`JPoints.realRootsBound`);
when `B` has at most `ROOT_BITS` bits, the roots in `(-B, B]` isolated (`JPoints.sturmIsolate`)
and the intervals recorded (`JPoints.realRootsRecord`); no interval otherwise.

C: `j-points.c:1563-1567`, `j-points.c:1611-1618`, `j-points.c:1634`, `j-points.c:1639-1640`

Deviation: the globals `coeffs` and `degree` as arguments, and the globals of the intervals
returned, from their initial values, as `real_roots_init` runs once; a natural number for the
`long` `degree`, which is `5` or `6`; `mpz_sizeinbase(B, 2)` as the number of bits of `B`; the
fuel `JPoints.sturmIsolateFuel` for the recursion of `sturm_isolate`, and no interval when it runs
out, which it does not for a squarefree `f`; the statics of the chain and of the isolating
intervals passed on. -/
def realRootsInit (coeffs : Array Int) (degree : Nat) : Id NegativeIntervals := do
  let ch ← realRootsChain (← realRootsStart coeffs degree)
  let B ← realRootsBound coeffs degree
  let neg : NegativeIntervals := { numNeg := 0 }
  if B.natAbs.log2 + 1 ≤ rootBits then
    let hi : Rat := B
    let lo := -hi
    let nlo ← sturmChanges ch lo
    let nhi ← sturmChanges ch hi
    let roots : RootIntervals := { numRoots := 0 }
    if let some roots ← sturmIsolate ch (sturmIsolateFuel coeffs degree) lo hi nlo nhi roots then
      return ← realRootsRecord coeffs degree roots neg
  return neg

/-! ### Examples

The values are those that a test program prints which includes `j-points.c` at the pin, with a hook
at the end of `real_roots_init`, before its clears, that prints the Sturm chain, the bound `B`, the
isolating intervals and the counts of `sturm_changes` at given rationals, and after it the globals
of the intervals on which `f` is negative, by their bits in hex. The curves are curves searched (as
`normalise_curve` leaves them): `x ^ 5 - x`, whose root `0` a midpoint meets; `x ^ 6 + 1` and
`-x ^ 6 - 1`, without a real root; `x ^ 5 + 1`, with one; `(x² - 1) (x² - 4) (x² - 9)` and
`x (x² - 1) (x² - 4)` and its multiple by `-2`, with six and five; `2 - 3 x ^ 6`; roots `2 ^ (-50)`
and `2 ^ (-49)`, closer than the width of the refinement, and `3 / 2` and `3 / 2 + 2 ^ (-46)`; roots
`2 ^ (-1100)` and `-2 ^ (-1060)`, which the doubles of the ends do not resolve, `± 2 ^ (-1030)`, and
roots near `2 ^ (-1070)` and `2 ^ (-1080)`, whose isolating intervals have subnormal and zero
doubles as their ends; the bounds `B = 2 ^ 480 - 1`, of `ROOT_BITS` bits, and `B = 2 ^ 480`, beyond
them, without an interval; roots `0`, `± 10 ^ 30` and `± 2 10 ^ 30`; curves of the tests of
`j-points`, one with roots near `10 ^ 10` and `2 10 ^ 10`; roots `3 / 2`, `-3 / 4` and `5 / 8`,
which the bisection meets; `(x² - 1) (x⁴ + x² - 1)`; and `(x - 1)² (x³ + 2)`, which is not
squarefree and whose zero remainder ends the chain.
-/

-- Whether the Sturm chain of `f` is `chain`, its polynomials by their degrees and coefficients.
private def chainIs (coeffs : Array Int) (degree : Nat) (chain : List (Nat × List Rat)) : Bool :=
  let ch := (realRootsChain (realRootsStart coeffs degree).run).run
  chain == (List.range ch.len).map fun i ↦
    let d := ch.deg.getD i 0
    (d, (ch.sturm.extract (i * 7) (i * 7 + d + 1)).toList)

-- The counts of the sign changes of the Sturm chain of `f` at the rationals `xs`.
private def changesAt (coeffs : Array Int) (degree : Nat) (xs : List Rat) : List Nat :=
  let ch := (realRootsChain (realRootsStart coeffs degree).run).run
  xs.map fun x ↦ (sturmChanges ch x).run

-- The bound `B` of `f` and the isolating intervals of its roots in `(-B, B]`, with the fuel
-- `fuel`.
private def isolated (coeffs : Array Int) (degree : Nat)
    (fuel : Nat := sturmIsolateFuel coeffs degree) : Int × Option (List (Rat × Rat)) :=
  let ch := (realRootsChain (realRootsStart coeffs degree).run).run
  let B := (realRootsBound coeffs degree).run
  let hi : Rat := B
  let r := (sturmIsolate ch fuel (-hi) hi (sturmChanges ch (-hi)).run (sturmChanges ch hi).run
    {}).run
  (B, r.map fun r ↦ (r.rootLo.toList.zip r.rootHi.toList).take r.numRoots)

-- Whether the bound of `f` is `B` and the isolating intervals of its roots are `ivs`.
private def isolatedAre (coeffs : Array Int) (degree : Nat) (B : Int) (ivs : List (Rat × Rat)) :
    Bool :=
  isolated coeffs degree == (B, some ivs)

-- The intervals on which `f` is negative: their number, the bits of the ends of the first
-- `numNeg` entries of the two arrays, and whether the other entries are `0.0`.
private def negOf (coeffs : Array Int) (degree : Nat) : Nat × List (UInt64 × UInt64) × Bool :=
  let neg := (realRootsInit coeffs degree).run
  let rows := (neg.shrunkLo.zip neg.shrunkHi).toList.map fun (a, b) ↦ (a.bits, b.bits)
  (neg.numNeg, rows.take neg.numNeg, (rows.drop neg.numNeg).all (· == (0, 0)))

-- The Sturm chain of `x ^ 5 - x`, of `(x² - 1) (x² - 4) (x² - 9)`, of a curve of the tests, of
-- `(x² - 1) (x⁴ + x² - 1)`, and of `(x - 1)² (x³ + 2)`, whose remainder `0` ends it at the gcd.
#guard chainIs #[0, -1, 0, 0, 0, 1, 0] 5 [(5, [0, -1, 0, 0, 0, 1]), (4, [-1, 0, 0, 0, 5]),
    (1, [0, 4 / 5]), (0, [1])]
#guard chainIs #[-36, 0, 49, 0, -14, 0, 1] 6 [(6, [-36, 0, 49, 0, -14, 0, 1]),
    (5, [0, 98, 0, -56, 0, 6]), (4, [36, 0, -98 / 3, 0, 14 / 3]), (3, [0, -362 / 7, 0, 14]),
    (2, [-36, 0, 108 / 7]), (1, [0, 400 / 21]), (0, [36])]
#guard chainIs #[21, 116, 171, 128, 55, 12, 1] 6 [(6, [21, 116, 171, 128, 55, 12, 1]),
    (5, [116, 342, 384, 220, 60, 6]), (4, [53 / 3, 52 / 3, 14, 28 / 3, 5 / 3]),
    (3, [4096 / 25, -96 / 25, -2496 / 25, -544 / 25]), (2, [-8775 / 289, -8550 / 289, -1725 / 289]),
    (1, [-1627648 / 13225, -887808 / 13225]), (0, [-13225 / 3468])]
#guard chainIs #[1, 0, -2, 0, 0, 0, 1] 6 [(6, [1, 0, -2, 0, 0, 0, 1]), (5, [0, -4, 0, 0, 0, 6]),
    (2, [-1, 0, 4 / 3]), (1, [0, 5 / 2 ^ 3]), (0, [1])]
#guard chainIs #[2, -4, 2, 1, -2, 1, 0] 5 [(5, [2, -4, 2, 1, -2, 1]), (4, [-4, 4, 3, -8, 5]),
    (3, [-42 / 25, 72 / 25, -36 / 25, 6 / 25]), (2, [-150, 225, -75]), (1, [6 / 25, -6 / 25])]

-- The counts of the sign changes, at the roots and between them; at the double root `1` of
-- `(x - 1)² (x³ + 2)` every polynomial of the chain vanishes.
#guard changesAt #[0, -1, 0, 0, 0, 1, 0] 5 [-7/3, -1, -1/2, 0, 1/2, 1, 3] == [3, 2, 2, 1, 1, 0, 0]
#guard changesAt #[-36, 0, 49, 0, -14, 0, 1] 6 [-3, -5/2, -2, -1, 0, 1, 2, 3, 7/2] == [5, 5, 4, 3,
    3, 2, 1, 0, 0]
#guard changesAt #[2, -4, 2, 1, -2, 1, 0] 5 [-2, 0, 1, 2] == [3, 2, 0, 1]
#guard changesAt #[21, 116, 171, 128, 55, 12, 1] 6 [-10, -3, -2, -1, -1/3, 0] == [5, 3, 3, 2, 2, 1]

-- The bound `B` and the isolating intervals: the root `0` of `x ^ 5 - x` in `(-3 / 2 ^ 43, 0]`, a
-- root that a midpoint meets at an upper end; the close roots `2 ^ (-50)` and `2 ^ (-49)` in
-- intervals of their own, which no refinement narrows; the root `2 ^ (-1100)` in `(0, 3 / 2 ^ 43]`.
#guard isolatedAre #[0, -1, 0, 0, 0, 1, 0] 5 3 [(-2199023255553 / 2 ^ 41, -4398046511103 / 2 ^ 42),
    (-3 / 2 ^ 43, 0), (4398046511103 / 2 ^ 42, 2199023255553 / 2 ^ 41)]
#guard isolatedAre #[1, 0, 0, 0, 0, 1, 0] 5 3 [(-2199023255553 / 2 ^ 41, -4398046511103 / 2 ^ 42)]
#guard isolatedAre #[-36, 0, 49, 0, -14, 0, 1] 6 51
    [(-52776558133251 / 2 ^ 44, -3298534883325 / 2 ^ 40),
    (-35184372088851 / 2 ^ 44, -70368744177651 / 2 ^ 45),
    (-35184372088851 / 2 ^ 45, -70368744177651 / 2 ^ 46),
    (70368744177651 / 2 ^ 46, 35184372088851 / 2 ^ 45),
    (70368744177651 / 2 ^ 45, 35184372088851 / 2 ^ 44),
    (3298534883325 / 2 ^ 40, 52776558133251 / 2 ^ 44)]
#guard isolatedAre #[2, 0, 0, 0, 0, 0, -3] 6 3 [(-4014313797 / 2 ^ 32, -4110657328125 / 2 ^ 42),
    (4110657328125 / 2 ^ 42, 4014313797 / 2 ^ 32)]
#guard isolatedAre #[4, -6755399441055744, 2 ^ 101, 2, -3377699720527872, 2 ^ 100, 0] 5 4
    [(-173162230555 / 2 ^ 37, -1385297844439 / 2 ^ 40), (0, 1 / 2 ^ 50), (1 / 2 ^ 50, 1 / 2 ^ 49)]
#guard isolatedAre #[11141460353568528027208384512, -14855280471424633667533668352,
    16093220510710049126804881408, -3713820117856105640325283840, -9903520314283112567937171456,
    2 ^ 92, 0] 5 6
    [(-50356644087 / 2 ^ 35, -3222825221565 / 2 ^ 41), (3298534883325 / 2 ^ 41, 3 / 2),
    (3 / 2, 3298534883331 / 2 ^ 41)]
#guard isolatedAre #[-1, 2 ^ 1100, 0, 0, -1, 2 ^ 1100, 0] 5 3 [(0, 3 / 2 ^ 43)]
#guard isolatedAre #[2, -3 * 2 ^ 1070, 2 ^ 2140, 1, -3 * 2 ^ 1069, 2 ^ 2139, 0] 5 4
    [(-173162230555 / 2 ^ 37, -1385297844439 / 2 ^ 40), (0, 1 / 2 ^ 1070),
    (1 / 2 ^ 1070, 1 / 2 ^ 1069)]
#guard isolatedAre #[-6, 7 * 2 ^ 1079, -2 ^ 2159, 3, -7 * 2 ^ 1078, 2 ^ 2158, 0] 5 4
    [(1 / 2 ^ 1079, 3 / 2 ^ 1080), (3 / 2 ^ 1080, 1 / 2 ^ 1078),
    (1385297844439 / 2 ^ 40, 173162230555 / 2 ^ 37)]
#guard isolatedAre #[1, 0, -2, 0, 0, 0, 1] 6 4 [(-1099511627777 / 2 ^ 40, -1),
    (-864382581037 / 2 ^ 40, -216095645259 / 2 ^ 38),
    (216095645259 / 2 ^ 38, 864382581037 / 2 ^ 40), (1099511627775 / 2 ^ 40, 1)]
#guard isolatedAre #[1, 178, 817, -274, 16, 1, 0] 5 819
    [(-956262684767481 / 2 ^ 45, -478131342383331 / 2 ^ 44),
    (-446652582012819 / 2 ^ 51, -13957893187875 / 2 ^ 46),
    (-1624432854681 / 2 ^ 48, -12995462836629 / 2 ^ 51),
    (730635662109717 / 2 ^ 47, 1461271324220253 / 2 ^ 48),
    (871343266076829 / 2 ^ 47, 54458954129853 / 2 ^ 43)]
#guard (realRootsBound #[-(2 ^ 480 - 3), 0, 0, 0, 0, 1, 0] 5).run == 2 ^ 480 - 1
#guard (realRootsBound #[-(2 ^ 480 - 2), 0, 0, 0, 0, 1, 0] 5).run == 2 ^ 480

-- The intervals on which `f` is negative, by the bits of their ends: none
-- for `x ^ 6 + 1`, `(-∞, ∞)` for `-x ^ 6 - 1`, subnormal ends and `±0.0` for roots near `0`, none
-- for `B = 2 ^ 480`.
#guard negOf #[0, -1, 0, 0, 0, 1, 0] 5 == (2, [(0x0000000000000001, 0x3feffffffffff7ff),
    (0xfff0000000000000, 0xbff0000000000801)], true)
#guard negOf #[1, 0, 0, 0, 0, 0, 1] 6 == (0, [], true)
#guard negOf #[-1, 0, 0, 0, 0, 0, -1] 6 == (1, [(0xfff0000000000000, 0x7ff0000000000000)], true)
#guard negOf #[1, 0, 0, 0, 0, 1, 0] 5 == (1, [(0xfff0000000000000, 0xbff0000000000801)], true)
#guard negOf #[-36, 0, 49, 0, -14, 0, 1] 6 == (3, [(0x4000000000000981, 0x4007ffffffffe7ff),
    (0xbfeffffffffff97f, 0x3feffffffffff97f), (0xc007ffffffffe7ff, 0xc000000000000981)], true)
#guard negOf #[0, 4, 0, -5, 0, 1, 0] 5 == (3, [(0x3ff0000000000a01, 0x3ffffffffffff7ff),
    (0xbfeffffffffff7ff, 0xbd5c000000000001), (0xfff0000000000000, 0xc000000000000a01)], true)
#guard negOf #[0, -8, 0, 10, 0, -2, 0] 5 == (3, [(0x4000000000000a01, 0x7ff0000000000000),
    (0x0000000000000001, 0x3feffffffffff7ff), (0xbffffffffffff7ff, 0xbff0000000000a01)], true)
#guard negOf #[2, 0, 0, 0, 0, 0, -3] 6 == (2, [(0x3fede8b228a00001, 0x7ff0000000000000),
    (0xfff0000000000000, 0xbfede8b228a00001)], true)
#guard negOf #[4, -6755399441055744, 2 ^ 101, 2, -3377699720527872, 2 ^ 100, 0] 5 == (2,
    [(0x3cd0000000000001, 0x3ccfffffffffffff), (0xfff0000000000000, 0xbff428a2f98d8001)], true)
#guard negOf #[11141460353568528027208384512, -14855280471424633667533668352,
    16093220510710049126804881408, -3713820117856105640325283840, -9903520314283112567937171456,
    2 ^ 92, 0] 5 == (2, [(0x3ff8000000000001, 0x3ff7ffffffffffff),
    (0xfff0000000000000, 0xbff772fad1ee0001)], true)
#guard negOf #[-1, 2 ^ 1100, 0, 0, -1, 2 ^ 1100, 0] 5 == (1,
    [(0xfff0000000000000, 0x8000000000000001)], true)
#guard negOf #[-1, -2 ^ 1060, 0, 0, 1, 2 ^ 1060, 0] 5 == (2,
    [(0x0000000000000001, 0x3feffffffffff7ff), (0xfff0000000000000, 0xbff0000000000801)], true)
#guard negOf #[2, -3 * 2 ^ 1070, 2 ^ 2140, 1, -3 * 2 ^ 1069, 2 ^ 2139, 0] 5 == (2,
    [(0x0000000000000011, 0x000000000000000f), (0xfff0000000000000, 0xbff428a2f98d8001)], true)
#guard negOf #[-6, 7 * 2 ^ 1079, -2 ^ 2159, 3, -7 * 2 ^ 1078, 2 ^ 2158, 0] 5 == (2,
    [(0x0000000000000001, 0x3ff428a2f98d6fff), (0xfff0000000000000, 0x8000000000000001)], true)
#guard negOf #[-1, 0, 2 ^ 2060, -1, 0, 2 ^ 2060, 0] 5 == (2,
    [(0x0000000000000001, 0x8000000000000001), (0xfff0000000000000, 0xbff0000000000801)], true)
#guard negOf #[-(2 ^ 480 - 3), 0, 0, 0, 0, 1, 0] 5 == (1,
    [(0xfff0000000000000, 0x45effffffffffffe)], true)
#guard negOf #[-(2 ^ 480 - 2), 0, 0, 0, 0, 1, 0] 5 == (0, [], true)
#guard negOf #[0, 4 * 10 ^ 120, 0, -5 * 10 ^ 60, 0, 1, 0] 5 == (3,
    [(0x46293e5939a08f57, 0x46393e5939a0768d), (0xc6293e5939a0768d, 0xbd58c8dac6a0342b),
    (0xfff0000000000000, 0xc6393e5939a08f57)], true)
#guard negOf #[1, 178, 817, -274, 16, 1, 0] 5 == (3, [(0x4014c412f8cd6d75, 0x4018c3db4ed0c4e7),
    (0xbfc963a687d245ff, 0xbf77a37be4699001), (0xfff0000000000000, 0xc03b2dba0d19a7c9)], true)
#guard negOf #[21, 116, 171, 128, 55, 12, 1] 6 == (2, [(0xbff95f619980c41f, 0xbfd126145e9ef701),
    (0xc011a827999fc76f, 0xc00ddb3d742c3b21)], true)
#guard negOf #[0, 4 * 10 ^ 20, -200000000060000000000, -399999999969999999998,
    200000000059999999999, -30000000002, 1] 6 == (3, [(0x4202a05f2000018a, 0x4212a05f1ffff6b1),
    (0x3ff000000000143d, 0x3ffffffffffffd19), (0xbfeffffffffffd19, 0xbd55af1d78b58c41)], true)
#guard negOf #[135, -126, -219, 195, -130, -24, 64] 6 == (2,
    [(0x3fe4000000001001, 0x3ff7ffffffffe7ff), (0xbffdd1bdefa52fff, 0xbfe8000000001801)], true)
#guard negOf #[-7, 0, 6, 6, 10, -7, -3] 6 == (3, [(0x3ff6423c1cb0f801, 0x7ff0000000000000),
    (0xbfea5102f36a9fff, 0x3fe83158e83c8fff), (0xfff0000000000000, 0xc009d104d3704801)], true)
#guard negOf #[1, 0, -2, 0, 0, 0, 1] 6 == (2, [(0x3fe92826ef25a001, 0x3fefffffffffdfff),
    (0xbfefffffffffffff, 0xbfe92826ef25a001)], true)

-- The fuel, a device of the model: the recursion for `x ^ 5 - x` needs `3` of the `503` that
-- `JPoints.sturmIsolateFuel` gives, for the six roots `7`, for the roots `2 ^ (-50)` and
-- `2 ^ (-49)` `53`, and for one root none; with less, no interval.
#guard sturmIsolateFuel #[0, -1, 0, 0, 0, 1, 0] 5 == 503
#guard isolated #[0, -1, 0, 0, 0, 1, 0] 5 3 == isolated #[0, -1, 0, 0, 0, 1, 0] 5
#guard (isolated #[0, -1, 0, 0, 0, 1, 0] 5 2).2 == none
#guard isolated #[-36, 0, 49, 0, -14, 0, 1] 6 7 == isolated #[-36, 0, 49, 0, -14, 0, 1] 6
#guard (isolated #[-36, 0, 49, 0, -14, 0, 1] 6 6).2 == none
#guard isolated #[4, -6755399441055744, 2 ^ 101, 2, -3377699720527872, 2 ^ 100, 0] 5 53 ==
    isolated #[4, -6755399441055744, 2 ^ 101, 2, -3377699720527872, 2 ^ 100, 0] 5
#guard (isolated #[4, -6755399441055744, 2 ^ 101, 2, -3377699720527872, 2 ^ 100, 0] 5 52).2 == none
#guard isolated #[1, 0, 0, 0, 0, 1, 0] 5 0 == isolated #[1, 0, 0, 0, 0, 1, 0] 5

end JPoints

end
