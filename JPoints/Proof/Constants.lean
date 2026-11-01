/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Prime.Defs

/-!
# The facts about the compile-time constants

The facts about the values of the compile-time constants of `JPoints.Model.Constants` that the
contracts and their proofs use, and no others: each holds in every build that the C code admits, the
conditions under which `scripts/constants_check.py` varies the constants, so that the proofs hold in
every variant of the constants check. The table of the primes holds odd primes in increasing order,
`JPoints.numPrimes` of them, up to `JPoints.maxPrime < JPoints.maxPrimeEven`, and
`JPoints.maxTablePrime` is one of them; the sizes of the tables and of the bands are positive;
`JPoints.rowRanges` leaves room for the ranges of a row, `JPoints.coeffRow` for a polynomial of
degree 4 in each variable; `JPoints.rootBits` keeps the products of the real region far below the
largest double; `JPoints.tubeEps` lies between `JPoints.tubeEpsMin`, the least margin that the
proofs of the tube admit, and `1`, and `JPoints.tubeBig` is at most the scale of the default build;
and `JPoints.rowBeyond` lies beyond every third coordinate of a row and within the `long`s.
`JPoints.maxHeight`, which the constants check does not vary (the words are those of LP64), is
`⌊√(2 ^ 63 - 1)⌋`, and `JPoints.halfMask`, which it does not vary either, has the odd bits of a
word.

## Main definitions

* `JPoints.tubeEpsMin`: the least margin of the tube that the proofs admit.

## Main statements

* `JPoints.size_primeTable`, `JPoints.prime_getElem!_primeTable`,
  `JPoints.three_le_getElem!_primeTable`, `JPoints.getElem!_primeTable_lt_getElem!_primeTable`,
  `JPoints.getElem!_primeTable_le_maxPrime`: the table of the primes.
* `JPoints.maxPrime_lt_maxPrimeEven`, `JPoints.maxPrimeEven_le_256`,
  `JPoints.exists_getElem!_primeTable_eq_maxTablePrime`: the bounds of the tables.
* `JPoints.numPrimes_pos`, `JPoints.defaultSize_pos`, `JPoints.samplePairs_pos`,
  `JPoints.tubeBand_pos`, `JPoints.tubeRanges_pos`, `JPoints.nine_le_rowRanges`,
  `JPoints.five_le_coeffRow`, `JPoints.rootBits_le_480`: the sizes.
* `JPoints.isFinite_tubeEps`, `JPoints.tubeEpsMin_le_toRat_tubeEps`,
  `JPoints.toRat_tubeEps_le_one`, `JPoints.isFinite_tubeBig`,
  `JPoints.toRat_tubeBig_pos`, `JPoints.toRat_tubeBig_le`, `JPoints.isFinite_rowBeyond`,
  `JPoints.lt_toRat_rowBeyond`, `JPoints.toRat_rowBeyond_lt`: the doubles.
* `JPoints.maxHeight_sq_lt`, `JPoints.le_succ_maxHeight_sq`, `JPoints.maxHeight_lt_two_pow_32`:
  the height bound.
* `JPoints.getLsbD_halfMask`: the bits of `HALF_MASK`.

## Implementation notes

Every statement is closed and decided by the kernel (`decide +kernel`), so that it is checked anew
in each variant of the constants; `JPoints.tubeRows_pos`, which the termination of `tube_cell`
needs, is in the model. The constants of the cost model are `Float`s, about which no proof reads
anything.
-/

@[expose] public section

namespace JPoints

/-! ### The table of the primes -/

theorem size_primeTable : primeTable.size = numPrimes := by decide +kernel

theorem prime_getElem!_primeTable {pn : ℕ} (h : pn < numPrimes) : (primeTable[pn]!).Prime :=
  (by decide +kernel : ∀ pn < numPrimes, (primeTable[pn]!).Prime) pn h

/-- The primes of the table are odd. -/
theorem three_le_getElem!_primeTable {pn : ℕ} (h : pn < numPrimes) : 3 ≤ primeTable[pn]! :=
  (by decide +kernel : ∀ pn < numPrimes, 3 ≤ primeTable[pn]!) pn h

/-- The primes of the table are in increasing order. -/
theorem getElem!_primeTable_lt_getElem!_primeTable {i j : ℕ} (hij : i < j) (hj : j < numPrimes) :
    primeTable[i]! < primeTable[j]! :=
  (by decide +kernel : ∀ j < numPrimes, ∀ i < j, primeTable[i]! < primeTable[j]!) j hj i hij

theorem getElem!_primeTable_le_maxPrime {pn : ℕ} (h : pn < numPrimes) :
    primeTable[pn]! ≤ maxPrime :=
  (by decide +kernel : ∀ pn < numPrimes, primeTable[pn]! ≤ maxPrime) pn h

/-! ### The bounds of the tables -/

theorem maxPrime_lt_maxPrimeEven : maxPrime < maxPrimeEven := by decide +kernel

/-- The tables of residues have rows of at most `256` entries, so that the operands of the
reductions by reciprocals (`MODP` below `2 ^ 24`, `MOD3` below `2 ^ 16`) stay within the bounds in
which they are exact. -/
theorem maxPrimeEven_le_256 : maxPrimeEven ≤ 256 := by decide +kernel

/-- `MAX_TABLE_PRIME` is a prime of the table. -/
theorem exists_getElem!_primeTable_eq_maxTablePrime :
    ∃ pn < numPrimes, primeTable[pn]! = maxTablePrime := by
  decide +kernel

/-! ### The sizes -/

theorem numPrimes_pos : 0 < numPrimes := by decide +kernel

theorem defaultSize_pos : 0 < defaultSize := by decide +kernel

theorem samplePairs_pos : 0 < samplePairs := by decide +kernel

theorem tubeBand_pos : 0 < tubeBand := by decide +kernel

theorem tubeRanges_pos : 0 < tubeRanges := by decide +kernel

/-- The local arrays of the ranges of a row have room for the `2 * 4 + 1` ranges that the four
intervals on which `f` is negative can leave of it. -/
theorem nine_le_rowRanges : 9 ≤ rowRanges := by decide +kernel

/-- A row of an array of coefficients holds the coefficients of a polynomial of degree 4. -/
theorem five_le_coeffRow : 5 ≤ coeffRow := by decide +kernel

theorem rootBits_le_480 : rootBits ≤ 480 := by decide +kernel

/-! ### The doubles -/

theorem isFinite_tubeEps : tubeEps.isFinite = true := by decide +kernel

/-- The least margin `TUBE_EPS` of the analysis of the tube that the proofs of its soundness admit,
`2 ^ (-47)`, `64` units of `2 ^ (-53)`, of which the margin `TUBE_EPS KA`, itself within `32`
roundings, keeps at least `63` units of the absolute polynomial `KA` at the far corner of the cell
(`JPoints.TubeSetup.err_facts`). The test of `Q(±W)` needs `46` of them: `24` for its shifted
coefficients (`JPoints.Double.ApproxCoeffs.shift2Gen`: two for each power of a coordinate), `19`
for `tube_sum` and `3` for the last sum and difference of `poly_sign`
(`JPoints.Double.PolySignSetup`). The test of the quadratic in the words needs, of the margin
divided by `W`, `50` units for `K₁`: `18` for its coefficients, `13` for `tube_sum`, `3` for
`poly_sign` and `16` for the comparison of `2 W |K₂|` with `|K₁|`
(`JPoints.TubeSetup.polySignSetup_k1`); and, of the margin divided by `W²`, `20` for `K₂`. -/
def tubeEpsMin : ℚ := 1 / 2 ^ 47

theorem tubeEpsMin_eq : tubeEpsMin = 1 / 2 ^ 47 := rfl

/-- The margin of the tube is at least `JPoints.tubeEpsMin`, which the proofs of its soundness
need. -/
theorem tubeEpsMin_le_toRat_tubeEps : tubeEpsMin ≤ tubeEps.toRat := by decide +kernel

/-- The margin of the tube is at most `1`, so that the margins of the analysis stay below the
values of the polynomials that they bound. -/
theorem toRat_tubeEps_le_one : tubeEps.toRat ≤ 1 := by decide +kernel

theorem isFinite_tubeBig : tubeBig.isFinite = true := by decide +kernel

theorem toRat_tubeBig_pos : 0 < tubeBig.toRat := by decide +kernel

/-- The scale of the tube is at most that of the default build, the double nearest to `1e300`. -/
theorem toRat_tubeBig_le : tubeBig.toRat ≤ 2 ^ 997 := by decide +kernel

theorem isFinite_rowBeyond : rowBeyond.isFinite = true := by decide +kernel

/-- `ROW_BEYOND` lies beyond every third coordinate of a row, `|c| < MAX_HEIGHT + LONG_LENGTH`. -/
theorem lt_toRat_rowBeyond : (maxHeight + 64 : ℚ) < rowBeyond.toRat := by decide +kernel

/-- An end of a range of the real region within `ROW_BEYOND` converts to a `long`. -/
theorem toRat_rowBeyond_lt : rowBeyond.toRat < 2 ^ 63 := by decide +kernel

/-! ### The height bound -/

theorem maxHeight_sq_lt : maxHeight ^ 2 < 2 ^ 63 := by decide +kernel

theorem le_succ_maxHeight_sq : 2 ^ 63 ≤ (maxHeight + 1) ^ 2 := by decide +kernel

/-- `MAX_HEIGHT` is below `2 ^ 32`, so that the step between two rows of the box stays below
`2 ^ 48` and the coordinates of the box are exact as doubles. -/
theorem maxHeight_lt_two_pow_32 : maxHeight < 2 ^ 32 := by decide +kernel

/-! ### The word -/

/-- The bits of `HALF_MASK`, the fill of the bit array of a row whose first two coordinates are
even: the odd positions of a word. -/
theorem getLsbD_halfMask {t : ℕ} (ht : t < 64) :
    halfMask.toBitVec.getLsbD t = decide (t % 2 = 1) :=
  (by decide +kernel : ∀ t < 64, halfMask.toBitVec.getLsbD t = decide (t % 2 = 1)) t ht

end JPoints

end
