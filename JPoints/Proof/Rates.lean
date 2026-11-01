/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Rates
public import JPoints.Proof.Double
public import JPoints.Proof.Tables

import JPoints.Mathlib.Algebra.BigOperators.Ring.Finset
import JPoints.Mathlib.Order.WithBotTop
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.DoubleArith
import JPoints.Proof.Kummer
import JPoints.Proof.Qsort
import JPoints.Proof.Rounding
import JPoints.Proof.Values
import Mathlib.Algebra.Order.Field.Power
import Std.Tactic.Do

/-!
# The contracts of the rates of the primes

What the first part of `init_fmodpsquare` leaves for the choice of the sieving primes. For one
prime, what it writes into the tables of the curve, in the terms of `JPoints.CurveTables.PrimeWF`
and `JPoints.CurveTables.RowsWF`: the coefficients of the curve searched reduced modulo `p`
(`JPoints.initFmodpsquareCoeffs_spec`), the values of `f` modulo `p` by Horner's rule
(`JPoints.initFmodpsquareEval_spec`), whether they and the leading coefficient `f₆` are squares
modulo `p` (`JPoints.initFmodpsquareValues_spec`), and for the primes whose rows are filled
(`tabled`), the rows of the third stage of `init_table`; the tables of the other primes stay as they
were (`JPoints.CurveTables.EqOff`), and the record of the prime is that of its rate
(`JPoints.initFmodpsquarePrime_spec`). For all primes considered (`JPoints.Rates.WF`,
`JPoints.initFmodpsquareRates_spec`): the tables of the curve at each, and their records in `prec`,
permuted by `qsort` (`JPoints.PrecWF`), each with a rate that is not `0`
(`JPoints.rateOf_beq_zero_eq_false`), so that the exact count of a sampled rate of `0` changes
nothing (`JPoints.initFmodpsquareRecount_spec`).

A rate is not `0` whatever the counts that it is made from: the doubles of the counts have the sign
bit clear, and so have their products, quotients and sums, or they are NaNs
(`JPoints.Double.IsPlus`), the numerator `(p - 1) (np0 + np1) + 1` is a NaN or at least `1`
(`JPoints.Double.IsPlus.isNaN_or_one_le_add_one`), and its quotient by the exact cube of the prime,
below `2 ^ 24`, is not a zero (`JPoints.Double.div_beq_zero_eq_false`), since the rounding is
monotone (`JPoints.Double.le_doubleValue_ofDyadic`, `JPoints.Double.le_doubleValue_ofRatio`).

## Main definitions

* `JPoints.CoeffsUpTo`, `JPoints.EvalInvariant`, `JPoints.FSquaresUpTo`,
  `JPoints.RatesInvariant`: the invariants of the loops of `JPoints.initFmodpsquareCoeffs`,
  `JPoints.initFmodpsquareEval`, `JPoints.initFmodpsquareValues` and
  `JPoints.initFmodpsquareRates`.
* `JPoints.Double.IsPlus`: a NaN or a double with the sign bit clear.
* `JPoints.Entry.WF`, `JPoints.PrecWF`, `JPoints.Rates.WF`: the records of the primes and what the
  first part of `init_fmodpsquare` leaves.

## Main statements

* `JPoints.sum_range_emod_mul_pow_emod`: the value of `f` from its coefficients modulo `p`.
* `JPoints.rateOf_beq_zero_eq_false`: no rate is `0`.
* `JPoints.initFmodpsquareCoeffs_spec`, `JPoints.initFmodpsquareEval_spec`,
  `JPoints.initFmodpsquareValues_spec`, `JPoints.initFmodpsquarePrime_spec`,
  `JPoints.initFmodpsquareRecount_spec`, `JPoints.initFmodpsquareRates_spec`: the contracts.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. As in `JPoints.Proof.Tables`, the contract
of `JPoints.initFmodpsquareValues` reads the coefficients of the curve through their residues in
`coeffs_mod_p`, quantifying the coefficients, which the program does not mention, in its
postcondition. The sample of the classes `(1, b, c)` of a prime whose rows are not filled
(`JPoints.initFmodpsquareSample`) writes no table; its counts enter only the rate, and its contract
is its value (`JPoints.initFmodpsquareSample_spec`). The facts about the cubes of the primes of the
table in doubles are decided by the kernel.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The coefficients modulo a prime -/

/-- The table `coeffs_mod_p` of `JPoints.initFmodpsquareCoeffs` after the coefficients `n < k` of
the prime `p` of the index `pn`: of the size of `coeffsModP`, these entries the coefficients reduced
modulo `p`, the rows of the other primes as in `coeffsModP`. -/
def CoeffsUpTo (coeffs coeffsModP : Array ℤ) (pn p : ℕ) (arr : Array ℤ) (k : ℕ) : Prop :=
  arr.size = coeffsModP.size ∧ (∀ n < k, arr[pn * 8 + n]! = coeffs[n]! % p) ∧
    ∀ pn' ≠ pn, ∀ n < 8, arr[pn' * 8 + n]! = coeffsModP[pn' * 8 + n]!

theorem coeffsUpTo_nil (coeffs coeffsModP : Array ℤ) (pn p : ℕ) :
    CoeffsUpTo coeffs coeffsModP pn p coeffsModP ([] : List ℕ).length :=
  ⟨rfl, nofun, fun _ _ _ _ ↦ rfl⟩

theorem CoeffsUpTo.set {coeffs coeffsModP : Array ℤ} {pn p : ℕ}
    (hsize : coeffsModP.size = numPrimes * 8) (hpn : pn < numPrimes) {arr : Array ℤ}
    {pref suff : List ℕ} {cur : ℕ} (h : ForIn.toList [:7] = pref ++ cur :: suff)
    (hinv : CoeffsUpTo coeffs coeffsModP pn p arr pref.length) :
    CoeffsUpTo coeffs coeffsModP pn p (arr.set! (pn * 8 + cur) (coeffs[cur]! % p))
      (pref ++ [cur]).length := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have h7 : cur < 7 := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  obtain ⟨h1, h2, h3⟩ := hinv
  refine ⟨by rw [Array.size_set!, h1], fun n hn ↦ ?_, fun pn' hpn' n hn ↦ ?_⟩
  · rw [List.length_append, List.length_singleton] at hn
    rcases (show n = cur ∨ n < pref.length by lia) with rfl | hn'
    · rw [Array.getElem!_set!_self _ _ _ (by rw [h1, hsize]; lia)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h2 n hn']
  · rw [Array.getElem!_set!_ne _ _ _ _ fun h ↦
      hpn' (Nat.eq_and_eq_of_mul_add_eq_mul_add (by lia) hn h).1.symm, h3 pn' hpn' n hn]

theorem CoeffsUpTo.post {coeffs coeffsModP : Array ℤ} {pn p : ℕ} {arr : Array ℤ}
    (h : CoeffsUpTo coeffs coeffsModP pn p arr (ForIn.toList [:7]).length) :
    arr.size = coeffsModP.size ∧ (∀ n ≤ 6, arr[pn * 8 + n]! = coeffs[n]! % p) ∧
      ∀ pn' ≠ pn, ∀ n < 8, arr[pn' * 8 + n]! = coeffsModP[pn' * 8 + n]! := by
  rw [Std.Legacy.Range.length_toList] at h
  exact ⟨h.1, fun n hn ↦ h.2.1 n (by lia), h.2.2⟩

attribute [local irreducible] CoeffsUpTo in
/-- The coefficients of the curve searched reduced modulo `p` in the row of `pn` of
`coeffs_mod_p`. -/
@[spec]
theorem initFmodpsquareCoeffs_spec (coeffs coeffsModP : Array ℤ) (pn p : ℕ) :
    ⦃ coeffsModP.size = numPrimes * 8 ∧ pn < numPrimes ⦄
    initFmodpsquareCoeffs coeffs coeffsModP pn p
    ⦃ fun r ↦ r.size = coeffsModP.size ∧ (∀ n ≤ 6, r[pn * 8 + n]! = coeffs[n]! % p) ∧
        ∀ pn' ≠ pn, ∀ n < 8, r[pn' * 8 + n]! = coeffsModP[pn' * 8 + n]! ⦄ := by
  vcgen [initFmodpsquareCoeffs] invariants
  · fun pref _ arr ↦ CoeffsUpTo coeffs coeffsModP pn p arr pref.length
  all_goals obtain ⟨hsize, hpn⟩ := ‹coeffsModP.size = numPrimes * 8 ∧ _›
  all_goals with_reducible first
    | exact coeffsUpTo_nil coeffs coeffsModP pn p
    | exact CoeffsUpTo.post ‹_›
    | exact CoeffsUpTo.set hsize hpn ‹_› ‹_›

/-! ### The values of `f` modulo a prime -/

/-- The invariant of the loop of `JPoints.initFmodpsquareEval`, Horner's rule modulo `p` from the
coefficient of degree `deg`: after `i` steps, `s = ∑ j ≤ i, c_(deg - j) aⁱ⁻ʲ` modulo `p` for the
coefficients `c` of the row of `pn` in `coeffsModP`. -/
def EvalInvariant (coeffsModP : Array ℤ) (deg pn : ℕ) (p a : ℤ) : Std.WP.Invariant ℕ ℤ Prop :=
  fun pref _ s ↦ s = (∑ j ∈ Finset.range (pref.length + 1),
    coeffsModP[pn * 8 + (deg - j)]! * a ^ (pref.length - j)) % p

theorem evalInvariant_nil {coeffsModP : Array ℤ} {deg pn : ℕ} {p a : ℤ}
    (h : 0 ≤ coeffsModP[pn * 8 + deg]! ∧ coeffsModP[pn * 8 + deg]! < p) (suff : List ℕ) :
    EvalInvariant coeffsModP deg pn p a [] suff coeffsModP[pn * 8 + deg]! := by
  simp [EvalInvariant, Int.emod_eq_of_lt h.1 h.2]

theorem EvalInvariant.append_singleton {coeffsModP : Array ℤ} {deg pn : ℕ} {p a : ℤ} (hp : 0 < p)
    (ha : 0 ≤ a) (hc : ∀ i ≤ deg, 0 ≤ coeffsModP[pn * 8 + i]!) {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:deg] = pref ++ cur :: suff) {s : ℤ}
    (hinv : EvalInvariant coeffsModP deg pn p a pref (cur :: suff) s) :
    EvalInvariant coeffsModP deg pn p a (pref ++ [cur]) suff
      ((s * a + coeffsModP[pn * 8 + (deg - 1 - cur)]!).tmod p) := by
  have hcur := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  rw [EvalInvariant] at hinv ⊢
  have hs : 0 ≤ s := hinv ▸ Int.emod_nonneg _ hp.ne'
  rw [Int.tmod_eq_emod_of_nonneg (add_nonneg (mul_nonneg hs ha) (hc _ (by lia))), hinv,
    List.length_append, List.length_singleton, ← Finset.sum_range_mul_pow_sub_mul_add, hcur,
    Nat.sub_sub, Nat.add_comm 1 cur]
  exact ((Int.mod_modEq _ _).mul_right a).add_right _

theorem EvalInvariant.post {coeffsModP : Array ℤ} {deg pn : ℕ} {p a : ℤ} {s : ℤ}
    (h : EvalInvariant coeffsModP deg pn p a (ForIn.toList [:deg]) [] s) :
    s = (∑ i ∈ Finset.range (deg + 1), coeffsModP[pn * 8 + i]! * a ^ i) % p := by
  rw [EvalInvariant, Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  rw [h, ← Finset.sum_range_reflect]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  congr 3 <;> lia

attribute [local irreducible] EvalInvariant in
/-- `f(a)` modulo `p` by Horner's rule from the coefficients modulo `p` in the row of `pn` of
`coeffs_mod_p`, for residues of these coefficients and `a ≥ 0`. -/
@[spec]
theorem initFmodpsquareEval_spec (coeffsModP : Array ℤ) (deg pn : ℕ) (p a : ℤ) :
    ⦃ 0 < p ∧ 0 ≤ a ∧ ∀ i ≤ deg, 0 ≤ coeffsModP[pn * 8 + i]! ∧ coeffsModP[pn * 8 + i]! < p ⦄
    initFmodpsquareEval coeffsModP deg pn p a
    ⦃ fun r ↦ r = (∑ i ∈ Finset.range (deg + 1), coeffsModP[pn * 8 + i]! * a ^ i) % p ⦄ := by
  vcgen [initFmodpsquareEval] invariants
  · EvalInvariant coeffsModP deg pn p a
  all_goals obtain ⟨hp, ha, hc⟩ := ‹0 < p ∧ _›
  all_goals with_reducible first
    | exact evalInvariant_nil (hc deg le_rfl) _
    | exact EvalInvariant.post ‹_›
    | exact EvalInvariant.append_singleton hp ha (fun i hi ↦ (hc i hi).1) ‹_› ‹_›

/-! ### The squares among the values of `f` -/

/-- The table `is_f_square` of `JPoints.initFmodpsquareValues` after the residues `x < k` of the
prime `p` of the index `pn`: of the size of `isFSquare`, these entries whether `f(x)` is a square
modulo `p` (`JPoints.refIsFSquare`), the rows of the other primes as in `isFSquare`. -/
def FSquaresUpTo (cs : List ℤ) (pn p : ℕ) (isFSquare arr : Array Bool) (k : ℕ) : Prop :=
  arr.size = isFSquare.size ∧ (∀ x < k, arr[pn * maxPrimeEven + x]! = refIsFSquare cs p x) ∧
    ∀ pn' ≠ pn, ∀ x < maxPrimeEven,
      arr[pn' * maxPrimeEven + x]! = isFSquare[pn' * maxPrimeEven + x]!

/-- An entry of the row of `p` in `squares` read at a residue modulo `p` says whether it is a square
modulo `p` (`JPoints.refIsSquare`), as `init_fmodpsquare` reads it. -/
theorem bne_eq_refIsSquare {squares : Array ℤ} {pn p : ℕ}
    (h : ∀ x < p, squares[pn * maxPrime + x]! = refSquareRoot p x) (hp : 0 < p) (y : ℤ) :
    (squares[pn * maxPrime + (y % p).toNat]! != (p : ℤ)) = refIsSquare p y := by
  rw [h _ (Int.toNat_emod_lt y hp), Int.natCast_bne_natCast, refIsSquare]

/-- The value of `f` at `x` modulo `p` from the coefficients of `f` reduced modulo `p` up to a bound
`deg ≤ 6` of its degree is `F(x, 1) = f(x)` modulo `p`. -/
theorem sum_range_emod_mul_pow_emod {cs : List ℤ} {deg : ℕ} (hd : degree cs ≤ deg) (h6 : deg ≤ 6)
    (p x : ℤ) : (∑ i ∈ Finset.range (deg + 1), cs.getD i 0 % p * x ^ i) % p =
      sexticForm (cs.getD · 0) x 1 % p := by
  have hg (i : ℕ) : cs.getD i 0 % p * x ^ i % p = cs.getD i 0 * x ^ i * 1 ^ (6 - i) % p := by
    rw [one_pow, mul_one, Int.mul_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.mul_emod]
  have hz : ∑ i ∈ Finset.range (deg + 1), cs.getD i 0 * x ^ i * 1 ^ (6 - i) % p =
      ∑ i ∈ Finset.range 7, cs.getD i 0 * x ^ i * 1 ^ (6 - i) % p :=
    Finset.sum_subset (Finset.range_subset_range.2 (show deg + 1 ≤ 7 by lia)) fun i hi hi' ↦ by
      rw [Finset.mem_range] at hi hi'
      rw [getD_eq_zero_of_degree_lt (by lia)]
      simp
  rw [Finset.sum_int_mod, sexticForm, Finset.sum_int_mod (Finset.range 7)]
  simp only [hg, hz]

theorem FSquaresUpTo.set {cs : List ℤ} {pn p : ℕ} {isFSquare arr : Array Bool} {k x : ℕ}
    (hpn : pn < numPrimes) (hpM : p ≤ maxPrimeEven)
    (hsize : isFSquare.size = numPrimes * maxPrimeEven) (hx : x < p) (hk : x = k)
    (h : FSquaresUpTo cs pn p isFSquare arr k) {v : Bool} (hv : v = refIsFSquare cs p x) :
    FSquaresUpTo cs pn p isFSquare (arr.set! (pn * maxPrimeEven + x) v) (k + 1) := by
  subst hk
  have hxM := lt_of_lt_of_le hx hpM
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [Array.size_set!, h1], fun y hy ↦ ?_, fun pn' hpn' y hy ↦ ?_⟩
  · rcases (show y = x ∨ y < x by lia) with rfl | hy'
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [h1, hsize]; exact Nat.mul_add_lt_mul_of_lt hpn le_rfl hxM), hv]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h2 y hy']
  · rw [Array.getElem!_set!_ne _ _ _ _ fun h ↦
      hpn' (Nat.eq_and_eq_of_mul_add_eq_mul_add hxM hy h).1.symm, h3 pn' hpn' y hy]

theorem fsquaresUpTo_one {squares coeffsModP : Array ℤ} {isFSquare : Array Bool} {pn p : ℕ}
    {cs : List ℤ} (h : PrimeRowArgs squares coeffsModP pn p cs) (hpn : pn < numPrimes)
    (hpM : p ≤ maxPrimeEven) (hsize : isFSquare.size = numPrimes * maxPrimeEven) (n : ℕ) :
    FSquaresUpTo cs pn p isFSquare (n, isFSquare.set! (pn * maxPrimeEven)
      (squares[pn * maxPrime + coeffsModP[pn * 8]!.toNat]! != (p : ℤ))).2
      (([] : List ℕ).length + 1) := by
  have h0 := h.coeffs (n := 0) (by lia)
  rw [Nat.add_zero] at h0
  have := FSquaresUpTo.set (cs := cs) (x := 0) hpn hpM hsize h.pos rfl
    ⟨rfl, nofun, fun _ _ _ _ ↦ rfl⟩
    (v := squares[pn * maxPrime + coeffsModP[pn * 8]!.toNat]! != (p : ℤ)) (by
      rw [h0, bne_eq_refIsSquare (fun x hx ↦ h.squares hx) h.pos, refIsFSquare]
      simp [sexticForm, Finset.sum_range_succ])
  rwa [Nat.add_zero] at this

theorem FSquaresUpTo.append_singleton {squares coeffsModP : Array ℤ} {isFSquare : Array Bool}
    {deg pn p : ℕ} {cs : List ℤ} (h : PrimeRowArgs squares coeffsModP pn p cs)
    (hd : degree cs ≤ deg) (h6 : deg ≤ 6) (hpn : pn < numPrimes) (hpM : p ≤ maxPrimeEven)
    (hsize : isFSquare.size = numPrimes * maxPrimeEven) {pref suff : List ℕ} {cur : ℕ}
    (hc : ForIn.toList [1:p] = pref ++ cur :: suff) {arr : Array Bool}
    (hinv : FSquaresUpTo cs pn p isFSquare arr (pref.length + 1)) {s : ℤ}
    (hs : s = (∑ i ∈ Finset.range (deg + 1), coeffsModP[pn * 8 + i]! * (cur : ℤ) ^ i) % p)
    (n : ℕ) :
    FSquaresUpTo cs pn p isFSquare (n, arr.set! (pn * maxPrimeEven + cur)
      (squares[pn * maxPrime + s.toNat]! != (p : ℤ))).2 ((pref ++ [cur]).length + 1) := by
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hcp := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  rw [List.length_append, List.length_singleton]
  refine hinv.set hpn hpM hsize hcp (by lia) ?_
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [h.coeffs (by simp at hi; lia)],
    sum_range_emod_mul_pow_emod hd h6] at hs
  rw [hs, bne_eq_refIsSquare (fun x hx ↦ h.squares hx) h.pos, refIsFSquare]

theorem FSquaresUpTo.post {squares coeffsModP : Array ℤ} {isFSquare : Array Bool} {pn p : ℕ}
    {cs : List ℤ} (h : PrimeRowArgs squares coeffsModP pn p cs) {arr : Array Bool}
    (hinv : FSquaresUpTo cs pn p isFSquare arr ((ForIn.toList [1:p]).length + 1))
    (hasInfinity H : Array Bool) (n : ℕ) :
    hasInfinity.set! pn (squares[pn * maxPrime + coeffsModP[pn * 8 + 6]!.toNat]! != (p : ℤ)) =
        hasInfinity.set! pn (refHasInfinity cs p) ∧
      (H, arr, n).2.1.size = isFSquare.size ∧
      (∀ x < p, (H, arr, n).2.1[pn * maxPrimeEven + x]! = refIsFSquare cs p x) ∧
      ∀ pn', ¬pn' = pn → ∀ x < maxPrimeEven,
        (H, arr, n).2.1[pn' * maxPrimeEven + x]! = isFSquare[pn' * maxPrimeEven + x]! := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_add_cancel h.pos] at hinv
  rw [h.coeffs le_rfl, bne_eq_refIsSquare (fun x hx ↦ h.squares hx) h.pos]
  exact ⟨rfl, hinv⟩

theorem PrimeRowArgs.initFmodpsquareEval_pre {squares coeffsModP : Array ℤ} {pn p : ℕ} {cs : List ℤ}
    (h : PrimeRowArgs squares coeffsModP pn p cs) {deg : ℕ} (h6 : deg ≤ 6) (a : ℕ) :
    0 < (p : ℤ) ∧ 0 ≤ (a : ℤ) ∧
      ∀ i ≤ deg, 0 ≤ coeffsModP[pn * 8 + i]! ∧ coeffsModP[pn * 8 + i]! < p := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  refine ⟨hp, Int.natCast_nonneg a, fun i hi ↦ ?_⟩
  rw [h.coeffs (by lia)]
  exact ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩

attribute [local irreducible] FSquaresUpTo in
/-- `init_fmodpsquare` records for the prime `p` of the index `pn` whether the curve with the
coefficients `cs` of degree at most `deg ≤ 6`, whose rows of `p` it is given
(`JPoints.PrimeRowArgs`), has points at infinity modulo `p` and which values of `f` are squares
modulo `p`: the first by its leading coefficient `f₆`, the value at `0` by `f₀`, the others by
`JPoints.initFmodpsquareEval` (`JPoints.sum_range_emod_mul_pow_emod`). -/
theorem initFmodpsquareValues_spec_of_primeRowArgs (squares coeffsModP : Array ℤ)
    (hasInfinity isFSquare : Array Bool) (deg pn p : ℕ) (cs : List ℤ) :
    ⦃ PrimeRowArgs squares coeffsModP pn p cs ∧ degree cs ≤ deg ∧ deg ≤ 6 ∧
      pn < numPrimes ∧ p ≤ maxPrimeEven ∧ isFSquare.size = numPrimes * maxPrimeEven ⦄
    initFmodpsquareValues squares coeffsModP hasInfinity isFSquare deg pn p
    ⦃ fun r ↦ r.1 = hasInfinity.set! pn (refHasInfinity cs p) ∧ r.2.1.size = isFSquare.size ∧
        (∀ x < p, r.2.1[pn * maxPrimeEven + x]! = refIsFSquare cs p x) ∧
        ∀ pn' ≠ pn, ∀ x < maxPrimeEven,
          r.2.1[pn' * maxPrimeEven + x]! = isFSquare[pn' * maxPrimeEven + x]! ⦄ := by
  vcgen [initFmodpsquareValues] invariants
  · fun pref _ s ↦ FSquaresUpTo cs pn p isFSquare s.2 (pref.length + 1)
  · fun pref _ s ↦ FSquaresUpTo cs pn p isFSquare s.2 (pref.length + 1)
  all_goals obtain ⟨h, hd, h6, hpn, hpM, hsize⟩ := ‹PrimeRowArgs squares coeffsModP pn p cs ∧ _›
  all_goals with_reducible first
    | exact fsquaresUpTo_one h hpn hpM hsize _
    | exact FSquaresUpTo.append_singleton h hd h6 hpn hpM hsize ‹_› ‹_› ‹_› _
    | exact FSquaresUpTo.post h ‹_› _ _ _
    | exact h.initFmodpsquareEval_pre h6 _

/-- `init_fmodpsquare` records for the prime `p` of the index `pn` whether the curve has points at
infinity modulo `p` (`JPoints.refHasInfinity`) and which values of `f` are squares modulo `p`
(`JPoints.refIsFSquare`), for the coefficients `cs` of every curve of degree at most `deg ≤ 6`
whose rows of `p` it is given (`JPoints.PrimeRowArgs`), and leaves the rows of the other primes as
they were. -/
@[spec]
theorem initFmodpsquareValues_spec (squares coeffsModP : Array ℤ)
    (hasInfinity isFSquare : Array Bool) (deg pn p : ℕ) :
    ⦃ deg ≤ 6 ∧ pn < numPrimes ∧ p ≤ maxPrimeEven ∧ isFSquare.size = numPrimes * maxPrimeEven ⦄
    initFmodpsquareValues squares coeffsModP hasInfinity isFSquare deg pn p
    ⦃ fun r ↦ ∀ cs, PrimeRowArgs squares coeffsModP pn p cs → degree cs ≤ deg →
        r.1 = hasInfinity.set! pn (refHasInfinity cs p) ∧ r.2.1.size = isFSquare.size ∧
        (∀ x < p, r.2.1[pn * maxPrimeEven + x]! = refIsFSquare cs p x) ∧
        ∀ pn' ≠ pn, ∀ x < maxPrimeEven,
          r.2.1[pn' * maxPrimeEven + x]! = isFSquare[pn' * maxPrimeEven + x]! ⦄ :=
  ⟨fun ⟨h6, hpn, hpM, hs⟩ cs h hd ↦ (initFmodpsquareValues_spec_of_primeRowArgs squares coeffsModP
    hasInfinity isFSquare deg pn p cs).le_wp ⟨h, hd, h6, hpn, hpM, hs⟩⟩

/-! ### The tables of the curve at a prime -/

/-- The sample of the classes `(1, b, c)` of a prime writes no table: its contract is its value. -/
@[spec]
theorem initFmodpsquareSample_spec (squares coeffsModP : Array ℤ) (deg pn p pp : ℕ)
    (recip : UInt64) (stride : ℕ) :
    ⦃ True ⦄ initFmodpsquareSample squares coeffsModP deg pn p pp recip stride
    ⦃ fun r ↦ r = (initFmodpsquareSample squares coeffsModP deg pn p pp recip stride).run ⦄ :=
  Std.WP.Id.triple_eq_run _

/-- The arguments of `init_fmodpsquare` for the prime `p = prime[pn]` after the coefficients modulo
`p`: the rows of `p` (`JPoints.PrimeRowArgs`) for the coefficients of the curve searched. -/
theorem primeRowArgs_of_coeffsModP {t : Tables} (ht : t.WF) {pn : ℕ} (hpn : pn < numPrimes)
    {coeffs coeffsModP : Array ℤ}
    (hco : ∀ n ≤ 6, coeffsModP[pn * 8 + n]! = coeffs[n]! % primeTable[pn]!) :
    PrimeRowArgs t.squares coeffsModP pn primeTable[pn]! coeffs.toList where
  pos := lt_of_lt_of_le (by decide) (three_le_getElem!_primeTable hpn)
  squares hx := ht.squares hpn hx
  coeffs hn := by rw [hco _ hn, ← Array.getD_toList_eq_getElem!]

/-- The tables of the curve after the coefficients, the points at infinity and the values of `f`
that are squares modulo the prime `prime[pn]` agree with `ct` off `pn`. -/
theorem CurveTables.eqOff_of_initFmodpsquareValues {ct : CurveTables} {pn : ℕ}
    {coeffsModP : Array ℤ} (h1 : coeffsModP.size = ct.coeffsModP.size)
    (h2 : ∀ pn', ¬pn' = pn → ∀ n < 8, coeffsModP[pn' * 8 + n]! = ct.coeffsModP[pn' * 8 + n]!)
    {hasInfinity isFSquare : Array Bool} {v : Bool} (h3 : hasInfinity = ct.hasInfinity.set! pn v)
    (h4 : isFSquare.size = ct.isFSquare.size)
    (h5 : ∀ pn', ¬pn' = pn → ∀ x < maxPrimeEven,
      isFSquare[pn' * maxPrimeEven + x]! = ct.isFSquare[pn' * maxPrimeEven + x]!) :
    ct.EqOff ⟨coeffsModP, hasInfinity, isFSquare, ct.isPointOnJ⟩ pn where
  size_coeffsModP := h1
  size_hasInfinity := by rw [h3, Array.size_set!]
  size_isFSquare := h4
  size_isPointOnJ := rfl
  primeWF hpn hp := ⟨fun hn ↦ by rw [h2 _ hpn _ (by lia), hp.coeffsModP hn],
    by rw [h3, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hpn), hp.hasInfinity],
    fun hx ↦ by rw [h5 _ hpn _ (lt_maxPrimeEven_of_lt_getElem!_primeTable hx), hp.isFSquare hx]⟩
  rowsWF _ hr := hr

/-- The tables of the curve after the coefficients, the points at infinity and the values of `f`
that are squares modulo the prime `prime[pn]`, for the curve searched with the coefficients
`coeffs`, agree with `ct` off `pn` and hold the tables of the curve at `pn`. -/
theorem eqOff_and_primeWF_of_initFmodpsquareValues {t : Tables} (ht : t.WF) {pn : ℕ}
    (hpn : pn < numPrimes) {coeffs : Array ℤ} {deg : ℕ} (hd : degree coeffs.toList ≤ deg)
    {ct : CurveTables} (hsize : ct.hasInfinity.size = numPrimes) {coeffsModP : Array ℤ}
    (hco : coeffsModP.size = ct.coeffsModP.size ∧
      (∀ n ≤ 6, coeffsModP[pn * 8 + n]! = coeffs[n]! % primeTable[pn]!) ∧
      ∀ pn', ¬pn' = pn → ∀ n < 8, coeffsModP[pn' * 8 + n]! = ct.coeffsModP[pn' * 8 + n]!)
    {hasInfinity isFSquare : Array Bool}
    (hva : ∀ cs, PrimeRowArgs t.squares coeffsModP pn primeTable[pn]! cs → degree cs ≤ deg →
      hasInfinity = ct.hasInfinity.set! pn (refHasInfinity cs primeTable[pn]!) ∧
      isFSquare.size = ct.isFSquare.size ∧
      (∀ x < primeTable[pn]!,
        isFSquare[pn * maxPrimeEven + x]! = refIsFSquare cs primeTable[pn]! x) ∧
      ∀ pn', ¬pn' = pn → ∀ x < maxPrimeEven,
        isFSquare[pn' * maxPrimeEven + x]! = ct.isFSquare[pn' * maxPrimeEven + x]!) :
    ct.EqOff ⟨coeffsModP, hasInfinity, isFSquare, ct.isPointOnJ⟩ pn ∧
      (⟨coeffsModP, hasInfinity, isFSquare, ct.isPointOnJ⟩ : CurveTables).PrimeWF
        coeffs.toList pn := by
  have ha := primeRowArgs_of_coeffsModP ht hpn hco.2.1
  obtain ⟨h1, h2, h3, h4⟩ := hva _ ha hd
  refine ⟨CurveTables.eqOff_of_initFmodpsquareValues hco.1 hco.2.2 h1 h2 h4,
    ⟨fun hn ↦ ha.coeffs hn, ?_, fun hx ↦ h3 _ hx⟩⟩
  rw [h1]
  exact Array.getElem!_set!_self _ _ _ (hsize ▸ hpn)

/-- The tables of the curve after `init_table` for the prime `prime[pn]`, from tables `ct₁` that
agree with `ct` off `pn` and hold the tables of the curve at `pn`: they agree with `ct` off `pn` and
hold the tables of the curve and the rows of the third stage at `pn`. -/
theorem eqOff_and_primeWF_and_rowsWF_of_initTable {ct ct₁ ct₂ : CurveTables} {cs : List ℤ}
    {deg pn : ℕ} (h : ct.EqOff ct₁ pn ∧ ct₁.PrimeWF cs pn)
    (ht : ∀ cs, (∀ n ≤ 6, ct₁.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!) →
      ct₂.coeffsModP = ct₁.coeffsModP ∧ ct₂.hasInfinity = ct₁.hasInfinity ∧
      ct₂.isFSquare = ct₁.isFSquare ∧ ct₁.EqOff ct₂ pn ∧ ct₂.RowsWF cs deg pn) :
    ct.EqOff ct₂ pn ∧ ct₂.PrimeWF cs pn ∧ ct₂.RowsWF cs deg pn := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht cs fun n hn ↦ h.2.coeffsModP hn
  exact ⟨h.1.trans h4, ⟨fun hn ↦ h1 ▸ h.2.coeffsModP hn, h2 ▸ h.2.hasInfinity,
    fun hx ↦ h3 ▸ h.2.isFSquare hx⟩, h5⟩

/-- `init_fmodpsquare` fills the tables of the curve at the prime `prime[pn]` for the curve
searched with the coefficients `coeffs` of degree at most `deg ≤ 6` (`JPoints.CurveTables.PrimeWF`),
and when its rows are filled, which `tabled` then says, the rows of the third stage
(`JPoints.CurveTables.RowsWF`); the tables of the other primes stay as they were
(`JPoints.CurveTables.EqOff`); and the record of the prime holds its rate, made from counts that the
contract leaves open. -/
@[spec]
theorem initFmodpsquarePrime_spec (t : Tables) (coeffs : Array ℤ) (deg : ℕ) (ct : CurveTables)
    (r : Rates) (pn : ℕ) :
    ⦃ t.WF ∧ pn < numPrimes ∧ degree coeffs.toList ≤ deg ∧ deg ≤ 6 ∧
      ct.coeffsModP.size = numPrimes * 8 ∧ ct.hasInfinity.size = numPrimes ∧
      ct.isFSquare.size = numPrimes * maxPrimeEven ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven ⦄
    initFmodpsquarePrime t coeffs deg ct r pn
    ⦃ fun r' ↦ ct.EqOff r'.1 pn ∧ r'.1.PrimeWF coeffs.toList pn ∧
        (r'.2.tabled[pn]! = true → r'.1.RowsWF coeffs.toList deg pn) ∧
        r'.2.tabled = r.tabled.set! pn
          ((primeTable[pn]! * primeTable[pn]! + samplePairs - 1) / samplePairs == 1) ∧
        r'.2.sampled = r.sampled.set! pn
          (decide (1 < (primeTable[pn]! * primeTable[pn]! + samplePairs - 1) / samplePairs)) ∧
        ∃ np0 count total : ℕ, r'.2.prec = r.prec.set! pn
          { p := primeTable[pn]!, n := pn, np0 := np0
            r := rateOf primeTable[pn]! np0 (Double.ofInt count *
              Double.ofInt (primeTable[pn]! * primeTable[pn]! : ℕ) / Double.ofInt total) } ⦄ := by
  vcgen [initFmodpsquarePrime]
  all_goals try dsimp only at *
  all_goals obtain ⟨ht, hpn, hd, h6, hs1, hs2, hs3, hs4⟩ := ‹t.WF ∧ _›
  all_goals try refine ⟨?_, ?_, ?_, ?_, _, _, _, rfl⟩
  all_goals with_reducible first
    | exact ⟨hs1, hpn⟩
    | exact ⟨h6, hpn, (getElem!_primeTable_le_maxPrime hpn).trans maxPrime_lt_maxPrimeEven.le, hs3⟩
    | exact ⟨ht, hpn, h6, hs4⟩
    | exact (eqOff_and_primeWF_and_rowsWF_of_initTable
        (eqOff_and_primeWF_of_initFmodpsquareValues ht hpn hd hs2 ‹_› ‹_›) ‹_›).1
    | exact (eqOff_and_primeWF_and_rowsWF_of_initTable
        (eqOff_and_primeWF_of_initFmodpsquareValues ht hpn hd hs2 ‹_› ‹_›) ‹_›).2.1
    | exact fun _ ↦ (eqOff_and_primeWF_and_rowsWF_of_initTable
        (eqOff_and_primeWF_of_initFmodpsquareValues ht hpn hd hs2 ‹_› ‹_›) ‹_›).2.2
    | exact Array.set!_set!_eq_set!_of_eq_true ‹_›
    | exact (eqOff_and_primeWF_of_initFmodpsquareValues ht hpn hd hs2 ‹_› ‹_›).1
    | exact (eqOff_and_primeWF_of_initFmodpsquareValues ht hpn hd hs2 ‹_› ‹_›).2
    | exact fun h ↦ absurd h (Array.getElem!_set!_false_ne_true _ _)
    | exact Array.set!_eq_set!_of_not_eq_true ‹_›

/-! ### The signs and the rounding of the operations -/

namespace Double

theorem signBit_ofRatio (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (ofRatio neg n d).signBit = neg := by
  by_cases hn : n = 0
  · subst hn; cases neg <;> simp only [ofRatio, ↓reduceIte, Bool.false_eq_true] <;> decide
  · rw [ofRatio_eq d hn]; exact signBit_ofSignificand neg _ (ofRatio_rounding hn hd).1

theorem isNaN_quiet {x : Double} (h : x.isNaN = true) : x.quiet.isNaN = true := by
  simp only [isNaN, expField, fracField, quiet, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h ⊢
  rw [UInt64.shiftRight_or, show (0x0008000000000000 : UInt64) >>> 52 = 0 by decide,
    UInt64.or_zero]
  refine ⟨h.1, fun h0 ↦ ?_⟩
  have h1 : (x.bits ||| 0x0008000000000000) &&& 0xfffffffffffff =
      (x.bits &&& 0xfffffffffffff) ||| 0x0008000000000000 :=
    UInt64.toBitVec_inj.1 (BitVec.and_or_distrib_right.trans (by rfl))
  rw [h1, ← UInt64.toNat_zero, UInt64.toNat_inj, UInt64.or_eq_zero_iff] at h0
  exact absurd h0.2 (by decide)

theorem isNaN_propagateNaN {x y : Double} (h : (x.isNaN || y.isNaN) = true) :
    (propagateNaN x y).isNaN = true := by
  rw [propagateNaN]
  split_ifs with hx
  · exact isNaN_quiet hx
  · exact isNaN_quiet (by simpa [hx] using h)

/-- The exact value of a double with the sign bit clear, by a natural significand. -/
theorem exists_toDyadic_eq_natCast {x : Double} (hs : x.signBit = false) :
    ∃ m : ℕ, x.toDyadic = ((m : ℤ), x.toDyadic.2) ∧ x.toRat = m * 2 ^ x.toDyadic.2 := by
  refine ⟨if x.expField = 0 then x.fracField else x.fracField + 2 ^ 52, ?_, ?_⟩
  · rw [toDyadic_eq, hs]; simp
  · rw [toRat_eq, toDyadic_eq, hs]; simp

/-- A double that is not finite, with the sign bit clear, has the value `+∞`, a NaN included. -/
theorem doubleValue_eq_top {x : Double} (hs : x.signBit = false) (hf : x.isFinite = false) :
    doubleValue x.bits = ⊤ := by
  rw [doubleValue_bits, ite_eq_left (by simpa [isFinite] using hf), hs]
  rfl

theorem doubleValue_zero : doubleValue zero.bits = ((0 : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat (by decide), toRat_eq]
  simp [show zero.toDyadic = (0, -1074) by decide]

/-- The rounding of `JPoints.Double.ofDyadic` is monotone: a double `T` not above `m 2 ^ e` is not
above its rounding, by the faithful rounding (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`)
when that is finite. -/
theorem le_doubleValue_ofDyadic {T : Double} (hT : T.isNaN = false) {m : ℕ} (hm : m ≠ 0) (e : ℤ)
    (h : doubleValue T.bits ≤ ((m * 2 ^ e : ℚ) : WithBotTop ℚ)) :
    doubleValue T.bits ≤ doubleValue (ofDyadic false m e).bits := by
  have hr := isNaN_ofDyadic false m e
  cases hf : (ofDyadic false m e).isFinite
  · rw [doubleValue_eq_top (signBit_ofDyadic ..) hf]; exact le_top
  · exact le_of_lt_nextUp hr hT (ne_huge_of_isFinite hf).1
      (h.trans_lt (by simpa using (lt_nextUp_and_nextDown_lt_ofDyadic hm hf).1))

/-- The rounding of `JPoints.Double.ofRatio` is monotone: a double `T` not above `n / d` is not
above its rounding, by the faithful rounding (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`)
when that is finite. -/
theorem le_doubleValue_ofRatio {T : Double} (hT : T.isNaN = false) {n d : ℕ} (hn : n ≠ 0)
    (hd : d ≠ 0) (h : doubleValue T.bits ≤ ((n / d : ℚ) : WithBotTop ℚ)) :
    doubleValue T.bits ≤ doubleValue (ofRatio false n d).bits := by
  have hr := isNaN_ofRatio false n hd
  cases hf : (ofRatio false n d).isFinite
  · rw [doubleValue_eq_top (signBit_ofRatio _ _ hd) hf]; exact le_top
  · exact le_of_lt_nextUp hr hT (ne_huge_of_isFinite hf).1
      (h.trans_lt (by simpa using (lt_nextUp_and_nextDown_lt_ofRatio hn hd hf).1))

theorem beq_zero_eq_false_of_le {x : Double} {c : ℚ} (hc : 0 < c) (hx : x.isNaN = false)
    (h : (c : WithBotTop ℚ) ≤ doubleValue x.bits) : x.beq zero = false := by
  rw [Bool.eq_false_iff, ne_eq, beq_eq_true_iff hx (by decide), doubleValue_zero]
  intro h'
  rw [h', WithBotTop.coe_le_coe] at h
  exact absurd h (not_le.2 hc)

theorem signBit_eq_false_of_le {x : Double} {c : ℚ} (hc : 0 < c)
    (h : (c : WithBotTop ℚ) ≤ doubleValue x.bits) : x.signBit = false := by
  rw [doubleValue_bits] at h
  split_ifs at h with he hs
  · exact absurd h (not_le.2 (WithBotTop.bot_lt_coe c))
  · simpa using hs
  · rw [WithBotTop.coe_le_coe, toRat_eq_fields] at h
    by_contra hs
    simp only [Bool.not_eq_false] at hs
    simp only [hs, ↓reduceIte, neg_one_mul] at h
    have : 0 ≤ (if x.expField = 0 then (x.fracField : ℚ) * 2 ^ (-1074 : ℤ)
      else (2 ^ 52 + x.fracField) * 2 ^ ((x.expField : ℤ) - 1075)) := by split_ifs <;> positivity
    linarith

/-- A NaN, or a double with the sign bit clear: `+0.0`, a positive double or `+∞`. Products,
quotients and sums of such doubles are such doubles (`JPoints.Double.IsPlus.mul`,
`JPoints.Double.IsPlus.div`, `JPoints.Double.IsPlus.add`). -/
abbrev IsPlus (x : Double) : Prop := x.isNaN = true ∨ x.signBit = false

theorem isPlus_ofInt_natCast (n : ℕ) : (ofInt n).IsPlus :=
  .inr (by rw [signBit_ofInt]; exact decide_eq_false (by lia))

theorem IsPlus.mul {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x * y).IsPlus := by
  change (Double.mul x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.mul, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  have hxs : x.signBit = false := hx.resolve_left fun h ↦ h1 (by simp [h])
  have hys : y.signBit = false := hy.resolve_left fun h ↦ h1 (by simp [h])
  simp only [Double.mul, h1, Bool.false_eq_true, ↓reduceIte, hxs, hys, bne_self_eq_false]
  split_ifs
  · exact .inl (by decide)
  · exact .inr (by decide)
  · generalize x.toDyadic = dx
    generalize y.toDyadic = dy
    obtain ⟨mx, ex⟩ := dx
    obtain ⟨my, ey⟩ := dy
    exact .inr (signBit_ofDyadic ..)

theorem IsPlus.div {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x / y).IsPlus := by
  change (Double.div x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.div, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  have hxs : x.signBit = false := hx.resolve_left fun h ↦ h1 (by simp [h])
  have hys : y.signBit = false := hy.resolve_left fun h ↦ h1 (by simp [h])
  obtain ⟨my, hmy, hry⟩ := exists_toDyadic_eq_natCast hys
  generalize y.toDyadic.2 = ey at hmy hry
  have hmy0 (h : ¬y.isZero = true) : my ≠ 0 := by
    rintro rfl; exact isZero_eq_false_iff.mp (Bool.eq_false_iff.mpr h) (by simp [hry])
  simp only [Double.div, h1, hxs, hys, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmy,
    Int.natAbs_natCast]
  split_ifs
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact .inr (by decide)
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact .inr (signBit_ofRatio _ _ (hmy0 ‹_›))
  · exact .inr (signBit_ofRatio _ _ (Nat.mul_ne_zero (hmy0 ‹_›) (by positivity)))

theorem IsPlus.add {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x + y).IsPlus := by
  change (Double.add x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.add, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  have hxs : x.signBit = false := hx.resolve_left fun h ↦ h1 (by simp [h])
  have hys : y.signBit = false := hy.resolve_left fun h ↦ h1 (by simp [h])
  obtain ⟨mx, hmx, -⟩ := exists_toDyadic_eq_natCast hxs
  obtain ⟨my, hmy, -⟩ := exists_toDyadic_eq_natCast hys
  generalize x.toDyadic.2 = ex at hmx
  generalize y.toDyadic.2 = ey at hmy
  simp only [Double.add, h1, hxs, hys, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte, hmx, hmy]
  split_ifs
  · exact .inr ‹_›
  · exact .inr hys
  · exact .inr (by decide)
  · exact .inr (by rw [signBit_ofDyadic]; exact decide_eq_false (not_lt.2 (by positivity)))

private theorem isNaN_one : (1.0 : Double).isNaN = false := by decide

private theorem isInf_one : (1.0 : Double).isInf = false := by decide

private theorem signBit_one : (1.0 : Double).signBit = false := by decide

private theorem toDyadic_one : (1.0 : Double).toDyadic = (2 ^ 52, -52) := by decide

private theorem doubleValue_one :
    doubleValue (1.0 : Double).bits = ((1 : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat (by decide), toRat_eq, toDyadic_one]
  norm_num

-- The rounding of a natural number times a power of `2` that is at least `1` is at least `1`.
private theorem one_le_doubleValue_ofDyadic {s : ℤ} {N : ℕ} (hs : s = N) {e : ℤ}
    (h : (1 : ℚ) ≤ N * 2 ^ e) :
    ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue (ofDyadic (decide (s < 0)) s.natAbs e).bits := by
  subst hs
  rw [Int.natAbs_natCast, decide_eq_false (by lia), ← doubleValue_one]
  refine le_doubleValue_ofDyadic isNaN_one (fun h0 ↦ ?_) e (by rwa [doubleValue_one,
    WithBotTop.coe_le_coe])
  rw [h0, Nat.cast_zero, zero_mul] at h
  exact absurd h (by norm_num)

/-- A double with the sign bit clear plus `1.0` is a NaN or at least `1`: the sum is exact or
rounded, and its rounding is monotone (`JPoints.Double.le_doubleValue_ofDyadic`). -/
theorem IsPlus.isNaN_or_one_le_add_one {x : Double} (hx : x.IsPlus) :
    (x + 1.0).isNaN = true ∨ ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue (x + 1.0).bits := by
  change (Double.add x 1.0).isNaN = true ∨ _ ≤ doubleValue (Double.add x 1.0).bits
  by_cases hn : x.isNaN = true
  · simp only [Double.add, hn, Bool.true_or, ↓reduceIte]
    exact .inl (isNaN_propagateNaN (by simp [hn]))
  have hxs := hx.resolve_left hn
  simp only [Double.add, hn, isNaN_one, isInf_one, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, toDyadic_one, hxs, signBit_one]
  obtain ⟨m, hm, hr⟩ := exists_toDyadic_eq_natCast hxs
  generalize x.toDyadic.2 = ex at hm hr
  rw [hm]
  split_ifs with hxi hs0
  · exact .inr (by rw [doubleValue_eq_top hxs (by simp_all [isInf, isFinite])]; exact le_top)
  · exact absurd hs0 (by positivity)
  refine .inr (one_le_doubleValue_ofDyadic (by push_cast; rfl) ?_)
  rw [Nat.cast_add, add_mul, natCast_mul_two_pow_mul_zpow m (min_le_left ex (-52)),
    natCast_mul_two_pow_mul_zpow 4503599627370496 (min_le_right ex (-52))]
  norm_num
  positivity

-- The value of the least subnormal `⟨1⟩`.
private theorem doubleValue_one_bits : doubleValue (⟨1⟩ : Double).bits =
    (((2 : ℚ) ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat (by decide), toRat_eq, show (⟨1⟩ : Double).toDyadic = (1, -1074) by
    decide]
  simp

/-- The rounding of `n / d ≥ 2 ^ (-24)` is not a zero: it is at least the least subnormal. -/
theorem ofRatio_beq_zero_eq_false {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : (2 : ℚ) ^ (-24 : ℤ) ≤ n / d) : (ofRatio false n d).beq zero = false := by
  refine beq_zero_eq_false_of_le (c := 2 ^ (-1074 : ℤ)) (by positivity) (isNaN_ofRatio _ _ hd) ?_
  rw [← doubleValue_one_bits]
  refine le_doubleValue_ofRatio (by decide) hn hd ?_
  rw [doubleValue_one_bits, WithBotTop.coe_le_coe]
  exact (zpow_le_zpow_right₀ one_le_two (by norm_num)).trans h

-- A quotient of a number at least `1` by a positive number at most `2 ^ 24`.
private theorem two_zpow_neg_le_div {X Y : ℚ} (hX : 1 ≤ X) (hY : 0 < Y) (hY' : Y ≤ 2 ^ 24) :
    (2 : ℚ) ^ (-24 : ℤ) ≤ X / Y := by
  rw [zpow_neg, zpow_ofNat, ← one_div]
  exact div_le_div₀ (by linarith) hX hY hY'

-- The last case of `JPoints.Double.div` for the significands and exponents of the operands, whose
-- quotient is at least `2 ^ (-24)`.
private theorem ratio_beq_zero_eq_false {mx my : ℕ} {ex ey : ℤ} (hmx : mx ≠ 0) (hmy : my ≠ 0)
    (h : (2 : ℚ) ^ (-24 : ℤ) ≤ mx * 2 ^ ex / (my * 2 ^ ey)) :
    (if 0 ≤ ex - ey then ofRatio false (mx * 2 ^ (ex - ey).toNat) my
      else ofRatio false mx (my * 2 ^ (-(ex - ey)).toNat)).beq zero = false := by
  have : (my : ℚ) ≠ 0 := mod_cast hmy
  split_ifs with hk
  · refine ofRatio_beq_zero_eq_false (Nat.mul_ne_zero hmx (by positivity)) hmy (h.trans_eq ?_)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hk,
      zpow_sub₀ two_ne_zero]
    field
  · refine ofRatio_beq_zero_eq_false hmx (Nat.mul_ne_zero hmy (by positivity)) (h.trans_eq ?_)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg (by lia), zpow_neg, zpow_sub₀ two_ne_zero]
    field

-- The significands and exponents of a double at least `1` and of a positive double at most
-- `2 ^ 24`, whose quotient is at least `2 ^ (-24)`.
private theorem exists_toDyadic_div {x y : Double} (hxs : x.signBit = false)
    (hx1 : 1 ≤ x.toRat) (hys : y.signBit = false) (hy0 : y.isZero = false)
    (hy1 : y.toRat ≤ 2 ^ 24) :
    ∃ mx my : ℕ, ∃ ex ey : ℤ, x.toDyadic = ((mx : ℤ), ex) ∧ y.toDyadic = ((my : ℤ), ey) ∧
      mx ≠ 0 ∧ my ≠ 0 ∧
      (2 : ℚ) ^ (-24 : ℤ) ≤ mx * 2 ^ ex / (my * 2 ^ ey) := by
  obtain ⟨mx, hmx, hrx⟩ := exists_toDyadic_eq_natCast hxs
  obtain ⟨my, hmy, hry⟩ := exists_toDyadic_eq_natCast hys
  have hY : 0 < y.toRat :=
    lt_of_le_of_ne (hry ▸ by positivity) (Ne.symm (isZero_eq_false_iff.mp hy0))
  refine ⟨mx, my, _, _, hmx, hmy, fun h0 ↦ ?_, fun h0 ↦ ?_,
    hrx ▸ hry ▸ two_zpow_neg_le_div hx1 hY hy1⟩
  · rw [hrx, h0, Nat.cast_zero, zero_mul] at hx1; exact absurd hx1 (by norm_num)
  · rw [hry, h0, Nat.cast_zero, zero_mul] at hY; exact lt_irrefl _ hY

/-- A NaN or a double at least `1`, divided by a positive double at most `2 ^ 24`, is not a zero:
the quotient is a NaN, `+∞`, or the rounding of a number at least `2 ^ (-24)`. -/
theorem div_beq_zero_eq_false {x y : Double}
    (hx : x.isNaN = true ∨ ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue x.bits)
    (hy : y.isFinite = true) (hys : y.signBit = false) (hy0 : y.isZero = false)
    (hy1 : y.toRat ≤ 2 ^ 24) : (x / y).beq zero = false := by
  change (div x y).beq zero = false
  have hyn : y.isNaN = false := by simp_all [isFinite, isNaN]
  by_cases hn : x.isNaN = true
  · simp only [div, hn, Bool.true_or, ↓reduceIte, beq, isNaN_propagateNaN (x := x) (y := y)
      (by simp [hn]), Bool.not_true, Bool.false_and]
  have hx1 := hx.resolve_left hn
  have hxs := signBit_eq_false_of_le one_pos hx1
  by_cases hxi : x.isInf = true
  · simp only [div, hn, hyn, hxs, hys, hxi, bne_self_eq_false, isInf_eq_false_of_isFinite hy,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    decide
  rw [doubleValue_eq_toRat (isFinite_of_isInf_eq_false (by simpa using hn) (by simpa using hxi)),
    WithBotTop.coe_le_coe] at hx1
  obtain ⟨mx, my, ex, ey, hmx, hmy, hmx0, hmy0, h2⟩ := exists_toDyadic_div hxs hx1 hys hy0 hy1
  simp only [div, hn, hyn, hxs, hys, hxi, bne_self_eq_false, isInf_eq_false_of_isFinite hy, hy0,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hmx, hmy, Int.natAbs_natCast]
  exact ratio_beq_zero_eq_false hmx0 hmy0 h2

end Double

/-! ### The rates are not `0` -/

open Double in
-- The cube of a prime of the table in doubles, the denominator of its rate.
private theorem ofInt_cube_primeTable {pn : ℕ} (hpn : pn < numPrimes) :
    (ofInt primeTable[pn]! * ofInt primeTable[pn]! * ofInt primeTable[pn]!).isFinite = true ∧
      (ofInt primeTable[pn]! * ofInt primeTable[pn]! * ofInt primeTable[pn]!).signBit = false ∧
      (ofInt primeTable[pn]! * ofInt primeTable[pn]! * ofInt primeTable[pn]!).isZero = false ∧
      (ofInt primeTable[pn]! * ofInt primeTable[pn]! * ofInt primeTable[pn]!).toRat ≤ 2 ^ 24 := by
  revert pn
  decide +kernel

/-- The rate of a prime of the table is not `0` for every estimate `np1` of the classes `(1, b, c)`
that is a NaN or has the sign bit clear: its numerator `(p - 1) (np0 + np1) + 1` is a NaN or at
least `1`, and its denominator `p p p` is the exact cube, below `2 ^ 24`. -/
theorem rateOf_beq_zero_eq_false {pn : ℕ} (hpn : pn < numPrimes) (np0 : ℕ) {np1 : Double}
    (h : np1.IsPlus) : (rateOf primeTable[pn]! np0 np1).beq .zero = false := by
  obtain ⟨h1, h2, h3, h4⟩ := ofInt_cube_primeTable hpn
  have hp := three_le_getElem!_primeTable hpn
  refine Double.div_beq_zero_eq_false (Double.IsPlus.isNaN_or_one_le_add_one (.mul (.inr ?_)
    (.add (Double.isPlus_ofInt_natCast np0) h))) h1 h2 h3 h4
  rw [Double.signBit_ofInt]
  exact decide_eq_false (by lia)

/-! ### The exact count of a sampled rate of `0` -/

-- The verification conditions of `JPoints.initFmodpsquareRecount`, each in its shape.

private theorem recount_absurd {nPrimes : ℕ} {prec : Array Entry} {sampled : Array Bool}
    (h : ∀ pn < nPrimes, prec[pn]!.r.beq .zero = false) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:nPrimes] = pref ++ cur :: suff) {α β : Type} {x : α × Array Entry × β}
    {a : α} {b : β} (he : x = (a, prec, b))
    (hc : (sampled[cur]! && x.2.1[cur]!.r.beq 0.0) = true) : False := by
  subst he
  rw [show (0.0 : Double) = .zero from rfl,
    h cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl), Bool.and_false] at hc
  exact Bool.false_ne_true hc

private theorem recount_post {ct : CurveTables} {r : Rates}
    {x : CurveTables × Array Entry × Array Bool} (he : x = (ct, r.prec, r.tabled)) :
    (x.1, { prec := x.2.1, sampled := r.sampled, tabled := x.2.2 : Rates }) = (ct, r) := by
  subst he; rfl

private theorem recount_skip {α β γ : Type} {x : α × β × γ} {y : α × β × γ} (he : x = y) :
    (x.1, x.2.1, x.2.2) = y := he

/-- The exact count of a sampled rate of `0` changes nothing when no rate of the primes considered
is `0` (`JPoints.rateOf_beq_zero_eq_false`). -/
@[spec]
theorem initFmodpsquareRecount_spec (t : Tables) (degree nPrimes : ℕ) (ct : CurveTables)
    (r : Rates) :
    ⦃ ∀ pn < nPrimes, r.prec[pn]!.r.beq .zero = false ⦄
    initFmodpsquareRecount t degree nPrimes ct r
    ⦃ fun s ↦ s = (ct, r) ⦄ := by
  vcgen [initFmodpsquareRecount] invariants
  · fun _ _ s ↦ s = (ct, r.prec, r.tabled)
  all_goals with_reducible first
    | exact recount_post ‹_›
    | exact recount_skip ‹_›
    | exact (recount_absurd ‹_› ‹_› ‹_› ‹_›).elim

/-! ### The records of the primes -/

/-- The record `e` of `prec` that `init_fmodpsquare` makes for the prime `prime[pn]`: the prime,
its index, and a rate that is not `0`. -/
structure Entry.WF (e : Entry) (pn : ℕ) : Prop where
  /-- The index of the prime. -/
  n_eq : e.n = pn
  /-- The prime. -/
  p_eq : e.p = primeTable[pn]!
  /-- The rate is not `0`. -/
  beq_zero : e.r.beq .zero = false

/-- The records `prec` of the first `nPrimes` primes of the table, in some order: the indices in
their first `nPrimes` entries are those of the primes, each record holding its prime and a rate
that is not `0`. -/
structure PrecWF (nPrimes : ℕ) (prec : Array Entry) : Prop where
  /-- `prec` has an entry for every prime of the table. -/
  size_eq : prec.size = numPrimes
  /-- The first `nPrimes` records hold the indices of the first `nPrimes` primes. -/
  perm : ((prec.toList.take nPrimes).map Entry.n).Perm (List.range nPrimes)
  /-- Each of them holds its prime and a rate that is not `0`. -/
  mem {e : Entry} (he : e ∈ prec.toList.take nPrimes) : e.WF e.n

/-- The records of the first `nPrimes` primes of the table in their order, sorted by `qsort`. -/
theorem precWF_qsort {nPrimes : ℕ} (hn : nPrimes ≤ numPrimes) {prec : Array Entry}
    (hs : prec.size = numPrimes) (h : ∀ j < nPrimes, prec[j]!.WF j) (cmp : Entry → Entry → ℤ) :
    PrecWF nPrimes (qsort cmp prec nPrimes) := by
  have hp := take_toList_qsort_perm cmp (show nPrimes ≤ prec.size by lia)
  have hm : (prec.toList.take nPrimes).map Entry.n = List.range nPrimes := by
    refine List.ext_getElem (by simp; lia) fun j h1 h2 ↦ ?_
    simp only [List.getElem_map, Array.getElem_take_toList, List.getElem_range]
    exact (h j (by simpa using h2)).n_eq
  refine ⟨(size_qsort cmp (by lia)).trans hs, hm ▸ hp.map _, fun he ↦ ?_⟩
  obtain ⟨j, hj, -, rfl⟩ := Array.exists_eq_of_mem_take_toList (hp.subset he)
  exact (h j hj).n_eq.symm ▸ h j hj

namespace PrecWF

variable {nPrimes : ℕ} {prec : Array Entry}

theorem le_size (h : PrecWF nPrimes prec) : nPrimes ≤ prec.size := by
  have := h.perm.length_eq
  simp only [List.length_map, List.length_take, Array.length_toList, List.length_range] at this
  lia

theorem mem_take (h : PrecWF nPrimes prec) {m : ℕ} (hm : m < nPrimes) :
    prec[m]! ∈ prec.toList.take nPrimes :=
  Array.mem_take_toList_of_lt hm h.le_size

theorem n_lt (h : PrecWF nPrimes prec) {m : ℕ} (hm : m < nPrimes) : prec[m]!.n < nPrimes :=
  List.mem_range.mp (h.perm.subset (List.mem_map_of_mem (h.mem_take hm)))

theorem p_eq (h : PrecWF nPrimes prec) {m : ℕ} (hm : m < nPrimes) :
    prec[m]!.p = primeTable[prec[m]!.n]! :=
  (h.mem (h.mem_take hm)).p_eq

theorem beq_zero (h : PrecWF nPrimes prec) {m : ℕ} (hm : m < nPrimes) :
    prec[m]!.r.beq .zero = false :=
  (h.mem (h.mem_take hm)).beq_zero

theorem n_injective (h : PrecWF nPrimes prec) {m m' : ℕ} (hm : m < nPrimes) (hm' : m' < nPrimes)
    (he : prec[m]!.n = prec[m']!.n) : m = m' := by
  have hl : ((prec.toList.take nPrimes).map Entry.n).length = nPrimes := by
    simp only [List.length_map, List.length_take, Array.length_toList]; lia [h.le_size]
  have h1 : m < ((prec.toList.take nPrimes).map Entry.n).length := hm.trans_eq hl.symm
  have h2 : m' < ((prec.toList.take nPrimes).map Entry.n).length := hm'.trans_eq hl.symm
  refine ((h.perm.nodup_iff.mpr List.nodup_range).getElem_inj_iff (hi := h1) (hj := h2)).mp ?_
  rw [List.getElem_map, List.getElem_map, Array.getElem_take_toList, Array.getElem_take_toList, he]

end PrecWF

/-! ### The rates of the primes -/

/-- The invariant of the loop of `JPoints.initFmodpsquareRates` over the primes, after the first
`k` primes of the table, for the curve searched with the coefficients `cs` of degree at most `deg`:
the tables of the curve keep their sizes and hold the tables of the curve at these primes, the rows
of the third stage where `tabled` says so, and `prec` their records. -/
structure RatesInvariant (cs : List ℤ) (deg k : ℕ) (ct : CurveTables) (r : Rates) : Prop where
  /-- The size of the coefficients modulo the primes. -/
  size_coeffsModP : ct.coeffsModP.size = numPrimes * 8
  /-- The size of the table of the points at infinity. -/
  size_hasInfinity : ct.hasInfinity.size = numPrimes
  /-- The size of the table of the values of `f` that are squares. -/
  size_isFSquare : ct.isFSquare.size = numPrimes * maxPrimeEven
  /-- The size of the table of the third stage. -/
  size_isPointOnJ : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven
  /-- The tables of the curve at the primes so far. -/
  primeWF {pn : ℕ} (hpn : pn < k) : ct.PrimeWF cs pn
  /-- The rows of the third stage of the primes so far whose rows are filled. -/
  rowsWF {pn : ℕ} (h : r.tabled[pn]! = true) : pn < k ∧ ct.RowsWF cs deg pn
  /-- The size of `tabled`. -/
  size_tabled : r.tabled.size = numPrimes
  /-- The size of `prec`. -/
  size_prec : r.prec.size = numPrimes
  /-- The records of the primes so far. -/
  prec {j : ℕ} (hj : j < k) : r.prec[j]!.WF j

theorem ratesInvariant_nil {cs : List ℤ} {deg : ℕ} {ct : CurveTables}
    (h1 : ct.coeffsModP.size = numPrimes * 8) (h2 : ct.hasInfinity.size = numPrimes)
    (h3 : ct.isFSquare.size = numPrimes * maxPrimeEven)
    (h4 : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven) {prec : Array Entry}
    (hp : prec.size = numPrimes) :
    RatesInvariant cs deg ([] : List ℕ).length ct
      { prec, sampled := .replicate numPrimes false, tabled := .replicate numPrimes false } where
  size_coeffsModP := h1
  size_hasInfinity := h2
  size_isFSquare := h3
  size_isPointOnJ := h4
  primeWF h := absurd h (Nat.not_lt_zero _)
  rowsWF {pn} h :=
    absurd ((Array.getElem!_replicate_default (α := Bool) numPrimes pn).symm.trans h)
      Bool.false_ne_true
  size_tabled := Array.size_replicate
  size_prec := hp
  prec h := absurd h (Nat.not_lt_zero _)

namespace RatesInvariant

variable {cs : List ℤ} {deg : ℕ} {ct : CurveTables} {r : Rates}

theorem recount_pre {nPrimes : ℕ}
    (h : RatesInvariant cs deg (ForIn.toList [:nPrimes]).length ct r) {pn : ℕ}
    (hpn : pn < nPrimes) :
    r.prec[pn]!.r.beq .zero = false :=
  (h.prec (by rw [Std.Legacy.Range.length_toList]; lia)).beq_zero

theorem prime_pre {t : Tables} (ht : t.WF) {nPrimes : ℕ} (hn : nPrimes ≤ numPrimes)
    (hd : degree cs ≤ deg) (h6 : deg ≤ 6) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:nPrimes] = pref ++ cur :: suff)
    (h : RatesInvariant cs deg pref.length ct r) :
    t.WF ∧ cur < numPrimes ∧ degree cs ≤ deg ∧ deg ≤ 6 ∧
      ct.coeffsModP.size = numPrimes * 8 ∧ ct.hasInfinity.size = numPrimes ∧
      ct.isFSquare.size = numPrimes * maxPrimeEven ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven :=
  ⟨ht, by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hl], hd, h6, h.size_coeffsModP,
    h.size_hasInfinity, h.size_isFSquare, h.size_isPointOnJ⟩

-- The record of the prime `prime[cur]` that `init_fmodpsquare` writes, and the others.
private theorem wf_getElem!_set! {k cur : ℕ} (hk : k = cur) (hcn : cur < numPrimes)
    {prec : Array Entry} (hs : prec.size = numPrimes) (h : ∀ {j : ℕ}, j < k → prec[j]!.WF j)
    (np0 count total : ℕ) {j : ℕ} (hj : j < cur + 1) :
    (prec.set! cur
      { p := primeTable[cur]!, n := cur, np0 := np0
        r := rateOf primeTable[cur]! np0 (Double.ofInt count *
          Double.ofInt (primeTable[cur]! * primeTable[cur]! : ℕ) / Double.ofInt total) })[j]!.WF
      j := by
  rcases (show j = cur ∨ j < cur by lia) with rfl | hj
  · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hcn)]
    exact ⟨rfl, rfl, rateOf_beq_zero_eq_false hcn np0 (.div
      (.mul (Double.isPlus_ofInt_natCast count) (Double.isPlus_ofInt_natCast _))
      (Double.isPlus_ofInt_natCast total))⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h (by lia)

theorem append_singleton {nPrimes : ℕ} (hn : nPrimes ≤ numPrimes) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:nPrimes] = pref ++ cur :: suff)
    (h : RatesInvariant cs deg pref.length ct r) {ct' : CurveTables} {r' : Rates} {b b' : Bool}
    (hs : ct.EqOff ct' cur ∧ ct'.PrimeWF cs cur ∧ (r'.tabled[cur]! = true → ct'.RowsWF cs deg cur) ∧
      r'.tabled = r.tabled.set! cur b ∧ r'.sampled = r.sampled.set! cur b' ∧
      ∃ np0 count total : ℕ, r'.prec = r.prec.set! cur
        { p := primeTable[cur]!, n := cur, np0 := np0
          r := rateOf primeTable[cur]! np0 (Double.ofInt count *
            Double.ofInt (primeTable[cur]! * primeTable[cur]! : ℕ) / Double.ofInt total) }) :
    RatesInvariant cs deg (pref ++ [cur]).length ct' r' := by
  obtain ⟨he, hp, hr, ht, -, np0, count, total, hprec⟩ := hs
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcn : cur < numPrimes := by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hl]
  rw [List.length_append, List.length_singleton, hc]
  refine ⟨he.size_coeffsModP.trans h.size_coeffsModP, he.size_hasInfinity.trans h.size_hasInfinity,
    he.size_isFSquare.trans h.size_isFSquare, he.size_isPointOnJ.trans h.size_isPointOnJ,
    fun {pn} hpn ↦ ?_, fun {pn} hpn ↦ ?_, by rw [ht, Array.size_set!, h.size_tabled],
    by rw [hprec, Array.size_set!, h.size_prec],
    hprec ▸ wf_getElem!_set! hc hcn h.size_prec h.prec np0 count total⟩
  · rcases (show pn = cur ∨ pn < cur by lia) with rfl | hpn
    · exact hp
    · exact he.primeWF (by lia) (h.primeWF (by lia))
  · by_cases hpc : pn = cur
    · subst hpc; exact ⟨by lia, hr hpn⟩
    · rw [ht, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hpc)] at hpn
      exact ⟨by lia [(h.rowsWF hpn).1], he.rowsWF hpc (h.rowsWF hpn).2⟩

end RatesInvariant

/-- What the first part of `init_fmodpsquare` leaves for the choice of the primes, for the curve
searched with the coefficients `cs` of degree at most `deg` and the first `nPrimes` primes of the
table: the tables of the curve at these primes, the rows of the third stage of those whose rows
`tabled` says are filled, the sizes of `tabled` and of the table of the third stage, and their
records in `prec` (`JPoints.PrecWF`). -/
structure Rates.WF (r : Rates) (ct : CurveTables) (cs : List ℤ) (deg nPrimes : ℕ) : Prop where
  /-- The tables of the curve at the primes considered. -/
  primeWF {pn : ℕ} (hpn : pn < nPrimes) : ct.PrimeWF cs pn
  /-- The rows of the third stage of the primes whose rows are filled. -/
  rowsWF {pn : ℕ} (h : r.tabled[pn]! = true) : ct.RowsWF cs deg pn
  /-- The size of `tabled`. -/
  size_tabled : r.tabled.size = numPrimes
  /-- The size of the table of the third stage. -/
  size_isPointOnJ : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven
  /-- The records of the primes considered. -/
  prec : PrecWF nPrimes r.prec

theorem RatesInvariant.wf {cs : List ℤ} {deg nPrimes : ℕ} (hn : nPrimes ≤ numPrimes)
    {ct : CurveTables} {r : Rates} (h : RatesInvariant cs deg (ForIn.toList [:nPrimes]).length ct r)
    {s : CurveTables × Rates} (hs : s = (ct, r)) :
    { s.2 with prec := qsort compareEntries s.2.prec nPrimes }.WF s.1 cs deg nPrimes := by
  subst hs
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact ⟨h.primeWF, fun hpn ↦ (h.rowsWF hpn).2, h.size_tabled, h.size_isPointOnJ,
    precWF_qsort hn h.size_prec (fun _ hj ↦ h.prec hj) _⟩

/-- `init_fmodpsquare` up to the choice of the primes fills the tables of the curve at the first
`nPrimes` primes of the table, and the rows of the third stage of those whose rows `tabled` says
are filled, for the curve searched with the coefficients `coeffs` of degree at most `deg ≤ 6`, and
leaves their records in `prec`, sorted by rate (`JPoints.Rates.WF`): each prime by
`JPoints.initFmodpsquarePrime_spec` (`JPoints.RatesInvariant`), then the exact count of a sampled
rate of `0`, which changes nothing (`JPoints.initFmodpsquareRecount_spec`). -/
@[spec]
theorem initFmodpsquareRates_spec (t : Tables) (coeffs : Array ℤ) (deg nPrimes : ℕ)
    (ct : CurveTables) (prec : Array Entry) :
    ⦃ t.WF ∧ nPrimes ≤ numPrimes ∧ degree coeffs.toList ≤ deg ∧ deg ≤ 6 ∧
      ct.coeffsModP.size = numPrimes * 8 ∧ ct.hasInfinity.size = numPrimes ∧
      ct.isFSquare.size = numPrimes * maxPrimeEven ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven ∧ prec.size = numPrimes ⦄
    initFmodpsquareRates t coeffs deg nPrimes ct prec
    ⦃ fun r ↦ r.2.WF r.1 coeffs.toList deg nPrimes ⦄ := by
  vcgen [initFmodpsquareRates] invariants
  · fun pref _ s ↦ RatesInvariant coeffs.toList deg pref.length s.1 s.2
  all_goals try dsimp only at *
  all_goals obtain ⟨ht, hn, hd, h6, h1, h2, h3, h4, hp⟩ := ‹t.WF ∧ _›
  all_goals with_reducible first
    | exact ratesInvariant_nil h1 h2 h3 h4 hp
    | exact RatesInvariant.recount_pre ‹_› ‹_›
    | exact RatesInvariant.prime_pre ht hn hd h6 ‹_› ‹_›
    | exact RatesInvariant.append_singleton hn ‹_› ‹_› ‹_›
    | exact RatesInvariant.wf hn ‹_› ‹_›

end JPoints

end
