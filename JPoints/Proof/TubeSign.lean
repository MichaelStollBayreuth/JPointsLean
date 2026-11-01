/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TubeApprox

import JPoints.Proof.Double
import JPoints.Proof.DoubleArith
import JPoints.Proof.TubeCoeffs
import JPoints.Proof.Rounding
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The sign of a polynomial over a cell in doubles

`poly_sign` (`JPoints.polySign`) decides the sign of a polynomial in two variables over a cell
from its coefficients at the centre of the cell, in doubles: a sign when the constant term exceeds
the sum `tube_sum` of the other terms at the corner of the cell plus a margin `e`, and bounds
`lo` and `hi` on the absolute value. When the doubles approximate the exact coefficients `V` of
the polynomial at the centre with the majorants `A` (`JPoints.Double.ApproxCoeffs`) and the margin
covers the rounding errors, relative to the majorants at the corner, `M = ∑ A_{jk} R ^ j S ^ k`
(`JPoints.Double.PolySignSetup`), a sign of `poly_sign` is that of the exact polynomial throughout
the cell (`JPoints.Double.PolySignSetup.mul_pos_eval2`), `hi` bounds its absolute value
(`JPoints.Double.PolySignSetup.abs_eval2_le`) and a positive `lo` bounds it from below
(`JPoints.Double.PolySignSetup.lo_le_abs_eval2`). Over the box `|s| ≤ R`, `|t| ≤ S` a
polynomial lies within the sum of the absolute values of its other terms at the corner of its
constant term (`JPoints.absSum`, `JPoints.abs_eval2_sub_le`).

## Main definitions

* `JPoints.absSum`: the sum of the absolute values of the terms of a polynomial at a corner.
* `JPoints.Double.PolySignSetup`: the setting of a call of `poly_sign`.

## Main statements

* `JPoints.abs_eval2_sub_le`, `JPoints.abs_eval2_sub_le_absSum`: a polynomial over a box.
* `JPoints.Double.PolySignSetup.mul_pos_eval2`, `JPoints.Double.PolySignSetup.abs_eval2_le`,
  `JPoints.Double.PolySignSetup.lo_le_abs_eval2`: the verdict and the bounds of `poly_sign`.
* `JPoints.Double.isFinite_of_lt_sub`, `JPoints.Double.div_bounds`: doubles of a margin.

## Implementation notes

The sums of `poly_sign` are sums of finite doubles, which round on the grid `2 ^ (-1074) ℤ` without
the error of the subnormal range; their finiteness comes from the comparisons themselves: a sum
without sign bits that some double is below when subtracted from a finite double is finite
(`JPoints.Double.isFinite_of_lt_sub`), and so are its operands. The arithmetic of the margins is in
units `2 ^ (-53)` of the majorants at the corner: `n + D + |JPoints.evalIndices D| + 3` of them
cover the `n` roundings of the coefficients, those of `tube_sum` and of the sum with `e`.
-/

@[expose] public section

namespace JPoints

open Finset

namespace Double

/-! ### Doubles -/

theorem lt_iff_toRat_lt {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x.lt y = true ↔ x.toRat < y.toRat := by
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite hx) (isNaN_eq_false_of_isFinite hy),
    doubleValue_eq_toRat hx, doubleValue_eq_toRat hy, WithBotTop.coe_lt_coe]

theorem zero_lt_iff_toRat_pos {x : Double} (hx : x.isFinite = true) :
    (0.0 : Double).lt x = true ↔ 0 < x.toRat := by
  rw [show (0.0 : Double) = zero from rfl, lt_iff_toRat_lt isFinite_zero hx, toRat_zero]

-- `x - s` for a finite `x` and an `s` that is a NaN is a NaN.
private theorem isNaN_sub_of_isNaN {x s : Double} (hx : x.isFinite = true) (hs : s.isNaN = true) :
    (x - s).isNaN = true := by
  have e : x - s = s.quiet := by
    change sub x s = _
    simp [sub, propagateNaN, isNaN_eq_false_of_isFinite hx, hs]
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq] at hs
  rw [e, isNaN_quiet hs.1]

/-- A double without a sign bit that some double is below when subtracted from a finite double is
finite: `x - NaN` is a NaN, `x - ∞` is `-∞`, and nothing is below either. -/
theorem isFinite_of_lt_sub {x s z : Double} (hx : x.isFinite = true) (hs : s.signBit = false)
    (h : z.lt (x - s) = true) : s.isFinite = true := by
  have hxn := isNaN_eq_false_of_isFinite hx
  have hn : (x - s).isNaN = false := by
    simp only [lt, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.2
  have hsn : s.isNaN = false := by
    by_contra hsn
    rw [isNaN_sub_of_isNaN hx (by simpa using hsn)] at hn
    exact absurd hn (by decide)
  cases hi : s.isInf
  · exact isFinite_of_isInf_eq_false hsn hi
  · have e : x - s = s.neg := by
      rw [sub_eq_add_neg hxn hsn]
      change add x s.neg = _
      simp [add, hxn, isNaN_neg, hsn, isInf_eq_false_of_isFinite hx, isInf_neg, hi]
    rw [e] at h hn
    rw [lt_eq_true_iff (by simp_all [lt]) hn, doubleValue_of_isInf ((isInf_neg s).trans hi),
      signBit_neg, hs] at h
    simp at h

/-- A quotient of doubles without sign bits by a finite double that is not zero has no sign
bit. -/
theorem signBit_div {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false)
    (hyf : y.isFinite = true) (hy0 : y.isZero = false) : (x / y).signBit = false := by
  change (div x y).signBit = false
  have hd := natAbs_toDyadic_fst_ne_zero (isZero_eq_false_iff.mp hy0)
  simp only [div, hx, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    isInf_eq_false_of_isFinite hyf, hy0]
  split_ifs with h1 h2 h3
  · exact signBit_propagateNaN hx hy
  · decide
  · exact signBit_ofRatio _ _ hd
  · exact signBit_ofRatio _ _ (by positivity)

theorem isFinite_of_isFinite_div {x y : Double} (h : (x / y).isFinite = true) :
    x.isFinite = true := by
  change (div x y).isFinite = true at h
  by_contra hx
  simp only [div] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · simp [isFinite_propagateNaN h1] at h
  all_goals try exact absurd h (by decide)
  all_goals
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
    exact hx (isFinite_of_isInf_eq_false h1.1 (by simpa using h2))

/-- A double without a sign bit below `y` puts `0.0` below `y`. -/
theorem zero_lt_of_lt {z y : Double} (hz : z.signBit = false) (h : z.lt y = true) :
    (0.0 : Double).lt y = true := by
  obtain ⟨-, hyn, hlt⟩ := lt_eq_true_iff'.mp h
  rw [← isNaN_eq_false_iff] at hyn
  rw [show (0.0 : Double) = zero from rfl, lt_eq_true_iff (by decide) hyn,
    doubleValue_eq_toRat isFinite_zero, toRat_zero]
  refine lt_of_le_of_lt ?_ hlt
  rw [doubleValue_bits]
  split_ifs with h1 h2
  · simp_all
  · exact le_top
  · exact WithBotTop.coe_le_coe.mpr (toRat_nonneg hz)

theorem isFinite_of_isFinite_iterate_mul {x y : Double} {j : ℕ}
    (h : ((· * x)^[j] y).isFinite = true) : y.isFinite = true := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h
    exact ih (isFinite_and_of_isFinite_mul h).1

/-- A finite iterated product `(· * x)^[j] y` of doubles without sign bits has no sign bit. -/
theorem signBit_iterate_mul_of_isFinite {x y : Double} (hx : x.signBit = false)
    (hy : y.signBit = false) {j : ℕ} (h : ((· * x)^[j] y).isFinite = true) :
    ((· * x)^[j] y).signBit = false := by
  induction j with
  | zero => exact hy
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at h ⊢
    obtain ⟨h1, h2⟩ := isFinite_and_of_isFinite_mul h
    rw [signBit_mul_of_isFinite h1 h2, ih h1, hx]
    rfl

end Double

theorem OnGrid.le_of_pos {k : ℕ} {v : ℚ} (h : OnGrid k v) (hv : 0 < v) : 1 / 2 ^ k ≤ v := by
  obtain ⟨n, rfl⟩ := h
  have hn : (0 : ℚ) < n := by
    by_contra! hn
    exact absurd hv (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hn (by positivity)))
  have : (1 : ℚ) ≤ n := mod_cast (show (1 : ℤ) ≤ n from mod_cast hn)
  exact div_le_div_of_nonneg_right this (by positivity)

namespace Double

theorem lt_two_pow_1022_of_le {x : ℚ} (h : x ≤ 2 ^ 60) : x < 2 ^ 1022 :=
  h.trans_lt (pow_lt_pow_right₀ one_lt_two (by norm_num))

-- The quotient `x / y` of a finite `0 ≤ x ≤ 2 ^ 1000` by a finite `y ≥ 1`: finite, and within
-- `x / y / 2 ^ 53 + 2 ^ (-1075)` of `x / y`.
private theorem div_rounding {x y : Double} (hx : x.isFinite = true) (hx0 : 0 ≤ x.toRat)
    (hxb : x.toRat ≤ 2 ^ 1000) (hy : y.isFinite = true) (hy1 : 1 ≤ y.toRat) :
    (x / y).isFinite = true ∧
      |(x / y).toRat - x.toRat / y.toRat| ≤ x.toRat / y.toRat / 2 ^ 53 + 1 / 2 ^ 1075 := by
  have hr := isRounding_div hx hy (by linarith)
  have hv0 : 0 ≤ x.toRat / y.toRat := div_nonneg hx0 (by linarith)
  have hf := hr.isFinite_of_abs_lt (by
    rw [abs_of_nonneg hv0]
    exact ((div_le_self hx0 hy1).trans hxb).trans_lt (pow_lt_pow_right₀ one_lt_two (by norm_num)))
  have hab := hr.abs_sub_le hf
  rw [abs_of_nonneg hv0, show (-1075 : ℤ) = -((1075 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
    ← one_div] at hab
  exact ⟨hf, hab⟩

/-- The quotient `x / y` of a finite `0 ≤ x ≤ 2 ^ 1000` on the grid `2 ^ (-k) ℤ` by a finite
`1 ≤ y ≤ 2 ^ m`, `k + m ≤ 900`, is finite and lies within `2 ^ (-52) x / y` of `x / y`: the error
of the subnormal range vanishes, as a positive `x` is at least `2 ^ (-k)`. -/
theorem div_bounds {x y : Double} {k m : ℕ} (hx : x.isFinite = true) (hx0 : 0 ≤ x.toRat)
    (hg : OnGrid k x.toRat) (hxb : x.toRat ≤ 2 ^ 1000) (hy : y.isFinite = true)
    (hy1 : 1 ≤ y.toRat) (hym : y.toRat ≤ 2 ^ m) (hkm : k + m ≤ 900) :
    (x / y).isFinite = true ∧ |(x / y).toRat - x.toRat / y.toRat| ≤
      x.toRat / y.toRat / 2 ^ 52 := by
  obtain ⟨hf, hab⟩ := div_rounding hx hx0 hxb hy hy1
  refine ⟨hf, ?_⟩
  rcases hx0.eq_or_lt with h0 | h0
  · rw [← h0, zero_div, sub_zero, zero_div, zero_add] at hab
    rw [← h0, zero_div, sub_zero, zero_div, (onGrid_toRat _).eq_of_abs_sub_lt (.zero 1074) (by
      rw [sub_zero]
      exact hab.trans_lt (one_div_lt_one_div_of_lt (by positivity)
        (pow_lt_pow_right₀ one_lt_two (by norm_num)))), abs_zero]
  · have hv : 1 / 2 ^ (k + m) ≤ x.toRat / y.toRat := by
      rw [pow_add, ← div_div]
      exact div_le_div₀ (by positivity) (hg.le_of_pos h0) (by positivity) hym
    have : (1 : ℚ) / 2 ^ 1075 ≤ x.toRat / y.toRat / 2 ^ 53 := by
      refine le_trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ one_le_two (show k + m + 53 ≤ 1075 by lia))) ?_
      rw [pow_add, ← div_div]
      exact div_le_div_of_nonneg_right hv (by positivity)
    generalize (1 : ℚ) / 2 ^ 1075 = ε at hab this
    linarith

/-- A finite product of doubles `x ≥ 0` on the grid `ℤ` and `y ≥ 0` is at least
`(1 - 2 ^ (-53)) x y`: a rounding on the grid of the doubles. -/
theorem one_sub_mul_le_toRat_mul {x y : Double} (hgx : OnGrid 0 x.toRat)
    (hf : (x * y).isFinite = true) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) :
    (1 - 1 / 2 ^ 53) * (x.toRat * y.toRat) ≤ (x * y).toRat := by
  obtain ⟨hx, hy⟩ := isFinite_and_of_isFinite_mul hf
  have hd := isGridRounding_mul (k := 0) (l := 1074) hx hy hgx (onGrid_toRat _) (by norm_num) hf
  have hd' := (abs_le.mp hd.abs_sub_le).1
  rw [abs_of_nonneg (mul_nonneg hx0 hy0)] at hd'
  linarith

/-- An approximation within less than the spacing of its grid is exact. -/
theorem Approx.exact {x : Double} {v a : ℚ} {n k : ℕ} (h : x.Approx v a n k) (hv : OnGrid k v)
    (hlt : ((1 + 1 / 2 ^ 53) ^ n - 1) * a < 1 / 2 ^ k) : x.Approx v |v| 0 k :=
  .of_toRat_eq h.isFinite (h.onGrid.eq_of_abs_sub_lt hv (h.abs_sub_le.trans_lt hlt)) hv

theorem Approx.toRat_eq_of_zero {x : Double} {v a : ℚ} {k : ℕ} (h : x.Approx v a 0 k) :
    x.toRat = v := by
  have := h.abs_sub_le
  rwa [pow_zero, sub_self, zero_mul, abs_nonpos_iff, sub_eq_zero] at this

theorem Approx.onGrid_of_zero {x : Double} {v a : ℚ} {k : ℕ} (h : x.Approx v a 0 k) :
    OnGrid k v :=
  h.toRat_eq_of_zero ▸ h.onGrid

end Double

/-! ### Polynomials over a box -/

/-- The sum of `|f j k| R ^ j S ^ k` over the pairs `j + k ≤ D`: for the coefficients `f j k` of a
polynomial at a centre, a bound on its terms over the box `|s| ≤ R`, `|t| ≤ S` around it, and with
the constant term `|f 0 0|` taken off, a bound on its distance from the constant term
(`JPoints.abs_eval2_sub_le`). -/
def absSum (f : ℕ → ℕ → ℚ) (D : ℕ) (R S : ℚ) : ℚ :=
  ∑ j ∈ range (D + 1), ∑ k ∈ range (D - j + 1), |f j k| * (R ^ j * S ^ k)

theorem sum_map_tail_evalIndices_abs (f : ℕ → ℕ → ℚ) (D : ℕ) (R S : ℚ) :
    ((evalIndices D).tail.map fun jk ↦ |f jk.1 jk.2| * (R ^ jk.1 * S ^ jk.2)).sum =
      absSum f D R S - |f 0 0| := by
  rw [Double.sum_map_tail_evalIndices]
  simp [absSum]

variable {D : ℕ} {R S : ℚ}

theorem abs_le_absSum (f : ℕ → ℕ → ℚ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    |f 0 0| ≤ absSum f D R S := by
  rw [← sub_nonneg, ← sum_map_tail_evalIndices_abs]
  exact List.sum_nonneg fun x hx ↦ by
    obtain ⟨jk, -, rfl⟩ := List.mem_map.mp hx
    positivity

/-- A polynomial with the coefficients `V` at a centre differs over the box `|s| ≤ R`, `|t| ≤ S`
from its constant term by at most the sum of the absolute values of its other terms at the
corner `(R, S)`. -/
theorem abs_eval2_sub_le (V : Array ℚ) {s t : ℚ} (hs : |s| ≤ R) (ht : |t| ≤ S) :
    |eval2 V D s t - V[coeffIndex 0 0]!| ≤
      absSum (fun j k ↦ V[coeffIndex j k]!) D R S - |V[coeffIndex 0 0]!| := by
  have := (abs_nonneg s).trans hs
  have := (abs_nonneg t).trans ht
  have e : eval2 V D s t - V[coeffIndex 0 0]! = ((evalIndices D).tail.map
      fun jk ↦ V[coeffIndex jk.1 jk.2]! * s ^ jk.1 * t ^ jk.2).sum := by
    rw [Double.sum_map_tail_evalIndices, eval2]
    simp
  rw [e, ← sum_map_tail_evalIndices_abs (fun j k ↦ V[coeffIndex j k]!)]
  refine (List.le_sum_of_subadditive _ abs_zero.le abs_add_le _).trans ?_
  rw [List.map_map]
  refine List.sum_le_sum fun jk _ ↦ ?_
  simp only [Function.comp_apply, abs_mul, abs_pow, mul_assoc]
  gcongr

/-- The terms of `f` other than the constant one are bounded, over the box, by those of `g` and of
`g - f`. -/
theorem absSum_sub_abs_le (f g : ℕ → ℕ → ℚ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum f D R S - |f 0 0| ≤ absSum g D R S - |g 0 0| +
      (absSum (fun j k ↦ g j k - f j k) D R S - |g 0 0 - f 0 0|) := by
  rw [← sum_map_tail_evalIndices_abs, ← sum_map_tail_evalIndices_abs,
    ← sum_map_tail_evalIndices_abs, ← List.sum_map_add]
  refine List.sum_le_sum fun jk _ ↦ ?_
  have := abs_sub_abs_le_abs_sub (f jk.1 jk.2) (g jk.1 jk.2)
  rw [abs_sub_comm (f _ _)] at this
  nlinarith [show 0 ≤ R ^ jk.1 * S ^ jk.2 by positivity]

/-- A polynomial with the coefficients `V` over the box `|s| ≤ R`, `|t| ≤ S` lies within `Tx + E` of
the constant term of `f`, for the sum `Tx` of the other terms of `f` at the corner `(R, S)` and the
sum `E` of the differences `f - V` there. -/
theorem abs_eval2_sub_le_absSum (V : Array ℚ) (f : ℕ → ℕ → ℚ) {s t : ℚ} (hs : |s| ≤ R)
    (ht : |t| ≤ S) :
    |eval2 V D s t - f 0 0| ≤ absSum f D R S - |f 0 0| +
      absSum (fun j k ↦ f j k - V[coeffIndex j k]!) D R S := by
  have h1 := abs_eval2_sub_le V (D := D) hs ht
  have h2 := absSum_sub_abs_le (D := D) (fun j k ↦ V[coeffIndex j k]!) f
    ((abs_nonneg s).trans hs) ((abs_nonneg t).trans ht)
  have h3 := abs_sub_le (eval2 V D s t) V[coeffIndex 0 0]! (f 0 0)
  rw [abs_sub_comm V[coeffIndex 0 0]!] at h3
  linarith

theorem eval2_nonneg_of_nonneg {q : Array ℚ} (hq : ∀ i : ℕ, 0 ≤ q[i]!) (D : ℕ) {X Y : ℚ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ eval2 q D X Y :=
  sum_nonneg fun j _ ↦ sum_nonneg fun k _ ↦ by
    have := hq (coeffIndex j k)
    positivity

theorem getElem!_le_eval2_one {q : Array ℚ} (hq : ∀ i : ℕ, 0 ≤ q[i]!) {j k : ℕ}
    (hjk : j + k ≤ D) : q[coeffIndex j k]! ≤ eval2 q D 1 1 := by
  rw [eval2]
  refine le_trans ?_ (single_le_sum (fun j' _ ↦ sum_nonneg fun k' _ ↦ ?_)
    (mem_range.mpr (by lia : j < D + 1)))
  · refine le_trans ?_ (single_le_sum (fun k' _ ↦ ?_) (mem_range.mpr (by lia : k < D - j + 1)))
    · simp
    · simpa using hq _
  · simpa using hq _

theorem coeffIndex_zero_zero : coeffIndex 0 0 = 0 := by simp [coeffIndex]

namespace Double

variable {q : Array Double} {V A : Array ℚ} {n g : ℕ}

theorem ApproxCoeffs.absSum_sub_le (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum (fun j k ↦ (q[coeffIndex j k]!).toRat - V[coeffIndex j k]!) D R S ≤
      ((1 + 1 / 2 ^ 53) ^ n - 1) * eval2 A D R S := by
  rw [absSum, eval2, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  have hjk : j + k ≤ D := by simp only [mem_range] at hj hk; lia
  calc _ ≤ ((1 + 1 / 2 ^ 53) ^ n - 1) * A[coeffIndex j k]! * (R ^ j * S ^ k) :=
        mul_le_mul_of_nonneg_right (h hjk).abs_sub_le (by positivity)
    _ = _ := by ring

theorem ApproxCoeffs.absSum_le (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S ≤
      (1 + 1 / 2 ^ 53) ^ n * eval2 A D R S := by
  rw [absSum, eval2, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  have hjk : j + k ≤ D := by simp only [mem_range] at hj hk; lia
  calc _ ≤ (1 + 1 / 2 ^ 53) ^ n * A[coeffIndex j k]! * (R ^ j * S ^ k) :=
        mul_le_mul_of_nonneg_right (h hjk).abs_toRat_le (by positivity)
    _ = _ := by ring

theorem ApproxCoeffs.eval2_nonneg (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ eval2 A D R S :=
  sum_nonneg fun j hj ↦ sum_nonneg fun k hk ↦ by
    have := (h (j := j) (k := k) (by simp only [mem_range] at hj hk; lia)).nonneg
    positivity

/-! ### `poly_sign` -/

-- The arithmetic of the margin of `poly_sign`: the rounded sum `sd ≥ (1 - u) (T + e)` of the sum
-- `T ≥ (2 - ρ_N) Tx` of the terms and of the margin `e ≥ (n + N + 3 + γ) u M` exceeds the sum `Tx`
-- of the terms of the doubles and their error `E ≤ (ρ_n - 1) M` by `γ u M`, for the factors
-- `ρ_n = (1 + u) ^ n` and `ρ_N` of the roundings, `u = 2 ^ (-53)`.
private theorem le_sub_sub_of_margin {T Tx E M e sd Q ρn ρN : ℚ} {n N γ : ℕ} (hn : n ≤ 2 ^ 10)
    (hN : N ≤ 2 ^ 10) (hγ : γ ≤ 2 ^ 10) (hρn : ρn - 1 ≤ n / 2 ^ 53 * (1 + 1 / 2 ^ 32))
    (hρN : ρN - 1 ≤ N / 2 ^ 53 * (1 + 1 / 2 ^ 32)) (hM : 0 ≤ M) (hTx : 0 ≤ Tx) (hQ : 0 ≤ Q)
    (hT : (2 - ρN) * Tx ≤ T) (hE : E ≤ (ρn - 1) * M) (hq : Tx + Q ≤ ρn * M)
    (hsd : (1 - 1 / 2 ^ 53) * (T + e) ≤ sd) (hm : (n + N + 3 + γ) * M / 2 ^ 53 ≤ e) :
    γ * M / 2 ^ 53 ≤ sd - Tx - E := by
  have hn' : (n : ℚ) ≤ 2 ^ 10 := mod_cast hn
  have hN' : (N : ℚ) ≤ 2 ^ 10 := mod_cast hN
  have hγ' : (γ : ℚ) ≤ 2 ^ 10 := mod_cast hγ
  have p1 := mul_le_mul_of_nonneg_right hρN hTx
  have p2 : Tx ≤ (1 + 1 / 2 ^ 42) * M := by nlinarith
  have p3 := mul_le_mul_of_nonneg_left p2 (Nat.cast_nonneg N)
  have p4 := mul_le_mul_of_nonneg_right hρn hM
  have p7 := mul_le_mul_of_nonneg_right hN' hM
  have p8 := mul_le_mul_of_nonneg_right hn' hM
  have p9 := mul_le_mul_of_nonneg_right hγ' hM
  linarith

-- `x ≤ 2 ^ 20 · 2 ^ 1000` is below `2 ^ 1022`, without the evaluation of the powers.
private theorem lt_two_pow_1022 {x : ℚ} (h : x ≤ 2 ^ 20 * 2 ^ 1000) : x < 2 ^ 1022 :=
  h.trans_lt (by
    rw [show (1022 : ℕ) = 22 + 1000 from rfl, pow_add]
    exact mul_lt_mul_of_pos_right (by norm_num) (by positivity))

/-- What a call `poly_sign(q, D, rp, e)` of the analysis of a cell needs for its verdict to be
sound: the coefficients `q` of degree `D ≤ 4` approximate the exact coefficients `V` of a polynomial
at the centre of the cell with the majorants `A` (`JPoints.Double.ApproxCoeffs`) within `n ≤ 2 ^ 10`
roundings, on the grid `2 ^ (-g) ℤ`; the products `rp` approximate the products `R ^ j S ^ k` of
the half-sizes `R` and `S` of the cell and have no sign bits; the majorants at the corner
`(R, S)`, `M = ∑ A_{jk} R ^ j S ^ k`, are at most `2 ^ 1000`; and the margin `e`, without a sign
bit, is at most `2 ^ 1000` and at least `(n + D + |JPoints.evalIndices D| + 3 + γ) M / 2 ^ 53` when
it is finite, `γ M / 2 ^ 53` of it more than the rounding errors of `q` and of `tube_sum` need. -/
structure PolySignSetup (q : Array Double) (V A : Array ℚ) (D n g : ℕ) (rp : Array Double)
    (R S : ℚ) (e : Double) (γ : ℕ) : Prop where
  /-- The coefficients approximate the exact ones. -/
  approx : ApproxCoeffs q V A D n g
  /-- The degree is at most `4`. -/
  deg_le : D ≤ 4
  /-- The grid and the products of the degree stay within the grid of the doubles. -/
  grid_le : g + D ≤ 1074
  /-- At most `2 ^ 10` roundings. -/
  count_le : n ≤ 2 ^ 10
  /-- The excess of the margin is at most `2 ^ 10` units. -/
  gamma_le : γ ≤ 2 ^ 10
  /-- The products of the half-sizes. -/
  rp_approx {j k : ℕ} (h : j + k ≤ D) :
    (rp[coeffIndex j k]!).Approx (R ^ j * S ^ k) (R ^ j * S ^ k) (j + k) (j + k)
  /-- The products of the half-sizes have no sign bits. -/
  rp_signBit {j k : ℕ} (h : j + k ≤ D) : (rp[coeffIndex j k]!).signBit = false
  /-- The half-size in the first variable. -/
  nonneg_R : 0 ≤ R
  /-- The half-size in the second variable. -/
  nonneg_S : 0 ≤ S
  /-- The majorants at the corner are bounded. -/
  le_pow : eval2 A D R S ≤ 2 ^ 1000
  /-- The margin has no sign bit. -/
  signBit_e : e.signBit = false
  /-- The margin, when finite, covers the errors and is bounded. -/
  margin (h : e.isFinite = true) :
    ((n + D + (evalIndices D).length + 3 + γ : ℕ) : ℚ) * eval2 A D R S / 2 ^ 53 ≤ e.toRat ∧
      e.toRat ≤ 2 ^ 1000

theorem fst_polySign_eq {q rp : Array Double} {D : ℕ} {e : Double}
    (hp : (polySign q D rp e).run.1 ≠ 0) :
    (polySign q D rp e).run.1 = 1 ∨ (polySign q D rp e).run.1 = -1 := by
  rw [run_polySign] at hp ⊢
  split_ifs at hp ⊢ <;> simp_all

-- A rational `P` within less than `|Q|` of `Q` has the sign of `Q`.
private theorem sign_mul_pos {P Q : ℚ} (h : |P - Q| < |Q|) :
    0 < (if 0 < Q then 1 else -1 : ℚ) * P := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  split_ifs with hQ
  · rw [abs_of_pos hQ] at h1; linarith
  · rw [abs_of_nonpos (not_lt.mp hQ)] at h2; linarith

namespace PolySignSetup

variable {q rp : Array Double} {V A : Array ℚ} {D n g γ : ℕ} {R S : ℚ} {e : Double}
  (h : PolySignSetup q V A D n g rp R S e γ)
include h

theorem approx_tubeSumGen (hs : (tubeSumGen q D rp).isFinite = true) :
    (tubeSumGen q D rp).Approx
      (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|)
      (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|)
      (D + (evalIndices D).length) (g + D) := by
  have := Double.approx_tubeSumGen (fun _ _ hjk ↦ ⟨(h.approx hjk).isFinite, (h.approx hjk).onGrid⟩)
    (fun _ _ hjk ↦ h.rp_approx hjk) h.grid_le hs
  rwa [coeffIndex_zero_zero] at this

theorem signBit_tubeSumGen : (tubeSumGen q D rp).signBit = false := by
  refine signBit_foldl_add (by decide) fun jk hjk ↦ ?_
  have hjk' := mem_evalIndices.mp (List.mem_of_mem_tail hjk)
  rw [signBit_mul_of_isFinite (by rw [isFinite_fabs]; exact (h.approx hjk').isFinite)
    (h.rp_approx hjk').isFinite, signBit_fabs, h.rp_signBit hjk']
  rfl

theorem count_le_19 : D + (evalIndices D).length ≤ 19 := by
  have := h.deg_le; interval_cases D <;> decide

theorem approx_zero : (q[0]!).Approx V[0]! A[0]! n g := by
  have := h.approx (j := 0) (k := 0) (by lia)
  rwa [coeffIndex_zero_zero] at this

/-- The sum `tube_sum(q)`, when finite: within `D + |JPoints.evalIndices D|` roundings of the sum
`Tx` of the terms of `q` other than the constant one at the corner, which with `|q₀|` is at most
`(1 + 2 ^ (-53)) ^ n M`. -/
theorem tubeSumGen_bounds (hT : (tubeSumGen q D rp).isFinite = true) :
    (0 : ℚ) ≤ absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat| ∧
      ((2 : ℚ) - (1 + 1 / 2 ^ 53) ^ (D + (evalIndices D).length)) *
          (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) ≤
        (tubeSumGen q D rp).toRat ∧
      (tubeSumGen q D rp).toRat ≤
        (2 : ℚ) * (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) ∧
      absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S ≤
        (1 + 1 / 2 ^ 53) ^ n * eval2 A D R S := by
  have hTa := h.approx_tubeSumGen hT
  have hTx := abs_le_absSum (D := D) (fun j k ↦ (q[coeffIndex j k]!).toRat) h.nonneg_R h.nonneg_S
  rw [coeffIndex_zero_zero] at hTx
  refine ⟨sub_nonneg.mpr hTx, hTa.two_sub_pow_mul_le_toRat, ((le_abs_self _).trans
    hTa.abs_toRat_le).trans (mul_le_mul_of_nonneg_right (one_add_pow_le_two (by
      lia [h.count_le_19])) (sub_nonneg.mpr hTx)), h.approx.absSum_le h.nonneg_R h.nonneg_S⟩

/-- The sum `sd = tube_sum(q) + e` of `poly_sign`, when finite, of a finite `tube_sum(q) ≥ 0` and a
finite margin `e ≥ 0`, within a rounding of their exact sum. -/
theorem sum_bounds (hs : (tubeSumGen q D rp + e).isFinite = true) :
    (1 - 1 / 2 ^ 53) * ((tubeSumGen q D rp).toRat + e.toRat) ≤ (tubeSumGen q D rp + e).toRat ∧
      (tubeSumGen q D rp + e).toRat ≤
        (1 + 1 / 2 ^ 53) * ((tubeSumGen q D rp).toRat + e.toRat) := by
  obtain ⟨hT, he⟩ := isFinite_and_of_isFinite_add hs
  obtain ⟨hTx, hT1, -, -⟩ := h.tubeSumGen_bounds hT
  have hr := (isGridRounding_add hT he (onGrid_toRat _) (onGrid_toRat _) le_rfl hs).abs_sub_le
  have hm0 := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  have he0 : 0 ≤ e.toRat := le_trans (by positivity) (h.margin he).1
  have hT0 : 0 ≤ (tubeSumGen q D rp).toRat := by
    nlinarith [one_add_pow_le_two (n := D + (evalIndices D).length) (by lia [h.count_le_19])]
  rw [abs_of_nonneg (add_nonneg hT0 he0)] at hr
  constructor <;> linarith [abs_le.mp hr]

/-- The sum `sd = tube_sum(q) + e` of `poly_sign`, when finite, exceeds the sum `Tx` of the terms
of `q` other than the constant one over the cell and the error `E` of `q` by `γ M / 2 ^ 53`, and
is at most `8 · 2 ^ 1000`. -/
theorem sub_sub_ge (hs : (tubeSumGen q D rp + e).isFinite = true) :
    e.isFinite = true ∧ (tubeSumGen q D rp + e).toRat ≤ 8 * 2 ^ 1000 ∧
      γ * eval2 A D R S / 2 ^ 53 ≤ (tubeSumGen q D rp + e).toRat -
        (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) -
        absSum (fun j k ↦ (q[coeffIndex j k]!).toRat - V[coeffIndex j k]!) D R S := by
  obtain ⟨hT, he⟩ := isFinite_and_of_isFinite_add hs
  obtain ⟨hm, he2⟩ := h.margin he
  obtain ⟨hTx, hT1, hT2, hq⟩ := h.tubeSumGen_bounds hT
  obtain ⟨hr1, hr2⟩ := h.sum_bounds hs
  have hm0 := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  push_cast at hm
  have t2 := hq.trans (mul_le_mul (one_add_pow_le_two (by lia [h.count_le])) h.le_pow hm0
    (by norm_num))
  have hq0 := abs_nonneg (q[0]!).toRat
  refine ⟨he, by generalize (2 : ℚ) ^ 1000 = B at t2 he2; linarith,
    le_sub_sub_of_margin (T := (tubeSumGen q D rp).toRat) (e := e.toRat) (Q := |(q[0]!).toRat|)
    h.count_le (h.count_le_19.trans (by norm_num)) h.gamma_le
    (one_add_pow_sub_one_le (n := n) (by lia [h.count_le]))
    (one_add_pow_sub_one_le (n := D + (evalIndices D).length) (by lia [h.count_le_19])) hm0 hTx
    hq0 hT1 (h.approx.absSum_sub_le h.nonneg_R h.nonneg_S) (by linarith) hr1
    (by push_cast; linarith)⟩

/-- The bound `lo = |q₀| - sd` of `poly_sign` for a finite sum `sd`: finite, and within a rounding
of `|q₀| - sd`. -/
theorem lo_rounding (hsd : (tubeSumGen q D rp + e).isFinite = true) :
    (q[0]!.fabs - (tubeSumGen q D rp + e)).isFinite = true ∧
      |(q[0]!.fabs - (tubeSumGen q D rp + e)).toRat -
          (|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat)| ≤
        |(|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat)| / 2 ^ 53 := by
  obtain ⟨-, hb, -⟩ := h.sub_sub_ge hsd
  obtain ⟨-, -, -, hq⟩ := h.tubeSumGen_bounds (isFinite_and_of_isFinite_add hsd).1
  have hA := hq.trans (mul_le_mul (one_add_pow_le_two (by lia [h.count_le])) h.le_pow
    (h.approx.eval2_nonneg h.nonneg_R h.nonneg_S) (by norm_num))
  have hT := abs_le_absSum (D := D) (fun j k ↦ (q[coeffIndex j k]!).toRat) h.nonneg_R h.nonneg_S
  rw [coeffIndex_zero_zero] at hT
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hf0 : (q[0]!.fabs).isFinite = true := by rw [isFinite_fabs]; exact h.approx_zero.isFinite
  have hlf := (isRounding_sub hf0 hsd).isFinite_of_abs_lt (lt_two_pow_1022 ((abs_sub _ _).trans
    (by rw [toRat_fabs, abs_abs, abs_of_nonneg hs0]; generalize (2 : ℚ) ^ 1000 = B at hA hb
        linarith)))
  have hr := (isGridRounding_sub hf0 hsd (onGrid_toRat _) (onGrid_toRat _) le_rfl hlf).abs_sub_le
  rw [toRat_fabs] at hr
  exact ⟨hlf, hr⟩

/-- The doubles of `poly_sign` that a positive bound `lo = |q₀| - sd` needs: the sum `sd` finite and
below `|q₀|`, `lo` at most `(1 + 2 ^ (-53)) (|q₀| - sd)`, and `lo` finite. -/
theorem lo_facts (hlo : (0.0 : Double).lt (q[0]!.fabs - (tubeSumGen q D rp + e)) = true) :
    (tubeSumGen q D rp + e).isFinite = true ∧ (tubeSumGen q D rp + e).toRat < |(q[0]!).toRat| ∧
      (q[0]!.fabs - (tubeSumGen q D rp + e)).toRat ≤
        (1 + 1 / 2 ^ 53) * (|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat) ∧
      (q[0]!.fabs - (tubeSumGen q D rp + e)).isFinite = true := by
  have hsd := isFinite_of_lt_sub (by rw [isFinite_fabs]; exact h.approx_zero.isFinite)
    (signBit_add h.signBit_tubeSumGen h.signBit_e) hlo
  obtain ⟨hlf, hr⟩ := h.lo_rounding hsd
  rw [zero_lt_iff_toRat_pos hlf] at hlo
  obtain ⟨-, hr2⟩ := abs_le.mp hr
  have hv : (tubeSumGen q D rp + e).toRat < |(q[0]!).toRat| := by
    by_contra! hv
    rw [abs_of_nonpos (sub_nonpos.mpr hv)] at hr2
    linarith
  refine ⟨hsd, hv, ?_, hlf⟩
  rw [abs_of_pos (sub_pos.mpr hv)] at hr2
  linarith

/-- A nonzero sign of `poly_sign` is the sign throughout the cell of the polynomial with the exact
coefficients `V`, and the margin is then finite. -/
theorem mul_pos_eval2 (hp : (polySign q D rp e).run.1 ≠ 0) :
    e.isFinite = true ∧ ∀ ⦃s t : ℚ⦄, |s| ≤ R → |t| ≤ S →
      0 < ((polySign q D rp e).run.1 : ℚ) * eval2 V D s t := by
  have hM := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  rw [run_polySign] at hp ⊢
  split_ifs at hp ⊢ with hlo hq
  all_goals try exact absurd rfl hp
  all_goals
    obtain ⟨hsd, hv, -, -⟩ := h.lo_facts hlo
    obtain ⟨he, -, hk⟩ := h.sub_sub_ge hsd
    refine ⟨he, fun s t hs ht ↦ ?_⟩
    have := abs_eval2_sub_le_absSum V (fun j k ↦ (q[coeffIndex j k]!).toRat) (D := D) hs ht
    rw [coeffIndex_zero_zero] at this
    have hγ : 0 ≤ (γ : ℚ) * eval2 A D R S / 2 ^ 53 := by positivity
    have hsign := sign_mul_pos (P := eval2 V D s t) (Q := (q[0]!).toRat) (by linarith)
  · change (0.0 : Double).lt q[0]! = true at hq
    rw [ite_eq_left ((zero_lt_iff_toRat_pos h.approx_zero.isFinite).mp hq)] at hsign
    exact_mod_cast hsign
  · change ¬(0.0 : Double).lt q[0]! = true at hq
    rw [ite_eq_right ((zero_lt_iff_toRat_pos h.approx_zero.isFinite).not.mp hq)] at hsign
    exact_mod_cast hsign

/-- The upper bound `hi` of `poly_sign`, when finite, bounds the polynomial with the exact
coefficients `V` throughout the cell, up to a rounding. -/
theorem abs_eval2_le (hf : (polySign q D rp e).run.2.2.isFinite = true) ⦃s t : ℚ⦄ (hs : |s| ≤ R)
    (ht : |t| ≤ S) :
    (1 - 1 / 2 ^ 53) * |eval2 V D s t| ≤ (polySign q D rp e).run.2.2.toRat := by
  rw [run_polySign] at hf ⊢
  dsimp only at hf ⊢
  obtain ⟨hf0, hsd⟩ := isFinite_and_of_isFinite_add hf
  obtain ⟨-, -, hk⟩ := h.sub_sub_ge hsd
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hr := (isGridRounding_add hf0 hsd (onGrid_toRat _) (onGrid_toRat _) le_rfl hf).abs_sub_le
  rw [toRat_fabs, abs_of_nonneg (add_nonneg (abs_nonneg _) hs0)] at hr
  have := abs_eval2_sub_le_absSum V (fun j k ↦ (q[coeffIndex j k]!).toRat) (D := D) hs ht
  rw [coeffIndex_zero_zero] at this
  have hγ : 0 ≤ (γ : ℚ) * eval2 A D R S / 2 ^ 53 := by
    have := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
    positivity
  have h1 := abs_sub_abs_le_abs_sub (eval2 V D s t) (q[0]!).toRat
  linarith [(abs_le.mp hr).1]

theorem signBit_hi : (polySign q D rp e).run.2.2.signBit = false := by
  rw [run_polySign]
  exact signBit_add (signBit_fabs _) (signBit_add h.signBit_tubeSumGen h.signBit_e)

theorem isFinite_lo (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) :
    (polySign q D rp e).run.2.1.isFinite = true := by
  rw [run_polySign] at hlo ⊢
  exact (h.lo_facts hlo).2.2.2

theorem lo_le_two_mul (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) :
    (polySign q D rp e).run.2.1.toRat ≤ 2 * eval2 A D R S := by
  rw [run_polySign] at hlo ⊢
  dsimp only at hlo ⊢
  obtain ⟨hsd, -, hlo', -⟩ := h.lo_facts hlo
  obtain ⟨-, -, -, hA⟩ := h.tubeSumGen_bounds (isFinite_and_of_isFinite_add hsd).1
  have hT := abs_le_absSum (D := D) (fun j k ↦ (q[coeffIndex j k]!).toRat) h.nonneg_R h.nonneg_S
  rw [coeffIndex_zero_zero] at hT
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hρ := one_add_pow_sub_one_le (n := n) (by lia [h.count_le])
  have hn : (n : ℚ) ≤ 2 ^ 10 := mod_cast h.count_le
  have hρM := mul_le_mul_of_nonneg_right (show (1 + 1 / 2 ^ 53 : ℚ) ^ n ≤ 1 + 1 / 2 ^ 42 by
    nlinarith) (h.approx.eval2_nonneg h.nonneg_R h.nonneg_S)
  nlinarith

/-- A positive lower bound `lo` of `poly_sign` bounds the polynomial with the exact coefficients
`V` from below throughout the cell, up to a rounding and with `γ M / 2 ^ 53` to spare. -/
theorem lo_le_abs_eval2 (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) ⦃s t : ℚ⦄
    (hs : |s| ≤ R) (ht : |t| ≤ S) :
    (polySign q D rp e).run.2.1.toRat ≤
      (1 + 1 / 2 ^ 53) * (|eval2 V D s t| - γ * eval2 A D R S / 2 ^ 53) := by
  rw [run_polySign] at hlo ⊢
  dsimp only at hlo ⊢
  obtain ⟨hsd, hv, hlo', -⟩ := h.lo_facts hlo
  obtain ⟨-, -, hk⟩ := h.sub_sub_ge hsd
  have := abs_eval2_sub_le_absSum V (fun j k ↦ (q[coeffIndex j k]!).toRat) (D := D) hs ht
  rw [coeffIndex_zero_zero] at this
  have h1 := abs_sub_abs_le_abs_sub (q[0]!).toRat (eval2 V D s t)
  rw [abs_sub_comm (q[0]!).toRat] at h1
  exact hlo'.trans (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))

end PolySignSetup

end Double

end JPoints

end
