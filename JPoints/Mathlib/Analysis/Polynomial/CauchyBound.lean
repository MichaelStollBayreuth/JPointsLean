/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Cauchy's bound for a bound of the coefficients

Candidates for `Mathlib.Analysis.Polynomial.CauchyBound`: when every coefficient of a polynomial
over a normed division ring below its degree is at most `C` times its leading coefficient in norm,
Cauchy's bound `Polynomial.cauchyBound` is at most `C + 1` (`Polynomial.cauchyBound_le_add_one`),
so that the roots of a nonzero real polynomial with such a bound `C ≥ 0` lie in `(-(C + 1), C + 1)`
(`Polynomial.abs_lt_add_one_of_isRoot`).

## Main statements

* `Polynomial.cauchyBound_le_add_one`: Cauchy's bound from a bound of the coefficients.
* `Polynomial.abs_lt_add_one_of_isRoot`: the bound of the real roots.
-/

@[expose] public section

namespace Polynomial

open NNReal

theorem cauchyBound_le_add_one {K : Type*} [NormedDivisionRing K] {p : K[X]} {C : ℝ≥0}
    (h : ∀ k < p.natDegree, ‖p.coeff k‖₊ ≤ ‖p.leadingCoeff‖₊ * C) : cauchyBound p ≤ C + 1 := by
  rw [cauchyBound]
  refine (add_le_add_iff_right 1).mpr
    (div_le_of_le_mul₀ zero_le zero_le (Finset.sup_le fun k hk ↦ ?_))
  rw [mul_comm]
  exact h k (Finset.mem_range.mp hk)

/-- Cauchy's bound in the form `|fₖ| ≤ |f_d| C` for `k < d`: a real root has an absolute value
below `C + 1` (`Polynomial.IsRoot.norm_lt_cauchyBound`). -/
theorem abs_lt_add_one_of_isRoot {F : ℝ[X]} (hF : F ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k < F.natDegree, |F.coeff k| ≤ |F.leadingCoeff| * C) {a : ℝ} (ha : F.IsRoot a) :
    |a| < C + 1 := by
  have h2 : cauchyBound F ≤ C.toNNReal + 1 := cauchyBound_le_add_one fun k hk ↦ by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.coe_toNNReal C hC]
    exact h k hk
  have h3 : (‖a‖₊ : ℝ) < ((C.toNNReal + 1 : NNReal) : ℝ) :=
    mod_cast (ha.norm_lt_cauchyBound hF).trans_le h2
  rwa [NNReal.coe_add, Real.coe_toNNReal C hC, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
    at h3

end Polynomial

end
