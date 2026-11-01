/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Basic.Real.Basic

/-!
# Cauchy's bound for a bound of the coefficients

A candidate for `Mathlib.Analysis.Polynomial.CauchyBound`: when every coefficient of a nonzero real
polynomial below its degree is at most `C ≥ 0` times its leading coefficient in absolute value, its
roots lie in `(-(C + 1), C + 1)` (`Polynomial.abs_lt_add_one_of_isRoot`), as Cauchy's bound
`Polynomial.cauchyBound` is at most `C + 1`.

## Main statements

* `Polynomial.abs_lt_add_one_of_isRoot`: Cauchy's bound from a bound of the coefficients.
-/

@[expose] public section

namespace Polynomial

/-- Cauchy's bound in the form `|fₖ| ≤ |f_d| C` for `k < d`: a real root has an absolute value
below `C + 1` (`Polynomial.IsRoot.norm_lt_cauchyBound`). -/
theorem abs_lt_add_one_of_isRoot {F : ℝ[X]} (hF : F ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k < F.natDegree, |F.coeff k| ≤ |F.leadingCoeff| * C) {a : ℝ} (ha : F.IsRoot a) :
    |a| < C + 1 := by
  have h1 := ha.norm_lt_cauchyBound hF
  have hlc : 0 < ‖F.leadingCoeff‖₊ := by simpa using hF
  have h2 : cauchyBound F ≤ C.toNNReal + 1 := by
    rw [cauchyBound]
    refine (add_le_add_iff_right 1).mpr ((div_le_iff₀ hlc).mpr (Finset.sup_le fun k hk ↦ ?_))
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.coe_toNNReal C hC, mul_comm]
    exact h k (Finset.mem_range.mp hk)
  have h3 : (‖a‖₊ : ℝ) < ((C.toNNReal + 1 : NNReal) : ℝ) := mod_cast h1.trans_le h2
  rwa [NNReal.coe_add, Real.coe_toNNReal C hC, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
    at h3

end Polynomial

end
