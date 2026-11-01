/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A quadratic without roots in an interval

A candidate for `Mathlib.Algebra.QuadraticDiscriminant`: a quadratic `a x² + b x + c` over an
ordered field that is positive at `W` and at `-W` is positive on `[-W, W]` when it is concave
there (`a ≤ 0`) or monotone there (`2 W |a| < |b|`, so that its derivative `2 a x + b` keeps the
sign of `b`); so a quadratic whose values at `±W` have the same strict sign has no root in
`[-W, W]` under either condition on that sign. The test is the one by which the analysis of the
tube of `j-points` drops a cell.

## Main statements

* `quadratic_pos_of_nonpos_of_abs_le`, `quadratic_pos_of_two_mul_abs_lt_of_abs_le`: the concave
  and the monotone case.
* `quadratic_pos_of_abs_le`: positivity on `[-W, W]`.
* `quadratic_ne_zero_of_abs_le`: no root in `[-W, W]`.
-/

@[expose] public section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c W x : K}

/-- A concave quadratic, `a ≤ 0`, that is positive at `W` and at `-W` is positive on `[-W, W]`:
`2 W Q(x) = (W + x) Q(W) + (W - x) Q(-W) - 2 a W (W² - x²)`. -/
theorem quadratic_pos_of_nonpos_of_abs_le (ha : a ≤ 0) (h₁ : 0 < a * (W * W) + b * W + c)
    (h₂ : 0 < a * (W * W) - b * W + c) (hx : |x| ≤ W) : 0 < a * (x * x) + b * x + c := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  rcases (show (0 : K) ≤ W by linarith).eq_or_lt with hW | hW
  · obtain rfl : x = 0 := by linarith
    simpa [← hW] using h₁
  refine pos_of_mul_pos_right (a := 2 * W) ?_ (by linarith)
  have key : 2 * W * (a * (x * x) + b * x + c) = (W + x) * (a * (W * W) + b * W + c) +
      (W - x) * (a * (W * W) - b * W + c) + 2 * (-a * ((W - x) * (W + x)) * W) := by ring
  have hc : 0 ≤ -a * ((W - x) * (W + x)) * W :=
    mul_nonneg (mul_nonneg (neg_nonneg.mpr ha) (mul_nonneg (by linarith) (by linarith)))
      hW.le
  rw [key]
  rcases le_total 0 x with h0 | h0
  · nlinarith [mul_pos (by linarith : (0 : K) < W + x) h₁,
      mul_nonneg (by linarith : (0 : K) ≤ W - x) h₂.le]
  · nlinarith [mul_nonneg (by linarith : (0 : K) ≤ W + x) h₁.le,
      mul_pos (by linarith : (0 : K) < W - x) h₂]

/-- A quadratic that is monotone on `[-W, W]`, `2 W |a| < |b|`, and positive at `W` and at `-W`
is positive on `[-W, W]`: `Q(x) - Q(-W) = (x + W) (a (x - W) + b)` and
`Q(W) - Q(x) = (W - x) (a (W + x) + b)`, whose second factors have the sign of `b`. -/
theorem quadratic_pos_of_two_mul_abs_lt_of_abs_le (hab : 2 * W * |a| < |b|)
    (h₁ : 0 < a * (W * W) + b * W + c) (h₂ : 0 < a * (W * W) - b * W + c) (hx : |x| ≤ W) :
    0 < a * (x * x) + b * x + c := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  have e1 : |a * (x - W)| ≤ 2 * W * |a| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg a)
  have e2 : |a * (W + x)| ≤ 2 * W * |a| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg a)
  rcases le_or_gt 0 b with hb0 | hb0
  · rw [abs_of_nonneg hb0] at hab
    have : 0 ≤ a * (x - W) + b := by linarith [neg_abs_le (a * (x - W))]
    nlinarith [mul_nonneg (by linarith : (0 : K) ≤ x + W) this]
  · rw [abs_of_neg hb0] at hab
    have : a * (W + x) + b ≤ 0 := by linarith [le_abs_self (a * (W + x))]
    nlinarith [mul_nonneg (by linarith : (0 : K) ≤ W - x) (neg_nonneg.mpr this)]

theorem quadratic_pos_of_abs_le (h : a ≤ 0 ∨ 2 * W * |a| < |b|)
    (h₁ : 0 < a * (W * W) + b * W + c) (h₂ : 0 < a * (W * W) - b * W + c) (hx : |x| ≤ W) :
    0 < a * (x * x) + b * x + c :=
  h.elim (quadratic_pos_of_nonpos_of_abs_le · h₁ h₂ hx)
    (quadratic_pos_of_two_mul_abs_lt_of_abs_le · h₁ h₂ hx)

/-- A quadratic whose values at `W` and at `-W` have the same strict sign, given by a scalar `σ`
for which `σ Q(W)` and `σ Q(-W)` are both positive, has no root in `[-W, W]` when `σ a ≤ 0`
(concave towards the axis) or `2 W |a| < |b|` (monotone there). -/
theorem quadratic_ne_zero_of_abs_le {σ : K} (h₁ : 0 < σ * (a * (W * W) + b * W + c))
    (h₂ : 0 < σ * (a * (W * W) - b * W + c)) (h : σ * a ≤ 0 ∨ 2 * W * |a| < |b|) (hx : |x| ≤ W) :
    a * (x * x) + b * x + c ≠ 0 := by
  have hσ : 0 < |σ| := abs_pos.mpr (left_ne_zero_of_mul h₁.ne')
  have h' : σ * a ≤ 0 ∨ 2 * W * |σ * a| < |σ * b| := by
    refine h.imp_right fun h ↦ ?_
    rw [abs_mul, abs_mul, mul_left_comm]
    exact mul_lt_mul_of_pos_left h hσ
  have := quadratic_pos_of_abs_le (c := σ * c) (x := x) h' (by linear_combination h₁)
    (by linear_combination h₂) hx
  intro h0
  have e : σ * a * (x * x) + σ * b * x + σ * c = σ * (a * (x * x) + b * x + c) := by ring
  rw [e, h0, mul_zero] at this
  exact lt_irrefl _ this
