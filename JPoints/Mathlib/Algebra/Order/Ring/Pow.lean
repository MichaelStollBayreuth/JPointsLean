/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Ring.Pow

import Mathlib.Tactic.Ring

/-!
# An upper bound for the powers of `1 + a`

A candidate for `Mathlib.Algebra.Order.Ring.Pow`, next to Bernoulli's inequality
`one_add_mul_le_pow`: for `a ≥ 0`, `(1 + a) ^ n (1 - n a) ≤ 1`, so that `(1 + a) ^ n` is at most
`1 / (1 - n a)` when `n a < 1`, the bound on the factor of `n` relative errors `a` that the error
analysis of floating-point computations uses.

## Main statements

* `one_add_pow_mul_one_sub_mul_le_one`: `(1 + a) ^ n (1 - n a) ≤ 1` for `a ≥ 0`.
-/

@[expose] public section

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- `(1 + a) ^ n (1 - n a) ≤ 1` for `a ≥ 0`: each factor `1 + a` raises the product
`(1 + a) ^ n (1 - n a)` by less than the factor `1 - a` takes away. Compare Bernoulli's
inequality `one_add_mul_le_pow`. -/
theorem one_add_pow_mul_one_sub_mul_le_one {a : R} (ha : 0 ≤ a) (n : ℕ) :
    (1 + a) ^ n * (1 - n * a) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (1 + a) ^ (n + 1) * (1 - (n + 1 : ℕ) * a) =
        (1 + a) ^ n * (1 - n * a) - (1 + a) ^ n * ((n + 1 : ℕ) * (a * a)) := by
      push_cast; ring
    rw [h]
    refine (sub_le_self _ ?_).trans ih
    exact mul_nonneg (pow_nonneg (add_nonneg zero_le_one ha) n)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha ha))

end
