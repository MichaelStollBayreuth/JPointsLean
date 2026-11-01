/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A step of Horner's rule

A candidate for `Mathlib.Algebra.BigOperators.Ring.Finset`, next to `Finset.sum_mul`: the step
`s ↦ s x + f (n + 1)` of Horner's rule takes `∑ i ≤ n, f i xⁿ⁻ⁱ` to `∑ i ≤ n + 1, f i xⁿ⁺¹⁻ⁱ`.

## Main statements

* `Finset.sum_range_mul_pow_sub_mul_add`: a step of Horner's rule.

## Implementation notes

The sums run over `Finset.range (n + 1)`, the indices `i ≤ n`, so that the exponents `n - i` are
those of the natural numbers without truncation.
-/

@[expose] public section

namespace Finset

theorem sum_range_mul_pow_sub_mul_add {R : Type*} [Semiring R] (f : ℕ → R) (x : R) (n : ℕ) :
    (∑ i ∈ range (n + 1), f i * x ^ (n - i)) * x + f (n + 1) =
      ∑ i ∈ range (n + 2), f i * x ^ (n + 1 - i) := by
  rw [sum_range_succ _ (n + 1), sum_mul, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mul_assoc, ← pow_succ, Nat.sub_add_comm (Nat.lt_succ_iff.mp (mem_range.mp hi))]

end Finset

end
