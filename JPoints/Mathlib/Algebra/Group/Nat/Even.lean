/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Nat.Even

import JPoints.Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Sqrt

/-!
# The squares among the natural numbers up to a bound

Candidates for `Mathlib.Algebra.Group.Nat.Even`, next to the decidability of `IsSquare` on `ℕ`:
the squares among `0, …, n` are the `k * k` for `k ≤ ⌊√n⌋`, in increasing order, so that a
`List.flatMap` over `0, …, n` of a function that vanishes off the squares is one over the
`k ≤ ⌊√n⌋` of its values at `k * k`.

## Main statements

* `Nat.filter_isSquare_range_succ`: the squares up to `n`.
* `Nat.flatMap_range_sqrt_succ_mul_self`: a `List.flatMap` over the squares up to `n`.

## Implementation notes

The two lists of the squares are compared as strictly increasing lists with the same members
(`List.Pairwise.eq_of_mem_iff`): `k * k` grows with `k` (`Nat.mul_self_lt_mul_self`), and
`k * k ≤ n` exactly for `k ≤ ⌊√n⌋` (`Nat.le_sqrt`). The `List.flatMap` then drops the non-squares
by `List.flatMap_filter_of_ne`, a candidate for `Mathlib.Data.List.Basic` of this project.
-/

@[expose] public section

namespace Nat

theorem filter_isSquare_range_succ (n : ℕ) :
    (List.range (n + 1)).filter (fun a ↦ decide (IsSquare a)) =
      (List.range (n.sqrt + 1)).map fun k ↦ k * k := by
  refine (List.pairwise_lt_range.filter _).eq_of_mem_iff
    (List.pairwise_map.mpr <| List.pairwise_lt_range.imp Nat.mul_self_lt_mul_self) fun a ↦ ?_
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map, Nat.lt_succ_iff,
    Nat.le_sqrt]
  exact ⟨fun ⟨ha, r, hr⟩ ↦ ⟨r, by lia, hr.symm⟩, fun ⟨k, hk, hka⟩ ↦ ⟨by lia, k, hka.symm⟩⟩

/-- A `List.flatMap` over `0, …, n` of a function `f` that vanishes off the squares is one over the
`k ≤ ⌊√n⌋` of the values `f (k * k)`. -/
theorem flatMap_range_sqrt_succ_mul_self {β : Type*} {n : ℕ} {f : ℕ → List β}
    (hf : ∀ a ≤ n, f a ≠ [] → IsSquare a) :
    (List.range (n.sqrt + 1)).flatMap (fun k ↦ f (k * k)) = (List.range (n + 1)).flatMap f := by
  rw [← List.flatMap_filter_of_ne (p := fun a ↦ decide (IsSquare a)) fun a ha h ↦
    decide_eq_true (hf a (Nat.lt_succ_iff.mp (List.mem_range.mp ha)) h),
    filter_isSquare_range_succ, List.flatMap_map]

end Nat

end
