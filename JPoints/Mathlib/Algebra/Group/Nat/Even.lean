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
the squares among `0, …, n` are the `k * k` for `k ≤ ⌊√n⌋`, and those among `1, …, n` the `k * k`
for `1 ≤ k ≤ ⌊√n⌋`, in increasing order, so that a `List.flatMap` over `0, …, n` or over
`1, …, n` of a function that vanishes off the squares is one over these `k` of its values at
`k * k`.

## Main statements

* `Nat.filter_isSquare_range_succ`, `Nat.filter_isSquare_range'`: the squares up to `n`.
* `Nat.flatMap_range_sqrt_succ_mul_self`, `Nat.flatMap_range'_sqrt_mul_self`: a `List.flatMap`
  over the squares up to `n`.

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

theorem filter_isSquare_range' (n : ℕ) :
    (List.range' 1 n).filter (fun a ↦ decide (IsSquare a)) =
      (List.range' 1 n.sqrt).map fun k ↦ k * k := by
  refine ((List.pairwise_lt_range' 1).filter _).eq_of_mem_iff
    (List.pairwise_map.mpr <| (List.pairwise_lt_range' 1).imp Nat.mul_self_lt_mul_self) fun a ↦ ?_
  simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq, List.mem_map]
  refine ⟨fun ⟨⟨h1, h2⟩, k, hk⟩ ↦ ⟨k, ⟨?_, ?_⟩, hk.symm⟩,
    fun ⟨k, ⟨h1, h2⟩, hk⟩ ↦ ⟨⟨?_, ?_⟩, k, hk.symm⟩⟩
  · rcases k with _ | k <;> simp_all
  · lia [Nat.le_sqrt.mpr (show k * k ≤ n by lia)]
  · lia [Nat.mul_le_mul h1 h1]
  · lia [Nat.le_sqrt.mp (show k ≤ n.sqrt by lia)]

/-- A `List.flatMap` over `1, …, n` of a function that vanishes off the squares is one over the
`1 ≤ k ≤ ⌊√n⌋` of the values `f (k * k)`. -/
theorem flatMap_range'_sqrt_mul_self {β : Type*} {n : ℕ} {f : ℕ → List β}
    (hf : ∀ a ≥ 1, a ≤ n → f a ≠ [] → IsSquare a) :
    (List.range' 1 n.sqrt).flatMap (fun k ↦ f (k * k)) = (List.range' 1 n).flatMap f := by
  rw [← List.flatMap_filter_of_ne (p := fun a ↦ decide (IsSquare a)) fun a ha h ↦
    decide_eq_true (hf a (List.mem_range'_1.mp ha).1 (by lia [(List.mem_range'_1.mp ha).2]) h),
    filter_isSquare_range', List.flatMap_map]

end Nat

end
