/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.List.DropRight

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.List.GetD

/-!
# The polynomial of a list of coefficients

The degree of a list of coefficients (`JPoints.degree`) and its polynomial over `ℚ`
(`JPoints.poly`) in the terms of the list: the degree is the length of the list without its
trailing zeros, less one (`JPoints.degree_eq_length_rdropWhile_sub_one`), at most the length less
one; the coefficient at a positive degree is not zero, and those beyond it are; the coefficients of
the polynomial are the entries of the list, its degree that of the list, under every map of `ℚ`
too, and its values, over any algebra over `ℚ`, and those of its derivative are sums over any range
that covers the list.

## Main statements

* `JPoints.degree_le_length_sub_one`, `JPoints.degree_toList_le_six`: bounds of the degree.
* `JPoints.getD_degree_ne_zero`, `JPoints.getD_eq_zero_of_degree_lt`: the coefficients at and
  beyond the degree.
* `JPoints.degree_eq_of_getD_ne_zero`, `JPoints.degree_eq_of_getD_eq_zero_iff`: the degree from
  the coefficients.
* `JPoints.coeff_poly`, `JPoints.natDegree_poly`, `JPoints.leadingCoeff_poly`,
  `JPoints.natDegree_map_poly`: the coefficients and the degree of the polynomial, also over a
  larger ring.
* `JPoints.eval_map_poly`, `JPoints.eval_poly`, `JPoints.eval_derivative_poly`: the values of the
  polynomial, over any algebra over `ℚ` and over `ℚ`, and of its derivative.
-/

@[expose] public section

namespace JPoints

open Polynomial

/-! ### The degree of a list of coefficients -/

theorem degree_le_length_sub_one (cs : List ℤ) : degree cs ≤ cs.length - 1 :=
  Nat.sub_le_sub_right (by simpa using (cs.reverse.dropWhile_sublist (· == 0)).length_le) 1

theorem degree_toList_le_six {cs : Array ℤ} (h : cs.size = 7) : degree cs.toList ≤ 6 := by
  simpa [h] using degree_le_length_sub_one cs.toList

theorem degree_eq_length_rdropWhile_sub_one (cs : List ℤ) :
    degree cs = (cs.rdropWhile (· == 0)).length - 1 := by
  simp [degree, List.rdropWhile]

theorem getD_degree_ne_zero {cs : List ℤ} (h : 0 < degree cs) : cs.getD (degree cs) 0 ≠ 0 := by
  have hc := List.rdropWhile_append_rtakeWhile (p := (· == (0 : ℤ))) (l := cs)
  have hlen := degree_eq_length_rdropWhile_sub_one cs
  have hne : cs.rdropWhile (· == 0) ≠ [] := fun h' ↦ by simp [h'] at hlen; lia
  rw [← hc, List.getD_append _ _ _ _ (by lia), List.getD_eq_getElem _ _ (by lia)]
  simpa [List.getLast_eq_getElem, hlen] using List.rdropWhile_last_not _ _ hne

theorem getD_eq_zero_of_degree_lt {cs : List ℤ} {i : ℕ} (h : degree cs < i) :
    cs.getD i 0 = 0 := by
  have hc := List.rdropWhile_append_rtakeWhile (p := (· == (0 : ℤ))) (l := cs)
  have hlen := degree_eq_length_rdropWhile_sub_one cs
  rw [← hc, List.getD_append_right _ _ _ _ (by lia)]
  rcases lt_or_ge (i - (cs.rdropWhile (· == 0)).length) (cs.rtakeWhile (· == 0)).length with
    hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    simpa using List.mem_rtakeWhile_imp (List.getElem_mem hi)
  · exact List.getD_eq_default _ _ hi

theorem degree_eq_of_getD_eq_zero_iff {cs cs' : List ℤ}
    (h : ∀ i, cs.getD i 0 = 0 ↔ cs'.getD i 0 = 0) : degree cs = degree cs' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact getD_degree_ne_zero (cs := cs') (by lia) ((h _).mp (getD_eq_zero_of_degree_lt hlt))
  · exact getD_degree_ne_zero (cs := cs) (by lia) ((h _).mpr (getD_eq_zero_of_degree_lt hlt))

theorem degree_eq_of_getD_ne_zero {cs : List ℤ} {n : ℕ} (h : cs.getD n 0 ≠ 0)
    (h' : ∀ i > n, cs.getD i 0 = 0) : degree cs = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h (getD_eq_zero_of_degree_lt hlt)
  · exact getD_degree_ne_zero (by lia) (h' _ hlt)

/-! ### The polynomial -/

theorem coeff_poly (cs : List ℤ) (i : ℕ) : (poly cs).coeff i = cs.getD i 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by lia), Int.cast_zero]

theorem natDegree_poly (cs : List ℤ) : (poly cs).natDegree = degree cs := by
  rcases Nat.eq_zero_or_pos (degree cs) with h | h
  · rw [h, natDegree_eq_zero_iff_degree_le_zero, degree_le_iff_coeff_zero]
    intro i hi
    rw [coeff_poly, getD_eq_zero_of_degree_lt (by rw [h]; exact_mod_cast hi), Int.cast_zero]
  · refine natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) ?_
    · rw [coeff_poly, getD_eq_zero_of_degree_lt (mod_cast hi), Int.cast_zero]
    · rw [coeff_poly]
      exact_mod_cast getD_degree_ne_zero h

theorem leadingCoeff_poly (cs : List ℤ) : (poly cs).leadingCoeff = cs.getD (degree cs) 0 := by
  rw [leadingCoeff, natDegree_poly, coeff_poly]

theorem natDegree_map_poly {K : Type*} [Semiring K] [Nontrivial K] (f : ℚ →+* K) (cs : List ℤ) :
    ((poly cs).map f).natDegree = degree cs := by
  rw [natDegree_map, natDegree_poly]

/-- The value of the polynomial of the coefficients `cs` over any algebra over `ℚ`, as the sum of
its terms up to any bound `n` of their number. -/
theorem eval_map_poly {K : Type*} [CommRing K] [Algebra ℚ K] {cs : List ℤ} {n : ℕ}
    (h : cs.length ≤ n) (x : K) :
    ((poly cs).map (algebraMap ℚ K)).eval x = ∑ i ∈ Finset.range n, (cs.getD i 0 : K) * x ^ i := by
  rw [poly, Polynomial.map_sum, eval_finsetSum,
    Finset.sum_subset (Finset.range_subset_range.mpr h)]
  · simp
  · intro i _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]
    simp

theorem eval_poly {cs : List ℤ} {n : ℕ} (h : cs.length ≤ n) (x : ℚ) :
    (poly cs).eval x = ∑ i ∈ Finset.range n, (cs.getD i 0 : ℚ) * x ^ i := by
  simpa using eval_map_poly (K := ℚ) h x

theorem eval_derivative_poly {cs : List ℤ} {n : ℕ} (h : cs.length ≤ n) (x : ℚ) :
    (derivative (poly cs)).eval x = ∑ i ∈ Finset.range n, (cs.getD i 0 : ℚ) * i * x ^ (i - 1) := by
  rw [poly, derivative_sum, eval_finsetSum, Finset.sum_subset (Finset.range_subset_range.mpr h)]
  · simp [derivative_X_pow, mul_assoc]
  · intro i _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]
    simp

end JPoints

end
