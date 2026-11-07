/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Tube
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Defs

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Taylor shifts of the analysis of the tube

`shift1` of `j-points` shifts a polynomial in one variable, whose coefficients lie in an array at
the indices `base + j s`, to a point `x` by repeated synthetic division: for each `i < deg`, the
coefficients `deg - 1` down to `i` raised by `x` times the next. `shift2` shifts a polynomial in two
variables, its coefficients at the indices `P(j, k)`, to `(bm, cm)`: each column in `b`, then each
row in `c`. This file models both as folds over the pairs of indices of their steps, for any type of
coefficients (`JPoints.shift1Gen`, `JPoints.shift2Gen`), so that one fold describes the doubles of
the model, the exact shift over `ℚ` and the shift of the absolute values, the majorant of the
errors; and it proves that over a commutative ring the shifts are Taylor shifts: the new
coefficients give at `t` the value of the old ones at `x + t` (`JPoints.sum_shift1Gen`), and at
`(s, t)` the value of the old ones at `(x + s, y + t)` (`JPoints.eval2_shift2Gen`), for the value
`JPoints.eval2` of a polynomial in two variables. For nonnegative coefficients and a nonnegative
point every step raises a coefficient (`JPoints.le_getElem!_foldl_addMulAt`), so that a coefficient
at any step of the shift is at most its final value, and a final coefficient is at most the value of
the polynomial at `(x + 1, y + 1)` (`JPoints.getElem!_shift2Gen_le_eval2`), as a coefficient of a
polynomial with nonnegative coefficients is at most its value at `(1, 1)`
(`JPoints.getElem!_le_eval2_one`). The array of the coefficients of a function of two indices
(`JPoints.coeffArray`) holds its value `φ j k` at `P(j, k)` (`JPoints.getElem!_coeffArray`). The
value of a polynomial at a degree above its own, whose coefficients there vanish, is its value
(`JPoints.eval2_add_of_forall_eq_zero`), and `shift2` leaves the coefficients above its degree as
they are (`JPoints.getElem!_shift2Gen_of_lt`), so that a shift evaluated at a higher degree is the
polynomial at the shifted point (`JPoints.eval2_shift2Gen_of_le`).

## Main definitions

* `JPoints.shiftIndices`, `JPoints.addMulAt`, `JPoints.shift1Pairs`, `JPoints.shift1Gen`: the
  steps of `shift1` and its fold.
* `JPoints.shift2ColPairs`, `JPoints.shift2RowPairs`, `JPoints.shift2Gen`, `JPoints.shiftLines`:
  the steps of `shift2` and its folds.
* `JPoints.eval2`: the value of a polynomial in two variables.
* `JPoints.coeffArray`: the array of the coefficients of a function of two indices.

## Main statements

* `JPoints.sum_shift1Gen`: `shift1` is a Taylor shift.
* `JPoints.eval2_shift2Gen`, `JPoints.eval2_shift2Gen_of_le`: `shift2` is a Taylor shift, also
  at a higher degree.
* `JPoints.getElem!_shift2Gen_of_lt`, `JPoints.eval2_add_of_forall_eq_zero`: the coefficients
  above the degree.
* `JPoints.le_getElem!_foldl_addMulAt`, `JPoints.getElem!_shift2Gen_le_eval2`: the shifts of
  nonnegative coefficients.
* `JPoints.coeffIndex_inj`: the index `P(j, k)` determines `j` and `k`.
* `JPoints.getElem!_coeffArray`, `JPoints.eval2_coeffArray`: the arrays of the coefficients.

## Implementation notes

The first round of `shift1`, `j` from `deg - 1` down to `0`, divides the polynomial by `T - x`, with
the remainder in the constant coefficient (`JPoints.roundIndices`); the other rounds are the shift
of the quotient, a polynomial of degree `deg - 1` at the indices from `base + s` on
(`JPoints.shiftIndices_succ`), which gives the Taylor shift by induction on the degree. The columns
and the rows of `shift2` are lines of the array that do not meet (`JPoints.shiftLines`): the indices
`P(j, k) = L j + k` with `k < L` determine `j` and `k` (`JPoints.coeffIndex_inj`, in the forms of
the columns and the rows `JPoints.eq_of_add_mul_coeffRow_eq` and
`JPoints.eq_of_coeffRow_mul_add_eq`), so that each statement about indices holds for every
`L = JPoints.coeffRow ≥ 5`, as the constants check needs.
-/

@[expose] public section

namespace JPoints

open Finset

/-- The indices `j` of the coefficients that `shift1` raises, in its order: for each `i < deg`,
`j` from `deg - 1` down to `i`. -/
def shiftIndices (deg : ℕ) : List ℕ :=
  (List.range deg).flatMap fun i ↦ (List.range (deg - i)).map fun t ↦ deg - 1 - t

/-- The indices `j` from `deg - 1` down to `0`, the first round of `shift1`, a synthetic division
by `T - x`. -/
def roundIndices (deg : ℕ) : List ℕ := (List.range deg).map fun t ↦ deg - 1 - t

theorem shiftIndices_succ (D : ℕ) :
    shiftIndices (D + 1) = roundIndices (D + 1) ++ (shiftIndices D).map (· + 1) := by
  rw [shiftIndices, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, shiftIndices,
    List.map_flatMap, roundIndices]
  congr 1
  refine List.flatMap_congr fun i hi ↦ ?_
  rw [List.map_map, Nat.succ_eq_add_one, show D + 1 - (i + 1) = D - i by lia]
  refine List.map_congr_left fun t ht ↦ ?_
  simp only [List.mem_range] at hi ht
  simp only [Function.comp_apply]
  lia

theorem roundIndices_succ (D : ℕ) : roundIndices (D + 1) = D :: roundIndices D := by
  rw [roundIndices, List.range_succ_eq_map, List.map_cons, List.map_map, roundIndices]
  congr 1
  refine List.map_congr_left fun t ht ↦ ?_
  simp only [List.mem_range] at ht
  simp only [Function.comp_apply]
  lia

theorem lt_of_mem_shiftIndices {D j : ℕ} (h : j ∈ shiftIndices D) : j < D := by
  simp only [shiftIndices, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, t, ht, rfl⟩ := h
  lia

theorem lt_of_mem_roundIndices {D j : ℕ} (h : j ∈ roundIndices D) : j < D := by
  simp only [roundIndices, List.mem_map, List.mem_range] at h
  obtain ⟨t, ht, rfl⟩ := h
  lia

section Folds

variable {α : Type*} [Add α] [Mul α] [Inhabited α]

/-- `p[i] := p[i] + x * p[i']`, a step of a Taylor shift by `x`, for the pair `(i, i')` of indices
into the array `p`. -/
def addMulAt (x : α) (p : Array α) (ii : ℕ × ℕ) : Array α :=
  p.set! ii.1 (p[ii.1]! + x * p[ii.2]!)

/-- The pairs `(base + j s, base + (j + 1) s)` of indices of the steps of `shift1` on the
coefficients `p[base + j s]`, `j ≤ deg`, for the indices `j` of `JPoints.shiftIndices`. -/
def shift1Pairs (base deg s : ℕ) : List (ℕ × ℕ) :=
  (shiftIndices deg).map fun j ↦ (base + j * s, base + (j + 1) * s)

/-- `shift1` of the model as a fold over its steps (`JPoints.shift1Pairs`), for any type of
coefficients: the Taylor shift of the polynomial of degree `deg` with the coefficients
`p[base + j s]` to `x`. -/
def shift1Gen (p : Array α) (base deg s : ℕ) (x : α) : Array α :=
  (shift1Pairs base deg s).foldl (addMulAt x) p

/-- The steps of the shifts of the columns `k ≤ deg` of `shift2`, in its order: the coefficients
`P(j, k)` (`JPoints.coeffIndex j k`), `j ≤ deg - k`, of the column `k` shifted in `b`. -/
def shift2ColPairs (deg : ℕ) : List (ℕ × ℕ) :=
  (List.range (deg + 1)).flatMap fun k ↦ shift1Pairs k (deg - k) coeffRow

/-- The steps of the shifts of the rows `j ≤ deg` of `shift2`, in its order: the coefficients
`P(j, k)` (`JPoints.coeffIndex j k`), `k ≤ deg - j`, of the row `j` shifted in `c`. -/
def shift2RowPairs (deg : ℕ) : List (ℕ × ℕ) :=
  (List.range (deg + 1)).flatMap fun j ↦ shift1Pairs (coeffRow * j) (deg - j) 1

/-- `shift2` of the model as two folds over its steps, for any type of coefficients: the shift of
the polynomial of degree `deg` in two variables with the coefficients `q[P(j, k)]`
(`P(j, k) = JPoints.coeffIndex j k`) to `(x, y)`, each column shifted by `x`
(`JPoints.shift2ColPairs`), then each row by `y` (`JPoints.shift2RowPairs`). -/
def shift2Gen (q : Array α) (deg : ℕ) (x y : α) : Array α :=
  (shift2RowPairs deg).foldl (addMulAt y) ((shift2ColPairs deg).foldl (addMulAt x) q)

theorem size_addMulAt (x : α) (p : Array α) (ii : ℕ × ℕ) : (addMulAt x p ii).size = p.size :=
  Array.size_set! ..

theorem size_foldl_addMulAt (x : α) (L : List (ℕ × ℕ)) (p : Array α) :
    (L.foldl (addMulAt x) p).size = p.size := by
  induction L generalizing p with
  | nil => rfl
  | cons ii L ih => rw [List.foldl_cons, ih, size_addMulAt]

theorem getElem!_foldl_addMulAt_of_forall_ne (x : α) {L : List (ℕ × ℕ)} {i : ℕ}
    (h : ∀ ii ∈ L, ii.1 ≠ i) (p : Array α) : (L.foldl (addMulAt x) p)[i]! = p[i]! := by
  induction L generalizing p with
  | nil => rfl
  | cons ii L ih =>
    rw [List.foldl_cons, ih (fun jj hj ↦ h jj (List.mem_cons_of_mem _ hj)), addMulAt,
      Array.getElem!_set!_ne _ _ _ _ (h ii List.mem_cons_self)]

theorem size_shift1Gen (p : Array α) (base D s : ℕ) (x : α) :
    (shift1Gen p base D s x).size = p.size :=
  size_foldl_addMulAt ..

/-- The shifts by `x` of the lines `b i + j σ`, `j ≤ D i`, `i < m`, of the array `q`, one after the
other, as `shift2` shifts its columns and its rows. -/
def shiftLines (q : Array α) (b D : ℕ → ℕ) (σ m : ℕ) (x : α) : Array α :=
  (List.range m).foldl (fun q i ↦ shift1Gen q (b i) (D i) σ x) q

theorem size_shiftLines (q : Array α) (b D : ℕ → ℕ) (σ m : ℕ) (x : α) :
    (shiftLines q b D σ m x).size = q.size := by
  induction m with
  | zero => rfl
  | succ m ih => rw [shiftLines, List.range_succ, List.foldl_append, ← shiftLines, List.foldl_cons,
      List.foldl_nil, size_shift1Gen, ih]

theorem shiftLines_succ (q : Array α) (b D : ℕ → ℕ) (σ m : ℕ) (x : α) :
    shiftLines q b D σ (m + 1) x = shift1Gen (shiftLines q b D σ m x) (b m) (D m) σ x := by
  rw [shiftLines, List.range_succ, List.foldl_append, ← shiftLines]
  rfl

theorem shift2Gen_eq_shiftLines (q : Array α) (deg : ℕ) (x y : α) :
    shift2Gen q deg x y = shiftLines (shiftLines q (fun k ↦ k) (fun k ↦ deg - k) coeffRow
      (deg + 1) x) (fun j ↦ coeffRow * j) (fun j ↦ deg - j) 1 (deg + 1) y := by
  rw [shift2Gen, shift2RowPairs, shift2ColPairs, List.foldl_flatMap, List.foldl_flatMap]
  rfl

-- The shift of a line leaves the entries of the other lines as they are.
private theorem getElem!_shift1Gen_of_ne {σ : ℕ} {b D : ℕ → ℕ} {M : ℕ} (x : α) (p : Array α)
    (hdisj : ∀ i < M, ∀ i' < M, ∀ j ≤ D i, ∀ j' ≤ D i', b i + j * σ = b i' + j' * σ → i = i')
    {i i' : ℕ} (hi : i < M) (hi' : i' < M) (hne : i ≠ i') {j : ℕ} (hj : j ≤ D i) :
    (shift1Gen p (b i') (D i') σ x)[b i + j * σ]! = p[b i + j * σ]! := by
  refine getElem!_foldl_addMulAt_of_forall_ne x (fun ii hii ↦ ?_) p
  simp only [shift1Pairs, List.mem_map] at hii
  obtain ⟨j', hj', rfl⟩ := hii
  exact fun h ↦ hne (hdisj i' hi' i hi j' (lt_of_mem_shiftIndices hj').le j hj h).symm

/-- The shifts of the first `m` of disjoint lines leave the lines after them as they are. -/
theorem getElem!_shiftLines_of_le {σ : ℕ} {b D : ℕ → ℕ} {M : ℕ} {q : Array α} (x : α)
    (hdisj : ∀ i < M, ∀ i' < M, ∀ j ≤ D i, ∀ j' ≤ D i', b i + j * σ = b i' + j' * σ → i = i')
    {m i : ℕ} (hmi : m ≤ i) (hiM : i < M) {j : ℕ} (hj : j ≤ D i) :
    (shiftLines q b D σ m x)[b i + j * σ]! = q[b i + j * σ]! := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [shiftLines_succ, getElem!_shift1Gen_of_ne x _ hdisj hiM (by lia) (by lia) hj]
    exact ih (by lia)

end Folds

theorem shift1Pairs_succ (base D s : ℕ) :
    shift1Pairs base (D + 1) s =
      (roundIndices (D + 1)).map (fun j ↦ (base + j * s, base + (j + 1) * s)) ++
        shift1Pairs (base + s) D s := by
  rw [shift1Pairs, shiftIndices_succ, List.map_append, List.map_map, shift1Pairs]
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply, Prod.mk.injEq]
  constructor <;> ring

section Shift

variable {R : Type*} [CommRing R] [Inhabited R]

-- The first round of `shift1` on the coefficients `p[base + j s]`, `j ≤ D`: the synthetic
-- division by `X - x`.
private def roundGen (p : Array R) (base D s : ℕ) (x : R) : Array R :=
  ((roundIndices D).map fun j ↦ (base + j * s, base + (j + 1) * s)).foldl (addMulAt x) p

private theorem roundGen_succ (p : Array R) (base D s : ℕ) (x : R) :
    roundGen p base (D + 1) s x =
      roundGen (addMulAt x p (base + D * s, base + (D + 1) * s)) base D s x := by
  rw [roundGen, roundIndices_succ, List.map_cons, List.foldl_cons, roundGen]

-- The first round leaves the coefficients from the `D`-th on as they are.
private theorem getElem!_roundGen_of_le (p : Array R) {base s : ℕ} (hs : 0 < s) {D i : ℕ}
    (hi : D ≤ i) (x : R) : (roundGen p base D s x)[base + i * s]! = p[base + i * s]! := by
  refine getElem!_foldl_addMulAt_of_forall_ne x (fun ii hii ↦ ?_) p
  simp only [List.mem_map] at hii
  obtain ⟨j, hj, rfl⟩ := hii
  lia [Nat.mul_lt_mul_of_pos_right ((lt_of_mem_roundIndices hj).trans_le hi) hs]

-- The first round of `shift1` divides the polynomial by `T - x`: the remainder is the new
-- constant coefficient, the quotient has the new coefficients `1, …, D`.
private theorem sum_eq_roundGen (x T : R) {base s : ℕ} (hs : 0 < s) (D : ℕ) {p : Array R}
    (hp : base + D * s < p.size) :
    ∑ j ∈ range (D + 1), p[base + j * s]! * T ^ j = (roundGen p base D s x)[base]! +
      (T - x) * ∑ j ∈ range D, (roundGen p base D s x)[base + (j + 1) * s]! * T ^ j := by
  induction D generalizing p with
  | zero => simp [roundGen, roundIndices]
  | succ D ih =>
    have hlt {i j : ℕ} (hij : i < j) : i * s < j * s := Nat.mul_lt_mul_of_pos_right hij hs
    set p1 := addMulAt x p (base + D * s, base + (D + 1) * s)
    have f1 (j : ℕ) (hj : j < D) : p1[base + j * s]! = p[base + j * s]! :=
      Array.getElem!_set!_ne _ _ _ _ (by lia [hlt hj])
    have f2 : p1[base + D * s]! = p[base + D * s]! + x * p[base + (D + 1) * s]! :=
      Array.getElem!_set!_self _ _ _ (by lia [hlt (lt_add_one D)])
    have f3 : (roundGen p1 base D s x)[base + (D + 1) * s]! = p[base + (D + 1) * s]! := by
      rw [getElem!_roundGen_of_le _ hs (Nat.le_succ D)]
      exact Array.getElem!_set!_ne _ _ _ _ (by lia [hlt (lt_add_one D)])
    have := ih (p := p1) (by rw [size_addMulAt]; lia [hlt (lt_add_one D)])
    rw [sum_range_succ, sum_congr rfl fun j hj ↦ by rw [f1 j (mem_range.mp hj)], f2] at this
    rw [roundGen_succ, sum_range_succ (fun j ↦ p[base + j * s]! * T ^ j) (D + 1),
      sum_range_succ (fun j ↦ p[base + j * s]! * T ^ j) D,
      sum_range_succ (fun j ↦ (roundGen p1 base D s x)[base + (j + 1) * s]! * T ^ j) D, f3]
    linear_combination this

private theorem shift1Gen_succ (p : Array R) (base D s : ℕ) (x : R) :
    shift1Gen p base (D + 1) s x = shift1Gen (roundGen p base (D + 1) s x) (base + s) D s x := by
  rw [shift1Gen, shift1Pairs_succ, List.foldl_append, roundGen, shift1Gen]

-- The shift of the coefficients from `base + s` on leaves the one at `base` as it is.
private theorem getElem!_shift1Gen_add {s : ℕ} (hs : 0 < s) (p : Array R) (base D : ℕ) (x : R) :
    (shift1Gen p (base + s) D s x)[base]! = p[base]! := by
  refine getElem!_foldl_addMulAt_of_forall_ne x (fun ii hi ↦ ?_) _
  simp only [shift1Pairs, List.mem_map] at hi
  obtain ⟨j, -, rfl⟩ := hi
  lia

/-- `shift1` shifts the polynomial `∑ p[base + j s] T ^ j` of degree `D` to `x`: the new
coefficients give at `t` the value of the old ones at `x + t`. -/
theorem sum_shift1Gen (x t : R) {s : ℕ} (hs : 0 < s) (D : ℕ) {base : ℕ} {p : Array R}
    (hp : base + D * s < p.size) :
    ∑ j ∈ range (D + 1), (shift1Gen p base D s x)[base + j * s]! * t ^ j =
      ∑ j ∈ range (D + 1), p[base + j * s]! * (x + t) ^ j := by
  induction D generalizing base p with
  | zero => simp [shift1Gen, shift1Pairs, shiftIndices]
  | succ D ih =>
    have e (j : ℕ) : base + s + j * s = base + (j + 1) * s := by ring
    have := ih (base := base + s) (p := roundGen p base (D + 1) s x)
      (by rw [roundGen, size_foldl_addMulAt]; lia [add_one_mul D s])
    simp only [e] at this
    rw [shift1Gen_succ, sum_range_succ', sum_eq_roundGen x (x + t) hs (D + 1) hp, zero_mul,
      add_zero, getElem!_shift1Gen_add hs, add_sub_cancel_left, pow_zero, mul_one, ← this, mul_sum,
      add_comm]
    exact congr(_ + $(sum_congr rfl fun k _ ↦ by ring))

/-- The shifts of disjoint lines: each line shifted gives at `u` the value of the line before at
`x + u`. -/
theorem sum_shiftLines {σ : ℕ} {b D : ℕ → ℕ} {M : ℕ} {q : Array R} (x u : R) (hσ : 0 < σ)
    (hsize : ∀ i < M, b i + D i * σ < q.size)
    (hdisj : ∀ i < M, ∀ i' < M, ∀ j ≤ D i, ∀ j' ≤ D i', b i + j * σ = b i' + j' * σ → i = i')
    {m : ℕ} (hm : m ≤ M) {i : ℕ} (hi : i < m) :
    ∑ j ∈ range (D i + 1), (shiftLines q b D σ m x)[b i + j * σ]! * u ^ j =
      ∑ j ∈ range (D i + 1), q[b i + j * σ]! * (x + u) ^ j := by
  induction m with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    rw [shiftLines_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [← ih (by lia) hi]
      exact sum_congr rfl fun j hj ↦ by
        rw [getElem!_shift1Gen_of_ne x _ hdisj (by lia) (by lia) (by lia)
          (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    · rw [sum_shift1Gen x u hσ (D i) (by rw [size_shiftLines]; exact hsize i (by lia))]
      exact sum_congr rfl fun j hj ↦ by
        rw [getElem!_shiftLines_of_le x hdisj le_rfl (by lia)
          (Nat.lt_succ_iff.mp (mem_range.mp hj))]

end Shift

/-! ### The indices of the coefficients -/

theorem coeffIndex_lt_numCoeffs {j k : ℕ} (hj : j < coeffRow) (hk : k < coeffRow) :
    coeffIndex j k < numCoeffs :=
  calc coeffRow * j + k < coeffRow * j + coeffRow := by lia
    _ = coeffRow * (j + 1) := by ring
    _ ≤ coeffRow * coeffRow := Nat.mul_le_mul_left _ hj

theorem coeffIndex_div_coeffRow {j k : ℕ} (hk : k < coeffRow) : coeffIndex j k / coeffRow = j := by
  rw [coeffIndex, Nat.mul_add_div (Nat.zero_lt_of_lt hk), Nat.div_eq_of_lt hk, Nat.add_zero]

theorem coeffIndex_mod_coeffRow {j k : ℕ} (hk : k < coeffRow) : coeffIndex j k % coeffRow = k := by
  rw [coeffIndex, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hk]

@[simp]
theorem coeffIndex_zero_zero : coeffIndex 0 0 = 0 := rfl

theorem five_mul_coeffRow_le : 5 * coeffRow ≤ numCoeffs :=
  Nat.mul_le_mul_right _ five_le_coeffRow

theorem coeffIndex_inj {j k j' k' : ℕ} (hk : k < coeffRow) (hk' : k' < coeffRow) :
    coeffIndex j k = coeffIndex j' k' ↔ j = j' ∧ k = k' :=
  ⟨fun h ↦ Nat.eq_and_eq_of_mul_add_eq_mul_add hk hk'
    (by simpa only [coeffIndex, Nat.mul_comm coeffRow] using h), fun h ↦ by rw [h.1, h.2]⟩

/-- The columns `k + j L`, `k < L`, of the indices do not meet: the disjointness of the lines of
the columns of `shift2`. -/
theorem eq_of_add_mul_coeffRow_eq {j k j' k' : ℕ} (hk : k < coeffRow) (hk' : k' < coeffRow)
    (h : k + j * coeffRow = k' + j' * coeffRow) : k = k' :=
  ((coeffIndex_inj (j := j) (j' := j') hk hk').mp (by rw [coeffIndex, coeffIndex]; lia)).2

/-- The rows `L j + k`, `k < L`, of the indices do not meet: the disjointness of the lines of the
rows of `shift2`. -/
theorem eq_of_coeffRow_mul_add_eq {j k j' k' : ℕ} (hk : k < coeffRow) (hk' : k' < coeffRow)
    (h : coeffRow * j + k * 1 = coeffRow * j' + k' * 1) : j = j' :=
  ((coeffIndex_inj hk hk').mp (by simpa only [coeffIndex, Nat.mul_one] using h)).1

/-! ### The arrays of the coefficients -/

/-- The array of the coefficients `φ j k` of `s ^ j t ^ k` of a polynomial in two variables at the
indices `P(j, k)`, `j, k < L`, as the analysis of the tube keeps them. -/
def coeffArray {α : Type*} (φ : ℕ → ℕ → α) : Array α :=
  Array.ofFn fun i : Fin numCoeffs ↦ φ (i / coeffRow) (i % coeffRow)

theorem size_coeffArray {α : Type*} (φ : ℕ → ℕ → α) : (coeffArray φ).size = numCoeffs :=
  Array.size_ofFn

theorem getElem!_coeffArray_of_lt {α : Type*} [Inhabited α] (φ : ℕ → ℕ → α) {i : ℕ}
    (hi : i < numCoeffs) : (coeffArray φ)[i]! = φ (i / coeffRow) (i % coeffRow) := by
  rw [coeffArray, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem getElem!_coeffArray {α : Type*} [Inhabited α] (φ : ℕ → ℕ → α) {j k : ℕ}
    (hj : j < coeffRow) (hk : k < coeffRow) : (coeffArray φ)[coeffIndex j k]! = φ j k := by
  rw [getElem!_coeffArray_of_lt φ (coeffIndex_lt_numCoeffs hj hk), coeffIndex_div_coeffRow hk,
    coeffIndex_mod_coeffRow hk]

/-- The coefficients of the degrees above `d` of an array of coefficients of degree `D < L` vanish
when those of the function vanish: the form in which the values at a higher degree
(`JPoints.eval2_add_of_forall_eq_zero`) and the shifts (`JPoints.eval2_shift2Gen_of_le`) take
them. -/
theorem getElem!_coeffArray_eq_zero {α : Type*} [Zero α] [Inhabited α] {φ : ℕ → ℕ → α} {d D : ℕ}
    (hD : D < coeffRow) (hφ : ∀ j k, d < j + k → φ j k = 0) (j k : ℕ) (h1 : d < j + k)
    (h2 : j + k ≤ D) : (coeffArray φ)[coeffIndex j k]! = 0 := by
  rw [getElem!_coeffArray φ (by lia) (by lia), hφ j k h1]

/-! ### The steps of `shift2` -/

theorem mem_shift2ColPairs {deg : ℕ} {ii : ℕ × ℕ} (h : ii ∈ shift2ColPairs deg) :
    ∃ j k, j + 1 + k ≤ deg ∧ ii = (coeffIndex j k, coeffIndex (j + 1) k) := by
  simp only [shift2ColPairs, shift1Pairs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨k, hk, j, hj, rfl⟩ := h
  have := lt_of_mem_shiftIndices hj
  exact ⟨j, k, by lia, by simp only [coeffIndex, Prod.mk.injEq]; constructor <;> ring⟩

theorem mem_shift2RowPairs {deg : ℕ} {ii : ℕ × ℕ} (h : ii ∈ shift2RowPairs deg) :
    ∃ j k, j + (k + 1) ≤ deg ∧ ii = (coeffIndex j k, coeffIndex j (k + 1)) := by
  simp only [shift2RowPairs, shift1Pairs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨j, hj, k, hk, rfl⟩ := h
  have := lt_of_mem_shiftIndices hk
  exact ⟨j, k, by lia, by simp only [coeffIndex, Prod.mk.injEq]; constructor <;> ring⟩

/-- `shift2` of degree `deg < L = JPoints.coeffRow` leaves the coefficients of `b ^ j c ^ k` with
`j + k > deg` as they are: its steps write only the coefficients of degree at most `deg`. -/
theorem getElem!_shift2Gen_of_lt {α : Type*} [Add α] [Mul α] [Inhabited α] {deg j k : ℕ}
    (hdeg : deg < coeffRow) (hk : k < coeffRow) (h : deg < j + k) (q : Array α) (x y : α) :
    (shift2Gen q deg x y)[coeffIndex j k]! = q[coeffIndex j k]! := by
  rw [shift2Gen, getElem!_foldl_addMulAt_of_forall_ne _ (fun ii hii ↦ ?_),
    getElem!_foldl_addMulAt_of_forall_ne _ (fun ii hii ↦ ?_)]
  · obtain ⟨j', k', hjk, rfl⟩ := mem_shift2ColPairs hii
    exact fun e ↦ absurd ((coeffIndex_inj (by lia) hk).mp e) (by lia)
  · obtain ⟨j', k', hjk, rfl⟩ := mem_shift2RowPairs hii
    exact fun e ↦ absurd ((coeffIndex_inj (by lia) hk).mp e) (by lia)

/-! ### The value of a polynomial in two variables -/

/-- The value at `(s, t)` of the polynomial of degree `deg` in two variables with the coefficients
`q[P(j, k)]` (`P(j, k) = JPoints.coeffIndex j k`), `j + k ≤ deg`, the sum that `tube_eval` computes
in doubles. -/
def eval2 {R : Type*} [CommSemiring R] [Inhabited R] (q : Array R) (deg : ℕ) (s t : R) : R :=
  ∑ j ∈ range (deg + 1), ∑ k ∈ range (deg - j + 1), q[coeffIndex j k]! * s ^ j * t ^ k

theorem eval2_coeffArray {R : Type*} [CommSemiring R] [Inhabited R] (φ : ℕ → ℕ → R) {deg : ℕ}
    (hdeg : deg < coeffRow) (s t : R) :
    eval2 (coeffArray φ) deg s t =
      ∑ j ∈ range (deg + 1), ∑ k ∈ range (deg - j + 1), φ j k * s ^ j * t ^ k :=
  sum_congr rfl fun j hj ↦ sum_congr rfl fun k hk ↦ by
    simp only [mem_range] at hj hk
    rw [getElem!_coeffArray φ (by lia) (by lia)]

section Degrees

variable {R : Type*} [CommSemiring R] [Inhabited R]

theorem eval2_succ (q : Array R) (D : ℕ) (s t : R) :
    eval2 q (D + 1) s t = eval2 q D s t +
      ∑ j ∈ range (D + 2), q[coeffIndex j (D + 1 - j)]! * s ^ j * t ^ (D + 1 - j) := by
  rw [eval2, eval2, sum_range_succ, sum_range_succ (fun j ↦ q[coeffIndex j (D + 1 - j)]! * s ^ j *
    t ^ (D + 1 - j)), Nat.sub_self, zero_add, sum_range_one, ← add_assoc, ← sum_add_distrib]
  refine congr($(sum_congr rfl fun j hj ↦ ?_) + _)
  have hj := mem_range.mp hj
  rw [show D + 1 - j + 1 = D - j + 1 + 1 by lia, sum_range_succ, show D - j + 1 = D + 1 - j by lia]

/-- The value of a polynomial of degree `D + 1` whose coefficients of degree `D + 1` vanish is
that of degree `D`. -/
theorem eval2_succ_of_forall_eq_zero {q : Array R} {D : ℕ}
    (h : ∀ j ≤ D + 1, q[coeffIndex j (D + 1 - j)]! = 0) (s t : R) :
    eval2 q (D + 1) s t = eval2 q D s t := by
  rw [eval2_succ, sum_eq_zero fun j hj ↦ by rw [h j (by simpa [Nat.lt_succ_iff] using hj)]; simp,
    add_zero]

/-- The value of a polynomial of degree `D` does not change when it is evaluated at a degree
`D + m`, its coefficients of the degrees from `D + 1` to `D + m` being `0`. -/
theorem eval2_add_of_forall_eq_zero {q : Array R} {D m : ℕ}
    (h : ∀ j k, D < j + k → j + k ≤ D + m → q[coeffIndex j k]! = 0) (s t : R) :
    eval2 q (D + m) s t = eval2 q D s t := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, eval2_succ_of_forall_eq_zero fun j hj ↦ h j _ (by lia) (by lia),
      ih fun j k h1 h2 ↦ h j k h1 (by lia)]

end Degrees

section Eval

variable {R : Type*} [CommRing R] [Inhabited R]

-- `eval2` by the columns `k ≤ deg`, each a polynomial in `s` of degree `deg - k`.
private theorem eval2_eq_sum_cols (q : Array R) (deg : ℕ) (s t : R) :
    eval2 q deg s t = ∑ k ∈ range (deg + 1),
      (∑ j ∈ range (deg - k + 1), q[k + j * coeffRow]! * s ^ j) * t ^ k := by
  rw [eval2, sum_comm' (s' := fun k ↦ range (deg - k + 1)) (t' := range (deg + 1))
    (fun j k ↦ by simp only [mem_range]; lia)]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_mul]
  exact sum_congr rfl fun j _ ↦ by rw [coeffIndex, add_comm, mul_comm j]

-- `eval2` by the rows `j ≤ deg`, each a polynomial in `t` of degree `deg - j`.
private theorem eval2_eq_sum_rows (q : Array R) (deg : ℕ) (s t : R) :
    eval2 q deg s t = ∑ j ∈ range (deg + 1),
      (∑ k ∈ range (deg - j + 1), q[coeffRow * j + k * 1]! * t ^ k) * s ^ j := by
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_mul]
  exact sum_congr rfl fun k _ ↦ by rw [coeffIndex, mul_one]; ring

-- The shifts of the columns of `shift2`, each a polynomial in `s`.
private theorem sum_shiftLines_cols (x s : R) {deg : ℕ} (hdeg : deg < coeffRow) {q : Array R}
    (hq : numCoeffs ≤ q.size) {k : ℕ} (hk : k < deg + 1) :
    ∑ j ∈ range (deg - k + 1), (shiftLines q (fun k ↦ k) (fun k ↦ deg - k) coeffRow (deg + 1)
      x)[k + j * coeffRow]! * s ^ j =
      ∑ j ∈ range (deg - k + 1), q[k + j * coeffRow]! * (x + s) ^ j :=
  sum_shiftLines (b := fun k ↦ k) (D := fun k ↦ deg - k) x s (by lia)
    (fun k hk ↦ by
      have := coeffIndex_lt_numCoeffs (j := deg - k) (k := k) (by lia) (by lia)
      rw [coeffIndex] at this; lia [mul_comm (deg - k) coeffRow])
    (fun _ hk _ hk' _ _ _ _ h ↦ eq_of_add_mul_coeffRow_eq (by lia) (by lia) h) le_rfl hk

-- The shifts of the rows of `shift2`, each a polynomial in `t`.
private theorem sum_shiftLines_rows (y t : R) {deg : ℕ} (hdeg : deg < coeffRow) {q : Array R}
    (hq : numCoeffs ≤ q.size) {j : ℕ} (hj : j < deg + 1) :
    ∑ k ∈ range (deg - j + 1), (shiftLines q (fun j ↦ coeffRow * j) (fun j ↦ deg - j) 1
      (deg + 1) y)[coeffRow * j + k * 1]! * t ^ k =
      ∑ k ∈ range (deg - j + 1), q[coeffRow * j + k * 1]! * (y + t) ^ k :=
  sum_shiftLines (b := fun j ↦ coeffRow * j) (D := fun j ↦ deg - j) y t one_pos
    (fun j hj ↦ by
      have := coeffIndex_lt_numCoeffs (j := j) (k := deg - j) (by lia) (by lia)
      rw [coeffIndex] at this; lia)
    (fun _ _ _ _ _ hk _ hk' h ↦ eq_of_coeffRow_mul_add_eq (by lia) (by lia) h) le_rfl hj

/-- `shift2` shifts the polynomial of degree `deg < L = JPoints.coeffRow` in two variables to
`(x, y)`: the new coefficients give at `(s, t)` the value of the old ones at `(x + s, y + t)`. -/
theorem eval2_shift2Gen (x y s t : R) {deg : ℕ} (hdeg : deg < coeffRow) {q : Array R}
    (hq : numCoeffs ≤ q.size) :
    eval2 (shift2Gen q deg x y) deg s t = eval2 q deg (x + s) (y + t) := by
  rw [shift2Gen_eq_shiftLines, eval2_eq_sum_rows, sum_congr rfl fun j hj ↦ by
    rw [sum_shiftLines_rows y t hdeg (by rw [size_shiftLines]; exact hq) (mem_range.mp hj)],
    ← eval2_eq_sum_rows, eval2_eq_sum_cols, eval2_eq_sum_cols,
    sum_congr rfl fun k hk ↦ by rw [sum_shiftLines_cols x s hdeg hq (mem_range.mp hk)]]

/-- A polynomial of degree `d` shifted to `(x, y)` and evaluated at a degree `D ≥ d` is the
polynomial at `(x + s, y + t)`, its coefficients of the degrees from `d + 1` to `D` being `0`. -/
theorem eval2_shift2Gen_of_le {q : Array R} {d D : ℕ}
    (hdD : d ≤ D) (hD : D < coeffRow) (hq : numCoeffs ≤ q.size)
    (h : ∀ j k, d < j + k → j + k ≤ D → q[coeffIndex j k]! = 0) (x y s t : R) :
    eval2 (shift2Gen q d x y) D s t = eval2 q D (x + s) (y + t) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hdD
  rw [eval2_add_of_forall_eq_zero (fun j k h1 h2 ↦ ?_), eval2_shift2Gen x y s t (by lia) hq,
    eval2_add_of_forall_eq_zero h]
  rw [getElem!_shift2Gen_of_lt (by lia) (by lia) h1]
  exact h j k h1 h2

end Eval

section Majorant

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [Inhabited R]

-- A step of a Taylor shift by `x ≥ 0` of nonnegative coefficients raises one of them.
private theorem le_getElem!_addMulAt {x : R} (hx : 0 ≤ x) {p : Array R} (hp : ∀ i : ℕ, 0 ≤ p[i]!)
    (ii : ℕ × ℕ) (i : ℕ) : p[i]! ≤ (addMulAt x p ii)[i]! := by
  rw [addMulAt]
  by_cases h : ii.1 = i
  · subst h
    by_cases hs : ii.1 < p.size
    · rw [Array.getElem!_set!_self _ _ _ hs]
      exact le_add_of_nonneg_right (mul_nonneg hx (hp _))
    · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by lia)]
  · rw [Array.getElem!_set!_ne _ _ _ _ h]

/-- The steps of a Taylor shift by `x ≥ 0` of nonnegative coefficients keep them nonnegative and
raise each: an entry after any number of steps is at least the entry before, as the majorants of
the error bounds of the shifts need. -/
theorem le_getElem!_foldl_addMulAt {x : R} (hx : 0 ≤ x) (L : List (ℕ × ℕ)) {p : Array R}
    (hp : ∀ i : ℕ, 0 ≤ p[i]!) :
    (∀ i : ℕ, 0 ≤ (L.foldl (addMulAt x) p)[i]!) ∧
      ∀ i : ℕ, p[i]! ≤ (L.foldl (addMulAt x) p)[i]! := by
  induction L generalizing p with
  | nil => exact ⟨hp, fun _ ↦ le_rfl⟩
  | cons ii L ih =>
    have h1 (i : ℕ) := le_getElem!_addMulAt hx hp ii i
    obtain ⟨ih1, ih2⟩ := ih (p := addMulAt x p ii) fun i ↦ (hp i).trans (h1 i)
    exact ⟨ih1, fun i ↦ (h1 i).trans (ih2 i)⟩

theorem getElem!_shift2Gen_nonneg {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) (deg : ℕ) {x y : R}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (i : ℕ) : 0 ≤ (shift2Gen q deg x y)[i]! :=
  (le_getElem!_foldl_addMulAt hy _ (le_getElem!_foldl_addMulAt hx _ hq).1).1 i

end Majorant

section Bounds

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Inhabited R]

theorem eval2_le_eval2 {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) (deg : ℕ) {s s' t t' : R}
    (hs : 0 ≤ s) (hss : s ≤ s') (ht : 0 ≤ t) (htt : t ≤ t') :
    eval2 q deg s t ≤ eval2 q deg s' t' :=
  sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hss j) (hq _))
    (pow_le_pow_left₀ ht htt k) (pow_nonneg ht k) (mul_nonneg (hq _) (pow_nonneg (hs.trans hss) j))

/-- The value of a polynomial of degree `deg` with nonnegative coefficients at a point scaled by
`c ≥ 1` is at most `c ^ deg` times its value at the point. -/
theorem eval2_mul_mul_le {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) (deg : ℕ) {c s t : R}
    (hc : 1 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    eval2 q deg (c * s) (c * t) ≤ c ^ deg * eval2 q deg s t := by
  rw [eval2, eval2, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  have hjk : j + k ≤ deg := by simp only [mem_range] at hj hk; lia
  have h1 : c ^ (j + k) ≤ c ^ deg := pow_le_pow_right₀ hc hjk
  have h2 : 0 ≤ q[coeffIndex j k]! * s ^ j * t ^ k :=
    mul_nonneg (mul_nonneg (hq _) (pow_nonneg hs j)) (pow_nonneg ht k)
  calc q[coeffIndex j k]! * (c * s) ^ j * (c * t) ^ k
      = c ^ (j + k) * (q[coeffIndex j k]! * s ^ j * t ^ k) := by
        rw [mul_pow, mul_pow, pow_add]; ring
    _ ≤ c ^ deg * (q[coeffIndex j k]! * s ^ j * t ^ k) := mul_le_mul_of_nonneg_right h1 h2

theorem eval2_nonneg {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) (D : ℕ) {X Y : R}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ eval2 q D X Y :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    mul_nonneg (mul_nonneg (hq _) (pow_nonneg hX _)) (pow_nonneg hY _)

theorem getElem!_le_eval2_one {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) {D j k : ℕ}
    (hjk : j + k ≤ D) : q[coeffIndex j k]! ≤ eval2 q D 1 1 := by
  rw [eval2]
  refine le_trans ?_ (single_le_sum (fun j' _ ↦ sum_nonneg fun k' _ ↦ ?_)
    (mem_range.mpr (by lia : j < D + 1)))
  · refine le_trans ?_ (single_le_sum (fun k' _ ↦ ?_) (mem_range.mpr (by lia : k < D - j + 1)))
    · simp
    · simpa using hq _
  · simpa using hq _

end Bounds

/-- A coefficient of the shift of a polynomial of degree `deg < L = JPoints.coeffRow` with
nonnegative coefficients to `(x, y)`, `x, y ≥ 0`, is at most the value of the polynomial at
`(x + 1, y + 1)`: the bound on the majorants of the shifted coefficients that keeps them finite. -/
theorem getElem!_shift2Gen_le_eval2 {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    [Inhabited R] {q : Array R} (hq : ∀ i : ℕ, 0 ≤ q[i]!) {deg : ℕ} (hdeg : deg < coeffRow)
    (hsize : numCoeffs ≤ q.size) {x y : R} (hx : 0 ≤ x) (hy : 0 ≤ y) {j k : ℕ}
    (hjk : j + k ≤ deg) :
    (shift2Gen q deg x y)[coeffIndex j k]! ≤ eval2 q deg (x + 1) (y + 1) :=
  (getElem!_le_eval2_one (getElem!_shift2Gen_nonneg hq deg hx hy) hjk).trans_eq
    (eval2_shift2Gen x y 1 1 hdeg hsize)

end JPoints

end
