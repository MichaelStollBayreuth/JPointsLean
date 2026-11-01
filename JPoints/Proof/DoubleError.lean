/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.DoubleArith

import JPoints.Mathlib.Algebra.Order.Ring.Pow
import JPoints.Proof.Truncation
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Field
import Mathlib.Tactic.Linarith

/-!
# The error bounds of computations in doubles

The error of a computation in doubles, counted operation by operation, as the analysis of the tube
needs it. A rounding to nearest of a rational number `v` on a grid `2 ^ (-k) ℤ`, `k ≤ 1074`
(`JPoints.OnGrid`), is within `|v| / 2 ^ 53` of `v` and on the same grid: the error of the
subnormal range does not arise (`JPoints.Double.IsGridRounding`,
`JPoints.Double.isGridRounding_ofDyadic`). Every finite double lies on the grid `2 ^ (-1074) ℤ`,
so that a sum of two doubles always rounds so; a product of doubles on the grids `2 ^ (-k) ℤ` and
`2 ^ (-l) ℤ` lies on the grid `2 ^ (-(k + l)) ℤ`, which keeps the products of a computation whose
inputs are integers, and whose grid grows by the grids of its factors, out of the subnormal range.

A double `x` approximates `v` with the majorant `a ≥ |v|` to within `n` roundings
(`JPoints.Double.Approx`) when it lies within `((1 + 2 ^ (-53)) ^ n - 1) a` of `v`: a sum adds the
majorants and takes the larger count plus one, a product multiplies the majorants and adds the
counts plus one (`JPoints.Double.Approx.add`, `JPoints.Double.Approx.mul`), so that the count of a
result is the number of roundings on the longest path to it, and its majorant the value of the
computation on the absolute values of the inputs. The inputs of the analysis of the tube are
approximations: `(double)n` of an integer (`JPoints.Double.approx_ofInt`) and `mpz_get_d`, which
truncates, within two roundings (`JPoints.Double.approx_mpzGetD`); the constants `0.5` and `32.0`
are exact (`JPoints.Double.approx_half`, `JPoints.Double.approx_thirtyTwo`). A computation whose
result is finite has finite operands (`JPoints.Double.isFinite_and_of_isFinite_add`,
`JPoints.Double.isFinite_and_of_isFinite_sub`, `JPoints.Double.isFinite_and_of_isFinite_mul`,
`JPoints.Double.isFinite_of_isFinite_div`), which `tube_ok` needs. Repeated products and sums in
order compose the counts of their steps (`JPoints.Double.Approx.iterate_mul`,
`JPoints.Double.Approx.foldl_add`); an approximation within less than the spacing of its grid is
exact (`JPoints.Double.Approx.exact`), and a double that approximates `v` with `v` as its majorant
within at most `2 ^ 20` roundings is at least `v / 2` (`JPoints.Double.Approx.div_two_le_toRat`),
positive when `v` is (`JPoints.Double.Approx.toRat_pos`). A majorant up to `2 ^ 1020` with the error
factor of at most `2 ^ 52` roundings stays below `2 ^ 1022`, as the finite sums and products need
(`JPoints.one_add_pow_mul_lt_two_pow_1022`). A quotient of a nonnegative double on a grid by a
double at least `1` has no error of the subnormal range (`JPoints.Double.div_bounds`).

## Main definitions

* `JPoints.OnGrid`: a rational number on the grid `2 ^ (-k) ℤ`.
* `JPoints.Double.IsGridRounding`: a rounding to nearest of a number on a grid.
* `JPoints.Double.Approx`: an approximation to within a number of roundings.

## Main statements

* `JPoints.Double.isGridRounding_ofDyadic`, `JPoints.Double.isGridRounding_add`,
  `JPoints.Double.isGridRounding_sub`, `JPoints.Double.isGridRounding_mul`,
  `JPoints.Double.isGridRounding_ofInt`: the roundings on a grid.
* `JPoints.Double.Approx.add`, `JPoints.Double.Approx.mul`, `JPoints.Double.Approx.neg`,
  `JPoints.Double.Approx.fabs`: the operations on approximations.
* `JPoints.Double.Approx.iterate_mul`, `JPoints.Double.Approx.foldl_add`: repeated products and
  sums.
* `JPoints.Double.approx_ofInt`, `JPoints.Double.approx_mpzGetD`: the inputs.
* `JPoints.Double.isFinite_and_of_isFinite_add`, `JPoints.Double.isFinite_and_of_isFinite_sub`,
  `JPoints.Double.isFinite_and_of_isFinite_mul`, `JPoints.Double.isFinite_of_isFinite_div`: finite
  operands of a finite result.
* `JPoints.Double.div_bounds`: the quotient by a double at least `1`.
* `JPoints.one_add_pow_sub_one_le`: the error factor of `n` roundings, linearly.
* `JPoints.one_add_pow_mul_lt_two_pow_1022`, `JPoints.Double.Approx.div_two_le_toRat`: the bounds
  of a majorant with its error factor.

## Implementation notes

The error factor `(1 + 2 ^ (-53)) ^ n - 1` of `n` roundings composes exactly: the factors of the
operands multiply, and a rounding multiplies by one factor more, so that the counts add up as the
operations do and no rounding of the counts up to powers of two is needed; for the final
comparisons, `JPoints.one_add_pow_sub_one_le` bounds the factor of up to `2 ^ 20` roundings
by `n 2 ^ (-53) (1 + 2 ^ (-32))`. The bound is that of rounding to nearest, `2 ^ (-53)` relative
(`JPoints.Double.ofDyadic_rounding`); the rule of the ties is not needed.
-/

@[expose] public section

namespace JPoints

/-! ### Grids -/

/-- The rational number `v` lies on the grid `2 ^ (-k) ℤ`, the integer multiples of `2 ^ (-k)`:
the values of a computation in doubles whose inputs are integers keep to such grids, the grid of a
product the sum of the grids of its factors (`JPoints.OnGrid.mul`), and a rounding of a value on
the grid `2 ^ (-k) ℤ`, `k ≤ 1074`, has no error of the subnormal range
(`JPoints.Double.isGridRounding_ofDyadic`). -/
def OnGrid (k : ℕ) (v : ℚ) : Prop := ∃ n : ℤ, v = n / 2 ^ k

namespace OnGrid

variable {k l : ℕ} {v w : ℚ}

theorem zero (k : ℕ) : OnGrid k 0 := ⟨0, by simp⟩

theorem intCast (n : ℤ) : OnGrid 0 n := ⟨n, by simp⟩

theorem add (hv : OnGrid k v) (hw : OnGrid k w) : OnGrid k (v + w) := by
  obtain ⟨n, rfl⟩ := hv
  obtain ⟨m, rfl⟩ := hw
  exact ⟨n + m, by push_cast; ring⟩

theorem neg (hv : OnGrid k v) : OnGrid k (-v) := by
  obtain ⟨n, rfl⟩ := hv
  exact ⟨-n, by push_cast; ring⟩

theorem sub (hv : OnGrid k v) (hw : OnGrid k w) : OnGrid k (v - w) := by
  rw [sub_eq_add_neg]; exact hv.add hw.neg

theorem abs (hv : OnGrid k v) : OnGrid k |v| := by
  rcases abs_choice v with h | h <;> rw [h]
  exacts [hv, hv.neg]

theorem mul (hv : OnGrid k v) (hw : OnGrid l w) : OnGrid (k + l) (v * w) := by
  obtain ⟨n, rfl⟩ := hv
  obtain ⟨m, rfl⟩ := hw
  exact ⟨n * m, by push_cast; rw [pow_add]; field⟩

theorem mono (hv : OnGrid k v) (h : k ≤ l) : OnGrid l v := by
  obtain ⟨n, rfl⟩ := hv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨n * 2 ^ d, by push_cast; rw [pow_add]; field⟩

theorem eq_of_abs_sub_lt (hv : OnGrid k v) (hw : OnGrid k w) (h : |v - w| < 1 / 2 ^ k) :
    v = w := by
  obtain ⟨n, rfl⟩ := hv
  obtain ⟨m, rfl⟩ := hw
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ k),
    div_lt_div_iff_of_pos_right (by positivity), ← Int.cast_sub, ← Int.cast_abs,
    ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, sub_eq_zero] at h
  rw [h]

theorem le_of_pos (h : OnGrid k v) (hv : 0 < v) : 1 / 2 ^ k ≤ v := by
  obtain ⟨n, rfl⟩ := h
  have hn : (0 : ℚ) < n := by
    by_contra! hn
    exact absurd hv (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hn (by positivity)))
  have : (1 : ℚ) ≤ n := mod_cast (show (1 : ℤ) ≤ n from mod_cast hn)
  exact div_le_div_of_nonneg_right this (by positivity)

theorem intCast_mul_zpow (n : ℤ) {e : ℤ} (h : -(k : ℤ) ≤ e) : OnGrid k (n * 2 ^ e) := by
  refine ⟨n * 2 ^ (e + k).toNat, ?_⟩
  push_cast
  rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_add₀ two_ne_zero, zpow_natCast]
  field

theorem ite_mul (neg : Bool) (hv : OnGrid k v) : OnGrid k ((if neg then -1 else 1) * v) := by
  cases neg
  · simpa using hv
  · simpa using hv.neg

end OnGrid

/-! ### The error factor of a count of roundings -/

theorem one_add_pow_le_one_add_pow {n m : ℕ} (h : n ≤ m) :
    ((1 : ℚ) + 1 / 2 ^ 53) ^ n ≤ (1 + 1 / 2 ^ 53) ^ m :=
  pow_le_pow_right₀ (by norm_num) h

/-- The factor `(1 + 2 ^ (-53)) ^ n` of at most `2 ^ 52` roundings is at most `2`. -/
theorem one_add_pow_le_two {n : ℕ} (hn : n ≤ 2 ^ 52) : (1 + 1 / 2 ^ 53 : ℚ) ^ n ≤ 2 := by
  have h := one_add_pow_mul_one_sub_mul_le_one (by positivity : (0 : ℚ) ≤ 1 / 2 ^ 53) n
  have h1 : (1 : ℚ) / 2 ≤ 1 - n * (1 / 2 ^ 53) := by
    have : (n : ℚ) ≤ 2 ^ 52 := mod_cast hn
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℚ) ≤ (1 + 1 / 2 ^ 53) ^ n)]

/-- The error factor `(1 + 2 ^ (-53)) ^ n - 1` of at most `2 ^ 20` roundings, in the linear form
`n 2 ^ (-53) (1 + 2 ^ (-32))`. -/
theorem one_add_pow_sub_one_le {n : ℕ} (hn : n ≤ 2 ^ 20) :
    (1 + 1 / 2 ^ 53 : ℚ) ^ n - 1 ≤ n / 2 ^ 53 * (1 + 1 / 2 ^ 32) := by
  have h := one_add_pow_mul_one_sub_mul_le_one (by positivity : (0 : ℚ) ≤ 1 / 2 ^ 53) n
  have h2 := one_add_pow_le_two (n := n) (by lia)
  have h0 : (n : ℚ) ≤ 2 ^ 20 := mod_cast hn
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℚ) ≤ n / 2 ^ 53)]

/-- A value of at most `2 ^ 1020` times the error factor of at most `2 ^ 52` roundings is below
`2 ^ 1022`, the bound that `JPoints.Double.Approx.add_of_lt` and
`JPoints.Double.Approx.mul_of_lt` ask of the majorant of a sum or a product. -/
theorem one_add_pow_mul_lt_two_pow_1022 {n : ℕ} {x : ℚ} (hn : n ≤ 2 ^ 52) (hx0 : 0 ≤ x)
    (hx : x ≤ 2 ^ 1020) : (1 + 1 / 2 ^ 53 : ℚ) ^ n * x < 2 ^ 1022 :=
  calc (1 + 1 / 2 ^ 53 : ℚ) ^ n * x ≤ 2 * 2 ^ 1020 :=
        mul_le_mul (one_add_pow_le_two hn) hx hx0 (by norm_num)
    _ = 2 ^ 1021 := (pow_succ' 2 1020).symm
    _ < 2 ^ 1022 := pow_lt_pow_right₀ one_lt_two (by norm_num)

namespace Double

/-! ### Finite operands of a finite result -/

theorem isFinite_and_of_isFinite_add {x y : Double} (h : (x + y).isFinite = true) :
    x.isFinite = true ∧ y.isFinite = true := by
  change (add x y).isFinite = true at h
  simp only [add] at h
  split_ifs at h with h1 h2 h3 h4
  · simp [isFinite_propagateNaN h1] at h
  · exact absurd h (by decide)
  · simp [isFinite_eq_false_of_isInf h2] at h
  · simp [isFinite_eq_false_of_isInf h4] at h
  all_goals
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1
    exact ⟨isFinite_of_isInf_eq_false h1.1 (by simpa using h2),
      isFinite_of_isInf_eq_false h1.2 (by simpa using h4)⟩

theorem isFinite_and_of_isFinite_mul {x y : Double} (h : (x * y).isFinite = true) :
    x.isFinite = true ∧ y.isFinite = true := by
  change (mul x y).isFinite = true at h
  simp only [mul] at h
  split_ifs at h with h1 h2 h3 h4
  · simp [isFinite_propagateNaN h1] at h
  all_goals try exact absurd h (by decide)
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h1 h2
  exact ⟨isFinite_of_isInf_eq_false h1.1 h2.1, isFinite_of_isInf_eq_false h1.2 h2.2⟩

theorem isFinite_and_of_isFinite_sub {x y : Double} (h : (x - y).isFinite = true) :
    x.isFinite = true ∧ y.isFinite = true := by
  by_cases hn : (x.isNaN || y.isNaN) = true
  · change (sub x y).isFinite = true at h
    simp [sub, hn, isFinite_propagateNaN hn] at h
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
  rw [sub_eq_add_neg hn.1 hn.2] at h
  exact ⟨(isFinite_and_of_isFinite_add h).1,
    (isFinite_neg y).symm.trans (isFinite_and_of_isFinite_add h).2⟩

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

/-- A finite sum of doubles, added up from `s` in order, has a finite start and finite terms. -/
theorem isFinite_of_isFinite_foldl_add {β : Type*} {T : β → Double} {L : List β} {s : Double}
    (h : (L.foldl (fun s t ↦ s + T t) s).isFinite = true) :
    s.isFinite = true ∧ ∀ t ∈ L, (T t).isFinite = true := by
  induction L generalizing s with
  | nil => exact ⟨h, fun _ ht ↦ absurd ht List.not_mem_nil⟩
  | cons t L ih =>
    obtain ⟨h1, h2⟩ := ih h
    obtain ⟨h3, h4⟩ := isFinite_and_of_isFinite_add h1
    exact ⟨h3, fun t' ht' ↦ (List.mem_cons.mp ht').elim (fun e ↦ e ▸ h4) (h2 t')⟩

/-! ### Roundings on a grid -/

/-- `x` is a finite double within `|v| / 2 ^ 53` of the rational number `v`, on the grid
`2 ^ (-k) ℤ`: a rounding to nearest of a `v` on that grid, without the error of the subnormal
range (`JPoints.Double.isGridRounding_ofDyadic`). -/
structure IsGridRounding (x : Double) (v : ℚ) (k : ℕ) : Prop where
  /-- The rounding is finite. -/
  isFinite : x.isFinite = true
  /-- The rounding lies within `|v| / 2 ^ 53` of `v`. -/
  abs_sub_le : |x.toRat - v| ≤ |v| / 2 ^ 53
  /-- The rounding lies on the grid. -/
  onGrid : OnGrid k x.toRat

theorem onGrid_toRat (x : Double) : OnGrid 1074 x.toRat := by
  rw [toRat_eq]
  exact .intCast_mul_zpow _ (by have := (toDyadic_bounds x).2.1; push_cast; lia)

/-- A double of absolute value at least `2 ^ (-j)` lies on the grid `2 ^ (-(j + 52)) ℤ`: the last
place of its significand is at least `2 ^ (-(j + 52))`. -/
theorem onGrid_toRat_of_le {x : Double} {j : ℕ} (h : 1 / 2 ^ j ≤ |x.toRat|) :
    OnGrid (j + 52) x.toRat := by
  obtain ⟨hm, -, -⟩ := toDyadic_bounds x
  rw [toRat_eq]
  refine .intCast_mul_zpow _ ?_
  by_contra! he
  have h1 : |x.toRat| < 2 ^ (53 + x.toDyadic.2) := by
    rw [abs_toRat, zpow_add₀ two_ne_zero, zpow_ofNat]
    exact mul_lt_mul_of_pos_right (mod_cast hm) (by positivity)
  have h2 : (2 : ℚ) ^ (53 + x.toDyadic.2) ≤ 1 / 2 ^ j := by
    rw [one_div, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ one_le_two (by push_cast at he ⊢; lia)
  linarith

-- The rounding of `JPoints.Double.ofDyadic` of `V = m 2 ^ e > 0` on the grid `2 ^ (-k) ℤ` to the
-- significand `M` with the last place `2 ^ q`, `q > -k`: within `V / 2 ^ 53`, on the grid.
private theorem abs_sub_le_and_onGrid_of_lt {M : ℕ} {q : ℤ} {k : ℕ} {V : ℚ} (hk : k ≤ 1074)
    (hqk : -(k : ℤ) < q) (hlo : M * 2 ^ q - 2 ^ (q - 1) ≤ V) (hhi : V ≤ M * 2 ^ q + 2 ^ (q - 1))
    (hnorm : -1074 < q → 2 ^ (q + 52) ≤ V) :
    |(M : ℚ) * 2 ^ q - V| ≤ V / 2 ^ 53 ∧ OnGrid k ((M : ℚ) * 2 ^ q) := by
  have h : (2 : ℚ) ^ (q - 1) = 2 ^ (q + 52) / 2 ^ 53 := by
    rw [← zpow_natCast, ← zpow_sub₀ two_ne_zero]; ring_nf
  have := div_le_div_of_nonneg_right (hnorm (by lia)) (by positivity : (0 : ℚ) ≤ 2 ^ 53)
  refine ⟨abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩, ?_⟩
  exact_mod_cast OnGrid.intCast_mul_zpow M hqk.le

-- The rounding of `V = m 2 ^ e > 0` on the grid `2 ^ (-k) ℤ` to the significand `M` with the last
-- place `2 ^ q`, `q ≤ -k`: exact, since `V` lies on the grid of the last place.
private theorem natCast_mul_zpow_eq_of_le {M : ℕ} {q : ℤ} {k : ℕ} {V : ℚ} (hg : OnGrid k V)
    (hqk : q ≤ -(k : ℤ)) (hlo : M * 2 ^ q - 2 ^ (q - 1) ≤ V) (hhi : V ≤ M * 2 ^ q + 2 ^ (q - 1)) :
    (M : ℚ) * 2 ^ q = V := by
  have hj : ((-q).toNat : ℤ) = -q := Int.toNat_of_nonneg (by lia)
  have hM : OnGrid (-q).toNat ((M : ℤ) * 2 ^ q) := OnGrid.intCast_mul_zpow M (by lia)
  push_cast at hM
  refine OnGrid.eq_of_abs_sub_lt hM (hg.mono (by lia)) ?_
  have h1 : (2 : ℚ) ^ (q - 1) < 2 ^ q := zpow_lt_zpow_right₀ one_lt_two (by lia)
  have h2 : (1 : ℚ) / 2 ^ (-q).toNat = 2 ^ q := by
    rw [one_div, ← zpow_natCast, hj, zpow_neg, inv_inv]
  rw [h2]
  exact (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩).trans_lt h1

-- `JPoints.Double.ofDyadic` on the grid: the bound and the grid of
-- `JPoints.Double.isGridRounding_ofDyadic`.
private theorem abs_toRat_ofDyadic_sub_le_and_onGrid {neg : Bool} {m : ℕ} {e : ℤ} {k : ℕ}
    (hk : k ≤ 1074) (hg : OnGrid k ((if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)))
    (hf : (ofDyadic neg m e).isFinite = true) :
    |(ofDyadic neg m e).toRat - (if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)| ≤
        |(if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)| / 2 ^ 53 ∧
      OnGrid k (ofDyadic neg m e).toRat := by
  have habs : |(if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)| = m * 2 ^ e := by
    rw [abs_mul, abs_ite_neg_one_one, one_mul, abs_of_nonneg (by positivity)]
  have hV : OnGrid k ((m : ℚ) * 2 ^ e) := habs ▸ hg.abs
  by_cases hm : m = 0
  · subst hm
    have h0 : (ofDyadic neg 0 e).toRat = 0 := by rw [ofDyadic_zero]; cases neg <;> decide +kernel
    simp [h0, OnGrid.zero]
  obtain ⟨hM, hq, hlo, hhi, hnorm⟩ := ofDyadic_rounding hm e
  rw [ofDyadic_eq e hm] at hf ⊢
  have hsub (h : _ < 2 ^ 52) := eq_of_lt_of_two_zpow_le h hhi hnorm hq
  rw [toRat_ofSignificand hM hq hsub hf, habs, ← mul_sub, abs_mul, abs_ite_neg_one_one, one_mul]
  rcases le_or_gt (max ((m.log2 : ℤ) + e - 52) (-1074)) (-(k : ℤ)) with hqk | hqk
  · rw [natCast_mul_zpow_eq_of_le hV hqk hlo hhi, sub_self, abs_zero]
    exact ⟨by positivity, hV.ite_mul neg⟩
  · obtain ⟨h1, h2⟩ := abs_sub_le_and_onGrid_of_lt hk hqk hlo hhi hnorm
    exact ⟨h1, h2.ite_mul neg⟩

/-- `JPoints.Double.ofDyadic` rounds `±m 2 ^ e` on the grid `2 ^ (-k) ℤ`, `k ≤ 1074`, within
`m 2 ^ e / 2 ^ 53`, to a double on the grid: either the last place of the result is at most the
spacing of the grid, and the rounding is exact, or it is coarser, the result normal. -/
theorem isGridRounding_ofDyadic {neg : Bool} {m : ℕ} {e : ℤ} {k : ℕ} (hk : k ≤ 1074)
    (hg : OnGrid k ((if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)))
    (hf : (ofDyadic neg m e).isFinite = true) :
    (ofDyadic neg m e).IsGridRounding ((if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)) k :=
  ⟨hf, (abs_toRat_ofDyadic_sub_le_and_onGrid hk hg hf).1,
    (abs_toRat_ofDyadic_sub_le_and_onGrid hk hg hf).2⟩

section Operations

variable {x y : Double} {k l : ℕ}

theorem isGridRounding_add (hgx : OnGrid k x.toRat) (hgy : OnGrid k y.toRat) (hk : k ≤ 1074)
    (hf : (x + y).isFinite = true) : (x + y).IsGridRounding (x.toRat + y.toRat) k := by
  obtain ⟨hx, hy⟩ := isFinite_and_of_isFinite_add hf
  obtain ⟨neg, m, e, h, hv⟩ := exists_add_eq_ofDyadic hx hy
  rw [h] at hf ⊢
  rw [← hv]
  exact isGridRounding_ofDyadic hk (by rw [hv]; exact hgx.add hgy) hf

theorem isGridRounding_sub (hgx : OnGrid k x.toRat) (hgy : OnGrid k y.toRat) (hk : k ≤ 1074)
    (hf : (x - y).isFinite = true) : (x - y).IsGridRounding (x.toRat - y.toRat) k := by
  obtain ⟨hx, hy⟩ := isFinite_and_of_isFinite_sub hf
  rw [sub_eq_add_neg (isNaN_eq_false_of_isFinite hx) (isNaN_eq_false_of_isFinite hy)] at hf ⊢
  rw [_root_.sub_eq_add_neg, ← toRat_neg]
  exact isGridRounding_add hgx (toRat_neg y ▸ hgy.neg) hk hf

theorem isGridRounding_mul (hgx : OnGrid k x.toRat) (hgy : OnGrid l y.toRat) (hkl : k + l ≤ 1074)
    (hf : (x * y).isFinite = true) : (x * y).IsGridRounding (x.toRat * y.toRat) (k + l) := by
  obtain ⟨hx, hy⟩ := isFinite_and_of_isFinite_mul hf
  have hv := ite_bne_mul_natAbs_mul_zpow x y
  rw [mul_eq_ofDyadic hx hy] at hf ⊢
  rw [← hv]
  exact isGridRounding_ofDyadic hkl (by rw [hv]; exact hgx.mul hgy) hf

theorem isGridRounding_ofInt {n : ℤ} (hf : (ofInt n).isFinite = true) :
    (ofInt n).IsGridRounding n 0 := by
  have h := ite_mul_natAbs (s := n) (b := decide (n < 0)) (fun _ ↦ rfl) (2 ^ (0 : ℤ))
  have := isGridRounding_ofDyadic (neg := decide (n < 0)) (m := n.natAbs) (e := 0) (k := 0)
    (by norm_num) (by rw [h, zpow_zero, mul_one]; exact .intCast n) hf
  rwa [h, zpow_zero, mul_one] at this

end Operations

/-! ### Products and quotients -/

/-- A finite product of doubles `x ≥ 0` on the grid `ℤ` and `y ≥ 0` is at least
`(1 - 2 ^ (-53)) x y`: a rounding on the grid of the doubles. -/
theorem one_sub_mul_le_toRat_mul {x y : Double} (hgx : OnGrid 0 x.toRat)
    (hf : (x * y).isFinite = true) (hx0 : 0 ≤ x.toRat) (hy0 : 0 ≤ y.toRat) :
    (1 - 1 / 2 ^ 53) * (x.toRat * y.toRat) ≤ (x * y).toRat := by
  have hd := isGridRounding_mul (k := 0) (l := 1074) hgx (onGrid_toRat _) (by norm_num) hf
  have hd' := (abs_le.mp hd.abs_sub_le).1
  rw [abs_of_nonneg (mul_nonneg hx0 hy0)] at hd'
  linarith

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

/-! ### Approximations -/

/-- The double `x` approximates the rational number `v`, with the majorant `a ≥ |v|`, to within
`n` roundings, on the grid `2 ^ (-k) ℤ`: finite, and within `((1 + 2 ^ (-53)) ^ n - 1) a` of `v`.
A rounding to nearest multiplies by a factor within `2 ^ (-53)` of `1`, so that a computation
whose every path to its result passes through at most `n` roundings, of values whose majorants
add up along the computation as the exact values do, meets this bound
(`JPoints.Double.Approx.add`, `JPoints.Double.Approx.mul`); the grid keeps the products out of the
error of the subnormal range. -/
structure Approx (x : Double) (v a : ℚ) (n k : ℕ) : Prop where
  /-- The double is finite. -/
  isFinite : x.isFinite = true
  /-- The majorant bounds the value. -/
  abs_le : |v| ≤ a
  /-- The error after `n` roundings. -/
  abs_sub_le : |x.toRat - v| ≤ ((1 + 1 / 2 ^ 53) ^ n - 1) * a
  /-- The double lies on the grid. -/
  onGrid : OnGrid k x.toRat

namespace Approx

variable {x y : Double} {v w a b : ℚ} {n m k l : ℕ}

theorem nonneg (h : x.Approx v a n k) : 0 ≤ a := (abs_nonneg v).trans h.abs_le

private theorem one_le_pow (n : ℕ) : (1 : ℚ) ≤ (1 + 1 / 2 ^ 53) ^ n :=
  one_le_pow₀ (by norm_num)

theorem abs_toRat_le (h : x.Approx v a n k) : |x.toRat| ≤ (1 + 1 / 2 ^ 53) ^ n * a := by
  have := abs_sub_abs_le_abs_sub x.toRat v
  linarith [h.abs_sub_le, h.abs_le]

theorem of_toRat_eq (hx : x.isFinite = true) (h : x.toRat = v) (hg : OnGrid k v) :
    x.Approx v |v| 0 k :=
  ⟨hx, le_rfl, by simp [h], h ▸ hg⟩

theorem mono (h : x.Approx v a n k) {a' : ℚ} {n' k' : ℕ} (ha : a ≤ a') (hn : n ≤ n')
    (hk : k ≤ k') : x.Approx v a' n' k' := by
  refine ⟨h.isFinite, h.abs_le.trans ha, h.abs_sub_le.trans ?_, h.onGrid.mono hk⟩
  have h1 := one_add_pow_le_one_add_pow (n := n) hn
  have h2 := one_le_pow n
  have h3 := h.nonneg
  nlinarith

theorem neg (h : x.Approx v a n k) : (-x).Approx (-v) a n k := by
  have e : (-x).toRat = -x.toRat := toRat_neg x
  refine ⟨(isFinite_neg x).trans h.isFinite, by rw [abs_neg]; exact h.abs_le, ?_, ?_⟩
  · rw [e, ← neg_sub', abs_neg]; exact h.abs_sub_le
  · rw [e]; exact h.onGrid.neg

theorem fabs (h : x.Approx v a n k) : x.fabs.Approx |v| a n k := by
  refine ⟨(isFinite_fabs x).trans h.isFinite, by rw [abs_abs]; exact h.abs_le, ?_, ?_⟩
  · rw [toRat_fabs]; exact (abs_abs_sub_abs_le_abs_sub _ _).trans h.abs_sub_le
  · rw [toRat_fabs]; exact h.onGrid.abs

-- One rounding `r` of `S` within `|S| / 2 ^ 53`, for `S` within `(ρ - 1) A` of `V` and
-- `|S| ≤ ρ A`, is within `(ρ (1 + 2 ^ (-53)) - 1) A` of `V`.
private theorem abs_sub_le_of_round {r S V A ρ : ℚ} (h1 : |r - S| ≤ |S| / 2 ^ 53)
    (h2 : |S - V| ≤ (ρ - 1) * A) (h3 : |S| ≤ ρ * A) :
    |r - V| ≤ (ρ * (1 + 1 / 2 ^ 53) - 1) * A := by
  have h4 := _root_.abs_sub_le r S V
  have h5 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℚ) ≤ 2 ^ 53)
  linarith

-- The exact sum of two approximations, within the larger of their factors.
private theorem abs_toRat_add_toRat_le (hx : x.Approx v a n k) (hy : y.Approx w b m k) :
    |x.toRat + y.toRat| ≤ (1 + 1 / 2 ^ 53) ^ max n m * (a + b) := by
  nlinarith [abs_add_le x.toRat y.toRat, hx.abs_toRat_le, hy.abs_toRat_le, hx.nonneg, hy.nonneg,
    one_add_pow_le_one_add_pow (le_max_left n m), one_add_pow_le_one_add_pow (le_max_right n m)]

theorem add (hx : x.Approx v a n k) (hy : y.Approx w b m k) (hk : k ≤ 1074)
    (hf : (x + y).isFinite = true) : (x + y).Approx (v + w) (a + b) (max n m + 1) k := by
  have hr := isGridRounding_add hx.onGrid hy.onGrid hk hf
  refine ⟨hf, (abs_add_le v w).trans (add_le_add hx.abs_le hy.abs_le), ?_, hr.onGrid⟩
  have p1 := one_add_pow_le_one_add_pow (le_max_left n m)
  have p2 := one_add_pow_le_one_add_pow (le_max_right n m)
  have ha := hx.nonneg
  have hb := hy.nonneg
  have h1 := abs_toRat_add_toRat_le hx hy
  have h2 : |x.toRat + y.toRat - (v + w)| ≤ ((1 + 1 / 2 ^ 53) ^ max n m - 1) * (a + b) := by
    rw [add_sub_add_comm]
    nlinarith [abs_add_le (x.toRat - v) (y.toRat - w), hx.abs_sub_le, hy.abs_sub_le]
  rw [pow_succ]
  exact abs_sub_le_of_round hr.abs_sub_le h2 h1

-- The exact product of two approximations, within the product of their factors.
private theorem abs_toRat_mul_toRat_le (hx : x.Approx v a n k) (hy : y.Approx w b m l) :
    |x.toRat * y.toRat| ≤ (1 + 1 / 2 ^ 53) ^ (n + m) * (a * b) := by
  rw [abs_mul, pow_add, mul_mul_mul_comm]
  exact mul_le_mul hx.abs_toRat_le hy.abs_toRat_le (abs_nonneg _)
    (mul_nonneg (by positivity) hx.nonneg)

-- The error of the exact product of two approximations, `x (y - w) + (x - v) w`.
private theorem abs_toRat_mul_toRat_sub_le (hx : x.Approx v a n k) (hy : y.Approx w b m l) :
    |x.toRat * y.toRat - v * w| ≤ ((1 + 1 / 2 ^ 53) ^ (n + m) - 1) * (a * b) := by
  have q1 : |x.toRat * (y.toRat - w)| ≤
      (1 + 1 / 2 ^ 53) ^ n * a * (((1 + 1 / 2 ^ 53) ^ m - 1) * b) := by
    rw [abs_mul]
    exact mul_le_mul hx.abs_toRat_le hy.abs_sub_le (abs_nonneg _)
      (mul_nonneg (by positivity) hx.nonneg)
  have q2 : |(x.toRat - v) * w| ≤ ((1 + 1 / 2 ^ 53) ^ n - 1) * a * b := by
    rw [abs_mul]
    exact mul_le_mul hx.abs_sub_le hy.abs_le (abs_nonneg _)
      (mul_nonneg (sub_nonneg.mpr (one_le_pow n)) hx.nonneg)
  rw [pow_add, show x.toRat * y.toRat - v * w = x.toRat * (y.toRat - w) + (x.toRat - v) * w by
    ring]
  nlinarith [abs_add_le (x.toRat * (y.toRat - w)) ((x.toRat - v) * w)]

theorem mul (hx : x.Approx v a n k) (hy : y.Approx w b m l) (hkl : k + l ≤ 1074)
    (hf : (x * y).isFinite = true) : (x * y).Approx (v * w) (a * b) (n + m + 1) (k + l) := by
  have hr := isGridRounding_mul hx.onGrid hy.onGrid hkl hf
  refine ⟨hf, by rw [abs_mul]; exact mul_le_mul hx.abs_le hy.abs_le (abs_nonneg _) hx.nonneg, ?_,
    hr.onGrid⟩
  rw [pow_succ]
  exact abs_sub_le_of_round hr.abs_sub_le (abs_toRat_mul_toRat_sub_le hx hy)
    (abs_toRat_mul_toRat_le hx hy)

theorem add_of_lt (hx : x.Approx v a n k) (hy : y.Approx w b m k) (hk : k ≤ 1074)
    (hlt : (1 + 1 / 2 ^ 53) ^ max n m * (a + b) < 2 ^ 1022) :
    (x + y).Approx (v + w) (a + b) (max n m + 1) k :=
  hx.add hy hk ((isRounding_add hx.isFinite hy.isFinite).isFinite_of_abs_lt
    ((abs_toRat_add_toRat_le hx hy).trans_lt hlt))

theorem sub_of_lt (hx : x.Approx v a n k) (hy : y.Approx w b m k) (hk : k ≤ 1074)
    (hlt : (1 + 1 / 2 ^ 53) ^ max n m * (a + b) < 2 ^ 1022) :
    (x - y).Approx (v - w) (a + b) (max n m + 1) k := by
  rw [sub_eq_add_neg (isNaN_eq_false_of_isFinite hx.isFinite)
    (isNaN_eq_false_of_isFinite hy.isFinite), _root_.sub_eq_add_neg]
  exact hx.add_of_lt hy.neg hk hlt

theorem mul_of_lt (hx : x.Approx v a n k) (hy : y.Approx w b m l) (hkl : k + l ≤ 1074)
    (hlt : (1 + 1 / 2 ^ 53) ^ (n + m) * (a * b) < 2 ^ 1022) :
    (x * y).Approx (v * w) (a * b) (n + m + 1) (k + l) :=
  hx.mul hy hkl ((isRounding_mul hx.isFinite hy.isFinite).isFinite_of_abs_lt
    ((abs_toRat_mul_toRat_le hx hy).trans_lt hlt))

/-- The lower bound of an approximation of a nonnegative value by itself as its majorant, as for
sums of absolute values. -/
theorem two_sub_pow_mul_le_toRat (h : x.Approx a a n k) :
    (2 - (1 + 1 / 2 ^ 53) ^ n) * a ≤ x.toRat := by
  have := (abs_sub_le_iff.mp h.abs_sub_le).2
  linarith

/-- A double that approximates `v` with `v` as its majorant within at most `2 ^ 20` roundings is at
least `v / 2`: its error is far below `v`. -/
theorem div_two_le_toRat (h : x.Approx v v n k) (hn : n ≤ 2 ^ 20) : v / 2 ≤ x.toRat := by
  have h1 := h.two_sub_pow_mul_le_toRat
  have h2 := one_add_pow_sub_one_le hn
  have h3 : (n : ℚ) ≤ 2 ^ 20 := mod_cast hn
  have h4 := h.nonneg
  nlinarith

/-- A double that approximates a positive `v` with `v` as its majorant within at most `2 ^ 20`
roundings is positive. -/
theorem toRat_pos (h : x.Approx v v n k) (hv : 0 < v) (hn : n ≤ 2 ^ 20) : 0 < x.toRat :=
  (half_pos hv).trans_le (h.div_two_le_toRat hn)

/-- A double that approximates a positive `v` with `v` as its majorant within at most `2 ^ 20`
roundings is not a zero. -/
theorem isZero_eq_false (h : x.Approx v v n k) (hv : 0 < v) (hn : n ≤ 2 ^ 20) :
    x.isZero = false :=
  isZero_eq_false_iff.mpr (h.toRat_pos hv hn).ne'

/-- An approximation within less than the spacing of its grid is exact. -/
theorem exact (h : x.Approx v a n k) (hv : OnGrid k v)
    (hlt : ((1 + 1 / 2 ^ 53) ^ n - 1) * a < 1 / 2 ^ k) : x.Approx v |v| 0 k :=
  .of_toRat_eq h.isFinite (h.onGrid.eq_of_abs_sub_lt hv (h.abs_sub_le.trans_lt hlt)) hv

theorem toRat_eq_of_zero (h : x.Approx v a 0 k) :
    x.toRat = v := by
  have := h.abs_sub_le
  rwa [pow_zero, sub_self, zero_mul, abs_nonpos_iff, sub_eq_zero] at this

theorem onGrid_of_zero (h : x.Approx v a 0 k) :
    OnGrid k v :=
  h.toRat_eq_of_zero ▸ h.onGrid

/-- The products `y x ⋯ x` of `j` factors `x` after `y`, by repeated products, approximate
`w X ^ j` within `j` roundings more than `y`, when every partial product stays below `2 ^ 1022`
by the margin of its count. -/
theorem iterate_mul {X B : ℚ} {g gx : ℕ} (hy : y.Approx w b n g) (hx : x.Approx X B 0 gx) (j : ℕ)
    (hB : ∀ i ≤ j, (1 + 1 / 2 ^ 53) ^ (n + i) * (b * B ^ i) < 2 ^ 1022)
    (hg : g + j * gx ≤ 1074) :
    ((· * x)^[j] y).Approx (w * X ^ j) (b * B ^ j) (n + j) (g + j * gx) := by
  induction j with
  | zero => simpa using hy
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_succ, ← mul_assoc, ← mul_assoc]
    have hb : (1 + 1 / 2 ^ 53 : ℚ) ^ (n + j + 0) * (b * B ^ j * B) ≤
        (1 + 1 / 2 ^ 53) ^ (n + (j + 1)) * (b * B ^ (j + 1)) := by
      rw [mul_assoc b, ← pow_succ]
      exact mul_le_mul_of_nonneg_right (one_add_pow_le_one_add_pow (by lia))
        (mul_nonneg hy.nonneg (pow_nonneg hx.nonneg _))
    have h := (ih (fun i hi ↦ hB i (by lia)) (by lia [Nat.succ_mul j gx])).mul_of_lt hx
      (by lia [Nat.succ_mul j gx]) (hb.trans_lt (hB (j + 1) le_rfl))
    exact h.mono le_rfl (by lia) (by lia [Nat.succ_mul j gx])

/-- A finite sum of doubles, added up from `s` in order, approximates the sum of the values with
the sum of the majorants, within the larger of the counts of the start and of the terms plus one
rounding for each term. -/
theorem foldl_add {β : Type*} {T : β → Double} {L : List β} {tv ta : β → ℚ} {s : Double}
    {sv sa : ℚ} {n C g : ℕ}
    (hs : s.Approx sv sa n g)
    (hT : ∀ t ∈ L, (T t).isFinite = true → (T t).Approx (tv t) (ta t) C g) (hg : g ≤ 1074)
    (hf : (L.foldl (fun s t ↦ s + T t) s).isFinite = true) :
    (L.foldl (fun s t ↦ s + T t) s).Approx (sv + (L.map tv).sum) (sa + (L.map ta).sum)
      (max n C + L.length) g := by
  induction L generalizing s sv sa n with
  | nil => simpa using hs.mono le_rfl (le_max_left n C) le_rfl
  | cons t L ih =>
    rw [List.foldl_cons] at hf ⊢
    have h1 := (isFinite_of_isFinite_foldl_add hf).1
    have h2 := hs.add (hT t List.mem_cons_self (isFinite_and_of_isFinite_add h1).2) hg h1
    have := ih h2 (fun t' ht' ↦ hT t' (List.mem_cons_of_mem _ ht')) hf
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.length_cons,
      ← add_assoc, ← add_assoc]
    exact this.mono le_rfl (by lia) le_rfl

end Approx

theorem approx_ofInt {z : ℤ} (h : |z| < 2 ^ 53) : (ofInt z).Approx z |(z : ℚ)| 0 0 :=
  .of_toRat_eq (isFinite_ofInt_and_toRat h).1 (isFinite_ofInt_and_toRat h).2 (.intCast z)

theorem approx_ofInt_of_lt {z : ℤ} (h : |(z : ℚ)| < 2 ^ 1022) :
    (ofInt z).Approx z |(z : ℚ)| 1 0 := by
  have hr := isGridRounding_ofInt ((isRounding_ofInt z).isFinite_of_abs_lt h)
  refine ⟨hr.isFinite, le_rfl, hr.abs_sub_le.trans (le_of_eq ?_), hr.onGrid⟩
  ring

theorem abs_lt_of_isFinite_mpzGetD {z : ℤ} (hf : (mpzGetD z).isFinite = true) :
    |(z : ℚ)| < 2 ^ 1024 := by
  by_contra! h
  have hz : z.natAbs ≠ 0 := by
    intro h0
    rw [Int.natAbs_eq_zero.mp h0, Int.cast_zero, abs_zero] at h
    exact absurd h (not_le.mpr (by positivity))
  have hE : 1024 ≤ ratioExponent z.natAbs 1 := by
    have h2 := (ratioExponent_bounds hz one_ne_zero).2
    rw [Nat.cast_one, div_one, Nat.cast_natAbs, Int.cast_abs] at h2
    have := h.trans_lt h2
    rw [← zpow_natCast, zpow_lt_zpow_iff_right₀ one_lt_two] at this
    push_cast at this
    lia
  rw [mpzGetD, ofRatioTrunc_eq 1 hz, ite_eq_left hE] at hf
  split_ifs at hf <;> simp [isFinite, expField, huge, neg] at hf

/-- `mpz_get_d` of an integer `z`, when finite, approximates `z` within two roundings: it truncates
to less than `2 ^ (-52)` relative, and its value, at least `1 / 2` for `z ≠ 0`, lies on the grid
`2 ^ (-53) ℤ`. -/
theorem approx_mpzGetD {z : ℤ} (hf : (mpzGetD z).isFinite = true) :
    (mpzGetD z).Approx z |(z : ℚ)| 2 53 := by
  have h := isFinite_and_abs_toRat_ofRatioTrunc_sub_le (decide (z < 0)) z.natAbs one_ne_zero
    (by rw [Nat.cast_one, div_one, Nat.cast_natAbs, Int.cast_abs]
        exact abs_lt_of_isFinite_mpzGetD hf)
  have e : (if decide (z < 0) then -1 else 1) * (z.natAbs : ℚ) = z := by
    simpa using ite_mul_natAbs (s := z) (b := decide (z < 0)) (fun _ ↦ rfl) 1
  rw [Nat.cast_one, div_one, e, Nat.cast_natAbs, Int.cast_abs] at h
  replace h : |(mpzGetD z).toRat - z| ≤ |(z : ℚ)| / 2 ^ 52 + 2 ^ (-1074 : ℤ) := h.2
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : (mpzGetD 0).toRat = 0 := by
      rw [mpzGetD, Int.natAbs_zero, ofRatioTrunc_zero, toRat_zero]
    exact ⟨hf, by simp, by simp [h0], by rw [h0]; exact .zero 53⟩
  have h1 : (1 : ℚ) ≤ |(z : ℚ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
  have h2 : (2 : ℚ) ^ (-1074 : ℤ) ≤ 2 / 2 ^ 200 := by
    rw [show (-1074 : ℤ) = 1 + -1075 by norm_num, zpow_add₀ two_ne_zero]
    linarith [two_zpow_neg_1075_le]
  refine ⟨hf, le_rfl, h.trans ?_, onGrid_toRat_of_le (j := 1) ?_⟩
  · nlinarith
  · have := abs_sub_abs_le_abs_sub (z : ℚ) (mpzGetD z).toRat
    rw [abs_sub_comm] at this
    linarith

theorem approx_half : (0.5 : Double).Approx (1 / 2) (1 / 2) 0 1 := by
  have := Approx.of_toRat_eq isFinite_half toRat_half (k := 1) ⟨1, by norm_num⟩
  rwa [abs_of_pos (by norm_num)] at this

theorem approx_thirtyTwo : (32.0 : Double).Approx 32 32 0 0 := by
  have := Approx.of_toRat_eq isFinite_thirtyTwo (show (32.0 : Double).toRat = 32 by decide +kernel)
    (k := 0) ⟨32, by norm_num⟩
  rwa [abs_of_pos (by norm_num)] at this

theorem approx_add_exact {x y : Double} {v w : ℚ} (hx : x.Approx v |v| 0 1)
    (hy : y.Approx w |w| 0 1) (h : |v| + |w| < 2 ^ 52) : (x + y).Approx (v + w) |v + w| 0 1 :=
  (hx.add_of_lt hy (by norm_num) (one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
    (h.le.trans (pow_le_pow_right₀ one_le_two (by norm_num))))).exact
    (hx.onGrid_of_zero.add hy.onGrid_of_zero) (by norm_num; linarith)

theorem approx_sub_exact {x y : Double} {v w : ℚ} (hx : x.Approx v |v| 0 1)
    (hy : y.Approx w |w| 0 1) (h : |v| + |w| < 2 ^ 52) : (x - y).Approx (v - w) |v - w| 0 1 :=
  (hx.sub_of_lt hy (by norm_num) (one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
    (h.le.trans (pow_le_pow_right₀ one_le_two (by norm_num))))).exact
    (hx.onGrid_of_zero.sub hy.onGrid_of_zero) (by norm_num; linarith)

end Double

end JPoints

end
