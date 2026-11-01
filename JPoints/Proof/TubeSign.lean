/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TubeApprox

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The sign of a polynomial over a cell in doubles

`poly_sign` (`JPoints.polySign`) decides the sign of a polynomial in two variables over a cell
from its coefficients at the centre of the cell, in doubles: a sign when the constant term exceeds
the sum `tube_sum` of the other terms at the corner of the cell plus a margin `e`, and bounds
`lo` and `hi` on the absolute value. When the doubles approximate the exact coefficients `V` of
the polynomial at the centre with the majorants `A` (`JPoints.Double.ApproxCoeffs`) and the margin
covers the rounding errors, relative to the majorants at the corner, `M = ∑ A_{jk} R ^ j S ^ k`
(`JPoints.Double.PolySignSetup`), a sign of `poly_sign` is that of the exact polynomial throughout
the cell (`JPoints.Double.PolySignSetup.mul_pos_eval2`), `hi` bounds its absolute value
(`JPoints.Double.PolySignSetup.abs_eval2_le`) and a positive `lo` bounds it from below
(`JPoints.Double.PolySignSetup.lo_le_abs_eval2`). Over the box `|s| ≤ R`, `|t| ≤ S` a
polynomial lies within the sum of the absolute values of its other terms at the corner of its
constant term (`JPoints.absSum`, `JPoints.abs_eval2_sub_le`).

## Main definitions

* `JPoints.absSum`: the sum of the absolute values of the terms of a polynomial at a corner.
* `JPoints.Double.PolySignSetup`: the setting of a call of `poly_sign`.

## Main statements

* `JPoints.abs_eval2_sub_le`, `JPoints.abs_eval2_sub_le_absSum`: a polynomial over a box.
* `JPoints.Double.PolySignSetup.mul_pos_eval2`, `JPoints.Double.PolySignSetup.abs_eval2_le`,
  `JPoints.Double.PolySignSetup.lo_le_abs_eval2`: the verdict and the bounds of `poly_sign`.

## Implementation notes

The sums of `poly_sign` are sums of finite doubles, which round on the grid `2 ^ (-1074) ℤ` without
the error of the subnormal range; their finiteness comes from the comparisons themselves: a sum
without sign bits that some double is below when subtracted from a finite double is finite
(`JPoints.Double.isFinite_of_lt_sub`), and so are its operands. The arithmetic of the margins is in
units `2 ^ (-53)` of the majorants at the corner: `n + D + |JPoints.evalIndices D| + 3` of them
cover the `n` roundings of the coefficients, those of `tube_sum` and of the sum with `e`.
-/

@[expose] public section

namespace JPoints

open Finset

/-! ### Polynomials over a box -/

/-- The sum of `|f j k| R ^ j S ^ k` over the pairs `j + k ≤ D`: for the coefficients `f j k` of a
polynomial at a centre, a bound on its terms over the box `|s| ≤ R`, `|t| ≤ S` around it, and with
the constant term `|f 0 0|` taken off, a bound on its distance from the constant term
(`JPoints.abs_eval2_sub_le`). -/
def absSum (f : ℕ → ℕ → ℚ) (D : ℕ) (R S : ℚ) : ℚ :=
  ∑ j ∈ range (D + 1), ∑ k ∈ range (D - j + 1), |f j k| * (R ^ j * S ^ k)

theorem sum_map_tail_evalIndices_abs (f : ℕ → ℕ → ℚ) (D : ℕ) (R S : ℚ) :
    ((evalIndices D).tail.map fun jk ↦ |f jk.1 jk.2| * (R ^ jk.1 * S ^ jk.2)).sum =
      absSum f D R S - |f 0 0| := by
  rw [Double.sum_map_tail_evalIndices]
  simp [absSum]

variable {D : ℕ} {R S : ℚ}

theorem abs_le_absSum (f : ℕ → ℕ → ℚ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    |f 0 0| ≤ absSum f D R S := by
  rw [← sub_nonneg, ← sum_map_tail_evalIndices_abs]
  exact List.sum_nonneg fun x hx ↦ by
    obtain ⟨jk, -, rfl⟩ := List.mem_map.mp hx
    positivity

/-- A polynomial with the coefficients `V` at a centre differs over the box `|s| ≤ R`, `|t| ≤ S`
from its constant term by at most the sum of the absolute values of its other terms at the
corner `(R, S)`. -/
theorem abs_eval2_sub_le (V : Array ℚ) {s t : ℚ} (hs : |s| ≤ R) (ht : |t| ≤ S) :
    |eval2 V D s t - V[coeffIndex 0 0]!| ≤
      absSum (fun j k ↦ V[coeffIndex j k]!) D R S - |V[coeffIndex 0 0]!| := by
  have := (abs_nonneg s).trans hs
  have := (abs_nonneg t).trans ht
  have e : eval2 V D s t - V[coeffIndex 0 0]! = ((evalIndices D).tail.map
      fun jk ↦ V[coeffIndex jk.1 jk.2]! * s ^ jk.1 * t ^ jk.2).sum := by
    rw [Double.sum_map_tail_evalIndices, eval2]
    simp
  rw [e, ← sum_map_tail_evalIndices_abs (fun j k ↦ V[coeffIndex j k]!)]
  refine (List.le_sum_of_subadditive _ abs_zero.le abs_add_le _).trans ?_
  rw [List.map_map]
  refine List.sum_le_sum fun jk _ ↦ ?_
  simp only [Function.comp_apply, abs_mul, abs_pow, mul_assoc]
  gcongr

/-- The terms of `f` other than the constant one are bounded, over the box, by those of `g` and of
`g - f`. -/
theorem absSum_sub_abs_le (f g : ℕ → ℕ → ℚ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum f D R S - |f 0 0| ≤ absSum g D R S - |g 0 0| +
      (absSum (fun j k ↦ g j k - f j k) D R S - |g 0 0 - f 0 0|) := by
  rw [← sum_map_tail_evalIndices_abs, ← sum_map_tail_evalIndices_abs,
    ← sum_map_tail_evalIndices_abs, ← List.sum_map_add]
  refine List.sum_le_sum fun jk _ ↦ ?_
  have := abs_sub_abs_le_abs_sub (f jk.1 jk.2) (g jk.1 jk.2)
  rw [abs_sub_comm (f _ _)] at this
  nlinarith [show 0 ≤ R ^ jk.1 * S ^ jk.2 by positivity]

/-- A polynomial with the coefficients `V` over the box `|s| ≤ R`, `|t| ≤ S` lies within `Tx + E` of
the constant term of `f`, for the sum `Tx` of the other terms of `f` at the corner `(R, S)` and the
sum `E` of the differences `f - V` there. -/
theorem abs_eval2_sub_le_absSum (V : Array ℚ) (f : ℕ → ℕ → ℚ) {s t : ℚ} (hs : |s| ≤ R)
    (ht : |t| ≤ S) :
    |eval2 V D s t - f 0 0| ≤ absSum f D R S - |f 0 0| +
      absSum (fun j k ↦ f j k - V[coeffIndex j k]!) D R S := by
  have h1 := abs_eval2_sub_le V (D := D) hs ht
  have h2 := absSum_sub_abs_le (D := D) (fun j k ↦ V[coeffIndex j k]!) f
    ((abs_nonneg s).trans hs) ((abs_nonneg t).trans ht)
  have h3 := abs_sub_le (eval2 V D s t) V[coeffIndex 0 0]! (f 0 0)
  rw [abs_sub_comm V[coeffIndex 0 0]!] at h3
  linarith

namespace Double

variable {q : Array Double} {V A : Array ℚ} {n g : ℕ}

theorem ApproxCoeffs.absSum_sub_le (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum (fun j k ↦ (q[coeffIndex j k]!).toRat - V[coeffIndex j k]!) D R S ≤
      ((1 + 1 / 2 ^ 53) ^ n - 1) * eval2 A D R S := by
  rw [absSum, eval2, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  have hjk : j + k ≤ D := by simp only [mem_range] at hj hk; lia
  calc _ ≤ ((1 + 1 / 2 ^ 53) ^ n - 1) * A[coeffIndex j k]! * (R ^ j * S ^ k) :=
        mul_le_mul_of_nonneg_right (h hjk).abs_sub_le (by positivity)
    _ = _ := by ring

theorem ApproxCoeffs.absSum_le (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S ≤
      (1 + 1 / 2 ^ 53) ^ n * eval2 A D R S := by
  rw [absSum, eval2, mul_sum]
  refine sum_le_sum fun j hj ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  have hjk : j + k ≤ D := by simp only [mem_range] at hj hk; lia
  calc _ ≤ (1 + 1 / 2 ^ 53) ^ n * A[coeffIndex j k]! * (R ^ j * S ^ k) :=
        mul_le_mul_of_nonneg_right (h hjk).abs_toRat_le (by positivity)
    _ = _ := by ring

theorem ApproxCoeffs.eval2_nonneg (h : ApproxCoeffs q V A D n g) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ eval2 A D R S :=
  sum_nonneg fun j hj ↦ sum_nonneg fun k hk ↦ by
    have := (h (j := j) (k := k) (by simp only [mem_range] at hj hk; lia)).nonneg
    positivity

/-! ### `poly_sign` -/

-- The arithmetic of the margin of `poly_sign`: the rounded sum `sd ≥ (1 - u) (T + e)` of the sum
-- `T ≥ (2 - ρ_N) Tx` of the terms and of the margin `e ≥ (n + N + 3 + γ) u M` exceeds the sum `Tx`
-- of the terms of the doubles and their error `E ≤ (ρ_n - 1) M` by `γ u M`, for the factors
-- `ρ_n = (1 + u) ^ n` and `ρ_N` of the roundings, `u = 2 ^ (-53)`.
private theorem le_sub_sub_of_margin {T Tx E M e sd Q ρn ρN : ℚ} {n N γ : ℕ} (hn : n ≤ 2 ^ 10)
    (hN : N ≤ 2 ^ 10) (hγ : γ ≤ 2 ^ 10) (hρn : ρn - 1 ≤ n / 2 ^ 53 * (1 + 1 / 2 ^ 32))
    (hρN : ρN - 1 ≤ N / 2 ^ 53 * (1 + 1 / 2 ^ 32)) (hM : 0 ≤ M) (hTx : 0 ≤ Tx) (hQ : 0 ≤ Q)
    (hT : (2 - ρN) * Tx ≤ T) (hE : E ≤ (ρn - 1) * M) (hq : Tx + Q ≤ ρn * M)
    (hsd : (1 - 1 / 2 ^ 53) * (T + e) ≤ sd) (hm : (n + N + 3 + γ) * M / 2 ^ 53 ≤ e) :
    γ * M / 2 ^ 53 ≤ sd - Tx - E := by
  have hn' : (n : ℚ) ≤ 2 ^ 10 := mod_cast hn
  have hN' : (N : ℚ) ≤ 2 ^ 10 := mod_cast hN
  have hγ' : (γ : ℚ) ≤ 2 ^ 10 := mod_cast hγ
  have p1 := mul_le_mul_of_nonneg_right hρN hTx
  have p2 : Tx ≤ (1 + 1 / 2 ^ 42) * M := by nlinarith
  have p3 := mul_le_mul_of_nonneg_left p2 (Nat.cast_nonneg N)
  have p4 := mul_le_mul_of_nonneg_right hρn hM
  have p7 := mul_le_mul_of_nonneg_right hN' hM
  have p8 := mul_le_mul_of_nonneg_right hn' hM
  have p9 := mul_le_mul_of_nonneg_right hγ' hM
  linarith

-- `x ≤ 2 ^ 20 · 2 ^ 1000` is below `2 ^ 1022`, without the evaluation of the powers.
private theorem lt_two_pow_1022 {x : ℚ} (h : x ≤ 2 ^ 20 * 2 ^ 1000) : x < 2 ^ 1022 :=
  h.trans_lt (by
    rw [show (1022 : ℕ) = 22 + 1000 from rfl, pow_add]
    exact mul_lt_mul_of_pos_right (by norm_num) (by positivity))

/-- What a call `poly_sign(q, D, rp, e)` of the analysis of a cell needs for its verdict to be
sound: the coefficients `q` of degree `D ≤ 4` approximate the exact coefficients `V` of a polynomial
at the centre of the cell with the majorants `A` (`JPoints.Double.ApproxCoeffs`) within `n ≤ 2 ^ 10`
roundings, on the grid `2 ^ (-g) ℤ`; the products `rp` approximate the products `R ^ j S ^ k` of
the half-sizes `R` and `S` of the cell and have no sign bits; the majorants at the corner
`(R, S)`, `M = ∑ A_{jk} R ^ j S ^ k`, are at most `2 ^ 1000`; and the margin `e`, without a sign
bit, is at most `2 ^ 1000` and at least `(n + D + |JPoints.evalIndices D| + 3 + γ) M / 2 ^ 53` when
it is finite, `γ M / 2 ^ 53` of it more than the rounding errors of `q` and of `tube_sum` need. -/
structure PolySignSetup (q : Array Double) (V A : Array ℚ) (D n g : ℕ) (rp : Array Double)
    (R S : ℚ) (e : Double) (γ : ℕ) : Prop where
  /-- The coefficients approximate the exact ones. -/
  approx : ApproxCoeffs q V A D n g
  /-- The degree is at most `4`. -/
  deg_le : D ≤ 4
  /-- The grid and the products of the degree stay within the grid of the doubles. -/
  grid_le : g + D ≤ 1074
  /-- At most `2 ^ 10` roundings. -/
  count_le : n ≤ 2 ^ 10
  /-- The excess of the margin is at most `2 ^ 10` units. -/
  gamma_le : γ ≤ 2 ^ 10
  /-- The products of the half-sizes. -/
  rp_approx {j k : ℕ} (h : j + k ≤ D) :
    (rp[coeffIndex j k]!).Approx (R ^ j * S ^ k) (R ^ j * S ^ k) (j + k) (j + k)
  /-- The products of the half-sizes have no sign bits. -/
  rp_signBit {j k : ℕ} (h : j + k ≤ D) : (rp[coeffIndex j k]!).signBit = false
  /-- The half-size in the first variable. -/
  nonneg_R : 0 ≤ R
  /-- The half-size in the second variable. -/
  nonneg_S : 0 ≤ S
  /-- The majorants at the corner are bounded. -/
  le_pow : eval2 A D R S ≤ 2 ^ 1000
  /-- The margin has no sign bit. -/
  signBit_e : e.signBit = false
  /-- The margin, when finite, covers the errors and is bounded. -/
  margin (h : e.isFinite = true) :
    ((n + D + (evalIndices D).length + 3 + γ : ℕ) : ℚ) * eval2 A D R S / 2 ^ 53 ≤ e.toRat ∧
      e.toRat ≤ 2 ^ 1000

/-- `JPoints.abs_eval2_sub_le_absSum` for the coefficients of the doubles `q`: a polynomial with the
coefficients `V` lies over the box within the other terms of `q` at the corner and the errors of
`q` of the constant term of `q`. -/
theorem abs_eval2_sub_toRat_le (V : Array ℚ) {D : ℕ} {R S s t : ℚ} (hs : |s| ≤ R) (ht : |t| ≤ S) :
    |eval2 V D s t - (q[0]!).toRat| ≤
      absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat| +
        absSum (fun j k ↦ (q[coeffIndex j k]!).toRat - V[coeffIndex j k]!) D R S :=
  abs_eval2_sub_le_absSum V (fun j k ↦ (q[coeffIndex j k]!).toRat) hs ht

theorem fst_polySign_eq {q rp : Array Double} {D : ℕ} {e : Double}
    (hp : (polySign q D rp e).run.1 ≠ 0) :
    (polySign q D rp e).run.1 = 1 ∨ (polySign q D rp e).run.1 = -1 := by
  rw [run_polySign] at hp ⊢
  split_ifs at hp ⊢ <;> simp_all

-- A rational `P` within less than `|Q|` of `Q` has the sign of `Q`.
private theorem sign_mul_pos {P Q : ℚ} (h : |P - Q| < |Q|) :
    0 < (if 0 < Q then 1 else -1 : ℚ) * P := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  split_ifs with hQ
  · rw [abs_of_pos hQ] at h1; linarith
  · rw [abs_of_nonpos (not_lt.mp hQ)] at h2; linarith

namespace PolySignSetup

variable {q rp : Array Double} {V A : Array ℚ} {D n g γ : ℕ} {R S : ℚ} {e : Double}
  (h : PolySignSetup q V A D n g rp R S e γ)
include h

theorem approx_tubeSumGen (hs : (tubeSumGen q D rp).isFinite = true) :
    (tubeSumGen q D rp).Approx
      (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|)
      (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|)
      (D + (evalIndices D).length) (g + D) :=
  Double.approx_tubeSumGen (fun _ _ hjk ↦ ⟨(h.approx hjk).isFinite, (h.approx hjk).onGrid⟩)
    (fun _ _ hjk ↦ h.rp_approx hjk) h.grid_le hs

theorem signBit_tubeSumGen : (tubeSumGen q D rp).signBit = false := by
  refine signBit_foldl_add (by decide) fun jk hjk ↦ ?_
  have hjk' := mem_evalIndices.mp (List.mem_of_mem_tail hjk)
  rw [signBit_mul_of_isFinite (by rw [isFinite_fabs]; exact (h.approx hjk').isFinite)
    (h.rp_approx hjk').isFinite, signBit_fabs, h.rp_signBit hjk']
  rfl

theorem count_le_19 : D + (evalIndices D).length ≤ 19 := by
  have := h.deg_le; interval_cases D <;> decide

theorem approx_zero : (q[0]!).Approx V[0]! A[0]! n g :=
  h.approx (j := 0) (k := 0) (by lia)

theorem abs_toRat_le_absSum :
    |(q[0]!).toRat| ≤ absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S :=
  abs_le_absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) h.nonneg_R h.nonneg_S

/-- The sum `tube_sum(q)`, when finite: within `D + |JPoints.evalIndices D|` roundings of the sum
`Tx` of the terms of `q` other than the constant one at the corner, which with `|q₀|` is at most
`(1 + 2 ^ (-53)) ^ n M`. -/
theorem tubeSumGen_bounds (hT : (tubeSumGen q D rp).isFinite = true) :
    (0 : ℚ) ≤ absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat| ∧
      ((2 : ℚ) - (1 + 1 / 2 ^ 53) ^ (D + (evalIndices D).length)) *
          (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) ≤
        (tubeSumGen q D rp).toRat ∧
      (tubeSumGen q D rp).toRat ≤
        (2 : ℚ) * (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) ∧
      absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S ≤
        (1 + 1 / 2 ^ 53) ^ n * eval2 A D R S := by
  have hTa := h.approx_tubeSumGen hT
  have hTx := h.abs_toRat_le_absSum
  refine ⟨sub_nonneg.mpr hTx, hTa.two_sub_pow_mul_le_toRat, ((le_abs_self _).trans
    hTa.abs_toRat_le).trans (mul_le_mul_of_nonneg_right (one_add_pow_le_two (by
      lia [h.count_le_19])) (sub_nonneg.mpr hTx)), h.approx.absSum_le h.nonneg_R h.nonneg_S⟩

/-- The sum `sd = tube_sum(q) + e` of `poly_sign`, when finite, of a finite `tube_sum(q) ≥ 0` and a
finite margin `e ≥ 0`, within a rounding of their exact sum. -/
theorem sum_bounds (hs : (tubeSumGen q D rp + e).isFinite = true) :
    (1 - 1 / 2 ^ 53) * ((tubeSumGen q D rp).toRat + e.toRat) ≤ (tubeSumGen q D rp + e).toRat ∧
      (tubeSumGen q D rp + e).toRat ≤
        (1 + 1 / 2 ^ 53) * ((tubeSumGen q D rp).toRat + e.toRat) := by
  obtain ⟨hT, he⟩ := isFinite_and_of_isFinite_add hs
  obtain ⟨hTx, hT1, -, -⟩ := h.tubeSumGen_bounds hT
  have hr := (isGridRounding_add (onGrid_toRat _) (onGrid_toRat _) le_rfl hs).abs_sub_le
  have hm0 := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  have he0 : 0 ≤ e.toRat := le_trans (by positivity) (h.margin he).1
  have hT0 : 0 ≤ (tubeSumGen q D rp).toRat := by
    nlinarith [one_add_pow_le_two (n := D + (evalIndices D).length) (by lia [h.count_le_19])]
  rw [abs_of_nonneg (add_nonneg hT0 he0)] at hr
  constructor <;> linarith [abs_le.mp hr]

/-- The sum `sd = tube_sum(q) + e` of `poly_sign`, when finite, exceeds the sum `Tx` of the terms
of `q` other than the constant one over the cell and the error `E` of `q` by `γ M / 2 ^ 53`, and
is at most `8 · 2 ^ 1000`. -/
theorem sub_sub_ge (hs : (tubeSumGen q D rp + e).isFinite = true) :
    e.isFinite = true ∧ (tubeSumGen q D rp + e).toRat ≤ 8 * 2 ^ 1000 ∧
      γ * eval2 A D R S / 2 ^ 53 ≤ (tubeSumGen q D rp + e).toRat -
        (absSum (fun j k ↦ (q[coeffIndex j k]!).toRat) D R S - |(q[0]!).toRat|) -
        absSum (fun j k ↦ (q[coeffIndex j k]!).toRat - V[coeffIndex j k]!) D R S := by
  obtain ⟨hT, he⟩ := isFinite_and_of_isFinite_add hs
  obtain ⟨hm, he2⟩ := h.margin he
  obtain ⟨hTx, hT1, hT2, hq⟩ := h.tubeSumGen_bounds hT
  obtain ⟨hr1, hr2⟩ := h.sum_bounds hs
  have hm0 := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  push_cast at hm
  have t2 := hq.trans (mul_le_mul (one_add_pow_le_two (by lia [h.count_le])) h.le_pow hm0
    (by norm_num))
  have hq0 := abs_nonneg (q[0]!).toRat
  refine ⟨he, by generalize (2 : ℚ) ^ 1000 = B at t2 he2; linarith,
    le_sub_sub_of_margin (T := (tubeSumGen q D rp).toRat) (e := e.toRat) (Q := |(q[0]!).toRat|)
    h.count_le (h.count_le_19.trans (by norm_num)) h.gamma_le
    (one_add_pow_sub_one_le (n := n) (by lia [h.count_le]))
    (one_add_pow_sub_one_le (n := D + (evalIndices D).length) (by lia [h.count_le_19])) hm0 hTx
    hq0 hT1 (h.approx.absSum_sub_le h.nonneg_R h.nonneg_S) (by linarith) hr1
    (by push_cast; linarith)⟩

/-- The bound `lo = |q₀| - sd` of `poly_sign` for a finite sum `sd`: finite, and within a rounding
of `|q₀| - sd`. -/
theorem lo_rounding (hsd : (tubeSumGen q D rp + e).isFinite = true) :
    (q[0]!.fabs - (tubeSumGen q D rp + e)).isFinite = true ∧
      |(q[0]!.fabs - (tubeSumGen q D rp + e)).toRat -
          (|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat)| ≤
        |(|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat)| / 2 ^ 53 := by
  obtain ⟨-, hb, -⟩ := h.sub_sub_ge hsd
  obtain ⟨-, -, -, hq⟩ := h.tubeSumGen_bounds (isFinite_and_of_isFinite_add hsd).1
  have hA := hq.trans (mul_le_mul (one_add_pow_le_two (by lia [h.count_le])) h.le_pow
    (h.approx.eval2_nonneg h.nonneg_R h.nonneg_S) (by norm_num))
  have hT := h.abs_toRat_le_absSum
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hf0 : (q[0]!.fabs).isFinite = true := by rw [isFinite_fabs]; exact h.approx_zero.isFinite
  have hlf := (isRounding_sub hf0 hsd).isFinite_of_abs_lt (lt_two_pow_1022 ((abs_sub _ _).trans
    (by rw [toRat_fabs, abs_abs, abs_of_nonneg hs0]; generalize (2 : ℚ) ^ 1000 = B at hA hb
        linarith)))
  have hr := (isGridRounding_sub (onGrid_toRat _) (onGrid_toRat _) le_rfl hlf).abs_sub_le
  rw [toRat_fabs] at hr
  exact ⟨hlf, hr⟩

/-- The doubles of `poly_sign` that a positive bound `lo = |q₀| - sd` needs: the sum `sd` finite and
below `|q₀|`, `lo` at most `(1 + 2 ^ (-53)) (|q₀| - sd)`, and `lo` finite. -/
theorem lo_facts (hlo : (0.0 : Double).lt (q[0]!.fabs - (tubeSumGen q D rp + e)) = true) :
    (tubeSumGen q D rp + e).isFinite = true ∧ (tubeSumGen q D rp + e).toRat < |(q[0]!).toRat| ∧
      (q[0]!.fabs - (tubeSumGen q D rp + e)).toRat ≤
        (1 + 1 / 2 ^ 53) * (|(q[0]!).toRat| - (tubeSumGen q D rp + e).toRat) ∧
      (q[0]!.fabs - (tubeSumGen q D rp + e)).isFinite = true := by
  have hsd := isFinite_of_lt_sub (by rw [isFinite_fabs]; exact h.approx_zero.isFinite)
    (signBit_add h.signBit_tubeSumGen h.signBit_e) hlo
  obtain ⟨hlf, hr⟩ := h.lo_rounding hsd
  rw [zero_lt_iff_toRat_pos hlf] at hlo
  obtain ⟨-, hr2⟩ := abs_le.mp hr
  have hv : (tubeSumGen q D rp + e).toRat < |(q[0]!).toRat| := by
    by_contra! hv
    rw [abs_of_nonpos (sub_nonpos.mpr hv)] at hr2
    linarith
  refine ⟨hsd, hv, ?_, hlf⟩
  rw [abs_of_pos (sub_pos.mpr hv)] at hr2
  linarith

/-- A nonzero sign of `poly_sign` is the sign throughout the cell of the polynomial with the exact
coefficients `V`, and the margin is then finite. -/
theorem mul_pos_eval2 (hp : (polySign q D rp e).run.1 ≠ 0) :
    e.isFinite = true ∧ ∀ ⦃s t : ℚ⦄, |s| ≤ R → |t| ≤ S →
      0 < ((polySign q D rp e).run.1 : ℚ) * eval2 V D s t := by
  have hM := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
  rw [run_polySign] at hp ⊢
  split_ifs at hp ⊢ with hlo hq
  all_goals try exact absurd rfl hp
  all_goals
    obtain ⟨hsd, hv, -, -⟩ := h.lo_facts hlo
    obtain ⟨he, -, hk⟩ := h.sub_sub_ge hsd
    refine ⟨he, fun s t hs ht ↦ ?_⟩
    have := abs_eval2_sub_toRat_le (q := q) V (D := D) hs ht
    have hγ : 0 ≤ (γ : ℚ) * eval2 A D R S / 2 ^ 53 := by positivity
    have hsign := sign_mul_pos (P := eval2 V D s t) (Q := (q[0]!).toRat) (by linarith)
  · change (0.0 : Double).lt q[0]! = true at hq
    rw [ite_eq_left ((zero_lt_iff_toRat_pos h.approx_zero.isFinite).mp hq)] at hsign
    exact_mod_cast hsign
  · change ¬(0.0 : Double).lt q[0]! = true at hq
    rw [ite_eq_right ((zero_lt_iff_toRat_pos h.approx_zero.isFinite).not.mp hq)] at hsign
    exact_mod_cast hsign

/-- The upper bound `hi` of `poly_sign`, when finite, bounds the polynomial with the exact
coefficients `V` throughout the cell, up to a rounding. -/
theorem abs_eval2_le (hf : (polySign q D rp e).run.2.2.isFinite = true) ⦃s t : ℚ⦄ (hs : |s| ≤ R)
    (ht : |t| ≤ S) :
    (1 - 1 / 2 ^ 53) * |eval2 V D s t| ≤ (polySign q D rp e).run.2.2.toRat := by
  rw [run_polySign] at hf ⊢
  dsimp only at hf ⊢
  obtain ⟨hf0, hsd⟩ := isFinite_and_of_isFinite_add hf
  obtain ⟨-, -, hk⟩ := h.sub_sub_ge hsd
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hr := (isGridRounding_add (onGrid_toRat _) (onGrid_toRat _) le_rfl hf).abs_sub_le
  rw [toRat_fabs, abs_of_nonneg (add_nonneg (abs_nonneg _) hs0)] at hr
  have := abs_eval2_sub_toRat_le (q := q) V (D := D) hs ht
  have hγ : 0 ≤ (γ : ℚ) * eval2 A D R S / 2 ^ 53 := by
    have := h.approx.eval2_nonneg h.nonneg_R h.nonneg_S
    positivity
  have h1 := abs_sub_abs_le_abs_sub (eval2 V D s t) (q[0]!).toRat
  linarith [(abs_le.mp hr).1]

theorem signBit_hi : (polySign q D rp e).run.2.2.signBit = false := by
  rw [run_polySign]
  exact signBit_add (signBit_fabs _) (signBit_add h.signBit_tubeSumGen h.signBit_e)

theorem isFinite_lo (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) :
    (polySign q D rp e).run.2.1.isFinite = true := by
  rw [run_polySign] at hlo ⊢
  exact (h.lo_facts hlo).2.2.2

theorem lo_le_two_mul (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) :
    (polySign q D rp e).run.2.1.toRat ≤ 2 * eval2 A D R S := by
  rw [run_polySign] at hlo ⊢
  dsimp only at hlo ⊢
  obtain ⟨hsd, -, hlo', -⟩ := h.lo_facts hlo
  obtain ⟨-, -, -, hA⟩ := h.tubeSumGen_bounds (isFinite_and_of_isFinite_add hsd).1
  have hT := h.abs_toRat_le_absSum
  have hs0 := toRat_nonneg (signBit_add h.signBit_tubeSumGen h.signBit_e)
  have hρ := one_add_pow_sub_one_le (n := n) (by lia [h.count_le])
  have hn : (n : ℚ) ≤ 2 ^ 10 := mod_cast h.count_le
  have hρM := mul_le_mul_of_nonneg_right (show (1 + 1 / 2 ^ 53 : ℚ) ^ n ≤ 1 + 1 / 2 ^ 42 by
    nlinarith) (h.approx.eval2_nonneg h.nonneg_R h.nonneg_S)
  nlinarith

/-- A positive lower bound `lo` of `poly_sign` bounds the polynomial with the exact coefficients
`V` from below throughout the cell, up to a rounding and with `γ M / 2 ^ 53` to spare. -/
theorem lo_le_abs_eval2 (hlo : (0.0 : Double).lt (polySign q D rp e).run.2.1 = true) ⦃s t : ℚ⦄
    (hs : |s| ≤ R) (ht : |t| ≤ S) :
    (polySign q D rp e).run.2.1.toRat ≤
      (1 + 1 / 2 ^ 53) * (|eval2 V D s t| - γ * eval2 A D R S / 2 ^ 53) := by
  rw [run_polySign] at hlo ⊢
  dsimp only at hlo ⊢
  obtain ⟨hsd, hv, hlo', -⟩ := h.lo_facts hlo
  obtain ⟨-, -, hk⟩ := h.sub_sub_ge hsd
  have := abs_eval2_sub_toRat_le (q := q) V (D := D) hs ht
  have h1 := abs_sub_abs_le_abs_sub (q[0]!).toRat (eval2 V D s t)
  rw [abs_sub_comm (q[0]!).toRat] at h1
  exact hlo'.trans (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))

end PolySignSetup

end Double

end JPoints

end
