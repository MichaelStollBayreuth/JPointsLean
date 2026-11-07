/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.DoubleError

import JPoints.Proof.Containers
import JPoints.Proof.Rounding
import Mathlib.Tactic.Linarith

/-!
# The half-sizes of a cell of the tube in doubles

What the analysis of a cell of the tube (`tube_cell`, `JPoints.tubeCell`) needs of the doubles of
its half-sizes `rb = 0.5 * (double)(b_hi - b_lo)` and `rc = 32.0 * (double)(i_hi - i_lo) - 0.5`,
whose products it caches and whose comparison `!=` decides when it computes them again: `rb` is
never `-0.0` (`JPoints.Double.half_mul_ofInt_ne_negZero`) and has no sign for `b_lo ≤ b_hi`
(`JPoints.Double.signBit_half_mul_ofInt`), and `rc` is never a zero
(`JPoints.Double.isZero_thirtyTwo_mul_ofInt_sub_half`), so that a double that `==` finds equal to
them has their bits (`JPoints.Double.eq_of_beq`, `JPoints.Double.eq_of_beq_of_signBit_eq_false`),
and no double without a sign bit is equal to the sentinel `-1.0`
(`JPoints.Double.beq_neg_one_eq_false`). For `|b_hi - b_lo| < 2 ^ 52` and `|i_hi - i_lo| < 2 ^ 40`
both are exact (`JPoints.Double.approx_half_mul_ofInt`,
`JPoints.Double.approx_thirtyTwo_mul_ofInt_sub_half`).

## Main statements

* `JPoints.Double.beq_neg_one_eq_false`: no double without a sign bit is `-1.0`.
* `JPoints.Double.half_mul_ofInt_ne_negZero`, `JPoints.Double.signBit_half_mul_ofInt`,
  `JPoints.Double.isZero_thirtyTwo_mul_ofInt_sub_half`: the half-sizes of a cell.
* `JPoints.Double.approx_half_mul_ofInt`, `JPoints.Double.approx_thirtyTwo_mul_ofInt_sub_half`:
  the half-sizes as exact doubles.

## Implementation notes

A product `0.5 * (double)d` or `32.0 * (double)w` with `d, w ≠ 0` is no zero, since the rounding
of a dyadic number above the least subnormal is none (`JPoints.Double.isZero_ofDyadic_eq_false`),
and `32.0 * (double)w` is at least `32` in absolute value when finite
(`JPoints.Double.two_pow_le_abs_toRat_ofDyadic`), so that subtracting `0.5` leaves no zero.
-/

@[expose] public section

namespace JPoints

namespace Double

theorem beq_neg_one_eq_false {x : Double} (hx : x.signBit = false) : x.beq (-1.0) = false := by
  by_contra h
  have e := orderValue_eq_of_beq (Bool.not_eq_false _ ▸ h)
  rw [orderValue_eq_mod, hx, show (-1.0 : Double).orderValue = -0x3ff0000000000000 by
    decide +kernel] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  lia

/-- The product of a finite double `c` with the significand `2 ^ 52` and an exponent of at least
`-1126` and a double `y` that is no NaN and, when finite, at least `1` in absolute value (an
infinity included) is not a zero: the exact product is at least `2 ^ (-1074)`, or the product an
infinity. -/
theorem isZero_mul_of_one_le {c y : Double} (hc : c.isFinite = true)
    (hc1 : c.toDyadic.1.natAbs = 2 ^ 52) (hc2 : -1074 ≤ c.toDyadic.2 + 52)
    (hyn : y.isNaN = false) (hy : y.isFinite = true → 1 ≤ |y.toRat|) : (c * y).isZero = false := by
  have hc0 : c.toRat ≠ 0 := by
    rw [← abs_ne_zero, abs_toRat, hc1]
    exact mul_ne_zero (by norm_num) (zpow_ne_zero _ two_ne_zero)
  cases hyi : y.isInf
  · have hyf := isFinite_of_isInf_eq_false hyn hyi
    have hy1 := hy hyf
    have hy0 := natAbs_toDyadic_fst_ne_zero fun h ↦ by rw [h] at hy1; norm_num at hy1
    rw [mul_eq_ofDyadic hc hyf, hc1]
    refine isZero_ofDyadic_eq_false _ (Nat.mul_ne_zero (Nat.two_pow_pos 52).ne' hy0) ?_
    rw [Nat.log2_two_pow_mul hy0]
    lia [natCast_log2_add_nonneg hy1]
  · rw [mul_of_isInf_right hc hc0 hyi]
    split_ifs <;> decide

theorem half_mul_ofInt_ne_negZero (d : ℤ) : (0.5 : Double) * ofInt d ≠ -0.0 := by
  intro h
  by_cases hd : d = 0
  · subst hd
    have := congr(Double.bits $h)
    revert this
    decide +kernel
  · have hz := isZero_mul_of_one_le isFinite_half (by rw [toDyadic_half]; rfl)
      (by rw [toDyadic_half]; norm_num) (isNaN_ofInt d) (one_le_abs_toRat_ofInt hd)
    rw [h] at hz
    exact absurd hz (by decide)

theorem signBit_half_mul_ofInt {d : ℤ} (hd : 0 ≤ d) :
    ((0.5 : Double) * ofInt d).signBit = false := by
  have hs := signBit_ofInt_of_nonneg hd
  have h0 : (0.5 : Double).signBit = false := by decide +kernel
  cases hyi : (ofInt d).isInf
  · rw [mul_eq_ofDyadic isFinite_half (isFinite_of_isInf_eq_false (isNaN_ofInt d) hyi),
      signBit_ofDyadic, hs, h0]
    rfl
  · rw [mul_of_isInf_right isFinite_half (by decide +kernel) hyi, hs, h0]
    decide

theorem isNaN_thirtyTwo_mul_ofInt (w : ℤ) : ((32.0 : Double) * ofInt w).isNaN = false := by
  have hc0 : (32.0 : Double).toRat ≠ 0 := by decide +kernel
  cases hyi : (ofInt w).isInf
  · rw [mul_eq_ofDyadic isFinite_thirtyTwo (isFinite_of_isInf_eq_false (isNaN_ofInt w) hyi)]
    exact isNaN_ofDyadic ..
  · rw [mul_of_isInf_right isFinite_thirtyTwo hc0 hyi]
    split_ifs <;> decide

theorem isFinite_ofInt_of_isInf_thirtyTwo_mul_eq_false {w : ℤ}
    (h : ((32.0 : Double) * ofInt w).isInf = false) : (ofInt w).isFinite = true := by
  have hc0 : (32.0 : Double).toRat ≠ 0 := by decide +kernel
  cases hyi : (ofInt w).isInf
  · exact isFinite_of_isInf_eq_false (isNaN_ofInt w) hyi
  · rw [mul_of_isInf_right isFinite_thirtyTwo hc0 hyi] at h
    split_ifs at h <;> exact absurd h (by decide)

theorem thirtyTwo_le_abs_toRat_mul_ofInt {w : ℤ} (hw : w ≠ 0) (hyf : (ofInt w).isFinite = true)
    (hxf : ((32.0 : Double) * ofInt w).isFinite = true) :
    (32 : ℚ) ≤ |((32.0 : Double) * ofInt w).toRat| := by
  have hy1 := one_le_abs_toRat_ofInt hw hyf
  have hy0 := natAbs_toDyadic_fst_ne_zero fun h ↦ by rw [h] at hy1; norm_num at hy1
  have hl := natCast_log2_add_nonneg hy1
  rw [mul_eq_ofDyadic isFinite_thirtyTwo hyf, toDyadic_thirtyTwo] at hxf ⊢
  dsimp only at hxf ⊢
  rw [show (2 ^ 52 : ℤ).natAbs = 2 ^ 52 from rfl] at hxf ⊢
  refine le_trans ?_ (two_pow_le_abs_toRat_ofDyadic _
    (Nat.mul_ne_zero (Nat.two_pow_pos 52).ne' hy0)
    (by rw [Nat.log2_two_pow_mul hy0]; push_cast; lia) hxf)
  rw [Nat.log2_two_pow_mul hy0]
  exact le_trans (by norm_num)
    (zpow_le_zpow_right₀ one_le_two (show (5 : ℤ) ≤ _ by push_cast; lia))

theorem isZero_add_neg_half {x : Double} (hxf : x.isFinite = true) (hx : 2 ≤ |x.toRat|) :
    (x + (0.5 : Double).neg).isZero = false := by
  have hn : (0.5 : Double).neg.isFinite = true := by decide +kernel
  have hh : (0.5 : Double).neg.toRat = -1 / 2 := by rw [toRat_neg]; decide +kernel
  obtain ⟨neg, m, e, he, hv⟩ := exists_add_eq_ofDyadic hxf hn
  rw [he]
  refine isZero_ofDyadic_of_one_le _ ?_
  have h := congr(|$hv|)
  rw [abs_mul, abs_ite_neg_one_one, one_mul,
    abs_of_nonneg (mul_nonneg m.cast_nonneg (zpow_pos two_pos e).le), hh] at h
  rw [h]
  cases abs_cases x.toRat <;> cases abs_cases (x.toRat + -1 / 2) <;> linarith

theorem isZero_thirtyTwo_mul_ofInt_sub_half (w : ℤ) :
    ((32.0 : Double) * ofInt w - 0.5).isZero = false := by
  by_cases hw : w = 0
  · subst hw; decide +kernel
  have hxn := isNaN_thirtyTwo_mul_ofInt w
  rw [Double.sub_eq_add_neg hxn (by decide +kernel)]
  cases hxi : ((32.0 : Double) * ofInt w).isInf
  · have hxf := isFinite_of_isInf_eq_false hxn hxi
    exact isZero_add_neg_half hxf (le_trans (by norm_num) (thirtyTwo_le_abs_toRat_mul_ofInt hw
      (isFinite_ofInt_of_isInf_thirtyTwo_mul_eq_false hxi) hxf))
  · rw [add_of_isInf_left hxi (by decide +kernel)]
    exact isZero_eq_false_of_isInf hxi

theorem approx_half_mul_ofInt {n : ℤ} (h : |n| < 2 ^ 52) :
    ((0.5 : Double) * ofInt n).Approx ((n : ℚ) / 2) |(n : ℚ) / 2| 0 1 := by
  have hn : |(n : ℚ)| < 2 ^ 52 := mod_cast h
  have h1 := approx_half.mul_of_lt (approx_ofInt (z := n) (by lia)) (by norm_num)
    (one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
      ((by linarith : 1 / 2 * |(n : ℚ)| ≤ 2 ^ 52).trans
        (pow_le_pow_right₀ one_le_two (by norm_num))))
  rw [show (1 / 2 : ℚ) * n = n / 2 by ring] at h1
  exact h1.exact ⟨n, by ring⟩ (by norm_num; linarith)

theorem approx_thirtyTwo_mul_ofInt_sub_half {n : ℤ} (h : |n| < 2 ^ 40) :
    ((32.0 : Double) * ofInt n - 0.5).Approx (32 * n - 1 / 2) |32 * (n : ℚ) - 1 / 2| 0 1 := by
  have hn : |(n : ℚ)| < 2 ^ 40 := mod_cast h
  have h1 := approx_thirtyTwo.mul_of_lt (approx_ofInt (z := n) (by lia)) (by norm_num)
    (one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
      ((by linarith : 32 * |(n : ℚ)| ≤ 2 ^ 45).trans (pow_le_pow_right₀ one_le_two (by norm_num))))
  have h2 := (h1.exact (k := 0) ⟨32 * n, by push_cast; ring⟩ (by norm_num; linarith)).mono le_rfl
    le_rfl (Nat.zero_le 1)
  refine approx_sub_exact h2 (by simpa using approx_half) ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 32)]
  norm_num
  linarith

end Double

end JPoints

end
