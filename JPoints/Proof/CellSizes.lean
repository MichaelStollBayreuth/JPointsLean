/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.DoubleArith
public import JPoints.Proof.Rounding

import JPoints.Proof.DoubleArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The half-sizes of a cell of the tube in doubles

What the analysis of a cell of the tube (`tube_cell`, `JPoints.tubeCell`) needs of the doubles of
its half-sizes `rb = 0.5 * (double)(b_hi - b_lo)` and `rc = 32.0 * (double)(i_hi - i_lo) - 0.5`,
whose products it caches and whose comparison `!=` decides when it computes them again: `rb` is
never `-0.0` (`JPoints.Double.half_mul_ofInt_ne_negZero`) and has no sign for `b_lo ≤ b_hi`
(`JPoints.Double.signBit_half_mul_ofInt`), and `rc` is never a zero
(`JPoints.Double.isZero_cellHalfWidth`), so that a double that `==` finds equal to them has their
bits (`JPoints.Double.eq_of_beq`, `JPoints.Double.eq_of_beq_of_signBit_eq_false`). Behind them,
general facts on the doubles: the magnitude of a rounded value
(`JPoints.Double.isZero_ofDyadic_eq_false`, `JPoints.Double.two_pow_le_abs_toRat_ofDyadic`) and the
product of a finite double with an infinity (`JPoints.Double.mul_eq_of_isInf`), beside the sign of
a rounded value and the products and sums of finite doubles as rounded values of
`JPoints.Proof.DoubleArith` (`JPoints.Double.signBit_ofDyadic`, `JPoints.Double.signBit_ofInt`,
`JPoints.Double.mul_eq_ofDyadic`, `JPoints.Double.exists_add_eq_ofDyadic`).

## Main statements

* `JPoints.Double.eq_of_beq`, `JPoints.Double.eq_of_beq_of_signBit_eq_false`,
  `JPoints.Double.beq_neg_one_eq_false`: doubles that `==` finds equal.
* `JPoints.Double.isZero_ofDyadic_eq_false`, `JPoints.Double.two_pow_le_abs_toRat_ofDyadic`: the
  rounding of a dyadic number.
* `JPoints.Double.mul_eq_of_isInf`: the product of a finite double with an infinity.
* `JPoints.Double.half_mul_ofInt_ne_negZero`, `JPoints.Double.signBit_half_mul_ofInt`,
  `JPoints.Double.isZero_cellHalfWidth`: the half-sizes of a cell.

## Implementation notes

The magnitude of a rounded value is bounded below from the significand of the rounding: in the
range of the normal doubles it is at least `2 ^ 52` (`JPoints.Double.two_pow_le_roundShift`), and
at least `1` above the least subnormal (`JPoints.Double.one_le_roundShift`).
-/

@[expose] public section

/-! ### General facts -/

theorem Nat.log2_two_pow_mul {k : ℕ} (hk : k ≠ 0) (n : ℕ) : (2 ^ n * k).log2 = n + k.log2 := by
  rw [Nat.log2_eq_iff (by positivity), Nat.add_assoc, Nat.pow_add, Nat.pow_add]
  exact ⟨Nat.mul_le_mul_left _ (Nat.log2_self_le hk),
    Nat.mul_lt_mul_of_pos_left Nat.lt_log2_self (Nat.two_pow_pos n)⟩

namespace JPoints

namespace Double

theorem beq_comm (x y : Double) : x.beq y = y.beq x := by
  simp only [beq]
  cases x.isNaN <;> cases y.isNaN <;> simp [eq_comm]

theorem eq_of_orderValue_eq {x y : Double} (h : x.orderValue = y.orderValue)
    (hy : y.isZero = false) : x = y := by
  rw [isZero_eq_decide, decide_eq_false_iff_not] at hy
  have hx := toNat_bits_eq_mod x
  have hy' := toNat_bits_eq_mod y
  rw [orderValue_eq_mod, orderValue_eq_mod] at h
  have e : x.bits.toNat = y.bits.toNat := by
    cases hsx : x.signBit <;> cases hsy : y.signBit <;> simp only [hsx, hsy] at h hx hy' <;> lia
  obtain ⟨bx⟩ := x
  obtain ⟨by'⟩ := y
  simp only [Double.mk.injEq]
  exact UInt64.toNat_inj.mp e

theorem orderValue_eq_of_beq {x y : Double} (h : x.beq y = true) :
    x.orderValue = y.orderValue := by
  simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem eq_of_beq {x y : Double} (h : x.beq y = true) (hy : y.isZero = false) : x = y :=
  eq_of_orderValue_eq (orderValue_eq_of_beq h) hy

theorem eq_of_beq_of_signBit_eq_false {x y : Double} (h : x.beq y = true)
    (hx : x.signBit = false) (hy : y ≠ -0.0) : x = y := by
  cases hz : y.isZero
  · exact eq_of_beq h hz
  have e := orderValue_eq_of_beq h
  rw [isZero_eq_decide, decide_eq_true_eq] at hz
  have hx' := toNat_bits_eq_mod x
  have hy' := toNat_bits_eq_mod y
  rw [orderValue_eq_mod, orderValue_eq_mod, hx, hz] at e
  rw [hx] at hx'
  cases hsy : y.signBit
  · rw [hsy] at hy' e
    obtain ⟨bx⟩ := x
    obtain ⟨by'⟩ := y
    simp only [Double.mk.injEq]
    exact UInt64.toNat_inj.mp (by simp only at hx' hy' e; lia)
  · exact absurd (show y = ⟨0x8000000000000000⟩ by
      obtain ⟨by'⟩ := y
      simp only [Double.mk.injEq]
      exact UInt64.toNat_inj.mp (by simp only [hsy, ↓reduceIte] at hy'; rw [hy', hz]; rfl)) hy

theorem beq_neg_one_eq_false {x : Double} (hx : x.signBit = false) : x.beq (-1.0) = false := by
  by_contra h
  have e := orderValue_eq_of_beq (Bool.not_eq_false _ ▸ h)
  rw [orderValue_eq_mod, hx, show (-1.0 : Double).orderValue = -0x3ff0000000000000 by
    decide +kernel] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  lia

theorem isZero_ofSignificand {neg : Bool} {M : ℕ} {q : ℤ} (h1 : 1 ≤ M) (hM : M ≤ 2 ^ 53)
    (hq : -1074 ≤ q) : (ofSignificand neg M q).isZero = false := by
  rw [isZero_eq_decide, decide_eq_false_iff_not, ← expField_mul_add_fracField]
  rcases hM.lt_or_eq with hM | rfl
  · rw [ofSignificand_of_ne _ hM.ne]
    obtain ⟨-, he, hf⟩ := fields_assemble neg q hM
    rw [he, hf]
    split_ifs <;> lia
  · rw [ofSignificand_two_pow]
    obtain ⟨-, he, hf⟩ := fields_assemble neg (q + 1) (M := 2 ^ 52) (by norm_num)
    rw [he, hf]
    split_ifs <;> lia

theorem one_le_roundShift {m : ℕ} (hm : m ≠ 0) {e : ℤ} (h : -1074 ≤ (m.log2 : ℤ) + e) :
    1 ≤ roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) := by
  obtain ⟨-, -, -, hhi, -⟩ := ofDyadic_rounding hm e
  have hv := (two_zpow_log2_le_mul hm e).1
  by_contra h0
  rw [show roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) = 0 by lia] at hhi
  have hlt : (2 : ℚ) ^ (max ((m.log2 : ℤ) + e - 52) (-1074) - 1) < 2 ^ ((m.log2 : ℤ) + e) :=
    zpow_lt_zpow_right₀ one_lt_two (by lia)
  push_cast at hhi
  linarith

theorem two_pow_le_roundShift {m : ℕ} (hm : m ≠ 0) {e : ℤ} (h : -1021 ≤ (m.log2 : ℤ) + e) :
    2 ^ 52 ≤ roundShift m (max ((m.log2 : ℤ) + e - 52) (-1074) - e) := by
  obtain ⟨-, -, -, hhi, hnorm⟩ := ofDyadic_rounding hm e
  have hq : max ((m.log2 : ℤ) + e - 52) (-1074) = (m.log2 : ℤ) + e - 52 := max_eq_left (by lia)
  rw [hq] at hhi hnorm ⊢
  have h1 := hnorm (by lia)
  rw [zpow_add₀ two_ne_zero] at h1
  rw [zpow_sub₀ two_ne_zero ((m.log2 : ℤ) + e - 52), zpow_one] at hhi
  have hp : (0 : ℚ) < 2 ^ ((m.log2 : ℤ) + e - 52) := zpow_pos two_pos _
  have h2 : (2 : ℚ) ^ (52 : ℤ) ≤ roundShift m ((m.log2 : ℤ) + e - 52 - e) + 1 / 2 := by
    refine le_of_mul_le_mul_right ?_ hp
    linarith
  by_contra h4
  have h5 : (roundShift m ((m.log2 : ℤ) + e - 52 - e) : ℚ) + 1 ≤ 2 ^ 52 := by
    exact_mod_cast (show roundShift m ((m.log2 : ℤ) + e - 52 - e) + 1 ≤ 2 ^ 52 by lia)
  norm_num at h2 h5
  linarith

theorem isZero_ofDyadic_eq_false (neg : Bool) {m : ℕ} (hm : m ≠ 0) {e : ℤ}
    (h : -1074 ≤ (m.log2 : ℤ) + e) : (ofDyadic neg m e).isZero = false := by
  rw [ofDyadic_eq e hm]
  exact isZero_ofSignificand (one_le_roundShift hm h) (ofDyadic_rounding hm e).1
    (le_max_right _ _)

theorem two_pow_le_abs_toRat_ofSignificand (neg : Bool) {M : ℕ} {q : ℤ} (hM : 2 ^ 52 ≤ M)
    (hM' : M ≤ 2 ^ 53) (hq : -1073 ≤ q) (hf : (ofSignificand neg M q).isFinite = true) :
    (2 : ℚ) ^ (q + 52) ≤ |(ofSignificand neg M q).toRat| := by
  have hsplit : (2 : ℚ) ^ (q + 52) = 2 ^ 52 * 2 ^ q := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
  have hp : (0 : ℚ) < 2 ^ q := zpow_pos two_pos _
  rcases hM'.lt_or_eq with hM' | rfl
  · rw [ofSignificand_of_ne _ hM'.ne] at hf ⊢
    have hfin := (isFinite_assemble_iff hM').mp hf
    rw [toRat_assemble hM' (fun h ↦ absurd h (by lia)) fun _ ↦ ⟨by lia, by lia⟩, abs_mul,
      abs_mul, hsplit]
    have : (2 : ℚ) ^ 52 ≤ M := mod_cast hM
    split_ifs <;> simp only [abs_neg, abs_one, one_mul, Nat.abs_cast, abs_of_pos hp] <;> nlinarith
  · rw [ofSignificand_two_pow] at hf ⊢
    have hfin := (isFinite_assemble_iff (by norm_num : 2 ^ 52 < 2 ^ 53)).mp hf
    rw [toRat_assemble (by norm_num) (fun h ↦ absurd h (by norm_num)) fun _ ↦ ⟨by lia, by lia⟩,
      abs_mul, abs_mul, hsplit, zpow_add_one₀ two_ne_zero]
    rw [abs_ite_neg_one_one, one_mul, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    push_cast
    nlinarith

theorem two_pow_le_abs_toRat_ofDyadic (neg : Bool) {m : ℕ} (hm : m ≠ 0) {e : ℤ}
    (h : -1021 ≤ (m.log2 : ℤ) + e) (hf : (ofDyadic neg m e).isFinite = true) :
    (2 : ℚ) ^ ((m.log2 : ℤ) + e) ≤ |(ofDyadic neg m e).toRat| := by
  have hq : max ((m.log2 : ℤ) + e - 52) (-1074) = (m.log2 : ℤ) + e - 52 := max_eq_left (by lia)
  have hM := two_pow_le_roundShift hm h
  have hM' := (ofDyadic_rounding hm e).1
  rw [ofDyadic_eq e hm] at hf ⊢
  rw [hq] at hM hM' hf ⊢
  have := two_pow_le_abs_toRat_ofSignificand neg hM hM' (by lia) hf
  rwa [sub_add_cancel] at this

theorem mul_eq_of_isInf {x y : Double} (hx : x.isFinite = true) (hx0 : x.isZero = false)
    (hy : y.isInf = true) (hyn : y.isNaN = false) :
    x * y = if x.signBit != y.signBit then huge.neg else huge := by
  change mul x y = _
  simp only [mul, isNaN_eq_false_of_isFinite hx, hyn, hy, hx0, Bool.or_false, Bool.or_true,
    Bool.false_eq_true, ↓reduceIte]
  have hy0 : y.isZero = false := by
    simp only [isInf, Bool.and_eq_true, beq_iff_eq] at hy
    rw [isZero_eq_decide, decide_eq_false_iff_not, ← expField_mul_add_fracField, hy.1]
    lia
  rw [hy0]
  rfl

theorem isZero_ofInt_eq_false {d : ℤ} (hd : d ≠ 0) : (ofInt d).isZero = false :=
  isZero_ofDyadic_eq_false _ (Int.natAbs_ne_zero.mpr hd) (by lia)

theorem isNaN_ofInt (d : ℤ) : (ofInt d).isNaN = false := isNaN_ofDyadic ..

theorem one_le_abs_toRat_ofInt {d : ℤ} (hd : d ≠ 0) (hf : (ofInt d).isFinite = true) :
    1 ≤ |(ofInt d).toRat| :=
  (one_le_zpow₀ one_le_two (by lia)).trans
    (two_pow_le_abs_toRat_ofDyadic _ (Int.natAbs_ne_zero.mpr hd) (by lia) hf)

theorem natCast_log2_add_nonneg {x : Double} (h : 1 ≤ |x.toRat|) :
    0 ≤ (x.toDyadic.1.natAbs.log2 : ℤ) + x.toDyadic.2 := by
  have h0 : x.toDyadic.1.natAbs ≠ 0 :=
    natAbs_toDyadic_fst_ne_zero fun h' ↦ by rw [h'] at h; norm_num at h
  have h1 := (two_zpow_log2_le_mul h0 x.toDyadic.2).2
  rw [← abs_toRat] at h1
  have := (one_lt_zpow_iff_right₀ one_lt_two).mp (h.trans_lt h1)
  lia

theorem toDyadic_half : (0.5 : Double).toDyadic = (2 ^ 52, -53) := by decide +kernel

theorem toDyadic_thirtyTwo : (32.0 : Double).toDyadic = (2 ^ 52, -47) := by decide +kernel

theorem isFinite_thirtyTwo : (32.0 : Double).isFinite = true := by decide +kernel

/-- The product of a finite double `c > 0` with the significand `2 ^ 52` and a double `y` of
magnitude at least `1` (or an infinity, or `±0`) is no zero unless `y` is one. -/
theorem isZero_mul_of_one_le {c y : Double} (hc : c.isFinite = true)
    (hc1 : c.toDyadic.1.natAbs = 2 ^ 52) (hc2 : -1074 ≤ c.toDyadic.2 + 52)
    (hyn : y.isNaN = false) (hy : y.isFinite = true → 1 ≤ |y.toRat|) : (c * y).isZero = false := by
  have hc0 : c.isZero = false := by
    rw [isZero_eq_false_iff, ← abs_ne_zero, abs_toRat, hc1]
    exact mul_ne_zero (by norm_num) (zpow_ne_zero _ two_ne_zero)
  cases hyi : y.isInf
  · have hyf := isFinite_of_isInf_eq_false hyn hyi
    have hy1 := hy hyf
    have hy0 := natAbs_toDyadic_fst_ne_zero fun h ↦ by rw [h] at hy1; norm_num at hy1
    rw [mul_eq_ofDyadic hc hyf, hc1]
    refine isZero_ofDyadic_eq_false _ (Nat.mul_ne_zero (Nat.two_pow_pos 52).ne' hy0) ?_
    rw [Nat.log2_two_pow_mul hy0]
    lia [natCast_log2_add_nonneg hy1]
  · rw [mul_eq_of_isInf hc hc0 hyi hyn]
    split_ifs <;> decide

theorem isZero_ofDyadic_of_one_le (neg : Bool) {m : ℕ} {e : ℤ} (hv : 1 ≤ (m : ℚ) * 2 ^ e) :
    (ofDyadic neg m e).isZero = false := by
  have hm : m ≠ 0 := by rintro rfl; norm_num at hv
  have := (one_lt_zpow_iff_right₀ one_lt_two).mp (hv.trans_lt (two_zpow_log2_le_mul hm e).2)
  exact isZero_ofDyadic_eq_false neg hm (by lia)

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
  have hs : (ofInt d).signBit = false := by rw [signBit_ofInt]; simp; lia
  have h0 : (0.5 : Double).signBit = false := by decide +kernel
  cases hyi : (ofInt d).isInf
  · rw [mul_eq_ofDyadic isFinite_half (isFinite_of_isInf_eq_false (isNaN_ofInt d) hyi),
      signBit_ofDyadic, hs, h0]
    rfl
  · rw [mul_eq_of_isInf isFinite_half (by decide +kernel) hyi (isNaN_ofInt d), hs, h0]
    decide

theorem isZero_eq_false_of_isInf {x : Double} (h : x.isInf = true) : x.isZero = false := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h
  rw [isZero_eq_decide, decide_eq_false_iff_not, ← expField_mul_add_fracField, h.1]
  lia

theorem add_eq_of_isInf_left {x y : Double} (hxn : x.isNaN = false) (hx : x.isInf = true)
    (hy : y.isFinite = true) : x + y = x := by
  change add x y = _
  simp only [add, hxn, isNaN_eq_false_of_isFinite hy, hx, isInf_eq_false_of_isFinite hy,
    Bool.or_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem isNaN_thirtyTwo_mul_ofInt (w : ℤ) : ((32.0 : Double) * ofInt w).isNaN = false := by
  have hc0 : (32.0 : Double).isZero = false := by decide +kernel
  cases hyi : (ofInt w).isInf
  · rw [mul_eq_ofDyadic isFinite_thirtyTwo (isFinite_of_isInf_eq_false (isNaN_ofInt w) hyi)]
    exact isNaN_ofDyadic ..
  · rw [mul_eq_of_isInf isFinite_thirtyTwo hc0 hyi (isNaN_ofInt w)]
    split_ifs <;> decide

theorem isFinite_ofInt_of_isInf_thirtyTwo_mul {w : ℤ}
    (h : ((32.0 : Double) * ofInt w).isInf = false) : (ofInt w).isFinite = true := by
  have hc0 : (32.0 : Double).isZero = false := by decide +kernel
  cases hyi : (ofInt w).isInf
  · exact isFinite_of_isInf_eq_false (isNaN_ofInt w) hyi
  · rw [mul_eq_of_isInf isFinite_thirtyTwo hc0 hyi (isNaN_ofInt w)] at h
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

theorem isZero_cellHalfWidth (w : ℤ) :
    ((32.0 : Double) * ofInt w - 0.5).isZero = false := by
  by_cases hw : w = 0
  · subst hw; decide +kernel
  have hxn := isNaN_thirtyTwo_mul_ofInt w
  rw [sub_eq_add_neg hxn (by decide +kernel)]
  cases hxi : ((32.0 : Double) * ofInt w).isInf
  · have hxf := isFinite_of_isInf_eq_false hxn hxi
    exact isZero_add_neg_half hxf (le_trans (by norm_num) (thirtyTwo_le_abs_toRat_mul_ofInt hw
      (isFinite_ofInt_of_isInf_thirtyTwo_mul hxi) hxf))
  · rw [add_eq_of_isInf_left hxn hxi (by decide +kernel)]
    exact isZero_eq_false_of_isInf hxi

end Double

end JPoints

end
