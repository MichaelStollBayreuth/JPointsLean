/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.DoubleArith
public import JPoints.Proof.Rounding

import JPoints.Mathlib.Order.WithBotTop
import JPoints.Proof.DoubleArith
import Mathlib.Algebra.Order.Field.Power

/-!
# The truncation of rational numbers to doubles

The doubles of `real_roots_init`. `mpq_get_d` and `mpz_get_d` of GMP truncate a rational number
towards zero to a double (`JPoints.Double.ofRatioTrunc` of the model): the significand
`M = ⌊n / (d 2 ^ q)⌋` for the exponent `q` of the last place that `JPoints.Double.ofRatio` finds,
with `M 2 ^ q ≤ n / d < (M + 1) 2 ^ q` (`JPoints.Double.ratioPair_div_bounds`), below `2 ^ 53`, and
normal unless `q` is the least exponent (`JPoints.Double.ratioTrunc_props`), so that the result is
no NaN (`JPoints.Double.isNaN_ofRatioTrunc`, `JPoints.Double.isNaN_mpqGetD`) and the number lies
strictly between the neighbours of the result
(`JPoints.Double.lt_nextUp_and_nextDown_lt_ofRatioTrunc`,
`JPoints.Double.lt_nextUp_and_nextDown_lt_mpqGetD`), also for an infinite result and for `0.0`,
whose neighbours have the values that `decide +kernel` computes; below `2 ^ 1024` the result is
finite and within less than a unit in its last place, `2 ^ (-52)` times the number and `2 ^ (-1074)`
(`JPoints.Double.isFinite_and_abs_toRat_ofRatioTrunc_sub_le`,
`JPoints.Double.isFinite_mpqGetD_and_abs_toRat_sub_le`). `nextafter` keeps a double that is no NaN
so (`JPoints.Double.isNaN_nextUp`, `JPoints.Double.isNaN_nextDown`). The test of the refinement of
`sturm_isolate` holds for every interval of a width of at most `2 ^ (-43)` within `±2 ^ 480`
(`JPoints.Double.mpqGetD_sub_mpqGetD_le`), so that its loop ends: the truncations of the ends move
their difference by about `2 ^ (-52)` times their absolute values, and the roundings of the
operations of the test (`JPoints.Double.IsRounding`) by half a unit in their last places, far less
than the margin of the test.

## Main statements

* `JPoints.Double.isNaN_mpqGetD`, `JPoints.Double.lt_nextUp_and_nextDown_lt_mpqGetD`: the
  truncation of `mpq_get_d` is no NaN and faithful.
* `JPoints.Double.isFinite_mpqGetD_and_abs_toRat_sub_le`: its error.
* `JPoints.Double.isNaN_nextUp`, `JPoints.Double.isNaN_nextDown`: `nextafter` gives no NaN.
* `JPoints.Double.mpqGetD_sub_mpqGetD_le`: the test of the refinement of `sturm_isolate`.

## Implementation notes

The large powers of `2` (the bound `2 ^ 480` of the ends, `2 ^ 1022` of the finite roundings) are
beyond what `linarith` reads; its arguments have them abstracted as a variable.
-/

@[expose] public section

namespace JPoints

namespace Double

theorem isNaN_nextUp {x : Double} (hx : x.isNaN = false) : (nextUp x).isNaN = false := by
  by_cases hi : x.bits = huge.bits
  · rwa [show nextUp x = x by simp [nextUp, hx, hi]]
  · exact (orderValue_nextUp hx hi).2

theorem isNaN_nextDown {x : Double} (hx : x.isNaN = false) : (nextDown x).isNaN = false := by
  by_cases hi : x.bits = huge.neg.bits
  · rwa [show nextDown x = x by simp [nextDown, hx, hi]]
  · exact (orderValue_nextDown hx hi).2

theorem ofRatioTrunc_eq {neg : Bool} {n : ℕ} (d : ℕ) (hn : n ≠ 0) :
    ofRatioTrunc neg n d = if 1024 ≤ ratioExponent n d then (if neg then huge.neg else huge)
      else if (ratioPair n d (ratioLast n d)).1 / (ratioPair n d (ratioLast n d)).2 = 0 then zero
      else assemble neg ((ratioPair n d (ratioLast n d)).1 / (ratioPair n d (ratioLast n d)).2)
        (ratioLast n d) := by
  simp only [ofRatioTrunc, ratioExponent, ratioLast, ratioPair, hn, ↓reduceIte]
  split_ifs <;> rfl

theorem doubleValue_nextUp_zero :
    doubleValue (nextUp zero).bits = ((2 : ℚ) ^ (-1074 : ℤ) : ℚ) := by
  decide +kernel

theorem doubleValue_nextDown_zero :
    doubleValue (nextDown zero).bits = (-(2 : ℚ) ^ (-1074 : ℤ) : ℚ) := by
  decide +kernel

theorem doubleValue_nextDown_huge :
    doubleValue (nextDown huge).bits = (((2 ^ 53 - 1) * 2 ^ 971 : ℕ) : ℚ) := by
  decide +kernel

theorem doubleValue_nextUp_huge_neg :
    doubleValue (nextUp huge.neg).bits = (-(((2 ^ 53 - 1) * 2 ^ 971 : ℕ) : ℚ) : ℚ) := by
  decide +kernel

theorem doubleValue_nextUp_huge : doubleValue (nextUp huge).bits = ⊤ := by
  decide +kernel

theorem doubleValue_nextDown_huge_neg : doubleValue (nextDown huge.neg).bits = ⊥ := by
  decide +kernel

/-- The quotient of `JPoints.Double.ofRatioTrunc` truncated to an integer: `M 2 ^ q ≤ n / d <
(M + 1) 2 ^ q` for the exponent `q` of its last place. -/
theorem ratioPair_div_bounds {n d : ℕ} (hd : d ≠ 0) (q : ℤ) :
    (((ratioPair n d q).1 / (ratioPair n d q).2 : ℕ) : ℚ) * 2 ^ q ≤ n / d ∧
      (n : ℚ) / d < (((ratioPair n d q).1 / (ratioPair n d q).2 : ℕ) + 1) * 2 ^ q := by
  have hb := ratioPair_snd_pos (n := n) hd q
  have hdiv := ratioPair_div n d q
  set a := (ratioPair n d q).1
  set b := (ratioPair n d q).2
  have hb' : (0 : ℚ) < b := mod_cast hb
  have h1 : ((a / b : ℕ) : ℚ) * b ≤ a := mod_cast Nat.div_mul_le_self a b
  have h2 : (a : ℚ) < ((a / b : ℕ) + 1) * b := by
    rw [add_mul, one_mul]; exact_mod_cast Nat.lt_div_mul_add hb
  have ht : (0 : ℚ) < 2 ^ q := by positivity
  have hnd : (n : ℚ) / d = a / b * 2 ^ q := by rw [hdiv, div_mul_cancel₀ _ ht.ne']
  rw [hnd]
  exact ⟨mul_le_mul_of_nonneg_right ((le_div_iff₀ hb').mpr h1) ht.le,
    mul_lt_mul_of_pos_right ((div_lt_iff₀ hb').mpr h2) ht⟩

/-- The truncated quotient `M` of `JPoints.Double.ofRatioTrunc` for an exponent below `1024`: a
significand below `2 ^ 53`, normal unless its last place is the least, `2 ^ (-1074)`, and an
exponent field below `2047`. -/
theorem ratioTrunc_props {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0) (hE : ratioExponent n d < 1024) :
    (ratioPair n d (ratioLast n d)).1 / (ratioPair n d (ratioLast n d)).2 < 2 ^ 53 ∧
      (ratioLast n d = -1074 ∨
        2 ^ 52 ≤ (ratioPair n d (ratioLast n d)).1 / (ratioPair n d (ratioLast n d)).2) ∧
      -1074 ≤ ratioLast n d ∧ ratioLast n d + 1075 < 2047 := by
  obtain ⟨e1, e2⟩ := ratioExponent_bounds hn hd
  obtain ⟨b1, b2⟩ := ratioPair_div_bounds (n := n) hd (ratioLast n d)
  set q := ratioLast n d with hq
  set M := (ratioPair n d q).1 / (ratioPair n d q).2
  have hq1 : ratioExponent n d - 52 ≤ q := le_max_left _ _
  have ht : (0 : ℚ) < 2 ^ q := by positivity
  have h53 : (2 : ℚ) ^ (ratioExponent n d + 1) ≤ 2 ^ q * 2 ^ 53 := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    exact zpow_le_zpow_right₀ one_le_two (by push_cast; lia)
  refine ⟨?_, ?_, le_max_right _ _, by rw [hq, ratioLast]; lia⟩
  · have : (M : ℚ) < 2 ^ 53 := lt_of_mul_lt_mul_left (by linarith) ht.le
    exact_mod_cast this
  · by_cases hq' : q = -1074
    · exact .inl hq'
    · refine .inr ?_
      have hqE : q = ratioExponent n d - 52 := by rw [hq, ratioLast] at hq' ⊢; lia
      have h52 : (2 : ℚ) ^ q * 2 ^ 52 ≤ n / d := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, hqE]; convert e1 using 2; push_cast; ring
      have : (2 : ℚ) ^ 52 < M + 1 := lt_of_mul_lt_mul_left (by linarith) ht.le
      exact Nat.lt_succ_iff.mp (mod_cast this)

theorem isNaN_ofRatioTrunc (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (ofRatioTrunc neg n d).isNaN = false := by
  by_cases hn : n = 0
  · simp only [ofRatioTrunc, hn, ↓reduceIte]; decide
  rw [ofRatioTrunc_eq d hn]
  split_ifs with hE
  · exact isNaN_huge_neg
  · exact isNaN_huge
  · decide
  · exact isNaN_assemble neg _ (ratioTrunc_props hn hd (by lia)).1

/-- `±v` for `v ≥ 0` below `2 ^ (-1074)` lies strictly between the neighbours of `0.0`. -/
theorem lt_nextUp_and_nextDown_lt_zero (neg : Bool) {v : ℚ} (h0 : 0 ≤ v)
    (h : v < 2 ^ (-1074 : ℤ)) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) < doubleValue (nextUp zero).bits ∧
      doubleValue (nextDown zero).bits < ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_nextUp_zero, doubleValue_nextDown_zero, WithBotTop.coe_lt_coe,
    WithBotTop.coe_lt_coe]
  have : (0 : ℚ) < 2 ^ (-1074 : ℤ) := by positivity
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

/-- `±v` for `v ≥ 2 ^ 1024` lies strictly between the neighbours of `±∞`. -/
theorem lt_nextUp_and_nextDown_lt_huge (neg : Bool) {v : ℚ} (h : 2 ^ (1024 : ℤ) ≤ v) :
    ((if neg then -v else v : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (if neg then huge.neg else huge)).bits ∧
      doubleValue (nextDown (if neg then huge.neg else huge)).bits <
        ((if neg then -v else v : ℚ) : WithBotTop ℚ) := by
  have hm : ((((2 ^ 53 - 1) * 2 ^ 971 : ℕ) : ℚ)) < 2 ^ (1024 : ℤ) := by
    rw [show (1024 : ℤ) = ((1024 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact_mod_cast (by decide +kernel : (2 ^ 53 - 1) * 2 ^ 971 < 2 ^ 1024)
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [doubleValue_nextUp_huge, doubleValue_nextDown_huge, WithBotTop.coe_lt_coe]
    exact ⟨WithBotTop.coe_lt_top _, by linarith⟩
  · rw [doubleValue_nextUp_huge_neg, doubleValue_nextDown_huge_neg, WithBotTop.coe_lt_coe]
    exact ⟨by linarith, WithBotTop.bot_lt_coe _⟩

-- The faithful truncation of `JPoints.Double.ofRatioTrunc` for an exponent below `1024`: `0.0`,
-- a subnormal or a normal double.
private theorem lt_nextUp_and_nextDown_lt_ofRatioTrunc_of_lt (neg : Bool) {n d : ℕ} (hn : n ≠ 0)
    (hd : d ≠ 0) (hE : ¬1024 ≤ ratioExponent n d) :
    ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofRatioTrunc neg n d)).bits ∧
      doubleValue (nextDown (ofRatioTrunc neg n d)).bits <
        ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) := by
  rw [ofRatioTrunc_eq d hn, ite_eq_right hE]
  obtain ⟨b1, b2⟩ := ratioPair_div_bounds (n := n) hd (ratioLast n d)
  have hv : 0 < (n : ℚ) / d := by positivity
  obtain ⟨hM53, hnorm, hq1, hq2⟩ := ratioTrunc_props hn hd (by lia)
  generalize (ratioPair n d (ratioLast n d)).1 / (ratioPair n d (ratioLast n d)).2 = M at *
  generalize ratioLast n d = q at *
  by_cases hM0 : M = 0
  · obtain rfl := hnorm.resolve_right (by lia)
    rw [ite_eq_left hM0]
    exact lt_nextUp_and_nextDown_lt_zero neg hv.le (by simpa [hM0] using b2)
  rw [ite_eq_right hM0]
  rcases lt_or_ge M (2 ^ 52) with hsub | hnormal
  · obtain rfl := hnorm.resolve_right (by lia)
    exact lt_nextUp_and_nextDown_lt_assemble_of_lt hsub hv b2 fun _ ↦ by linarith
  · exact lt_nextUp_and_nextDown_lt_assemble_of_two_pow_le hnormal hM53 hq1 hq2 hv b2
      ((sub_lt_self _ (by split_ifs <;> positivity)).trans_le b1)

/-- `JPoints.Double.ofRatioTrunc` truncates faithfully: `±n / d` lies strictly between the
neighbours of the result, also for an infinite result and for `0.0`. -/
theorem lt_nextUp_and_nextDown_lt_ofRatioTrunc (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) <
        doubleValue (nextUp (ofRatioTrunc neg n d)).bits ∧
      doubleValue (nextDown (ofRatioTrunc neg n d)).bits <
        ((if neg then -((n : ℚ) / d) else (n : ℚ) / d : ℚ) : WithBotTop ℚ) := by
  by_cases hn : n = 0
  · subst hn
    simpa [ofRatioTrunc] using lt_nextUp_and_nextDown_lt_zero neg le_rfl (by positivity)
  by_cases hE : 1024 ≤ ratioExponent n d
  · rw [ofRatioTrunc_eq d hn, ite_eq_left hE]
    exact lt_nextUp_and_nextDown_lt_huge neg
      ((zpow_le_zpow_right₀ one_le_two hE).trans (ratioExponent_bounds hn hd).1)
  · exact lt_nextUp_and_nextDown_lt_ofRatioTrunc_of_lt neg hn hd hE

-- The rational number from the sign, the absolute value of the numerator and the denominator.
private theorem ite_natAbs_num_div_den (r : ℚ) :
    (if decide (r.num < 0) = true then -((r.num.natAbs : ℚ) / r.den)
      else (r.num.natAbs : ℚ) / r.den) = r := by
  split_ifs with h
  · rw [decide_eq_true_eq] at h
    rw [Nat.cast_natAbs, abs_of_neg h, Int.cast_neg, neg_div, neg_neg, Rat.num_div_den]
  · rw [decide_eq_true_eq, not_lt] at h
    rw [Nat.cast_natAbs, abs_of_nonneg h, Rat.num_div_den]

/-- `mpq_get_d(r)` truncates `r` towards zero to a double, so that `r` lies strictly between its
neighbours. -/
theorem lt_nextUp_and_nextDown_lt_mpqGetD (r : ℚ) :
    (r : WithBotTop ℚ) < doubleValue (nextUp (mpqGetD r)).bits ∧
      doubleValue (nextDown (mpqGetD r)).bits < r := by
  have := lt_nextUp_and_nextDown_lt_ofRatioTrunc (r.num < 0) r.num.natAbs r.den_nz
  rwa [ite_natAbs_num_div_den] at this

theorem isNaN_mpqGetD (r : ℚ) : (mpqGetD r).isNaN = false :=
  isNaN_ofRatioTrunc _ _ r.den_nz

/-! ### The error of the truncation -/

-- `|s a - s b| = |a - b|` for a sign `s = ±1`.
private theorem abs_ite_mul_sub_ite_mul (neg : Bool) (a b : ℚ) :
    |(if neg then -1 else 1) * a - (if neg then -1 else 1) * b| = |a - b| := by
  cases neg
  · simp
  · simp only [↓reduceIte, neg_mul, one_mul, sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm]

-- `2 ^ (-1074)`, the least subnormal, bounded by a power that `linarith` reads.
private theorem two_zpow_neg_1074_le : (2 : ℚ) ^ (-1074 : ℤ) ≤ 1 / 2 ^ 200 := by
  rw [← zpow_natCast, one_div, ← zpow_neg]
  exact zpow_le_zpow_right₀ one_le_two (by norm_num)

-- The double of a truncated significand `M < 2 ^ 53` and the exponent `q` of its last place, `0.0`
-- for `M = 0`, for `v > 0` in `[M 2 ^ q, (M + 1) 2 ^ q)`, `M` normal unless `q` is the least
-- exponent: finite and within less than a unit in its last place of `±v`.
private theorem isFinite_and_abs_toRat_ite_sub_le {neg : Bool} {M : ℕ} {q : ℤ} {v : ℚ}
    (hv : 0 < v) (b1 : M * 2 ^ q ≤ v) (b2 : v < (M + 1) * 2 ^ q) (hM53 : M < 2 ^ 53)
    (hnorm : q = -1074 ∨ 2 ^ 52 ≤ M) (hq1 : -1074 ≤ q) (hq2 : q + 1075 < 2047) :
    (if M = 0 then zero else assemble neg M q).isFinite = true ∧
      |(if M = 0 then zero else assemble neg M q).toRat - (if neg then -1 else 1) * v| ≤
        v / 2 ^ 52 + 2 ^ (-1074 : ℤ) := by
  have ht : (0 : ℚ) < 2 ^ (-1074 : ℤ) := by positivity
  have ht2 : (0 : ℚ) < 2 ^ q := by positivity
  have hu : (2 : ℚ) ^ q ≤ v / 2 ^ 52 + 2 ^ (-1074 : ℤ) := by
    rcases hnorm with rfl | h52
    · linarith [div_nonneg hv.le (by positivity : (0 : ℚ) ≤ 2 ^ 52)]
    · have h52' : (2 : ℚ) ^ 52 ≤ M := mod_cast h52
      have := mul_le_mul_of_nonneg_right h52' ht2.le
      linarith
  by_cases hM0 : M = 0
  · subst hM0
    rw [ite_eq_left rfl, toRat_zero, zero_sub, abs_neg, abs_mul, abs_of_pos hv,
      abs_ite_neg_one_one, one_mul]
    simp only [Nat.cast_zero, zero_add, one_mul] at b2
    exact ⟨isFinite_zero, by linarith⟩
  rw [ite_eq_right hM0, toRat_assemble hM53 (fun h ↦ hnorm.resolve_right (by lia))
    fun _ ↦ ⟨hq1, hq2⟩, abs_ite_mul_sub_ite_mul, abs_sub_comm, abs_of_nonneg (by linarith)]
  exact ⟨(isFinite_assemble_iff hM53).mpr (.inr hq2), by linarith⟩

theorem ofRatioTrunc_zero (neg : Bool) (d : ℕ) : ofRatioTrunc neg 0 d = zero := by
  simp [ofRatioTrunc]

/-- `JPoints.Double.ofRatioTrunc` truncates `±n / d` below `2 ^ 1024` to a finite double within
less than a unit in its last place. -/
theorem isFinite_and_abs_toRat_ofRatioTrunc_sub_le (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0)
    (h : (n : ℚ) / d < 2 ^ 1024) :
    (ofRatioTrunc neg n d).isFinite = true ∧
      |(ofRatioTrunc neg n d).toRat - (if neg then -1 else 1) * ((n : ℚ) / d)| ≤
        n / d / 2 ^ 52 + 2 ^ (-1074 : ℤ) := by
  by_cases hn : n = 0
  · subst hn
    rw [ofRatioTrunc_zero, toRat_zero, Nat.cast_zero, zero_div, mul_zero, sub_zero, abs_zero,
      zero_div, zero_add]
    exact ⟨isFinite_zero, by positivity⟩
  have hE : ¬1024 ≤ ratioExponent n d := fun hE ↦ by
    have := (zpow_le_zpow_right₀ one_le_two hE).trans (ratioExponent_bounds hn hd).1
    rw [zpow_ofNat] at this
    exact absurd h (not_lt.mpr this)
  rw [ofRatioTrunc_eq d hn, ite_eq_right hE]
  obtain ⟨b1, b2⟩ := ratioPair_div_bounds (n := n) hd (ratioLast n d)
  obtain ⟨hM53, hnorm, hq1, hq2⟩ := ratioTrunc_props hn hd (by lia)
  exact isFinite_and_abs_toRat_ite_sub_le (by positivity) b1 b2 hM53 hnorm hq1 hq2

/-- `mpq_get_d(r)` truncates `r` below `2 ^ 1024` in absolute value to a finite double within less
than a unit in its last place. -/
theorem isFinite_mpqGetD_and_abs_toRat_sub_le {r : ℚ} (h : |r| < 2 ^ 1024) :
    (mpqGetD r).isFinite = true ∧ |(mpqGetD r).toRat - r| ≤ |r| / 2 ^ 52 + 2 ^ (-1074 : ℤ) := by
  have e : (if decide (r.num < 0) = true then -1 else 1) * ((r.num.natAbs : ℚ) / r.den) = r := by
    conv_rhs => rw [← ite_natAbs_num_div_den r]
    split_ifs <;> ring
  have ha : |r| = (r.num.natAbs : ℚ) / r.den := by
    conv_lhs => rw [← e]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (r.num.natAbs : ℚ) / r.den)]
    split_ifs <;> simp
  rw [ha] at h ⊢
  have := isFinite_and_abs_toRat_ofRatioTrunc_sub_le (decide (r.num < 0)) r.num.natAbs r.den_nz h
  rwa [e] at this

/-! ### The test of the refinement -/

-- A rounding of `v` with `|v| ≤ 4 B` for `B ≤ 2 ^ 482` is finite, in the form for `linarith`,
-- which does not read the large powers of `2`.
private theorem IsRounding.isFinite_of_abs_le_four_mul {x : Double} {v : ℚ} (h : x.IsRounding v)
    {B : ℚ} (hB : B ≤ 2 ^ 482) (hv : |v| ≤ 4 * B) : x.isFinite = true := by
  refine h.isFinite_of_abs_le (n := 484) (by norm_num) (hv.trans ?_)
  rw [show 484 = 2 + 482 from rfl, pow_add, show (2 : ℚ) ^ 2 = 4 by norm_num]
  exact mul_le_mul_of_nonneg_left hB (by norm_num)

-- `|a| + |b| + 1.0` in doubles for finite `a` and `b` with `|a| + |b| ≤ B ≤ 2 ^ 482`: finite, and
-- between `(1 - 2 ^ (-52)) (|a| + |b| + 1)` and `2 (|a| + |b| + 1)`.
private theorem isFinite_and_toRat_fabs_add_fabs_add_one_mem {a b : Double}
    (ha : a.isFinite = true) (hb : b.isFinite = true) {B : ℚ} (hB : B ≤ 2 ^ 482) (hB1 : 1 ≤ B)
    (hab : |a.toRat| + |b.toRat| ≤ B) :
    (a.fabs + b.fabs + 1.0).isFinite = true ∧
      (|a.toRat| + |b.toRat| + 1) * (1 - 1 / 2 ^ 52) ≤ (a.fabs + b.fabs + 1.0).toRat ∧
      (a.fabs + b.fabs + 1.0).toRat ≤ 2 * (|a.toRat| + |b.toRat| + 1) := by
  have ht := two_zpow_neg_1075_le
  have ht0 : (0 : ℚ) < 2 ^ (-1075 : ℤ) := by positivity
  have h0 : 0 ≤ |a.toRat| + |b.toRat| := by positivity
  have hs := isRounding_add ((isFinite_fabs a).trans ha) ((isFinite_fabs b).trans hb)
  rw [toRat_fabs, toRat_fabs] at hs
  have hsf := hs.isFinite_of_abs_le_four_mul hB (by rw [abs_of_nonneg h0]; linarith)
  obtain ⟨s1, s2⟩ := abs_sub_le_iff.mp (hs.abs_sub_le hsf)
  rw [abs_of_nonneg h0] at s1 s2
  have hs0 := hs.nonneg hsf h0
  have hu := isRounding_add hsf isFinite_one
  rw [toRat_one] at hu
  have huf := hu.isFinite_of_abs_le_four_mul hB (by rw [abs_of_nonneg (by linarith)]; linarith)
  obtain ⟨u1, u2⟩ := abs_sub_le_iff.mp (hu.abs_sub_le huf)
  rw [abs_of_nonneg (by linarith)] at u1 u2
  exact ⟨huf, by linarith, by linarith⟩

-- The right side of the test of the refinement of `sturm_isolate`, `2 ^ (-41) (|a| + |b| + 1)` in
-- doubles, for finite `a` and `b` with `|a| + |b| ≤ B ≤ 2 ^ 482`: finite, and at least
-- `(2 ^ (-41) - 2 ^ (-90)) (|a| + |b| + 1)`.
private theorem isFinite_and_le_toRat_mul_fabs_add_fabs_add_one {a b : Double}
    (ha : a.isFinite = true) (hb : b.isFinite = true) {B : ℚ} (hB : B ≤ 2 ^ 482) (hB1 : 1 ≤ B)
    (hab : |a.toRat| + |b.toRat| ≤ B) :
    (0.5 * ldexp 1.0 (-40) * (a.fabs + b.fabs + 1.0)).isFinite = true ∧
      (|a.toRat| + |b.toRat| + 1) * (1 / 2 ^ 41 - 1 / 2 ^ 90) ≤
        (0.5 * ldexp 1.0 (-40) * (a.fabs + b.fabs + 1.0)).toRat := by
  obtain ⟨huf, u1, u2⟩ := isFinite_and_toRat_fabs_add_fabs_add_one_mem ha hb hB hB1 hab
  have hc : (0.5 * ldexp 1.0 (-40) : Double).isFinite = true := by decide +kernel
  have hc' : (0.5 * ldexp 1.0 (-40) : Double).toRat = 1 / 2 ^ 41 := by decide +kernel
  have hR := isRounding_mul hc huf
  rw [hc'] at hR
  have h0 : 0 ≤ |a.toRat| + |b.toRat| := by positivity
  have hu0 : 0 ≤ 1 / 2 ^ 41 * (a.fabs + b.fabs + 1.0).toRat := by
    refine mul_nonneg (by norm_num) ?_
    linarith
  have hRf := hR.isFinite_of_abs_le_four_mul hB (by rw [abs_of_nonneg hu0]; linarith)
  obtain ⟨-, r2⟩ := abs_sub_le_iff.mp (hR.abs_sub_le hRf)
  rw [abs_of_nonneg hu0] at r2
  exact ⟨hRf, by linarith [two_zpow_neg_1075_le]⟩

-- The test of the refinement of `sturm_isolate` for finite `a` and `b` with `|a| + |b| ≤ B ≤
-- 2 ^ 482` and `b - a ≤ 2 ^ (-42) + 2 ^ (-50) (|a| + |b|)`.
private theorem sub_le_mul_fabs_add_fabs_add_one {a b : Double} (ha : a.isFinite = true)
    (hb : b.isFinite = true) {B : ℚ} (hB : B ≤ 2 ^ 482) (hB1 : 1 ≤ B)
    (hab : |a.toRat| + |b.toRat| ≤ B)
    (h : b.toRat - a.toRat ≤ 1 / 2 ^ 42 + (|a.toRat| + |b.toRat|) / 2 ^ 50) :
    b - a ≤ 0.5 * ldexp 1.0 (-40) * (a.fabs + b.fabs + 1.0) := by
  obtain ⟨hRf, hR⟩ := isFinite_and_le_toRat_mul_fabs_add_fabs_add_one ha hb hB hB1 hab
  have hd := isRounding_sub hb ha
  have hv : |b.toRat - a.toRat| ≤ |a.toRat| + |b.toRat| := by
    rw [add_comm]; exact abs_sub _ _
  have hdf := hd.isFinite_of_abs_le_four_mul hB (by linarith)
  obtain ⟨d1, -⟩ := abs_sub_le_iff.mp (hd.abs_sub_le hdf)
  rw [le_iff_toRat_le hdf hRf]
  linarith [two_zpow_neg_1075_le, abs_nonneg a.toRat, abs_nonneg b.toRat]

-- The truncations `L` and `H` of the ends of an interval `(lo, hi]` within `±2 ^ 480` of a width
-- of at most `2 ^ (-43)`: finite, with `|L| + |H| ≤ 2 ^ 482` and
-- `H - L ≤ 2 ^ (-42) + 2 ^ (-50) (|L| + |H|)`.
private theorem isFinite_mpqGetD_and_toRat_sub_le {lo hi : ℚ} (hlo : -2 ^ 480 ≤ lo)
    (hhi : hi ≤ 2 ^ 480) (hlt : lo < hi) (h : (hi - lo) * 2 ^ 43 ≤ 1) :
    (mpqGetD lo).isFinite = true ∧ (mpqGetD hi).isFinite = true ∧
      |(mpqGetD lo).toRat| + |(mpqGetD hi).toRat| ≤ 2 ^ 482 ∧
      (mpqGetD hi).toRat - (mpqGetD lo).toRat ≤
        1 / 2 ^ 42 + (|(mpqGetD lo).toRat| + |(mpqGetD hi).toRat|) / 2 ^ 50 := by
  have hal : |lo| ≤ 2 ^ 480 := abs_le.mpr ⟨hlo, (hlt.trans_le hhi).le⟩
  have hah : |hi| ≤ 2 ^ 480 := abs_le.mpr ⟨hlo.trans hlt.le, hhi⟩
  have hB : (2 : ℚ) ^ 480 < 2 ^ 1024 := pow_lt_pow_right₀ one_lt_two (by norm_num)
  obtain ⟨fl, el⟩ := isFinite_mpqGetD_and_abs_toRat_sub_le (hal.trans_lt hB)
  obtain ⟨fh, eh⟩ := isFinite_mpqGetD_and_abs_toRat_sub_le (hah.trans_lt hB)
  obtain ⟨l1, l2⟩ := abs_sub_le_iff.mp el
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp eh
  have a1 := abs_sub_abs_le_abs_sub (mpqGetD lo).toRat lo
  have a2 := abs_sub_abs_le_abs_sub lo (mpqGetD lo).toRat
  have a3 := abs_sub_abs_le_abs_sub (mpqGetD hi).toRat hi
  have a4 := abs_sub_abs_le_abs_sub hi (mpqGetD hi).toRat
  rw [abs_sub_comm] at a2 a4
  have ht := two_zpow_neg_1074_le
  have hB1 : (1 : ℚ) ≤ 2 ^ 480 := one_le_pow₀ one_le_two
  rw [show 482 = 2 + 480 from rfl, pow_add, show (2 : ℚ) ^ 2 = 4 by norm_num]
  clear hB
  generalize (2 : ℚ) ^ 480 = B at *
  exact ⟨fl, fh, by linarith, by linarith⟩

/-- The test of the refinement of `sturm_isolate`, `d ≤ 2 ^ (-41) (s + 1)` for the difference `d`
and the sum `s` of the absolute values of the truncations of the ends to doubles, holds for an
interval `(lo, hi]` within `±2 ^ 480` of a width of at most `2 ^ (-43)`: the truncations move the
ends by less than `2 ^ (-52)` times their absolute values, and the roundings of the operations by
less than a unit in their last places. -/
theorem mpqGetD_sub_mpqGetD_le {lo hi : ℚ} (hlo : -2 ^ 480 ≤ lo) (hhi : hi ≤ 2 ^ 480)
    (hlt : lo < hi) (h : (hi - lo) * 2 ^ 43 ≤ 1) :
    mpqGetD hi - mpqGetD lo ≤
      0.5 * ldexp 1.0 (-40) * ((mpqGetD lo).fabs + (mpqGetD hi).fabs + 1.0) := by
  obtain ⟨fl, fh, hab, hd⟩ := isFinite_mpqGetD_and_toRat_sub_le hlo hhi hlt h
  exact sub_le_mul_fabs_add_fabs_add_one fl fh le_rfl (one_le_pow₀ one_le_two) hab hd

end Double

end JPoints

end
