/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants
public import JPoints.Model.DoubleArith
public import JPoints.Proof.Double
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Set.Defs

import JPoints.Proof.Constants
import JPoints.Proof.Rounding
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Field

/-!
# The arithmetic of the doubles of the model

The operations on doubles of `JPoints.Model.DoubleArith` round as IEEE 754 rounds to nearest: the
result of `+`, `-`, `*` and `/` on finite doubles, and the conversion `(double)n` of an integer, is
a rounding of the exact result (`JPoints.Double.IsRounding`): no NaN, finite below `2 ^ 1022`, of
the sign of the exact result, and within half a unit in its last place, `2 ^ (-53)` times the exact
result in the normal range and `2 ^ (-1075)` in the subnormal one (`JPoints.Double.isRounding_add`,
`JPoints.Double.isRounding_sub`, `JPoints.Double.isRounding_mul`, `JPoints.Double.isRounding_div`,
`JPoints.Double.isRounding_ofInt`), from the roundings of `JPoints.Double.ofDyadic` and
`JPoints.Double.ofRatio` (`JPoints.Double.isRounding_ofDyadic`,
`JPoints.Double.isRounding_ofRatio`); `(double)n` is exact for `|n| < 2 ^ 53`
(`JPoints.Double.isFinite_ofInt_and_toRat`) and `floor` for every finite double
(`JPoints.Double.isFinite_floor_and_toRat`).

The operations on the other doubles as the C code meets them: a NaN operand gives a NaN of its sign
(`JPoints.Double.isNaN_propagateNaN`, `JPoints.Double.signBit_propagateNaN`), an infinity times a
finite double other than a zero, or plus a finite double, is the infinity
(`JPoints.Double.mul_of_isInf`, `JPoints.Double.mul_of_isInf_right`,
`JPoints.Double.add_of_isInf_left`, `JPoints.Double.add_of_isInf_right`), and an infinite sum of
finite doubles is the infinity of the sign of the exact sum
(`JPoints.Double.doubleValue_add_of_isFinite_eq_false`). Sums, products and quotients of doubles
without a sign bit have none (`JPoints.Double.signBit_add`, `JPoints.Double.signBit_mul`,
`JPoints.Double.signBit_div`), so that the NaNs and the doubles without a sign bit
(`JPoints.Double.IsPlus`) are closed under them, and so are the doubles without a sign bit that are
no NaN (`JPoints.Double.IsNonneg`) under sums and products by finite doubles other than zeros. The
rounding is monotone (`JPoints.Double.le_doubleValue_ofDyadic`,
`JPoints.Double.le_doubleValue_ofRatio`), so that a NaN or a double at least `1` divided by a
positive double at most `2 ^ 24` is not a zero (`JPoints.Double.div_beq_zero_eq_false`).

Two computations in doubles whose results the search reads as integers. `⌊√H⌋`, as
`floor(sqrt(height))` computes it for `find_double_points` and `find_points`, is the integer square
root of the height bound (`JPoints.Double.toInt_toInt64_floor_sqrt_ofInt`): `H` is exact as a
double, and the square root, rounded to nearest by `sqrtsd` from the integer square root of the
significand scaled by `4 ^ u`, the integer square root rounded up when the remainder exceeds it,
never reaches the next integer. The number of the full periods of `walk_parts`,
`(long)((double)(k p) * invp + 0.5)` with `invp = 1.0 / p`, is `k`
(`JPoints.Double.toInt_toInt64_ofInt_mul_one_div_add_half`): the two roundings move `k + 1 / 2` by
far less than `1 / 2`. The quotient of `row_setup`, `(long)((double)d * invp)`, is `⌊d / p⌋` or one
less (`JPoints.Double.toInt_toInt64_ofInt_mul_one_div_mem_Icc`), so that one correction gives the
residue `d mod p`.

## Main definitions

* `JPoints.Double.IsRounding`: a double rounded from a rational number to nearest.
* `JPoints.Double.IsPlus`, `JPoints.Double.IsNonneg`: a NaN or a double without a sign bit, and a
  double without a sign bit that is no NaN.

## Main statements

* `JPoints.Double.isRounding_ofDyadic`, `JPoints.Double.isRounding_ofRatio`: the roundings of
  the model.
* `JPoints.Double.isRounding_add`, `JPoints.Double.isRounding_sub`,
  `JPoints.Double.isRounding_mul`, `JPoints.Double.isRounding_div`,
  `JPoints.Double.isRounding_ofInt`: the operations.
* `JPoints.Double.isFinite_ofInt_and_toRat`, `JPoints.Double.isFinite_floor_and_toRat`: the exact
  conversion of an integer and `floor`.
* `JPoints.Double.mul_of_isInf`, `JPoints.Double.mul_of_isInf_right`,
  `JPoints.Double.add_of_isInf_left`, `JPoints.Double.add_of_isInf_right`,
  `JPoints.Double.doubleValue_add_of_isFinite_eq_false`: the operations with infinities.
* `JPoints.Double.signBit_add`, `JPoints.Double.signBit_mul`, `JPoints.Double.signBit_div`: the
  operations on doubles without a sign bit.
* `JPoints.Double.le_doubleValue_ofDyadic`, `JPoints.Double.le_doubleValue_ofRatio`: the rounding
  is monotone.
* `JPoints.Double.div_beq_zero_eq_false`: a quotient that is not a zero.
* `JPoints.Double.sqrt_assemble`: `sqrt` of a normal positive double, by its bits.
* `JPoints.Double.toInt_toInt64_floor_sqrt_ofInt`: `⌊√H⌋` in doubles.
* `JPoints.Double.toInt_toInt64_ofInt_mul_one_div_add_half`,
  `JPoints.Double.toInt_toInt64_ofInt_mul_one_div_mem_Icc`: the quotients by a reciprocal.

## Implementation notes

The error bound is that of rounding to nearest, half a unit in the last place, which
`JPoints.Double.ofDyadic_rounding` and `JPoints.Double.ofRatio_rounding` give for the significand
before the bits are assembled; the rule of the ties is not needed. It is stated as
`|x - v| ≤ |v| / 2 ^ 53 + 2 ^ (-1075)`, a form that `linarith` reads, with the error in the
subnormal range as a power with an integer exponent that it keeps as an atom; the large powers of
`2`, which it cannot read, stay out of its arguments
(`JPoints.Double.IsRounding.isFinite_of_abs_le`). The facts about the floating literals of the model
are decided by the kernel.
-/

@[expose] public section

namespace JPoints

/-! ### Facts on numbers -/

/-- The error `2 ^ (-1075)` of the rounding in the subnormal range, bounded by a power that
`linarith` reads. -/
theorem two_zpow_neg_1075_le : (2 : ℚ) ^ (-1075 : ℤ) ≤ 1 / 2 ^ 200 := by
  rw [← zpow_natCast, one_div, ← zpow_neg]
  exact zpow_le_zpow_right₀ one_le_two (by norm_num)

/-- The signed magnitude of an integer: `s` times `t` as its sign `±1` (`b` the sign of a nonzero
`s`) times its absolute value times `t`. -/
theorem ite_mul_natAbs {s : ℤ} {b : Bool} (hb : s ≠ 0 → b = decide (s < 0)) (t : ℚ) :
    (if b then -1 else 1) * ((s.natAbs : ℚ) * t) = s * t := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp
  rw [hb h0, Nat.cast_natAbs, Int.cast_abs]
  rcases lt_or_gt_of_ne h0 with h | h
  · simp [h, abs_of_neg (Int.cast_lt_zero.mpr h)]
  · simp [show ¬s < 0 by lia, abs_of_pos (Int.cast_pos.mpr h)]

namespace Double

/-! ### Roundings -/

/-- `x` is a rounding of the rational number `v` to a double such as the operations of IEEE 754
make in the rounding mode to nearest: no NaN, finite for `|v| < 2 ^ 1022`, and, when finite, of the
sign of `v` and within `|v| / 2 ^ 53 + 2 ^ (-1075)` of it, half a unit in the last place of a
normal double or of a subnormal one. -/
structure IsRounding (x : Double) (v : ℚ) : Prop where
  /-- The rounding is no NaN. -/
  isNaN_eq_false : x.isNaN = false
  /-- The rounding of a `v` below `2 ^ 1022` in absolute value is finite. -/
  isFinite_of_abs_lt : |v| < 2 ^ 1022 → x.isFinite = true
  /-- A finite rounding of a `v ≥ 0` is not negative. -/
  nonneg : x.isFinite = true → 0 ≤ v → 0 ≤ x.toRat
  /-- A finite rounding of a `v ≤ 0` is not positive. -/
  nonpos : x.isFinite = true → v ≤ 0 → x.toRat ≤ 0
  /-- A finite rounding lies within half a unit in its last place of `v`. -/
  abs_sub_le : x.isFinite = true → |x.toRat - v| ≤ |v| / 2 ^ 53 + 2 ^ (-1075 : ℤ)

theorem IsRounding.of_toRat_eq {x : Double} {v : ℚ} (hx : x.isFinite = true) (h : x.toRat = v) :
    x.IsRounding v :=
  ⟨isNaN_eq_false_of_isFinite hx, fun _ ↦ hx, fun _ ↦ h ▸ id, fun _ ↦ h ▸ id,
    fun _ ↦ by rw [h, sub_self, abs_zero]; positivity⟩

/-- A rounding of `v` with `|v| ≤ 2 ^ n` for some `n < 1022` is finite: the form of
`JPoints.Double.IsRounding.isFinite_of_abs_lt` for an `n` whose power `linarith` reads. -/
theorem IsRounding.isFinite_of_abs_le {x : Double} {v : ℚ} (h : x.IsRounding v) {n : ℕ}
    (hn : n < 1022) (hv : |v| ≤ 2 ^ n) : x.isFinite = true :=
  h.isFinite_of_abs_lt (hv.trans_lt (pow_lt_pow_right₀ one_lt_two hn))

theorem IsRounding.abs_toRat_le {x : Double} {v : ℚ} (h : x.IsRounding v)
    (hf : x.isFinite = true) : |x.toRat| ≤ 2 * |v| + 1 := by
  have h1 := h.abs_sub_le hf
  have h2 := abs_sub_abs_le_abs_sub x.toRat v
  linarith [two_zpow_neg_1075_le, abs_nonneg v]

theorem IsRounding.half_le_toRat {x : Double} {v : ℚ} (h : x.IsRounding v)
    (hf : x.isFinite = true) (hv : 1 ≤ v) : v / 2 ≤ x.toRat := by
  have he := h.abs_sub_le hf
  rw [abs_of_pos (show (0 : ℚ) < v by linarith), abs_le] at he
  linarith [two_zpow_neg_1075_le]

theorem IsRounding.toRat_le_half {x : Double} {v : ℚ} (h : x.IsRounding v)
    (hf : x.isFinite = true) (hv : v ≤ -1) : x.toRat ≤ v / 2 := by
  have he := h.abs_sub_le hf
  rw [abs_of_neg (show v < 0 by linarith), abs_le] at he
  linarith [two_zpow_neg_1075_le]

/-! ### The roundings of `ofDyadic` and `ofRatio` -/

/-- The value `±M 2 ^ q` of the finite double of a significand `M ≤ 2 ^ 53` and the exponent
`q ≥ -1074` of its last place, `q` the least exponent for a subnormal `M < 2 ^ 52`. -/
theorem toRat_ofSignificand {neg : Bool} {M : ℕ} {q : ℤ} (hM : M ≤ 2 ^ 53) (hq : -1074 ≤ q)
    (hsub : M < 2 ^ 52 → q = -1074) (hf : (ofSignificand neg M q).isFinite = true) :
    (ofSignificand neg M q).toRat = (if neg then -1 else 1) * ((M : ℚ) * 2 ^ q) := by
  rcases hM.lt_or_eq with hM | rfl
  · rw [ofSignificand_of_ne q hM.ne] at hf ⊢
    have := (isFinite_assemble_iff hM).mp hf
    exact toRat_assemble hM hsub fun _ ↦ ⟨hq, by lia⟩
  · rw [ofSignificand_two_pow] at hf ⊢
    have := (isFinite_assemble_iff (by norm_num)).mp hf
    rw [toRat_assemble (by norm_num) (by norm_num) fun _ ↦ ⟨by lia, by lia⟩,
      zpow_add_one₀ two_ne_zero]
    push_cast; ring

theorem signBit_ofSignificand (neg : Bool) {M : ℕ} (q : ℤ) (hM : M ≤ 2 ^ 53) :
    (ofSignificand neg M q).signBit = neg := by
  rcases hM.lt_or_eq with hM | rfl
  · rw [ofSignificand_of_ne q hM.ne]; exact (fields_assemble neg q hM).1
  · rw [ofSignificand_two_pow]; exact (fields_assemble neg _ (by norm_num)).1

-- Half a unit `2 ^ (q - 1)` in the last place of a double rounded from `v > 0`, where
-- `2 ^ (q + 52) ≤ v` unless `q = -1074`, is at most `v / 2 ^ 53 + 2 ^ (-1075)`.
private theorem two_zpow_sub_one_le {q : ℤ} {v : ℚ} (hv : 0 < v) (hq : -1074 ≤ q)
    (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v) :
    (2 : ℚ) ^ (q - 1) ≤ v / 2 ^ 53 + 2 ^ (-1075 : ℤ) := by
  have h1 : (0 : ℚ) < 2 ^ (-1075 : ℤ) := by positivity
  rcases hq.lt_or_eq with hq | rfl
  · have h : (2 : ℚ) ^ (q - 1) = 2 ^ (q + 52) / 2 ^ 53 := by
      rw [← zpow_natCast, ← zpow_sub₀ two_ne_zero]; ring_nf
    have := div_le_div_of_nonneg_right (hnorm hq) (by positivity : (0 : ℚ) ≤ 2 ^ 53)
    linarith
  · rw [show (-1074 : ℤ) - 1 = -1075 by norm_num]
    exact le_add_of_nonneg_left (by positivity)

-- A positive `v` below `2 ^ 1022` is rounded with an exponent `q < 970` of the last place.
private theorem add_lt_of_two_zpow_le_of_lt {q : ℤ} {v : ℚ}
    (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v) (h : v < 2 ^ 1022) : q + 1076 < 2046 := by
  by_contra hq
  have h1 := (hnorm (by lia)).trans_lt h
  rw [← zpow_natCast, zpow_lt_zpow_iff_right₀ one_lt_two] at h1
  lia

/-- The double of a significand `M ≤ 2 ^ 53` rounded from `v > 0` to within half a unit of the
exponent `q ≥ -1074` of its last place, with `v ≥ 2 ^ (q + 52)` unless `q` is the least exponent,
is a rounding of `±v`: the facts that `JPoints.Double.ofDyadic_rounding` and
`JPoints.Double.ofRatio_rounding` give. -/
theorem isRounding_ofSignificand {neg : Bool} {M : ℕ} {q : ℤ} {v : ℚ} (hv : 0 < v)
    (hM : M ≤ 2 ^ 53) (hq : -1074 ≤ q) (hlo : M * 2 ^ q - 2 ^ (q - 1) ≤ v)
    (hhi : v ≤ M * 2 ^ q + 2 ^ (q - 1)) (hnorm : -1074 < q → 2 ^ (q + 52) ≤ v) :
    (ofSignificand neg M q).IsRounding ((if neg then -1 else 1) * v) := by
  have hsub (h : M < 2 ^ 52) := eq_of_lt_of_two_zpow_le h hhi hnorm hq
  have habs : |(if neg then -1 else 1) * v| = v := by
    rw [abs_mul, abs_of_pos hv, abs_ite_neg_one_one, one_mul]
  have hhalf := two_zpow_sub_one_le hv hq hnorm
  refine ⟨isNaN_ofSignificand neg q hM, fun h ↦ ?_, fun hf h0 ↦ ?_, fun hf h0 ↦ ?_, fun hf ↦ ?_⟩
  · exact isFinite_ofSignificand hM (add_lt_of_two_zpow_le_of_lt hnorm (habs ▸ h))
  · rw [toRat_ofSignificand hM hq hsub hf]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; positivity
    · simp only [↓reduceIte] at h0; linarith
  · rw [toRat_ofSignificand hM hq hsub hf]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte] at h0; linarith
    · simp only [↓reduceIte, neg_mul, one_mul, neg_nonpos]; positivity
  · rw [toRat_ofSignificand hM hq hsub hf, habs, ← mul_sub, abs_mul, abs_ite_neg_one_one, one_mul,
      abs_sub_le_iff]
    constructor <;> linarith

theorem ofDyadic_zero (neg : Bool) (e : ℤ) :
    ofDyadic neg 0 e = ⟨if neg then 0x8000000000000000 else 0⟩ := by
  simp [ofDyadic]

theorem ofRatio_zero (neg : Bool) (d : ℕ) :
    ofRatio neg 0 d = ⟨if neg then 0x8000000000000000 else 0⟩ := by
  simp [ofRatio]

/-- `JPoints.Double.ofDyadic` rounds `±m 2 ^ e` to nearest. -/
theorem isRounding_ofDyadic (neg : Bool) (m : ℕ) (e : ℤ) :
    (ofDyadic neg m e).IsRounding ((if neg then -1 else 1) * ((m : ℚ) * 2 ^ e)) := by
  by_cases hm : m = 0
  · subst hm
    rw [ofDyadic_zero, Nat.cast_zero, zero_mul, mul_zero]
    exact .of_toRat_eq (by cases neg <;> decide) (by cases neg <;> decide +kernel)
  obtain ⟨hM, hq, hlo, hhi, hnorm⟩ := ofDyadic_rounding hm e
  rw [ofDyadic_eq e hm]
  exact isRounding_ofSignificand (by positivity) hM hq hlo hhi hnorm

/-- `JPoints.Double.ofRatio` rounds `±n / d` to nearest. -/
theorem isRounding_ofRatio (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (ofRatio neg n d).IsRounding ((if neg then -1 else 1) * ((n : ℚ) / d)) := by
  by_cases hn : n = 0
  · subst hn
    rw [ofRatio_zero, Nat.cast_zero, zero_div, mul_zero]
    exact .of_toRat_eq (by cases neg <;> decide) (by cases neg <;> decide +kernel)
  obtain ⟨hM, hq, hlo, hhi, hnorm⟩ := ofRatio_rounding hn hd
  rw [ofRatio_eq d hn]
  exact isRounding_ofSignificand (by positivity) hM hq hlo hhi hnorm

theorem signBit_ofDyadic (neg : Bool) (m : ℕ) (e : ℤ) : (ofDyadic neg m e).signBit = neg := by
  by_cases hm : m = 0
  · subst hm; rw [ofDyadic_zero]; cases neg <;> decide
  · rw [ofDyadic_eq e hm]; exact signBit_ofSignificand neg _ (ofDyadic_rounding hm e).1

theorem signBit_ofInt (n : ℤ) : (ofInt n).signBit = decide (n < 0) := signBit_ofDyadic ..

theorem signBit_ofInt_of_nonneg {n : ℤ} (hn : 0 ≤ n) : (ofInt n).signBit = false := by
  rw [signBit_ofInt, decide_eq_false_iff_not]; lia

theorem signBit_ofRatio (neg : Bool) (n : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (ofRatio neg n d).signBit = neg := by
  by_cases hn : n = 0
  · subst hn; simp only [ofRatio, ↓reduceIte]; cases neg <;> decide
  · rw [ofRatio_eq d hn]; exact signBit_ofSignificand neg _ (ofRatio_rounding hn hd).1

/-- The rounding of `JPoints.Double.ofDyadic` is monotone: a double `T` not above `m 2 ^ e` is not
above its rounding, by the faithful rounding (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`)
when that is finite. -/
theorem le_doubleValue_ofDyadic {T : Double} (hT : T.isNaN = false) {m : ℕ} (hm : m ≠ 0) (e : ℤ)
    (h : doubleValue T.bits ≤ ((m * 2 ^ e : ℚ) : WithBotTop ℚ)) :
    doubleValue T.bits ≤ doubleValue (ofDyadic false m e).bits := by
  have hr := isNaN_ofDyadic false m e
  cases hf : (ofDyadic false m e).isFinite
  · rw [doubleValue_eq_top (signBit_ofDyadic ..) hf]; exact le_top
  · exact le_of_lt_nextUp hr hT (ne_huge_of_isFinite hf).1
      (h.trans_lt (by simpa using (lt_nextUp_and_nextDown_lt_ofDyadic hm hf).1))

/-- The rounding of `JPoints.Double.ofRatio` is monotone: a double `T` not above `n / d` is not
above its rounding, by the faithful rounding (`JPoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`)
when that is finite. -/
theorem le_doubleValue_ofRatio {T : Double} (hT : T.isNaN = false) {n d : ℕ} (hn : n ≠ 0)
    (hd : d ≠ 0) (h : doubleValue T.bits ≤ ((n / d : ℚ) : WithBotTop ℚ)) :
    doubleValue T.bits ≤ doubleValue (ofRatio false n d).bits := by
  have hr := isNaN_ofRatio false n hd
  cases hf : (ofRatio false n d).isFinite
  · rw [doubleValue_eq_top (signBit_ofRatio _ _ hd) hf]; exact le_top
  · exact le_of_lt_nextUp hr hT (ne_huge_of_isFinite hf).1
      (h.trans_lt (by simpa using (lt_nextUp_and_nextDown_lt_ofRatio hn hd hf).1))

/-! ### Quiet NaNs -/

theorem expField_quiet (x : Double) : x.quiet.expField = x.expField := by
  rw [expField_eq, expField_eq]
  simp only [quiet, UInt64.toNat_or]
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib]
  norm_num

/-- Quieting a double of the largest exponent field, a NaN or an infinity, gives a NaN. -/
theorem isNaN_quiet {x : Double} (h : x.expField = 2047) : x.quiet.isNaN = true := by
  have hf : x.quiet.fracField ≠ 0 := by
    rw [fracField_eq]
    simp only [quiet, UInt64.toNat_or, show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 from rfl,
      Nat.or_mod_two_pow, show (2 : ℕ) ^ 51 % 2 ^ 52 = 2 ^ 51 by norm_num]
    have := Nat.right_le_or (n := x.bits.toNat % 2 ^ 52) (m := 2 ^ 51)
    lia
  simp [isNaN, expField_quiet, h, hf]

private theorem two_pow_63_le_or_iff {n : ℕ} : 2 ^ 63 ≤ n ||| 2 ^ 51 ↔ 2 ^ 63 ≤ n := by
  have h (m : ℕ) : 2 ^ 63 ≤ m ↔ 0 < m >>> 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_pos_iff]; simp
  rw [h, h, Nat.shiftRight_or_distrib, show (2 : ℕ) ^ 51 >>> 63 = 0 by decide, Nat.or_zero]

theorem signBit_quiet (x : Double) : x.quiet.signBit = x.signBit := by
  rw [signBit_eq_decide, signBit_eq_decide]
  simp only [quiet, UInt64.toNat_or, show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 from rfl]
  exact decide_eq_decide.mpr two_pow_63_le_or_iff

theorem isNaN_propagateNaN {x y : Double} (h : (x.isNaN || y.isNaN) = true) :
    (propagateNaN x y).isNaN = true := by
  rw [propagateNaN]
  split_ifs with hx
  · exact isNaN_quiet (expField_eq_of_isNaN hx)
  · exact isNaN_quiet (expField_eq_of_isNaN (by simpa [hx] using h))

theorem isFinite_propagateNaN {x y : Double} (h : (x.isNaN || y.isNaN) = true) :
    (propagateNaN x y).isFinite = false :=
  isFinite_eq_false_of_isNaN (isNaN_propagateNaN h)

theorem signBit_propagateNaN {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false) :
    (propagateNaN x y).signBit = false := by
  simp only [propagateNaN]
  split_ifs <;> rwa [signBit_quiet]

/-! ### The four operations and the conversion of an integer -/

-- The exact value `s 2 ^ e` of a sum of two dyadic numbers on the smaller exponent.
private theorem intCast_add_mul_zpow (mx my ex ey : ℤ) :
    ((mx * 2 ^ (ex - min ex ey).toNat + my * 2 ^ (ey - min ex ey).toNat : ℤ) : ℚ) *
      2 ^ min ex ey = mx * 2 ^ ex + my * 2 ^ ey := by
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by lia), Int.toNat_of_nonneg (by lia),
    add_mul, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
    sub_add_cancel, sub_add_cancel]

/-- The sum of two finite doubles is the double that `JPoints.Double.ofDyadic` rounds their exact
sum to, as `JPoints.Double.add` adds them on the smaller exponent; an exact sum `0` is the zero
with the sign that `JPoints.Double.add` gives it. -/
theorem exists_add_eq_ofDyadic {x y : Double} (hx : x.isFinite = true)
    (hy : y.isFinite = true) :
    ∃ (neg : Bool) (m : ℕ) (e : ℤ), x + y = ofDyadic neg m e ∧
      (if neg then -1 else 1) * ((m : ℚ) * 2 ^ e) = x.toRat + y.toRat := by
  have hvx := toRat_eq x
  have hvy := toRat_eq y
  rcases hdx : x.toDyadic with ⟨mx, ex⟩
  rcases hdy : y.toDyadic with ⟨my, ey⟩
  rw [hdx] at hvx
  rw [hdy] at hvy
  have hadd : x + y = ofDyadic
      (if mx * 2 ^ (ex - min ex ey).toNat + my * 2 ^ (ey - min ex ey).toNat = 0 then
        x.signBit && y.signBit
      else decide (mx * 2 ^ (ex - min ex ey).toNat + my * 2 ^ (ey - min ex ey).toNat < 0))
      (mx * 2 ^ (ex - min ex ey).toNat + my * 2 ^ (ey - min ex ey).toNat).natAbs (min ex ey) := by
    change add x y = _
    simp only [add, isNaN_eq_false_of_isFinite hx, isNaN_eq_false_of_isFinite hy,
      isInf_eq_false_of_isFinite hx, isInf_eq_false_of_isFinite hy, hdx, hdy, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte]
    by_cases h : mx * 2 ^ (ex - min ex ey).toNat + my * 2 ^ (ey - min ex ey).toNat = 0
    · rw [ite_eq_left h, ite_eq_left h, h, Int.natAbs_zero, ofDyadic_zero]
    · rw [ite_eq_right h, ite_eq_right h]
  refine ⟨_, _, _, hadd, ?_⟩
  rw [ite_mul_natAbs fun h ↦ ite_eq_right h, intCast_add_mul_zpow, hvx, hvy]

theorem isRounding_add {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (x + y).IsRounding (x.toRat + y.toRat) := by
  obtain ⟨neg, m, e, h, hv⟩ := exists_add_eq_ofDyadic hx hy
  rw [h, ← hv]
  exact isRounding_ofDyadic neg m e

/-- An infinity plus a double that is no NaN and, when infinite, of the same sign is the
infinity. -/
theorem add_of_isInf_of_signBit_eq {x y : Double} (hx : x.isInf = true) (hy : y.isNaN = false)
    (hs : y.isInf = true → y.signBit = x.signBit) : x + y = x := by
  change Double.add x y = x
  by_cases hyi : y.isInf = true
  · simp [Double.add, isNaN_eq_false_of_isInf hx, hy, hx, hyi, hs hyi]
  · simp [Double.add, isNaN_eq_false_of_isInf hx, hy, hx, hyi]

/-- An infinity plus a finite double is the infinity. -/
theorem add_of_isInf_left {x y : Double} (hx : x.isInf = true) (hy : y.isFinite = true) :
    x + y = x :=
  add_of_isInf_of_signBit_eq hx (isNaN_eq_false_of_isFinite hy)
    fun h ↦ absurd h (by simp [isInf_eq_false_of_isFinite hy])

/-- A finite double plus an infinity is the infinity. -/
theorem add_of_isInf_right {x y : Double} (hx : x.isFinite = true) (hy : y.isInf = true) :
    x + y = y := by
  change Double.add x y = y
  simp [Double.add, isNaN_eq_false_of_isFinite hx, isNaN_eq_false_of_isInf hy,
    isInf_eq_false_of_isFinite hx, hy]

/-- The value of an infinite sum of two finite doubles: the infinity of the sign of the exact
sum. -/
theorem doubleValue_add_of_isFinite_eq_false {x y : Double} (hx : x.isFinite = true)
    (hy : y.isFinite = true) (h : (x + y).isFinite = false) :
    doubleValue (x + y).bits = if x.toRat + y.toRat < 0 then ⊥ else ⊤ := by
  obtain ⟨neg, m, e, he, hv⟩ := exists_add_eq_ofDyadic hx hy
  rw [he] at h ⊢
  rw [doubleValue_of_isFinite_eq_false (isNaN_ofDyadic _ _ _) h, signBit_ofDyadic, ← hv]
  have hm : m ≠ 0 := by
    rintro rfl
    rw [ofDyadic_zero] at h
    cases neg <;> exact absurd h (by decide)
  have hp : (0 : ℚ) < m * 2 ^ e := by positivity
  cases neg <;> simp [hp, hp.le]

/-- The sum of two finite doubles whose exact sum is at most `-K`, `K ≥ 1`, is no NaN and at most
`-K / 2`, `-∞` included. -/
theorem doubleValue_add_le_of_le {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true)
    {K : ℚ} (hK : 1 ≤ K) (hv : x.toRat + y.toRat ≤ -K) :
    (x + y).isNaN = false ∧ doubleValue (x + y).bits ≤ ((-K / 2 : ℚ) : WithBotTop ℚ) := by
  have h := isRounding_add hx hy
  refine ⟨h.isNaN_eq_false, ?_⟩
  cases hr : (x + y).isFinite
  · rw [doubleValue_add_of_isFinite_eq_false hx hy hr, ite_eq_left (by linarith)]
    exact bot_le
  · rw [doubleValue_eq_toRat hr, WithBotTop.coe_le_coe]
    linarith [h.toRat_le_half hr (by linarith)]

/-- The sum of two finite doubles whose exact sum is at least `K ≥ 1` is no NaN and at least
`K / 2`, `+∞` included. -/
theorem le_doubleValue_add_of_le {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true)
    {K : ℚ} (hK : 1 ≤ K) (hv : K ≤ x.toRat + y.toRat) :
    (x + y).isNaN = false ∧ ((K / 2 : ℚ) : WithBotTop ℚ) ≤ doubleValue (x + y).bits := by
  have h := isRounding_add hx hy
  refine ⟨h.isNaN_eq_false, ?_⟩
  cases hr : (x + y).isFinite
  · rw [doubleValue_add_of_isFinite_eq_false hx hy hr, ite_eq_right (by linarith)]
    exact le_top
  · rw [doubleValue_eq_toRat hr, WithBotTop.coe_le_coe]
    linarith [h.half_le_toRat hr (by linarith)]

protected theorem sub_eq_add_neg {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x - y = x + y.neg := by
  change sub x y = _
  simp only [sub, hx, hy, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A double that is no NaN less an infinity with the sign bit clear is a NaN or `-∞`. -/
theorem isNaN_or_doubleValue_sub_of_isInf {x y : Double} (hx : x.isNaN = false)
    (hy : y.isInf = true) (hys : y.signBit = false) :
    (x - y).isNaN = true ∨ doubleValue (x - y).bits = ⊥ := by
  rw [Double.sub_eq_add_neg hx (isNaN_eq_false_of_isInf hy)]
  change (add x y.neg).isNaN = true ∨ doubleValue (add x y.neg).bits = ⊥
  have hi : y.neg.isInf = true := (isInf_neg y).trans hy
  have hn : y.neg.isNaN = false := isNaN_eq_false_of_isInf hi
  have hs : y.neg.signBit = true := by rw [signBit_neg, hys]; rfl
  by_cases hxi : x.isInf = true
  · cases hsx : x.signBit
    · left
      simp only [add, hx, hn, hxi, hi, hsx, hs, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte, Bool.bne_true, Bool.not_false, Bool.and_self]
      decide
    · right
      simp only [add, hx, hn, hxi, hi, hsx, hs, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte, bne_self_eq_false, Bool.and_false]
      rw [doubleValue_of_isInf hxi, hsx]; rfl
  · right
    simp only [add, hx, hn, hxi, hi, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rw [doubleValue_of_isInf hi, hs]; rfl

-- `x - s` for a finite `x` and an `s` that is a NaN is a NaN.
private theorem isNaN_sub_of_isNaN {x s : Double} (hx : x.isFinite = true) (hs : s.isNaN = true) :
    (x - s).isNaN = true := by
  have e : x - s = s.quiet := by
    change sub x s = _
    simp [sub, propagateNaN, isNaN_eq_false_of_isFinite hx, hs]
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq] at hs
  rw [e, isNaN_quiet hs.1]

/-- A double without a sign bit that some double is below when subtracted from a finite double is
finite: `x - NaN` is a NaN, `x - ∞` is `-∞`, and nothing is below either. -/
theorem isFinite_of_lt_sub {x s z : Double} (hx : x.isFinite = true) (hs : s.signBit = false)
    (h : z.lt (x - s) = true) : s.isFinite = true := by
  have hxn := isNaN_eq_false_of_isFinite hx
  have hn : (x - s).isNaN = false := by
    simp only [lt, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.2
  have hsn : s.isNaN = false := by
    by_contra hsn
    rw [isNaN_sub_of_isNaN hx (by simpa using hsn)] at hn
    exact absurd hn (by decide)
  cases hi : s.isInf
  · exact isFinite_of_isInf_eq_false hsn hi
  · have e : x - s = s.neg := by
      rw [Double.sub_eq_add_neg hxn hsn]
      change add x s.neg = _
      simp [add, hxn, isNaN_neg, hsn, isInf_eq_false_of_isFinite hx, isInf_neg, hi]
    rw [e] at h hn
    rw [lt_eq_true_iff (by simp_all [lt]) hn, doubleValue_of_isInf ((isInf_neg s).trans hi),
      signBit_neg, hs] at h
    simp at h

theorem isRounding_sub {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (x - y).IsRounding (x.toRat - y.toRat) := by
  rw [Double.sub_eq_add_neg (isNaN_eq_false_of_isFinite hx) (isNaN_eq_false_of_isFinite hy),
    sub_eq_add_neg, ← toRat_neg]
  exact isRounding_add hx ((isFinite_neg y).trans hy)

theorem ite_signBit_mul_abs_toRat (x : Double) :
    (if x.signBit then -1 else 1) * |x.toRat| = x.toRat := by
  have := sign_mul_natAbs_mul_zpow x 0
  rwa [add_zero, zpow_zero, mul_one, ← abs_toRat] at this

private theorem ite_bne_eq_mul (a b : Bool) :
    (if (a != b) = true then (-1 : ℚ) else 1) = (if a then -1 else 1) * (if b then -1 else 1) := by
  cases a <;> cases b <;> simp

theorem mul_eq_ofDyadic {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x * y = ofDyadic (x.signBit != y.signBit) (x.toDyadic.1.natAbs * y.toDyadic.1.natAbs)
      (x.toDyadic.2 + y.toDyadic.2) := by
  change mul x y = _
  simp only [mul, isNaN_eq_false_of_isFinite hx, isNaN_eq_false_of_isFinite hy,
    isInf_eq_false_of_isFinite hx, isInf_eq_false_of_isFinite hy, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]

/-- An infinity times a finite double other than a zero is the infinity of the sign of the
product. -/
theorem mul_of_isInf {x y : Double} (hx : x.isInf = true) (hy : y.isFinite = true)
    (hy0 : y.toRat ≠ 0) : x * y = if x.signBit != y.signBit then huge.neg else huge := by
  change mul x y = _
  simp only [mul, isNaN_eq_false_of_isInf hx, isNaN_eq_false_of_isFinite hy, hx,
    isZero_eq_false_of_isInf hx, isZero_eq_false_iff.mpr hy0, Bool.or_false, Bool.true_or,
    Bool.false_eq_true, ↓reduceIte]

/-- A finite double other than a zero times an infinity is the infinity of the sign of the
product. -/
theorem mul_of_isInf_right {x y : Double} (hx : x.isFinite = true) (hx0 : x.toRat ≠ 0)
    (hy : y.isInf = true) : x * y = if x.signBit != y.signBit then huge.neg else huge := by
  change mul x y = _
  simp only [mul, isNaN_eq_false_of_isInf hy, isNaN_eq_false_of_isFinite hx, hy,
    isZero_eq_false_of_isInf hy, isZero_eq_false_iff.mpr hx0, isInf_eq_false_of_isFinite hx,
    Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte]

theorem signBit_mul_of_isFinite {x y : Double} (hx : x.isFinite = true)
    (hy : y.isFinite = true) : (x * y).signBit = (x.signBit != y.signBit) := by
  rw [mul_eq_ofDyadic hx hy, signBit_ofDyadic]

/-- The value of the product of the magnitudes of two doubles with the exclusive or of their signs,
the exact product that `JPoints.Double.mul_eq_ofDyadic` rounds. -/
theorem ite_bne_mul_natAbs_mul_zpow (x y : Double) :
    (if (x.signBit != y.signBit) = true then -1 else 1) *
        (((x.toDyadic.1.natAbs * y.toDyadic.1.natAbs : ℕ) : ℚ) *
          2 ^ (x.toDyadic.2 + y.toDyadic.2)) = x.toRat * y.toRat := by
  conv_rhs => rw [← ite_signBit_mul_abs_toRat x, ← ite_signBit_mul_abs_toRat y, abs_toRat,
    abs_toRat]
  rw [ite_bne_eq_mul, Nat.cast_mul, zpow_add₀ two_ne_zero]
  ring

theorem isRounding_mul {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (x * y).IsRounding (x.toRat * y.toRat) := by
  rw [mul_eq_ofDyadic hx hy, ← ite_bne_mul_natAbs_mul_zpow]
  exact isRounding_ofDyadic ..

-- The quotient of the magnitudes of two dyadic numbers, cleared of the power of `2`.
private theorem natCast_ite_div_natCast_ite (a b : ℕ) (e f : ℤ) (hb : b ≠ 0) :
    ((if 0 ≤ e - f then a * 2 ^ (e - f).toNat else a : ℕ) : ℚ) /
        ((if 0 ≤ e - f then b else b * 2 ^ (-(e - f)).toNat : ℕ) : ℚ) =
      (a * 2 ^ e) / (b * 2 ^ f) := by
  have hb' : (b : ℚ) ≠ 0 := mod_cast hb
  split_ifs with h
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg h, zpow_sub₀ two_ne_zero]
    field
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), neg_sub, zpow_sub₀ two_ne_zero]
    field

theorem div_eq_ofRatio {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hy0 : y.toRat ≠ 0) :
    x / y = ofRatio (x.signBit != y.signBit)
      (if 0 ≤ x.toDyadic.2 - y.toDyadic.2 then
        x.toDyadic.1.natAbs * 2 ^ (x.toDyadic.2 - y.toDyadic.2).toNat else x.toDyadic.1.natAbs)
      (if 0 ≤ x.toDyadic.2 - y.toDyadic.2 then y.toDyadic.1.natAbs
        else y.toDyadic.1.natAbs * 2 ^ (-(x.toDyadic.2 - y.toDyadic.2)).toNat) := by
  change div x y = _
  simp only [div, isNaN_eq_false_of_isFinite hx, isNaN_eq_false_of_isFinite hy,
    isInf_eq_false_of_isFinite hx, isInf_eq_false_of_isFinite hy, isZero_eq_false_iff.mpr hy0,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

theorem isRounding_div {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hy0 : y.toRat ≠ 0) : (x / y).IsRounding (x.toRat / y.toRat) := by
  have hd : (if 0 ≤ x.toDyadic.2 - y.toDyadic.2 then y.toDyadic.1.natAbs
      else y.toDyadic.1.natAbs * 2 ^ (-(x.toDyadic.2 - y.toDyadic.2)).toNat) ≠ 0 := by
    have := natAbs_toDyadic_fst_ne_zero hy0
    split_ifs <;> positivity
  rw [div_eq_ofRatio hx hy hy0]
  convert isRounding_ofRatio _ _ hd using 1
  rw [ite_bne_eq_mul, natCast_ite_div_natCast_ite _ _ _ _ (natAbs_toDyadic_fst_ne_zero hy0),
    ← abs_toRat, ← abs_toRat]
  conv_lhs => rw [← ite_signBit_mul_abs_toRat x, ← ite_signBit_mul_abs_toRat y]
  split_ifs <;> ring

theorem isRounding_ofInt (n : ℤ) : (ofInt n).IsRounding n := by
  have h := isRounding_ofDyadic (decide (n < 0)) n.natAbs 0
  rwa [zpow_zero, ite_mul_natAbs fun _ ↦ rfl, mul_one] at h

theorem isFinite_ofInt_and_toRat {n : ℤ} (h : |n| < 2 ^ 53) :
    (ofInt n).isFinite = true ∧ (ofInt n).toRat = n := by
  rcases eq_or_ne n 0 with rfl | h0
  · exact ⟨by decide, by decide +kernel⟩
  have hn : n.natAbs < 2 ^ 53 := by rw [Int.abs_eq_natAbs] at h; lia
  have hl : (n.natAbs.log2 : ℤ) + 0 ≤ 1023 := by
    have := (Nat.log2_lt (by lia)).mpr hn
    lia
  obtain ⟨h1, -, h3⟩ := ofDyadic_exact (neg := decide (n < 0)) (Int.natAbs_ne_zero.mpr h0) hn
    (by norm_num) hl
  refine ⟨h1, ?_⟩
  change (ofDyadic _ _ _).toRat = _
  rw [h3, zpow_zero, ite_mul_natAbs fun _ ↦ rfl, mul_one]

theorem isNaN_ofInt (d : ℤ) : (ofInt d).isNaN = false := isNaN_ofDyadic ..

theorem isZero_ofInt_eq_false {d : ℤ} (hd : d ≠ 0) : (ofInt d).isZero = false :=
  isZero_ofDyadic_eq_false _ (Int.natAbs_ne_zero.mpr hd) (by lia)

theorem one_le_abs_toRat_ofInt {d : ℤ} (hd : d ≠ 0) (hf : (ofInt d).isFinite = true) :
    1 ≤ |(ofInt d).toRat| :=
  (one_le_zpow₀ one_le_two (by lia)).trans
    (two_pow_le_abs_toRat_ofDyadic _ (Int.natAbs_ne_zero.mpr hd) (by lia) hf)

/-! ### Signs -/

/-- A sum of doubles without a sign bit has no sign bit: the infinities are `+∞`, a NaN keeps the
sign of its operand, and the exact sum of finite operands is not negative. -/
theorem signBit_add {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false) :
    (x + y).signBit = false := by
  change (add x y).signBit = false
  simp only [add]
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact signBit_propagateNaN hx hy
  · simp [hx, hy] at h3
  · exact hx
  · exact hy
  · simp [hx] at h6
  · rfl
  · rw [signBit_ofDyadic, decide_eq_false_iff_not, not_lt]
    exact add_nonneg (mul_nonneg (toDyadic_fst_nonneg (toRat_nonneg hx)) (by positivity))
      (mul_nonneg (toDyadic_fst_nonneg (toRat_nonneg hy)) (by positivity))

/-- A product of doubles without a sign bit, one of them finite and not zero, has no sign bit. -/
theorem signBit_mul {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false)
    (h : x.isFinite = true ∧ x.isZero = false ∨ y.isFinite = true ∧ y.isZero = false) :
    (x * y).signBit = false := by
  change (mul x y).signBit = false
  simp only [mul, hx, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h1 h2 h3
  · exact signBit_propagateNaN hx hy
  · exfalso
    rcases h with ⟨hf, hz⟩ | ⟨hf, hz⟩ <;>
      simp_all [isInf_eq_false_of_isFinite, isZero_eq_false_of_isInf]
  · decide
  · exact signBit_ofDyadic ..

/-- A quotient of doubles without sign bits by a finite double that is not zero has no sign
bit. -/
theorem signBit_div {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false)
    (hyf : y.isFinite = true) (hy0 : y.isZero = false) : (x / y).signBit = false := by
  change (div x y).signBit = false
  have hd := natAbs_toDyadic_fst_ne_zero (isZero_eq_false_iff.mp hy0)
  simp only [div, hx, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    isInf_eq_false_of_isFinite hyf, hy0]
  split_ifs with h1 h2 h3
  · exact signBit_propagateNaN hx hy
  · decide
  · exact signBit_ofRatio _ _ hd
  · exact signBit_ofRatio _ _ (by positivity)

theorem signBit_foldl_add {β : Type*} {T : β → Double} {L : List β} {s : Double}
    (hs : s.signBit = false) (hT : ∀ t ∈ L, (T t).signBit = false) :
    (L.foldl (fun s t ↦ s + T t) s).signBit = false := by
  induction L generalizing s with
  | nil => exact hs
  | cons t L ih =>
    exact ih (signBit_add hs (hT t List.mem_cons_self)) fun t' ht' ↦
      hT t' (List.mem_cons_of_mem _ ht')

/-! ### Constants -/

theorem isFinite_zero : zero.isFinite = true := by decide

theorem toRat_zero : zero.toRat = 0 := by decide +kernel

theorem doubleValue_zero : doubleValue zero.bits = ((0 : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat isFinite_zero, toRat_zero]

theorem beq_zero_eq_false_of_le {x : Double} {c : ℚ} (hc : 0 < c) (hx : x.isNaN = false)
    (h : (c : WithBotTop ℚ) ≤ doubleValue x.bits) : x.beq zero = false := by
  rw [Bool.eq_false_iff, ne_eq, beq_eq_true_iff hx (by decide), doubleValue_zero]
  intro h'
  rw [h', WithBotTop.coe_le_coe] at h
  exact absurd h (not_le.2 hc)

theorem zero_lt_iff_toRat_pos {x : Double} (hx : x.isFinite = true) :
    (0.0 : Double).lt x = true ↔ 0 < x.toRat := by
  rw [← toRat_zero]
  exact lt_iff_toRat_lt isFinite_zero hx

/-- A double without a sign bit below `y` puts `0.0` below `y`. -/
theorem zero_lt_of_lt {z y : Double} (hz : z.signBit = false) (h : z.lt y = true) :
    (0.0 : Double).lt y = true := by
  obtain ⟨-, hyn, hlt⟩ := lt_eq_true_iff'.mp h
  rw [← isNaN_eq_false_iff] at hyn
  rw [show (0.0 : Double) = zero from rfl, lt_eq_true_iff (by decide) hyn,
    doubleValue_eq_toRat isFinite_zero, toRat_zero]
  refine lt_of_le_of_lt ?_ hlt
  rw [doubleValue_bits]
  split_ifs with h1 h2
  · simp_all
  · exact le_top
  · exact WithBotTop.coe_le_coe.mpr (toRat_nonneg hz)

theorem isFinite_one : (1.0 : Double).isFinite = true := by decide +kernel

theorem toRat_one : (1.0 : Double).toRat = 1 := by decide +kernel

theorem toDyadic_one : (1.0 : Double).toDyadic = (2 ^ 52, -52) := by decide

theorem doubleValue_one : doubleValue (1.0 : Double).bits = ((1 : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat isFinite_one, toRat_one]

/-- The value `2 ^ (-1074)` of the least subnormal `⟨1⟩`. -/
theorem doubleValue_one_bits : doubleValue (⟨1⟩ : Double).bits =
    (((2 : ℚ) ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat (by decide), toRat_eq, show (⟨1⟩ : Double).toDyadic = (1, -1074) by
    decide]
  simp

theorem isFinite_half : (0.5 : Double).isFinite = true := by decide +kernel

theorem toRat_half : (0.5 : Double).toRat = 1 / 2 := by decide +kernel

theorem toDyadic_half : (0.5 : Double).toDyadic = (2 ^ 52, -53) := by decide +kernel

theorem isFinite_thirtyTwo : (32.0 : Double).isFinite = true := by decide +kernel

theorem toDyadic_thirtyTwo : (32.0 : Double).toDyadic = (2 ^ 52, -47) := by decide +kernel

theorem toRat_one_e_neg_nine : (1.0e-9 : Double).toRat = 4835703278458517 / 2 ^ 82 := by
  decide +kernel

theorem isFinite_one_e_neg_nine : (1.0e-9 : Double).isFinite = true := by decide +kernel

/-! ### Doubles without a sign bit -/

/-- A NaN, or a double with the sign bit clear: `+0.0`, a positive double or `+∞`. Products,
quotients and sums of such doubles are such doubles (`JPoints.Double.IsPlus.mul`,
`JPoints.Double.IsPlus.div`, `JPoints.Double.IsPlus.add`). -/
abbrev IsPlus (x : Double) : Prop := x.isNaN = true ∨ x.signBit = false

theorem isPlus_ofInt_natCast (n : ℕ) : (ofInt n).IsPlus :=
  .inr (signBit_ofInt_of_nonneg (Int.natCast_nonneg n))

theorem IsPlus.mul {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x * y).IsPlus := by
  change (Double.mul x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.mul, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  have hxs : x.signBit = false := hx.resolve_left fun h ↦ h1 (by simp [h])
  have hys : y.signBit = false := hy.resolve_left fun h ↦ h1 (by simp [h])
  simp only [Double.mul, h1, Bool.false_eq_true, ↓reduceIte, hxs, hys, bne_self_eq_false]
  split_ifs
  · exact .inl (by decide)
  · exact .inr (by decide)
  · generalize x.toDyadic = dx
    generalize y.toDyadic = dy
    obtain ⟨mx, ex⟩ := dx
    obtain ⟨my, ey⟩ := dy
    exact .inr (signBit_ofDyadic ..)

theorem IsPlus.div {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x / y).IsPlus := by
  change (Double.div x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.div, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  have hxs : x.signBit = false := hx.resolve_left fun h ↦ h1 (by simp [h])
  have hys : y.signBit = false := hy.resolve_left fun h ↦ h1 (by simp [h])
  obtain ⟨my, hmy, hry⟩ := exists_toDyadic_eq_natCast hys
  generalize y.toDyadic.2 = ey at hmy hry
  have hmy0 (h : ¬y.isZero = true) : my ≠ 0 := by
    rintro rfl; exact isZero_eq_false_iff.mp (Bool.eq_false_iff.mpr h) (by simp [hry])
  simp only [Double.div, h1, hxs, hys, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hmy,
    Int.natAbs_natCast]
  split_ifs
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact .inr (by decide)
  · exact .inl (by decide)
  · exact .inr (by decide)
  · exact .inr (signBit_ofRatio _ _ (hmy0 ‹_›))
  · exact .inr (signBit_ofRatio _ _ (Nat.mul_ne_zero (hmy0 ‹_›) (by positivity)))

theorem IsPlus.add {x y : Double} (hx : x.IsPlus) (hy : y.IsPlus) : (x + y).IsPlus := by
  change (Double.add x y).IsPlus
  by_cases h1 : (x.isNaN || y.isNaN) = true
  · simp only [Double.add, h1, ↓reduceIte]; exact .inl (isNaN_propagateNaN h1)
  exact .inr (signBit_add (hx.resolve_left fun h ↦ h1 (by simp [h]))
    (hy.resolve_left fun h ↦ h1 (by simp [h])))

-- The rounding of a natural number times a power of `2` that is at least `1` is at least `1`.
private theorem one_le_doubleValue_ofDyadic {s : ℤ} {N : ℕ} (hs : s = N) {e : ℤ}
    (h : (1 : ℚ) ≤ N * 2 ^ e) :
    ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue (ofDyadic (decide (s < 0)) s.natAbs e).bits := by
  subst hs
  rw [Int.natAbs_natCast, decide_eq_false (by lia), ← doubleValue_one]
  refine le_doubleValue_ofDyadic (isNaN_eq_false_of_isFinite isFinite_one) (fun h0 ↦ ?_) e
    (by rwa [doubleValue_one, WithBotTop.coe_le_coe])
  rw [h0, Nat.cast_zero, zero_mul] at h
  exact absurd h (by norm_num)

/-- A double with the sign bit clear plus `1.0` is a NaN or at least `1`: the sum is exact or
rounded, and its rounding is monotone (`JPoints.Double.le_doubleValue_ofDyadic`). -/
theorem IsPlus.isNaN_or_one_le_add_one {x : Double} (hx : x.IsPlus) :
    (x + 1.0).isNaN = true ∨ ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue (x + 1.0).bits := by
  change (Double.add x 1.0).isNaN = true ∨ _ ≤ doubleValue (Double.add x 1.0).bits
  by_cases hn : x.isNaN = true
  · simp only [Double.add, hn, Bool.true_or, ↓reduceIte]
    exact .inl (isNaN_propagateNaN (by simp [hn]))
  have hxs := hx.resolve_left hn
  simp only [Double.add, hn, isNaN_eq_false_of_isFinite isFinite_one,
    isInf_eq_false_of_isFinite isFinite_one, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Bool.false_and, toDyadic_one, hxs,
    signBit_eq_false_of_pos (x := 1.0) (by rw [toRat_one]; exact one_pos)]
  obtain ⟨m, hm, hr⟩ := exists_toDyadic_eq_natCast hxs
  generalize x.toDyadic.2 = ex at hm hr
  rw [hm]
  split_ifs with hxi hs0
  · exact .inr (by rw [doubleValue_eq_top hxs (by simp_all [isInf, isFinite])]; exact le_top)
  · exact absurd hs0 (by positivity)
  refine .inr (one_le_doubleValue_ofDyadic (by push_cast; rfl) ?_)
  rw [Nat.cast_add, add_mul, natCast_mul_two_pow_mul_zpow m (min_le_left ex (-52)),
    natCast_mul_two_pow_mul_zpow 4503599627370496 (min_le_right ex (-52))]
  norm_num
  positivity

/-- A double with the sign bit clear that is no NaN: `+0.0`, a positive finite double or `+∞`, as
the margins of `row_region` are. -/
def IsNonneg (x : Double) : Prop := x.isNaN = false ∧ x.signBit = false

theorem isNonneg_fabs {x : Double} (hx : x.isNaN = false) : IsNonneg x.fabs :=
  ⟨(isNaN_fabs x).trans hx, signBit_fabs x⟩

theorem isNonneg_one : IsNonneg 1.0 := ⟨by decide, by decide⟩

theorem isNonneg_huge : IsNonneg huge := ⟨isNaN_huge, by decide⟩

theorem IsNonneg.add {x y : Double} (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  refine ⟨?_, signBit_add hx.2 hy.2⟩
  by_cases hxi : x.isInf = true
  · rw [add_of_isInf_of_signBit_eq hxi hy.1 fun _ ↦ hy.2.trans hx.2.symm]
    exact hx.1
  have hxf := isFinite_of_isInf_eq_false hx.1 (by simpa using hxi)
  by_cases hyi : y.isInf = true
  · rw [add_of_isInf_right hxf hyi]
    exact hy.1
  exact (isRounding_add hxf (isFinite_of_isInf_eq_false hy.1 (by simpa using hyi))).isNaN_eq_false

theorem IsNonneg.mul {x y : Double} (hx : IsNonneg x) (hxf : x.isFinite = true)
    (hx0 : x.toRat ≠ 0) (hy : IsNonneg y) : IsNonneg (x * y) := by
  by_cases hyi : y.isInf = true
  · rw [mul_of_isInf_right hxf hx0 hyi, hx.2, hy.2]; exact isNonneg_huge
  have hyf := isFinite_of_isInf_eq_false hy.1 (by simpa using hyi)
  exact ⟨(isRounding_mul hxf hyf).isNaN_eq_false,
    by rw [signBit_mul_of_isFinite hxf hyf, hx.2, hy.2]; rfl⟩

/-- A double `x` at most `-K`, `K ≥ 1`, less a double `m` with the sign bit clear is no NaN and at
most `-K / 2`. -/
theorem doubleValue_sub_le_of_isNonneg {x m : Double} (hx : x.isNaN = false) {K : ℚ} (hK : 1 ≤ K)
    (hxK : doubleValue x.bits ≤ ((-K : ℚ) : WithBotTop ℚ)) (hm : IsNonneg m) :
    (x - m).isNaN = false ∧ doubleValue (x - m).bits ≤ ((-K / 2 : ℚ) : WithBotTop ℚ) := by
  rw [Double.sub_eq_add_neg hx hm.1]
  have hmn : m.neg.isNaN = false := (isNaN_neg m).trans hm.1
  have hms : m.neg.signBit = true := by rw [signBit_neg, hm.2]; rfl
  cases hxf : x.isFinite
  · have hxs := signBit_eq_true_of_doubleValue_le hx hxf hxK
    rw [add_of_isInf_of_signBit_eq (isInf_of_isFinite_eq_false hx hxf) hmn
      fun _ ↦ hms.trans hxs.symm, doubleValue_of_isFinite_eq_false hx hxf, hxs]
    exact ⟨hx, bot_le⟩
  have hxK' : x.toRat ≤ -K := by rwa [doubleValue_eq_toRat hxf, WithBotTop.coe_le_coe] at hxK
  cases hmf : m.isFinite
  · have hmi := isInf_of_isFinite_eq_false hmn ((isFinite_neg m).trans hmf)
    rw [add_of_isInf_right hxf hmi, doubleValue_of_isInf hmi, hms]
    exact ⟨hmn, bot_le⟩
  have hmf' : m.neg.isFinite = true := (isFinite_neg m).trans hmf
  exact doubleValue_add_le_of_le hxf hmf' hK (by linarith [toRat_neg m, toRat_nonneg hm.2])

/-- A double `x` at least `K ≥ 1` plus a double `m` with the sign bit clear is no NaN and at
least `K / 2`. -/
theorem doubleValue_add_ge_of_isNonneg {x m : Double} (hx : x.isNaN = false) {K : ℚ} (hK : 1 ≤ K)
    (hxK : ((K : ℚ) : WithBotTop ℚ) ≤ doubleValue x.bits) (hm : IsNonneg m) :
    (x + m).isNaN = false ∧ ((K / 2 : ℚ) : WithBotTop ℚ) ≤ doubleValue (x + m).bits := by
  change (Double.add x m).isNaN = false ∧ _ ≤ doubleValue (Double.add x m).bits
  cases hxf : x.isFinite
  · have hxi := isInf_of_isFinite_eq_false hx hxf
    have hv := doubleValue_of_isFinite_eq_false hx hxf
    cases hxs : x.signBit
    · simp only [Double.add, hx, hm.1, hxi, hxs, hm.2, Bool.or_false, ↓reduceIte,
        bne_self_eq_false, Bool.and_false, Bool.false_eq_true]
      exact ⟨trivial, by rw [hv, hxs]; exact le_top⟩
    · rw [hv, hxs] at hxK; exact absurd hxK (by simp)
  have hxK' : K ≤ x.toRat := by rwa [doubleValue_eq_toRat hxf, WithBotTop.coe_le_coe] at hxK
  cases hmf : m.isFinite
  · have hmi : m.isInf = true := isInf_of_isFinite_eq_false hm.1 hmf
    simp only [Double.add, hx, hm.1, isInf_eq_false_of_isFinite hxf, hmi, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, by rw [doubleValue_of_isInf hmi, hm.2]; exact le_top⟩
  exact le_doubleValue_add_of_le hxf hmf hK (by linarith [toRat_nonneg hm.2])

/-! ### Quotients that are not zero -/

/-- The rounding of `n / d ≥ 2 ^ (-24)` is not a zero: it is at least the least subnormal. -/
theorem ofRatio_beq_zero_eq_false {n d : ℕ} (hn : n ≠ 0) (hd : d ≠ 0)
    (h : (2 : ℚ) ^ (-24 : ℤ) ≤ n / d) : (ofRatio false n d).beq zero = false := by
  refine beq_zero_eq_false_of_le (c := 2 ^ (-1074 : ℤ)) (by positivity) (isNaN_ofRatio _ _ hd) ?_
  rw [← doubleValue_one_bits]
  refine le_doubleValue_ofRatio (by decide) hn hd ?_
  rw [doubleValue_one_bits, WithBotTop.coe_le_coe]
  exact (zpow_le_zpow_right₀ one_le_two (by norm_num)).trans h

-- A quotient of a number at least `1` by a positive number at most `2 ^ 24`.
private theorem two_zpow_neg_le_div {X Y : ℚ} (hX : 1 ≤ X) (hY : 0 < Y) (hY' : Y ≤ 2 ^ 24) :
    (2 : ℚ) ^ (-24 : ℤ) ≤ X / Y := by
  rw [zpow_neg, zpow_ofNat, ← one_div]
  exact div_le_div₀ (by linarith) hX hY hY'

-- The last case of `JPoints.Double.div` for the significands and exponents of the operands, whose
-- quotient is at least `2 ^ (-24)`.
private theorem ratio_beq_zero_eq_false {mx my : ℕ} {ex ey : ℤ} (hmx : mx ≠ 0) (hmy : my ≠ 0)
    (h : (2 : ℚ) ^ (-24 : ℤ) ≤ mx * 2 ^ ex / (my * 2 ^ ey)) :
    (if 0 ≤ ex - ey then ofRatio false (mx * 2 ^ (ex - ey).toNat) my
      else ofRatio false mx (my * 2 ^ (-(ex - ey)).toNat)).beq zero = false := by
  have : (my : ℚ) ≠ 0 := mod_cast hmy
  split_ifs with hk
  · refine ofRatio_beq_zero_eq_false (Nat.mul_ne_zero hmx (by positivity)) hmy (h.trans_eq ?_)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg hk,
      zpow_sub₀ two_ne_zero]
    field
  · refine ofRatio_beq_zero_eq_false hmx (Nat.mul_ne_zero hmy (by positivity)) (h.trans_eq ?_)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg (by lia), zpow_neg, zpow_sub₀ two_ne_zero]
    field

-- The significands and exponents of a double at least `1` and of a positive double at most
-- `2 ^ 24`, whose quotient is at least `2 ^ (-24)`.
private theorem exists_toDyadic_div {x y : Double} (hxs : x.signBit = false)
    (hx1 : 1 ≤ x.toRat) (hys : y.signBit = false) (hy0 : y.isZero = false)
    (hy1 : y.toRat ≤ 2 ^ 24) :
    ∃ mx my : ℕ, ∃ ex ey : ℤ, x.toDyadic = ((mx : ℤ), ex) ∧ y.toDyadic = ((my : ℤ), ey) ∧
      mx ≠ 0 ∧ my ≠ 0 ∧
      (2 : ℚ) ^ (-24 : ℤ) ≤ mx * 2 ^ ex / (my * 2 ^ ey) := by
  obtain ⟨mx, hmx, hrx⟩ := exists_toDyadic_eq_natCast hxs
  obtain ⟨my, hmy, hry⟩ := exists_toDyadic_eq_natCast hys
  have hY : 0 < y.toRat :=
    lt_of_le_of_ne (hry ▸ by positivity) (Ne.symm (isZero_eq_false_iff.mp hy0))
  refine ⟨mx, my, _, _, hmx, hmy, fun h0 ↦ ?_, fun h0 ↦ ?_,
    hrx ▸ hry ▸ two_zpow_neg_le_div hx1 hY hy1⟩
  · rw [hrx, h0, Nat.cast_zero, zero_mul] at hx1; exact absurd hx1 (by norm_num)
  · rw [hry, h0, Nat.cast_zero, zero_mul] at hY; exact lt_irrefl _ hY

/-- A NaN or a double at least `1`, divided by a positive double at most `2 ^ 24`, is not a zero:
the quotient is a NaN, `+∞`, or the rounding of a number at least `2 ^ (-24)`. -/
theorem div_beq_zero_eq_false {x y : Double}
    (hx : x.isNaN = true ∨ ((1 : ℚ) : WithBotTop ℚ) ≤ doubleValue x.bits)
    (hy : y.isFinite = true) (hys : y.signBit = false) (hy0 : y.isZero = false)
    (hy1 : y.toRat ≤ 2 ^ 24) : (x / y).beq zero = false := by
  change (div x y).beq zero = false
  have hyn : y.isNaN = false := by simp_all [isFinite, isNaN]
  by_cases hn : x.isNaN = true
  · simp only [div, hn, Bool.true_or, ↓reduceIte, beq, isNaN_propagateNaN (x := x) (y := y)
      (by simp [hn]), Bool.not_true, Bool.false_and]
  have hx1 := hx.resolve_left hn
  have hxs := signBit_eq_false_of_le one_pos hx1
  by_cases hxi : x.isInf = true
  · simp only [div, hn, hyn, hxs, hys, hxi, bne_self_eq_false, isInf_eq_false_of_isFinite hy,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    decide
  rw [doubleValue_eq_toRat (isFinite_of_isInf_eq_false (by simpa using hn) (by simpa using hxi)),
    WithBotTop.coe_le_coe] at hx1
  obtain ⟨mx, my, ex, ey, hmx, hmy, hmx0, hmy0, h2⟩ := exists_toDyadic_div hxs hx1 hys hy0 hy1
  simp only [div, hn, hyn, hxs, hys, hxi, bne_self_eq_false, isInf_eq_false_of_isFinite hy, hy0,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hmx, hmy, Int.natAbs_natCast]
  exact ratio_beq_zero_eq_false hmx0 hmy0 h2

/-! ### `sqrt` and `floor` -/

theorem toDyadic_assemble {neg : Bool} {M : ℕ} {q : ℤ} (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53)
    (hq : -1074 ≤ q) (hq' : q + 1075 < 2047) :
    (assemble neg M q).toDyadic = ((if neg then -1 else 1) * (M : ℤ), q) := by
  obtain ⟨hs, he, hf⟩ := fields_assemble neg q h2
  rw [toDyadic_eq, hs, he, hf]
  simp only [show ¬M < 2 ^ 52 by lia, show ¬2047 ≤ q + 1075 by lia, ↓reduceIte,
    show (q + 1075).toNat ≠ 0 by lia, Nat.sub_add_cancel h1,
    Int.toNat_of_nonneg (by lia : 0 ≤ q + 1075), add_sub_cancel_right]

/-- The bits of `(double)n` for `0 < n < 2 ^ 53`: the significand `n` shifted to `53` bits, and
the exponent `⌊log₂ n⌋ - 52` of its last place. -/
theorem ofInt_natCast_eq_assemble {n : ℕ} (h0 : n ≠ 0) (h : n < 2 ^ 53) :
    ofInt n = assemble false (n * 2 ^ (52 - n.log2)) (n.log2 - 52) := by
  have hl : n.log2 < 53 := (Nat.log2_lt h0).mpr h
  have hM : n * 2 ^ (52 - n.log2) < 2 ^ 53 := mul_two_pow_lt_two_pow_53 (by lia)
  change ofDyadic (decide ((n : ℤ) < 0)) (n : ℤ).natAbs 0 = _
  rw [decide_eq_false (by lia), Int.natAbs_natCast, ofDyadic_eq 0 h0, roundShift_of_nonpos (by lia),
    show max ((n.log2 : ℤ) + 0 - 52) (-1074) = n.log2 - 52 by lia,
    show (-((n.log2 : ℤ) - 52 - 0)).toNat = 52 - n.log2 by lia, ofSignificand_of_ne _ hM.ne]

-- `⌊√n⌋ < 2 ^ u` for `u = 52 - ⌊log₂ n / 2⌋` and `0 < n < 2 ^ 51`.
private theorem sqrt_lt_two_pow {n : ℕ} (h0 : n ≠ 0) (h : n < 2 ^ 51) :
    n.sqrt < 2 ^ (52 - n.log2 / 2) := by
  have hl : n.log2 < 51 := (Nat.log2_lt h0).mpr h
  refine Nat.sqrt_lt.mpr (Nat.lt_log2_self.trans_le ?_)
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) (by lia)

/-- `sqrt` of the normal positive double of the significand `M` and the exponent `q` of its last
place, as `JPoints.Double.sqrt` computes it: the significand rounded from the integer square root
`s` of `N = M 2 ^ (q - 2 r)`, for the exponent `r` of the last place of the result. -/
theorem sqrt_assemble {M N s : ℕ} {q r : ℤ} (h1 : 2 ^ 52 ≤ M) (h2 : M < 2 ^ 53) (hq : -1074 ≤ q)
    (hq' : q + 1075 < 2047) (hr : r = (52 + q) / 2 - 52) (hN : N = M * 2 ^ (q - 2 * r).toNat)
    (hs : s = N.sqrt) :
    (assemble false M q).sqrt = ofSignificand false (if s < N - s * s then s + 1 else s) r := by
  have hf := (isFinite_assemble_iff (neg := false) (q := q) h2).mpr (.inr hq')
  have hz : (assemble false M q).isZero = false := by
    rw [isZero_eq_false_iff, toRat_assemble h2 (by lia) fun _ ↦ ⟨hq, hq'⟩]
    positivity
  have hlog : M.log2 = 52 := (Nat.log2_eq_iff (by positivity)).mpr ⟨h1, h2⟩
  subst hr hN hs
  simp only [sqrt, isNaN_assemble false _ h2, hz, (fields_assemble false _ h2).1,
    isInf_eq_false_of_isFinite hf, toDyadic_assemble h1 h2 hq hq', Bool.false_eq_true, ↓reduceIte,
    one_mul, Int.toNat_natCast, hlog, Nat.cast_ofNat]

-- The integer square root `s` of `N = n k²`, rounded up when the remainder `N - s²` exceeds `s`
-- (to the nearest integer, as `sqrtsd` rounds), lies in `[⌊√n⌋ k, (⌊√n⌋ + 1) k)` for `⌊√n⌋ < k`.
private theorem sqrt_mul_le_and_lt_of_round {n k N s M : ℕ} (hk : n.sqrt < k) (hN : N = n * (k * k))
    (hs : s = N.sqrt) (hM : M = if s < N - s * s then s + 1 else s) :
    n.sqrt * k ≤ M ∧ M < (n.sqrt + 1) * k := by
  have h1 : n.sqrt * k ≤ s := hs ▸ Nat.le_sqrt.mpr (by
    rw [Nat.mul_mul_mul_comm, hN]; exact Nat.mul_le_mul_right _ (Nat.sqrt_le n))
  have h2 : s < (n.sqrt + 1) * k := hs ▸ Nat.sqrt_lt.mpr (by
    rw [Nat.mul_mul_mul_comm, hN]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_sqrt n) (Nat.mul_pos (by lia) (by lia)))
  have h3 : s * s ≤ N := hs ▸ Nat.sqrt_le N
  refine ⟨by split_ifs at hM <;> lia, ?_⟩
  split_ifs at hM with h
  · by_contra! h4
    have h5 := Nat.mul_le_mul_right (k * k) (Nat.lt_succ_sqrt n)
    have h6 : s + 1 = (n.sqrt + 1) * k := by lia
    have h7 : (s + 1) * (s + 1) = (n.sqrt + 1) * (n.sqrt + 1) * (k * k) := by rw [h6]; ring
    have h8 : k * k < (n.sqrt + 1) * k := by lia
    lia [Nat.lt_of_mul_lt_mul_right h8]
  · lia

-- `sqrt` of `(double)n` for `0 < n < 2 ^ 51`: the significand `M` rounded from the square root of
-- `n 4 ^ u` for the exponent `-u` of its last place, `u = 52 - ⌊log₂ n / 2⌋`, between
-- `⌊√n⌋ 2 ^ u` and `(⌊√n⌋ + 1) 2 ^ u`.
private theorem exists_sqrt_ofInt_natCast_eq {n : ℕ} (h0 : n ≠ 0) (h : n < 2 ^ 51) :
    ∃ M, (ofInt n).sqrt = ofSignificand false M (-((52 - n.log2 / 2 : ℕ) : ℤ)) ∧
      n.sqrt * 2 ^ (52 - n.log2 / 2) ≤ M ∧ M < (n.sqrt + 1) * 2 ^ (52 - n.log2 / 2) := by
  have hl : n.log2 < 51 := (Nat.log2_lt h0).mpr h
  have hN : n * (2 ^ (52 - n.log2 / 2) * 2 ^ (52 - n.log2 / 2)) = n * 2 ^ (52 - n.log2) *
      2 ^ ((n.log2 : ℤ) - 52 - 2 * -((52 - n.log2 / 2 : ℕ) : ℤ)).toNat := by
    rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    congr 2
    lia
  have hs := sqrt_assemble (q := n.log2 - 52) (r := -((52 - n.log2 / 2 : ℕ) : ℤ))
    (two_pow_le_mul_two_pow h0 (t := 52 - n.log2) (by lia)) (mul_two_pow_lt_two_pow_53 (by lia))
    (by lia) (by lia) (by lia) hN rfl
  rw [ofInt_natCast_eq_assemble h0 (by lia), hs]
  exact ⟨_, rfl, sqrt_mul_le_and_lt_of_round (sqrt_lt_two_pow h0 h) rfl rfl rfl⟩

-- `⌊√n⌋ 2 ^ u` is at least `2 ^ 52` and `(⌊√n⌋ + 1) 2 ^ u` at most `2 ^ 53` for
-- `u = 52 - ⌊log₂ n / 2⌋` and `0 < n < 2 ^ 51`.
private theorem two_pow_le_sqrt_mul_and_le {n : ℕ} (h0 : n ≠ 0) (h : n < 2 ^ 51) :
    2 ^ 52 ≤ n.sqrt * 2 ^ (52 - n.log2 / 2) ∧ (n.sqrt + 1) * 2 ^ (52 - n.log2 / 2) ≤ 2 ^ 53 := by
  have h1 : 2 ^ (n.log2 / 2) ≤ n.sqrt := Nat.le_sqrt.mpr <| by
    rw [← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by decide) (by lia)).trans (Nat.log2_self_le h0)
  have h2 : n.sqrt < 2 ^ (n.log2 / 2 + 1) := Nat.sqrt_lt.mpr <| Nat.lt_log2_self.trans_le <| by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by lia)
  have hl : n.log2 < 51 := (Nat.log2_lt h0).mpr h
  constructor
  · calc 2 ^ 52 = 2 ^ (n.log2 / 2) * 2 ^ (52 - n.log2 / 2) := by rw [← Nat.pow_add]; congr 1; lia
      _ ≤ _ := Nat.mul_le_mul_right _ h1
  · calc (n.sqrt + 1) * 2 ^ (52 - n.log2 / 2) ≤ 2 ^ (n.log2 / 2 + 1) * 2 ^ (52 - n.log2 / 2) :=
          Nat.mul_le_mul_right _ h2
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; lia

-- `(double)⌊m / 2 ^ k⌋` of `|m| < 2 ^ 53` is exact.
private theorem isFinite_ofInt_ediv_and_toRat {m : ℤ} (hm : m.natAbs < 2 ^ 53) (k : ℕ) :
    (ofInt (m / 2 ^ k)).isFinite = true ∧ (ofInt (m / 2 ^ k)).toRat = ⌊(m : ℚ) / 2 ^ k⌋ := by
  have hf : |m / 2 ^ k| < 2 ^ 53 := by
    rw [Int.abs_eq_natAbs]
    lia [Int.natAbs_ediv_le_natAbs m (2 ^ k)]
  obtain ⟨h1, h2⟩ := isFinite_ofInt_and_toRat hf
  have h2k : ((2 ^ k : ℕ) : ℚ) = 2 ^ k := by push_cast; rfl
  refine ⟨h1, ?_⟩
  rw [h2, ← h2k, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- `floor` of `math.h` is exact on a finite double. -/
theorem isFinite_floor_and_toRat {x : Double} (hx : x.isFinite = true) :
    x.floor.isFinite = true ∧ x.floor.toRat = ⌊x.toRat⌋ := by
  have hn := isNaN_eq_false_of_isFinite hx
  by_cases hz : x.isZero = true
  · have hfl : x.floor = x := by simp [floor, hn, hz]
    rw [hfl, isZero_eq_true_iff.mp hz]
    exact ⟨hx, by simp⟩
  have hv := toRat_eq x
  have hm := (toDyadic_bounds x).1
  rcases hd : x.toDyadic with ⟨m, e⟩
  rw [hd] at hv hm
  by_cases he : 0 ≤ e
  · have hfl : x.floor = x := by simp [floor, hn, hx, hz, hd, he]
    rw [hfl, hv, ← Int.toNat_of_nonneg he, zpow_natCast]
    exact ⟨hx, mod_cast (Int.floor_intCast (R := ℚ) _).symm⟩
  have hk : (m : ℚ) * 2 ^ e = m / 2 ^ (-e).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg, div_inv_eq_mul]
  have hfl : x.floor = ofInt (m / 2 ^ (-e).toNat) := by simp [floor, hn, hx, hz, hd, he]; rfl
  rw [hfl, hv, hk]
  exact isFinite_ofInt_ediv_and_toRat hm _

/-! ### The integers computed in doubles -/

/-- `floor(sqrt(height))`, converted to a `long`, is the integer square root of the height bound
`0 ≤ H ≤ MAX_HEIGHT`: `H` converts exactly, and `√H` lies below the next integer `⌊√H⌋ + 1` by more
than half a unit in its last place, so that its rounding stays below it. -/
theorem toInt_toInt64_floor_sqrt_ofInt {H : ℤ} (h0 : 0 ≤ H) (hH : H ≤ maxHeight) :
    (ofInt H).sqrt.floor.toInt64.toInt = H.toNat.sqrt := by
  lift H to ℕ using h0
  rw [Int.toNat_natCast]
  rcases Nat.eq_zero_or_pos H with rfl | hpos
  · decide +kernel
  have h51 : H < 2 ^ 51 := by
    have : maxHeight < 2 ^ 51 := lt_of_pow_lt_pow_left₀ 2 (by positivity) (by lia [maxHeight_sq_lt])
    lia
  obtain ⟨M, hs, hM1, hM2⟩ := exists_sqrt_ofInt_natCast_eq hpos.ne' h51
  obtain ⟨h52, h53⟩ := two_pow_le_sqrt_mul_and_le hpos.ne' h51
  have hf := isFinite_ofSignificand (neg := false) (M := M)
    (q := -((52 - H.log2 / 2 : ℕ) : ℤ)) (by lia) (by lia)
  obtain ⟨-, hfv⟩ := isFinite_floor_and_toRat hf
  have hfl : ⌊(ofSignificand false M (-((52 - H.log2 / 2 : ℕ) : ℤ))).toRat⌋ = H.sqrt := by
    rw [toRat_ofSignificand (by lia) (by lia) (by lia) hf, ite_eq_right Bool.false_ne_true,
      one_mul, zpow_neg, zpow_natCast, ← div_eq_mul_inv, Int.floor_eq_iff, Int.cast_natCast,
      le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    exact ⟨mod_cast hM1, mod_cast hM2⟩
  rw [hs, toInt_toInt64 (by rw [hfv, hfl]; positivity) (by
    rw [hfv, hfl]; exact_mod_cast (Nat.sqrt_le_self H).trans_lt (by lia)), hfv, hfl]
  simp

-- The reciprocal `1.0 / (double)p` of `0 < p < 2 ^ 53`, where `(double)p` is exact.
private theorem isFinite_and_isRounding_one_div_ofInt_natCast {p : ℕ} (hp : 0 < p)
    (hp' : p < 2 ^ 53) : (1.0 / ofInt p).isFinite = true ∧ (1.0 / ofInt p).IsRounding (1 / p) := by
  obtain ⟨hf, hv⟩ := isFinite_ofInt_and_toRat (n := p) (by rw [Nat.abs_cast]; exact_mod_cast hp')
  have hB := isRounding_div isFinite_one hf (by rw [hv]; positivity)
  rw [toRat_one, hv, Int.cast_natCast] at hB
  have hp1 : (1 : ℚ) ≤ p := mod_cast hp
  refine ⟨hB.isFinite_of_abs_le (n := 100) (by norm_num) ?_, hB⟩
  rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hp1

-- `1.0 / (double)p` of a `p` for which `(double)p` overflows to `+∞` is `0.0`.
private theorem one_div_ofInt_natCast_eq_zero {p : ℕ} (hf : (ofInt p).isFinite = false) :
    1.0 / ofInt p = zero := by
  have hP := isRounding_ofInt p
  have hi : (ofInt p).isInf = true := by
    by_contra h
    simp [isFinite_of_isInf_eq_false hP.isNaN_eq_false (by simpa using h)] at hf
  have hs : (ofInt p).signBit = false := by
    change (ofDyadic _ _ _).signBit = false
    rw [signBit_ofDyadic, decide_eq_false (by lia)]
  have h1 : (1.0 : Double).signBit = false := by decide +kernel
  change div _ _ = _
  simp [div, hi, hs, h1, isNaN_eq_false_of_isFinite isFinite_one,
    isInf_eq_false_of_isFinite isFinite_one, hP.isNaN_eq_false, zero]

-- The reciprocal `1.0 / (double)p` of `p ≥ 2 ^ 51` for a finite `(double)p`: finite, not negative,
-- and at most `2 ^ (-49)`.
private theorem isFinite_and_toRat_one_div_le_of_isFinite {p : ℕ} (hp : 2 ^ 51 ≤ p)
    (hf : (ofInt p).isFinite = true) :
    (1.0 / ofInt p).isFinite = true ∧ 0 ≤ (1.0 / ofInt p).toRat ∧
      (1.0 / ofInt p).toRat ≤ 1 / 2 ^ 49 := by
  have ht := two_zpow_neg_1075_le
  have ht0 : (0 : ℚ) < 2 ^ (-1075 : ℤ) := by positivity
  have hp1 : (2 : ℚ) ^ 51 ≤ p := mod_cast hp
  obtain ⟨-, l2⟩ := abs_sub_le_iff.mp ((isRounding_ofInt p).abs_sub_le hf)
  rw [Int.cast_natCast, abs_of_nonneg (by positivity)] at l2
  have hP2 : (2 : ℚ) ^ 50 ≤ (ofInt p).toRat := by linarith
  have hB := isRounding_div isFinite_one hf (by positivity)
  rw [toRat_one] at hB
  have hinv : 1 / (ofInt p).toRat ≤ 1 / 2 ^ 50 := one_div_le_one_div_of_le (by positivity) hP2
  have hBf := hB.isFinite_of_abs_le (n := 100) (by norm_num) <| by
    rw [abs_of_pos (by positivity)]
    linarith
  refine ⟨hBf, hB.nonneg hBf (by positivity), ?_⟩
  obtain ⟨b1, -⟩ := abs_sub_le_iff.mp (hB.abs_sub_le hBf)
  rw [abs_of_pos (by positivity)] at b1
  linarith

-- The reciprocal `1.0 / (double)p` of `p ≥ 2 ^ 51`, also where `(double)p` overflows: finite, not
-- negative, and at most `2 ^ (-49)`.
private theorem isFinite_and_toRat_one_div_ofInt_natCast_le {p : ℕ} (hp : 2 ^ 51 ≤ p) :
    (1.0 / ofInt p).isFinite = true ∧ 0 ≤ (1.0 / ofInt p).toRat ∧
      (1.0 / ofInt p).toRat ≤ 1 / 2 ^ 49 := by
  by_cases hf : (ofInt p).isFinite = true
  · exact isFinite_and_toRat_one_div_le_of_isFinite hp hf
  rw [one_div_ofInt_natCast_eq_zero (by simpa using hf), toRat_zero]
  exact ⟨isFinite_zero, le_rfl, by positivity⟩

-- The reciprocal `1.0 / (double)p` of a positive `p` is finite.
private theorem isFinite_one_div_ofInt_natCast {p : ℕ} (hp : 0 < p) :
    (1.0 / ofInt p).isFinite = true := by
  rcases lt_or_ge p (2 ^ 53) with h | h
  · exact (isFinite_and_isRounding_one_div_ofInt_natCast hp h).1
  · exact (isFinite_and_toRat_one_div_ofInt_natCast_le (by lia)).1

-- `n` times the reciprocal `1.0 / (double)p` of `0 < p < 2 ^ 53`, for `n < 2 ^ 48`: within
-- `2 ^ (-53) n / p + 2 ^ (-152)` of `n / p`.
private theorem abs_natCast_mul_toRat_one_div_sub_le {n p : ℕ} (hp : 0 < p) (hp' : p < 2 ^ 53)
    (hn : n < 2 ^ 48) :
    0 ≤ (1.0 / ofInt p).toRat ∧
      |(n : ℚ) * (1.0 / ofInt p).toRat - n / p| ≤ n / p / 2 ^ 53 + 1 / 2 ^ 152 := by
  obtain ⟨hBf, hB⟩ := isFinite_and_isRounding_one_div_ofInt_natCast hp hp'
  have hip : 0 < (1 : ℚ) / p := by positivity
  have hn' : (n : ℚ) < 2 ^ 48 := mod_cast hn
  obtain ⟨b1, b2⟩ := abs_sub_le_iff.mp (hB.abs_sub_le hBf)
  rw [abs_of_pos hip] at b1 b2
  have m1 := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg n)
  have m2 := mul_le_mul_of_nonneg_left b2 (Nat.cast_nonneg n)
  have m3 := mul_le_mul_of_nonneg_right hn'.le (zpow_nonneg zero_le_two (-1075 : ℤ))
  refine ⟨hB.nonneg hBf hip.le, ?_⟩
  rw [← mul_one_div, abs_sub_le_iff]
  constructor <;> linarith [two_zpow_neg_1075_le]

-- `(double)n * (1.0 / (double)p)` for `n < 2 ^ 48` and `0 < p < 2 ^ 53`: finite, not negative,
-- and within `2 ^ (-51) n / p + 2 ^ (-150)` of `n / p`, by the roundings of the reciprocal and of
-- the product.
private theorem isFinite_and_abs_toRat_ofInt_mul_one_div_sub_le {n p : ℕ} (hp : 0 < p)
    (hp' : p < 2 ^ 53) (hn : n < 2 ^ 48) :
    (ofInt n * (1.0 / ofInt p)).isFinite = true ∧ 0 ≤ (ofInt n * (1.0 / ofInt p)).toRat ∧
      |(ofInt n * (1.0 / ofInt p)).toRat - n / p| ≤ n / p / 2 ^ 51 + 1 / 2 ^ 150 := by
  obtain ⟨hB0, hnB⟩ := abs_natCast_mul_toRat_one_div_sub_le hp hp' hn
  obtain ⟨hAf, hA⟩ := isFinite_ofInt_and_toRat (n := n) <| by
    rw [Nat.abs_cast]; exact_mod_cast hn.trans (by norm_num)
  have hC := isRounding_mul hAf (isFinite_one_div_ofInt_natCast hp)
  rw [hA, Int.cast_natCast] at hC
  obtain ⟨n1, n2⟩ := abs_sub_le_iff.mp hnB
  have hnp : (n : ℚ) / p ≤ 2 ^ 48 :=
    (div_le_self (Nat.cast_nonneg n) (mod_cast hp)).trans (mod_cast hn.le)
  have h0 : 0 ≤ (n : ℚ) * (1.0 / ofInt p).toRat := by positivity
  have hCf := hC.isFinite_of_abs_le (n := 100) (by norm_num) <| by
    rw [abs_of_nonneg h0]; linarith
  refine ⟨hCf, hC.nonneg hCf h0, ?_⟩
  obtain ⟨c1, c2⟩ := abs_sub_le_iff.mp (hC.abs_sub_le hCf)
  rw [abs_of_nonneg h0] at c1 c2
  rw [abs_sub_le_iff]
  constructor <;> linarith [two_zpow_neg_1075_le]

-- `(double)0 * y` of a finite `y` is a zero.
private theorem isFinite_ofInt_zero_mul_and_toRat {y : Double} (hy : y.isFinite = true) :
    (ofInt 0 * y).isFinite = true ∧ (ofInt 0 * y).toRat = 0 := by
  have h0 : (ofInt 0).toDyadic.1.natAbs = 0 := by decide +kernel
  rw [mul_eq_ofDyadic (by decide) hy, h0, Nat.zero_mul, ofDyadic_zero]
  generalize ((ofInt 0).signBit != y.signBit) = b
  cases b <;> exact ⟨by decide, by decide +kernel⟩

-- A finite `C` within `1 / 4` of `k < 2 ^ 48`: `C + 0.5`, converted to a `long`, is `k`.
private theorem toInt_toInt64_add_half {C : Double} {k : ℕ} (hC : C.isFinite = true)
    (hk : k < 2 ^ 48) (h : |C.toRat - k| ≤ 1 / 4) : (C + 0.5).toInt64.toInt = k := by
  have hD := isRounding_add hC isFinite_half
  rw [toRat_half] at hD
  obtain ⟨c1, c2⟩ := abs_sub_le_iff.mp h
  have hk' : (k : ℚ) < 2 ^ 48 := mod_cast hk
  have ht := two_zpow_neg_1075_le
  have ht0 : (0 : ℚ) < 2 ^ (-1075 : ℤ) := by positivity
  have hpos : 0 < C.toRat + 1 / 2 := by linarith
  have hDf := hD.isFinite_of_abs_le (n := 100) (by norm_num) (by rw [abs_of_pos hpos]; linarith)
  obtain ⟨d1, d2⟩ := abs_sub_le_iff.mp (hD.abs_sub_le hDf)
  rw [abs_of_pos hpos] at d1 d2
  have hD0 : 0 ≤ (C + 0.5).toRat := by linarith
  have hfl : ⌊(C + 0.5).toRat⌋₊ = k := (Nat.floor_eq_iff hD0).mpr ⟨by linarith, by linarith⟩
  rw [toInt_toInt64 hD0 (by linarith), hfl]

/-- The number of the full periods of `walk_parts`, `(double)(k p) * invp + 0.5` with the
reciprocal `invp = 1.0 / p` of a positive `p`, converted to a `long`, is `k` for `k p < 2 ^ 48`:
`k p` and `p` convert exactly, and the rounding of the reciprocal and of the two operations moves
`k + 1 / 2` by less than `1 / 2`. -/
theorem toInt_toInt64_ofInt_mul_one_div_add_half {k p : ℕ} (hp : 0 < p) (hkp : k * p < 2 ^ 48) :
    (ofInt ((k * p : ℕ) : ℤ) * (1.0 / ofInt (p : ℤ)) + 0.5).toInt64.toInt = k := by
  have hk : k < 2 ^ 48 := (Nat.le_mul_of_pos_right k hp).trans_lt hkp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain ⟨hCf, hC⟩ := isFinite_ofInt_zero_mul_and_toRat (isFinite_one_div_ofInt_natCast hp)
    rw [Nat.zero_mul, Nat.cast_zero]
    exact toInt_toInt64_add_half hCf (by norm_num) (by rw [hC]; norm_num)
  have hp' : p < 2 ^ 53 := ((Nat.le_mul_of_pos_left p hk0).trans_lt hkp).trans (by norm_num)
  obtain ⟨hCf, -, hC⟩ := isFinite_and_abs_toRat_ofInt_mul_one_div_sub_le hp hp' hkp
  have e : ((k * p : ℕ) : ℚ) / p = k := by
    rw [Nat.cast_mul, mul_div_cancel_right₀ _ (by positivity)]
  rw [e] at hC
  have hk' : (k : ℚ) < 2 ^ 48 := mod_cast hk
  exact toInt_toInt64_add_half hCf hk (hC.trans (by linarith))

-- A double `0 ≤ C < Q + 1` with `Q - 1 < C` for `Q < 2 ^ 62`, converted to a `long`, lies in
-- `[Q - 1, Q]`.
private theorem toInt_toInt64_mem_Icc {C : Double} {Q : ℕ} (hQ : Q < 2 ^ 62) (h0 : 0 ≤ C.toRat)
    (h1 : (Q : ℚ) - 1 < C.toRat) (h2 : C.toRat < Q + 1) :
    C.toInt64.toInt ∈ Set.Icc ((Q : ℤ) - 1) Q := by
  have hQ' : (Q : ℚ) < 2 ^ 62 := mod_cast hQ
  rw [toInt_toInt64 h0 (by linarith)]
  have f1 : ⌊C.toRat⌋₊ < Q + 1 := (Nat.floor_lt h0).mpr (mod_cast h2)
  have f2 : (Q : ℚ) < ⌊C.toRat⌋₊ + 2 := by linarith [Nat.lt_floor_add_one C.toRat]
  have f3 : Q < ⌊C.toRat⌋₊ + 2 := mod_cast f2
  constructor <;> lia

-- The quotient of `row_setup` for `p < 2 ^ 51`, where the product is within `2 ^ (-51) d / p +
-- 2 ^ (-150)` of `d / p`, less than the distance `1 / p` of `d / p` from the next integer above.
private theorem toInt_toInt64_ofInt_mul_one_div_mem_Icc_of_lt {d p : ℕ} (hp : 0 < p)
    (hp51 : p < 2 ^ 51) (hd : d < 2 ^ 48) :
    (ofInt d * (1.0 / ofInt p)).toInt64.toInt ∈ Set.Icc (((d / p : ℕ) : ℤ) - 1) (d / p : ℕ) := by
  have hd' : (d : ℚ) < 2 ^ 48 := mod_cast hd
  obtain ⟨hCf, hC0, hC⟩ := isFinite_and_abs_toRat_ofInt_mul_one_div_sub_le hp (by lia) hd
  obtain ⟨c1, c2⟩ := abs_sub_le_iff.mp hC
  have hQ1 : ((d / p : ℕ) : ℚ) ≤ d / p := Nat.cast_div_le
  have hQ2 : (d : ℚ) / p + 1 / p ≤ (d / p : ℕ) + 1 := by
    rw [← add_div, div_le_iff₀ (by positivity)]
    exact_mod_cast (by lia [Nat.div_add_mod d p, Nat.mod_lt d hp] : d + 1 ≤ (d / p + 1) * p)
  have hx : (d : ℚ) / p ≤ 2 ^ 48 * (1 / p) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hd'.le (by positivity)
  have hy : (1 : ℚ) / 2 ^ 51 < 1 / p := one_div_lt_one_div_of_lt (by positivity) (mod_cast hp51)
  have hy1 : (1 : ℚ) / p ≤ 1 := (div_le_one (by positivity)).mpr (mod_cast hp)
  refine toInt_toInt64_mem_Icc ((Nat.div_le_self d p).trans_lt (by lia)) hC0 ?_ ?_
  all_goals
    generalize (d : ℚ) / p = x at *
    generalize (1 : ℚ) / p = y at *
    linarith

/-- The quotient of `row_setup` by a reciprocal, `(long)((double)d * invp)` with the reciprocal
`invp = 1.0 / p` of a positive `p`, is `⌊d / p⌋` or one less for `0 ≤ d < 2 ^ 48`, so that
`d - p q` lies in `[0, 2 p)` and one correction gives `d mod p`: the product is `d / p` up to a
relative error of about `2 ^ (-52)`, less than the distance `1 / p` of a fraction `d / p` from the
next integer above it. -/
theorem toInt_toInt64_ofInt_mul_one_div_mem_Icc {d : ℤ} {p : ℕ} (hp : 0 < p) (hd0 : 0 ≤ d)
    (hd : d < 2 ^ 48) :
    (ofInt d * (1.0 / ofInt (p : ℤ))).toInt64.toInt ∈ Set.Icc (d / p - 1) (d / p) := by
  lift d to ℕ using hd0
  have hd48 : d < 2 ^ 48 := mod_cast hd
  rw [← Int.natCast_ediv]
  rcases lt_or_ge p (2 ^ 51) with hp51 | hp51
  · exact toInt_toInt64_ofInt_mul_one_div_mem_Icc_of_lt hp hp51 hd48
  have hd' : (d : ℚ) < 2 ^ 48 := mod_cast hd
  obtain ⟨hBf, hB0, hB⟩ := isFinite_and_toRat_one_div_ofInt_natCast_le hp51
  obtain ⟨hAf, hA⟩ := isFinite_ofInt_and_toRat (n := d) <| by
    rw [Nat.abs_cast]; exact_mod_cast hd48.trans (by norm_num)
  have hC := isRounding_mul hAf hBf
  rw [hA, Int.cast_natCast] at hC
  have hdB := mul_le_mul hd'.le hB hB0 (by positivity)
  have hdB0 : 0 ≤ (d : ℚ) * (1.0 / ofInt p).toRat := by positivity
  have hCf := hC.isFinite_of_abs_le (n := 100) (by norm_num) (by rw [abs_of_nonneg hdB0]; linarith)
  obtain ⟨c1, -⟩ := abs_sub_le_iff.mp (hC.abs_sub_le hCf)
  rw [abs_of_nonneg hdB0] at c1
  have hC0 := hC.nonneg hCf hdB0
  rw [Nat.div_eq_of_lt (by lia)]
  exact toInt_toInt64_mem_Icc (by norm_num) hC0 (by linarith) (by linarith [two_zpow_neg_1075_le])

end Double

end JPoints

end
