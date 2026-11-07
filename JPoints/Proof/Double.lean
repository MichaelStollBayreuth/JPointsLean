/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.WithBotTop

import JPoints.Mathlib.Order.WithBotTop
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The values of the doubles of the model

The doubles of the model (`JPoints.Double`) are bits, with the operations of the C language and of
the C library on them; a double has its value in `ℚ` extended by `⊥` and `⊤`
(`JPoints.doubleValue`), which is `±∞` for the largest exponent field and the exact value
`JPoints.Double.toRat` otherwise (`JPoints.Double.doubleValue_bits`,
`JPoints.Double.doubleValue_eq_toRat`). This file proves that the operations do on the values what
the C code relies on: a double that is not a NaN has an order value, its bits without the sign bit,
negated when the sign bit is set (`JPoints.Double.orderValue`), in which its value is strictly
increasing (`JPoints.Double.strictMonoOn_valueOfOrderValue`), so that the comparisons of the C
language are the order of the values (`JPoints.Double.lt_eq_true_iff`,
`JPoints.Double.le_eq_true_iff`, `JPoints.Double.beq_eq_true_iff`) and `nextafter` steps to the
neighbouring double (`JPoints.Double.orderValue_nextUp`, `JPoints.Double.nextUp_le_of_lt`, and
downwards `JPoints.Double.orderValue_nextDown`, the step upwards of the negation by
`JPoints.Double.nextDown_eq_neg_nextUp_neg`); the negation and `fabs` act on the sign of the value;
the double that `JPoints.Double.assemble` makes from a significand `M` and the exponent `q` of its
last place has the fields of a subnormal, an infinity or a normal double
(`JPoints.Double.fields_assemble`) and, in the range of the finite doubles, the value `±M 2 ^ q`
(`JPoints.Double.toRat_assemble`); the double `JPoints.Double.ofDyadic` nearest to `±m 2 ^ e`, which
ends with it, is exact when `0 < m < 2 ^ 53`, `e ≥ -1074` and `m 2 ^ e < 2 ^ 1024`
(`JPoints.Double.ofDyadic_exact`, where the last hypothesis reads `Nat.log2 m + e ≤ 1023`); and the
conversion to `long` truncates (`JPoints.Double.toInt_toInt64`,
`JPoints.Double.abs_toInt_toInt64_sub_lt`).

The exponent field sorts the doubles into NaNs, infinities and finite doubles, and an infinity has
the value `±∞` of its sign (`JPoints.Double.doubleValue_of_isInf`,
`JPoints.Double.doubleValue_of_isFinite_eq_false`); a double that `==` finds equal to one that is
not a zero has its bits (`JPoints.Double.eq_of_beq`), and so has one without a sign bit equal to
any double but `-0.0` (`JPoints.Double.eq_of_beq_of_signBit_eq_false`); the sign bit of a double
is the sign of its value (`JPoints.Double.toRat_nonneg`, `JPoints.Double.signBit_eq_false_of_pos`,
`JPoints.Double.toRat_neg_iff`); and `<` and `<=` of finite doubles are the order of their values
(`JPoints.Double.lt_iff_toRat_lt`, `JPoints.Double.le_iff_toRat_le`), every finite double lying
strictly between `-HUGE_VAL` and `HUGE_VAL` (`JPoints.Double.neg_huge_lt`,
`JPoints.Double.lt_huge`).

## Main definitions

* `JPoints.IsNaN`, `JPoints.doubleValue`: whether the bits of a double are a NaN, and the value
  of a double.
* `JPoints.Double.maxOrderValue`, `JPoints.Double.magnitudeUnits`,
  `JPoints.Double.orderValueUnits`, `JPoints.Double.valueOfOrderValue`: the order value of
  `+∞`, and the value of the doubles of an order value.

## Main statements

* `JPoints.Double.doubleValue_eq_valueOfOrderValue`,
  `JPoints.Double.strictMonoOn_valueOfOrderValue`: the value of a double that is not a NaN is that
  of its order value, strictly increasing in it.
* `JPoints.Double.lt_eq_true_iff`, `JPoints.Double.le_eq_true_iff`,
  `JPoints.Double.beq_eq_true_iff`: the comparisons of the C language off NaN.
* `JPoints.Double.doubleValue_bits`, `JPoints.Double.doubleValue_eq_toRat`: the value of a
  double by its fields, and that of a finite double.
* `JPoints.Double.fields_assemble`, `JPoints.Double.isFinite_assemble_iff`,
  `JPoints.Double.toRat_assemble`: the bits of a significand and an exponent.
* `JPoints.Double.ofDyadic_exact`: the exact rounding of a dyadic number.
* `JPoints.Double.toInt_toInt64`, `JPoints.Double.abs_toInt_toInt64_sub_lt`: the conversion to
  `long`.
* `JPoints.Double.doubleValue_of_isInf`, `JPoints.Double.doubleValue_of_isFinite_eq_false`: the
  value of an infinity.
* `JPoints.Double.eq_of_beq`, `JPoints.Double.eq_of_beq_of_signBit_eq_false`: doubles that `==`
  finds equal.
* `JPoints.Double.toRat_nonneg`, `JPoints.Double.signBit_eq_false_of_pos`,
  `JPoints.Double.toRat_neg_iff`: the sign bit and the sign of the value.
* `JPoints.Double.lt_iff_toRat_lt`, `JPoints.Double.le_iff_toRat_le`: `<` and `<=` of finite
  doubles.
* `JPoints.Double.orderValue_nextUp`, `JPoints.Double.nextUp_le_of_lt`,
  `JPoints.Double.nextDown_eq_neg_nextUp_neg`, `JPoints.Double.orderValue_nextDown`: `nextafter`
  towards `±HUGE_VAL`.

## References

Adapted from `Ratpoints/Proof/Double.lean`, with `doubleValue` and `IsNaN` from
`Ratpoints/Spec/Region.lean`, of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

namespace JPoints

/-- Whether the IEEE binary64 bits `x` are a NaN: the exponent field all ones and the fraction
nonzero. -/
def IsNaN (x : UInt64) : Prop := (x.toNat / 2 ^ 52) % 2 ^ 11 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0

/-- The value of the IEEE binary64 double with the bits `x`: `±f 2 ^ (-1074)` for the exponent
field `0` (the zeros and the subnormals, both zeros giving `0`), `±(2 ^ 52 + f) 2 ^ (e - 1075)` for
an exponent field `e` from `1` to `2046`, and `⊥` and `⊤` for the infinities, where `f` is the
fraction and the sign is that of the top bit. The value of a NaN (the exponent field `2047` with a
nonzero fraction) is junk, an infinity. -/
def doubleValue (x : UInt64) : WithBotTop ℚ :=
  let e : ℕ := (x.toNat / 2 ^ 52) % 2 ^ 11
  let f : ℕ := x.toNat % 2 ^ 52
  if e = 2047 then (if 2 ^ 63 ≤ x.toNat then ⊥ else ⊤)
  else
    let a : ℚ := if e = 0 then f * 2 ^ (-1074 : ℤ) else (2 ^ 52 + f) * 2 ^ ((e : ℤ) - 1075)
    ((if 2 ^ 63 ≤ x.toNat then -a else a : ℚ) : WithBotTop ℚ)

/-! ### Facts on numbers -/

theorem abs_ite_neg_one_one (neg : Bool) : |(if neg then -1 else 1 : ℚ)| = 1 := by
  split_ifs <;> simp

/-- The integer `±⌊|X|⌋` of the sign of `X` lies within `1` of `X`. -/
theorem abs_ite_floor_sub_lt {X : ℚ} {neg : Prop} [Decidable neg] (hneg : neg ↔ X < 0) :
    |((if neg then -(⌊|X|⌋₊ : ℤ) else (⌊|X|⌋₊ : ℤ) : ℤ) : ℚ) - X| < 1 := by
  have h1 := Nat.floor_le (abs_nonneg X)
  have h2 := Nat.lt_floor_add_one |X|
  generalize ⌊|X|⌋₊ = n at h1 h2 ⊢
  by_cases h : neg
  · rw [ite_eq_left h, Int.cast_neg, Int.cast_natCast, abs_lt]
    rw [abs_of_neg (hneg.mp h)] at h1 h2
    constructor <;> linarith
  · rw [ite_eq_right h, Int.cast_natCast, abs_lt]
    rw [abs_of_nonneg (not_lt.mp (mt hneg.mpr h))] at h1 h2
    constructor <;> linarith

theorem natCast_mul_two_pow_mul_zpow (m : ℕ) {e q : ℤ} (h : q ≤ e) :
    ((m * 2 ^ (e - q).toNat : ℕ) : ℚ) * 2 ^ q = m * 2 ^ e := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by lia),
    mul_assoc, ← zpow_add₀ two_ne_zero, sub_add_cancel]

theorem two_zpow_log2_le_mul {m : ℕ} (hm : m ≠ 0) (e : ℤ) :
    (2 : ℚ) ^ ((m.log2 : ℤ) + e) ≤ m * 2 ^ e ∧ (m : ℚ) * 2 ^ e < 2 ^ ((m.log2 : ℤ) + 1 + e) := by
  have h1 : (2 : ℚ) ^ m.log2 ≤ m := mod_cast Nat.log2_self_le hm
  have h2 : (m : ℚ) < 2 ^ (m.log2 + 1) := mod_cast Nat.lt_log2_self
  have ht : (0 : ℚ) < 2 ^ e := zpow_pos two_pos _
  rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, ← zpow_natCast,
    show ((m.log2 : ℤ) + 1) = ((m.log2 + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  exact ⟨mul_le_mul_of_nonneg_right h1 ht.le, mul_lt_mul_of_pos_right h2 ht⟩

theorem toNat_shift_eq_floor (m : ℕ) (e : ℤ) :
    (if 0 ≤ e then m <<< e.toNat else m >>> (-e).toNat) = ⌊(m : ℚ) * 2 ^ e⌋₊ := by
  split_ifs with he
  · rw [Nat.shiftLeft_eq, ← Int.toNat_of_nonneg he, zpow_natCast, Int.toNat_of_nonneg he]
    exact_mod_cast (Nat.floor_natCast (R := ℚ) _).symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨(-e).toNat, by lia⟩
    rw [Nat.shiftRight_eq_div_pow, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      show ((2 : ℚ) ^ k) = ((2 ^ k : ℕ) : ℚ) by push_cast; rfl, Nat.floor_div_eq_div]
    simp

theorem mul_two_pow_lt_two_pow_53 {m t : ℕ} (ht : m.log2 + t ≤ 52) : m * 2 ^ t < 2 ^ 53 := by
  calc m * 2 ^ t < 2 ^ (m.log2 + 1) * 2 ^ t :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
    _ = 2 ^ (m.log2 + 1 + t) := (Nat.pow_add ..).symm
    _ ≤ 2 ^ 53 := Nat.pow_le_pow_right (by decide) (by lia)

theorem two_pow_le_mul_two_pow {m t : ℕ} (hm0 : m ≠ 0) (ht : m.log2 + t = 52) :
    2 ^ 52 ≤ m * 2 ^ t :=
  calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ t := by rw [← Nat.pow_add, ht]
    _ ≤ m * 2 ^ t := Nat.mul_le_mul_right _ (Nat.log2_self_le hm0)

namespace Double

theorem expField_eq (x : Double) : x.expField = x.bits.toNat / 2 ^ 52 % 2 ^ 11 := by
  rw [expField, UInt64.toNat_and, UInt64.toNat_shiftRight,
    show (0x7ff : UInt64).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  rfl

theorem fracField_eq (x : Double) : x.fracField = x.bits.toNat % 2 ^ 52 := by
  rw [fracField, UInt64.toNat_and, show (0xfffffffffffff : UInt64).toNat = 2 ^ 52 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem toNat_and_mask (b : UInt64) :
    (b &&& 0x7fffffffffffffff).toNat = b.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and, show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem signBit_eq_decide (x : Double) : x.signBit = decide (2 ^ 63 ≤ x.bits.toNat) := by
  simp only [signBit]
  exact decide_eq_decide.mpr (by lia [x.bits.toNat_lt])

theorem signBit_eq_true_iff (x : Double) : x.signBit = true ↔ 2 ^ 63 ≤ x.bits.toNat := by
  simp [signBit_eq_decide]

theorem fracField_lt (x : Double) : x.fracField < 2 ^ 52 :=
  fracField_eq x ▸ Nat.mod_lt _ (Nat.two_pow_pos 52)

theorem expField_lt (x : Double) : x.expField < 2048 :=
  expField_eq x ▸ Nat.mod_lt _ (Nat.two_pow_pos 11)

theorem toNat_bits (x : Double) :
    x.bits.toNat = (if x.signBit then 2 ^ 63 else 0) + (x.expField * 2 ^ 52 + x.fracField) := by
  have h := x.bits.toNat_lt
  have h1 := Nat.div_add_mod x.bits.toNat (2 ^ 52)
  have h2 := Nat.div_add_mod (x.bits.toNat / 2 ^ 52) (2 ^ 11)
  rw [signBit_eq_decide, expField_eq, fracField_eq]
  split <;> rename_i h3 <;> simp only [decide_eq_true_eq] at h3 <;> lia

theorem expField_mul_add_fracField (x : Double) :
    x.expField * 2 ^ 52 + x.fracField = x.bits.toNat % 2 ^ 63 := by
  rw [toNat_bits x]; split <;> lia [fracField_lt x, expField_lt x]

theorem isNaN_iff (x : Double) : x.isNaN = true ↔ IsNaN x.bits := by
  simp [isNaN, IsNaN, expField_eq, fracField_eq]

theorem fields_eq_of_toNat_bits_eq {x : Double} {neg : Bool} {E F : ℕ} (hE : E < 2048)
    (hF : F < 2 ^ 52) (h : x.bits.toNat = (if neg then 2 ^ 63 else 0) + (E * 2 ^ 52 + F)) :
    x.signBit = neg ∧ x.expField = E ∧ x.fracField = F := by
  have e : F + 2 ^ 52 * ((if neg then 2 ^ 11 else 0) + E) = x.bits.toNat := by
    rw [h]; cases neg <;> simp <;> lia
  have hd := (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr ⟨e, hF⟩
  rw [signBit_eq_decide, expField_eq, fracField_eq, hd.1, hd.2, Nat.add_mod,
    Nat.mod_eq_of_lt (show E < 2 ^ 11 by lia)]
  cases neg <;> simp [h] <;> lia

/-! ### The exact value of a finite double -/

theorem toRat_eq (x : Double) : x.toRat = (x.toDyadic.1 : ℚ) * 2 ^ x.toDyadic.2 := by
  rcases h : x.toDyadic with ⟨m, e⟩
  simp only [toRat, h]
  split_ifs with he
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg he]
  · rw [Rat.mkRat_eq_div]
    push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg, div_inv_eq_mul]

theorem toDyadic_eq (x : Double) : x.toDyadic =
    ((if x.signBit then -1 else 1 : ℤ) *
      ((if x.expField = 0 then x.fracField else x.fracField + 2 ^ 52 : ℕ) : ℤ),
      if x.expField = 0 then -1074 else (x.expField : ℤ) - 1075) := by
  simp only [toDyadic]
  split_ifs <;> simp

theorem toRat_eq_fields (x : Double) : x.toRat = (if x.signBit then -1 else 1) *
    (if x.expField = 0 then (x.fracField : ℚ) * 2 ^ (-1074 : ℤ)
      else (2 ^ 52 + x.fracField) * 2 ^ ((x.expField : ℤ) - 1075)) := by
  rw [toRat_eq, toDyadic_eq]
  split_ifs <;> simp only [Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Int.cast_add, Int.cast_pow, Int.cast_ofNat,
    mul_assoc, add_comm]

/-- The value of the bits of a double (`JPoints.doubleValue`), by the
fields of the model: `±∞` for the exponent field `2047` and the exact value
`JPoints.Double.toRat` otherwise. -/
theorem doubleValue_bits (x : Double) : doubleValue x.bits =
    if x.expField = 2047 then (if x.signBit then ⊥ else ⊤) else (x.toRat : WithBotTop ℚ) := by
  simp only [doubleValue, ← expField_eq, ← fracField_eq, ← signBit_eq_true_iff, toRat_eq_fields]
  split_ifs <;> simp

theorem doubleValue_eq_toRat {x : Double} (hx : x.isFinite = true) :
    doubleValue x.bits = (x.toRat : WithBotTop ℚ) := by
  rw [doubleValue_bits, ite_eq_right (by simpa [isFinite] using hx)]

/-! ### The order of the values -/

/-- The order value (`JPoints.Double.orderValue`) of `+∞`, `2047 · 2 ^ 52`, the bits of `+∞`;
`-maxOrderValue` is that of `-∞`. -/
def maxOrderValue : ℕ := 2047 * 2 ^ 52

/-- The value of the nonnegative finite double with the bits `a`, in units of the least subnormal
`2 ^ (-1074)`: the fraction `f` for the exponent field `0`, and `(2 ^ 52 + f) 2 ^ (e - 1)` for an
exponent field `e ≥ 1`. -/
def magnitudeUnits (a : ℕ) : ℕ :=
  if a / 2 ^ 52 = 0 then a % 2 ^ 52 else (2 ^ 52 + a % 2 ^ 52) * 2 ^ (a / 2 ^ 52 - 1)

/-- `JPoints.Double.magnitudeUnits` with the sign of the order value `k`, the value of the finite
doubles with the order value `k` in units of `2 ^ (-1074)`. -/
def orderValueUnits (k : ℤ) : ℤ :=
  if k < 0 then -(magnitudeUnits k.natAbs : ℤ) else magnitudeUnits k.natAbs

/-- The value of the doubles with the order value `k` (`JPoints.Double.orderValue`), for
`|k| ≤ JPoints.Double.maxOrderValue`: `⊥` at `-JPoints.Double.maxOrderValue`, `⊤` at
`JPoints.Double.maxOrderValue`, and `JPoints.Double.orderValueUnits k` times `2 ^ (-1074)`
between. -/
def valueOfOrderValue (k : ℤ) : WithBotTop ℚ :=
  if k ≤ -(maxOrderValue : ℤ) then ⊥ else if (maxOrderValue : ℤ) ≤ k then ⊤
  else (((orderValueUnits k : ℚ) * 2 ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ)

theorem magnitudeUnits_lt_two_pow (a : ℕ) : magnitudeUnits a < 2 ^ (52 + a / 2 ^ 52) := by
  simp only [magnitudeUnits]
  split_ifs with h
  · rw [h]; exact Nat.mod_lt _ (Nat.two_pow_pos 52)
  · have := Nat.mod_lt a (Nat.two_pow_pos 52)
    calc (2 ^ 52 + a % 2 ^ 52) * 2 ^ (a / 2 ^ 52 - 1) < 2 ^ 53 * 2 ^ (a / 2 ^ 52 - 1) :=
          Nat.mul_lt_mul_of_pos_right (by lia) (Nat.two_pow_pos _)
      _ = 2 ^ (52 + a / 2 ^ 52) := by rw [← Nat.pow_add]; congr 1; lia

theorem two_pow_le_magnitudeUnits {a : ℕ} (h : a / 2 ^ 52 ≠ 0) :
    2 ^ (51 + a / 2 ^ 52) ≤ magnitudeUnits a := by
  simp only [magnitudeUnits, h, ↓reduceIte]
  rw [show 51 + a / 2 ^ 52 = 52 + (a / 2 ^ 52 - 1) by lia, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem magnitudeUnits_strictMono : StrictMono magnitudeUnits := by
  intro a b hab
  rcases (Nat.div_le_div_right (c := 2 ^ 52) hab.le).lt_or_eq with h | h
  · calc magnitudeUnits a < 2 ^ (52 + a / 2 ^ 52) := magnitudeUnits_lt_two_pow a
      _ ≤ 2 ^ (51 + b / 2 ^ 52) := Nat.pow_le_pow_right (by decide) (by lia)
      _ ≤ magnitudeUnits b := two_pow_le_magnitudeUnits (by lia)
  · have h1 := Nat.div_add_mod a (2 ^ 52)
    have h2 := Nat.div_add_mod b (2 ^ 52)
    have hf : a % 2 ^ 52 < b % 2 ^ 52 := by rw [h] at h1; lia
    simp only [magnitudeUnits]
    rw [h]
    split_ifs
    · exact hf
    · exact Nat.mul_lt_mul_of_pos_right (by lia) (Nat.two_pow_pos _)

@[simp]
theorem magnitudeUnits_zero : magnitudeUnits 0 = 0 := rfl

theorem orderValueUnits_strictMono : StrictMono orderValueUnits := by
  intro k l hkl
  have hm := magnitudeUnits_strictMono
  have h0 (n : ℕ) (hn : 0 < n) : 0 < magnitudeUnits n := magnitudeUnits_zero ▸ hm hn
  simp only [orderValueUnits]
  split_ifs with h1 h2 h2
  · lia [hm (show l.natAbs < k.natAbs by lia)]
  · lia [h0 k.natAbs (by lia)]
  · lia
  · lia [hm (show k.natAbs < l.natAbs by lia)]

theorem strictMonoOn_valueOfOrderValue :
    StrictMonoOn valueOfOrderValue (Set.Icc (-(maxOrderValue : ℤ)) maxOrderValue) := by
  intro k ⟨hk1, hk2⟩ l ⟨hl1, hl2⟩ hkl
  have hs : (orderValueUnits k : ℚ) < orderValueUnits l := mod_cast orderValueUnits_strictMono hkl
  simp only [valueOfOrderValue]
  split_ifs <;> try lia
  all_goals first
    | exact WithBotTop.bot_lt_coe _
    | exact WithBotTop.coe_lt_top _
    | exact bot_lt_top
    | exact WithBotTop.coe_lt_coe.mpr (mul_lt_mul_of_pos_right hs (zpow_pos two_pos _))

theorem orderValue_eq_mod (x : Double) : x.orderValue = if x.signBit
    then -((x.bits.toNat % 2 ^ 63 : ℕ) : ℤ) else ((x.bits.toNat % 2 ^ 63 : ℕ) : ℤ) := by
  simp only [orderValue, toNat_and_mask]

theorem orderValue_eq (x : Double) : x.orderValue =
    if x.signBit then -((x.expField * 2 ^ 52 + x.fracField : ℕ) : ℤ)
    else ((x.expField * 2 ^ 52 + x.fracField : ℕ) : ℤ) := by
  rw [orderValue_eq_mod, expField_mul_add_fracField]

theorem expField_lt_or_of_isNaN_eq_false {x : Double} (hx : x.isNaN = false) :
    x.expField < 2047 ∨ x.expField = 2047 ∧ x.fracField = 0 := by
  simp only [isNaN, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hx
  lia [expField_lt x]

theorem natAbs_orderValue_le {x : Double} (hx : x.isNaN = false) :
    x.orderValue.natAbs ≤ maxOrderValue := by
  rw [orderValue_eq, maxOrderValue]
  rcases expField_lt_or_of_isNaN_eq_false hx with h | h <;> split <;> lia [fracField_lt x]

theorem orderValue_mem_Icc {x : Double} (hx : x.isNaN = false) :
    x.orderValue ∈ Set.Icc (-(maxOrderValue : ℤ)) maxOrderValue := by
  constructor <;> lia [natAbs_orderValue_le hx]

theorem magnitudeUnits_fields {E F : ℕ} (hF : F < 2 ^ 52) :
    magnitudeUnits (E * 2 ^ 52 + F) = if E = 0 then F else (2 ^ 52 + F) * 2 ^ (E - 1) := by
  have hd := (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr
    ⟨show F + 2 ^ 52 * E = E * 2 ^ 52 + F by lia, hF⟩
  rw [magnitudeUnits, hd.1, hd.2]

theorem orderValueUnits_natCast (n : ℕ) : orderValueUnits n = magnitudeUnits n := by
  simp [orderValueUnits]

theorem orderValueUnits_neg_natCast (n : ℕ) :
    orderValueUnits (-(n : ℤ)) = -(magnitudeUnits n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [orderValueUnits]
  · simp [orderValueUnits, h]

theorem magnitudeUnits_mul_eq {E F : ℕ} (hF : F < 2 ^ 52) :
    (magnitudeUnits (E * 2 ^ 52 + F) : ℚ) * 2 ^ (-1074 : ℤ) =
      if E = 0 then (F : ℚ) * 2 ^ (-1074 : ℤ) else (2 ^ 52 + F) * 2 ^ ((E : ℤ) - 1075) := by
  rw [magnitudeUnits_fields hF]
  split_ifs with h
  · rfl
  · rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, ← zpow_natCast,
      ← zpow_add₀ two_ne_zero, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
    push_cast
    congr 2
    lia

theorem valueOfOrderValue_natCast {k : ℕ} (hk : k < maxOrderValue) :
    valueOfOrderValue k = (((magnitudeUnits k : ℚ) * 2 ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) := by
  have h1 : ¬((k : ℤ) ≤ -(maxOrderValue : ℤ)) := by lia
  have h2 : ¬((maxOrderValue : ℤ) ≤ k) := by lia
  simp only [valueOfOrderValue, h1, h2, ↓reduceIte, orderValueUnits_natCast, Int.cast_natCast]

theorem valueOfOrderValue_neg_natCast {k : ℕ} (hk : k < maxOrderValue) :
    valueOfOrderValue (-(k : ℤ)) =
      ((-((magnitudeUnits k : ℚ) * 2 ^ (-1074 : ℤ)) : ℚ) : WithBotTop ℚ) := by
  have h1 : ¬(-(k : ℤ) ≤ -(maxOrderValue : ℤ)) := by lia
  have h2 : ¬((maxOrderValue : ℤ) ≤ -(k : ℤ)) := by lia
  simp only [valueOfOrderValue, h1, h2, ↓reduceIte, orderValueUnits_neg_natCast, Int.cast_neg,
    Int.cast_natCast, neg_mul]

theorem doubleValue_eq_valueOfOrderValue {x : Double} (hx : x.isNaN = false) :
    doubleValue x.bits = valueOfOrderValue x.orderValue := by
  rw [doubleValue_bits, orderValue_eq]
  rcases expField_lt_or_of_isNaN_eq_false hx with h | ⟨h, h0⟩
  · have hk : x.expField * 2 ^ 52 + x.fracField < maxOrderValue := by
      rw [maxOrderValue]; lia [fracField_lt x]
    rw [ite_eq_right h.ne, toRat_eq_fields, ← magnitudeUnits_mul_eq (fracField_lt x)]
    cases x.signBit <;> simp only [Bool.false_eq_true, ↓reduceIte, valueOfOrderValue_natCast hk,
      valueOfOrderValue_neg_natCast hk, one_mul, neg_one_mul]
  · cases x.signBit <;> simp [h, h0, valueOfOrderValue, maxOrderValue]

theorem lt_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.lt y = true ↔ doubleValue x.bits < doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.lt_iff_lt (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [lt, hx, hy]

theorem le_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.le y = true ↔ doubleValue x.bits ≤ doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.le_iff_le (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [le, hx, hy]

theorem beq_eq_true_iff {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false) :
    x.beq y = true ↔ doubleValue x.bits = doubleValue y.bits := by
  rw [doubleValue_eq_valueOfOrderValue hx, doubleValue_eq_valueOfOrderValue hy,
    strictMonoOn_valueOfOrderValue.injOn.eq_iff (orderValue_mem_Icc hx) (orderValue_mem_Icc hy)]
  simp [beq, hx, hy]

theorem isNaN_eq_false_iff (x : Double) : x.isNaN = false ↔ ¬ IsNaN x.bits := by
  rw [← isNaN_iff]; simp

/-! ### The magnitude and the operations on the sign bit -/

theorem toNat_bits_eq_mod (x : Double) :
    x.bits.toNat = (if x.signBit then 2 ^ 63 else 0) + x.bits.toNat % 2 ^ 63 := by
  rw [← expField_mul_add_fracField]; exact toNat_bits x

theorem isNaN_eq_false_iff_le (x : Double) :
    x.isNaN = false ↔ x.bits.toNat % 2 ^ 63 ≤ maxOrderValue := by
  rw [← expField_mul_add_fracField, maxOrderValue]
  simp only [isNaN, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]
  lia [fracField_lt x, expField_lt x]

private theorem signBit_and_mod_of_toNat_eq {x : Double} {s : Bool} {n : ℕ} (hn : n < 2 ^ 63)
    (h : x.bits.toNat = (if s then 2 ^ 63 else 0) + n) :
    x.signBit = s ∧ x.bits.toNat % 2 ^ 63 = n := by
  rw [signBit_eq_decide, h]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mod_eq_of_lt hn, and_true]
    simpa using hn
  · simp only [↓reduceIte, Nat.add_mod_left, Nat.mod_eq_of_lt hn, and_true]
    simp

theorem toNat_fabs (x : Double) : (fabs x).bits.toNat = x.bits.toNat % 2 ^ 63 :=
  toNat_and_mask x.bits

theorem toNat_mod_fabs (x : Double) : (fabs x).bits.toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
  rw [toNat_fabs, Nat.mod_mod]

theorem signBit_fabs (x : Double) : (fabs x).signBit = false := by
  rw [signBit_eq_decide, toNat_fabs]
  exact decide_eq_false (Nat.not_le.mpr (Nat.mod_lt _ (Nat.two_pow_pos 63)))

theorem toNat_mod_neg (x : Double) : (neg x).bits.toNat % 2 ^ 63 = x.bits.toNat % 2 ^ 63 := by
  rw [neg, UInt64.toNat_xor, Nat.xor_mod_two_pow]; simp

/-- Flipping the sign bit adds `2 ^ 63` to the bits, modulo `2 ^ 64`. -/
theorem toNat_bits_neg (x : Double) :
    (neg x).bits.toNat = (x.bits.toNat + 2 ^ 63) % 2 ^ 64 := by
  have hd : (neg x).bits.toNat / 2 ^ 63 = x.bits.toNat / 2 ^ 63 ^^^ 1 := by
    rw [neg, UInt64.toNat_xor, Nat.xor_div_two_pow]; rfl
  have hm := toNat_mod_neg x
  have h1 := x.bits.toNat_lt
  have h2 := (neg x).bits.toNat_lt
  rcases Nat.lt_or_ge x.bits.toNat (2 ^ 63) with hs | hs
  · rw [Nat.div_eq_of_lt hs, Nat.zero_xor] at hd; lia
  · rw [Nat.div_eq_of_lt_le (k := 1) (m := x.bits.toNat) (by lia) (by lia), Nat.xor_self] at hd
    lia

theorem signBit_neg (x : Double) : (neg x).signBit = !x.signBit := by
  rw [signBit_eq_decide, signBit_eq_decide, toNat_bits_neg, ← decide_not]
  exact decide_eq_decide.mpr (by lia [x.bits.toNat_lt])

theorem bits_neg (x : Double) : (neg x).bits = x.bits + 0x8000000000000000 :=
  UInt64.toNat_inj.mp (by rw [toNat_bits_neg, UInt64.toNat_add]; rfl)

protected theorem neg_neg (x : Double) : neg (neg x) = x := by
  simp only [neg, UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero]

theorem orderValue_neg (x : Double) : (neg x).orderValue = -x.orderValue := by
  rw [orderValue_eq_mod, orderValue_eq_mod, signBit_neg, toNat_mod_neg]
  cases x.signBit <;> simp

private theorem div_mod_eq_fields (x : Double) :
    x.bits.toNat % 2 ^ 63 / 2 ^ 52 = x.expField ∧ x.bits.toNat % 2 ^ 63 % 2 ^ 52 = x.fracField :=
  (Nat.div_mod_unique (Nat.two_pow_pos 52)).mpr
    ⟨by rw [← expField_mul_add_fracField]; lia, fracField_lt x⟩

theorem expField_eq_mod (x : Double) : x.expField = x.bits.toNat % 2 ^ 63 / 2 ^ 52 :=
  (div_mod_eq_fields x).1.symm

theorem fracField_eq_mod (x : Double) : x.fracField = x.bits.toNat % 2 ^ 63 % 2 ^ 52 :=
  (div_mod_eq_fields x).2.symm

theorem expField_neg (x : Double) : (neg x).expField = x.expField := by
  rw [expField_eq_mod, expField_eq_mod, toNat_mod_neg]

theorem fracField_neg (x : Double) : (neg x).fracField = x.fracField := by
  rw [fracField_eq_mod, fracField_eq_mod, toNat_mod_neg]

theorem expField_fabs (x : Double) : (fabs x).expField = x.expField := by
  rw [expField_eq_mod, expField_eq_mod, toNat_mod_fabs]

theorem fracField_fabs (x : Double) : (fabs x).fracField = x.fracField := by
  rw [fracField_eq_mod, fracField_eq_mod, toNat_mod_fabs]

theorem isNaN_fabs (x : Double) : (fabs x).isNaN = x.isNaN := by
  simp only [isNaN, expField_fabs, fracField_fabs]

theorem isNaN_neg (x : Double) : (neg x).isNaN = x.isNaN := by
  simp only [isNaN, expField_neg, fracField_neg]

theorem isInf_neg (x : Double) : (neg x).isInf = x.isInf := by
  simp only [isInf, expField_neg, fracField_neg]

theorem isFinite_neg (x : Double) : (neg x).isFinite = x.isFinite := by
  simp only [isFinite, expField_neg]

theorem isFinite_fabs (x : Double) : (fabs x).isFinite = x.isFinite := by
  simp only [isFinite, expField_fabs]

theorem toRat_neg (x : Double) : (neg x).toRat = -x.toRat := by
  rw [toRat_eq_fields, toRat_eq_fields, signBit_neg, expField_neg, fracField_neg]
  cases x.signBit <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, one_mul, neg_neg]

theorem toRat_fabs (x : Double) : (fabs x).toRat = |x.toRat| := by
  have h0 : 0 ≤ if x.expField = 0 then (x.fracField : ℚ) * 2 ^ (-1074 : ℤ)
      else (2 ^ 52 + x.fracField) * 2 ^ ((x.expField : ℤ) - 1075) := by
    split_ifs <;> exact mul_nonneg (by positivity) (zpow_nonneg zero_le_two _)
  rw [toRat_eq_fields, toRat_eq_fields, signBit_fabs, expField_fabs, fracField_fabs]
  cases x.signBit <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul, abs_neg,
    abs_of_nonneg h0]

/-! ### NaNs, infinities and finite doubles -/

theorem isNaN_eq_false_of_isFinite {x : Double} (hx : x.isFinite = true) : x.isNaN = false := by
  simp only [isFinite, bne_iff_ne, ne_eq] at hx
  simp [isNaN, hx]

theorem isInf_eq_false_of_isFinite {x : Double} (hx : x.isFinite = true) : x.isInf = false := by
  simp only [isFinite, bne_iff_ne, ne_eq] at hx
  simp [isInf, hx]

theorem isFinite_of_isInf_eq_false {x : Double} (hx : x.isNaN = false) (hi : x.isInf = false) :
    x.isFinite = true := by
  simp only [isNaN, isInf, isFinite, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    bne_eq_false_iff_eq, bne_iff_ne] at hx hi ⊢
  rcases hx with hx | hx <;> rcases hi with hi | hi <;> lia

theorem isInf_of_isFinite_eq_false {x : Double} (hx : x.isNaN = false)
    (hf : x.isFinite = false) : x.isInf = true := by
  cases h : x.isInf
  · rw [isFinite_of_isInf_eq_false hx h] at hf; exact absurd hf (by decide)
  · rfl

theorem isNaN_eq_false_of_isInf {x : Double} (h : x.isInf = true) : x.isNaN = false := by
  simp_all [isInf, isNaN]

theorem isFinite_eq_false_of_isNaN {x : Double} (h : x.isNaN = true) : x.isFinite = false := by
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq] at h
  simp [isFinite, h.1]

theorem isFinite_eq_false_of_isInf {x : Double} (h : x.isInf = true) : x.isFinite = false := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h
  simp [isFinite, h.1]

theorem expField_eq_of_isNaN {x : Double} (h : x.isNaN = true) : x.expField = 2047 := by
  simp only [isNaN, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem isZero_eq_decide (x : Double) : x.isZero = decide (x.bits.toNat % 2 ^ 63 = 0) := by
  simp only [isZero]
  refine decide_eq_decide.mpr ?_
  rw [← UInt64.toNat_inj, toNat_and_mask]
  rfl

theorem isZero_eq_false_of_isInf {x : Double} (h : x.isInf = true) : x.isZero = false := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at h
  rw [isZero_eq_decide, decide_eq_false_iff_not, ← expField_mul_add_fracField, h.1]
  lia

theorem doubleValue_of_isInf {x : Double} (hi : x.isInf = true) :
    doubleValue x.bits = if x.signBit then ⊥ else ⊤ := by
  simp only [isInf, Bool.and_eq_true, beq_iff_eq] at hi
  rw [doubleValue_bits, ite_eq_left hi.1]

theorem doubleValue_of_isFinite_eq_false {x : Double} (hx : x.isNaN = false)
    (hf : x.isFinite = false) : doubleValue x.bits = if x.signBit then ⊥ else ⊤ :=
  doubleValue_of_isInf (isInf_of_isFinite_eq_false hx hf)

/-- A double that is not finite, with the sign bit clear, has the value `+∞`, a NaN included. -/
theorem doubleValue_eq_top {x : Double} (hs : x.signBit = false) (hf : x.isFinite = false) :
    doubleValue x.bits = ⊤ := by
  rw [doubleValue_bits, ite_eq_left (by simpa [isFinite] using hf), hs]
  rfl

/-- An infinite double that is no NaN and at most a rational number is `-∞`. -/
theorem signBit_eq_true_of_doubleValue_le {x : Double} (hx : x.isNaN = false)
    (hf : x.isFinite = false) {q : ℚ} (h : doubleValue x.bits ≤ (q : WithBotTop ℚ)) :
    x.signBit = true := by
  cases hs : x.signBit
  · rw [doubleValue_of_isFinite_eq_false hx hf, hs] at h; exact absurd h (by simp)
  · rfl

theorem isNaN_huge : huge.isNaN = false := by decide

theorem isNaN_huge_neg : huge.neg.isNaN = false := by decide

theorem doubleValue_huge : doubleValue huge.bits = ⊤ := by decide

theorem doubleValue_huge_neg : doubleValue huge.neg.bits = ⊥ := by decide

/-! ### Doubles that `==` finds equal -/

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

/-! ### Doubles from their fields -/

private theorem toNat_sign_or {neg : Bool} {n : ℕ} (hn : n < 2 ^ 63) :
    ((if neg then 0x8000000000000000 else 0 : UInt64) ||| n.toUInt64).toNat =
      (if neg then 2 ^ 63 else 0) + n := by
  rw [UInt64.toNat_or, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by lia)]
  cases neg
  · simp
  · simp only [↓reduceIte]
    rw [show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, Nat.or_comm,
      Nat.or_two_pow_eq_add_of_lt hn, Nat.add_comm]

private theorem shiftLeft_or_eq {E F : ℕ} (hE : E < 2048) (hF : F < 2 ^ 52) :
    (E.toUInt64 <<< 52 ||| F.toUInt64) = (E * 2 ^ 52 + F).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [Nat.toUInt64_eq, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  rw [show (52 : UInt64).toNat % 64 = 52 from rfl, Nat.mod_eq_of_lt (by lia : E < 2 ^ 64),
    Nat.mod_eq_of_lt (by lia : F < 2 ^ 64), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by lia),
    Nat.mod_eq_of_lt (by lia), Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hF]

private theorem toNat_sign_or_or {neg : Bool} {E F : ℕ} (hE : E < 2048) (hF : F < 2 ^ 52) :
    ((if neg then 0x8000000000000000 else 0 : UInt64) ||| E.toUInt64 <<< 52 ||| F.toUInt64).toNat =
      (if neg then 2 ^ 63 else 0) + (E * 2 ^ 52 + F) := by
  rw [UInt64.or_assoc, shiftLeft_or_eq hE hF, toNat_sign_or (by lia)]

theorem roundShift_of_nonpos {m : ℕ} {k : ℤ} (hk : k ≤ 0) :
    roundShift m k = m * 2 ^ (-k).toNat := by
  simp [roundShift, hk, Nat.shiftLeft_eq]

/-! ### The assembly of the bits -/

theorem ofSignificand_of_ne {neg : Bool} {M : ℕ} (q : ℤ) (h : M ≠ 2 ^ 53) :
    ofSignificand neg M q = assemble neg M q := by
  simp only [ofSignificand, h, ↓reduceIte]

theorem ofSignificand_two_pow (neg : Bool) (q : ℤ) :
    ofSignificand neg (2 ^ 53) q = assemble neg (2 ^ 52) (q + 1) := by
  simp only [ofSignificand, ↓reduceIte]

/-- The sign bit, the exponent field and the fraction of the double that
`JPoints.Double.assemble` makes from a significand `M < 2 ^ 53` and the exponent `q` of its last
place: those of a subnormal or a zero for `M < 2 ^ 52`, of an infinity when the exponent field
`q + 1075` would reach `2047`, and of a normal double otherwise. -/
theorem fields_assemble (neg : Bool) {M : ℕ} (q : ℤ) (hM : M < 2 ^ 53) :
    (assemble neg M q).signBit = neg ∧
      (assemble neg M q).expField =
        (if M < 2 ^ 52 then 0 else if 2047 ≤ q + 1075 then 2047 else (q + 1075).toNat) ∧
      (assemble neg M q).fracField =
        if M < 2 ^ 52 then M else if 2047 ≤ q + 1075 then 0 else M - 2 ^ 52 := by
  by_cases h1 : M < 2 ^ 52
  · simp only [h1, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by decide) h1 ?_
    simp only [assemble, h1, ↓reduceIte]
    rw [toNat_sign_or (by lia)]; simp
  by_cases h2 : 2047 ≤ q + 1075
  · simp only [h1, h2, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by decide) (by decide) ?_
    simp only [assemble, h1, h2, ↓reduceIte]
    exact toNat_sign_or (n := 2047 * 2 ^ 52 + 0) (by norm_num)
  · simp only [h1, h2, ↓reduceIte]
    refine fields_eq_of_toNat_bits_eq (by lia) (by lia) ?_
    simp only [assemble, h1, h2, ↓reduceIte]
    exact toNat_sign_or_or (by lia) (by lia)

theorem isFinite_assemble_iff {neg : Bool} {M : ℕ} {q : ℤ} (hM : M < 2 ^ 53) :
    (assemble neg M q).isFinite = true ↔ M < 2 ^ 52 ∨ q + 1075 < 2047 := by
  obtain ⟨-, he, -⟩ := fields_assemble neg q hM
  simp only [isFinite, he]
  split_ifs <;> simp <;> lia

/-- The value `±M 2 ^ q` of the double that `JPoints.Double.assemble` makes from a significand
`M < 2 ^ 53` and the exponent `q` of its last place in the range of the finite doubles: `q = -1074`
for a subnormal or a zero (`M < 2 ^ 52`), and `-1074 ≤ q` with the exponent field `q + 1075` below
`2047` for a normal double. -/
theorem toRat_assemble {neg : Bool} {M : ℕ} {q : ℤ} (hM : M < 2 ^ 53)
    (hsub : M < 2 ^ 52 → q = -1074) (hnorm : 2 ^ 52 ≤ M → -1074 ≤ q ∧ q + 1075 < 2047) :
    (assemble neg M q).toRat = (if neg then -1 else 1) * ((M : ℚ) * 2 ^ q) := by
  obtain ⟨hs, he, hf⟩ := fields_assemble neg q hM
  rw [toRat_eq_fields, hs, he, hf]
  by_cases h1 : M < 2 ^ 52
  · simp only [h1, ↓reduceIte, hsub h1]
  obtain ⟨hq1, hq2⟩ := hnorm (by lia)
  simp only [h1, show ¬2047 ≤ q + 1075 by lia, ↓reduceIte, show (q + 1075).toNat ≠ 0 by lia]
  rw [Int.toNat_of_nonneg (by lia), Nat.cast_sub (by lia)]
  simp only [Nat.cast_pow, Nat.cast_ofNat, add_sub_cancel, add_sub_cancel_right]

theorem ofDyadic_exact {neg : Bool} {m : ℕ} {e : ℤ} (hm0 : m ≠ 0) (hm : m < 2 ^ 53)
    (he : -1074 ≤ e) (he' : (m.log2 : ℤ) + e ≤ 1023) :
    (ofDyadic neg m e).isFinite = true ∧ (ofDyadic neg m e).signBit = neg ∧
      (ofDyadic neg m e).toRat = (if neg then -1 else 1) * ((m : ℚ) * 2 ^ e) := by
  have hl : m.log2 < 53 := (Nat.log2_lt hm0).mpr hm
  have hq1 := le_max_left ((m.log2 : ℤ) + e - 52) (-1074)
  have hq2 := le_max_right ((m.log2 : ℤ) + e - 52) (-1074)
  have hq3 := max_choice ((m.log2 : ℤ) + e - 52) (-1074)
  simp only [ofDyadic, hm0, ↓reduceIte, roundShift_of_nonpos
    (by lia : max ((m.log2 : ℤ) + e - 52) (-1074) - e ≤ 0), neg_sub]
  generalize max ((m.log2 : ℤ) + e - 52) (-1074) = q at hq1 hq2 hq3 ⊢
  have hM : m * 2 ^ (e - q).toNat < 2 ^ 53 := mul_two_pow_lt_two_pow_53 (by lia)
  rw [ofSignificand_of_ne q hM.ne]
  have hsub (h : m * 2 ^ (e - q).toNat < 2 ^ 52) : q = -1074 := by
    by_contra hq
    lia [two_pow_le_mul_two_pow hm0 (t := (e - q).toNat) (by lia)]
  refine ⟨(isFinite_assemble_iff hM).mpr (.inr (by lia)), (fields_assemble neg q hM).1, ?_⟩
  rw [toRat_assemble hM hsub fun _ ↦ ⟨hq2, by lia⟩, natCast_mul_two_pow_mul_zpow m (by lia)]

/-! ### The neighbours -/

theorem toNat_huge : huge.bits.toNat = maxOrderValue := rfl

private theorem toNat_nextUp {x : Double} (hx : x.isNaN = false) (hi : x.bits ≠ huge.bits) :
    (nextUp x).bits.toNat = if x.bits.toNat % 2 ^ 63 = 0 then 1
      else if x.signBit then x.bits.toNat - 1 else x.bits.toNat + 1 := by
  have h := toNat_bits_eq_mod x
  have hk := (isNaN_eq_false_iff_le x).mp hx
  have hi' : x.bits.toNat ≠ maxOrderValue := fun h ↦
    hi (UInt64.toNat_inj.mp (h.trans toNat_huge.symm))
  simp only [nextUp, hx, Bool.false_or, beq_iff_eq, hi, ↓reduceIte, isZero_eq_decide,
    decide_eq_true_eq]
  split_ifs with h0 hs
  · rfl
  · rw [hs] at h
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; lia))]; rfl
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at h
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simp [maxOrderValue] at hk ⊢; lia)]; rfl

/-- The order value of a double whose bits are the sign bit `s` and the magnitude `n < 2 ^ 63`, and
whether it is a NaN. -/
theorem orderValue_of_toNat_eq {x : Double} {s : Bool} {n : ℕ} (hn : n < 2 ^ 63)
    (h : x.bits.toNat = (if s then 2 ^ 63 else 0) + n) :
    x.orderValue = (if s then -(n : ℤ) else n) ∧ (x.isNaN = false ↔ n ≤ maxOrderValue) := by
  obtain ⟨h1, h2⟩ := signBit_and_mod_of_toNat_eq hn h
  rw [orderValue_eq_mod, isNaN_eq_false_iff_le, h1, h2]
  exact ⟨rfl, Iff.rfl⟩

theorem orderValue_nextUp {x : Double} (hx : x.isNaN = false) (hi : x.bits ≠ huge.bits) :
    (nextUp x).orderValue = x.orderValue + 1 ∧ (nextUp x).isNaN = false := by
  have h := toNat_nextUp hx hi
  have hb := toNat_bits_eq_mod x
  have hk := (isNaN_eq_false_iff_le x).mp hx
  have hi' : x.bits.toNat ≠ maxOrderValue := fun h ↦
    hi (UInt64.toNat_inj.mp (h.trans toNat_huge.symm))
  rw [orderValue_eq_mod x]
  split_ifs at h with h0 hs
  · obtain ⟨h1, h2⟩ := orderValue_of_toNat_eq (x := nextUp x) (s := false) (n := 1) (by decide)
      (by simpa)
    rw [h1, h2, h0]; cases x.signBit <;> simp [maxOrderValue]
  · rw [hs] at hb ⊢
    obtain ⟨h1, h2⟩ := orderValue_of_toNat_eq (x := nextUp x) (s := true)
      (n := x.bits.toNat % 2 ^ 63 - 1) (by lia) (by simp; lia)
    simp only [h1, h2, ↓reduceIte]; constructor <;> lia
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hb ⊢
    obtain ⟨h1, h2⟩ := orderValue_of_toNat_eq (x := nextUp x) (s := false)
      (n := x.bits.toNat % 2 ^ 63 + 1) (by simp [maxOrderValue] at hk ⊢; lia) (by simp; lia)
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; constructor <;> lia

theorem nextUp_le_of_lt {x y : Double} (hi : x.bits ≠ huge.bits) (h : x.lt y = true) :
    (nextUp x).le y = true := by
  simp only [lt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hx, hy⟩, h⟩ := h
  obtain ⟨h1, h2⟩ := orderValue_nextUp hx hi
  simp only [le, h2, hy, Bool.not_false, Bool.true_and, decide_eq_true_eq, h1]
  lia

theorem toNat_huge_neg : huge.neg.bits.toNat = 2 ^ 63 + maxOrderValue := rfl

theorem isZero_neg (x : Double) : (neg x).isZero = x.isZero := by
  rw [isZero_eq_decide, isZero_eq_decide, toNat_mod_neg]

theorem nextDown_eq_neg_nextUp_neg (x : Double) : nextDown x = neg (nextUp (neg x)) := by
  have hn (b : UInt64) : neg ⟨b⟩ = ⟨b + 0x8000000000000000⟩ := congr(Double.mk $(bits_neg ⟨b⟩))
  have hh : ((neg x).bits == huge.bits) = (x.bits == huge.neg.bits) := by grind [bits_neg]
  simp only [nextDown, nextUp, isNaN_neg, isZero_neg, signBit_neg, hh]
  split_ifs <;> first | rw [Double.neg_neg] | rfl | (rw [bits_neg, hn, Double.mk.injEq]; grind)

theorem orderValue_nextDown {x : Double} (hx : x.isNaN = false) (hi : x.bits ≠ huge.neg.bits) :
    (nextDown x).orderValue = x.orderValue - 1 ∧ (nextDown x).isNaN = false := by
  have hi' : (neg x).bits ≠ huge.bits := fun h ↦ hi (by grind [bits_neg])
  obtain ⟨h1, h2⟩ := orderValue_nextUp (x := neg x) (by rwa [isNaN_neg]) hi'
  rw [nextDown_eq_neg_nextUp_neg, orderValue_neg, isNaN_neg, h1, orderValue_neg]
  exact ⟨by ring, h2⟩

/-! ### The conversions -/

theorem toDyadic_bounds (x : Double) :
    x.toDyadic.1.natAbs < 2 ^ 53 ∧ -1074 ≤ x.toDyadic.2 ∧ x.toDyadic.2 ≤ 972 := by
  have hF := fracField_lt x
  have hE := expField_lt x
  rw [toDyadic_eq]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> simp <;> lia

theorem toDyadic_fst_eq (x : Double) :
    x.toDyadic.1 = (if x.signBit then -1 else 1) * (x.toDyadic.1.natAbs : ℤ) := by
  rw [toDyadic_eq]
  dsimp only
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  split_ifs <;> simp

theorem isZero_eq_true_iff {x : Double} : x.isZero = true ↔ x.toRat = 0 := by
  rw [isZero_eq_decide, decide_eq_true_eq, ← expField_mul_add_fracField, toRat_eq_fields]
  refine ⟨fun h ↦ by rw [show x.expField = 0 by lia, show x.fracField = 0 by lia]; simp, fun h ↦ ?_⟩
  have h1 : (if x.signBit then (-1 : ℚ) else 1) ≠ 0 := by split_ifs <;> norm_num
  have h2 := (mul_eq_zero.mp h).resolve_left h1
  split_ifs at h2 with hE
  · rw [hE]; simpa using h2
  · exact absurd h2 (mul_ne_zero (by positivity) (zpow_ne_zero _ two_ne_zero))

theorem isZero_eq_false_iff {x : Double} : x.isZero = false ↔ x.toRat ≠ 0 := by
  rw [ne_eq, ← isZero_eq_true_iff, Bool.not_eq_true]

theorem toDyadic_fst_nonneg {x : Double} (h0 : 0 ≤ x.toRat) : 0 ≤ x.toDyadic.1 := by
  have hr := toRat_eq x
  by_contra hm
  have : (x.toDyadic.1 : ℚ) * 2 ^ x.toDyadic.2 < 0 :=
    mul_neg_of_neg_of_pos (mod_cast not_le.mp hm) (zpow_pos two_pos _)
  linarith

/-- The exact value of a double with the sign bit clear, by a natural significand. -/
theorem exists_toDyadic_eq_natCast {x : Double} (hs : x.signBit = false) :
    ∃ m : ℕ, x.toDyadic = ((m : ℤ), x.toDyadic.2) ∧ x.toRat = m * 2 ^ x.toDyadic.2 := by
  refine ⟨if x.expField = 0 then x.fracField else x.fracField + 2 ^ 52, ?_, ?_⟩
  · rw [toDyadic_eq, hs]; simp
  · rw [toRat_eq, toDyadic_eq, hs]; simp

/-- The truncation of the magnitude of `JPoints.Double.toDyadic x = (m, e)` that the conversions
compute is the floor of a double `x ≥ 0`. -/
theorem shift_eq_floor_toRat {x : Double} (h0 : 0 ≤ x.toRat) {m e : ℤ} (hd : x.toDyadic = (m, e)) :
    (if 0 ≤ e then m.natAbs <<< e.toNat else m.natAbs >>> (-e).toNat) = ⌊x.toRat⌋₊ := by
  have hm := toDyadic_fst_nonneg h0
  rw [hd] at hm
  rw [toNat_shift_eq_floor, toRat_eq, hd, Nat.cast_natAbs, Int.cast_abs,
    abs_of_nonneg (mod_cast hm)]

/-- A double whose value is below `2 ^ 1024` in absolute value is finite: an infinity or a NaN has
the exponent field `2047`, for which the value that `JPoints.Double.toRat` gives it is at least
`2 ^ 1024` in absolute value. -/
theorem isFinite_of_abs_toRat_lt {x : Double} (h : |x.toRat| < 2 ^ 1024) : x.isFinite = true := by
  by_contra hx
  have hE : x.expField = 2047 := by simpa [isFinite] using hx
  have h2 : (2 : ℚ) ^ 1024 ≤ (2 ^ 52 + x.fracField) * 2 ^ 972 := by
    rw [show (2 : ℚ) ^ 1024 = 2 ^ 52 * 2 ^ 972 by rw [← pow_add]]
    gcongr
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  rw [toRat_eq_fields, hE, ite_eq_right (c := (2047 : ℕ) = 0) (by norm_num),
    show ((2047 : ℕ) : ℤ) - 1075 = (972 : ℕ) by norm_num, zpow_natCast, abs_mul, abs_mul,
    abs_of_pos (pow_pos (two_pos (α := ℚ)) 972),
    abs_of_pos (by positivity : (0 : ℚ) < 2 ^ 52 + x.fracField)] at h
  split_ifs at h <;> simp only [abs_neg, abs_one, one_mul] at h <;>
    exact lt_irrefl _ (h2.trans_lt h)

theorem toInt_toInt64 {x : Double} (h0 : 0 ≤ x.toRat) (h1 : x.toRat < 2 ^ 63) :
    x.toInt64.toInt = ⌊x.toRat⌋₊ := by
  have hm := toDyadic_fst_nonneg h0
  rcases hd : x.toDyadic with ⟨m, e⟩
  rw [hd] at hm
  have hf : ⌊x.toRat⌋₊ < 2 ^ 63 := (Nat.floor_lt h0).mpr (mod_cast h1)
  have hx : x.isFinite = true := isFinite_of_abs_toRat_lt <|
    (abs_of_nonneg h0).symm ▸ h1.trans (pow_lt_pow_right₀ one_lt_two (by norm_num))
  simp only [toInt64, hx, hd, show ¬m < 0 by lia, ↓reduceIte]
  rw [shift_eq_floor_toRat h0 hd, ite_eq_left ⟨by lia, by lia⟩,
    Int64.toInt_ofInt_of_le (by lia) (by lia)]

theorem abs_toRat (x : Double) : |x.toRat| = x.toDyadic.1.natAbs * 2 ^ x.toDyadic.2 := by
  rw [toRat_eq, abs_mul, abs_of_pos (zpow_pos (two_pos (α := ℚ)) x.toDyadic.2), Nat.cast_natAbs,
    Int.cast_abs]

/-- Every finite double lies below `2 ^ 1025` in absolute value. -/
theorem abs_toRat_lt (x : Double) : |x.toRat| < 2 ^ 1025 := by
  obtain ⟨h1, -, h3⟩ := toDyadic_bounds x
  rw [abs_toRat]
  calc (x.toDyadic.1.natAbs : ℚ) * 2 ^ x.toDyadic.2 < 2 ^ 53 * 2 ^ (972 : ℤ) :=
        mul_lt_mul_of_pos_of_nonneg' (mod_cast h1)
          (zpow_le_zpow_right₀ one_le_two h3) (zpow_pos two_pos _) (by positivity)
    _ = 2 ^ 1025 := by rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; norm_num

/-- `(long)x` of a finite double `x` below `2 ^ 63` in absolute value truncates towards zero: it
lies within `1` of `x` (`JPoints.abs_ite_floor_sub_lt`). -/
theorem abs_toInt_toInt64_sub_lt {x : Double} (hx : x.isFinite = true)
    (h : |x.toRat| < 2 ^ 63) : |(x.toInt64.toInt : ℚ) - x.toRat| < 1 := by
  have hv := toRat_eq x
  have hfl := toNat_shift_eq_floor x.toDyadic.1.natAbs x.toDyadic.2
  rw [← abs_toRat] at hfl
  have ha63 : ⌊|x.toRat|⌋₊ < 2 ^ 63 := by
    have := (Nat.floor_le (abs_nonneg x.toRat)).trans_lt h
    exact_mod_cast this
  have hneg : x.toDyadic.1 < 0 ↔ x.toRat < 0 := by
    rw [hv]
    exact ⟨fun h ↦ mul_neg_of_neg_of_pos (mod_cast h) (zpow_pos two_pos _), fun h ↦ by
      by_contra! h'; exact h.not_ge (mul_nonneg (mod_cast h') (zpow_pos two_pos _).le)⟩
  simp only [toInt64, hx, ↓reduceIte, hfl]
  rw [ite_eq_left (by split_ifs <;> lia), Int64.toInt_ofInt_of_le (by split_ifs <;> lia)
    (by split_ifs <;> lia)]
  exact abs_ite_floor_sub_lt hneg

theorem natAbs_toDyadic_fst_ne_zero {x : Double} (hx0 : x.toRat ≠ 0) :
    x.toDyadic.1.natAbs ≠ 0 := fun h ↦ hx0 <| by
  rw [toRat_eq, Int.natAbs_eq_zero.mp h]; simp

theorem natCast_log2_add_nonneg {x : Double} (h : 1 ≤ |x.toRat|) :
    0 ≤ (x.toDyadic.1.natAbs.log2 : ℤ) + x.toDyadic.2 := by
  have h0 : x.toDyadic.1.natAbs ≠ 0 :=
    natAbs_toDyadic_fst_ne_zero fun h' ↦ by rw [h'] at h; norm_num at h
  have h1 := (two_zpow_log2_le_mul h0 x.toDyadic.2).2
  rw [← abs_toRat] at h1
  have := (one_lt_zpow_iff_right₀ one_lt_two).mp (h.trans_lt h1)
  lia

/-- The value `±|m| 2 ^ (e + k)` of a double with the sign of `x` and the magnitude of
`JPoints.Double.toDyadic x = (m, e)` scaled by `2 ^ k` is `x 2 ^ k`. -/
theorem sign_mul_natAbs_mul_zpow (x : Double) (k : ℤ) :
    (if x.signBit then -1 else 1) * ((x.toDyadic.1.natAbs : ℚ) * 2 ^ (x.toDyadic.2 + k)) =
      x.toRat * 2 ^ k := by
  rw [toRat_eq x, zpow_add₀ two_ne_zero]
  conv_rhs => rw [toDyadic_fst_eq x]
  rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs <;> push_cast <;> ring

/-! ### Signs -/

theorem toRat_nonneg {x : Double} (hs : x.signBit = false) : 0 ≤ x.toRat := by
  rw [toRat_eq_fields, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  split_ifs <;> exact mul_nonneg (by positivity) (zpow_nonneg zero_le_two _)

theorem signBit_eq_false_of_pos {x : Double} (h : 0 < x.toRat) : x.signBit = false := by
  by_contra hs
  rw [Bool.not_eq_false] at hs
  rw [toRat_eq_fields, hs] at h
  simp only [↓reduceIte, neg_one_mul, neg_pos] at h
  split_ifs at h <;>
    exact absurd h (not_lt.mpr (mul_nonneg (by positivity) (zpow_nonneg zero_le_two _)))

theorem signBit_eq_false_of_le {x : Double} {c : ℚ} (hc : 0 < c)
    (h : (c : WithBotTop ℚ) ≤ doubleValue x.bits) : x.signBit = false := by
  rw [doubleValue_bits] at h
  split_ifs at h with he hs
  · exact absurd h (not_le.2 (WithBotTop.bot_lt_coe c))
  · simpa using hs
  · exact signBit_eq_false_of_pos (hc.trans_le (WithBotTop.coe_le_coe.mp h))

/-- A finite double other than a zero is negative exactly when its sign bit is set. -/
theorem toRat_neg_iff {x : Double} (h0 : x.toRat ≠ 0) : x.toRat < 0 ↔ x.signBit = true := by
  cases hs : x.signBit
  · simpa using toRat_nonneg hs
  · have := toRat_nonneg (x := neg x) (by rw [signBit_neg, hs]; rfl)
    rw [toRat_neg] at this
    simpa using lt_of_le_of_ne (neg_nonneg.mp this) h0

/-- Two finite doubles other than zeros with the same sign bit have a positive product. -/
theorem mul_toRat_pos_of_signBit_eq {x y : Double} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0)
    (h : x.signBit = y.signBit) : 0 < x.toRat * y.toRat := by
  rcases lt_or_gt_of_ne hy with hy' | hy'
  · exact mul_pos_of_neg_of_neg ((toRat_neg_iff hx).mpr (h.trans ((toRat_neg_iff hy).mp hy'))) hy'
  · refine mul_pos (lt_of_le_of_ne (not_lt.mp fun h' ↦ ?_) hx.symm) hy'
    exact absurd ((toRat_neg_iff hy).mpr (h.symm.trans ((toRat_neg_iff hx).mp h'))) hy'.not_gt

/-! ### Comparisons off NaN -/

theorem lt_eq_true_iff' {x y : Double} :
    x.lt y = true ↔ ¬ IsNaN x.bits ∧ ¬ IsNaN y.bits ∧ doubleValue x.bits < doubleValue y.bits := by
  rw [← isNaN_eq_false_iff, ← isNaN_eq_false_iff]
  by_cases hx : x.isNaN = false
  · by_cases hy : y.isNaN = false
    · rw [lt_eq_true_iff hx hy]; simp [hx, hy]
    · simp_all [lt]
  · simp_all [lt]

theorem lt_iff_toRat_lt {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x < y ↔ x.toRat < y.toRat := by
  change x.lt y = true ↔ _
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite hx) (isNaN_eq_false_of_isFinite hy),
    doubleValue_eq_toRat hx, doubleValue_eq_toRat hy, WithBotTop.coe_lt_coe]

theorem le_iff_toRat_le {x y : Double} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    x ≤ y ↔ x.toRat ≤ y.toRat := by
  change x.le y = true ↔ _
  rw [le_eq_true_iff (isNaN_eq_false_of_isFinite hx) (isNaN_eq_false_of_isFinite hy),
    doubleValue_eq_toRat hx, doubleValue_eq_toRat hy, WithBotTop.coe_le_coe]

theorem doubleValue_lt_of_lt {x y : Double} (h : x < y) :
    doubleValue x.bits < doubleValue y.bits := by
  change x.lt y = true at h
  exact (lt_eq_true_iff'.mp h).2.2

theorem doubleValue_le_of_not_lt {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : ¬x < y) : doubleValue y.bits ≤ doubleValue x.bits := by
  change ¬x.lt y = true at h
  rw [lt_eq_true_iff hx hy, not_lt] at h
  exact h

/-- A double without a sign bit below a finite double is finite: neither a NaN nor `+∞`. -/
theorem isFinite_of_lt {x y : Double} (hs : x.signBit = false) (hy : y.isFinite = true)
    (h : x.lt y = true) : x.isFinite = true := by
  have hn : x.isNaN = false := by
    simp only [lt, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  cases hi : x.isInf
  · exact isFinite_of_isInf_eq_false hn hi
  · rw [lt_eq_true_iff hn (isNaN_eq_false_of_isFinite hy), doubleValue_of_isInf hi, hs,
      doubleValue_eq_toRat hy] at h
    simp at h

/-- A double that is no NaN between two doubles is finite. -/
theorem isFinite_of_lt_of_lt {x y z : Double} (hx : x.isNaN = false) (hy : y < x) (hz : x < z) :
    x.isFinite = true := by
  change y.lt x = true at hy
  change x.lt z = true at hz
  rw [lt_eq_true_iff'] at hy hz
  cases hf : x.isFinite
  · rw [doubleValue_of_isFinite_eq_false hx hf] at hy hz
    cases hs : x.signBit
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hz; exact absurd hz.2.2 (not_lt.mpr le_top)
    · simp only [hs, ↓reduceIte] at hy; exact absurd hy.2.2 (not_lt.mpr bot_le)
  · rfl

theorem neg_huge_lt {x : Double} (hx : x.isFinite = true) : -Double.huge < x := by
  change huge.neg.lt x = true
  rw [lt_eq_true_iff isNaN_huge_neg (isNaN_eq_false_of_isFinite hx), doubleValue_huge_neg,
    doubleValue_eq_toRat hx]
  exact WithBotTop.bot_lt_coe _

theorem lt_huge {x : Double} (hx : x.isFinite = true) : x < Double.huge := by
  change x.lt huge = true
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite hx) isNaN_huge, doubleValue_huge,
    doubleValue_eq_toRat hx]
  exact WithBotTop.coe_lt_top _

theorem signBit_eq_true_of_beq_huge {x : Double} (hx : x.isNaN = false)
    (hf : x.isFinite = false) (hb : x.beq huge = false) : x.signBit = true := by
  cases hs : x.signBit
  · have := doubleValue_of_isFinite_eq_false hx hf
    rw [hs] at this
    have h := (beq_eq_true_iff hx isNaN_huge).mpr (this.trans doubleValue_huge.symm)
    rw [hb] at h; exact absurd h (by decide)
  · rfl

theorem signBit_eq_false_of_beq_neg_huge {x : Double} (hx : x.isNaN = false)
    (hf : x.isFinite = false) (hb : x.beq (-huge) = false) : x.signBit = false := by
  cases hs : x.signBit
  · rfl
  · have := doubleValue_of_isFinite_eq_false hx hf
    rw [hs] at this
    have h := (beq_eq_true_iff hx isNaN_huge_neg).mpr (this.trans doubleValue_huge_neg.symm)
    change x.beq huge.neg = false at hb
    rw [hb] at h; exact absurd h (by decide)

/-- A double that is `+∞` lies above every rational. -/
theorem coe_lt_doubleValue_of_beq_huge {x : Double} (hx : x.isNaN = false)
    (h : x.beq huge = true) (q : ℚ) : (q : WithBotTop ℚ) < doubleValue x.bits :=
  (beq_eq_true_iff hx isNaN_huge).mp h ▸ doubleValue_huge ▸ WithBotTop.coe_lt_top _

/-- A double that is `-∞` lies below every rational. -/
theorem doubleValue_lt_coe_of_beq_neg_huge {x : Double} (hx : x.isNaN = false)
    (h : x.beq (-huge) = true) (q : ℚ) : doubleValue x.bits < (q : WithBotTop ℚ) := by
  change x.beq huge.neg = true at h
  exact (beq_eq_true_iff hx isNaN_huge_neg).mp h ▸ doubleValue_huge_neg ▸ WithBotTop.bot_lt_coe _

/-- A double that is no NaN, not `+∞` and above some value is finite. -/
theorem isFinite_of_not_beq_huge_of_lt_doubleValue {x : Double} {q : WithBotTop ℚ}
    (hx : x.isNaN = false) (hb : ¬x.beq huge = true) (h : q < doubleValue x.bits) :
    x.isFinite = true := by
  cases hf : x.isFinite
  · have hv := doubleValue_of_isFinite_eq_false hx hf
    rw [signBit_eq_true_of_beq_huge hx hf (by simpa using hb)] at hv
    rw [hv] at h
    exact absurd h (not_lt.mpr bot_le)
  · rfl

/-- A double that is no NaN, not `-∞` and below some value is finite. -/
theorem isFinite_of_not_beq_neg_huge_of_doubleValue_lt {x : Double} {q : WithBotTop ℚ}
    (hx : x.isNaN = false) (hb : ¬x.beq (-huge) = true) (h : doubleValue x.bits < q) :
    x.isFinite = true := by
  cases hf : x.isFinite
  · have hv := doubleValue_of_isFinite_eq_false hx hf
    rw [signBit_eq_false_of_beq_neg_huge hx hf (by simpa using hb)] at hv
    rw [hv] at h
    exact absurd h (not_lt.mpr le_top)
  · rfl

end Double

end JPoints

end
