/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Region
public import JPoints.Proof.DoubleArith

import JPoints.Mathlib.Order.WithBotTop
import JPoints.Proof.Constants
import Mathlib.Algebra.Order.Field.Power

/-!
# The ends of the excluded intervals of the real region in doubles

The ends `B x - A x x` of the excluded intervals of the third coordinate `c` that `row_region`
computes in doubles for the row `(a, b)`, `A = (double)a`, `B = (double)b`, moved inwards by the
margins `1e-9 (|C| + 1) + 1` and truncated with a slack of `2`, keep every `c` on the right side
of the exact value `C(x) = b x - a x²` when `1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`: a `c` above
a raised lower end lies above `C(x)` (`JPoints.Double.value_lt_of_marginLo`), a `c` below a lowered
upper end below it (`JPoints.Double.lt_value_of_marginHi`), and for `a = 0` the same holds for
`B x` and `c / b` (`JPoints.Double.lt_div_of_marginLo`, `JPoints.Double.div_lt_of_marginHi`).

The bound `2 ^ 26` keeps the products `B x` and `A x x` below `2 ^ 53` near `x = b / a`, where
they cancel: there each of the three roundings errs by at most half a unit, and the computed end
lies within `7 / 4` of `C(x)` (`JPoints.abs_sub_le_of_roundings`), which the margin and the slack
cover; away from `b / a`, the relative error is far below the relative margin `10 ^ (-9)`. At
`|x| > 2 ^ 480`, where `a x²` dwarfs `b x`, the end is a NaN or below `-2 ^ 900`
(`JPoints.Double.isNaN_or_doubleValue_value_le`), so that no upper end there takes out a word;
the margins of such ends, `+∞` and NaNs included, keep their side of `ROW_BEYOND`
(`JPoints.Double.isNaN_eq_false_and_marginHi_le`, `JPoints.Double.isNaN_eq_false_and_le_marginLo`).
The words wholly inside an excluded interval, from `(long)xl + 2` to `(long)xh - 2`, lie strictly
inside it with a slack of `1` (`JPoints.le_or_lt_of_rowRegionEnds_fst_le`,
`JPoints.le_or_lt_of_lt_rowRegionEnds_snd`), since `(long)` truncates
(`JPoints.Double.abs_toInt_toInt64_sub_lt`).

## Main statements

* `JPoints.abs_sub_le_of_roundings`: the error of `B x - A x x` below the bound.
* `JPoints.Double.isFinite_margin_and_bounds`, `JPoints.Double.isFinite_marginLo_and_le`,
  `JPoints.Double.isFinite_marginHi_and_le`: the margins of finite ends.
* `JPoints.Double.isNaN_or_doubleValue_value_le`: the ends far out.
* `JPoints.Double.value_lt_of_marginLo`, `JPoints.Double.lt_value_of_marginHi`,
  `JPoints.Double.lt_div_of_marginLo`, `JPoints.Double.div_lt_of_marginHi`: the ends.

## Implementation notes

The error bounds are those of `JPoints.Double.IsRounding`, with the infinities of the overflow
signed by `JPoints.Double.doubleValue_add_of_isFinite_eq_false` and the products of infinities by
`JPoints.Double.mul_of_isInf`. `linarith` reads no power of `2` above the exponent threshold, so the
large powers are named by `generalize` before it runs.
-/

@[expose] public section

namespace JPoints

theorem two_zpow_neg_1075_le_mul {X : ℚ} (hX : |X| ≤ 2 ^ 480) :
    2 ^ (-1075 : ℤ) * |X| ≤ 1 / 1000 :=
  calc 2 ^ (-1075 : ℤ) * |X| ≤ 2 ^ (-1075 : ℤ) * 2 ^ 480 := by gcongr
    _ = 2 ^ (-595 : ℤ) := by rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; norm_num
    _ ≤ 2 ^ (-10 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
    _ ≤ 1 / 1000 := by norm_num

theorem two_zpow_neg_1075_le_inv : (2 : ℚ) ^ (-1075 : ℤ) ≤ 1 / 1000 :=
  (zpow_le_zpow_right₀ one_le_two (by norm_num : (-1075 : ℤ) ≤ -10)).trans (by norm_num)

/-- A rounding `q` of `a x`, `a ≥ 1`, bounds `|q x|` and `|(q - a x) x|`. -/
theorem abs_mul_le_of_abs_sub_le {a X q η : ℚ} (ha : 1 ≤ a)
    (hq : |q - a * X| ≤ |a * X| / 2 ^ 53 + η) :
    |q * X| ≤ (a * |X| + a * |X| / 2 ^ 53 + η) * |X| ∧
      |(q - a * X) * X| ≤ (a * |X| / 2 ^ 53 + η) * |X| := by
  have haX : |a * X| = a * |X| := by rw [abs_mul, abs_of_pos (by linarith)]
  rw [haX] at hq
  have h1 : |q| ≤ a * |X| + a * |X| / 2 ^ 53 + η := by
    linarith [abs_sub_abs_le_abs_sub q (a * X)]
  rw [abs_mul, abs_mul]
  exact ⟨mul_le_mul_of_nonneg_right h1 (abs_nonneg X),
    mul_le_mul_of_nonneg_right hq (abs_nonneg X)⟩

/-- The error of `B x - A x x` with the roundings `q` of `a x`, `p₁` of `b x`, `p₂` of `q x` and
`e` of `p₁ - p₂`, each within half a unit in its last place, by the error of each step: at most
`|C| / 2 ^ 53` for the last rounding, and `(1 + 2 ^ (-53))` times the error `D` of `p₁ - p₂`, which
the products `|b| |x|` and `a x²` bound. -/
private theorem abs_sub_le_of_roundings' {a b X q p₁ p₂ e : ℚ} (ha : 1 ≤ a)
    (hq : |q - a * X| ≤ |a * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (hp₁ : |p₁ - b * X| ≤ |b * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (hp₂ : |p₂ - q * X| ≤ |q * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (he : |e - (p₁ - p₂)| ≤ |p₁ - p₂| / 2 ^ 53 + 2 ^ (-1075 : ℤ)) :
    |e - (b * X - a * X * X)| ≤ |b * X - a * X * X| / 2 ^ 53 + (1 + 1 / 2 ^ 53) *
      (|b| * |X| / 2 ^ 53 + a * |X| * |X| * (2 / 2 ^ 53 + 1 / 2 ^ 106) + 3 * 2 ^ (-1075 : ℤ) +
        2 * (2 ^ (-1075 : ℤ) * |X|)) + 2 ^ (-1075 : ℤ) := by
  have hX0 := abs_nonneg X
  obtain ⟨h2, h3⟩ := abs_mul_le_of_abs_sub_le ha hq
  rw [abs_mul] at hp₁
  have h4 : |p₂ - a * X * X| ≤ |p₂ - q * X| + |(q - a * X) * X| := by
    rw [show p₂ - a * X * X = (p₂ - q * X) + (q - a * X) * X by ring]; exact abs_add_le _ _
  have h5 : |p₁ - p₂ - (b * X - a * X * X)| ≤ |p₁ - b * X| + |p₂ - a * X * X| := by
    rw [show p₁ - p₂ - (b * X - a * X * X) = (p₁ - b * X) - (p₂ - a * X * X) by ring]
    exact abs_sub _ _
  have h6 := abs_sub_abs_le_abs_sub (p₁ - p₂) (b * X - a * X * X)
  have h7 : |e - (b * X - a * X * X)| ≤ |e - (p₁ - p₂)| + |p₁ - p₂ - (b * X - a * X * X)| := by
    rw [show e - (b * X - a * X * X) = (e - (p₁ - p₂)) + (p₁ - p₂ - (b * X - a * X * X)) by ring]
    exact abs_add_le _ _
  have hD : |p₁ - p₂ - (b * X - a * X * X)| ≤ |b| * |X| / 2 ^ 53 +
      a * |X| * |X| * (2 / 2 ^ 53 + 1 / 2 ^ 106) + 3 * 2 ^ (-1075 : ℤ) +
        2 * (2 ^ (-1075 : ℤ) * |X|) := by
    have hη0 : (0 : ℚ) < 2 ^ (-1075 : ℤ) := by positivity
    nlinarith [mul_nonneg hη0.le hX0]
  nlinarith

/-- The error of `B x - A x x` with a rounding in each step, bounded by the products `P = |b| |x|`
and `Q = a x²` and the value `C`, is at most `7 / 4 + C / 2 ^ 40` near `x = b / a`, where
`P ≤ 17 b² / 16` and `Q ≤ 289 b² / 256` with `b² ≤ 2 ^ 52`. -/
theorem roundings_bound_le_of_near {b P Q C t η : ℚ} (hb : b ^ 2 ≤ 2 ^ 52)
    (hP : P ≤ 17 * b ^ 2 / 16) (hQ : Q ≤ 289 * b ^ 2 / 256) (hC : 0 ≤ C) (ht : t ≤ 1 / 1000)
    (hη : η ≤ 1 / 1000) :
    C / 2 ^ 53 + (1 + 1 / 2 ^ 53) * (P / 2 ^ 53 + Q * (2 / 2 ^ 53 + 1 / 2 ^ 106) + 3 * η +
      2 * t) + η ≤ 7 / 4 + C / 2 ^ 40 := by
  norm_num at *
  linarith

/-- The error of `B x - A x x` with a rounding in each step, bounded by the products `P = |b| |x|`
and `Q = a x²` and the value `C`, is at most `7 / 4 + C / 2 ^ 40` away from `x = b / a`, where
`P ≤ 16 Q / 17` and `Q ≤ 17 C`. -/
theorem roundings_bound_le_of_far {P Q C t η : ℚ} (hP : P ≤ 16 * Q / 17) (hQ : Q ≤ 17 * C)
    (hC : 0 ≤ C) (ht : t ≤ 1 / 1000) (hη : η ≤ 1 / 1000) :
    C / 2 ^ 53 + (1 + 1 / 2 ^ 53) * (P / 2 ^ 53 + Q * (2 / 2 ^ 53 + 1 / 2 ^ 106) + 3 * η +
      2 * t) + η ≤ 7 / 4 + C / 2 ^ 40 := by
  norm_num at *
  linarith

/-- `|x| a` within `17 |b| / 16` keeps the products of `b x - a x²` below `17 b² / 16` and
`289 b² / 256`. -/
theorem mul_abs_le_and_mul_abs_le_of_near {a b X : ℚ} (ha : 1 ≤ a)
    (hc : 16 * (a * |X|) ≤ 17 * |b|) :
    |b| * |X| ≤ 17 * b ^ 2 / 16 ∧ a * |X| * |X| ≤ 289 * b ^ 2 / 256 := by
  have hX0 := abs_nonneg X
  have hXb : |X| ≤ 17 * |b| / 16 := by linarith [le_mul_of_one_le_left hX0 ha]
  refine ⟨?_, ?_⟩
  · calc |b| * |X| ≤ |b| * (17 * |b| / 16) := mul_le_mul_of_nonneg_left hXb (abs_nonneg b)
      _ = 17 * b ^ 2 / 16 := by rw [← sq_abs b]; ring
  · calc a * |X| * |X| ≤ (17 * |b| / 16) * (17 * |b| / 16) :=
          mul_le_mul (by linarith) hXb hX0 (by positivity)
      _ = 289 * b ^ 2 / 256 := by rw [← sq_abs b]; ring

/-- `|x| a` beyond `17 |b| / 16` keeps `|b x|` below `16 a x² / 17` and `a x²` below
`17 |b x - a x²|`. -/
theorem mul_abs_le_and_mul_abs_le_of_far {a b X : ℚ} (ha : 1 ≤ a)
    (hc : 17 * |b| < 16 * (a * |X|)) :
    |b| * |X| ≤ 16 * (a * |X| * |X|) / 17 ∧ a * |X| * |X| ≤ 17 * |b * X - a * X * X| := by
  have hX0 := abs_nonneg X
  have haX : |a * X| = a * |X| := by rw [abs_mul, abs_of_pos (by linarith)]
  have hCX : |X| * (a * |X| / 17) ≤ |b * X - a * X * X| := by
    rw [show b * X - a * X * X = X * (b - a * X) by ring, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ hX0
    linarith [abs_sub_abs_le_abs_sub (a * X) b, abs_sub_comm (a * X) b]
  refine ⟨?_, by linarith⟩
  calc |b| * |X| ≤ (16 * (a * |X|) / 17) * |X| := mul_le_mul_of_nonneg_right (by linarith) hX0
    _ = 16 * (a * |X| * |X|) / 17 := by ring

/-- `B x - A x x` in doubles, with the roundings `q` of `a x`, `p₁` of `b x`, `p₂` of `q x` and `e`
of `p₁ - p₂`, for `a ≥ 1`, `b² ≤ 2 ^ 52` and `|x| ≤ 2 ^ 480`, lies within `7 / 4 + |C| / 2 ^ 40`
of `C = b x - a x²`: near `x = b / a`, where the products cancel, they stay below about `2 ^ 52`,
and each rounding errs by at most half a unit; away from it, `|C|` is at least a seventeenth of
`a x²`, and the error is relative. -/
theorem abs_sub_le_of_roundings {a b X q p₁ p₂ e : ℚ} (ha : 1 ≤ a) (hb : b ^ 2 ≤ 2 ^ 52)
    (hX : |X| ≤ 2 ^ 480) (hq : |q - a * X| ≤ |a * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (hp₁ : |p₁ - b * X| ≤ |b * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (hp₂ : |p₂ - q * X| ≤ |q * X| / 2 ^ 53 + 2 ^ (-1075 : ℤ))
    (he : |e - (p₁ - p₂)| ≤ |p₁ - p₂| / 2 ^ 53 + 2 ^ (-1075 : ℤ)) :
    |e - (b * X - a * X * X)| ≤ 7 / 4 + |b * X - a * X * X| / 2 ^ 40 := by
  refine (abs_sub_le_of_roundings' ha hq hp₁ hp₂ he).trans ?_
  have hC := abs_nonneg (b * X - a * X * X)
  rcases le_or_gt (16 * (a * |X|)) (17 * |b|) with hc | hc
  · obtain ⟨hP, hQ⟩ := mul_abs_le_and_mul_abs_le_of_near ha hc
    exact roundings_bound_le_of_near hb hP hQ hC (two_zpow_neg_1075_le_mul hX)
      two_zpow_neg_1075_le_inv
  · obtain ⟨hP, hQ⟩ := mul_abs_le_and_mul_abs_le_of_far ha hc
    exact roundings_bound_le_of_far hP hQ hC (two_zpow_neg_1075_le_mul hX)
      two_zpow_neg_1075_le_inv

/-- The margin `1.0e-9 * (|x| + 1.0) + 1.0` of `row_region` with the roundings of its three
operations, for `E = |x|`. -/
theorem margin_bounds_of_roundings {E t₁ t₂ m d η : ℚ} (hE : 0 ≤ E) (hd₁ : 1 / 10 ^ 9 ≤ d)
    (hd₂ : d ≤ 2 / 10 ^ 9) (hη : η ≤ 1 / 2 ^ 200)
    (h₁ : |t₁ - (E + 1)| ≤ |E + 1| / 2 ^ 53 + η) (h₂ : |t₂ - d * t₁| ≤ |d * t₁| / 2 ^ 53 + η)
    (h₃ : |m - (t₂ + 1)| ≤ |t₂ + 1| / 2 ^ 53 + η) :
    1 - 1 / 2 ^ 41 + E / 2 ^ 30 ≤ m ∧ m ≤ 2 + E := by
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ E + 1), abs_le] at h₁
  have ht₁ : 0 ≤ t₁ := by linarith
  rw [abs_of_nonneg (by positivity : 0 ≤ d * t₁), abs_le] at h₂
  have ht₂ : 0 ≤ t₂ := by nlinarith
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ t₂ + 1), abs_le] at h₃
  constructor <;> nlinarith

namespace Double

theorem IsRounding.isFinite_of_abs_le_mul {x : Double} {v : ℚ} (h : x.IsRounding v)
    (hv : |v| ≤ 2 ^ 1000 * 2 ^ 21) : x.isFinite = true :=
  h.isFinite_of_abs_le (n := 1021) (by norm_num) (by rwa [← pow_add] at hv)

/-- `fabs(x) + 1.0` for a finite `x` of absolute value at most `2 ^ 1000`: finite, a rounding of
`|x| + 1`, and at most `2 ^ 1001 + 3` in absolute value. -/
theorem isFinite_fabs_add_one {x : Double} (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 1000) :
    (x.fabs + 1.0).isFinite = true ∧ (x.fabs + 1.0).IsRounding (|x.toRat| + 1) ∧
      |(x.fabs + 1.0).toRat| ≤ 2 * 2 ^ 1000 + 3 := by
  have hK1 : (1 : ℚ) ≤ 2 ^ 1000 := one_le_pow₀ one_le_two
  have h1 := isRounding_add ((isFinite_fabs x).trans hx) isFinite_one
  rw [toRat_fabs, toRat_one] at h1
  have hX0 := abs_nonneg x.toRat
  have hf1 := h1.isFinite_of_abs_le_mul (by
    rw [abs_of_nonneg (by positivity)]; generalize (2 : ℚ) ^ 1000 = K at *; linarith)
  have hb1 := h1.abs_toRat_le hf1
  rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ |x.toRat| + 1)] at hb1
  exact ⟨hf1, h1, by generalize (2 : ℚ) ^ 1000 = K at *; linarith⟩

/-- `1.0e-9 * t` for a finite `t` of absolute value at most `2 ^ 1001 + 3`: finite, a rounding of
the product with the value of the double `1.0e-9`, and at most `2 ^ 1002 + 7` in absolute
value. -/
theorem isFinite_one_e_neg_nine_mul {t : Double} (ht : t.isFinite = true)
    (hT : |t.toRat| ≤ 2 * 2 ^ 1000 + 3) :
    (1.0e-9 * t).isFinite = true ∧
      (1.0e-9 * t).IsRounding (4835703278458517 / 2 ^ 82 * t.toRat) ∧
      |(1.0e-9 * t).toRat| ≤ 2 * (2 * 2 ^ 1000 + 3) + 1 := by
  have h2 := isRounding_mul isFinite_one_e_neg_nine ht
  rw [toRat_one_e_neg_nine] at h2
  have hd : |(4835703278458517 / 2 ^ 82 : ℚ) * t.toRat| ≤ |t.toRat| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 4835703278458517 / 2 ^ 82)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num)
  have hK1 : (1 : ℚ) ≤ 2 ^ 1000 := one_le_pow₀ one_le_two
  have hf2 := h2.isFinite_of_abs_le_mul (by generalize (2 : ℚ) ^ 1000 = K at *; linarith)
  have hb2 := h2.abs_toRat_le hf2
  exact ⟨hf2, h2, by generalize (2 : ℚ) ^ 1000 = K at *; linarith⟩

/-- The margin `1.0e-9 * (|x| + 1.0) + 1.0` of `row_region` for a finite `x` of absolute value at
most `2 ^ 1000`: finite, at least `1 - 2 ^ (-41) + |x| / 2 ^ 30` and at most `2 + |x|`, by the
roundings of its three operations (`JPoints.margin_bounds_of_roundings`). -/
theorem isFinite_margin_and_bounds {x : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 1000) :
    (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).isFinite = true ∧
      1 - 1 / 2 ^ 41 + |x.toRat| / 2 ^ 30 ≤ (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat ∧
      (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat ≤ 2 + |x.toRat| := by
  obtain ⟨hf1, h1, hb1⟩ := isFinite_fabs_add_one hx hX
  obtain ⟨hf2, h2, hb2⟩ := isFinite_one_e_neg_nine_mul hf1 hb1
  have h3 := isRounding_add hf2 isFinite_one
  rw [toRat_one] at h3
  have hf3 := h3.isFinite_of_abs_le_mul (by
    have := abs_add_le (1.0e-9 * (x.fabs + 1.0) : Double).toRat 1
    have hK1 : (1 : ℚ) ≤ 2 ^ 1000 := one_le_pow₀ one_le_two
    generalize (2 : ℚ) ^ 1000 = K at *; norm_num at *; linarith)
  refine ⟨hf3, margin_bounds_of_roundings (abs_nonneg _) (by norm_num) (by norm_num)
    two_zpow_neg_1075_le (h1.abs_sub_le hf1) (h2.abs_sub_le hf2) (h3.abs_sub_le hf3)⟩

/-- A finite lower end `x` of an excluded interval of `row_region`, of absolute value at most
`2 ^ 1000`, raised by its margin: finite, and at least `x + 1 - 2 ^ (-40) + |x| / 2 ^ 31`. -/
theorem isFinite_marginLo_and_le {x : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 1000) :
    (if -Double.huge < x then x + (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).isFinite = true ∧
      x.toRat + 1 - 1 / 2 ^ 40 + |x.toRat| / 2 ^ 31 ≤
        (if -Double.huge < x then x + (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).toRat := by
  rw [ite_eq_left (neg_huge_lt hx)]
  obtain ⟨hm, hm1, hm2⟩ := isFinite_margin_and_bounds hx hX
  have h := isRounding_add hx hm
  have hX0 := abs_nonneg x.toRat
  have hm0 : 0 ≤ (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat := by
    linarith [abs_nonneg x.toRat]
  have ha := abs_add_le x.toRat (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat
  rw [abs_of_nonneg hm0] at ha
  have hf := h.isFinite_of_abs_le_mul (by
    have hK1 : (1 : ℚ) ≤ 2 ^ 1000 := one_le_pow₀ one_le_two
    generalize (2 : ℚ) ^ 1000 = K at *; linarith)
  have he := h.abs_sub_le hf
  rw [abs_le] at he
  exact ⟨hf, by linarith [two_zpow_neg_1075_le]⟩

/-- A finite upper end `x` of an excluded interval of `row_region`, of absolute value at most
`2 ^ 1000`, lowered by its margin: finite, and at most `x - 1 + 2 ^ (-40) - |x| / 2 ^ 31`. -/
theorem isFinite_marginHi_and_le {x : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 1000) :
    (if x < Double.huge then x - (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).isFinite = true ∧
      (if x < Double.huge then x - (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).toRat ≤
        x.toRat - 1 + 1 / 2 ^ 40 - |x.toRat| / 2 ^ 31 := by
  rw [ite_eq_left (lt_huge hx)]
  obtain ⟨hm, hm1, hm2⟩ := isFinite_margin_and_bounds hx hX
  have h := isRounding_sub hx hm
  have hX0 := abs_nonneg x.toRat
  have hm0 : 0 ≤ (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat := by
    linarith [abs_nonneg x.toRat]
  have ha := abs_sub x.toRat (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double).toRat
  rw [abs_of_nonneg hm0] at ha
  have hf := h.isFinite_of_abs_le_mul (by
    have hK1 : (1 : ℚ) ≤ 2 ^ 1000 := one_le_pow₀ one_le_two
    generalize (2 : ℚ) ^ 1000 = K at *; linarith)
  have he := h.abs_sub_le hf
  rw [abs_le] at he
  exact ⟨hf, by linarith [two_zpow_neg_1075_le]⟩

/-- `(double)n * x` for `|n| ≤ 2 ^ 26` at a finite `x` of absolute value at most `2 ^ 480`:
finite, a rounding of `n x`, and at most `2 ^ 508` in absolute value. -/
theorem isFinite_ofInt_mul {n : ℤ} (hn : |n| ≤ 2 ^ 26) {x : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 480) :
    (ofInt n * x).isFinite = true ∧ (ofInt n * x).IsRounding (n * x.toRat) ∧
      |(ofInt n * x).toRat| ≤ 2 ^ 28 * 2 ^ 480 := by
  obtain ⟨hN, hN'⟩ := isFinite_ofInt_and_toRat (n := n) (by lia)
  have h := isRounding_mul hN hx
  rw [hN'] at h
  have hn' : |(n : ℚ)| ≤ 2 ^ 26 := mod_cast hn
  have hnX : |(n : ℚ) * x.toRat| ≤ 2 ^ 26 * 2 ^ 480 := by
    rw [abs_mul]; exact mul_le_mul hn' hX (abs_nonneg _) (by positivity)
  have hPK : (2 : ℚ) ^ 26 * 2 ^ 480 ≤ 2 ^ 1000 * 2 ^ 21 := by
    simp only [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)
  have hf := h.isFinite_of_abs_le_mul (hnX.trans hPK)
  have hb := h.abs_toRat_le hf
  have hP1 : (1 : ℚ) ≤ 2 ^ 480 := one_le_pow₀ one_le_two
  exact ⟨hf, h, by clear hPK; generalize (2 : ℚ) ^ 480 = P at *; linarith⟩

/-- `q * x` for finite doubles with `|q| ≤ 2 ^ 508` and `|x| ≤ 2 ^ 480`: finite, a rounding of the
product, and at most `2 ^ 989` in absolute value. -/
theorem isFinite_mul_of_abs_le {q x : Double} (hq : q.isFinite = true)
    (hqb : |q.toRat| ≤ 2 ^ 28 * 2 ^ 480) (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 480) :
    (q * x).isFinite = true ∧ (q * x).IsRounding (q.toRat * x.toRat) ∧
      |(q * x).toRat| ≤ 2 ^ 30 * 2 ^ 480 * 2 ^ 480 := by
  have h := isRounding_mul hq hx
  have hqX : |q.toRat * x.toRat| ≤ 2 ^ 28 * 2 ^ 480 * 2 ^ 480 := by
    rw [abs_mul]; exact mul_le_mul hqb hX (abs_nonneg _) (by positivity)
  have hP1 : (1 : ℚ) ≤ 2 ^ 480 := one_le_pow₀ one_le_two
  have hPK : (2 : ℚ) ^ 480 * 2 ^ 480 * 2 ^ 30 ≤ 2 ^ 1000 * 2 ^ 21 := by
    simp only [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)
  have hf := h.isFinite_of_abs_le_mul (by
    generalize (2 : ℚ) ^ 480 = P at *; generalize (2 : ℚ) ^ 1000 = K at *; nlinarith)
  have hb := h.abs_toRat_le hf
  refine ⟨hf, h, ?_⟩
  have : (1 : ℚ) ≤ 2 ^ 480 * 2 ^ 480 := one_le_mul_of_one_le_of_one_le hP1 hP1
  generalize (2 : ℚ) ^ 480 = P at *; nlinarith

/-- `B x - A x x` in doubles for `A = (double)a` and `B = (double)b` with `1 ≤ a ≤ 2 ^ 26` and
`|b| ≤ 2 ^ 26`, at a finite `x` of absolute value at most `2 ^ 480`: finite, and within
`7 / 4 + |C| / 2 ^ 40` of `C = b x - a x²` (`JPoints.abs_sub_le_of_roundings`). -/
theorem isFinite_value_and_abs_sub_le {a b : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26)
    (hb : |b| ≤ 2 ^ 26) {x : Double} (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 480) :
    (ofInt b * x - ofInt a * x * x).isFinite = true ∧
      |(ofInt b * x - ofInt a * x * x).toRat - (b * x.toRat - a * x.toRat * x.toRat)| ≤
        7 / 4 + |b * x.toRat - a * x.toRat * x.toRat| / 2 ^ 40 := by
  obtain ⟨hqf, hq, hqb⟩ := isFinite_ofInt_mul (n := a) (by rw [abs_of_pos (by lia)]; lia) hx hX
  obtain ⟨hp₁f, hp₁, hp₁b⟩ := isFinite_ofInt_mul hb hx hX
  obtain ⟨hp₂f, hp₂, hp₂b⟩ := isFinite_mul_of_abs_le hqf hqb hx hX
  have he := isRounding_sub hp₁f hp₂f
  have hef := he.isFinite_of_abs_le_mul (by
    have := abs_sub (ofInt b * x).toRat (ofInt a * x * x).toRat
    have hPK : (2 : ℚ) ^ 480 * 2 ^ 480 * 2 ^ 31 ≤ 2 ^ 1000 * 2 ^ 21 := by
      simp only [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)
    have hP1 : (1 : ℚ) ≤ 2 ^ 480 := one_le_pow₀ one_le_two
    clear hX
    generalize (2 : ℚ) ^ 480 = P at *; generalize (2 : ℚ) ^ 1000 = K at *; nlinarith)
  refine ⟨hef, abs_sub_le_of_roundings (mod_cast ha) ?_ hX (hq.abs_sub_le hqf)
    (hp₁.abs_sub_le hp₁f) (hp₂.abs_sub_le hp₂f) (he.abs_sub_le hef)⟩
  rw [← sq_abs]
  exact (pow_le_pow_left₀ (abs_nonneg _) (mod_cast hb : |(b : ℚ)| ≤ 2 ^ 26) 2).trans (by norm_num)

theorem isNonneg_margin {x : Double} (hx : x.isNaN = false) :
    IsNonneg (1.0e-9 * (x.fabs + 1.0) + 1.0 : Double) :=
  (IsNonneg.mul ⟨by decide, by decide⟩ (by decide +kernel) (by decide +kernel)
    ((isNonneg_fabs hx).add isNonneg_one)).add isNonneg_one

theorem isNaN_eq_false_and_marginHi_le {x : Double} (hx : x.isNaN = false) {K : ℚ} (hK : 1 ≤ K)
    (hxK : doubleValue x.bits ≤ ((-K : ℚ) : WithBotTop ℚ)) :
    (if x < huge then x - (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).isNaN = false ∧
      doubleValue (if x < huge then x - (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).bits ≤
        ((-K / 2 : ℚ) : WithBotTop ℚ) := by
  have hlt : x < huge := by
    change x.lt huge = true
    rw [lt_eq_true_iff hx isNaN_huge, doubleValue_huge]
    exact hxK.trans_lt (WithBotTop.coe_lt_top _)
  rw [ite_eq_left hlt]
  exact doubleValue_sub_le_of_isNonneg hx hK hxK (isNonneg_margin hx)

theorem isNaN_eq_false_and_le_marginLo {x : Double} (hx : x.isNaN = false) {K : ℚ} (hK : 1 ≤ K)
    (hxK : ((K : ℚ) : WithBotTop ℚ) ≤ doubleValue x.bits) :
    (if -huge < x then x + (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).isNaN = false ∧
      ((K / 2 : ℚ) : WithBotTop ℚ) ≤
        doubleValue (if -huge < x then x + (1.0e-9 * (x.fabs + 1.0) + 1.0) else x).bits := by
  have hlt : -huge < x := by
    change huge.neg.lt x = true
    rw [lt_eq_true_iff isNaN_huge_neg hx, doubleValue_huge_neg]
    exact (WithBotTop.bot_lt_coe _).trans_le hxK
  rw [ite_eq_left hlt]
  exact doubleValue_add_ge_of_isNonneg hx hK hxK (isNonneg_margin hx)

theorem marginHi_of_isNaN {x : Double} (hx : x.isNaN = true) :
    (if x < huge then x - (1.0e-9 * (x.fabs + 1.0) + 1.0) else x) = x := by
  have : ¬x < huge := by simp [LT.lt, Double.lt, hx]
  rw [ite_eq_right this]

/-- A double that is no NaN and lies strictly between `-ROW_BEYOND` and `ROW_BEYOND` is finite. -/
theorem isFinite_and_abs_lt_of_not_le {x : Double} (hx : x.isNaN = false)
    (h1 : ¬x ≤ -rowBeyond) (h2 : ¬rowBeyond ≤ x) :
    x.isFinite = true ∧ |x.toRat| < rowBeyond.toRat := by
  have hR := isFinite_rowBeyond
  have hR' : rowBeyond.neg.isFinite = true := (isFinite_neg rowBeyond).trans hR
  change ¬x.le rowBeyond.neg = true at h1
  change ¬rowBeyond.le x = true at h2
  rw [le_eq_true_iff hx (isNaN_eq_false_of_isFinite hR'), not_le] at h1
  rw [le_eq_true_iff (isNaN_eq_false_of_isFinite hR) hx, not_le] at h2
  rw [doubleValue_eq_toRat hR'] at h1
  rw [doubleValue_eq_toRat hR] at h2
  cases hf : x.isFinite
  · rw [doubleValue_of_isFinite_eq_false hx hf] at h1 h2
    cases hs : x.signBit
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h2
      exact absurd h2 (not_lt.mpr le_top)
    · simp only [hs, ↓reduceIte] at h1
      exact absurd h1 (not_lt.mpr bot_le)
  rw [doubleValue_eq_toRat hf, WithBotTop.coe_lt_coe] at h1 h2
  rw [toRat_neg] at h1
  exact ⟨rfl, abs_lt.mpr ⟨h1, h2⟩⟩

/-- `A x` in doubles, `A = (double)a`, `1 ≤ a ≤ 2 ^ 26`, at a finite `x` with `|x| > 1`, finite:
of the sign of `x` and at least `|x| / 2` in absolute value, so that its product with `x` is at
least `x² / 2`. -/
theorem mul_self_div_two_le_mul {a : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) {x : Double}
    (hx : x.isFinite = true) (hX1 : 1 < |x.toRat|) (hqf : (ofInt a * x).isFinite = true) :
    x.toRat * x.toRat / 2 ≤ (ofInt a * x).toRat * x.toRat := by
  obtain ⟨hA, hA'⟩ := isFinite_ofInt_and_toRat (n := a) (by rw [abs_of_pos (by lia)]; lia)
  have hq := isRounding_mul hA hx
  rw [hA'] at hq
  have ha1 : (1 : ℚ) ≤ a := mod_cast ha
  have hqa := hq.abs_sub_le hqf
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℚ) < a)] at hqa
  have hqb : |x.toRat| / 2 ≤ |(ofInt a * x).toRat| := by
    have := abs_sub_abs_le_abs_sub (a * x.toRat) (ofInt a * x).toRat
    rw [abs_sub_comm, abs_mul, abs_of_pos (by linarith : (0 : ℚ) < a)] at this
    linarith [le_mul_of_one_le_left (abs_nonneg x.toRat) ha1, two_zpow_neg_1075_le]
  have hX0 : x.toRat ≠ 0 := fun h ↦ by rw [h, abs_zero] at hX1; linarith
  have hq0 : (ofInt a * x).toRat ≠ 0 := fun h ↦ by rw [h, abs_zero] at hqb; linarith
  have hs : (ofInt a * x).signBit = x.signBit := by
    rw [signBit_mul_of_isFinite hA hx, signBit_ofInt_of_nonneg (by lia)]; simp
  rw [← abs_of_pos (mul_toRat_pos_of_signBit_eq hq0 hX0 hs), abs_mul, ← abs_mul_abs_self x.toRat]
  nlinarith [abs_nonneg x.toRat]

/-- The product `A x x` of `row_region` in doubles, `A = (double)a`, `1 ≤ a ≤ 2 ^ 26`, at a finite
`x` of absolute value above `2 ^ 480`: an infinity with the sign bit clear, or finite and at least
`x² / 4`. -/
theorem isInf_or_le_mul_mul {a : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) {x : Double}
    (hx : x.isFinite = true) (hX : 2 ^ 480 < |x.toRat|) :
    ((ofInt a * x * x).isInf = true ∧ (ofInt a * x * x).signBit = false) ∨
      ((ofInt a * x * x).isFinite = true ∧ x.toRat * x.toRat / 4 ≤ (ofInt a * x * x).toRat) := by
  obtain ⟨hA, -⟩ := isFinite_ofInt_and_toRat (n := a) (by rw [abs_of_pos (by lia)]; lia)
  have hX1 : (1 : ℚ) < |x.toRat| := (one_lt_pow₀ one_lt_two (by norm_num)).trans hX
  clear hX
  have hX0 : x.toRat ≠ 0 := fun h ↦ by rw [h, abs_zero] at hX1; linarith
  have hqs : (ofInt a * x).signBit = x.signBit := by
    rw [signBit_mul_of_isFinite hA hx, signBit_ofInt_of_nonneg (by lia)]; simp
  cases hqf : (ofInt a * x).isFinite
  · rw [mul_of_isInf (isInf_of_isFinite_eq_false (isRounding_mul hA hx).isNaN_eq_false hqf) hx hX0,
      hqs, bne_self_eq_false]
    exact .inl ⟨by decide, by decide⟩
  have hqX := mul_self_div_two_le_mul ha ha' hx hX1 hqf
  have hp := isRounding_mul hqf hx
  cases hpf : (ofInt a * x * x).isFinite
  · refine .inl ⟨isInf_of_isFinite_eq_false hp.isNaN_eq_false hpf, ?_⟩
    rw [signBit_mul_of_isFinite hqf hx, hqs, bne_self_eq_false]
  · refine .inr ⟨rfl, ?_⟩
    have := hp.abs_sub_le hpf
    have h1 : 1 < x.toRat * x.toRat := by rw [← abs_mul_abs_self]; nlinarith
    rw [abs_of_pos (show 0 < (ofInt a * x).toRat * x.toRat by linarith), abs_le] at this
    linarith [two_zpow_neg_1075_le]

/-- A double at least `x² / 4` bounds `x` by `2 ^ 514`. -/
theorem abs_lt_of_mul_self_div_four_le {X : ℚ} {y : Double} (h : X * X / 4 ≤ y.toRat) :
    |X| < 2 ^ 514 := by
  by_contra! h'
  have h1 : (2 : ℚ) ^ 514 * 2 ^ 514 = 2 ^ 1025 * 8 := by
    rw [← pow_add, show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_add]
  have h2 := mul_self_le_mul_self (by positivity) h'
  have hN : (0 : ℚ) < 2 ^ 1025 := by positivity
  have hlt := abs_toRat_lt y
  rw [abs_mul_abs_self] at h2
  generalize (2 : ℚ) ^ 514 = P at *; generalize (2 : ℚ) ^ 1025 = N at *
  linarith [le_abs_self y.toRat]

/-- `b x - a x²` in rationals with a bound `|p₁| ≤ 2 |b x| + 1` and `p₂ ≥ x² / 4`, for
`|b| ≤ 2 ^ 26` and `|x| > 2 ^ 480`: `p₁ - p₂ ≤ -2 ^ 901`. -/
theorem sub_le_neg_two_pow_of_lt {b X p₁ p₂ : ℚ} (hb : |b| ≤ 2 ^ 26) (hX : 2 ^ 480 < |X|)
    (hp₁ : |p₁| ≤ 2 * |b * X| + 1) (hp₂ : X * X / 4 ≤ p₂) : p₁ - p₂ ≤ -2 ^ 901 := by
  have hX0 := abs_nonneg X
  have h1 : (2 : ℚ) ^ 31 ≤ 2 ^ 480 := pow_le_pow_right₀ one_le_two (by norm_num)
  have h2 : (2 : ℚ) ^ 901 * 8 ≤ 2 ^ 480 * 2 ^ 480 := by
    simp only [show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_add]
    exact pow_le_pow_right₀ one_le_two (by norm_num)
  have h3 := mul_le_mul_of_nonneg_right hX.le hX0
  have h4 := mul_self_le_mul_self (by positivity) hX.le
  have hbX : |b * X| ≤ 2 ^ 26 * |X| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb hX0
  rw [abs_mul_abs_self] at h3 h4
  generalize (2 : ℚ) ^ 480 = P at *; generalize (2 : ℚ) ^ 901 = N at *
  nlinarith [le_abs_self p₁]

/-- `B x - A x x` of `row_region` in doubles, `A = (double)a` and `B = (double)b` with
`1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`, at a finite `x` of absolute value above `2 ^ 480`: a NaN or
at most `-2 ^ 900`, as `a x²` dwarfs `b x`. -/
theorem isNaN_or_doubleValue_value_le {a b : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26)
    (hb : |b| ≤ 2 ^ 26) {x : Double} (hx : x.isFinite = true) (hX : 2 ^ 480 < |x.toRat|) :
    (ofInt b * x - ofInt a * x * x).isNaN = true ∨
      doubleValue (ofInt b * x - ofInt a * x * x).bits ≤ ((-2 ^ 900 : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by lia)
  have hp₁ := isRounding_mul hB hx
  rw [hB'] at hp₁
  rcases isInf_or_le_mul_mul ha ha' hx hX with ⟨hpi, hps⟩ | ⟨hpf, hpv⟩
  · exact (isNaN_or_doubleValue_sub_of_isInf hp₁.isNaN_eq_false hpi hps).imp_right
      fun h ↦ by rw [h]; exact bot_le
  have hb' : |(b : ℚ)| ≤ 2 ^ 26 := mod_cast hb
  have h514 := abs_lt_of_mul_self_div_four_le hpv
  have hbX : |(b : ℚ) * x.toRat| ≤ 2 ^ 26 * 2 ^ 514 := by
    rw [abs_mul]; exact mul_le_mul hb' h514.le (abs_nonneg _) (by positivity)
  have hp₁f := hp₁.isFinite_of_abs_le_mul (hbX.trans (by
    simp only [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)))
  have hv := sub_le_neg_two_pow_of_lt hb' hX (hp₁.abs_toRat_le hp₁f) hpv
  rw [sub_eq_add_neg (isNaN_eq_false_of_isFinite hp₁f) (isNaN_eq_false_of_isFinite hpf)]
  refine .inr ((doubleValue_add_le_of_le hp₁f ((isFinite_neg _).trans hpf) (K := 2 ^ 901)
    (one_le_pow₀ one_le_two) (by rw [toRat_neg, ← _root_.sub_eq_add_neg]; exact hv)).2.trans
      (le_of_eq ?_))
  rw [pow_succ, neg_div, mul_div_cancel_right₀ _ two_ne_zero]

end Double

/-- The first word `wl` that `row_region` takes out of the row for a lower end `xl` of an
excluded interval, no NaN and below `ROW_BEYOND`: at or below the third coordinate `c` of a word
from `wl` on lies an end at or below `-ROW_BEYOND`, or a finite one below `c - 1`. -/
theorem le_or_lt_of_rowRegionEnds_fst_le {sd : SiftData} {xl xh : Double} {c : ℤ}
    (hxl : xl.isNaN = false) (h1 : ¬rowBeyond ≤ xl)
    (h2 : (rowRegionEnds sd xl xh).1 ≤ c >>> longShift) :
    xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c) := by
  by_cases hle : xl ≤ -rowBeyond
  · exact .inl hle
  refine .inr ?_
  obtain ⟨hf, hb⟩ := Double.isFinite_and_abs_lt_of_not_le hxl hle h1
  have ht := Double.abs_toInt_toInt64_sub_lt hf (hb.trans toRat_rowBeyond_lt)
  simp only [rowRegionEnds, hle, ↓reduceIte, longMask, longShift, Int.shiftRight_eq_div_pow,
    Nat.cast_ofNat] at h2
  have h3 : xl.toInt64.toInt + 2 ≤ c := by lia
  have h3' : (xl.toInt64.toInt : ℚ) + 2 ≤ c := mod_cast h3
  rw [abs_lt] at ht
  exact ⟨hf, by linarith⟩

theorem rowRegionEnds_snd_of_isNaN {sd : SiftData} {xl xh : Double} (h : xh.isNaN = true) :
    (rowRegionEnds sd xl xh).2 = (Int64.minValue.toInt - 2 + 1) >>> longShift := by
  have hle : ¬rowBeyond ≤ xh := by simp [LE.le, Double.le, h]
  have hnf : xh.isFinite = false := by
    cases hf : xh.isFinite
    · rfl
    · rw [Double.isNaN_eq_false_of_isFinite hf] at h; contradiction
  simp only [rowRegionEnds, hle, ↓reduceIte, Double.toInt64, hnf, Bool.false_eq_true]

/-- The end `wh` of the words that `row_region` takes out of the row for an upper end `xh` of an
excluded interval above `-ROW_BEYOND`: a third coordinate `c ≥ -2 ^ 62` of a word below `wh` lies
below an end that is no NaN, at or above `ROW_BEYOND` or finite and above `c + 1`. -/
theorem le_or_lt_of_lt_rowRegionEnds_snd {sd : SiftData} {xl xh : Double} {c : ℤ}
    (hc : -2 ^ 62 ≤ c) (h1 : ¬xh ≤ -rowBeyond) (h2 : c >>> longShift < (rowRegionEnds sd xl xh).2) :
    xh.isNaN = false ∧ (rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1)) := by
  cases hxh : xh.isNaN
  · refine ⟨rfl, ?_⟩
    by_cases hle : rowBeyond ≤ xh
    · exact .inl hle
    refine .inr ?_
    obtain ⟨hf, hb⟩ := Double.isFinite_and_abs_lt_of_not_le hxh h1 hle
    have ht := Double.abs_toInt_toInt64_sub_lt hf (hb.trans toRat_rowBeyond_lt)
    simp only [rowRegionEnds, hle, ↓reduceIte, longShift, Int.shiftRight_eq_div_pow] at h2
    have h3 : c + 2 ≤ xh.toInt64.toInt := by lia
    have h3' : (c : ℚ) + 2 ≤ xh.toInt64.toInt := mod_cast h3
    rw [abs_lt] at ht
    exact ⟨hf, by linarith⟩
  · rw [rowRegionEnds_snd_of_isNaN hxh, Int64.toInt_minValue] at h2
    simp only [longShift, Int.shiftRight_eq_div_pow] at h2
    lia

/-- `b x - a x²` for `1 ≤ a ≤ 2 ^ 26`, `|b| ≤ 2 ^ 26` and `|x| ≤ 2 ^ 480`, and a double within
`7 / 4 + |C| / 2 ^ 40` of it, are at most `2 ^ 1000` in absolute value. -/
theorem abs_le_of_abs_sub_le {a b X e : ℚ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26)
    (hX : |X| ≤ 2 ^ 480) (hE : |e - (b * X - a * X * X)| ≤ 7 / 4 + |b * X - a * X * X| / 2 ^ 40) :
    |e| ≤ 2 ^ 1000 := by
  have hX0 := abs_nonneg X
  have h1 : |b * X| ≤ 2 ^ 26 * 2 ^ 480 := by
    rw [abs_mul]; exact mul_le_mul hb hX hX0 (by positivity)
  have h2 : |a * X * X| ≤ 2 ^ 26 * 2 ^ 480 * 2 ^ 480 := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith)]
    exact mul_le_mul (mul_le_mul ha' hX hX0 (by positivity)) hX hX0 (by positivity)
  have h3 := abs_sub (b * X) (a * X * X)
  have h4 := abs_sub_abs_le_abs_sub e (b * X - a * X * X)
  have hP : (1 : ℚ) ≤ 2 ^ 480 := one_le_pow₀ one_le_two
  have hK : (2 : ℚ) ^ 480 * 2 ^ 480 * 2 ^ 30 ≤ 2 ^ 1000 := by
    simp only [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)
  generalize (2 : ℚ) ^ 480 = P at *; generalize (2 : ℚ) ^ 1000 = K at *
  nlinarith [abs_nonneg (b * X - a * X * X)]

namespace Double

-- The lower end `xl ≥ e + 1 + …` of an excluded interval, `e` within the margin of `C`: a third
-- coordinate `c ≥ -2 ^ 26` above `xl + 1`, or above `-ROW_BEYOND + 2` when `xl ≤ -ROW_BEYOND`,
-- lies above `C`.
private theorem lt_of_marginLo {C e : ℚ} {xl : Double} {c : ℤ} (hc : -2 ^ 26 ≤ c)
    (hE : |e - C| ≤ 7 / 4 + |C| / 2 ^ 40) (hlf : xl.isFinite = true)
    (hl : e + 1 - 1 / 2 ^ 40 + |e| / 2 ^ 31 ≤ xl.toRat)
    (h : xl.isNaN = false → xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c)) :
    C < c := by
  have h1 := abs_sub_abs_le_abs_sub C e
  rw [abs_sub_comm] at h1
  have hE' := abs_le.mp hE
  rcases h (isNaN_eq_false_of_isFinite hlf) with h | ⟨-, h⟩
  · have h' := (le_iff_toRat_le hlf ((isFinite_neg _).trans isFinite_rowBeyond)).mp h
    rw [toRat_neg] at h'
    have hR := lt_toRat_rowBeyond
    have hc' : (-2 ^ 26 : ℚ) ≤ c := mod_cast hc
    simp only [maxHeight, Nat.cast_ofNat] at hR
    linarith [abs_nonneg e, abs_nonneg C]
  · linarith [abs_nonneg e, abs_nonneg C]

-- The upper end `xh ≤ e - 1 - …` of an excluded interval, `e` within the margin of `C`: a third
-- coordinate `c ≤ 2 ^ 26` below `xh - 1`, or any when `xh ≥ ROW_BEYOND`, lies below `C`.
private theorem lt_of_marginHi {C e : ℚ} {xh : Double} {c : ℤ} (hc : c ≤ 2 ^ 26)
    (hE : |e - C| ≤ 7 / 4 + |C| / 2 ^ 40) (hhf : xh.isFinite = true)
    (hh : xh.toRat ≤ e - 1 + 1 / 2 ^ 40 - |e| / 2 ^ 31)
    (h : rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1)) : (c : ℚ) < C := by
  have h1 := abs_sub_abs_le_abs_sub C e
  rw [abs_sub_comm] at h1
  have hE' := abs_le.mp hE
  rcases h with h | ⟨-, h⟩
  · have h' := (le_iff_toRat_le isFinite_rowBeyond hhf).mp h
    have hR := lt_toRat_rowBeyond
    have hc' : (c : ℚ) ≤ 2 ^ 26 := mod_cast hc
    simp only [maxHeight, Nat.cast_ofNat] at hR
    linarith [abs_nonneg e, abs_nonneg C]
  · linarith [abs_nonneg e, abs_nonneg C]

theorem doubleValue_neg_rowBeyond :
    doubleValue rowBeyond.neg.bits = ((-rowBeyond.toRat : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat ((isFinite_neg _).trans isFinite_rowBeyond), toRat_neg]

/-- A double that is no NaN and at most `-2 ^ 63` is at most `-ROW_BEYOND`. -/
theorem le_neg_rowBeyond {x : Double} (hx : x.isNaN = false)
    (h : doubleValue x.bits ≤ ((-2 ^ 63 : ℚ) : WithBotTop ℚ)) : x ≤ -rowBeyond := by
  change x.le rowBeyond.neg = true
  rw [le_eq_true_iff hx (isNaN_eq_false_of_isFinite ((isFinite_neg _).trans isFinite_rowBeyond)),
    doubleValue_neg_rowBeyond]
  exact h.trans (WithBotTop.coe_le_coe.mpr (by linarith [toRat_rowBeyond_lt]))

/-- A double that is no NaN and at least `2 ^ 63` is at least `ROW_BEYOND`. -/
theorem rowBeyond_le {x : Double} (hx : x.isNaN = false)
    (h : ((2 ^ 63 : ℚ) : WithBotTop ℚ) ≤ doubleValue x.bits) : rowBeyond ≤ x := by
  change rowBeyond.le x = true
  rw [le_eq_true_iff (isNaN_eq_false_of_isFinite isFinite_rowBeyond) hx,
    doubleValue_eq_toRat isFinite_rowBeyond]
  exact (WithBotTop.coe_le_coe.mpr (by linarith [toRat_rowBeyond_lt])).trans h

/-- The lower end `B x - A x x` of an excluded interval of `row_region` at a finite `x`, `|x| ≤
2 ^ 480`, raised by its margin to `xl`, for `1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`: a third coordinate
`c ≥ -2 ^ 26` above `xl + 1`, or above `-ROW_BEYOND + 2` when `xl ≤ -ROW_BEYOND`, lies above
`b x - a x²`. -/
theorem value_lt_of_marginLo_of_abs_le {a b c : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26)
    (hb : |b| ≤ 2 ^ 26) (hc : -2 ^ 26 ≤ c) {x e xl : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 480) (he : e = ofInt b * x - ofInt a * x * x)
    (hxl : xl = if -huge < e then e + (1.0e-9 * (e.fabs + 1.0) + 1.0) else e)
    (h : xl.isNaN = false → xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c)) :
    (b : ℚ) * x.toRat - a * x.toRat * x.toRat < c := by
  obtain ⟨hef, hE⟩ := isFinite_value_and_abs_sub_le ha ha' hb hx hX
  rw [← he] at hef hE
  obtain ⟨hlf, hl⟩ := isFinite_marginLo_and_le hef
    (abs_le_of_abs_sub_le (mod_cast ha) (mod_cast ha') (mod_cast hb) hX hE)
  rw [← hxl] at hlf hl
  exact lt_of_marginLo hc hE hlf hl h

/-- `b x - a x²` lies below every `c ≥ -2 ^ 26` for `1 ≤ a`, `|b| ≤ 2 ^ 26` and `|x| > 2 ^ 480`. -/
theorem sub_lt_of_lt_abs {a b c X : ℚ} (ha : 1 ≤ a) (hb : |b| ≤ 2 ^ 26) (hc : -2 ^ 26 ≤ c)
    (hX : 2 ^ 480 < |X|) : b * X - a * X * X < c := by
  have hX0 := abs_nonneg X
  have h1 : |b * X| ≤ 2 ^ 26 * |X| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb hX0
  have h2 : |X| * |X| ≤ a * X * X := by
    rw [abs_mul_abs_self, mul_assoc]; exact le_mul_of_one_le_left (mul_self_nonneg _) ha
  have h3 : (2 : ℚ) ^ 28 ≤ 2 ^ 480 := pow_le_pow_right₀ one_le_two (by norm_num)
  generalize (2 : ℚ) ^ 480 = P at *
  nlinarith [le_abs_self (b * X)]

/-- The lower end `B x - A x x` of an excluded interval of `row_region` at a finite `x`, raised
by its margin to `xl`, for `1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`: a third coordinate
`c ≥ -2 ^ 26` above `xl + 1`, or above `-ROW_BEYOND + 2` when `xl ≤ -ROW_BEYOND`, lies above
`b x - a x²` (`JPoints.Double.value_lt_of_marginLo_of_abs_le`), and every one does far out
(`JPoints.Double.sub_lt_of_lt_abs`), whatever the NaN of the end there. -/
theorem value_lt_of_marginLo {a b c : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26)
    (hc : -2 ^ 26 ≤ c) {x e xl : Double} (hx : x.isFinite = true)
    (he : e = ofInt b * x - ofInt a * x * x)
    (hxl : xl = if -huge < e then e + (1.0e-9 * (e.fabs + 1.0) + 1.0) else e)
    (h : xl.isNaN = false → xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c)) :
    (b : ℚ) * x.toRat - a * x.toRat * x.toRat < c := by
  rcases le_or_gt |x.toRat| (2 ^ 480) with hX | hX
  · exact value_lt_of_marginLo_of_abs_le ha ha' hb hc hx hX he hxl h
  · exact sub_lt_of_lt_abs (mod_cast ha) (mod_cast hb) (mod_cast hc) hX

/-- The upper end `B x - A x x` of an excluded interval of `row_region` at a finite `x`, `|x| ≤
2 ^ 480`, lowered by its margin to `xh`, for `1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`: a third
coordinate `c ≤ 2 ^ 26` below `xh - 1`, or any when `xh ≥ ROW_BEYOND`, lies below `b x - a x²`. -/
theorem lt_value_of_marginHi_of_abs_le {a b c : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26)
    (hb : |b| ≤ 2 ^ 26) (hc : c ≤ 2 ^ 26) {x e xh : Double} (hx : x.isFinite = true)
    (hX : |x.toRat| ≤ 2 ^ 480) (he : e = ofInt b * x - ofInt a * x * x)
    (hxh : xh = if e < huge then e - (1.0e-9 * (e.fabs + 1.0) + 1.0) else e)
    (h : rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1)) :
    (c : ℚ) < b * x.toRat - a * x.toRat * x.toRat := by
  obtain ⟨hef, hE⟩ := isFinite_value_and_abs_sub_le ha ha' hb hx hX
  rw [← he] at hef hE
  obtain ⟨hhf, hh⟩ := isFinite_marginHi_and_le hef
    (abs_le_of_abs_sub_le (mod_cast ha) (mod_cast ha') (mod_cast hb) hX hE)
  rw [← hxh] at hhf hh
  exact lt_of_marginHi hc hE hhf hh h

/-- The upper end `B x - A x x` of an excluded interval of `row_region` at a finite `x` far out,
`|x| > 2 ^ 480`, lowered by its margin to `xh`, for `1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`: no NaN
end lies below `-ROW_BEYOND` (`JPoints.Double.isNaN_or_doubleValue_value_le`). -/
theorem marginHi_le_neg_rowBeyond {a b : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26)
    {x e xh : Double} (hx : x.isFinite = true) (hX : 2 ^ 480 < |x.toRat|)
    (he : e = ofInt b * x - ofInt a * x * x)
    (hxh : xh = if e < huge then e - (1.0e-9 * (e.fabs + 1.0) + 1.0) else e)
    (hn : xh.isNaN = false) : xh ≤ -rowBeyond := by
  have hNaN : e.isNaN = false := by
    cases h : e.isNaN
    · rfl
    · rw [hxh, marginHi_of_isNaN h] at hn; exact absurd hn (by simp [h])
  rcases isNaN_or_doubleValue_value_le ha ha' hb hx hX with h | hv
  · rw [← he, hNaN] at h; exact absurd h (by simp)
  rw [← he] at hv
  obtain ⟨-, hm⟩ := isNaN_eq_false_and_marginHi_le hNaN (one_le_pow₀ one_le_two) hv
  rw [← hxh] at hm
  refine le_neg_rowBeyond hn (hm.trans (WithBotTop.coe_le_coe.mpr ?_))
  have h63 : (2 : ℚ) ^ 63 * 2 ≤ 2 ^ 900 := by
    rw [← pow_succ]; exact pow_le_pow_right₀ one_le_two (by norm_num)
  generalize (2 : ℚ) ^ 900 = N at *
  linarith

/-- The upper end `B x - A x x` of an excluded interval of `row_region` at a finite `x`, lowered
by its margin to `xh`, for `1 ≤ a ≤ 2 ^ 26` and `|b| ≤ 2 ^ 26`: when `xh` is no NaN and above
`-ROW_BEYOND`, a third coordinate `c ≤ 2 ^ 26` below `xh - 1`, or any when `xh ≥ ROW_BEYOND`,
lies below `b x - a x²` (`JPoints.Double.lt_value_of_marginHi_of_abs_le`); far out, where `a x²`
dwarfs `b x`, no such `xh` arises (`JPoints.Double.marginHi_le_neg_rowBeyond`). -/
theorem lt_value_of_marginHi {a b c : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26)
    (hc : c ≤ 2 ^ 26) {x e xh : Double} (hx : x.isFinite = true)
    (he : e = ofInt b * x - ofInt a * x * x)
    (hxh : xh = if e < huge then e - (1.0e-9 * (e.fabs + 1.0) + 1.0) else e)
    (h : xh.isNaN = false ∧ ¬xh ≤ -rowBeyond ∧
      (rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1))) :
    (c : ℚ) < b * x.toRat - a * x.toRat * x.toRat := by
  rcases le_or_gt |x.toRat| (2 ^ 480) with hX | hX
  · exact lt_value_of_marginHi_of_abs_le ha ha' hb hc hx hX he hxh h.2.2
  · exact absurd (marginHi_le_neg_rowBeyond ha ha' hb hx hX he hxh h.1) h.2.1

/-! ### The ends of `row_region` for `a = 0` -/

/-- `B x` in doubles for `B = (double)b`, `1 ≤ b ≤ 2 ^ 26`, at a finite `x` of absolute value at
most `2 ^ 900`: finite, within `7 / 4 + |b x| / 2 ^ 40` of `b x`, and at most `2 ^ 1000` in
absolute value. -/
theorem isFinite_mul_and_abs_sub_le {b : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) {x : Double}
    (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 900) :
    (ofInt b * x).isFinite = true ∧
      |(ofInt b * x).toRat - b * x.toRat| ≤ 7 / 4 + |b * x.toRat| / 2 ^ 40 ∧
      |(ofInt b * x).toRat| ≤ 2 ^ 1000 := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by rw [abs_of_pos (by lia)]; lia)
  have h := isRounding_mul hB hx
  rw [hB'] at h
  have hb1 : (0 : ℚ) < b := mod_cast (show (0 : ℤ) < b by lia)
  have hbX : |(b : ℚ) * x.toRat| ≤ 2 ^ 26 * 2 ^ 900 := by
    rw [abs_mul, abs_of_pos hb1]
    exact mul_le_mul (mod_cast hb') hX (abs_nonneg _) (by positivity)
  have hK : (2 : ℚ) ^ 26 * 2 ^ 900 * 4 ≤ 2 ^ 1000 := by
    simp only [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]
    exact pow_le_pow_right₀ one_le_two (by norm_num)
  have hf := h.isFinite_of_abs_le_mul (by
    have : (2 : ℚ) ^ 1000 ≤ 2 ^ 1000 * 2 ^ 21 := le_mul_of_one_le_right (by positivity)
      (one_le_pow₀ one_le_two)
    generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 1000 = K at *; linarith)
  have he := h.abs_sub_le hf
  have hb := h.abs_toRat_le hf
  refine ⟨hf, he.trans (by linarith [two_zpow_neg_1075_le_inv, abs_nonneg ((b : ℚ) * x.toRat)]), ?_⟩
  have h1 : (1 : ℚ) ≤ 2 ^ 900 := one_le_pow₀ one_le_two
  generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 1000 = K at *; linarith

/-- `B x` in doubles for `B = (double)b`, `1 ≤ b ≤ 2 ^ 26`, at a finite `x` above `2 ^ 900`: at
least `2 ^ 899`, `+∞` included. -/
theorem le_doubleValue_mul {b : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) {x : Double}
    (hx : x.isFinite = true) (hX : 2 ^ 900 < x.toRat) :
    ((2 ^ 899 : ℚ) : WithBotTop ℚ) ≤ doubleValue (ofInt b * x).bits := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by rw [abs_of_pos (by lia)]; lia)
  have h := isRounding_mul hB hx
  rw [hB'] at h
  have hb1 : (1 : ℚ) ≤ b := mod_cast hb
  have h1 : (1 : ℚ) ≤ 2 ^ 899 := one_le_pow₀ one_le_two
  have h2 : (2 : ℚ) ^ 900 = 2 * 2 ^ 899 := by rw [pow_succ, mul_comm]
  have hv : 2 ^ 900 < (b : ℚ) * x.toRat := hX.trans_le (le_mul_of_one_le_left (by
    generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 899 = Q at *; linarith) hb1)
  cases hf : (ofInt b * x).isFinite
  · rw [doubleValue_of_isFinite_eq_false h.isNaN_eq_false hf, signBit_mul_of_isFinite hB hx,
      signBit_ofInt_of_nonneg (by lia), signBit_eq_false_of_pos ((pow_pos two_pos 900).trans hX)]
    exact le_top
  · rw [doubleValue_eq_toRat hf, WithBotTop.coe_le_coe]
    have he := h.half_le_toRat hf (by
      clear hX; generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 899 = Q at *; linarith)
    clear hX
    generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 899 = Q at *
    linarith

/-- `B x` in doubles for `B = (double)b`, `1 ≤ b ≤ 2 ^ 26`, at a finite `x` below `-2 ^ 900`: at
most `-2 ^ 899`, `-∞` included. -/
theorem doubleValue_mul_le {b : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) {x : Double}
    (hx : x.isFinite = true) (hX : x.toRat < -2 ^ 900) :
    doubleValue (ofInt b * x).bits ≤ ((-2 ^ 899 : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by rw [abs_of_pos (by lia)]; lia)
  have h := isRounding_mul hB hx
  rw [hB'] at h
  have hb1 : (1 : ℚ) ≤ b := mod_cast hb
  have h1 : (1 : ℚ) ≤ 2 ^ 899 := one_le_pow₀ one_le_two
  have h2 : (2 : ℚ) ^ 900 = 2 * 2 ^ 899 := by rw [pow_succ, mul_comm]
  have hX0 : x.toRat < 0 := hX.trans (neg_neg_of_pos (pow_pos two_pos 900))
  have hv : (b : ℚ) * x.toRat < -2 ^ 900 :=
    (mul_le_of_one_le_left hX0.le hb1).trans_lt hX
  cases hf : (ofInt b * x).isFinite
  · rw [doubleValue_of_isFinite_eq_false h.isNaN_eq_false hf, signBit_mul_of_isFinite hB hx,
      signBit_ofInt_of_nonneg (by lia), (toRat_neg_iff hX0.ne).mp hX0]
    exact bot_le
  · rw [doubleValue_eq_toRat hf, WithBotTop.coe_le_coe]
    have he := h.abs_sub_le hf
    have hv0 : (b : ℚ) * x.toRat < 0 := hv.trans (neg_neg_of_pos (pow_pos two_pos 900))
    rw [abs_of_neg hv0, abs_le] at he
    clear hX
    generalize (2 : ℚ) ^ 900 = P at *; generalize (2 : ℚ) ^ 899 = Q at *
    linarith [two_zpow_neg_1075_le]

/-- A double that is no NaN and at least `2 ^ 64`, `+∞` included, stays at or above `ROW_BEYOND`
when `row_region` raises it by its margin. -/
theorem rowBeyond_le_marginLo {e : Double} (he : e.isNaN = false)
    (h : ((2 ^ 64 : ℚ) : WithBotTop ℚ) ≤ doubleValue e.bits) :
    rowBeyond ≤ if -huge < e then e + (1.0e-9 * (e.fabs + 1.0) + 1.0) else e := by
  obtain ⟨hn, hm⟩ := isNaN_eq_false_and_le_marginLo he (one_le_pow₀ one_le_two) h
  exact rowBeyond_le hn (le_of_eq_of_le (by norm_num) hm)

/-- A double that is no NaN and at most `-2 ^ 64`, `-∞` included, stays at or below `-ROW_BEYOND`
when `row_region` lowers it by its margin. -/
theorem marginHi_le_neg_rowBeyond_of_le {e : Double} (he : e.isNaN = false)
    (h : doubleValue e.bits ≤ ((-2 ^ 64 : ℚ) : WithBotTop ℚ)) :
    (if e < huge then e - (1.0e-9 * (e.fabs + 1.0) + 1.0) else e) ≤ -rowBeyond := by
  obtain ⟨hn, hm⟩ := isNaN_eq_false_and_marginHi_le he (one_le_pow₀ one_le_two) h
  exact le_neg_rowBeyond hn (hm.trans (le_of_eq (by norm_num)))

/-- `B x` for `1 ≤ b ≤ 2 ^ 26` at a finite `x`, `|x| ≤ 2 ^ 900`, raised by its margin to `xl`: a
third coordinate `c ≥ -2 ^ 26` above `xl + 1`, or above `-ROW_BEYOND + 2` when
`xl ≤ -ROW_BEYOND`, lies above `b x`. -/
theorem mul_lt_of_marginLo_of_abs_le {b c : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26)
    (hc : -2 ^ 26 ≤ c) {x xl : Double} (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 900)
    (hxl : xl = if -huge < ofInt b * x then ofInt b * x + (1.0e-9 * ((ofInt b * x).fabs + 1.0) +
      1.0) else ofInt b * x)
    (h : xl.isNaN = false → xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c)) :
    (b : ℚ) * x.toRat < c := by
  obtain ⟨hef, hE, hE'⟩ := isFinite_mul_and_abs_sub_le hb hb' hx hX
  obtain ⟨hlf, hl⟩ := isFinite_marginLo_and_le hef hE'
  rw [← hxl] at hlf hl
  exact lt_of_marginLo hc hE hlf hl h

/-- `B x` for `1 ≤ b ≤ 2 ^ 26` at a finite `x`, `|x| ≤ 2 ^ 900`, lowered by its margin to `xh`: a
third coordinate `c ≤ 2 ^ 26` below `xh - 1`, or any when `xh ≥ ROW_BEYOND`, lies below `b x`. -/
theorem lt_mul_of_marginHi_of_abs_le {b c : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) (hc : c ≤ 2 ^ 26)
    {x xh : Double} (hx : x.isFinite = true) (hX : |x.toRat| ≤ 2 ^ 900)
    (hxh : xh = if ofInt b * x < huge then ofInt b * x - (1.0e-9 * ((ofInt b * x).fabs + 1.0) +
      1.0) else ofInt b * x)
    (h : rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1)) :
    (c : ℚ) < b * x.toRat := by
  obtain ⟨hef, hE, hE'⟩ := isFinite_mul_and_abs_sub_le hb hb' hx hX
  obtain ⟨hhf, hh⟩ := isFinite_marginHi_and_le hef hE'
  rw [← hxh] at hhf hh
  exact lt_of_marginHi hc hE hhf hh h

/-- A power `2 ^ 899` dwarfs `2 ^ 64`, as a bound in the values of the doubles. -/
theorem two_pow_sixtyFour_le : ((2 ^ 64 : ℚ) : WithBotTop ℚ) ≤ ((2 ^ 899 : ℚ) : WithBotTop ℚ) :=
  WithBotTop.coe_le_coe.mpr (pow_le_pow_right₀ one_le_two (by norm_num))

/-- A power `-2 ^ 899` lies far below `-2 ^ 64`, as a bound in the values of the doubles. -/
theorem neg_two_pow_le_neg_two_pow_sixtyFour :
    ((-2 ^ 899 : ℚ) : WithBotTop ℚ) ≤ ((-2 ^ 64 : ℚ) : WithBotTop ℚ) :=
  WithBotTop.coe_le_coe.mpr (neg_le_neg (pow_le_pow_right₀ one_le_two (by norm_num)))

/-- `b x < c` for `b ≥ 1`, `c ≥ -2 ^ 26` and `x < -2 ^ 900`. -/
theorem mul_lt_of_lt_neg_two_pow {b c X : ℚ} (hb : 1 ≤ b) (hc : -2 ^ 26 ≤ c)
    (hX : X < -2 ^ 900) : b * X < c := by
  have h26 : (2 : ℚ) ^ 26 * 2 ^ 26 ≤ 2 ^ 900 := by
    rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)
  have := mul_le_mul_of_nonneg_left hX.le (by linarith : (0 : ℚ) ≤ b)
  generalize (2 : ℚ) ^ 900 = P at *
  nlinarith

/-- `c < b x` for `b ≥ 1`, `c ≤ 2 ^ 26` and `x > 2 ^ 900`. -/
theorem lt_mul_of_two_pow_lt {b c X : ℚ} (hb : 1 ≤ b) (hc : c ≤ 2 ^ 26) (hX : 2 ^ 900 < X) :
    c < b * X := by
  have h26 : (2 : ℚ) ^ 26 ≤ 2 ^ 900 := pow_le_pow_right₀ one_le_two (by norm_num)
  have := le_mul_of_one_le_left (hX.le.trans' (pow_nonneg zero_le_two _)) hb
  generalize (2 : ℚ) ^ 900 = P at *; linarith

/-- The lower end `B nl` of an excluded interval of `row_region` for `a = 0`, raised by its margin
to `xl`, `1 ≤ b ≤ 2 ^ 26`: when `xl` is below `ROW_BEYOND`, a third coordinate `c ≥ -2 ^ 26`
above `xl + 1`, or any when `xl ≤ -ROW_BEYOND`, gives `nl < c / b`
(`JPoints.Double.mul_lt_of_marginLo_of_abs_le`); far out and at `+∞`, `xl` is at least
`ROW_BEYOND` (`JPoints.Double.rowBeyond_le_marginLo`). -/
theorem lt_div_of_marginLo {b c : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) (hc : -2 ^ 26 ≤ c)
    {nl lo xl : Double} (hnl : nl.isNaN = false)
    (hlo : lo = if nl.beq (-huge) then -huge else ofInt b * nl)
    (hxl : xl = if -huge < lo then lo + (1.0e-9 * (lo.fabs + 1.0) + 1.0) else lo)
    (h1 : ¬rowBeyond ≤ xl)
    (h : xl.isNaN = false → xl ≤ -rowBeyond ∨ (xl.isFinite = true ∧ xl.toRat + 1 < c)) :
    doubleValue nl.bits < ((c / b : ℚ) : WithBotTop ℚ) := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by rw [abs_of_pos (by lia)]; lia)
  have hb0 : (0 : ℚ) < b := mod_cast (show (0 : ℤ) < b by lia)
  by_cases hbeq : nl.beq (-huge) = true
  · exact doubleValue_lt_coe_of_beq_neg_huge hnl hbeq _
  rw [ite_eq_right hbeq] at hlo
  subst hlo hxl
  cases hf : nl.isFinite
  · rw [mul_of_isInf_right hB (by rw [hB']; exact hb0.ne') (isInf_of_isFinite_eq_false hnl hf),
      signBit_ofInt_of_nonneg (by lia),
      signBit_eq_false_of_beq_neg_huge hnl hf (by simpa using hbeq)] at h1
    exact absurd (rowBeyond_le_marginLo isNaN_huge (by rw [doubleValue_huge]; exact le_top)) h1
  rw [doubleValue_eq_toRat hf, WithBotTop.coe_lt_coe, lt_div_iff₀ hb0, mul_comm]
  rcases le_or_gt |nl.toRat| (2 ^ 900) with hX | hX
  · exact hB' ▸ mul_lt_of_marginLo_of_abs_le hb hb' hc hf hX rfl h
  rcases lt_abs.mp hX with hp | hn
  · exact absurd (rowBeyond_le_marginLo (isRounding_mul hB hf).isNaN_eq_false
      (two_pow_sixtyFour_le.trans (le_doubleValue_mul hb hb' hf hp))) h1
  · exact mul_lt_of_lt_neg_two_pow (mod_cast hb) (mod_cast hc) (lt_neg.mp hn)

/-- The upper end `B nh` of an excluded interval of `row_region` for `a = 0`, lowered by its
margin to `xh`, `1 ≤ b ≤ 2 ^ 26`: when `xh` is no NaN and above `-ROW_BEYOND`, a third coordinate
`c ≤ 2 ^ 26` below `xh - 1`, or any when `xh ≥ ROW_BEYOND`, gives `c / b < nh`
(`JPoints.Double.lt_mul_of_marginHi_of_abs_le`); far out and at `-∞`, `xh` is at most
`-ROW_BEYOND` (`JPoints.Double.marginHi_le_neg_rowBeyond_of_le`). -/
theorem div_lt_of_marginHi {b c : ℤ} (hb : 1 ≤ b) (hb' : b ≤ 2 ^ 26) (hc : c ≤ 2 ^ 26)
    {nh hi xh : Double} (hnh : nh.isNaN = false)
    (hhi : hi = if nh.beq huge then huge else ofInt b * nh)
    (hxh : xh = if hi < huge then hi - (1.0e-9 * (hi.fabs + 1.0) + 1.0) else hi)
    (h : xh.isNaN = false ∧ ¬xh ≤ -rowBeyond ∧
      (rowBeyond ≤ xh ∨ (xh.isFinite = true ∧ c < xh.toRat - 1))) :
    ((c / b : ℚ) : WithBotTop ℚ) < doubleValue nh.bits := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by rw [abs_of_pos (by lia)]; lia)
  have hb0 : (0 : ℚ) < b := mod_cast (show (0 : ℤ) < b by lia)
  by_cases hbeq : nh.beq huge = true
  · exact coe_lt_doubleValue_of_beq_huge hnh hbeq _
  rw [ite_eq_right hbeq] at hhi
  subst hhi hxh
  cases hf : nh.isFinite
  · rw [mul_of_isInf_right hB (by rw [hB']; exact hb0.ne') (isInf_of_isFinite_eq_false hnh hf),
      signBit_ofInt_of_nonneg (by lia),
      signBit_eq_true_of_beq_huge hnh hf (by simpa using hbeq)] at h
    exact absurd (marginHi_le_neg_rowBeyond_of_le isNaN_huge_neg
      (by rw [doubleValue_huge_neg]; exact bot_le)) h.2.1
  rw [doubleValue_eq_toRat hf, WithBotTop.coe_lt_coe, div_lt_iff₀ hb0, mul_comm]
  rcases le_or_gt |nh.toRat| (2 ^ 900) with hX | hX
  · exact hB' ▸ lt_mul_of_marginHi_of_abs_le hb hb' hc hf hX rfl h.2.2
  rcases lt_abs.mp hX with hp | hn
  · exact lt_mul_of_two_pow_lt (mod_cast hb) (mod_cast hc) hp
  · exact absurd (marginHi_le_neg_rowBeyond_of_le (isRounding_mul hB hf).isNaN_eq_false
      ((doubleValue_mul_le hb hb' hf (lt_neg.mp hn)).trans neg_two_pow_le_neg_two_pow_sixtyFour))
      h.2.1

end Double

end JPoints

end
