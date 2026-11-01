/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Mathlib.Analysis.Polynomial.Order
public import JPoints.Proof.Globals
public import JPoints.Proof.Kummer
public import JPoints.Proof.Reference
public import JPoints.Proof.RowRegion

import JPoints.Mathlib.Order.WithBotTop
import JPoints.Proof.Order
import JPoints.Proof.Reduction
import JPoints.Proof.RowRegionEnds
import JPoints.Proof.Rounding
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Topology.Order.IntermediateValue

/-!
# The points of the curve in the real region

A point of the Kummer surface over the triple `(a, b, c)` that comes from a rational point of the
Jacobian gives real points of the curve: `f(x) ≥ 0` at a real root `x` of `a t² - b t + c`,
`a ≠ 0`, by the identity `a⁴ f(x) = (α x + β)²` (`JPoints.sum_nonneg_of_hasPointOver`), and
`f(c / b) ≥ 0` for `a = 0` (`JPoints.eval_poly_div_nonneg_of_hasPointOver`). On the real points
inside an interval on which `f` is negative (`JPoints.NegativeIntervals.Contains`), a squarefree
`f` is negative (`JPoints.NegativeIntervals.Sound.eval_map_neg_of_contains`). An excluded interval
of `row_region` that took out the word of the third coordinate `c` of a point, for
`1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`, would put `c` strictly between the exact values of its
ends (`JPoints.Proof.RowRegionEnds`), hence a root of `a t² - b t + c` inside the interval, by the
intermediate value theorem
(`JPoints.NegativeIntervals.Sound.exists_contains_of_regionExcludes_from`,
`JPoints.NegativeIntervals.Sound.exists_contains_of_regionExcludes_upTo`), or `c / b` inside it
for `a = 0`; so it takes out no such word
(`JPoints.NegativeIntervals.Sound.not_regionExcludes_of_hasPointOver`).

## Main definitions

* `JPoints.NegativeIntervals.Contains`: a real point inside an interval of `neg`.

## Main statements

* `JPoints.sum_nonneg_of_hasPointOver`, `JPoints.eval_poly_div_nonneg_of_hasPointOver`: `f` at
  the real points over a triple.
* `JPoints.NegativeIntervals.Sound.eval_map_neg_of_contains`: `f` inside the intervals.
* `JPoints.NegativeIntervals.Sound.not_regionExcludes_of_hasPointOver`: the excluded intervals keep
  the points.
-/

@[expose] public section

open Polynomial

namespace JPoints

/-! ### The real points over a triple -/

/-- At a root `x` of `a t² - b t + c`, `a⁴ f(x) = A₂ x² + C x + B₂` for the polynomials of the
lifting test and `C` of `JPoints.auxC`, whatever `d`: the remainder of
`a⁴ f - A₂ t² - C t - B₂` modulo `a t² - b t + c` vanishes identically. -/
theorem pow_four_mul_sum_eq_of_quadratic_eq_zero {K : Type*} [CommRing K] (f : ℕ → ℤ)
    (a b c d : ℤ) {x : K} (hx : (a : K) * x ^ 2 - b * x + c = 0) :
    (a : K) ^ 4 * ∑ k ∈ Finset.range 7, (f k : K) * x ^ k =
      auxA2 f a b c d * x ^ 2 + auxC f a b c d * x + auxB2 f a b c d := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, auxA2, auxB2, auxC]
  push_cast
  linear_combination (f 6 * a ^ 3 * x ^ 4 + (f 5 * a ^ 3 + f 6 * a ^ 2 * b) * x ^ 3 +
    (f 4 * a ^ 3 + f 5 * a ^ 2 * b - f 6 * a ^ 2 * c + f 6 * a * b ^ 2) * x ^ 2 +
    (f 3 * a ^ 3 + f 4 * a ^ 2 * b - f 5 * a ^ 2 * c + f 5 * a * b ^ 2 - 2 * f 6 * a * b * c +
      f 6 * b ^ 3) * x - f 4 * a ^ 2 * c - f 5 * a * b * c - f 6 * b ^ 2 * c - a ^ 2 * d : K) * hx

/-- `f` takes a value of at least `0` at a real root `x` of `a t² - b t + c`, `a ≠ 0`, when the
point `(a, b, c, d)` of the Kummer surface comes from a rational point of the Jacobian: with the
squares `α² = A₂`, `β² = B₂` and `2 α β = C` of `JPoints.exists_sq_auxA2_auxB2`,
`a⁴ f(x) = (α x + β)²`. -/
theorem sum_nonneg_of_lifts {f : ℕ → ℤ} {a b c d : ℤ} (ha : a ≠ 0) (hK : kummer f a b c d = 0)
    (hL : Lifts f a b c d) {x : ℝ} (hx : (a : ℝ) * x ^ 2 - b * x + c = 0) :
    0 ≤ ∑ k ∈ Finset.range 7, (f k : ℝ) * x ^ k := by
  simp only [Lifts, ha, ↓reduceIte] at hL
  obtain ⟨α, β, hα, hβ, hαβ⟩ := exists_sq_auxA2_auxB2 hK hL.1 hL.2
  have h := pow_four_mul_sum_eq_of_quadratic_eq_zero f a b c d hx
  rw [← hα, ← hβ, ← hαβ] at h
  push_cast at h
  refine nonneg_of_mul_nonneg_right (h.trans (by ring : _ = ((α : ℝ) * x + β) ^ 2) ▸
    sq_nonneg _) (by positivity : (0 : ℝ) < (a : ℝ) ^ 4)

theorem sum_nonneg_of_hasPointOver {cs : List ℤ} {a b c : ℤ} (ha : a ≠ 0)
    (h : HasPointOver cs (a, b, c)) {x : ℝ} (hx : (a : ℝ) * x ^ 2 - b * x + c = 0) :
    0 ≤ ∑ k ∈ Finset.range 7, (cs.getD k 0 : ℝ) * x ^ k := by
  obtain ⟨p, hp, hL⟩ := h
  have hK := kummer_eq_zero_of_mem_kummerPoints hp
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
  refine sum_nonneg_of_lifts (mul_ne_zero (mod_cast y.den_ne_zero) ha) hK hL ?_
  push_cast
  linear_combination (y.den : ℝ) * hx

theorem sexticForm_mul_mul (f : ℕ → ℤ) (m x z : ℤ) :
    sexticForm f (m * x) (m * z) = m ^ 6 * sexticForm f x z := by
  simp only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem pow_six_mul_sum_eq_sexticForm (f : ℕ → ℤ) (x : ℚ) {z : ℤ} (hz : z ≠ 0) :
    (z : ℚ) ^ 6 * ∑ k ∈ Finset.range 7, (f k : ℚ) * (x / z) ^ k =
      ∑ k ∈ Finset.range 7, (f k : ℚ) * x ^ k * (z : ℚ) ^ (6 - k) := by
  have : (z : ℚ) ≠ 0 := mod_cast hz
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  field

/-- `f` takes a value of at least `0` at `c / b`, `b ≠ 0`, when a point lies over `(0, b, c)`:
then `F(c, b) = b⁶ f(c / b)` is a square. -/
theorem eval_poly_div_nonneg_of_hasPointOver {cs : List ℤ} (h7 : cs.length ≤ 7) {b c : ℤ}
    (hb : b ≠ 0) (h : HasPointOver cs (0, b, c)) : 0 ≤ (poly cs).eval ((c : ℚ) / b) := by
  obtain ⟨p, hp, hL⟩ := h
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
  have hm : (y.den : ℤ) ≠ 0 := mod_cast y.den_ne_zero
  simp only [Lifts, mul_zero, mul_eq_zero, hm, hb, or_self, ↓reduceIte, sexticForm_mul_mul] at hL
  obtain ⟨s, hs⟩ := hL.2
  have h6 : 0 ≤ sexticForm (cs.getD · 0) c b :=
    nonneg_of_mul_nonneg_right (hs ▸ mul_self_nonneg s) (by positivity)
  rw [eval_poly h7]
  refine nonneg_of_mul_nonneg_right ((pow_six_mul_sum_eq_sexticForm (cs.getD · 0) c hb) ▸ ?_)
    (by positivity : (0 : ℚ) < (b : ℚ) ^ 6)
  exact_mod_cast h6

theorem eval_map_poly_eq_sum {cs : List ℤ} (h7 : cs.length ≤ 7) (x : ℝ) :
    ((poly cs).map (algebraMap ℚ ℝ)).eval x =
      ∑ k ∈ Finset.range 7, (cs.getD k 0 : ℝ) * x ^ k := by
  rw [poly, Polynomial.map_sum, eval_finsetSum,
    Finset.sum_subset (Finset.range_subset_range.mpr h7)]
  · simp
  · intro i _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]
    simp

/-! ### The roots of the quadratic -/

theorem exists_eq_zero_of_neg_of_pos {a b c l h : ℝ} (hlh : l < h)
    (hl : a * l ^ 2 - b * l + c < 0) (hh : 0 < a * h ^ 2 - b * h + c) :
    ∃ x, l < x ∧ x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo hlh.le
    (by fun_prop : Continuous fun t : ℝ ↦ a * t ^ 2 - b * t + c).continuousOn ⟨hl, hh⟩
  exact ⟨x, h1, h2, h3⟩

theorem exists_eq_zero_of_pos_of_neg {a b c l h : ℝ} (hlh : l < h)
    (hl : 0 < a * l ^ 2 - b * l + c) (hh : a * h ^ 2 - b * h + c < 0) :
    ∃ x, l < x ∧ x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' hlh.le
    (by fun_prop : Continuous fun t : ℝ ↦ a * t ^ 2 - b * t + c).continuousOn ⟨hh, hl⟩
  exact ⟨x, h1, h2, h3⟩

/-- `a t² - b t + c`, `a ≥ 1`, negative at `l` has a root above `l`. -/
theorem exists_gt_eq_zero {a b c l : ℝ} (ha : 1 ≤ a) (hl : a * l ^ 2 - b * l + c < 0) :
    ∃ x, l < x ∧ a * x ^ 2 - b * x + c = 0 := by
  set T := max l 0 + |b| + |c| + 1
  have hT : l < T := by linarith [le_max_left l 0, abs_nonneg b, abs_nonneg c]
  have hT1 : |b| + |c| + 1 ≤ T := by linarith [le_max_right l 0]
  obtain ⟨x, h1, -, h3⟩ := exists_eq_zero_of_neg_of_pos hT hl (by
    nlinarith [le_abs_self b, neg_abs_le c, abs_nonneg b, abs_nonneg c])
  exact ⟨x, h1, h3⟩

/-- `a t² - b t + c`, `a ≥ 1`, negative at `h` has a root below `h`. -/
theorem exists_lt_eq_zero {a b c h : ℝ} (ha : 1 ≤ a) (hh : a * h ^ 2 - b * h + c < 0) :
    ∃ x, x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  set T := min h 0 - |b| - |c| - 1
  have hT : T < h := by linarith [min_le_left h 0, abs_nonneg b, abs_nonneg c]
  have hT1 : T ≤ -(|b| + |c| + 1) := by linarith [min_le_right h 0]
  obtain ⟨x, -, h2, h3⟩ := exists_eq_zero_of_pos_of_neg hT (by
    nlinarith [neg_abs_le b, neg_abs_le c, abs_nonneg b, abs_nonneg c]) hh
  exact ⟨x, h2, h3⟩

/-! ### The doubles of the branches -/

namespace Double

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

theorem doubleValue_le_of_not_lt {x y : Double} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : ¬x < y) : doubleValue x.bits ≥ doubleValue y.bits := by
  change ¬x.lt y = true at h
  rw [lt_eq_true_iff hx hy, not_lt] at h
  exact h

theorem doubleValue_lt_of_lt {x y : Double} (h : x < y) :
    doubleValue x.bits < doubleValue y.bits := by
  change x.lt y = true at h
  exact ((lt_eq_true_iff' ).mp h).2.2

theorem isFinite_rowRegionVertex {a b : ℤ} (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) :
    (rowRegionVertex a b).isFinite = true := by
  obtain ⟨hB, hB'⟩ := isFinite_ofInt_and_toRat (n := b) (by lia)
  have h1 := isRounding_mul isFinite_half hB
  rw [toRat_half, hB'] at h1
  have hb' : |(b : ℚ)| ≤ 2 ^ 26 := mod_cast hb
  have hf1 := h1.isFinite_of_abs_le (n := 26) (by norm_num) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2)]; linarith [abs_nonneg (b : ℚ)])
  obtain ⟨hA, hA'⟩ := isFinite_ofInt_and_toRat (n := a) (by rw [abs_of_pos (by lia)]; lia)
  have ha1 : (1 : ℚ) ≤ a := mod_cast ha
  have h2 := isRounding_div hf1 hA (by rw [hA']; positivity)
  rw [hA'] at h2
  have hq := h1.abs_toRat_le hf1
  refine h2.isFinite_of_abs_le (n := 28) (by norm_num) ?_
  rw [abs_div, abs_of_pos (by linarith : (0 : ℚ) < a)]
  refine (div_le_self (abs_nonneg _) ha1).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2)] at hq
  linarith [abs_nonneg (b : ℚ)]

/-- The start `l = max(nl, m)` of the branch of the larger root of `row_region` lies in the
interval when the branch is not empty: finite, and at or above `nl`. -/
theorem isFinite_rowRegionFrom_and_le {neg : NegativeIntervals} {a b : ℤ} {i : ℕ} (ha : 1 ≤ a)
    (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hnl : neg.shrunkLo[i]!.isNaN = false)
    (hl : rowRegionFrom neg a b i < neg.shrunkHi[i]!) :
    (rowRegionFrom neg a b i).isFinite = true ∧
      doubleValue neg.shrunkLo[i]!.bits ≤ doubleValue (rowRegionFrom neg a b i).bits := by
  have hm := isFinite_rowRegionVertex ha ha' hb
  by_cases h : rowRegionVertex a b < neg.shrunkLo[i]!
  · simp only [rowRegionFrom, h, ↓reduceIte] at hl ⊢
    exact ⟨isFinite_of_lt_of_lt hnl h hl, le_rfl⟩
  · simp only [rowRegionFrom, h, ↓reduceIte] at hl ⊢
    exact ⟨hm, doubleValue_le_of_not_lt (isNaN_eq_false_of_isFinite hm) hnl h⟩

/-- The end `h = min(nh, m)` of the branch of the smaller root of `row_region` lies in the
interval when the branch is not empty: finite, and at or below `nh`. -/
theorem isFinite_rowRegionUpTo_and_le {neg : NegativeIntervals} {a b : ℤ} {i : ℕ} (ha : 1 ≤ a)
    (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hnh : neg.shrunkHi[i]!.isNaN = false)
    (hh : neg.shrunkLo[i]! < rowRegionUpTo neg a b i) :
    (rowRegionUpTo neg a b i).isFinite = true ∧
      doubleValue (rowRegionUpTo neg a b i).bits ≤ doubleValue neg.shrunkHi[i]!.bits := by
  have hm := isFinite_rowRegionVertex ha ha' hb
  by_cases h : neg.shrunkHi[i]! < rowRegionVertex a b
  · simp only [rowRegionUpTo, h, ↓reduceIte] at hh ⊢
    exact ⟨isFinite_of_lt_of_lt hnh hh h, le_rfl⟩
  · simp only [rowRegionUpTo, h, ↓reduceIte] at hh ⊢
    exact ⟨hm, doubleValue_le_of_not_lt hnh (isNaN_eq_false_of_isFinite hm) h⟩

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

/-! ### The branches -/

/-- The real number `x` lies inside the interval `i` of `neg`: between two reals whose rational
points between them all lie strictly between the values of the shrunk ends of the interval. -/
def NegativeIntervals.Contains (neg : NegativeIntervals) (i : ℕ) (x : ℝ) : Prop :=
  ∃ L U : ℝ, L < x ∧ x < U ∧ ∀ q : ℚ, L < q → (q : ℝ) < U →
    doubleValue neg.shrunkLo[i]!.bits < q ∧ (q : WithBotTop ℚ) < doubleValue neg.shrunkHi[i]!.bits

/-- `f` is negative on the real points inside a sound interval when it is squarefree
(`Polynomial.eval_map_neg_of_forall_ratCast`). -/
theorem NegativeIntervals.Sound.eval_map_neg_of_contains {neg : NegativeIntervals} {cs : List ℤ}
    (h : neg.Sound cs) (hsq : Squarefree (poly cs)) {i : ℕ} (hi : i < neg.numNeg) {x : ℝ}
    (hx : neg.Contains i x) : ((poly cs).map (algebraMap ℚ ℝ)).eval x < 0 :=
  have ⟨_, _, hL, hU, hq⟩ := hx
  eval_map_neg_of_forall_ratCast hsq (fun q h1 h2 ↦ h.eval_neg hi (hq q h1 h2).1 (hq q h1 h2).2)
    hL hU

section Branches

variable {neg : NegativeIntervals} {cs : List ℤ} {i : ℕ} {sd : SiftData} {a b c : ℤ}

/-- The value `b x - a x²` at a finite double `x`, for `1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`,
lowered by its margin to the upper end of an excluded interval of `row_region`: a third coordinate
`c` that the interval takes out lies below the exact value (`JPoints.Double.lt_value_of_marginHi`).
-/
theorem mul_sq_sub_mul_add_neg_of_lt_rowRegionEnds_snd {x xl : Double} (ha : 1 ≤ a)
    (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hc : |c| ≤ 2 ^ 26) (hx : x.isFinite = true)
    (h2 : ¬rowRegionMarginHi (rowRegionValue a b x) ≤ -rowBeyond)
    (h4 : c >>> longShift < (rowRegionEnds sd xl (rowRegionMarginHi (rowRegionValue a b x))).2) :
    (a : ℝ) * x.toRat ^ 2 - b * x.toRat + c < 0 := by
  have hc' := abs_le.mp hc
  have hup := le_or_lt_of_lt_rowRegionEnds_snd (c := c) (by linarith) h2 h4
  have hC := Double.lt_value_of_marginHi ha ha' hb hc'.2 hx rfl rfl ⟨hup.1, h2, hup.2⟩
  have := (Rat.cast_strictMono (K := ℝ)) hC
  push_cast at this; linarith

/-- The value `b x - a x²` at a finite double `x`, for `1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`,
raised by its margin to the lower end of an excluded interval of `row_region`: a third coordinate
`c` that the interval takes out lies above the exact value (`JPoints.Double.value_lt_of_marginLo`).
-/
theorem mul_sq_sub_mul_add_pos_of_rowRegionEnds_fst_le {x xh : Double} (ha : 1 ≤ a)
    (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hc : |c| ≤ 2 ^ 26) (hx : x.isFinite = true)
    (h1 : ¬rowBeyond ≤ rowRegionMarginLo (rowRegionValue a b x))
    (h3 : (rowRegionEnds sd (rowRegionMarginLo (rowRegionValue a b x)) xh).1 ≤ c >>> longShift) :
    0 < (a : ℝ) * x.toRat ^ 2 - b * x.toRat + c := by
  have hC := Double.value_lt_of_marginLo ha ha' hb (abs_le.mp hc).1 hx rfl rfl
    fun hn ↦ le_or_lt_of_rowRegionEnds_fst_le hn h1 h3
  have := (Rat.cast_strictMono (K := ℝ)) hC
  push_cast at this; linarith

/-- An excluded interval of `row_region` on the branch of the larger root, from `C(nh)` to `C(l)`,
for `1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`: a third coordinate `c` of a word that it takes out
lies strictly between the exact values `C(nh) < c < C(l)`, so that `a t² - b t + c` has a root in
`(l, nh)`, inside the interval. -/
theorem NegativeIntervals.Sound.exists_contains_of_regionExcludes_from (hneg : neg.Sound cs)
    (hi : i < neg.numNeg) (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hc : |c| ≤ 2 ^ 26)
    (hl : rowRegionFrom neg a b i < neg.shrunkHi[i]!)
    (hx : RegionExcludes sd (rowRegionMarginLo (if neg.shrunkHi[i]!.beq Double.huge then
      -Double.huge else rowRegionValue a b neg.shrunkHi[i]!))
      (rowRegionMarginHi (rowRegionValue a b (rowRegionFrom neg a b i))) (c >>> longShift)) :
    ∃ x : ℝ, (a : ℝ) * x ^ 2 - b * x + c = 0 ∧ neg.Contains i x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hnh := (Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkHi hi)
  obtain ⟨hlf, hnll⟩ := Double.isFinite_rowRegionFrom_and_le ha ha' hb
    ((Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkLo hi)) hl
  have hCl := mul_sq_sub_mul_add_neg_of_lt_rowRegionEnds_snd ha ha' hb hc hlf hx2 hx4
  have hlt := Double.doubleValue_lt_of_lt hl
  rw [Double.doubleValue_eq_toRat hlf] at hnll hlt
  by_cases hbeq : neg.shrunkHi[i]!.beq Double.huge = true
  · obtain ⟨x, hlx, hx⟩ := exists_gt_eq_zero (mod_cast ha) hCl
    refine ⟨x, hx, _, x + 1, hlx, by linarith, fun q h1 _ ↦ ⟨hnll.trans_lt ?_, ?_⟩⟩
    · exact WithBotTop.coe_lt_coe.mpr (mod_cast h1)
    · exact Double.coe_lt_doubleValue_of_beq_huge hnh hbeq _
  rw [ite_eq_right hbeq] at hx1 hx3
  have hnhf := Double.isFinite_of_not_beq_huge_of_lt_doubleValue hnh hbeq hlt
  have hCh := mul_sq_sub_mul_add_pos_of_rowRegionEnds_fst_le ha ha' hb hc hnhf hx1 hx3
  rw [Double.doubleValue_eq_toRat hnhf, WithBotTop.coe_lt_coe] at hlt
  obtain ⟨x, h1, h2, h3⟩ := exists_eq_zero_of_neg_of_pos (mod_cast hlt) hCl hCh
  refine ⟨x, h3, _, _, h1, h2, fun q h1 h2 ↦ ⟨hnll.trans_lt ?_, ?_⟩⟩
  · exact WithBotTop.coe_lt_coe.mpr (mod_cast h1)
  · exact Double.doubleValue_eq_toRat hnhf ▸ WithBotTop.coe_lt_coe.mpr (mod_cast h2)

/-- An excluded interval of `row_region` on the branch of the smaller root, from `C(nl)` to
`C(h)`, for `1 ≤ a ≤ 2 ^ 26` and `|b|, |c| ≤ 2 ^ 26`: a third coordinate `c` of a word that it
takes out lies strictly between the exact values `C(nl) < c < C(h)`, so that `a t² - b t + c` has
a root in `(nl, h)`, inside the interval. -/
theorem NegativeIntervals.Sound.exists_contains_of_regionExcludes_upTo (hneg : neg.Sound cs)
    (hi : i < neg.numNeg) (ha : 1 ≤ a) (ha' : a ≤ 2 ^ 26) (hb : |b| ≤ 2 ^ 26) (hc : |c| ≤ 2 ^ 26)
    (hh : neg.shrunkLo[i]! < rowRegionUpTo neg a b i)
    (hx : RegionExcludes sd (rowRegionMarginLo (if neg.shrunkLo[i]!.beq (-Double.huge) then
      -Double.huge else rowRegionValue a b neg.shrunkLo[i]!))
      (rowRegionMarginHi (rowRegionValue a b (rowRegionUpTo neg a b i))) (c >>> longShift)) :
    ∃ x : ℝ, (a : ℝ) * x ^ 2 - b * x + c = 0 ∧ neg.Contains i x := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hnl := (Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkLo hi)
  obtain ⟨hhf, hhnh⟩ := Double.isFinite_rowRegionUpTo_and_le ha ha' hb
    ((Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkHi hi)) hh
  have hCh := mul_sq_sub_mul_add_neg_of_lt_rowRegionEnds_snd ha ha' hb hc hhf hx2 hx4
  have hlt := Double.doubleValue_lt_of_lt hh
  rw [Double.doubleValue_eq_toRat hhf] at hhnh hlt
  by_cases hbeq : neg.shrunkLo[i]!.beq (-Double.huge) = true
  · obtain ⟨x, hxh, hx⟩ := exists_lt_eq_zero (mod_cast ha) hCh
    refine ⟨x, hx, x - 1, _, by linarith, hxh, fun q _ h2 ↦ ⟨?_, ?_⟩⟩
    · exact Double.doubleValue_lt_coe_of_beq_neg_huge hnl hbeq _
    · exact (WithBotTop.coe_lt_coe.mpr (mod_cast h2)).trans_le hhnh
  rw [ite_eq_right hbeq] at hx1 hx3
  have hnlf := Double.isFinite_of_not_beq_neg_huge_of_doubleValue_lt hnl hbeq hlt
  have hCl := mul_sq_sub_mul_add_pos_of_rowRegionEnds_fst_le ha ha' hb hc hnlf hx1 hx3
  rw [Double.doubleValue_eq_toRat hnlf, WithBotTop.coe_lt_coe] at hlt
  obtain ⟨x, h1, h2, h3⟩ := exists_eq_zero_of_pos_of_neg (mod_cast hlt) hCl hCh
  refine ⟨x, h3, _, _, h1, h2, fun q h1 h2 ↦ ⟨?_, ?_⟩⟩
  · exact Double.doubleValue_eq_toRat hnlf ▸ WithBotTop.coe_lt_coe.mpr (mod_cast h1)
  · exact (WithBotTop.coe_lt_coe.mpr (mod_cast h2)).trans_le hhnh

/-- The third coordinate `c` of a point over a triple `(a, b, c)`, `0 ≤ a` and `|b|, |c| ≤ 2 ^ 26`
(and `b > 0` when `a = 0`), lies in no word that an excluded interval of `row_region` for the row
`(a, b)` takes out, for sound intervals of a squarefree `f`: the interval would give a root of
`a t² - b t + c` (or `c / b` for `a = 0`) inside an interval on which `f` is negative, where the
point makes `f` at least `0`. -/
theorem NegativeIntervals.Sound.not_regionExcludes_of_hasPointOver (hneg : neg.Sound cs)
    (h7 : cs.length ≤ 7) (hsq : Squarefree (poly cs)) (ha : 0 ≤ a) (ha' : a ≤ 2 ^ 26)
    (hb : |b| ≤ 2 ^ 26) (hc : |c| ≤ 2 ^ 26) (hb0 : a = 0 → 0 < b) (hp : HasPointOver cs (a, b, c))
    (hi : i < neg.numNeg) {lo hi' : Double} (hI : RegionInterval neg a b i lo hi') :
    ¬RegionExcludes sd (rowRegionMarginLo lo) (rowRegionMarginHi hi') (c >>> longShift) := by
  intro hx
  rcases hI with ⟨ha0, hP⟩ | ⟨ha0, hlo, hhi⟩
  · obtain ⟨x, hx0, hcont⟩ : ∃ x : ℝ, (a : ℝ) * x ^ 2 - b * x + c = 0 ∧ neg.Contains i x := by
      rcases hP with ⟨hl, rfl, rfl⟩ | ⟨hh, rfl, rfl⟩
      · exact hneg.exists_contains_of_regionExcludes_from hi ha0 ha' hb hc hl hx
      · exact hneg.exists_contains_of_regionExcludes_upTo hi ha0 ha' hb hc hh hx
    have h1 := hneg.eval_map_neg_of_contains hsq hi hcont
    rw [eval_map_poly_eq_sum h7] at h1
    linarith [sum_nonneg_of_hasPointOver ha0.ne' hp hx0]
  obtain rfl : a = 0 := by lia
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hb1 := hb0 rfl
  have hc' := abs_le.mp hc
  have hnl := (Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkLo hi)
  have hnh := (Double.isNaN_eq_false_iff _).mpr (hneg.not_isNaN_shrunkHi hi)
  have hup := le_or_lt_of_lt_rowRegionEnds_snd (c := c) (by linarith) hx2 hx4
  have h1 := Double.lt_div_of_marginLo hb1 (le_of_abs_le hb) hc'.1 hnl hlo rfl hx1
    fun hn ↦ le_or_lt_of_rowRegionEnds_fst_le hn hx1 hx3
  have h2 := Double.div_lt_of_marginHi hb1 (le_of_abs_le hb) hc'.2 hnh hhi rfl ⟨hup.1, hx2, hup.2⟩
  linarith [hneg.eval_neg hi h1 h2, eval_poly_div_nonneg_of_hasPointOver h7 hb1.ne' hp]

end Branches

end JPoints

end
