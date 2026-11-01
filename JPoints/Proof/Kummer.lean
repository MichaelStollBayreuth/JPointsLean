/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic
public import Mathlib.Algebra.Polynomial.Derivative

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.FieldTheory.Separable
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Perfect

/-!
# The algebra of the Kummer surface

Two facts about the polynomials of the specification on which the exact check of `j-points` rests.

* The lifting test needs `B₂` only when `A₂ = 0`: by the identity
  `4 A₂ B₂ = C² - a⁴ K(a, b, c, d)` (`JPoints.four_mul_auxA2_mul_auxB2`), on the Kummer surface a
  nonzero square `A₂` makes `B₂` a square (`JPoints.isSquare_auxB2_of_isSquare_auxA2`), so that the
  test of the program decides `JPoints.Lifts` (`JPoints.lifts_iff_of_kummer_eq_zero`).
* The Kummer equation over a triple `(a, b, c) ≠ 0` is never constant zero when `f` is squarefree
  of degree 5 or 6 (`JPoints.kummerK0_ne_zero`): on the conic `b² = 4ac`, with `x = b / (2a)`,
  `K₁ = -4 a³ f(x)` and `K₀ = a⁴ (f'(x)² - 4 f(x) g(x))` for a polynomial `g`, so that
  `K₁ = K₀ = 0` makes `x` a double root of `f`; and over `(0, 0, c)`, `K₁ = -4 f₆ c³` and
  `K₀ = (f₅² - 4 f₄ f₆) c⁴` vanish only when `f₆ = f₅ = 0`.

## Main definitions

* `JPoints.auxC`: the polynomial `C` of the identity `4 A₂ B₂ = C² - a⁴ K`.

## Main statements

* `JPoints.four_mul_auxA2_mul_auxB2`: the identity.
* `JPoints.lifts_iff_of_kummer_eq_zero`: on the Kummer surface, `JPoints.Lifts` is the lifting
  test of the program.
* `JPoints.kummer_mul`, `JPoints.kummer_mul_div`: the Kummer equation is homogeneous of degree 4.
* `JPoints.kummerK0_ne_zero`: the Kummer equation over a nonzero triple is not constant zero.
-/

@[expose] public section

namespace JPoints

/-- The polynomial `C = f₁ a⁴ - f₃ a³ c - 2 f₄ a² b c + f₅ a² c² - 2 f₅ a b² c + 2 f₆ a b c² -
2 f₆ b³ c - a² b d` of the identity `4 A₂ B₂ = C² - a⁴ K(a, b, c, d)`
(`JPoints.four_mul_auxA2_mul_auxB2`). -/
def auxC (f : ℕ → ℤ) (a b c d : ℤ) : ℤ :=
  f 1 * a ^ 4 - f 3 * a ^ 3 * c - 2 * f 4 * a ^ 2 * b * c + f 5 * a ^ 2 * c ^ 2 -
    2 * f 5 * a * b ^ 2 * c + 2 * f 6 * a * b * c ^ 2 - 2 * f 6 * b ^ 3 * c - a ^ 2 * b * d

theorem four_mul_auxA2_mul_auxB2 (f : ℕ → ℤ) (a b c d : ℤ) :
    4 * auxA2 f a b c d * auxB2 f a b c d = auxC f a b c d ^ 2 - a ^ 4 * kummer f a b c d := by
  simp only [auxA2, auxB2, auxC, kummer, kummerK2, kummerK1, kummerK0]
  ring

/-- On the Kummer surface a nonzero square `A₂` makes `B₂` a square: `4 A₂ B₂ = C²`. -/
theorem isSquare_auxB2_of_isSquare_auxA2 {f : ℕ → ℤ} {a b c d : ℤ} (hK : kummer f a b c d = 0)
    (hA : auxA2 f a b c d ≠ 0) (hs : IsSquare (auxA2 f a b c d)) :
    IsSquare (auxB2 f a b c d) := by
  obtain ⟨s, hs⟩ := hs
  refine Int.isSquare_of_sq_mul_eq_sq (b := auxC f a b c d)
    (mul_ne_zero two_ne_zero (left_ne_zero_of_mul (hs ▸ hA))) ?_
  linear_combination four_mul_auxA2_mul_auxB2 f a b c d - 4 * auxB2 f a b c d * hs - a ^ 4 * hK

/-- On the Kummer surface, `JPoints.Lifts` is the lifting test of the program (`check_lifts`), which
looks at `B₂` only when `A₂ = 0`. -/
theorem lifts_iff_of_kummer_eq_zero {f : ℕ → ℤ} {a b c d : ℤ} (hK : kummer f a b c d = 0) :
    Lifts f a b c d ↔
      if a = 0 then (if b = 0 then IsSquare (f 6) else IsSquare (f 6) ∧ IsSquare (sexticForm f c b))
      else if auxA2 f a b c d = 0 then IsSquare (auxB2 f a b c d)
      else IsSquare (auxA2 f a b c d) := by
  rw [Lifts]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte]
  by_cases hA : auxA2 f a b c d = 0
  · simp [ha, hA]
  · simpa [ha, hA] using isSquare_auxB2_of_isSquare_auxA2 hK hA

theorem kummer_mul (f : ℕ → ℤ) (m a b c d : ℤ) :
    kummer f (m * a) (m * b) (m * c) (m * d) = m ^ 4 * kummer f a b c d := by
  simp only [kummer, kummerK2, kummerK1, kummerK0]
  ring

/-- The Kummer equation at `(m a, m b, m c, n)` is `m⁴` times the Kummer quadratic over `(a, b, c)`
at `n / m`. -/
theorem kummer_mul_div (f : ℕ → ℤ) (a b c n : ℤ) {m : ℤ} (hm : m ≠ 0) :
    (kummer f (m * a) (m * b) (m * c) n : ℚ) = m ^ 4 * (kummerK2 a b c * ((n : ℚ) / m) ^ 2 +
      kummerK1 f a b c * ((n : ℚ) / m) + kummerK0 f a b c) := by
  have : (m : ℚ) ≠ 0 := mod_cast hm
  push_cast [kummer, kummerK2, kummerK1, kummerK0]
  field

/-! ### The Kummer equation over a nonzero triple -/

section

open Polynomial

theorem degree_le_length_sub_one (cs : List ℤ) : degree cs ≤ cs.length - 1 :=
  Nat.sub_le_sub_right (by simpa using (cs.reverse.dropWhile_sublist (· == 0)).length_le) 1

theorem getD_degree_ne_zero {cs : List ℤ} (h : 0 < degree cs) : cs.getD (degree cs) 0 ≠ 0 := by
  have hc := List.rdropWhile_append_rtakeWhile (p := (· == (0 : ℤ))) (l := cs)
  have hlen : degree cs = (cs.rdropWhile (· == 0)).length - 1 := by
    simp [degree, List.rdropWhile]
  have hne : cs.rdropWhile (· == 0) ≠ [] := fun h' ↦ by simp [h'] at hlen; lia
  rw [← hc, List.getD_append _ _ _ _ (by lia), List.getD_eq_getElem _ _ (by lia)]
  simpa [List.getLast_eq_getElem, hlen] using List.rdropWhile_last_not _ _ hne

theorem getD_eq_zero_of_degree_lt {cs : List ℤ} {i : ℕ} (h : degree cs < i) :
    cs.getD i 0 = 0 := by
  have hc := List.rdropWhile_append_rtakeWhile (p := (· == (0 : ℤ))) (l := cs)
  have hlen : degree cs = (cs.rdropWhile (· == 0)).length - 1 := by
    simp [degree, List.rdropWhile]
  rw [← hc, List.getD_append_right _ _ _ _ (by lia)]
  rcases lt_or_ge (i - (cs.rdropWhile (· == 0)).length) (cs.rtakeWhile (· == 0)).length with
    hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    simpa using List.mem_rtakeWhile_imp (List.getElem_mem hi)
  · exact List.getD_eq_default _ _ hi

theorem eval_poly {cs : List ℤ} {n : ℕ} (h : cs.length ≤ n) (x : ℚ) :
    (poly cs).eval x = ∑ i ∈ Finset.range n, (cs.getD i 0 : ℚ) * x ^ i := by
  rw [poly, eval_finsetSum, Finset.sum_subset (Finset.range_subset_range.mpr h)]
  · simp
  · intro i _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]
    simp

theorem eval_derivative_poly {cs : List ℤ} {n : ℕ} (h : cs.length ≤ n) (x : ℚ) :
    (derivative (poly cs)).eval x = ∑ i ∈ Finset.range n, (cs.getD i 0 : ℚ) * i * x ^ (i - 1) := by
  rw [poly, derivative_sum, eval_finsetSum, Finset.sum_subset (Finset.range_subset_range.mpr h)]
  · simp [derivative_X_pow, mul_assoc]
  · intro i _ hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]
    simp

/-- On the conic `K₂ = b² - 4ac = 0`, parametrized as `(a, 2 a x, a x²)`, the coefficient `K₁` of
the Kummer equation is `-4 a³ f(x)`. -/
theorem cast_kummerK1_eq_mul_sum (f : ℕ → ℤ) {a b c : ℤ} {x : ℚ} (hb : (b : ℚ) = 2 * a * x)
    (hc : (c : ℚ) = a * x ^ 2) :
    (kummerK1 f a b c : ℚ) = -4 * a ^ 3 * ∑ k ∈ Finset.range 7, (f k : ℚ) * x ^ k := by
  push_cast [kummerK1, Finset.sum_range_succ, Finset.sum_range_zero, hb, hc]
  ring

/-- On the conic `K₂ = b² - 4ac = 0`, parametrized as `(a, 2 a x, a x²)`, the constant term `K₀`
of the Kummer equation is `a⁴ (f'(x)² - 4 f(x) g(x))`, where
`g(x) = f₂ + 2 f₃ x + 4 f₄ x² + 6 f₅ x³ + 9 f₆ x⁴`; so it is `a⁴ f'(x)²` at a root `x` of `f`. -/
theorem cast_kummerK0_eq_mul_sq (f : ℕ → ℤ) {a b c : ℤ} {x : ℚ} (hb : (b : ℚ) = 2 * a * x)
    (hc : (c : ℚ) = a * x ^ 2) (hF : ∑ k ∈ Finset.range 7, (f k : ℚ) * x ^ k = 0) :
    (kummerK0 f a b c : ℚ) = a ^ 4 * (∑ k ∈ Finset.range 7, (f k : ℚ) * k * x ^ (k - 1)) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hF
  push_cast [kummerK0, Finset.sum_range_succ, Finset.sum_range_zero, hb, hc]
  linear_combination
    -4 * a ^ 4 * (f 2 + 2 * f 3 * x + 4 * f 4 * x ^ 2 + 6 * f 5 * x ^ 3 + 9 * f 6 * x ^ 4) * hF

-- Over `(0, 0, c)`, `K₁ = -4 f₆ c³` and `K₀ = (f₅² - 4 f₄ f₆) c⁴` vanish only when `f₆ = f₅ = 0`.
private theorem kummerK0_ne_zero_of_left_eq_zero {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h5 : 5 ≤ degree cs) {b c : ℤ} (hbc : b ≠ 0 ∨ c ≠ 0) (h2 : kummerK2 0 b c = 0)
    (h1 : kummerK1 (cs.getD · 0) 0 b c = 0) : kummerK0 (cs.getD · 0) 0 b c ≠ 0 := by
  obtain rfl : b = 0 := by simpa [kummerK2] using h2
  have hc : c ≠ 0 := by simpa using hbc
  have h6 : cs.getD 6 0 = 0 := by simpa [kummerK1, hc] using h1
  intro h0
  simp only [kummerK0, h6] at h0
  have h5' : cs.getD 5 0 = 0 := by simpa [hc] using h0
  refine getD_degree_ne_zero (cs := cs) (by lia) ?_
  obtain h | h : degree cs = 5 ∨ degree cs = 6 := by lia [degree_le_length_sub_one cs]
  · rwa [h]
  · rwa [h]

-- Over `(a, b, c)` with `a ≠ 0`, `K₁ = K₀ = 0` makes `x = b / (2a)` a double root of `f`.
private theorem kummerK0_ne_zero_of_ne_zero {cs : List ℤ} (h7 : cs.length ≤ 7)
    (hsq : Squarefree (poly cs)) {a b c : ℤ} (ha : a ≠ 0)
    (h2 : kummerK2 a b c = 0) (h1 : kummerK1 (cs.getD · 0) a b c = 0) :
    kummerK0 (cs.getD · 0) a b c ≠ 0 := by
  have ha' : (a : ℚ) ≠ 0 := mod_cast ha
  rw [kummerK2] at h2
  have h2' : (b : ℚ) ^ 2 - 4 * a * c = 0 := mod_cast h2
  have hb : (b : ℚ) = 2 * a * (b / (2 * a)) := by field
  have hc : (c : ℚ) = a * (b / (2 * a)) ^ 2 := by
    linear_combination (norm := field) (-1 / (4 * a)) * h2'
  have hF := cast_kummerK1_eq_mul_sum (cs.getD · 0) hb hc
  rw [h1, Int.cast_zero, eq_comm, mul_eq_zero] at hF
  replace hF := hF.resolve_left (by simp [ha'])
  intro h0
  have hF' := cast_kummerK0_eq_mul_sq (cs.getD · 0) hb hc hF
  rw [h0, Int.cast_zero, eq_comm] at hF'
  refine (PerfectField.separable_iff_squarefree.mpr hsq).eval_derivative_ne_zero
    (x := b / (2 * a)) ?_ ?_
  · rwa [eval_poly h7]
  · rw [eval_derivative_poly h7]
    simpa [ha'] using hF'

/-- The Kummer equation over a triple `(a, b, c) ≠ 0` is not constant zero, for a squarefree `f`
of degree 5 or 6: if `K₂ = K₁ = 0`, then `K₀ ≠ 0`. -/
theorem kummerK0_ne_zero {cs : List ℤ} (h7 : cs.length ≤ 7) (h5 : 5 ≤ degree cs)
    (hsq : Squarefree (poly cs)) {a b c : ℤ} (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h2 : kummerK2 a b c = 0) (h1 : kummerK1 (cs.getD · 0) a b c = 0) :
    kummerK0 (cs.getD · 0) a b c ≠ 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact kummerK0_ne_zero_of_left_eq_zero h7 h5 (by simpa using habc) h2 h1
  · exact kummerK0_ne_zero_of_ne_zero h7 hsq ha h2 h1

end

end JPoints

end
