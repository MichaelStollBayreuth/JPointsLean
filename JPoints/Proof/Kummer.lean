/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.FieldTheory.Separable
import JPoints.Proof.Poly
import Mathlib.FieldTheory.Perfect

/-!
# The algebra of the Kummer surface

Facts about the polynomials of the specification on which the exact check of `j-points` rests.

* The lifting test needs `B₂` only when `A₂ = 0`: by the identity
  `4 A₂ B₂ = C² - a⁴ K(a, b, c, d)` (`JPoints.four_mul_auxA2_mul_auxB2`), on the Kummer surface a
  nonzero square `A₂` makes `B₂` a square (`JPoints.isSquare_auxB2_of_isSquare_auxA2`), so that the
  test of the program decides `JPoints.Lifts` (`JPoints.lifts_iff_of_kummer_eq_zero`); squares
  `A₂ = α²` and `B₂ = β²` there have the signs with `C = 2 α β` (`JPoints.exists_sq_auxA2_auxB2`),
  and give the square `A₂'` of the point `(c, b, a, d)` of the reversed curve `y² = x⁶ f(1 / x)` for
  `a ≠ 0` (`JPoints.isSquare_auxA2_of_reversed`), by the linear transformation of the coefficients
  of the Mumford representation (`JPoints.pow_four_mul_auxA2_eq_of_reversed`,
  `JPoints.sq_mul_auxB2_eq_of_reversed`); over the triple `(m s², 2 m s t, m t²)` of a double point
  they make `m⁴ s⁴ F(t, s) = (t α + s β)²` a square
  (`JPoints.pow_four_mul_pow_four_mul_sexticForm_eq`).
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
* `JPoints.exists_sq_auxA2_auxB2`: the square roots of `A₂` and `B₂` with `C = 2 α β`.
* `JPoints.isSquare_auxA2_of_reversed`: the square `A₂'` of the reversed point.
* `JPoints.kummer_mul`, `JPoints.kummer_mul_div`: the Kummer equation is homogeneous of degree 4.
* `JPoints.kummer_mul_mul_mul`, `JPoints.kummer_mul_mul_mul_eq_zero_iff`,
  `JPoints.auxA2_mul_mul_mul`: the Kummer equation and `A₂` at `(m a, m b, m c, n)`.
* `JPoints.pow_four_mul_pow_four_mul_sexticForm_eq`: the form `F(t, s)` over the triple of a
  double point, from `A₂`, `B₂` and `C`.
* `JPoints.cast_sexticForm`, `JPoints.sexticForm_mul_mul`, `JPoints.sexticForm_neg`,
  `JPoints.sexticForm_zero_left`: the binary sextic form `F(x, z) = z⁶ f(x / z)`.
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

/-- On the conic `b² = 4ac`, over the triple `(m s², 2 m s t, m t²)` of the double point of
`x = t / s`, the value `F(t, s) = s⁶ f(t / s)` from `A₂`, `B₂` and `C`:
`m⁴ s⁴ F(t, s) = t² A₂ + s t C + s² B₂`, which is `(t α + s β)²` when `A₂ = α²`, `B₂ = β²` and
`C = 2 α β`. -/
theorem pow_four_mul_pow_four_mul_sexticForm_eq (f : ℕ → ℤ) (m s t d : ℤ) :
    m ^ 4 * s ^ 4 * sexticForm f t s =
      t ^ 2 * auxA2 f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d +
        s * t * auxC f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d +
        s ^ 2 * auxB2 f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d := by
  simp only [sexticForm, auxA2, auxB2, auxC, Finset.sum_range_succ, Finset.sum_range_zero]
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

/-- The squares `A₂ = α²` and `B₂ = β²` of the lifting test on the Kummer surface, with the signs
of the Mumford representation `(x² - (b / a) x + c / a, v₁ x + v₀)`, `α = a² v₁` and `β = a² v₀`:
`2 α β = C` (`JPoints.auxC`), since `4 A₂ B₂ = C²` there (`JPoints.four_mul_auxA2_mul_auxB2`). -/
theorem exists_sq_auxA2_auxB2 {f : ℕ → ℤ} {a b c d : ℤ} (hK : kummer f a b c d = 0)
    (hA : IsSquare (auxA2 f a b c d)) (hB : IsSquare (auxB2 f a b c d)) :
    ∃ α β, α ^ 2 = auxA2 f a b c d ∧ β ^ 2 = auxB2 f a b c d ∧ 2 * α * β = auxC f a b c d := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, hβ⟩ := hB
  have h : auxC f a b c d ^ 2 = (2 * α * β) ^ 2 := by
    linear_combination -(four_mul_auxA2_mul_auxB2 f a b c d) + a ^ 4 * hK +
      4 * auxB2 f a b c d * hα + 4 * α ^ 2 * hβ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨α, β, by rw [hα, sq], by rw [hβ, sq], h.symm⟩
  · exact ⟨-α, β, by rw [hα, neg_sq, sq], by rw [hβ, sq], by linear_combination -h⟩

section Reversed

variable {f g : ℕ → ℤ}

/-- `A₂` of the reversed curve `g` at `(c, b, a, d)` from `A₂`, `B₂` and `C` of `f` at
`(a, b, c, d)`: `a⁴ A₂' = b² c² A₂ + b c (b² - a c) C + (b² - a c)² B₂`, which is
`(b c α + (b² - a c) β)²` when `A₂ = α²`, `B₂ = β²` and `C = 2 α β`. -/
theorem pow_four_mul_auxA2_eq_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (a b c d : ℤ) :
    a ^ 4 * auxA2 g c b a d = b ^ 2 * c ^ 2 * auxA2 f a b c d +
      b * c * (b ^ 2 - a * c) * auxC f a b c d + (b ^ 2 - a * c) ^ 2 * auxB2 f a b c d := by
  simp (disch := lia) only [auxA2, auxB2, auxC, hg]
  ring

/-- `B₂` of the reversed curve `g` at `(c, b, a, d)` from `A₂`, `B₂` and `C` of `f` at
`(a, b, c, d)`: `a² B₂' = c² A₂ + b c C + b² B₂`, which is `(c α + b β)²` when `A₂ = α²`,
`B₂ = β²` and `C = 2 α β`. -/
theorem sq_mul_auxB2_eq_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (a b c d : ℤ) :
    a ^ 2 * auxB2 g c b a d =
      c ^ 2 * auxA2 f a b c d + b * c * auxC f a b c d + b ^ 2 * auxB2 f a b c d := by
  simp (disch := lia) only [auxA2, auxB2, auxC, hg]
  ring

/-- The polynomial `A₂` of the point `(c, b, a, d)` of the reversed curve `g`, with
`g(x) = x⁶ f(1 / x)`, is a square for a point `(a, b, c, d)`, `a ≠ 0`, with the squares `α² = A₂`,
`β² = B₂` and `2 α β = C`: `a⁴` times it is `(b c α + (b² - a c) β)²`
(`JPoints.pow_four_mul_auxA2_eq_of_reversed`). -/
theorem isSquare_auxA2_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) {a b c d α β : ℤ}
    (ha : a ≠ 0) (hα : α ^ 2 = auxA2 f a b c d) (hβ : β ^ 2 = auxB2 f a b c d)
    (hαβ : 2 * α * β = auxC f a b c d) : IsSquare (auxA2 g c b a d) :=
  Int.isSquare_of_sq_mul_eq_sq (pow_ne_zero 2 ha) (b := b * c * α + (b ^ 2 - a * c) * β)
    (by linear_combination pow_four_mul_auxA2_eq_of_reversed hg a b c d - b ^ 2 * c ^ 2 * hα -
      b * c * (b ^ 2 - a * c) * hαβ - (b ^ 2 - a * c) ^ 2 * hβ)

end Reversed

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

/-- The Kummer equation at `(m a, m b, m c, n)` is `m²` times the Kummer quadratic over `(a, b, c)`
at `n / m`, cleared of its denominator. -/
theorem kummer_mul_mul_mul (f : ℕ → ℤ) (m a b c n : ℤ) :
    kummer f (m * a) (m * b) (m * c) n = m ^ 2 *
      (kummerK2 a b c * n ^ 2 + kummerK1 f a b c * (m * n) + kummerK0 f a b c * m ^ 2) := by
  simp only [kummer, kummerK2, kummerK1, kummerK0]
  ring

theorem kummer_mul_mul_mul_eq_zero_iff {f : ℕ → ℤ} {m : ℤ} (hm : m ≠ 0) (a b c n : ℤ) :
    kummer f (m * a) (m * b) (m * c) n = 0 ↔
      kummerK2 a b c * n ^ 2 + kummerK1 f a b c * (m * n) + kummerK0 f a b c * m ^ 2 = 0 := by
  rw [kummer_mul_mul_mul, mul_eq_zero, or_iff_right (pow_ne_zero 2 hm)]

theorem auxA2_mul_mul_mul (f : ℕ → ℤ) (m a b c n : ℤ) :
    auxA2 f (m * a) (m * b) (m * c) n = m ^ 3 * (a ^ 3 * n + m * auxA2 f a b c 0) := by
  simp only [auxA2]
  ring

/-! ### The binary sextic form -/

theorem cast_sexticForm {R : Type*} [CommRing R] (f : ℕ → ℤ) (x z : ℤ) :
    ((sexticForm f x z : ℤ) : R) =
      ∑ k ∈ Finset.range 7, (f k : R) * (x : R) ^ k * (z : R) ^ (6 - k) := by
  simp [sexticForm]

theorem sexticForm_mul_mul (f : ℕ → ℤ) (m x z : ℤ) :
    sexticForm f (m * x) (m * z) = m ^ 6 * sexticForm f x z := by
  simp only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem sexticForm_neg (f : ℕ → ℤ) (x z : ℤ) : sexticForm f (-x) (-z) = sexticForm f x z := by
  simpa using sexticForm_mul_mul f (-1) x z

theorem sexticForm_zero_left (f : ℕ → ℤ) (z : ℤ) : sexticForm f 0 z = f 0 * z ^ 6 := by
  simp [sexticForm, Finset.sum_range_succ]

/-! ### The Kummer equation over a nonzero triple -/

section

open Polynomial

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
  all_goals rwa [h]

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
