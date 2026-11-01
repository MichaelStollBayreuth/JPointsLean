/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Factorization.Defs

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.Data.Nat.Factorization.Defs
import JPoints.Proof.Order
import JPoints.Proof.Reduction
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination

/-!
# The first coordinates of the points of a monic quintic

For a quintic `f` whose leading coefficient `f₅` is a unit, the first coordinate `a ≥ 0` of a
coprime triple `(a, b, c)` over which a point of the Kummer surface lies that comes from a rational
point of the Jacobian is a square (`JPoints.isSquare_of_mem_kummerPoints`); this is why the main
search takes only the squares `a` for a monic quintic. The exponent in `a` of every prime `p ∣ a` is
even. For `p ∤ b`, the Kummer equation makes `p` prime to the denominator `m` of the point
`(m a, m b, m c, n)`, and `A₂ = a m³ Y` with `Y ≡ f₅ m b³ (mod p)` is a square
(`JPoints.even_factorization_natAbs_of_isSquare_auxA2`). For `p ∣ b`, the discriminant of the Kummer
quadratic, a square, is `16 a R` with `R ≡ f₅² c⁵ (mod p)`, where `R` is the resultant of `f` and
`a x² - b x + c` (`JPoints.exists_discrim_kummerK2_eq`,
`JPoints.even_factorization_natAbs_of_kummer_eq_zero`).

## Main statements

* `JPoints.isSquare_of_mem_kummerPoints`: the first coordinate is a square.
* `JPoints.exists_discrim_kummerK2_eq`: the discriminant of the Kummer quadratic of a quintic.
* `JPoints.even_factorization_natAbs_of_isSquare_auxA2`,
  `JPoints.even_factorization_natAbs_of_kummer_eq_zero`: the exponent of a prime that divides the
  first coordinate.

## Implementation notes

The exponents are those of `Nat.factorization` of the absolute value, through
`Int.isSquare_iff_nonneg_even_factorization` and the candidate for Mathlib
`Int.even_factorization_natAbs_of_isSquare_mul`; the conditions modulo `p` are read in `ZMod p`.
-/

@[expose] public section

namespace JPoints

/-- For a quintic, `f 6 = 0`, the discriminant of the Kummer quadratic over `(a, b, c)` is `16 a`
times the resultant `R` of `f` and `a x² - b x + c`, and `R ≡ f₅² c⁵` modulo `a` and `b`: the
discriminant vanishes on the lines `a r² - b r + c = 0` for the roots `r` of `f` and on the line
`a = 0` of the point at infinity. -/
theorem exists_discrim_kummerK2_eq {f : ℕ → ℤ} (h6 : f 6 = 0) (a b c : ℤ) :
    ∃ S T, discrim (kummerK2 a b c) (kummerK1 f a b c) (kummerK0 f a b c) =
      16 * a * (f 5 ^ 2 * c ^ 5 + a * S + b * T) := by
  refine ⟨f 0 ^ 2 * a ^ 4 + f 0 * f 1 * a ^ 3 * b - 2 * f 0 * f 2 * a ^ 3 * c +
    f 0 * f 2 * a ^ 2 * b ^ 2 - 3 * f 0 * f 3 * a ^ 2 * b * c + f 0 * f 3 * a * b ^ 3 +
    2 * f 0 * f 4 * a ^ 2 * c ^ 2 - 4 * f 0 * f 4 * a * b ^ 2 * c + f 0 * f 4 * b ^ 4 +
    5 * f 0 * f 5 * a * b * c ^ 2 - 5 * f 0 * f 5 * b ^ 3 * c + f 1 ^ 2 * a ^ 3 * c +
    f 1 * f 2 * a ^ 2 * b * c - 2 * f 1 * f 3 * a ^ 2 * c ^ 2 + f 1 * f 3 * a * b ^ 2 * c -
    3 * f 1 * f 4 * a * b * c ^ 2 + f 1 * f 4 * b ^ 3 * c + 2 * f 1 * f 5 * a * c ^ 3 -
    4 * f 1 * f 5 * b ^ 2 * c ^ 2 + f 2 ^ 2 * a ^ 2 * c ^ 2 + f 2 * f 3 * a * b * c ^ 2 -
    2 * f 2 * f 4 * a * c ^ 3 + f 2 * f 4 * b ^ 2 * c ^ 2 - 3 * f 2 * f 5 * b * c ^ 3 +
    f 3 ^ 2 * a * c ^ 3 + f 3 * f 4 * b * c ^ 3 - 2 * f 3 * f 5 * c ^ 4 + f 4 ^ 2 * c ^ 4,
    f 5 * (f 0 * b ^ 4 + f 1 * b ^ 3 * c + f 2 * b ^ 2 * c ^ 2 + f 3 * b * c ^ 3 + f 4 * c ^ 4), ?_⟩
  simp only [discrim, kummerK2, kummerK1, kummerK0, h6]
  ring

/-- The exponent in `a` of a prime `p` that divides `a` and `b` but not `c` is even when the Kummer
quadratic over `(a, b, c)` of a quintic with `p ∤ f₅` has the rational root `n / m`: its
discriminant `16 a R` (`JPoints.exists_discrim_kummerK2_eq`) is then a square, and
`R ≡ f₅² c⁵ (mod p)`. -/
theorem even_factorization_natAbs_of_kummer_eq_zero {f : ℕ → ℤ} (h6 : f 6 = 0) {p : ℕ}
    (hp : p.Prime) (h5 : ¬(p : ℤ) ∣ f 5) {m a b c n : ℤ} (hm : m ≠ 0)
    (hK : kummer f (m * a) (m * b) (m * c) n = 0) (ha : (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b)
    (hc : ¬(p : ℤ) ∣ c) : Even (a.natAbs.factorization p) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, T, hD⟩ := exists_discrim_kummerK2_eq h6 a b c
  rw [discrim] at hD
  have hq := (mul_eq_zero.1 ((kummer_mul_mul_mul f m a b c n).symm.trans hK)).resolve_left
    (pow_ne_zero 2 hm)
  refine Int.even_factorization_natAbs_of_isSquare_mul (z := f 5 ^ 2 * c ^ 5 + a * S + b * T)
    (Int.isSquare_of_sq_mul_eq_sq (a := 4 * m) (b := 2 * kummerK2 a b c * n + kummerK1 f a b c * m)
      (by simpa using hm) (by linear_combination (-m ^ 2) * hD - 4 * kummerK2 a b c * hq)) ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb hc h5 ⊢
  push_cast [ha, hb]
  simpa using ⟨h5, hc⟩

/-- The exponent in `a` of a prime `p` that divides `a` but not `b` is even when `A₂` of the point
`(m a, m b, m c, n)` of the Kummer surface of a quintic with `p ∤ f₅`, `n` and `m` coprime, is a
square: `p ∤ m`, since otherwise `b² ≡ K₂ ≡ 0 (mod p)`
(`JPoints.cast_kummerK2_eq_zero_of_kummer_eq_zero`), and
`A₂ = a m³ (a² n + m (f₂ a³ + f₃ a² b + f₄ a b² + f₅ b (b² - a c)))`, whose second factor is
`≡ f₅ m⁴ b³ (mod p)`. -/
theorem even_factorization_natAbs_of_isSquare_auxA2 {f : ℕ → ℤ} (h6 : f 6 = 0) {p : ℕ}
    (hp : p.Prime) (h5 : ¬(p : ℤ) ∣ f 5) {m a b c n : ℤ} (hm : m ≠ 0) (hnm : IsCoprime n m)
    (hK : kummer f (m * a) (m * b) (m * c) n = 0)
    (hA : IsSquare (auxA2 f (m * a) (m * b) (m * c) n)) (ha : (p : ℤ) ∣ a)
    (hb : ¬(p : ℤ) ∣ b) : Even (a.natAbs.factorization p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA' : auxA2 f (m * a) (m * b) (m * c) n = a * (m ^ 3 * (a ^ 2 * n +
      m * (f 2 * a ^ 3 + f 3 * a ^ 2 * b + f 4 * a * b ^ 2 + f 5 * b * (b ^ 2 - a * c)))) := by
    simp only [auxA2, h6]
    ring
  refine Int.even_factorization_natAbs_of_isSquare_mul (hA' ▸ hA) ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb h5 ⊢
  have hm' : (m : ZMod p) ≠ 0 := fun h ↦ by
    have hn := hnm.map (Int.castRingHom (ZMod p))
    simp only [eq_intCast, h, isCoprime_zero_right] at hn
    simpa [kummerK2, ha, hb] using cast_kummerK2_eq_zero_of_kummer_eq_zero hm hK h hn.ne_zero
  push_cast [ha]
  simpa using ⟨hm', h5, hb⟩

/-- For a quintic whose leading coefficient `f₅` is a unit, the first coordinate `a ≥ 0` of a
coprime triple over which a candidate of `JPoints.kummerPoints` lifts is a square: the exponent in
`a` of a prime `p ∣ a` is even, by `A₂` for `p ∤ b`
(`JPoints.even_factorization_natAbs_of_isSquare_auxA2`) and by the discriminant of the Kummer
quadratic for `p ∣ b` (`JPoints.even_factorization_natAbs_of_kummer_eq_zero`). -/
theorem isSquare_of_mem_kummerPoints {f : ℕ → ℤ} (h5 : IsUnit (f 5)) (h6 : f 6 = 0) {a b c : ℤ}
    (ha : 0 ≤ a) (habc : gcd a (gcd b c) = 1) {P : ℤ × ℤ × ℤ × ℤ}
    (hP : P ∈ kummerPoints f (a, b, c)) (hL : Lifts f P.1 P.2.1 P.2.2.1 P.2.2.2) :
    IsSquare a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact .zero
  have hK := kummer_eq_zero_of_mem_kummerPoints hP
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hP
  have hm : (x.den : ℤ) ≠ 0 := by positivity
  simp only [Lifts, mul_eq_zero, hm, ha0, or_self, ↓reduceIte] at hL
  refine Int.isSquare_iff_nonneg_even_factorization.mpr ⟨ha, fun p hp ↦ ?_⟩
  have hp' := Nat.prime_iff_prime_int.mp hp
  have h5p : ¬(p : ℤ) ∣ f 5 := fun h ↦ hp'.not_isUnit (isUnit_of_dvd_unit h h5)
  by_cases hpa : (p : ℤ) ∣ a
  swap
  · rw [Nat.factorization_eq_zero_of_not_dvd (by rwa [← Int.natCast_dvd])]
    exact .zero
  by_cases hpb : (p : ℤ) ∣ b
  · exact even_factorization_natAbs_of_kummer_eq_zero h6 hp h5p hm hK hpa hpb
      fun hc ↦ hp'.not_dvd_one (habc ▸ dvd_gcd hpa (dvd_gcd hpb hc))
  · exact even_factorization_natAbs_of_isSquare_auxA2 h6 hp h5p hm
      (Rat.isCoprime_num_den x) hK hL.1 hpa hpb

end JPoints

end
