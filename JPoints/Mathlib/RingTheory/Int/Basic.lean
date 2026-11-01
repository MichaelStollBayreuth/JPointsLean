/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Int.Basic

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

/-!
# Coprime triples on the conic `b² = 4ac`

Candidates for `Mathlib.RingTheory.Int.Basic`, next to `Int.sq_of_gcd_eq_one`: a coprime triple
`(a, b, c)` with `b² = 4ac` and `a > 0` is `(s², 2st, t²)` for coprime `s > 0` and `t`
(`Int.exists_eq_of_sq_eq_four_mul_mul`), and such a triple is coprime
(`Int.gcd_sq_gcd_two_mul_mul_sq_eq_one`).

## Main statements

* `Int.gcd_eq_one_of_mul_eq_sq`: the first and the third coordinate of a coprime triple
  `(a, 2m, c)` with `ac = m²` are coprime.
* `Int.exists_eq_of_sq_eq_four_mul_mul`, `Int.gcd_sq_gcd_two_mul_mul_sq_eq_one`: the coprime
  triples on the conic.

## Implementation notes

The names are written `_root_.Int.…`, so that the namespace `Int` is not opened in the statements
and the proofs, where `gcd` is `GCDMonoid.gcd`, not `Int.gcd`.
-/

@[expose] public section

/-- The first and the third coordinate of a coprime triple `(a, 2m, c)` with `ac = m²` are
coprime. -/
theorem _root_.Int.gcd_eq_one_of_mul_eq_sq {a c m : ℤ} (hg : gcd a (gcd (2 * m) c) = 1)
    (hm : a * c = m ^ 2) : Int.gcd a c = 1 := by
  have hd : (Int.gcd a c : ℤ) ∣ m := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← hm, sq]
    exact mul_dvd_mul (Int.gcd_dvd_left a c) (Int.gcd_dvd_right a c)
  have h1 : (Int.gcd a c : ℤ) ∣ 1 := hg ▸ dvd_gcd (Int.gcd_dvd_left a c)
    (dvd_gcd (hd.mul_left 2) (Int.gcd_dvd_right a c))
  exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1

/-- A coprime triple `(a, b, c)` on the conic `b² = 4ac` with `a > 0` is `(s², 2st, t²)` for coprime
`s > 0` and `t`: `b = 2m` with `ac = m²` and `a`, `c` coprime, so that `a` and `c` are squares. -/
theorem _root_.Int.exists_eq_of_sq_eq_four_mul_mul {a b c : ℤ} (hg : gcd a (gcd b c) = 1)
    (ha : 0 < a) (h : b ^ 2 = 4 * a * c) :
    ∃ s t : ℤ, 0 < s ∧ Int.gcd s t = 1 ∧ (a, b, c) = (s ^ 2, 2 * s * t, t ^ 2) := by
  obtain ⟨m, rfl⟩ : 2 ∣ b := Int.prime_two.dvd_of_dvd_pow ⟨2 * a * c, by rw [h]; ring⟩
  have hm : a * c = m ^ 2 := mul_left_cancel₀ four_ne_zero (by linear_combination -h)
  have hac := Int.gcd_eq_one_of_mul_eq_sq hg hm
  obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one hac hm
  have ha' : a = |s| ^ 2 := by
    rw [sq_abs]
    exact hs.resolve_right fun h ↦ by lia [sq_nonneg s]
  have hs0 : 0 < |s| := abs_pos.mpr fun h ↦ by simp [h] at ha'; lia
  obtain ⟨t, rfl⟩ : |s| ∣ m := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨c, by rw [← hm, ha']⟩
  have hc : c = t ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hs0.ne') (by rw [← ha', hm, ha']; ring)
  refine ⟨|s|, t, hs0, ?_, by rw [ha', hc]; ring_nf⟩
  rw [← Int.isCoprime_iff_gcd_eq_one] at hac ⊢
  rw [ha', hc] at hac
  exact IsCoprime.pow_iff two_pos two_pos |>.mp hac

theorem _root_.Int.gcd_sq_gcd_two_mul_mul_sq_eq_one {s t : ℤ} (h : Int.gcd s t = 1) :
    gcd (s ^ 2) (gcd (2 * s * t) (t ^ 2)) = 1 := by
  have hc : gcd (s ^ 2) (t ^ 2) = 1 := by
    rw [← Int.coe_gcd, Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr h).pow,
      Nat.cast_one]
  exact Int.eq_one_of_dvd_one (Int.gcd_nonneg _ _) (hc ▸ gcd_dvd_gcd dvd_rfl (gcd_dvd_right _ _))

end
