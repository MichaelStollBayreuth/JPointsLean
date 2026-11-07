/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Coprime triples and squares of integers

Candidates for `Mathlib.Algebra.GCDMonoid.Nat`: a triple of integers, not all zero, is a positive
multiple of a coprime triple (`Int.exists_pos_mul_and_gcd_eq_one`), whose gcd is the factor
(`Int.gcd_mul_gcd_mul_mul_of_gcd_eq_one`), and an integer whose product with a nonzero square is a
square is a square (`Int.isSquare_of_sq_mul_eq_sq`).

## Main statements

* `Int.exists_pos_mul_and_gcd_eq_one`, `Int.gcd_mul_gcd_mul_mul_of_gcd_eq_one`: a triple as a
  multiple of a coprime triple.
* `Int.isSquare_of_sq_mul_eq_sq`: an integer whose product with a nonzero square is a square.

## Implementation notes

The names are written `_root_.Int.…`, so that the namespace `Int` is not opened in the statements
and the proofs, where `gcd` is `GCDMonoid.gcd`, not `Int.gcd`.
-/

@[expose] public section

/-- A triple of integers, not all zero, is a positive multiple of a coprime triple. Compare
`Int.exists_gcd_one'`, for two integers, with `Int.gcd`, a natural factor on the right and the
hypothesis `0 < Int.gcd m n`. -/
theorem _root_.Int.exists_pos_mul_and_gcd_eq_one (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ g A B C : ℤ, 0 < g ∧ gcd A (gcd B C) = 1 ∧ a = g * A ∧ b = g * B ∧ c = g * C := by
  set g := gcd a (gcd b c) with hg
  have hg0 : g ≠ 0 := by simp only [hg, ne_eq, gcd_eq_zero_iff]; tauto
  have hpos : 0 < g := (Int.gcd_nonneg _ _).lt_of_ne' hg0
  obtain ⟨A, hA⟩ := gcd_dvd_left a (gcd b c)
  obtain ⟨B, hB⟩ := (gcd_dvd_right a (gcd b c)).trans (gcd_dvd_left b c)
  obtain ⟨C, hC⟩ := (gcd_dvd_right a (gcd b c)).trans (gcd_dvd_right b c)
  have : gcd (g * A) (gcd (g * B) (g * C)) = g := by rw [← hA, ← hB, ← hC]
  simp only [gcd_mul_left, Int.normalize_of_nonneg hpos.le, mul_eq_left₀ hg0] at this
  exact ⟨g, A, B, C, hpos, this, hA, hB, hC⟩

theorem _root_.Int.gcd_mul_gcd_mul_mul_of_gcd_eq_one {m a b c : ℤ} (hm : 0 ≤ m)
    (h : gcd a (gcd b c) = 1) : gcd (m * a) (gcd (m * b) (m * c)) = m := by
  simp [Int.normalize_of_nonneg hm, h]

theorem _root_.Int.isSquare_of_sq_mul_eq_sq {a b x : ℤ} (ha : a ≠ 0) (h : a ^ 2 * x = b ^ 2) :
    IsSquare x := by
  obtain ⟨t, rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨x, h.symm⟩
  exact ⟨t, mul_left_cancel₀ (pow_ne_zero 2 ha) (h.trans (by rw [mul_pow, sq t]))⟩

end
