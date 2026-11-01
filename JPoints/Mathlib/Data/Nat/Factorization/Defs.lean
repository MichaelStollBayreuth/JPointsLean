/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Factorization.Defs

/-!
# The exponents of a factor of a square integer

A candidate for `Mathlib.Data.Nat.Factorization.Defs`, next to
`Int.isSquare_iff_nonneg_even_factorization`: a factor `y` of a square integer `y * z` has an even
exponent at every prime that does not divide the cofactor `z`
(`Int.even_factorization_natAbs_of_isSquare_mul`).

## Main statements

* `Int.even_factorization_natAbs_of_isSquare_mul`: the exponents of a factor of a square.

## Implementation notes

The exponents are those of `Nat.factorization` of the absolute value, as in
`Int.isSquare_iff_nonneg_even_factorization`; at a number `p` that is not prime they are `0`, so
that the statement needs no primality.
-/

@[expose] public section

theorem Int.even_factorization_natAbs_of_isSquare_mul {p : ℕ} {y z : ℤ} (h : IsSquare (y * z))
    (hz : ¬(p : ℤ) ∣ z) : Even (y.natAbs.factorization p) := by
  refine (em p.Prime).elim (fun hp ↦ ?_) fun hp ↦ by
    simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have := (Int.isSquare_iff_nonneg_even_factorization.mp h).2 p hp
  rwa [Int.natAbs_mul, Nat.factorization_mul (natAbs_ne_zero.mpr hy)
    (natAbs_ne_zero.mpr fun h : z = 0 ↦ hz (h ▸ dvd_zero _)), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (n := z.natAbs) (by rwa [← Int.natCast_dvd]),
    add_zero] at this

end
