/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Powers by the quotient and the remainder of the exponent

A candidate for `Mathlib.Algebra.Group.Defs`, next to `pow_mul` and `pow_add`: in a monoid,
`b ^ (n % k) * (b ^ k) ^ (n / k) = b ^ n`, the power of `Nat.mod_add_div`, which the steps of
binary exponentiation (`k = 2`) use.

## Main statements

* `pow_mod_mul_pow_pow_div`: the power by the remainder times the power of `b ^ k` by the quotient.
-/

@[expose] public section

theorem pow_mod_mul_pow_pow_div {M : Type*} [Monoid M] (b : M) (n k : ℕ) :
    b ^ (n % k) * (b ^ k) ^ (n / k) = b ^ n := by
  rw [← pow_mul, ← pow_add, Nat.mod_add_div]

end
