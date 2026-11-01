/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.GCD

import Mathlib.Data.Int.Basic

/-!
# The gcd of integers and their odd parts

Candidates for `Mathlib.Data.Int.GCD`: the factors `2` of an integer do not change its gcd with an
odd integer (`Int.gcd_two_pow_mul_of_emod_two_eq_one`), so that the gcd of two integers, or of
three, one of them odd, is that of their odd parts (`Int.gcd_eq_gcd_of_two_pow_mul_eq`,
`Int.gcd_gcd_eq_of_two_pow_mul_eq`), and a divisor of an odd integer is odd
(`Int.emod_two_eq_one_of_dvd`, the form for `ℤ` of `Odd.of_dvd_nat`).

## Implementation notes

The statements need only the gcd of core; the proofs reduce modulo `2` by `Int.gcd_emod` of
`Mathlib.Data.Int.Basic`.

## Main statements

* `Int.gcd_two_pow_mul_of_emod_two_eq_one`, `Int.gcd_gcd_two_pow_mul_of_emod_two_eq_one`: the
  factors `2` and the gcd with an odd integer.
* `Int.gcd_eq_gcd_of_two_pow_mul_eq`, `Int.gcd_gcd_eq_of_two_pow_mul_eq`: the gcd of two and of
  three integers, one of them odd, from their odd parts.
* `Int.emod_two_eq_one_of_dvd`: a divisor of an odd integer is odd.
-/

@[expose] public section

/-- The factors `2` of `2 ^ t y` do not change its gcd with an odd `m`. -/
theorem Int.gcd_two_pow_mul_of_emod_two_eq_one {m : ℤ} (hm : m % 2 = 1) (t : ℕ) (y : ℤ) :
    Int.gcd (2 ^ t * y) m = Int.gcd y m := by
  refine Int.gcd_mul_right_left_of_gcd_eq_one (Int.gcd_pow_left_of_gcd_eq_one ?_)
  rw [Int.gcd_comm, ← Int.gcd_emod, hm]
  rfl

/-- The gcd of two integers, one of them odd, is that of their odd parts. -/
theorem Int.gcd_eq_gcd_of_two_pow_mul_eq {n m n' m' : ℤ} {s t : ℕ} (hn : 2 ^ s * n' = n)
    (hm : 2 ^ t * m' = m) (hn' : n' % 2 = 1) (hm' : m' % 2 = 1) (h : n % 2 = 1 ∨ m % 2 = 1) :
    Int.gcd n m = Int.gcd n' m' := by
  subst hn hm
  rcases h with h | h
  · rw [Int.gcd_comm, Int.gcd_two_pow_mul_of_emod_two_eq_one h, Int.gcd_comm,
      Int.gcd_two_pow_mul_of_emod_two_eq_one hm']
  · rw [Int.gcd_two_pow_mul_of_emod_two_eq_one h, Int.gcd_comm,
      Int.gcd_two_pow_mul_of_emod_two_eq_one hn', Int.gcd_comm]

/-- A divisor of an odd integer is odd. -/
theorem Int.emod_two_eq_one_of_dvd {d m : ℤ} (hd : d ∣ m) (hm : m % 2 = 1) :
    d % 2 = 1 := by
  rcases Int.emod_two_eq_zero_or_one d with h | h
  · have := Int.emod_eq_zero_of_dvd (Int.dvd_trans (Int.dvd_of_emod_eq_zero h) hd)
    lia
  · exact h

/-- The factors `2` of two integers do not change the gcd of their gcd with an odd `m`. -/
theorem Int.gcd_gcd_two_pow_mul_of_emod_two_eq_one {m : ℤ} (hm : m % 2 = 1) (r s : ℕ)
    (x y : ℤ) : Int.gcd (Int.gcd (2 ^ r * x) (2 ^ s * y)) m = Int.gcd (Int.gcd x y) m := by
  rw [Int.gcd_assoc, Int.gcd_two_pow_mul_of_emod_two_eq_one hm,
    Int.gcd_two_pow_mul_of_emod_two_eq_one (Int.emod_two_eq_one_of_dvd (Int.gcd_dvd_right ..) hm),
    ← Int.gcd_assoc]

private theorem gcd_gcd_eq_of_left {a' b' c' : ℤ} {r s t : ℕ} (hb' : b' % 2 = 1)
    (h : 2 ^ r * a' % 2 = 1) :
    Int.gcd (Int.gcd (2 ^ r * a') (2 ^ s * b')) (2 ^ t * c') = Int.gcd (Int.gcd a' b') c' := by
  rw [Int.gcd_assoc, Int.gcd_comm, Int.gcd_gcd_two_pow_mul_of_emod_two_eq_one h, Int.gcd_comm,
    Int.gcd_two_pow_mul_of_emod_two_eq_one
      (Int.emod_two_eq_one_of_dvd (Int.gcd_dvd_left ..) hb'), ← Int.gcd_assoc]

/-- The gcd of three integers, not all even, is that of their odd parts: the odd one makes every
common divisor odd. -/
theorem Int.gcd_gcd_eq_of_two_pow_mul_eq {a b c a' b' c' : ℤ} {r s t : ℕ}
    (ha : 2 ^ r * a' = a) (hb : 2 ^ s * b' = b) (hc : 2 ^ t * c' = c) (ha' : a' % 2 = 1)
    (hb' : b' % 2 = 1) (h : a % 2 = 1 ∨ b % 2 = 1 ∨ c % 2 = 1) :
    Int.gcd (Int.gcd a b) c = Int.gcd (Int.gcd a' b') c' := by
  subst ha hb hc
  rcases h with h | h | h
  · exact gcd_gcd_eq_of_left hb' h
  · rw [Int.gcd_comm (2 ^ r * a'), gcd_gcd_eq_of_left ha' h, Int.gcd_comm b']
  · rw [Int.gcd_gcd_two_pow_mul_of_emod_two_eq_one h, Int.gcd_comm,
      Int.gcd_two_pow_mul_of_emod_two_eq_one (Int.emod_two_eq_one_of_dvd (Int.gcd_dvd_left ..) ha'),
      Int.gcd_comm]

end
