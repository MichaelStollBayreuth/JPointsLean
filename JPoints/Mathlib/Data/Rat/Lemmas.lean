/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Rat.Lemmas

import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Int.Cast.Field

/-!
# The numerator and the denominator of a quotient of integers

Candidates for `Mathlib.Data.Rat.Lemmas`, next to `Rat.num_div_eq_of_coprime` and
`Rat.den_div_eq_of_coprime`, which have a positive denominator: for coprime `a` and `b < 0` the
numerator of `a / b` is `-a` and its denominator `-b` (`Rat.num_div_eq_neg_of_coprime`,
`Rat.den_div_eq_neg_of_coprime`), and the quotient of `a` and `b` by their gcd is `a / b`
(`Rat.intCast_ediv_gcd_div_intCast_ediv_gcd`).

## Main statements

* `Rat.num_div_eq_neg_of_coprime`, `Rat.den_div_eq_neg_of_coprime`: a negative denominator.
* `Rat.intCast_ediv_gcd_div_intCast_ediv_gcd`: the reduction of a quotient by the gcd.

## Implementation notes

The proof of `Rat.intCast_ediv_gcd_div_intCast_ediv_gcd` computes in the field `ℚ`
(`Mathlib.Algebra.Field.Rat`), which `Mathlib.Data.Rat.Lemmas` does not import.
-/

@[expose] public section

namespace Rat

theorem num_div_eq_neg_of_coprime {a b : ℤ} (hb0 : b < 0) (h : Nat.Coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = -a := by
  have hc : Nat.Coprime (-a).natAbs (-b).natAbs := by rwa [Int.natAbs_neg, Int.natAbs_neg]
  rw [← neg_div_neg_eq, ← Int.cast_neg, ← Int.cast_neg, num_div_eq_of_coprime (by lia) hc]

theorem den_div_eq_neg_of_coprime {a b : ℤ} (hb0 : b < 0) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = -b := by
  have hc : Nat.Coprime (-a).natAbs (-b).natAbs := by rwa [Int.natAbs_neg, Int.natAbs_neg]
  rw [← neg_div_neg_eq, ← Int.cast_neg, ← Int.cast_neg, den_div_eq_of_coprime (by lia) hc]

theorem intCast_ediv_gcd_div_intCast_ediv_gcd (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    ((a / (a.gcd b : ℤ) : ℤ) : ℚ) / ((b / (a.gcd b : ℤ) : ℤ) : ℚ) = a / b := by
  have hg : ((Int.gcd a b : ℤ) : ℚ) ≠ 0 := mod_cast (Int.gcd_pos_of_ne_zero_right a hb).ne'
  rw [Int.cast_div (Int.gcd_dvd_left ..) hg, Int.cast_div (Int.gcd_dvd_right ..) hg,
    div_div_div_cancel_right₀ hg]

end Rat

end
