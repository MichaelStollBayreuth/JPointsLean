/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Ring.Rat

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
# A rational number is at most its numerator in absolute value

A candidate for `Mathlib.Algebra.Order.Ring.Rat`, next to `Rat.abs_def`: `|q| ≤ |q.num|`,
as `q = q.num / q.den` with `q.den ≥ 1`.

## Main statements

* `Rat.abs_le_abs_num`: `|q| ≤ |q.num|`.
-/

@[expose] public section

namespace Rat

theorem abs_le_abs_num (q : ℚ) : |q| ≤ |(q.num : ℚ)| := by
  conv_lhs => rw [← num_div_den q]
  rw [abs_div, Nat.abs_cast]
  exact div_le_self (abs_nonneg _) (mod_cast q.den_pos)

end Rat

end
