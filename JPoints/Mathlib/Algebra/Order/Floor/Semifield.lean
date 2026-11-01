/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The ceiling of a half

A candidate for `Mathlib.Algebra.Order.Floor.Semifield`, next to `Nat.ceil_lt_two_mul`: the ceiling
of `w / 2` is below that of `w` for `w > 1` (`Nat.ceil_div_two_lt_ceil`), the measure of a loop
that halves an interval.
-/

@[expose] public section

theorem Nat.ceil_div_two_lt_ceil {K : Type*} [Field K] [LinearOrder K] [IsOrderedRing K]
    [FloorSemiring K] {w : K} (h : 1 < w) : ⌈w / 2⌉₊ < ⌈w⌉₊ :=
  Nat.cast_lt.mp ((Nat.ceil_lt_two_mul (by linarith)).trans_le
    (by rw [mul_div_cancel₀ _ two_ne_zero]; exact Nat.le_ceil w))

end
