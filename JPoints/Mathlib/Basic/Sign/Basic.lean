/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Rat.Cast.Order

/-!
# The sign of a rational number in an ordered field

A candidate for `Mathlib.Basic.Sign.Basic`, next to `sign_intCast`: the sign of the cast of a
rational number to an ordered field is its sign (`sign_ratCast`).

## Implementation notes

The statement needs the casts of rational numbers to an ordered field
(`Mathlib.Data.Rat.Cast.Order`), which `Mathlib.Basic.Sign.Basic` does not import.
-/

@[expose] public section

@[simp]
theorem sign_ratCast {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (q : ℚ) :
    SignType.sign (q : K) = SignType.sign q := by
  simp only [sign_apply, Rat.cast_pos, Rat.cast_lt_zero]

end
