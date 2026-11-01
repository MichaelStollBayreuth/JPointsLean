/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Sqrt

/-!
# The square test by the integer square root

A candidate for `Mathlib.Data.Int.Sqrt`, next to `Int.exists_mul_self`: an integer is a square
exactly when its integer square root squares to it (`Int.isSquare_iff_sqrt_mul_sqrt`), the form of
`Int.exists_mul_self` with `IsSquare`.

## Implementation notes

The statement needs `IsSquare` (`Mathlib.Algebra.Group.Even`), which `Mathlib.Data.Int.Sqrt` does
not import.
-/

@[expose] public section

theorem Int.isSquare_iff_sqrt_mul_sqrt (n : ℤ) : IsSquare n ↔ Int.sqrt n * Int.sqrt n = n := by
  rw [← Int.exists_mul_self]
  exact ⟨fun ⟨r, h⟩ ↦ ⟨r, h.symm⟩, fun ⟨r, h⟩ ↦ ⟨r, h.symm⟩⟩

end
