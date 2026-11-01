/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The value of the cast of an integer to `ZMod n`

A candidate for `Mathlib.Data.ZMod.Basic`, next to `ZMod.val_intCast`, which gives the value in
`ℤ`: the value of the cast of `x` is the natural number `(x % n).toNat`
(`ZMod.val_intCast_eq_toNat_emod`), the form of `Fin.val_intCast` for `ZMod n`.
-/

@[expose] public section

theorem ZMod.val_intCast_eq_toNat_emod {n : ℕ} [NeZero n] (x : ℤ) :
    (x : ZMod n).val = (x % n).toNat := by
  rw [← Int.natCast_inj, ZMod.val_intCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by simp [NeZero.ne n]))]

end
