/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree elements under multiplicative equivalences

A candidate for `Mathlib.Algebra.Squarefree.Basic`, next to `Associated.squarefree_iff`: a
multiplicative equivalence keeps squarefree elements squarefree (`MulEquiv.squarefree_iff`), as
`MulEquiv.irreducible_iff` keeps irreducible ones irreducible.
-/

@[expose] public section

theorem MulEquiv.squarefree_iff {F M N : Type*} [Monoid M] [Monoid N] [EquivLike F M N]
    [MulEquivClass F M N] (f : F) {x : M} : Squarefree (f x) ↔ Squarefree x := by
  simp [Squarefree, (EquivLike.surjective f).forall, ← map_mul, map_dvd_iff]

end
