/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Perfect

/-!
# Squarefree polynomials over a perfect field under a map

A candidate for `Mathlib.FieldTheory.Perfect`, next to `PerfectField.separable_iff_squarefree`: the
image of a squarefree polynomial over a perfect field under a map of rings is squarefree
(`Polynomial.squarefree_map_of_squarefree`), since the polynomial is separable.
-/

@[expose] public section

open Polynomial

/-- The image of a squarefree polynomial over a perfect field under a map of rings is squarefree,
since the polynomial is separable (`PerfectField.separable_iff_squarefree`). -/
theorem Polynomial.squarefree_map_of_squarefree {K L : Type*} [Field K] [PerfectField K]
    [CommSemiring L] (φ : K →+* L) {f : K[X]} (hf : Squarefree f) : Squarefree (f.map φ) :=
  (PerfectField.separable_iff_squarefree.mpr hf).map.squarefree

end
