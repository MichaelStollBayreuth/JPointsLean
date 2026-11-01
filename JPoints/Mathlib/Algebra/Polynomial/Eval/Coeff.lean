/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Rat.Cast.Defs

/-!
# The value of the image of a polynomial at a rational number

A candidate for `Mathlib.Algebra.Polynomial.Eval.Coeff`, next to `Polynomial.eval_natCast_map` and
`Polynomial.eval_intCast_map`: the image of a polynomial under a map of division rings takes at a
rational number the image of the value (`Polynomial.eval_ratCast_map`).
-/

@[expose] public section

open Polynomial

theorem Polynomial.eval_ratCast_map {R S : Type*} [DivisionRing R] [DivisionRing S] (f : R →+* S)
    (p : R[X]) (q : ℚ) : (p.map f).eval (q : S) = f (p.eval q) := by
  rw [eval_map, ← map_ratCast f, eval₂_at_apply]

end
