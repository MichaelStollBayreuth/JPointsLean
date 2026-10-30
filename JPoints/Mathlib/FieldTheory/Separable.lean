/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# The derivative of a separable polynomial at a root

A candidate for `Mathlib.FieldTheory.Separable`: the derivative of a separable polynomial does not
vanish at a root (`Polynomial.Separable.eval_derivative_ne_zero`), the form with `eval` of
`Polynomial.Separable.eval₂_derivative_ne_zero` and `Polynomial.Separable.aeval_derivative_ne_zero`.
-/

@[expose] public section

namespace Polynomial

theorem Separable.eval_derivative_ne_zero {R : Type*} [CommSemiring R] [Nontrivial R] {p : R[X]}
    (h : p.Separable) {x : R} (hx : p.eval x = 0) :
    (derivative p).eval x ≠ 0 :=
  h.eval₂_derivative_ne_zero (RingHom.id R) hx

end Polynomial

end
