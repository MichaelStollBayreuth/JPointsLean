/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.Algebra.Squarefree.Basic

import JPoints.Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree polynomials under `Polynomial.mirror` and `Polynomial.reverse`

Candidates for `Mathlib.Algebra.Polynomial.Mirror`: over a semiring without zero divisors,
`Polynomial.mirror` is a multiplicative involution, so that it keeps squarefree polynomials
squarefree (`Polynomial.squarefree_mirror_iff`), and so does `Polynomial.reverse`, a factor of the
mirror (`Squarefree.reverse`).
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R] [NoZeroDivisors R] {p : R[X]}

theorem squarefree_mirror_iff : Squarefree p.mirror ↔ Squarefree p :=
  MulEquiv.squarefree_iff (MulEquiv.mk (mirror_involutive.toPerm _) (mirror_mul_of_domain · ·))

theorem _root_.Squarefree.reverse (h : Squarefree p) : Squarefree p.reverse :=
  (squarefree_mirror_iff.mpr h).squarefree_of_dvd (dvd_mul_right _ _)

end Polynomial

end
