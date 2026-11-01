/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Card

/-!
# Counting roots with a property

Candidates for `Mathlib.Algebra.Polynomial.Roots`: the roots of a nonzero polynomial with a
property `P` number at most its degree (`Polynomial.ncard_setOf_isRoot_le_natDegree`), and, when
the roots are simple, they are counted by the multiset of the roots
(`Polynomial.card_filter_roots_eq_ncard`).

## Main statements

* `Polynomial.ncard_setOf_isRoot_le_natDegree`: at most `deg p` roots with a property.
* `Polynomial.card_filter_roots_eq_ncard`: the roots with a property of a polynomial without
  multiple roots, by the multiset of the roots.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}

theorem ncard_setOf_isRoot_le_natDegree (hp : p ≠ 0) (P : R → Prop) :
    {y | P y ∧ p.IsRoot y}.ncard ≤ p.natDegree := by
  classical
  refine (Set.ncard_le_ncard (t := (p.roots.toFinset : Set R)) (fun y hy ↦ ?_)
    (Finset.finite_toSet _)).trans ?_
  · simpa [mem_roots hp] using hy.2
  · rw [Set.ncard_coe_finset]
    exact p.roots.toFinset_card_le.trans (card_roots' p)

/-- For a nonzero polynomial without multiple roots, the number of its roots with the property `P`,
counted with multiplicity, is the number of the roots with `P`. -/
theorem card_filter_roots_eq_ncard (hp : p ≠ 0) (hn : p.roots.Nodup) (P : R → Prop)
    [DecidablePred P] : (p.roots.filter P).card = {y | P y ∧ p.IsRoot y}.ncard := by
  classical
  rw [← Multiset.toFinset_card_of_nodup (hn.filter _), ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [mem_roots hp, and_comm]

end Polynomial

end
