/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Data.Set.Card

import JPoints.Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Algebra.Polynomial

/-!
# The sign of a real polynomial

Candidates for `Mathlib.Analysis.Polynomial.Order`: over a linearly ordered normed field with the
order topology, such as `ℝ`, a nonzero polynomial has, far right, the sign of its leading
coefficient (`Polynomial.eventually_atTop_sign_eval`); by the intermediate value theorem, opposite
signs of a real polynomial at two points give a root between them
(`Polynomial.exists_isRoot_of_eval_mul_eval_neg`), so that a real polynomial without a real root
has the sign of its leading coefficient everywhere
(`Polynomial.sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot`); and by the factorisation
`p = ∏ (X - a) q` over the roots `a` of `p`, with a `q` without a real root, the sign of `p` at a
point `x` that is not a root is that of its leading coefficient times `-1` to the number of its
roots above `x`, counted with multiplicity (`Polynomial.sign_eval_eq_sign_leadingCoeff_mul`), and
for a squarefree `p`, whose roots are simple, to the number of its real roots above `x`
(`Polynomial.sign_eval_eq_of_squarefree`).

## Main statements

* `Polynomial.eventually_atTop_sign_eval`: the sign far right.
* `Polynomial.exists_isRoot_of_eval_mul_eval_neg`: a root between values of opposite signs.
* `Polynomial.sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot`: the sign without a root.
* `Polynomial.sign_eval_multiset_prod_X_sub_C`: the sign of a product of linear factors.
* `Polynomial.sign_eval_eq_sign_leadingCoeff_mul`, `Polynomial.sign_eval_eq_of_squarefree`: the
  sign by the roots above a point.

## Implementation notes

The lemmas that rest on the intermediate value theorem are stated over `ℝ`, as those of the
sibling are: they need a conditionally complete, densely ordered field. The file imports the
sibling's private import `Mathlib.Topology.Algebra.Polynomial` for the continuity of polynomials,
and for the squarefree case the separability of a squarefree polynomial over the perfect field
`ℝ`.

## References

`Polynomial.eventually_atTop_sign_eval` and `Polynomial.exists_isRoot_of_eval_mul_eval_neg` are
adapted from `Ratpoints/Mathlib/Analysis/Polynomial/Order.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

open Filter

namespace Polynomial

section OrderTopology

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]

/-- Far right, a nonzero polynomial has the sign of its leading coefficient. -/
theorem eventually_atTop_sign_eval {p : 𝕜[X]} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  by_cases hd : p.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hd]
    simp
  have hd' : 0 < p.degree := not_le.mp hd
  rcases (leadingCoeff_ne_zero.mpr hp).lt_or_gt with hlt | hgt
  · filter_upwards [(tendsto_atBot_of_leadingCoeff_nonpos p hd' hlt.le).eventually_lt_atBot 0]
      with x hx
    rw [sign_neg hx, sign_neg hlt]
  · filter_upwards [(tendsto_atTop_of_leadingCoeff_nonneg p hd' hgt.le).eventually_gt_atTop 0]
      with x hx
    rw [sign_pos hx, sign_pos hgt]

end OrderTopology

/-- A real polynomial with values of opposite signs at `a < b` has a root strictly between. -/
theorem exists_isRoot_of_eval_mul_eval_neg {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ z ∈ Set.Ioo a b, p.IsRoot z := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨hb, ha⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨ha, hb⟩

/-- A nonzero real polynomial without a real root has the sign of its leading coefficient
everywhere: by the intermediate value theorem, it has the sign that it has far right. -/
theorem sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ y, ¬p.IsRoot y) (x : ℝ) : SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  obtain ⟨y, hy, hxy⟩ := ((eventually_atTop_sign_eval hp).and (eventually_gt_atTop x)).exists
  rw [← hy]
  by_contra hne
  have hx : p.eval x ≠ 0 := h x
  have hy0 : p.eval y ≠ 0 := h y
  obtain ⟨z, -, hz⟩ := exists_isRoot_of_eval_mul_eval_neg (p := p) hxy (by
    rcases hx.lt_or_gt with hx | hx <;> rcases hy0.lt_or_gt with hy' | hy' <;>
      simp_all [sign_neg, sign_pos, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg])
  exact h z hz

/-- The sign of `∏ (x - a)` over a multiset of reals that does not contain `x` is `-1` to the
number of its elements above `x`. -/
theorem sign_eval_multiset_prod_X_sub_C {s : Multiset ℝ} {x : ℝ} (hx : x ∉ s) :
    SignType.sign ((s.map fun a ↦ X - C a).prod.eval x) = (-1) ^ (s.filter (x < ·)).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hx
    rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, sign_mul, ih hx.2, Multiset.filter_cons]
    rcases lt_or_gt_of_ne hx.1 with h | h
    · simp [h, sign_neg (sub_neg.mpr h), pow_succ, mul_comm]
    · simp [h.not_gt, sign_pos (sub_pos.mpr h)]

/-- The sign of a nonzero real polynomial `p` at a point `x` that is not a root: the sign of its
leading coefficient, times `-1` to the number of its roots above `x`, counted with multiplicity.
By the factorisation `p = ∏ (X - a) q` over its roots, with a `q` without a real root. -/
theorem sign_eval_eq_sign_leadingCoeff_mul {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ} (hx : ¬p.IsRoot x) :
    SignType.sign (p.eval x) =
      SignType.sign p.leadingCoeff * (-1) ^ (p.roots.filter (x < ·)).card := by
  obtain ⟨q, hq, -, hq0⟩ := exists_prod_multiset_X_sub_C_mul p
  have hm := monic_multiset_prod_of_monic p.roots (fun a ↦ X - C a) fun a _ ↦ monic_X_sub_C a
  have hq' : q ≠ 0 := by
    rintro rfl
    exact hp (by rw [← hq, mul_zero])
  have hroot (y : ℝ) : ¬q.IsRoot y := fun hy ↦ by simpa [hq0] using (mem_roots hq').mpr hy
  have hlc : p.leadingCoeff = q.leadingCoeff := by
    rw [← hq, leadingCoeff_mul, hm.leadingCoeff, one_mul]
  rw [← hq, eval_mul, sign_mul, sign_eval_multiset_prod_X_sub_C fun h ↦ hx ((mem_roots hp).mp h),
    sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot hq' hroot, ← hlc, hq, mul_comm]

/-- The sign of a squarefree real polynomial at a point that is not a root: that of its leading
coefficient, times `-1` to the number of the real roots above the point. -/
theorem sign_eval_eq_of_squarefree {p : ℝ[X]} (hp : Squarefree p) {x : ℝ} (hx : ¬p.IsRoot x) :
    SignType.sign (p.eval x) =
      SignType.sign p.leadingCoeff * (-1) ^ {y | x < y ∧ p.IsRoot y}.ncard := by
  rw [sign_eval_eq_sign_leadingCoeff_mul hp.ne_zero hx, card_filter_roots_eq_ncard hp.ne_zero
    (nodup_roots (PerfectField.separable_iff_squarefree.mpr hp)) (x < ·)]

end Polynomial

end
