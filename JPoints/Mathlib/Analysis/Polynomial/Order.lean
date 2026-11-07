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

import JPoints.Mathlib.Algebra.Polynomial.Eval.Coeff
import JPoints.Mathlib.Algebra.Polynomial.Roots
import JPoints.Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# The sign of a real polynomial

Candidates for `Mathlib.Analysis.Polynomial.Order`: a real polynomial without a real root has the
sign of its leading coefficient everywhere, by the signs that `Mathlib.Analysis.Polynomial.Order`
gives beyond every root (`Polynomial.sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot`);
and by the factorisation `p = ∏ (X - a) q` over the roots `a` of `p`, with a `q` without a real
root, the sign of `p` at a point `x` that is not a root is that of its leading coefficient times
`-1` to the number of its roots above `x`, counted with multiplicity
(`Polynomial.sign_eval_eq_sign_leadingCoeff_mul`), and for a squarefree `p`, whose roots are simple,
to the number of its real roots above `x`
(`Polynomial.sign_eval_eq_sign_leadingCoeff_mul_of_squarefree`). A polynomial over `ℚ` negative at
the rational points of an open interval of `ℝ` is at most `0` on its real points
(`Polynomial.eval_map_nonpos_of_forall_ratCast`), by continuity, and negative there when it is
squarefree (`Polynomial.eval_map_neg_of_forall_ratCast`): a real root inside would be a local
maximum, a root of the derivative too. A real quadratic `a t² - b t + c` with values of opposite
signs at two points has a root between them (`exists_quadratic_eq_zero_of_neg_of_pos`,
`exists_quadratic_eq_zero_of_pos_of_neg`), and one with `a > 0` negative at a point has a root on
each side of it (`exists_gt_quadratic_eq_zero_of_neg`, `exists_lt_quadratic_eq_zero_of_neg`).

## Main statements

* `Polynomial.sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot`: the sign without a root.
* `Polynomial.sign_eval_multiset_prod_X_sub_C`: the sign of a product of linear factors.
* `Polynomial.sign_eval_eq_sign_leadingCoeff_mul`,
  `Polynomial.sign_eval_eq_sign_leadingCoeff_mul_of_squarefree`: the sign by the roots above a
  point.
* `Polynomial.eval_map_nonpos_of_forall_ratCast`, `Polynomial.eval_map_neg_of_forall_ratCast`: from
  the rational points of an open interval to its real points.
* `exists_quadratic_eq_zero_of_neg_of_pos`, `exists_quadratic_eq_zero_of_pos_of_neg`,
  `exists_gt_quadratic_eq_zero_of_neg`, `exists_lt_quadratic_eq_zero_of_neg`: the roots of a real
  quadratic.

## Implementation notes

The lemmas are stated over `ℝ`, as the lemmas of `Mathlib.Analysis.Polynomial.Order` that they rest
on are: those need a conditionally complete, densely ordered field. The file imports
`Mathlib.Topology.Algebra.Polynomial`, which `Mathlib.Analysis.Polynomial.Order` imports privately,
for the continuity of polynomials, and for the squarefree case the separability of a squarefree
polynomial over the perfect field `ℝ`.
-/

@[expose] public section

namespace Polynomial

/-- A nonzero real polynomial without a real root has the sign of its leading coefficient
everywhere: by `Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg` and
`Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos`, vacuously beyond every root. -/
theorem sign_eval_eq_sign_leadingCoeff_of_forall_not_isRoot {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ y, ¬p.IsRoot y) (x : ℝ) : SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  have hr (y : ℝ) (hy : p.IsRoot y) : y < x := (h y hy).elim
  rcases (leadingCoeff_ne_zero.mpr hp).lt_or_gt with hlt | hgt
  · rw [sign_neg (eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hr hlt.le), sign_neg hlt]
  · rw [sign_pos (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hr hgt.le), sign_pos hgt]

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
theorem sign_eval_eq_sign_leadingCoeff_mul_of_squarefree {p : ℝ[X]} (hp : Squarefree p) {x : ℝ}
    (hx : ¬p.IsRoot x) :
    SignType.sign (p.eval x) =
      SignType.sign p.leadingCoeff * (-1) ^ {y | x < y ∧ p.IsRoot y}.ncard := by
  rw [sign_eval_eq_sign_leadingCoeff_mul hp.ne_zero hx, card_filter_roots_eq_ncard hp.ne_zero
    (nodup_roots (PerfectField.separable_iff_squarefree.mpr hp)) (x < ·)]

/-- A polynomial over `ℚ` negative at the rational points of the open interval `(L, U)` of `ℝ` is
at most `0` on it: a positive value would be positive on a neighbourhood, which holds a rational
point. -/
theorem eval_map_nonpos_of_forall_ratCast {p : ℚ[X]} {L U : ℝ}
    (h : ∀ q : ℚ, L < q → (q : ℝ) < U → p.eval q < 0) {x : ℝ} (hL : L < x) (hU : x < U) :
    (p.map (algebraMap ℚ ℝ)).eval x ≤ 0 := by
  by_contra! hx
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (continuousAt_const.eventually_lt (p.map (algebraMap ℚ ℝ)).continuous.continuousAt hx)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x := max L (x - ε)) (y := min U (x + ε)) (by
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  have hq := hball (y := q) (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right L (x - ε), min_le_right U (x + ε)])
  rw [eval_ratCast_map, eq_ratCast] at hq
  exact (h q (lt_of_le_of_lt (le_max_left _ _) hq1) (hq2.trans_le (min_le_left _ _))).not_gt
    (mod_cast hq)

/-- A squarefree polynomial over `ℚ` negative at the rational points of the open interval `(L, U)`
of `ℝ` is negative on it: it is at most `0` there
(`Polynomial.eval_map_nonpos_of_forall_ratCast`), so that a real root inside is a local maximum,
where the derivative vanishes, which the separability of a squarefree polynomial rules out. -/
theorem eval_map_neg_of_forall_ratCast {p : ℚ[X]} (hp : Squarefree p) {L U : ℝ}
    (h : ∀ q : ℚ, L < q → (q : ℝ) < U → p.eval q < 0) {x : ℝ} (hL : L < x) (hU : x < U) :
    (p.map (algebraMap ℚ ℝ)).eval x < 0 := by
  refine (eval_map_nonpos_of_forall_ratCast h hL hU).lt_of_ne fun h0 ↦ ?_
  have hmax : IsLocalMax (fun y ↦ (p.map (algebraMap ℚ ℝ)).eval y) x :=
    Filter.mem_of_superset (Ioo_mem_nhds hL hU) fun y hy ↦ by
      simpa [h0] using eval_map_nonpos_of_forall_ratCast h hy.1 hy.2
  have hd := hmax.deriv_eq_zero
  rw [Polynomial.deriv] at hd
  exact (PerfectField.separable_iff_squarefree.mpr hp).map.eval_derivative_ne_zero h0 hd

end Polynomial

/-! ### Real quadratics -/

/-- A real quadratic `a t² - b t + c` negative at `l` and positive at `h > l` has a root between
them, by the intermediate value theorem. -/
theorem exists_quadratic_eq_zero_of_neg_of_pos {a b c l h : ℝ} (hlh : l < h)
    (hl : a * l ^ 2 - b * l + c < 0) (hh : 0 < a * h ^ 2 - b * h + c) :
    ∃ x, l < x ∧ x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo hlh.le
    (by fun_prop : Continuous fun t : ℝ ↦ a * t ^ 2 - b * t + c).continuousOn ⟨hl, hh⟩
  exact ⟨x, h1, h2, h3⟩

/-- A real quadratic `a t² - b t + c` positive at `l` and negative at `h > l` has a root between
them, by the intermediate value theorem. -/
theorem exists_quadratic_eq_zero_of_pos_of_neg {a b c l h : ℝ} (hlh : l < h)
    (hl : 0 < a * l ^ 2 - b * l + c) (hh : a * h ^ 2 - b * h + c < 0) :
    ∃ x, l < x ∧ x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' hlh.le
    (by fun_prop : Continuous fun t : ℝ ↦ a * t ^ 2 - b * t + c).continuousOn ⟨hh, hl⟩
  exact ⟨x, h1, h2, h3⟩

-- `a t² - b t + c`, `a > 0`, is positive at `T ≥ 1` with `|b| + |c| + a ≤ a T`.
private theorem quadratic_pos_of_le_mul {a b c T : ℝ} (ha : 0 < a) (hT1 : 1 ≤ T)
    (hT : |b| + |c| + a ≤ a * T) : 0 < a * T ^ 2 - b * T + c := by
  nlinarith [mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℝ) ≤ T),
    mul_le_mul_of_nonneg_left hT1 (abs_nonneg c), le_abs_self b, neg_abs_le c,
    mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith : (0 : ℝ) ≤ T)]

/-- A real quadratic `a t² - b t + c`, `a > 0`, negative at `l` has a root above `l`: it is positive
at `max l 0 + (|b| + |c| + a) / a`. -/
theorem exists_gt_quadratic_eq_zero_of_neg {a b c l : ℝ} (ha : 0 < a)
    (hl : a * l ^ 2 - b * l + c < 0) :
    ∃ x, l < x ∧ a * x ^ 2 - b * x + c = 0 := by
  have hq := div_mul_cancel₀ (|b| + |c| + a) ha.ne'
  have hq1 : 1 ≤ (|b| + |c| + a) / a :=
    (one_le_div ha).mpr (by linarith [abs_nonneg b, abs_nonneg c])
  have hm := mul_nonneg ha.le (le_max_right l 0)
  obtain ⟨x, h1, -, h3⟩ :=
    exists_quadratic_eq_zero_of_neg_of_pos (h := max l 0 + (|b| + |c| + a) / a)
    (by linarith [le_max_left l 0]) hl
    (quadratic_pos_of_le_mul ha (by linarith [le_max_right l 0]) (by nlinarith))
  exact ⟨x, h1, h3⟩

/-- A real quadratic `a t² - b t + c`, `a > 0`, negative at `h` has a root below `h`: the root above
`-h` of `a t² + b t + c` (`exists_gt_quadratic_eq_zero_of_neg`), negated. -/
theorem exists_lt_quadratic_eq_zero_of_neg {a b c h : ℝ} (ha : 0 < a)
    (hh : a * h ^ 2 - b * h + c < 0) :
    ∃ x, x < h ∧ a * x ^ 2 - b * x + c = 0 := by
  obtain ⟨x, hx, e⟩ := exists_gt_quadratic_eq_zero_of_neg (b := -b) (l := -h) ha (by linarith)
  exact ⟨-x, by linarith, by linarith⟩

end
