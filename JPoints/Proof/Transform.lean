/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Kummer
public import Mathlib.Algebra.Polynomial.Reverse

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.Algebra.Polynomial.Mirror
import JPoints.Mathlib.Algebra.Squarefree.Basic
import JPoints.Proof.Poly
import JPoints.Proof.Reference
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination

/-!
# The curve searched and the points taken back

The program searches the curve of `JPoints.searchedCoeffs` and takes its points back to the curve
given by `JPoints.backPoint`; this file shows that the points so taken back are exactly the points
of the curve given (`JPoints.isPoint_backPoint_iff`), and that the curve searched is one that the
program does not refuse when the curve given is not.

* The curve searched has at most seven coefficients (`JPoints.length_searchedCoeffs_le`), the
  degree `5` after a reversal and the degree of the curve given otherwise
  (`JPoints.degree_searchedCoeffs`), and is squarefree when the curve given is
  (`JPoints.squarefree_poly_searchedCoeffs`): its polynomial is the reverse of the polynomial given
  (`JPoints.poly_map_reverse_range`) or the polynomial given at `-x`
  (`JPoints.poly_map_range_neg_one_pow_mul`), or both, and both transformations keep squarefree
  polynomials squarefree (`Squarefree.reverse`, `Squarefree.map`).
* The Kummer equation and the lifting test do not see the sign of a point (`JPoints.kummer_neg`,
  `JPoints.lifts_neg_iff`) and follow the negation `x ↦ -x` of the curve, which negates the second
  coordinate (`JPoints.kummer_eq_of_negated`, `JPoints.lifts_iff_of_negated`), and its reversal
  `x ↦ 1 / x`, which exchanges the first and the third (`JPoints.kummer_eq_of_reversed`,
  `JPoints.lifts_iff_of_reversed`).
* The map back keeps the normalization (`JPoints.isNormalized_of_backPoint_eq`,
  `JPoints.isNormalized_backPoint`) and the bounds (`JPoints.inBounds_iff_of_backPoint_eq`), and is
  its own inverse on normalized points (`JPoints.backPoint_backPoint`), so that it is injective on
  them (`JPoints.injOn_backPoint`).

## Main statements

* `JPoints.length_searchedCoeffs_le`, `JPoints.degree_searchedCoeffs`,
  `JPoints.squarefree_poly_searchedCoeffs`: the curve searched.
* `JPoints.lifts_iff_of_reversed`: the lifting test of a curve and that of its reversal, across
  the charts.
* `JPoints.isPoint_backPoint_iff`: a normalized point of the curve searched is a point exactly when
  its image on the curve given is.
* `JPoints.backPoint_backPoint`, `JPoints.injOn_backPoint`: the map back is an involution on the
  normalized points, and injective on them.

## Implementation notes

The lifting test (`JPoints.Lifts`) is a condition in the chart `a ≠ 0` and, for `a = 0`, in the
charts at infinity, so that the reversal, which exchanges `a` and `c`, compares different charts.
For `a, c ≠ 0` the square roots `α`, `β` of `A₂` and `B₂` with `C = 2 α β`
(`JPoints.exists_sq_auxA2_auxB2`) give square roots of `a⁴ A₂'` and `a² B₂'` for the reversed curve,
by the identities `JPoints.pow_four_mul_auxA2_eq_of_reversed` and
`JPoints.sq_mul_auxB2_eq_of_reversed`: the coefficients `v₁, v₀` of the Mumford representation
transform linearly (`JPoints.isSquare_auxA2_of_reversed`). For `c = 0` the point has the root `0` of
`u`, and `a² F(b, a)` is the square `(a b α + a² β)²` (`JPoints.sq_mul_sexticForm_eq`). For `a = 0`
the identities `JPoints.kummer_zero_eq_of_reversed` and
`JPoints.sexticForm_eq_sq_mul_auxA2_of_reversed` give the square `A₂'` of the reversed curve from
`f₆` or, for `f₆ = 0`, from `F(c, b)`; this needs `f₅ ≠ 0` or `f₆ ≠ 0`, the degree at least `5`.
-/

@[expose] public section

namespace JPoints

/-! ### The coefficients of the curve searched -/

section Polynomial

open Polynomial

private theorem getD_map_reverse_range (cs : List ℤ) {k : ℕ} (hk : k < 7) :
    ((List.range 7).reverse.map (cs.getD · 0)).getD k 0 = cs.getD (6 - k) 0 := by
  simp [List.getD_eq_getElem?_getD, hk]

private theorem getD_map_range_neg_one_pow_mul (cs : List ℤ) {k : ℕ} (hk : k < 7) :
    ((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0).getD k 0 = (-1) ^ k * cs.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, hk]

private theorem degree_map_range_neg_one_pow_mul {cs : List ℤ} (h : cs.length ≤ 7) :
    degree ((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0) = degree cs :=
  degree_eq_of_getD_eq_zero_iff fun i ↦ by
    rcases lt_or_ge i 7 with hi | hi
    · rw [getD_map_range_neg_one_pow_mul cs hi]
      simp
    · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by lia)]

/-- The seven coefficients of a curve with `f₀ = 0 ≠ f₁`, reversed, have the degree `5`. -/
private theorem degree_map_reverse_range {cs : List ℤ} (h0 : cs.getD 0 0 = 0)
    (h1 : |cs.getD 1 0| = 1) :
    degree ((List.range 7).reverse.map (cs.getD · 0)) = 5 := by
  refine degree_eq_of_getD_ne_zero ?_ fun i hi ↦ ?_
  · rw [getD_map_reverse_range cs (by decide)]
    exact abs_pos.mp (h1 ▸ one_pos)
  obtain rfl | hi : i = 6 ∨ 7 ≤ i := by lia
  · rwa [getD_map_reverse_range cs (by decide)]
  · exact List.getD_eq_default _ _ (by simpa using hi)

theorem poly_map_reverse_range {cs : List ℤ} (h7 : cs.length ≤ 7) (h6 : degree cs = 6) :
    poly ((List.range 7).reverse.map (cs.getD · 0)) = (poly cs).reverse := by
  ext i
  rw [coeff_reverse, natDegree_poly, h6, coeff_poly, coeff_poly]
  rcases le_or_gt i 6 with hi | hi
  · rw [revAt_le hi, getD_map_reverse_range cs (by lia)]
  · rw [revAt_eq_self_of_lt hi, List.getD_eq_default _ _ (by simp; lia),
      List.getD_eq_default _ _ (by lia)]

theorem poly_map_range_neg_one_pow_mul {cs : List ℤ} (h7 : cs.length ≤ 7) :
    poly ((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0) = (poly cs).comp (-X) := by
  refine Polynomial.funext fun x ↦ ?_
  rw [eval_comp, eval_neg, eval_X, eval_poly (n := 7) (by simp) x, eval_poly h7 (-x)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_map_range_neg_one_pow_mul cs (Finset.mem_range.mp hi), neg_pow]
  push_cast
  ring

private theorem squarefree_poly_map_range_neg_one_pow_mul {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h : Squarefree (poly cs)) :
    Squarefree (poly ((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0)) := by
  rw [poly_map_range_neg_one_pow_mul h7, comp_eq_aeval, ← algEquivAevalNegX_apply]
  exact h.map _

private theorem squarefree_poly_map_reverse_range {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h6 : degree cs = 6)
    (h : Squarefree (poly cs)) : Squarefree (poly ((List.range 7).reverse.map (cs.getD · 0))) :=
  poly_map_reverse_range h7 h6 ▸ h.reverse

end Polynomial

/-- The curve searched by the cases of its definition, with the condition of the negation of a
reversed sextic in terms of the curve given: `f₁ = -1`. -/
theorem searchedCoeffs_eq (cs : List ℤ) :
    searchedCoeffs cs = if degree cs = 6 ∧ cs.getD 0 0 = 0 ∧ |cs.getD 1 0| = 1 then
      (if cs.getD 1 0 = -1 then ((List.range 7).map fun i ↦
          (-1) ^ i * ((List.range 7).reverse.map (cs.getD · 0)).getD i 0, true, true)
        else ((List.range 7).reverse.map (cs.getD · 0), true, false))
      else if degree cs = 5 ∧ cs.getD 5 0 = -1 then
        ((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0, false, true)
      else (cs, false, false) := by
  simp only [searchedCoeffs, decide_eq_true_eq]
  by_cases hr : degree cs = 6 ∧ cs.getD 0 0 = 0 ∧ |cs.getD 1 0| = 1
  · simp only [hr, degree_map_reverse_range hr.2.1 hr.2.2,
      getD_map_reverse_range cs (show 5 < 7 by decide), true_and, and_self, ↓reduceIte,
      decide_true, Nat.reduceSub]
    split_ifs with h <;> simp only [h, decide_true, decide_false]
  · simp only [hr, ↓reduceIte, decide_false]
    split_ifs with h <;> simp only [h, and_self, decide_true, decide_false]

theorem length_searchedCoeffs_le {cs : List ℤ} (h7 : cs.length ≤ 7) :
    (searchedCoeffs cs).1.length ≤ 7 := by
  simp only [searchedCoeffs, decide_eq_true_eq]
  split_ifs <;> simp [h7]

theorem length_searchedCoeffs_of_length_eq {cs : List ℤ} (h7 : cs.length = 7) :
    (searchedCoeffs cs).1.length = 7 := by
  simp only [searchedCoeffs, decide_eq_true_eq]
  split_ifs <;> simp [h7]

theorem degree_searchedCoeffs {cs : List ℤ} (h7 : cs.length ≤ 7) :
    degree (searchedCoeffs cs).1 = if (searchedCoeffs cs).2.1 then 5 else degree cs := by
  simp only [searchedCoeffs, decide_eq_true_eq]
  split_ifs with hr hn hn
  · rw [degree_map_range_neg_one_pow_mul (by simp), degree_map_reverse_range hr.2.1 hr.2.2]
  · exact degree_map_reverse_range hr.2.1 hr.2.2
  · exact degree_map_range_neg_one_pow_mul h7
  · rfl

/-- The curve searched is squarefree when the curve given is: its polynomial is the reverse of the
polynomial given (`JPoints.poly_map_reverse_range`) or the polynomial given at `-x`
(`JPoints.poly_map_range_neg_one_pow_mul`), or both. -/
theorem squarefree_poly_searchedCoeffs {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h : Squarefree (poly cs)) : Squarefree (poly (searchedCoeffs cs).1) := by
  simp only [searchedCoeffs, decide_eq_true_eq]
  split_ifs with hr hn hn
  · exact squarefree_poly_map_range_neg_one_pow_mul (by simp)
      (squarefree_poly_map_reverse_range h7 hr.1 h)
  · exact squarefree_poly_map_reverse_range h7 hr.1 h
  · exact squarefree_poly_map_range_neg_one_pow_mul h7 h
  · exact h

/-! ### The Kummer surface under the sign, the negation and the reversal -/

section Kummer

variable {f g : ℕ → ℤ}

variable (f) in
theorem kummer_neg (a b c d : ℤ) :
    kummer f (-a) (-b) (-c) (-d) = kummer f a b c d := by
  simpa using kummer_mul f (-1) a b c d

theorem lifts_neg_iff {a b c d : ℤ} : Lifts f (-a) (-b) (-c) (-d) ↔ Lifts f a b c d := by
  have hA : auxA2 f (-a) (-b) (-c) (-d) = auxA2 f a b c d := by simp only [auxA2]; ring
  have hB : auxB2 f (-a) (-b) (-c) (-d) = auxB2 f a b c d := by simp only [auxB2]; ring
  simp only [Lifts, neg_eq_zero, hA, hB, sexticForm_neg]

/-- The Kummer equation of the curve `g` with `y² = g(x) = f(-x)` at `(a, b, c, d)` is that of
`f` at `(a, -b, c, d)`. -/
theorem kummer_eq_of_negated (hg : ∀ k ≤ 6, g k = (-1) ^ k * f k) (a b c d : ℤ) :
    kummer g a b c d = kummer f a (-b) c d := by
  simp (disch := lia) only [kummer, kummerK2, kummerK1, kummerK0, hg]
  ring

/-- The lifting test of the curve `g` with `y² = g(x) = f(-x)` at `(a, b, c, d)` is that of `f`
at `(a, -b, c, d)`, in every chart. -/
theorem lifts_iff_of_negated (hg : ∀ k ≤ 6, g k = (-1) ^ k * f k) {a b c d : ℤ} :
    Lifts g a b c d ↔ Lifts f a (-b) c d := by
  have hA : auxA2 g a b c d = auxA2 f a (-b) c d := by
    simp (disch := lia) only [auxA2, hg]
    ring
  have hB : auxB2 g a b c d = auxB2 f a (-b) c d := by
    simp (disch := lia) only [auxB2, hg]
    ring
  have hS : sexticForm g c b = sexticForm f c (-b) := by
    simp (disch := lia) only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero, hg]
    ring
  simp (disch := lia) [Lifts, hA, hB, hS, hg]

/-- The Kummer equation of the reversed curve `g` with `y² = g(x) = x⁶ f(1 / x)` at `(a, b, c, d)`
is that of `f` at `(c, b, a, d)`. -/
theorem kummer_eq_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (a b c d : ℤ) :
    kummer g a b c d = kummer f c b a d := by
  simp (disch := lia) only [kummer, kummerK2, kummerK1, kummerK0, hg]
  ring

private theorem sexticForm_eq_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (x z : ℤ) :
    sexticForm g x z = sexticForm f z x := by
  simp (disch := lia) only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero, hg]
  ring

variable (f) in
/-- Over `(a, b, 0)`, where `0` is a root of `u`, `a² F(b, a) = a² b² A₂ + a⁴ B₂ + a³ b C`, which
is `(a b α + a² β)²` when `A₂ = α²`, `B₂ = β²` and `C = 2 α β`. -/
theorem sq_mul_sexticForm_eq (a b d : ℤ) :
    a ^ 2 * sexticForm f b a = a ^ 2 * b ^ 2 * auxA2 f a b 0 d + a ^ 4 * auxB2 f a b 0 d +
      a ^ 3 * b * auxC f a b 0 d := by
  simp only [sexticForm, auxA2, auxB2, auxC, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- Over `(0, b, c)` the Kummer equation is `(b d - f₅ c²)² - 4 f₆ A₂'`, with `A₂'` the
polynomial `A₂` of the reversed curve `g` at `(c, b, 0, d)`. -/
theorem kummer_zero_eq_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (b c d : ℤ) :
    kummer f 0 b c d = (b * d - f 5 * c ^ 2) ^ 2 - 4 * f 6 * auxA2 g c b 0 d := by
  simp (disch := lia) only [kummer, kummerK2, kummerK1, kummerK0, auxA2, hg]
  ring

/-- `F(c, b) = b⁶ f(c / b)` in terms of the polynomial `A₂'` of the reversed curve `g` at
`(c, b, 0, d)`. -/
theorem sexticForm_eq_sq_mul_auxA2_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (b c d : ℤ) :
    sexticForm f c b =
      b ^ 2 * auxA2 g c b 0 d - c ^ 3 * b * (b * d - f 5 * c ^ 2) + f 6 * c ^ 6 := by
  simp (disch := lia) only [sexticForm, auxA2, Finset.sum_range_succ, Finset.sum_range_zero, hg]
  ring

-- In the charts `a ≠ 0` of `f` and `c ≠ 0` of the reversed curve.
private theorem isSquare_auxA2_and_isSquare_auxB2_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k))
    {a b c d : ℤ} (hK : kummer f a b c d = 0) (ha : a ≠ 0) (hA : IsSquare (auxA2 f a b c d))
    (hB : IsSquare (auxB2 f a b c d)) :
    IsSquare (auxA2 g c b a d) ∧ IsSquare (auxB2 g c b a d) := by
  obtain ⟨α, β, hα, hβ, hC⟩ := exists_sq_auxA2_auxB2 hK hA hB
  refine ⟨isSquare_auxA2_of_reversed hg ha hα hβ hC,
    Int.isSquare_of_sq_mul_eq_sq ha (b := c * α + b * β) ?_⟩
  linear_combination sq_mul_auxB2_eq_of_reversed hg a b c d - c ^ 2 * hα - b * c * hC -
    b ^ 2 * hβ

-- The chart `a ≠ 0` of `f`, the chart `c ≠ 0` or the charts at infinity of the reversed curve.
private theorem lifts_of_reversed_of_ne_zero (hg : ∀ k ≤ 6, g k = f (6 - k)) {a b c d : ℤ}
    (hK : kummer f a b c d = 0) (ha : a ≠ 0) (h : Lifts f a b c d) : Lifts g c b a d := by
  simp only [Lifts, ha, ↓reduceIte] at h
  rcases eq_or_ne c 0 with rfl | hc
  · obtain ⟨α, β, hα, hβ, hC⟩ := exists_sq_auxA2_auxB2 hK h.1 h.2
    have hB : auxB2 f a b 0 d = f 0 * a ^ 4 := by simp only [auxB2]; ring
    have h0 : IsSquare (g 6) := hg 6 le_rfl ▸
      Int.isSquare_of_sq_mul_eq_sq (pow_ne_zero 2 ha) (b := β) (by linear_combination -hβ - hB)
    have hS : IsSquare (sexticForm g a b) := sexticForm_eq_of_reversed hg a b ▸
      Int.isSquare_of_sq_mul_eq_sq ha (b := a * (b * α + a * β)) (by
        linear_combination sq_mul_sexticForm_eq f a b d - a ^ 2 * b ^ 2 * hα - a ^ 4 * hβ -
          a ^ 3 * b * hC)
    simp only [Lifts, h0, hS, ↓reduceIte, and_self, ite_self]
  · simp only [Lifts, hc, ↓reduceIte]
    exact isSquare_auxA2_and_isSquare_auxB2_of_reversed hg hK ha h.1 h.2

-- The charts at infinity of `f`, the chart `c ≠ 0` of the reversed curve.
private theorem lifts_of_reversed_of_left_eq_zero (hg : ∀ k ≤ 6, g k = f (6 - k))
    (hf : f 5 ≠ 0 ∨ f 6 ≠ 0) {b c d : ℤ} (hK : kummer f 0 b c d = 0) (hc : c ≠ 0)
    (h : Lifts f 0 b c d) : Lifts g c b 0 d := by
  have h6 : IsSquare (f 6) := by rw [Lifts] at h; split_ifs at h <;> simp_all
  simp only [Lifts, hc, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · have hK' := kummer_zero_eq_of_reversed hg b c d
    rcases eq_or_ne (f 6) 0 with h60 | h60
    · have hbd : b * d - f 5 * c ^ 2 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
        (by linear_combination hK'.symm + hK + 4 * auxA2 g c b 0 d * h60)
      have hb : b ≠ 0 := by
        rintro rfl
        exact hf.elim (· (by simpa [hc] using hbd)) (· h60)
      obtain ⟨-, σ, hσ⟩ : IsSquare (f 6) ∧ IsSquare (sexticForm f c b) := by
        simpa [Lifts, hb] using h
      exact Int.isSquare_of_sq_mul_eq_sq hb (b := σ) (by
        linear_combination -(sexticForm_eq_sq_mul_auxA2_of_reversed hg b c d) + hσ +
          c ^ 3 * b * hbd - c ^ 6 * h60)
    · obtain ⟨γ, hγ⟩ := h6
      exact Int.isSquare_of_sq_mul_eq_sq (a := 2 * γ) (by intro h; simp_all)
        (b := b * d - f 5 * c ^ 2) (by linear_combination hK' - hK - 4 * auxA2 g c b 0 d * hγ)
  · obtain ⟨γ, hγ⟩ := h6
    exact ⟨γ * c ^ 2, by simp (disch := lia) only [auxB2, hg]; rw [hγ]; ring⟩

-- The charts at infinity of both curves.
private theorem lifts_of_reversed_of_eq_zero_of_eq_zero (hg : ∀ k ≤ 6, g k = f (6 - k)) {b d : ℤ}
    (hb : b ≠ 0) (h : Lifts f 0 b 0 d) : Lifts g 0 b 0 d := by
  simp only [Lifts, hb, ↓reduceIte, sexticForm_zero_left] at h ⊢
  obtain ⟨⟨γ, hγ⟩, ⟨σ, hσ⟩⟩ := h
  refine ⟨hg 6 le_rfl ▸ Int.isSquare_of_sq_mul_eq_sq (pow_ne_zero 3 hb) (b := σ) ?_,
    ⟨γ * b ^ 3, ?_⟩⟩
  · linear_combination hσ
  · rw [hg 0 (by lia), Nat.sub_zero, hγ]
    ring

/-- A point `(a, b, c, d)` with `(a, b, c) ≠ 0` of the Kummer surface of a curve `f` of degree at
least `5` that lifts gives the point `(c, b, a, d)` of the reversed curve `g` that lifts, across the
charts of the lifting test. -/
private theorem lifts_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (hf : f 5 ≠ 0 ∨ f 6 ≠ 0)
    {a b c d : ℤ} (hK : kummer f a b c d = 0) (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h : Lifts f a b c d) : Lifts g c b a d := by
  rcases eq_or_ne a 0 with rfl | ha
  · rcases eq_or_ne c 0 with rfl | hc
    · exact lifts_of_reversed_of_eq_zero_of_eq_zero hg (by simpa using habc) h
    · exact lifts_of_reversed_of_left_eq_zero hg hf hK hc h
  · exact lifts_of_reversed_of_ne_zero hg hK ha h

/-- On the Kummer surface, a point `(a, b, c, d)` with `(a, b, c) ≠ 0` lifts on the reversed curve
`g` with `y² = g(x) = x⁶ f(1 / x)` exactly when `(c, b, a, d)` lifts on `f`, for curves `f` and `g`
of degree at least `5`. -/
theorem lifts_iff_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k)) (hf : f 5 ≠ 0 ∨ f 6 ≠ 0)
    (hf' : f 0 ≠ 0 ∨ f 1 ≠ 0) {a b c d : ℤ} (hK : kummer f c b a d = 0)
    (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : Lifts g a b c d ↔ Lifts f c b a d := by
  have hf'' : ∀ k ≤ 6, f k = g (6 - k) := fun k hk ↦ by rw [hg _ (by lia), Nat.sub_sub_self hk]
  refine ⟨lifts_of_reversed hf'' ?_ ((kummer_eq_of_reversed hg a b c d).trans hK) habc,
    lifts_of_reversed hg hf hK (by tauto)⟩
  rw [hg 5 (by lia), hg 6 (by lia)]
  exact hf'.symm

private theorem kummer_eq_zero_and_lifts_iff_of_negated (hg : ∀ k ≤ 6, g k = (-1) ^ k * f k)
    {a b c d : ℤ} :
    (kummer g a b c d = 0 ∧ Lifts g a b c d) ↔ (kummer f a (-b) c d = 0 ∧ Lifts f a (-b) c d) := by
  rw [kummer_eq_of_negated hg, lifts_iff_of_negated hg]

private theorem kummer_eq_zero_and_lifts_iff_of_reversed (hg : ∀ k ≤ 6, g k = f (6 - k))
    (hf : f 5 ≠ 0 ∨ f 6 ≠ 0) (hf' : f 0 ≠ 0 ∨ f 1 ≠ 0) {a b c d : ℤ}
    (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (kummer g a b c d = 0 ∧ Lifts g a b c d) ↔ (kummer f c b a d = 0 ∧ Lifts f c b a d) := by
  rw [kummer_eq_of_reversed hg]
  exact and_congr_right fun hK ↦ lifts_iff_of_reversed hg hf hf' hK habc

end Kummer

/-! ### The points taken back -/

/-- The map back to the curve given (`JPoints.backPoint`) keeps the gcd of the first three
coordinates and that of all four. -/
private theorem gcd_eq_and_gcd_eq_of_backPoint_eq {rev neg : Bool} {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    gcd a' (gcd b' c') = gcd a (gcd b c) ∧
      gcd a' (gcd b' (gcd c' d')) = gcd a (gcd b (gcd c d)) := by
  rcases backPoint_eq_or_eq_neg rev neg a b c d with h' | h' <;> rw [h] at h' <;>
    simp only [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h' <;>
    cases rev <;> cases neg <;> refine ⟨?_, ?_⟩ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, gcd_neg, neg_gcd] <;> ac_rfl

theorem isNormalized_of_backPoint_eq {rev neg : Bool} {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) (hn : IsNormalized a b c d) :
    IsNormalized a' b' c' d' := by
  refine ⟨(gcd_eq_and_gcd_eq_of_backPoint_eq h).2.trans hn.1, ?_⟩
  obtain ⟨-, hs⟩ := hn
  cases rev <;> cases neg <;> simp only [backPoint] at h <;> split_ifs at h <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> lia

theorem isNormalized_backPoint (rev neg : Bool) {p : ℤ × ℤ × ℤ × ℤ}
    (hp : IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2) :
    IsNormalized (backPoint rev neg p).1 (backPoint rev neg p).2.1 (backPoint rev neg p).2.2.1
      (backPoint rev neg p).2.2.2 := by
  obtain ⟨a, b, c, d⟩ := p
  exact isNormalized_of_backPoint_eq rfl hp

theorem inBounds_iff_of_backPoint_eq {rev neg : Bool} {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) {H : ℕ} {all : Bool}
    {W : Option ℕ} : InBounds H all W a' b' c' d' ↔ InBounds H all W a b c d := by
  obtain ⟨hm, hd⟩ := max_abs_eq_and_abs_eq_of_backPoint_eq h
  rw [InBounds, InBounds, hm, hd, (gcd_eq_and_gcd_eq_of_backPoint_eq h).1]

/-- The map back to the curve given is its own inverse on the normalized points: it is a signed
permutation of order two, followed by the sign that normalizes. -/
theorem backPoint_backPoint (rev neg : Bool) {a b c d : ℤ} (hn : IsNormalized a b c d) :
    backPoint rev neg (backPoint rev neg (a, b, c, d)) = (a, b, c, d) := by
  obtain ⟨-, hs⟩ := hn
  generalize hq : backPoint rev neg (a, b, c, d) = q
  obtain ⟨a', b', c', d'⟩ := q
  cases rev <;> cases neg <;> simp only [backPoint, Bool.false_eq_true, ↓reduceIte] at hq ⊢ <;>
    split_ifs at hq <;> simp only [Prod.mk.injEq] at hq <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := hq <;>
    split_ifs <;> simp only [Prod.mk.injEq, neg_neg] <;> lia

/-- The map back to the curve given is injective on the normalized points: it is its own inverse
there (`JPoints.backPoint_backPoint`). -/
theorem injOn_backPoint (rev neg : Bool) :
    Set.InjOn (backPoint rev neg) {p | IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2} :=
  Set.LeftInvOn.injOn (f₁' := backPoint rev neg) fun ⟨_, _, _, _⟩ hp ↦
    backPoint_backPoint rev neg hp

-- The sign of the map back.
private theorem kummer_eq_zero_and_lifts_iff_ite_of_backPoint_eq {f : ℕ → ℤ} {rev neg : Bool}
    {a b c d a' b' c' d' : ℤ} (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    (kummer f a' b' c' d' = 0 ∧ Lifts f a' b' c' d') ↔
      (kummer f (if rev then c else a) (if neg then -b else b) (if rev then a else c) d = 0 ∧
        Lifts f (if rev then c else a) (if neg then -b else b) (if rev then a else c) d) := by
  rcases backPoint_eq_or_eq_neg rev neg a b c d with h' | h' <;> rw [h] at h' <;>
    simp only [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  · rfl
  · rw [kummer_neg, lifts_neg_iff]

-- The negation of the curve searched.
private theorem kummer_eq_zero_and_lifts_iff_map_range_neg_one_pow_mul (cs : List ℤ)
    {a b c d : ℤ} :
    (kummer (((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0).getD · 0) a b c d = 0 ∧
        Lifts (((List.range 7).map fun i ↦ (-1) ^ i * cs.getD i 0).getD · 0) a b c d) ↔
      (kummer (cs.getD · 0) a (-b) c d = 0 ∧ Lifts (cs.getD · 0) a (-b) c d) :=
  kummer_eq_zero_and_lifts_iff_of_negated fun _ hk ↦
    getD_map_range_neg_one_pow_mul cs (Nat.lt_succ_of_le hk)

-- The reversal of the curve searched.
private theorem kummer_eq_zero_and_lifts_iff_map_reverse_range {cs : List ℤ}
    (hr : degree cs = 6 ∧ cs.getD 0 0 = 0 ∧ |cs.getD 1 0| = 1) {a b c d : ℤ}
    (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (kummer (((List.range 7).reverse.map (cs.getD · 0)).getD · 0) a b c d = 0 ∧
        Lifts (((List.range 7).reverse.map (cs.getD · 0)).getD · 0) a b c d) ↔
      (kummer (cs.getD · 0) c b a d = 0 ∧ Lifts (cs.getD · 0) c b a d) :=
  kummer_eq_zero_and_lifts_iff_of_reversed
    (fun _ hk ↦ getD_map_reverse_range cs (Nat.lt_succ_of_le hk))
    (.inr (by simpa [hr.1] using getD_degree_ne_zero (cs := cs) (by lia)))
    (.inr (abs_pos.mp (hr.2.2 ▸ one_pos))) habc

/-- A point `(a, b, c, d)` with `(a, b, c) ≠ 0` lies on the Kummer surface of the curve searched
and lifts exactly when its image on the curve given does: the sign does not matter, and the
negation and the reversal of the curve move the coordinates as the map back does. -/
theorem kummer_eq_zero_and_lifts_iff_of_backPoint_eq {cs : List ℤ} {a b c d a' b' c' d' : ℤ}
    (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h : backPoint (searchedCoeffs cs).2.1 (searchedCoeffs cs).2.2 (a, b, c, d) =
      (a', b', c', d')) :
    (kummer (cs.getD · 0) a' b' c' d' = 0 ∧ Lifts (cs.getD · 0) a' b' c' d') ↔
      (kummer ((searchedCoeffs cs).1.getD · 0) a b c d = 0 ∧
        Lifts ((searchedCoeffs cs).1.getD · 0) a b c d) := by
  rw [kummer_eq_zero_and_lifts_iff_ite_of_backPoint_eq h]
  simp only [searchedCoeffs, decide_eq_true_eq]
  split_ifs with hr hn hn
  · rw [kummer_eq_zero_and_lifts_iff_map_range_neg_one_pow_mul,
      kummer_eq_zero_and_lifts_iff_map_reverse_range hr (by simpa using habc)]
  · rw [kummer_eq_zero_and_lifts_iff_map_reverse_range hr habc]
  · rw [kummer_eq_zero_and_lifts_iff_map_range_neg_one_pow_mul]
  · rfl

/-- A normalized point `p` of the curve searched is a point exactly when its image on the curve
given (`JPoints.backPoint`) is a point of the curve given: the map back keeps the Kummer equation
and the lifting (`JPoints.kummer_eq_zero_and_lifts_iff_of_backPoint_eq`), the normalization
(`JPoints.isNormalized_of_backPoint_eq`) and the bounds (`JPoints.inBounds_iff_of_backPoint_eq`). -/
theorem isPoint_backPoint_iff {cs : List ℤ} {H : ℕ} {all : Bool} {W : Option ℕ}
    {p : ℤ × ℤ × ℤ × ℤ} (hp : IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2) :
    IsPoint cs H all W (backPoint (searchedCoeffs cs).2.1 (searchedCoeffs cs).2.2 p) ↔
      IsPoint (searchedCoeffs cs).1 H all W p := by
  obtain ⟨a, b, c, d⟩ := p
  generalize hq : backPoint (searchedCoeffs cs).2.1 (searchedCoeffs cs).2.2 (a, b, c, d) = q
  obtain ⟨a', b', c', d'⟩ := q
  have habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by have := hp.2; lia
  simp only [IsPoint, isNormalized_of_backPoint_eq hq hp, hp, true_and,
    inBounds_iff_of_backPoint_eq hq, ← and_assoc,
    kummer_eq_zero_and_lifts_iff_of_backPoint_eq habc hq]

end JPoints

end
