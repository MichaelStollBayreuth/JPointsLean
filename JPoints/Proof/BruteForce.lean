/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.BruteForce
public import JPoints.Spec.Basic

import JPoints.Mathlib.Data.Int.Sqrt
import JPoints.Mathlib.Data.Rat.Lemmas
import JPoints.Proof.Kummer
import JPoints.Proof.Order

/-!
# The brute-force reference finds exactly the points

`JPoints.bruteForce cs H all W` lists every point of the specification (`JPoints.IsPoint`), and
nothing else, each once, for every curve that the program does not refuse; for every curve it is the
list of the candidates of `JPoints.kummerPoints` over the triples of `JPoints.orderedTriples H` that
are points, which is `JPoints.orderedPoints` for a curve that the program does not transform.
Comparator certifies `JPoints.bruteForce_eq_filter_flatMap_kummerPoints`,
`JPoints.mem_bruteForce_iff`, `JPoints.nodup_bruteForce` and
`JPoints.orderedPoints_eq_map_bruteForce` (`comparator/Challenge.lean`).

## Main statements

* `JPoints.bruteForce_eq_filter_flatMap_kummerPoints`: the brute-force reference is the list of the
  candidates that are points, in the order of the search.
* `JPoints.mem_bruteForce_iff`: a quadruple lies in `JPoints.bruteForce cs H all W` exactly when
  it is a point.
* `JPoints.nodup_bruteForce`: the list has no duplicates.
* `JPoints.isNormalized_of_mem_bruteForce`: its points are normalised.
* `JPoints.orderedPoints_eq_map_bruteForce`: the points in the order of `j-points` are those of
  the brute-force reference of the curve searched, taken back to the curve given.

## Proof

The triples of the model are those of the specification (`JPoints.BruteForce.orderedTriples_eq`).
The candidates of the model, from the discriminant as the exact check of the program computes them,
are those of `JPoints.kummerPoints` (`JPoints.BruteForce.candidates_eq`); the reduction of a
fraction by the gcd of its numerator and denominator gives the numerator and the denominator of the
rational number (`JPoints.BruteForce.pointOf_eq`). A candidate over a coprime normalised triple is
normalised and lies on the Kummer surface, so that it is a point exactly when it is within the
bounds and lifts, which the lifting test of the program decides there
(`JPoints.lifts_iff_of_kummer_eq_zero`).
-/

@[expose] public section

namespace JPoints

namespace BruteForce

private theorem boxTriples_eq (H : ℕ) : boxTriples H = JPoints.boxTriples H := by
  refine List.filter_congr fun ⟨a, b, c⟩ _ ↦ ?_
  simp [← Int.coe_gcd, Bool.beq_eq_decide_eq]

theorem orderedTriples_eq (H : ℕ) : orderedTriples H = JPoints.orderedTriples H := by
  rw [orderedTriples, JPoints.orderedTriples, boxTriples_eq]
  congr 1 <;> refine List.filter_congr fun ⟨a, b, c⟩ _ ↦ ?_ <;>
    simp [sq, bne, Bool.beq_eq_decide_eq]

theorem pointOf_eq (a b c d₁ : ℤ) {d₂ : ℤ} (hd : d₂ ≠ 0) :
    pointOf a b c d₁ d₂ = (((d₁ : ℚ) / d₂).den * a, ((d₁ : ℚ) / d₂).den * b,
      ((d₁ : ℚ) / d₂).den * c, ((d₁ : ℚ) / d₂).num) := by
  have hcop : Nat.Coprime (d₁ / Int.gcd d₁ d₂).natAbs (d₂ / Int.gcd d₁ d₂).natAbs :=
    Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right hd
  have hm : d₂ / Int.gcd d₁ d₂ ≠ 0 := Int.ediv_gcd_ne_zero_of_ne_zero_right d₁ hd
  rw [pointOf, ← Rat.intCast_ediv_gcd_div_intCast_ediv_gcd d₁ hd]
  generalize d₁ / Int.gcd d₁ d₂ = n, d₂ / Int.gcd d₁ d₂ = m at *
  split_ifs with h
  · rw [Rat.num_div_eq_neg_of_coprime h hcop, Rat.den_div_eq_neg_of_coprime h hcop]
  · rw [Rat.num_div_eq_of_coprime (by lia) hcop, Rat.den_div_eq_of_coprime (by lia) hcop]

private theorem kummerCoeffs_eq (cs : List ℤ) (a b c : ℤ) :
    kummerCoeffs cs a b c =
      (kummerK2 a b c, kummerK1 (cs.getD · 0) a b c, kummerK0 (cs.getD · 0) a b c) := by
  simp only [kummerCoeffs, kummerK2, kummerK1, kummerK0, coeff, sq]

theorem isSquare_eq_decide (n : ℤ) : isSquare n = decide (IsSquare n) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Int.isSquare_iff_sqrt_mul_sqrt, isSquare, Int.sqrt]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨fun ⟨h0, h⟩ ↦ by rw [← Nat.cast_mul, h, Int.toNat_of_nonneg h0], fun h ↦ ?_⟩
  have h0 : 0 ≤ n := h ▸ mul_self_nonneg _
  exact ⟨h0, mod_cast h.trans (Int.toNat_of_nonneg h0).symm⟩

private theorem foldr_eq_sexticForm (f : ℕ → ℤ) (x z : ℤ) :
    (List.range 7).foldr (fun k s ↦ f k * x ^ k * z ^ (6 - k) + s) 0 = sexticForm f x z := by
  simp [sexticForm, Finset.sum_range_succ, List.range_succ, add_assoc]

/- The bounds on the absolute values in `ℕ`, as the brute force compares them, and in `ℤ`. -/
private theorem natAbs_le_iff_abs_le {a : ℤ} {n : ℕ} : a.natAbs ≤ n ↔ |a| ≤ n := by
  rw [← Int.natCast_natAbs, Nat.cast_le]

private theorem inBounds_eq_decide (H : ℕ) (all : Bool) (W : Option ℕ) (a b c d : ℤ) :
    inBounds H all W a b c d = decide (InBounds H all W a b c d) := by
  cases all <;> cases W <;>
    simp [inBounds, InBounds, ← Int.coe_gcd, natAbs_le_iff_abs_le, Bool.and_assoc]

/-- The lifting test of the brute-force reference, in the polynomials of the specification: for
`a ≠ 0` whether `A₂` is a square when it is not `0`, and `B₂` when it is. -/
theorem lifts_eq_ite (cs : List ℤ) (a b c d : ℤ) :
    lifts cs a b c d = if a = 0 then (if b = 0 then decide (IsSquare (cs.getD 6 0)) else
      decide (IsSquare (cs.getD 6 0)) && decide (IsSquare (sexticForm (cs.getD · 0) c b)))
    else if auxA2 (cs.getD · 0) a b c d ≠ 0 then decide (IsSquare (auxA2 (cs.getD · 0) a b c d))
    else decide (IsSquare (auxB2 (cs.getD · 0) a b c d)) := by
  simp only [lifts, coeff, foldr_eq_sexticForm, isSquare_eq_decide, auxA2, auxB2, sq, beq_iff_eq,
    bne_iff_ne]

theorem lifts_eq_decide {cs : List ℤ} {a b c d : ℤ} (hK : kummer (cs.getD · 0) a b c d = 0) :
    lifts cs a b c d = decide (Lifts (cs.getD · 0) a b c d) := by
  simp only [lifts_iff_of_kummer_eq_zero hK, lifts, coeff, foldr_eq_sexticForm, isSquare_eq_decide,
    auxA2, auxB2, sq]
  split_ifs <;> simp_all

theorem candidates_eq (cs : List ℤ) (a b c : ℤ) :
    candidates cs a b c = kummerPoints (cs.getD · 0) (a, b, c) := by
  simp only [candidates, kummerCoeffs_eq, kummerPoints, kummerRoots, ← sq, isSquare_eq_decide,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  generalize kummerK2 a b c = k2, kummerK1 (cs.getD · 0) a b c = k1,
    kummerK0 (cs.getD · 0) a b c = k0
  by_cases h2 : k2 = 0
  · subst h2
    by_cases h1 : k1 = 0
    · simp [h1]
    · simp [h1, pointOf_eq _ _ _ _ h1, IsSquare.sq]
  have h2' : 2 * k2 ≠ 0 := by lia
  simp only [h2, false_and, ite_false, Int.isSquare_iff_sqrt_mul_sqrt, ← sq, neg_add']
  generalize k1 ^ 2 - 4 * k0 * k2 = d
  rw [show ((d.toNat.sqrt : ℕ) : ℤ) = Int.sqrt d from rfl]
  by_cases hd : d = 0
  · simp [hd, pointOf_eq _ _ _ _ h2']
  by_cases hs : Int.sqrt d ^ 2 = d
  · have h0 : Int.sqrt d ≠ 0 := fun h ↦ hd (by rw [← hs, h, zero_pow two_ne_zero])
    simp [hd, hs, h0, pointOf_eq _ _ _ _ h2']
  · simp [hd, hs]

/-- On a candidate over a triple of the search, the test of the brute-force reference decides
`JPoints.IsPoint`. -/
private theorem inBounds_and_lifts_eq_decide {cs : List ℤ} {H : ℕ} {all : Bool} {W : Option ℕ}
    {t : ℤ × ℤ × ℤ} (ht : t ∈ JPoints.orderedTriples H) {p : ℤ × ℤ × ℤ × ℤ}
    (hp : p ∈ kummerPoints (cs.getD · 0) t) :
    (inBounds H all W p.1 p.2.1 p.2.2.1 p.2.2.2 && lifts cs p.1 p.2.1 p.2.2.1 p.2.2.2) =
      decide (IsPoint cs H all W p) := by
  have hK := kummer_eq_zero_of_mem_kummerPoints hp
  have hN := isNormalized_of_mem_kummerPoints ht hp
  obtain ⟨a, b, c, d⟩ := p
  rw [inBounds_eq_decide, lifts_eq_decide hK, ← Bool.decide_and]
  exact decide_eq_decide.2 ⟨fun h ↦ ⟨hK, h.2, hN, h.1⟩, fun h ↦ ⟨h.2.2.2, h.2.1⟩⟩

end BruteForce

open BruteForce in
/-- The brute-force reference is the list of the candidates of `JPoints.kummerPoints` over the
triples of `JPoints.orderedTriples H` that are points, in the order of the search; comparator
certifies this (`comparator/Challenge.lean`). -/
theorem bruteForce_eq_filter_flatMap_kummerPoints (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    bruteForce cs H all W =
      ((orderedTriples H).flatMap (kummerPoints (cs.getD · 0))).filter (IsPoint cs H all W) := by
  rw [bruteForce, orderedTriples_eq, List.filter_flatMap]
  refine List.flatMap_congr fun ⟨a, b, c⟩ ht ↦ ?_
  dsimp only
  rw [candidates_eq]
  exact List.filter_congr fun p hp ↦ inBounds_and_lifts_eq_decide ht hp

theorem isNormalized_of_mem_bruteForce {cs : List ℤ} {H : ℕ} {all : Bool} {W : Option ℕ}
    {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ bruteForce cs H all W) :
    IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  rw [bruteForce_eq_filter_flatMap_kummerPoints] at hp
  obtain ⟨a, b, c, d⟩ := p
  exact (of_decide_eq_true (List.mem_filter.mp hp).2).2.2.1

/-- The brute-force reference lists exactly the points, for every curve that the program does not
refuse; comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_bruteForce_iff {cs : List ℤ} (h7 : cs.length ≤ 7) (h5 : 5 ≤ degree cs)
    (hsq : Squarefree (poly cs)) {H : ℕ} {all : Bool} {W : Option ℕ} {p : ℤ × ℤ × ℤ × ℤ} :
    p ∈ bruteForce cs H all W ↔ IsPoint cs H all W p :=
  bruteForce_eq_filter_flatMap_kummerPoints cs H all W ▸
    mem_filter_flatMap_kummerPoints_iff h7 h5 hsq

/-- The brute-force reference lists each point once; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem nodup_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    (bruteForce cs H all W).Nodup :=
  bruteForce_eq_filter_flatMap_kummerPoints cs H all W ▸ (nodup_flatMap_kummerPoints _ H).filter _

/-- The points in the order of `j-points` are those of the brute-force reference of the curve
searched, taken back to the curve given; comparator certifies this (`comparator/Challenge.lean`). -/
theorem orderedPoints_eq_map_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    orderedPoints cs H all W = (bruteForce (searchedCoeffs cs).1 H all W).map
      (backPoint (searchedCoeffs cs).2.1 (searchedCoeffs cs).2.2) := by
  rw [orderedPoints, bruteForce_eq_filter_flatMap_kummerPoints]


/-! ### The axioms of the main theorems -/

/--
info: 'JPoints.bruteForce_eq_filter_flatMap_kummerPoints' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bruteForce_eq_filter_flatMap_kummerPoints

/--
info: 'JPoints.mem_bruteForce_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mem_bruteForce_iff

/--
info: 'JPoints.nodup_bruteForce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodup_bruteForce

/--
info: 'JPoints.orderedPoints_eq_map_bruteForce' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms orderedPoints_eq_map_bruteForce

end JPoints

end
