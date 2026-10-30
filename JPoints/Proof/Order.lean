/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Spec.Basic

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.Data.List.Nodup
import JPoints.Proof.Kummer
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The enumeration of the order lists every point once

Over the triples of `JPoints.orderedTriples H`, the candidates of `JPoints.kummerPoints` that are
points (`JPoints.IsPoint`) are all the points, each once, for every curve that the program does not
refuse. A point `(a, b, c, d)` lies over the triple `(a, b, c) / g`, `g = gcd(a, b, c)`, which is
coprime, normalized and in the box, and `d / g` is a root of the Kummer equation over it, in lowest
terms since the point is normalized; the Kummer equation over a triple is never constant zero
(`JPoints.kummerK0_ne_zero`), so that `JPoints.kummerRoots` lists its rational roots
(`JPoints.mem_kummerRoots_iff`). Distinct roots give distinct candidates, and the candidates over
distinct coprime triples differ, since the triple is the candidate divided by the gcd of its first
three coordinates.

## Main statements

* `JPoints.mem_boxTriples_iff`, `JPoints.mem_orderedTriples_iff`, `JPoints.nodup_orderedTriples`:
  the triples of the box.
* `JPoints.mem_kummerRoots_iff`, `JPoints.nodup_kummerRoots`: the roots of the Kummer equation.
* `JPoints.mem_filter_flatMap_kummerPoints_iff`: the candidates that are points are all the points.
* `JPoints.nodup_flatMap_kummerPoints`: the candidates are distinct.
* `JPoints.kummer_eq_zero_of_mem_kummerPoints`, `JPoints.isNormalized_of_mem_kummerPoints`: the
  candidates over the triples of the search lie on the Kummer surface and are normalized.
-/

@[expose] public section

namespace JPoints

theorem mem_intRange_iff {H : ℕ} {x : ℤ} : x ∈ intRange H ↔ |x| ≤ H := by
  simp only [intRange, List.mem_map, List.mem_range, abs_le]
  exact ⟨fun ⟨i, hi, h⟩ ↦ by lia, fun h ↦ ⟨(x + H).toNat, by lia, by lia⟩⟩

theorem nodup_intRange (H : ℕ) : (intRange H).Nodup :=
  List.nodup_range.map fun i j h ↦ by simpa using h

theorem mem_boxTriples_iff {H : ℕ} {a b c : ℤ} :
    (a, b, c) ∈ boxTriples H ↔ gcd a (gcd b c) = 1 ∧ (0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c)) ∧
      |a| ≤ H ∧ |b| ≤ H ∧ |c| ≤ H := by
  simp only [boxTriples, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range,
    mem_intRange_iff, Prod.mk.injEq, decide_eq_true_eq, abs_le]
  refine ⟨fun ⟨⟨a', ha', b', hb, c', hc, h⟩, hg, hn⟩ ↦ ⟨hg, hn, by lia⟩,
    fun ⟨hg, hn, ha, hb, hc⟩ ↦ ⟨⟨a.toNat, by lia, b, hb, c, hc, by lia, rfl, rfl⟩, hg, hn⟩⟩

theorem mem_orderedTriples_iff {H : ℕ} {t : ℤ × ℤ × ℤ} :
    t ∈ orderedTriples H ↔ t ∈ boxTriples H := by
  simp only [orderedTriples, List.mem_append, List.mem_filter]
  grind

theorem nodup_boxTriples (H : ℕ) : (boxTriples H).Nodup := by
  refine .filter _ <| .flatMap (fun t ↦ t.1.toNat) List.nodup_range (fun a _ ↦ ?_)
    (by simp; lia)
  exact .flatMap (fun t ↦ t.2.1) (nodup_intRange H)
    (fun b _ ↦ (nodup_intRange H).map fun c c' h ↦ by simpa using h) (by simp)

theorem nodup_orderedTriples (H : ℕ) : (orderedTriples H).Nodup :=
  ((nodup_boxTriples H).filter _).append ((nodup_boxTriples H).filter _) fun t h h' ↦ by
    simp_all [List.mem_filter]

/- An integer whose cast is the discriminant of a quadratic with a rational root is the square of
its integer square root. -/
private theorem sqrt_sq_of_quadratic_eq_zero {a b c x : ℚ} {d : ℤ} (hd : (d : ℚ) = discrim a b c)
    (hx : a * (x * x) + b * x + c = 0) : Int.sqrt d ^ 2 = d := by
  obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.1
    ⟨_, (hd.trans (discrim_eq_sq_of_quadratic_eq_zero hx)).trans (sq _)⟩
  rw [sq, ← Int.exists_mul_self]
  exact ⟨r, hr.symm⟩

/- The roots of a quadratic with integer coefficients whose discriminant `d` is a square in `ℤ`. -/
private theorem quadratic_eq_zero_iff_of_sqrt_sq {a b c d : ℤ} (ha : a ≠ 0)
    (hd : (d : ℚ) = discrim (a : ℚ) b c) (hs : Int.sqrt d ^ 2 = d) {x : ℚ} :
    (a : ℚ) * (x * x) + b * x + c = 0 ↔
      x = ((Int.sqrt d - b : ℤ) : ℚ) / (2 * a) ∨ x = ((-Int.sqrt d - b : ℤ) : ℚ) / (2 * a) := by
  rw [quadratic_eq_zero_iff (mod_cast ha) (s := (Int.sqrt d : ℚ))
    (by rw [← hd, ← sq]; exact_mod_cast hs.symm)]
  push_cast
  rw [neg_add_eq_sub, neg_sub_comm]

theorem mem_kummerRoots_iff {f : ℕ → ℤ} {a b c : ℤ}
    (h : kummerK2 a b c ≠ 0 ∨ kummerK1 f a b c ≠ 0 ∨ kummerK0 f a b c ≠ 0) {x : ℚ} :
    x ∈ kummerRoots f a b c ↔
      (kummerK2 a b c : ℚ) * x ^ 2 + kummerK1 f a b c * x + kummerK0 f a b c = 0 := by
  simp only [kummerRoots]
  generalize kummerK2 a b c = k2, kummerK1 f a b c = k1, kummerK0 f a b c = k0 at *
  have hd : ((k1 ^ 2 - 4 * k0 * k2 : ℤ) : ℚ) = discrim (k2 : ℚ) k1 k0 := by
    push_cast [discrim]; ring
  generalize k1 ^ 2 - 4 * k0 * k2 = d at *
  rw [sq x]
  split_ifs with h2 h1 hs hs0
  · simp only [h2, h1, Int.cast_zero, zero_mul, zero_add, List.not_mem_nil, false_iff,
      Int.cast_eq_zero]
    tauto
  · rw [h2, List.mem_singleton, eq_div_iff (mod_cast h1)]
    grind
  · exact iff_of_false List.not_mem_nil fun hq ↦ hs (sqrt_sq_of_quadratic_eq_zero hd hq)
  · rw [List.mem_singleton, quadratic_eq_zero_iff_of_sqrt_sq h2 hd (not_not.1 hs), hs0]
    simp
  · simp [quadratic_eq_zero_iff_of_sqrt_sq h2 hd (not_not.1 hs)]

theorem nodup_kummerRoots (f : ℕ → ℤ) (a b c : ℤ) : (kummerRoots f a b c).Nodup := by
  simp only [kummerRoots]
  split_ifs with h2 _ _ hs0
  all_goals simp [h2]
  norm_cast
  lia

/- The scaled triple `(m a, m b, m c)` of a coprime triple has the gcd `m`, for `m ≥ 0`. -/
private theorem gcd_mul_gcd_mul_mul_of_gcd_eq_one {m a b c : ℤ} (hm : 0 ≤ m)
    (h : gcd a (gcd b c) = 1) : gcd (m * a) (gcd (m * b) (m * c)) = m := by
  simp [Int.normalize_of_nonneg hm, h]

theorem mul_mem_kummerPoints {f : ℕ → ℤ} {g a b c d : ℤ} (hg : 0 < g) (hd : gcd g d = 1)
    (h : (d / g : ℚ) ∈ kummerRoots f a b c) :
    (g * a, g * b, g * c, d) ∈ kummerPoints f (a, b, c) := by
  have hcop : Nat.Coprime d.natAbs g.natAbs := by
    change Int.gcd d g = 1
    rw [← Int.natAbs_gcd, gcd_comm, hd]
    rfl
  refine List.mem_map.2 ⟨_, h, ?_⟩
  rw [Rat.num_div_eq_of_coprime hg hcop, Rat.den_div_eq_of_coprime hg hcop]

/- The bounds of the search on a point `(g a, g b, g c, d)`, `g > 0`, over a coprime triple
`(a, b, c)` put the triple into the box. -/
private theorem abs_le_of_inBounds {H : ℕ} {all : Bool} {W : Option ℕ} {g a b c d : ℤ}
    (hg : 0 < g) (h1 : gcd a (gcd b c) = 1) (h : InBounds H all W (g * a) (g * b) (g * c) d) :
    |a| ≤ H ∧ |b| ≤ H ∧ |c| ≤ H := by
  suffices max |a| (max |b| |c|) ≤ H by simpa only [max_le_iff] using this
  rw [InBounds, gcd_mul_gcd_mul_mul_of_gcd_eq_one hg.le h1] at h
  simp only [abs_mul, abs_of_pos hg, ← mul_max_of_nonneg _ _ hg.le] at h
  split_ifs at h
  · exact le_of_mul_le_mul_left (h.1.trans_eq (mul_comm _ _)) hg
  · exact (le_mul_of_one_le_left (by positivity) (by lia)).trans h.1

/-- Every point is a candidate over a triple of the search, for every curve that the program does
not refuse. -/
theorem mem_flatMap_kummerPoints_of_isPoint {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h5 : 5 ≤ degree cs) (hsq : Squarefree (poly cs)) {H : ℕ} {all : Bool} {W : Option ℕ}
    {p : ℤ × ℤ × ℤ × ℤ} (hp : IsPoint cs H all W p) :
    p ∈ (orderedTriples H).flatMap (kummerPoints (cs.getD · 0)) := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨hK, -, ⟨h1, hn⟩, hB⟩ := hp
  obtain ⟨g, A, B, C, hg, hcop, rfl, rfl, rfl⟩ :=
    Int.exists_pos_mul_and_gcd_eq_one a b c (by lia)
  rw [← gcd_assoc (g * B), ← gcd_assoc, gcd_mul_gcd_mul_mul_of_gcd_eq_one hg.le hcop] at h1
  have hn' : 0 < A ∨ A = 0 ∧ (0 < B ∨ B = 0 ∧ 0 < C) := by
    simpa [mul_pos_iff_of_pos_left hg, hg.ne'] using hn
  have hroot := kummer_mul_div (cs.getD · 0) A B C d hg.ne'
  rw [hK, Int.cast_zero, eq_comm, mul_eq_zero] at hroot
  refine List.mem_flatMap.2 ⟨(A, B, C), mem_orderedTriples_iff.2 (mem_boxTriples_iff.2
    ⟨hcop, hn', abs_le_of_inBounds hg hcop hB⟩), mul_mem_kummerPoints hg h1
    ((mem_kummerRoots_iff ?_).2 (hroot.resolve_left (by positivity)))⟩
  by_contra! h0
  exact kummerK0_ne_zero h7 h5 hsq (by lia) h0.1 h0.2.1 h0.2.2

theorem mem_filter_flatMap_kummerPoints_iff {cs : List ℤ} (h7 : cs.length ≤ 7)
    (h5 : 5 ≤ degree cs) (hsq : Squarefree (poly cs)) {H : ℕ} {all : Bool} {W : Option ℕ}
    {p : ℤ × ℤ × ℤ × ℤ} :
    p ∈ ((orderedTriples H).flatMap (kummerPoints (cs.getD · 0))).filter (IsPoint cs H all W) ↔
      IsPoint cs H all W p :=
  List.mem_filter.trans ⟨fun h ↦ of_decide_eq_true h.2,
    fun h ↦ ⟨mem_flatMap_kummerPoints_of_isPoint h7 h5 hsq h, decide_eq_true h⟩⟩

/- Over a nonzero triple, a candidate determines its root. -/
private theorem injective_kummerPoint {a b c : ℤ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    Function.Injective fun x : ℚ ↦
      ((x.den : ℤ) * a, (x.den : ℤ) * b, (x.den : ℤ) * c, x.num) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨ha, hb, hc, hn⟩ := hxy
  have : (x.den : ℤ) = y.den := by
    rcases h with h | h | h
    exacts [mul_right_cancel₀ h ha, mul_right_cancel₀ h hb, mul_right_cancel₀ h hc]
  exact Rat.ext hn (mod_cast this)

theorem nodup_flatMap_kummerPoints (f : ℕ → ℤ) (H : ℕ) :
    ((orderedTriples H).flatMap (kummerPoints f)).Nodup := by
  refine .flatMap
    (fun (a, b, c, _) ↦ (a / gcd a (gcd b c), b / gcd a (gcd b c), c / gcd a (gcd b c)))
    (nodup_orderedTriples H) (fun ⟨a, b, c⟩ ht ↦ ?_) (fun ⟨a, b, c⟩ ht p hp ↦ ?_)
  all_goals obtain ⟨hcop, hn, -⟩ := mem_boxTriples_iff.1 (mem_orderedTriples_iff.1 ht)
  · exact (nodup_kummerRoots f a b c).map (injective_kummerPoint (by lia))
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
    simp only [gcd_mul_gcd_mul_mul_of_gcd_eq_one (Nat.cast_nonneg x.den) hcop]
    simp [x.den_ne_zero]

/- The roots of `JPoints.kummerRoots` are roots of the Kummer quadratic. -/
private theorem quadratic_eq_zero_of_mem_kummerRoots {f : ℕ → ℤ} {a b c : ℤ} {x : ℚ}
    (hx : x ∈ kummerRoots f a b c) :
    (kummerK2 a b c : ℚ) * x ^ 2 + kummerK1 f a b c * x + kummerK0 f a b c = 0 := by
  by_cases h : kummerK2 a b c = 0 ∧ kummerK1 f a b c = 0
  · simp [kummerRoots, h] at hx
  · exact (mem_kummerRoots_iff (by tauto)).1 hx

theorem kummer_eq_zero_of_mem_kummerPoints {f : ℕ → ℤ} {t : ℤ × ℤ × ℤ} {p : ℤ × ℤ × ℤ × ℤ}
    (hp : p ∈ kummerPoints f t) : kummer f p.1 p.2.1 p.2.2.1 p.2.2.2 = 0 := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  have := kummer_mul_div f a b c x.num (m := x.den) (by positivity)
  rw [Int.cast_natCast, Rat.num_div_den, quadratic_eq_zero_of_mem_kummerRoots hx, mul_zero] at this
  exact_mod_cast this

theorem isNormalized_of_mem_kummerPoints {f : ℕ → ℤ} {H : ℕ} {t : ℤ × ℤ × ℤ}
    (ht : t ∈ orderedTriples H) {p : ℤ × ℤ × ℤ × ℤ} (hp : p ∈ kummerPoints f t) :
    IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨hcop, hn, -⟩ := mem_boxTriples_iff.1 (mem_orderedTriples_iff.1 ht)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
  refine ⟨?_, by simpa [mul_pos_iff_of_pos_left, x.den_pos, x.den_ne_zero] using hn⟩
  rw [← gcd_assoc (_ * b), ← gcd_assoc,
    gcd_mul_gcd_mul_mul_of_gcd_eq_one (Nat.cast_nonneg x.den) hcop, ← Int.coe_gcd, Int.gcd_comm]
  exact_mod_cast x.reduced

end JPoints

end
