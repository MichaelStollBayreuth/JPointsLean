/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Filters
public import JPoints.Proof.Globals

import JPoints.Mathlib.Algebra.Group.Nat.Even
import JPoints.Mathlib.Data.List.Basic
import JPoints.Proof.Order
import JPoints.Proof.Search
import JPoints.Proof.Sound
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

/-!
# The rows and the units of work hold the points

The tests of the main search, sound one by one (`JPoints.Proof.Sound`), drop no point from the
lists of the search. The rows of `run_a` for a first coordinate `0 ≤ a ≤ H`, from
`b₀ = m` for `a = 0` and `b₀ = -⌊H / m⌋ m` otherwise by the step `m` of `row_step`, are the rows of
the box whose second coordinate the step divides, `b > 0` for `a = 0`; with the third coordinates
that the sieve of a row keeps, in the box (`JPoints.flatMap_rowPoints_rowsFrom`) and in the bands
(`JPoints.bandsPoints_rowStart`), they hold the points over the triples of the first coordinate
(`JPoints.unitTriples`). The units of work of `find_points` hold the points of the main search
(`JPoints.flatMap_range_unitTriples_unitA`): for a monic quintic its units are the squares `k²`,
since the first coordinates that are not squares have no points over their triples.

## Main statements

* `JPoints.neg_le_rowStart`: the first row of `run_a` lies in the box.
* `JPoints.flatMap_rowPoints_rowsFrom`, `JPoints.bandsPoints_rowStart`: the rows of a first
  coordinate hold the points of its triples.
* `JPoints.flatMap_range_unitTriples_unitA`: the units of work hold the points of the main search.
-/

@[expose] public section

namespace JPoints

/-! ### The rows of a first coordinate -/

/-- The first row `b₀` of `run_a`, `m` for `a = 0` and `-⌊H / m⌋ m` otherwise, is at least `-H`. -/
theorem neg_le_rowStart {H a m : ℤ} (hH : 0 ≤ H) (hm : 1 ≤ m) :
    -H ≤ if a == 0 then m else -H.tdiv m * m := by
  split_ifs
  · lia
  · lia [Int.tdiv_eq_ediv_of_nonneg hH, Int.ediv_mul_le H (b := m) (by lia)]

-- The rows `b ≥ -H` of `run_a`: the multiples of the step `m`, and `b > 0` for `a = 0`.
private theorem rowStart_le_iff {a m H b : ℤ} (hH : 0 ≤ H) (hm : 0 < m) (hb : -H ≤ b) :
    ((if a == 0 then m else -H.tdiv m * m) ≤ b ∧
        m ∣ b - if a == 0 then m else -H.tdiv m * m) ↔ m ∣ b ∧ (a ≠ 0 ∨ 0 < b) := by
  rw [Int.tdiv_eq_ediv_of_nonneg hH]
  by_cases ha : a = 0
  · simp only [ha, beq_self_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, false_or]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa using dvd_add h2 (dvd_refl m), by lia⟩,
      fun ⟨⟨j, hj⟩, h⟩ ↦ ⟨?_, ⟨j - 1, by rw [hj]; ring⟩⟩⟩
    rw [hj] at h ⊢
    exact le_mul_of_one_le_right hm.le (pos_of_mul_pos_right h hm.le)
  · simp only [beq_iff_eq, ha, ↓reduceIte, ne_eq, not_false_eq_true, true_or, and_true]
    refine ⟨fun ⟨_, j, hj⟩ ↦ ⟨j - H / m, by linear_combination hj⟩, fun ⟨j, hj⟩ ↦ ⟨?_, ?_⟩⟩
    · have : -(H / m) ≤ j := by
        by_contra! h'
        lia [Int.lt_ediv_add_one_mul_self H hm,
          Int.mul_le_mul_of_nonneg_left (show j ≤ -(H / m) - 1 by lia) hm.le]
      lia [Int.mul_le_mul_of_nonneg_left this hm.le]
    · exact ⟨j + H / m, by linear_combination hj⟩

-- The points over the triples `(a, b, c)` of the main search with the first two coordinates `a` and
-- `b`, for the globals `gl` of the exact check, `c` increasing.
private def unitRowPoints (gl : CheckGlobals) (a b : ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  ((intRange gl.H).filter fun c ↦ gcd a (gcd b c) = 1 ∧
      (0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c)) ∧ b ^ 2 ≠ 4 * a * c).flatMap
    fun c ↦ gl.points (a, b, c)

private theorem flatMap_unitTriples_points (gl : CheckGlobals) (a : ℕ) :
    (unitTriples gl.H a).flatMap gl.points = (intRange gl.H).flatMap (unitRowPoints gl a) := by
  simp only [unitTriples, List.flatMap_assoc, List.flatMap_map]
  rfl

-- A test of the third coordinates of a row that keeps only coprime triples off the conic, and every
-- triple of the box off the conic with a point over it, leaves the points of the row.
private theorem flatMap_filter_eq_unitRowPoints {gl : CheckGlobals} {a b : ℤ} (ha : 0 ≤ a)
    (haH : a ≤ gl.H) (hb : |b| ≤ gl.H) (hab : a ≠ 0 ∨ 0 < b) {p : ℤ → Bool}
    (hp : ∀ c, p c = true → gcd a (gcd b c) = 1 ∧ b ^ 2 ≠ 4 * a * c)
    (hq : ∀ c, (a, b, c) ∈ boxTriples gl.H → b ^ 2 ≠ 4 * a * c → gl.points (a, b, c) ≠ [] →
      p c = true) :
    ((intRange gl.H).filter p).flatMap (fun c ↦ gl.points (a, b, c)) = unitRowPoints gl a b := by
  refine List.flatMap_filter_eq_flatMap_filter_of_ne (fun c _ hc ↦ ?_) fun c hc hT hpt ↦ ?_
  · obtain ⟨h1, h2⟩ := hp c hc
    simp only [decide_eq_true_eq]
    exact ⟨h1, by lia, h2⟩
  · obtain ⟨h1, h2, h3⟩ := of_decide_eq_true hT
    exact hq c (mem_boxTriples_iff.mpr
      ⟨h1, h2, (abs_of_nonneg ha).le.trans haH, hb, mem_intRange_iff.mp hc⟩) h3 hpt

private theorem rowPoints_eq_unitRowPoints {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b : ℤ} (ha : 0 ≤ a) (haH : a ≤ bg.sift.check.H)
    (hb : |b| ≤ bg.sift.check.H) (hab : a ≠ 0 ∨ 0 < b) :
    rowPoints bg.sift sd a b = unitRowPoints bg.sift.check a b :=
  flatMap_filter_eq_unitRowPoints ha haH hb hab
    (fun c hc ↦ by simp_all [colKeeps, coprimeKeeps, conic]) fun c ht hc hp ↦ by
      simp [colKeeps_of_hasPointOver h ht (hasPointOver_of_pointsOver_ne_nil hp), conic, hc]

private theorem bandRowPoints_eq_unitRowPoints {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a bFirst m b : ℤ} (ha : 0 ≤ a) (haH : a ≤ bg.sift.check.H)
    (hm : 1 ≤ m) (hbF : -bg.sift.check.height ≤ bFirst)
    (hb : b ∈ rowsFrom bFirst m bg.sift.check.height) (hb' : |b| ≤ bg.sift.check.H)
    (hab : a ≠ 0 ∨ 0 < b) :
    bandRowPoints bg sd a bFirst m b = unitRowPoints bg.sift.check a b := by
  obtain ⟨h1, -, h3⟩ := (mem_rowsFrom_iff (by lia)).mp hb
  exact flatMap_filter_eq_unitRowPoints ha haH hb' hab
    (fun c hc ↦ by simp_all [colKeeps, coprimeKeeps, conic]) fun c ht hc hp ↦ by
      simp [colKeeps_of_hasPointOver h ht (hasPointOver_of_pointsOver_ne_nil hp), conic, hc,
        bandKeeps_of_points_ne_nil h hm hbF h1 h3 ht hc hp]

private theorem rowKeeps_of_unitRowPoints_ne_nil {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b : ℤ} (hb : |b| ≤ bg.sift.check.height)
    (hne : unitRowPoints bg.sift.check a b ≠ []) :
    rowKeeps bg.sift a b = true ∧ (a ≠ 0 ∨ 0 < b) := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hp
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true (List.mem_filter.mp hc).2
  refine ⟨rowKeeps_of_hasPointOver h hb h1
    (hasPointOver_of_pointsOver_ne_nil (List.ne_nil_of_mem hpc)), ?_⟩
  rcases h2 with h2 | ⟨rfl, h2 | ⟨rfl, -⟩⟩
  · exact .inl h2.ne'
  · exact .inr h2
  · simp at h3

private theorem flatMap_unitRowPoints_rowsFrom {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a m : ℤ} (ha : 0 ≤ a) (hm : m = (rowStep bg.sift a).run) :
    ((rowsFrom (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
        bg.sift.check.height).filter (aliveKeeps bg.sift a)).flatMap
        (unitRowPoints bg.sift.check a) =
      (unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points := by
  have hH := h.check.one_le_height
  have hm1 : 1 ≤ m := hm ▸ h.one_le_rowStep a
  rw [rowsFrom_eq_filter_intRange (by lia) (neg_le_rowStart (by lia) hm1), List.filter_filter,
    List.flatMap_filter_of_ne fun b hb hne ↦ ?_]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [Int.toNat_natCast, flatMap_unitTriples_points]
  have hb' : |b| ≤ bg.sift.check.height := by lia [mem_intRange_iff.mp hb]
  obtain ⟨hk, hab⟩ := rowKeeps_of_unitRowPoints_ne_nil h hb' hne
  simp only [rowKeeps, ← hm, Bool.and_eq_true, decide_eq_true_eq] at hk ⊢
  exact ⟨hk.2, (rowStart_le_iff (by lia) (by lia) (by lia [abs_le.mp hb'])).mpr ⟨hk.1, hab⟩⟩

-- A row of `run_a` lies in the box, `b > 0` for `a = 0`.
private theorem abs_le_and_ne_zero_or_pos_of_mem_rowsFrom {H a m b : ℤ} (hH : 1 ≤ H) (hm1 : 1 ≤ m)
    (hb : b ∈ rowsFrom (if a == 0 then m else -H.tdiv m * m) m H) :
    |b| ≤ H.toNat ∧ (a ≠ 0 ∨ 0 < b) := by
  have hb₀ := neg_le_rowStart (a := a) (by lia : 0 ≤ H) hm1
  obtain ⟨h1, h2, h3⟩ := (mem_rowsFrom_iff (by lia)).mp hb
  exact ⟨abs_le.mpr ⟨by lia, by lia⟩, ((rowStart_le_iff (by lia) (by lia) (by lia)).mp ⟨h1, h3⟩).2⟩

/-- The rows of `run_a` in the box hold the points of the main search with the first coordinate
`0 ≤ a ≤ H` (`JPoints.unitTriples`): the rows from `b₀ = m` for `a = 0` and `b₀ = -⌊H / m⌋ m`
otherwise by the step `m` of `row_step` are the rows of the box whose second coordinate the step
divides, `b > 0` for `a = 0`; the rows that the step or the condition at 2 drops
(`JPoints.rowKeeps_of_hasPointOver`) and the third coordinates that the sieve of a row drops
(`JPoints.colKeeps_of_hasPointOver`) have no points over them. -/
theorem flatMap_rowPoints_rowsFrom {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a m : ℤ} (ha : 0 ≤ a) (haH : a ≤ bg.sift.check.height) (hm : m = (rowStep bg.sift a).run) :
    ((rowsFrom (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
        bg.sift.check.height).filter (aliveKeeps bg.sift a)).flatMap (rowPoints bg.sift sd a) =
      (unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points := by
  have hH := h.check.one_le_height
  rw [← flatMap_unitRowPoints_rowsFrom h ha hm]
  refine List.flatMap_congr fun b hb ↦ ?_
  obtain ⟨hb', hab⟩ := abs_le_and_ne_zero_or_pos_of_mem_rowsFrom hH (hm ▸ h.one_le_rowStep a)
    (List.mem_filter.mp hb).1
  exact rowPoints_eq_unitRowPoints h ha (by lia) hb' hab

/-- The rows of `run_a` that the sieve by bands takes hold the points of the main search with the
first coordinate `0 ≤ a ≤ H` (`JPoints.unitTriples`), as in the box
(`JPoints.flatMap_rowPoints_rowsFrom`), and the analysis of the bands drops no point
(`JPoints.bandKeeps_of_points_ne_nil`). -/
theorem bandsPoints_rowStart {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a m : ℤ} (ha : 0 ≤ a) (haH : a ≤ bg.sift.check.height) (hm : m = (rowStep bg.sift a).run) :
    bandsPoints bg sd a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m =
      (unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points := by
  have hH := h.check.one_le_height
  have hm1 : 1 ≤ m := hm ▸ h.one_le_rowStep a
  rw [bandsPoints, ← flatMap_unitRowPoints_rowsFrom h ha hm]
  refine List.flatMap_congr fun b hb ↦ ?_
  have hbr := (List.mem_filter.mp hb).1
  obtain ⟨hb', hab⟩ := abs_le_and_ne_zero_or_pos_of_mem_rowsFrom hH hm1 hbr
  exact bandRowPoints_eq_unitRowPoints h ha (by lia) hm1 (neg_le_rowStart (by lia) hm1) hbr hb' hab

/-! ### The units of work -/

private theorem isSquare_of_flatMap_unitTriples_ne_nil {gl : CheckGlobals} (hgl : gl.WF)
    (hq : (gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1) = true) {a : ℕ}
    (h : (unitTriples gl.H a).flatMap gl.points ≠ []) : IsSquare a := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
  obtain ⟨b, -, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
  have hk := unitKeeps_of_hasPointOver hgl (of_decide_eq_true (List.mem_filter.mp hc).2).1
    (hasPointOver_of_pointsOver_ne_nil (List.ne_nil_of_mem hpt))
  simpa [unitKeeps, hq] using hk

/-- The units of work `k < units` of `find_points` hold the points of the main search: for a monic
quintic, whose units are the squares `k²` (`JPoints.unitA`) with `k ≤ ⌊√H⌋`, the first coordinates
that are not squares have no points over their triples (`JPoints.unitKeeps_of_hasPointOver`); for
any other curve, the units are the first coordinates `0 ≤ a ≤ H`. -/
theorem flatMap_range_unitTriples_unitA {gl : CheckGlobals} (hgl : gl.WF) {units : ℤ}
    (hu : units = if gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1 then
      (gl.height.toNat.sqrt : ℤ) + 1 else gl.height + 1) :
    (List.range units.toNat).flatMap (fun k : ℕ ↦
        (unitTriples gl.H (unitA gl.curve k).toNat).flatMap gl.points) =
      (mainTriples gl.H).flatMap gl.points := by
  rw [mainTriples_eq, List.flatMap_assoc, hu]
  by_cases hq : (gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1) = true
  · rw [← Nat.flatMap_range_sqrt_succ_mul_self fun a _ ↦
      isSquare_of_flatMap_unitTriples_ne_nil hgl hq]
    simp only [hq, ↓reduceIte, unitA, ← Nat.cast_mul, Int.toNat_natCast,
      show ((gl.height.toNat.sqrt : ℤ) + 1).toNat = gl.H.sqrt + 1 by lia]
  · simp only [hq, Bool.false_eq_true, ↓reduceIte, unitA, Int.toNat_natCast,
      show (gl.height + 1).toNat = gl.H + 1 by lia [hgl.one_le_height]]

end JPoints

end
