/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Check
public import JPoints.Proof.DoubleSieve
public import Std.WP

import JPoints.Mathlib.Algebra.Group.Nat.Even
import JPoints.Proof.Containers
import JPoints.Proof.DoubleArith
import JPoints.Proof.Order
import JPoints.Proof.Poly
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The loops of the double points

`find_double_points` searches the triples `(s², 2st, t²)` of the double points
(`JPoints.doubleTriples`) row by row (`JPoints.doubleRow`): for each first coordinate `a` it sets
the records of its sieving primes (`JPoints.findDoublePointsSetup_spec`) and runs over the second
coordinates `|b| ≤ min(H / (2a), ⌊√H⌋)` (`JPoints.filter_intRange_eq_toList_rcc`), checking the
triples of the coprime pairs that pass the sieve (`JPoints.findDoublePointsRows_spec`); the first
coordinates are the squares `a = aa²` for a monic quintic (`JPoints.findDoublePointsSquares_spec`),
whose other rows have no points (`JPoints.CheckGlobals.squareRowsPoints_sqrt_sqrt`), and all
`1 ≤ a ≤ ⌊√H⌋` otherwise, skipping the rows without points at the primes that divide `a`
(`JPoints.findDoublePointsAll_spec`). Each loop prints the points that it finds, only the first
under `-1`, where it stops (`JPoints.Output.Searched`).

## Main definitions

* `JPoints.doubleRowPoints`: the points over the triples of the coprime pairs of a row of the
  double points.
* `JPoints.DoubleRowsInvariant`: the invariant of the loop over the second coordinates.
* `JPoints.squareRowsPoints`, `JPoints.DoubleSquaresInvariant`: the rows of the squares, and the
  invariant of their loop.
* `JPoints.doubleRowsPoints`, `JPoints.DoubleAllInvariant`: the rows of a list of first
  coordinates, and the invariant of the loop over all of them.
* `JPoints.DoubleRecordsInvariant`: the invariant of the loop that writes the primes into the
  records.

## Main statements

* `JPoints.findDoublePointsRows_spec`, `JPoints.findDoublePointsSquares_spec`,
  `JPoints.findDoublePointsAll_spec`: the loops.
* `JPoints.findDoublePoints_spec_of_doubleSetup`: the double points.

## Implementation notes

`vcgen` copies the loop over the second coordinates into the two branches of the `if` that sets its
bound, with the ranges `-⌊√H⌋…⌊√H⌋` and `-H/(2a)…H/(2a)`; the same invariant serves both, and the
verification conditions that read the range come in two forms. The floor of the square root of the
height bound in doubles is `⌊√H⌋` by `JPoints.Double.toInt_toInt64_floor_sqrt_ofInt`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The range of the second coordinates -/

/-- The second coordinates `t` of the double points `(s², 2st, t²)` with `t² ≤ H` and `|2st| ≤ H`,
for `s > 0`: the integers of absolute value at most `min(H / (2s), ⌊√H⌋)`, in increasing order,
the range of the loop over `b` of `find_double_points`. -/
theorem filter_intRange_eq_toList_rcc (H : ℕ) {s : ℤ} (hs : 0 < s) :
    (intRange H).filter (fun t : ℤ ↦ t ^ 2 ≤ H ∧ |2 * s * t| ≤ H) =
      ((-min ((H : ℤ) / (2 * s)) (H.sqrt : ℤ))...=min ((H : ℤ) / (2 * s)) (H.sqrt : ℤ)).toList := by
  refine List.Pairwise.eq_of_mem_iff ((pairwise_lt_intRange H).filter _) Std.Rcc.pairwise_toList_lt
    fun t ↦ ?_
  have hsq : t ^ 2 ≤ H ↔ |t| ≤ H.sqrt := by
    rw [Int.abs_eq_natAbs, Nat.cast_le, Nat.le_sqrt', ← Int.natAbs_sq, ← Nat.cast_le (α := ℤ),
      Nat.cast_pow]
  have hst : |2 * s * t| ≤ H ↔ |t| ≤ (H : ℤ) / (2 * s) := by
    rw [abs_mul, abs_of_pos (by lia : 0 < 2 * s), Int.le_ediv_iff_mul_le (by lia), mul_comm]
  simp only [List.mem_filter, mem_intRange_iff, decide_eq_true_eq, Std.Rcc.mem_toList_iff_mem,
    Std.Rcc.mem_iff, hsq, hst]
  rw [← abs_le, le_min_iff]
  lia [show (H.sqrt : ℤ) ≤ H from mod_cast Nat.sqrt_le_self H]

/-! ### The rows of the double points -/

/-- The points over the triples `(a², 2ab, b²)` of the double points, for the second coordinates
`b` of `L` coprime to `a`, in their order. -/
def doubleRowPoints (gl : CheckGlobals) (a : ℤ) (L : List ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  (L.filter fun b ↦ Int.gcd a b = 1).flatMap fun b ↦ gl.points (a ^ 2, 2 * a * b, b ^ 2)

theorem flatMap_doubleRow_points (gl : CheckGlobals) {a : ℤ} (ha : 0 < a) :
    (doubleRow gl.H a).flatMap gl.points = doubleRowPoints gl a
      ((-min ((gl.H : ℤ) / (2 * a)) (gl.H.sqrt : ℤ))...=min ((gl.H : ℤ) / (2 * a))
        (gl.H.sqrt : ℤ)).toList := by
  rw [doubleRowPoints, ← filter_intRange_eq_toList_rcc gl.H ha, List.filter_filter, doubleRow,
    List.flatMap_map]
  congr 2
  funext t
  simp only [Bool.decide_and, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem doubleRowPoints_append_singleton (gl : CheckGlobals) {a b : ℤ} (L : List ℤ)
    (hab : Int.gcd a b = 1) : doubleRowPoints gl a (L ++ [b]) =
      doubleRowPoints gl a L ++ gl.points (a ^ 2, 2 * a * b, b ^ 2) := by
  simp [doubleRowPoints, hab]

theorem doubleRowPoints_append_singleton_of_gcd_ne_one (gl : CheckGlobals) {a b : ℤ} (L : List ℤ)
    (hab : Int.gcd a b ≠ 1) : doubleRowPoints gl a (L ++ [b]) = doubleRowPoints gl a L := by
  simp [doubleRowPoints, hab]

theorem doubleRowPoints_append_cons (gl : CheckGlobals) {a b : ℤ} (L R : List ℤ)
    (hab : Int.gcd a b = 1) : doubleRowPoints gl a (L ++ b :: R) =
      doubleRowPoints gl a L ++ gl.points (a ^ 2, 2 * a * b, b ^ 2) ++ doubleRowPoints gl a R := by
  simp [doubleRowPoints, hab]

/-- A triple of the double points whose first coordinate is the square of `1 ≤ s ≤ ⌊√H⌋` and whose
second coordinate is in the range of the loop over `b` of `find_double_points` is one of the box,
and the exact check may take it. -/
theorem mem_boxTriples_of_mem_toList_rcc {H : ℕ} {s t : ℤ} (hs : 1 ≤ s) (hsH : s ≤ H.sqrt)
    (ht : t ∈ ((-min ((H : ℤ) / (2 * s)) (H.sqrt : ℤ))...=min ((H : ℤ) / (2 * s))
      (H.sqrt : ℤ)).toList) (hst : Int.gcd s t = 1) :
    (s * s, 2 * s * t, t * t) ∈ boxTriples H := by
  rw [← filter_intRange_eq_toList_rcc H (by lia), List.mem_filter, decide_eq_true_eq] at ht
  have hd : (s ^ 2, 2 * s * t, t ^ 2) ∈ doubleTriples H := mem_doubleTriples_iff.mpr
    ⟨s, t, by lia, by lia [pow_le_pow_left₀ (by lia) hsH 2,
      show (H.sqrt : ℤ) ^ 2 ≤ H from mod_cast Nat.sqrt_le' H], ht.2.1, ht.2.2, hst, rfl⟩
  rw [← sq, ← sq]
  exact List.mem_of_mem_filter (mem_conicTriples_iff.mpr (.inr hd))

theorem CheckGlobals.points_mul_self (gl : CheckGlobals) (a b : ℤ) :
    gl.points (a * a, 2 * a * b, b * b) = gl.points (a ^ 2, 2 * a * b, b ^ 2) := by
  rw [sq, sq]

/-- The invariant of the loop of `JPoints.findDoublePointsRows` over the second coordinates `b`, for
the first coordinate `a`, from the output `out₀`: while it goes on, the output is `out₀` with the
points over the triples of the coprime `b` of `pref` (`JPoints.doubleRowPoints`), none under
`-1`; once it has returned at a point under `-1`, the output is `out₀` with the first point over the
triples of the row (`JPoints.doubleRow`). -/
def DoubleRowsInvariant (g : SiftGlobals) (out₀ : Output) (a : ℤ) (pref suff : List ℤ)
    (st : Option (Bool × Output) × Output) : Prop :=
  st.1.elim (out₀.Searched g.check (doubleRowPoints g.check a pref) st.2) fun r ↦ suff = [] ∧
    r.2 = out₀.appendPoints g.check (firstIf g.check.onePoint
      ((doubleRow g.check.H a).flatMap g.check.points)) ∧
    r.1 = (g.check.onePoint && !((doubleRow g.check.H a).flatMap g.check.points).isEmpty)

section DoubleRows

variable {g : SiftGlobals} {ssp0 : Array Stype} {wheight : ℤ} {out₀ : Output} {a : ℤ}

-- The precondition of `JPoints.findDoublePointsRows_spec`.
private abbrev DoubleRowsPre (g : SiftGlobals) (ssp0 : Array Stype) (wheight a : ℤ) : Prop :=
  DoubleSetup g ∧ 1 ≤ a ∧ a ≤ wheight ∧ wheight = g.check.H.sqrt ∧
    ∀ n < g.sievePrimes3, ssp0[n]! = doubleRecord g a n

-- The postcondition of `JPoints.findDoublePointsRows_spec`.
private abbrev DoubleRowsPost (g : SiftGlobals) (out₀ : Output) (a : ℤ) (r : Bool × Output) :
    Prop :=
  r.2 = out₀.appendPoints g.check (firstIf g.check.onePoint
      ((doubleRow g.check.H a).flatMap g.check.points)) ∧
    r.1 = (g.check.onePoint && !((doubleRow g.check.H a).flatMap g.check.points).isEmpty)

private theorem DoubleRowsInvariant.none_of_cons {pref suff : List ℤ} {cur : ℤ}
    {x : Option (Bool × Output)} {o : Output}
    (h : DoubleRowsInvariant g out₀ a pref (cur :: suff) (x, o)) :
    out₀.Searched g.check (doubleRowPoints g.check a pref) o :=
  (Option.eq_none_and_of_elim_cons h).2

private theorem DoubleRowsInvariant.init (l : List ℤ) :
    DoubleRowsInvariant g out₀ a [] l (none, out₀) :=
  Output.searched_nil out₀ g.check

private theorem DoubleRowsInvariant.post_some {l : List ℤ} {x : Option (Bool × Output)}
    {o : Output} {r : Bool × Output} (h : DoubleRowsInvariant g out₀ a l [] (x, o))
    (hx : x = some r) : DoubleRowsPost g out₀ a r := by
  subst hx
  exact h.2

-- The bound `min(H / (2 a), ⌊√H⌋)` of the second coordinates, in the two branches of the program.
private theorem min_eq_of_lt (h : DoubleRowsPre g ssp0 wheight a)
    (hb : wheight < g.check.height / (2 * a)) :
    min ((g.check.H : ℤ) / (2 * a)) (g.check.H.sqrt : ℤ) = wheight := by
  rw [Int.toNat_of_nonneg (by lia [h.1.check.one_le_height]), ← h.2.2.2.1]
  exact min_eq_right hb.le

private theorem min_eq_of_not_lt (h : DoubleRowsPre g ssp0 wheight a)
    (hb : ¬wheight < g.check.height / (2 * a)) :
    min ((g.check.H : ℤ) / (2 * a)) (g.check.H.sqrt : ℤ) = g.check.height / (2 * a) := by
  rw [Int.toNat_of_nonneg (by lia [h.1.check.one_le_height]), ← h.2.2.2.1]
  exact min_eq_left (not_lt.mp hb)

private theorem DoubleRowsInvariant.post_none_of_min_eq (h : DoubleRowsPre g ssp0 wheight a)
    {bmax : ℤ} (hb : min ((g.check.H : ℤ) / (2 * a)) (g.check.H.sqrt : ℤ) = bmax)
    {x : Option (Bool × Output)} {o : Output}
    (hinv : DoubleRowsInvariant g out₀ a (ForIn.toList (-bmax...=bmax)) [] (x, o))
    (hx : x = none) : DoubleRowsPost g out₀ a (false, o) := by
  subst hx
  have := Output.Searched.post (out := o) hinv
  rwa [Std.Internal.ForIn.toList_rcc, ← hb, ← flatMap_doubleRow_points g.check (by lia)] at this

private theorem doubleRows_pre_relprime (h : DoubleRowsPre g ssp0 wheight a) : 1 ≤ a :=
  h.2.1

private theorem doubleRows_pre_sieve (h : DoubleRowsPre g ssp0 wheight a) {k : ℕ}
    (hk : k < g.sievePrimes3) : 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap :=
  h.2.2.2.2 k hk ▸ h.1.pos_and_nonneg_doubleRecord hk

private theorem doubleRows_pre_check_of_min_eq (h : DoubleRowsPre g ssp0 wheight a) {bmax : ℤ}
    (hb : min ((g.check.H : ℤ) / (2 * a)) (g.check.H.sqrt : ℤ) = bmax) {pref suff : List ℤ}
    {cur : ℤ} (hl : ForIn.toList (-bmax...=bmax) = pref ++ cur :: suff) {r : Bool}
    (hr : r = decide (a.gcd cur = 1)) (hr' : r = true) :
    g.check.WF ∧ (a * a, 2 * a * cur, cur * cur) ∈ boxTriples g.check.height.toNat := by
  refine ⟨h.1.check, mem_boxTriples_of_mem_toList_rcc h.2.1 (h.2.2.2.1 ▸ h.2.2.1) ?_
    (by simpa [hr'] using hr.symm)⟩
  rw [hb, ← Std.Internal.ForIn.toList_rcc, hl]
  simp

private theorem DoubleRowsInvariant.stop_of_min_eq (h : DoubleRowsPre g ssp0 wheight a) {bmax : ℤ}
    (hb : min ((g.check.H : ℤ) / (2 * a)) (g.check.H.sqrt : ℤ) = bmax) {pref suff : List ℤ}
    {cur : ℤ} (hl : ForIn.toList (-bmax...=bmax) = pref ++ cur :: suff)
    {x : Option (Bool × Output)} {o : Output}
    (hinv : DoubleRowsInvariant g out₀ a pref (cur :: suff) (x, o)) {r₁ : Bool}
    (hr : r₁ = decide (a.gcd cur = 1)) (hr' : r₁ = true) {r : Bool} {out' : Output}
    (hc : (r, out').2 = (x, o).2.appendPoints g.check
        (firstIf g.check.onePoint (g.check.points (a * a, 2 * a * cur, cur * cur))) ∧
      (g.check.onePoint = true →
        ((r, out').1 = true ↔ ¬g.check.points (a * a, 2 * a * cur, cur * cur) = [])))
    (hstop : (r && g.check.onePoint) = true) :
    DoubleRowsInvariant g out₀ a (ForIn.toList (-bmax...=bmax)) [] (some (true, out'), out') := by
  rw [CheckGlobals.points_mul_self] at hc
  have hop : g.check.onePoint = true := ((Bool.and_eq_true _ _).mp hstop).2
  have hP := (hc.2 hop).mp ((Bool.and_eq_true _ _).mp hstop).1
  have := hinv.none_of_cons.stop hc.1 hop hP (doubleRowPoints g.check a suff)
  rw [← doubleRowPoints_append_cons _ _ _ (by simpa [hr'] using hr.symm), ← hl,
    Std.Internal.ForIn.toList_rcc, ← hb, ← flatMap_doubleRow_points g.check (by lia [h.2.1])]
    at this
  exact ⟨rfl, this.1, this.2⟩

private theorem DoubleRowsInvariant.next {pref suff : List ℤ} {cur : ℤ}
    {x : Option (Bool × Output)} {o : Output}
    (hinv : DoubleRowsInvariant g out₀ a pref (cur :: suff) (x, o)) {r₁ : Bool}
    (hr : r₁ = decide (a.gcd cur = 1)) (hr' : r₁ = true) {r : Bool} {out' : Output}
    (hc : (r, out').2 = (x, o).2.appendPoints g.check
        (firstIf g.check.onePoint (g.check.points (a * a, 2 * a * cur, cur * cur))) ∧
      (g.check.onePoint = true →
        ((r, out').1 = true ↔ ¬g.check.points (a * a, 2 * a * cur, cur * cur) = [])))
    (hstop : ¬(r && g.check.onePoint) = true) :
    DoubleRowsInvariant g out₀ a (pref ++ [cur]) suff (none, out') := by
  rw [CheckGlobals.points_mul_self] at hc
  have := hinv.none_of_cons.append hc.1 fun hop ↦ by
    have := hc.2 hop
    simp only [hop, Bool.and_true] at hstop
    tauto
  rwa [← doubleRowPoints_append_singleton _ _ (by simpa [hr'] using hr.symm)] at this

private theorem DoubleRowsInvariant.coprime_false {pref suff : List ℤ} {cur : ℤ}
    {x : Option (Bool × Output)} {o : Output}
    (hinv : DoubleRowsInvariant g out₀ a pref (cur :: suff) (x, o)) {r₁ : Bool}
    (hr : r₁ = decide (a.gcd cur = 1)) (hr' : ¬r₁ = true) :
    DoubleRowsInvariant g out₀ a (pref ++ [cur]) suff (none, o) := by
  have := hinv.none_of_cons
  rwa [← doubleRowPoints_append_singleton_of_gcd_ne_one _ _ (by simpa [hr] using hr')] at this

private theorem DoubleRowsInvariant.sieve_false (h : DoubleRowsPre g ssp0 wheight a)
    {pref suff : List ℤ} {cur : ℤ} {x : Option (Bool × Output)} {o : Output}
    (hinv : DoubleRowsInvariant g out₀ a pref (cur :: suff) (x, o)) {r₁ : Bool}
    (hr : r₁ = decide (a.gcd cur = 1)) (hr' : r₁ = true) {r₂ : Bool}
    (hs : r₂ = (List.range g.sievePrimes3).all fun k ↦ ssp0[k]!.passes g.curve cur)
    (hs' : ¬r₂ = true) : DoubleRowsInvariant g out₀ a (pref ++ [cur]) suff (none, o) := by
  have hg : a.gcd cur = 1 := by simpa [hr'] using hr.symm
  have hP : g.check.points (a ^ 2, 2 * a * cur, cur ^ 2) = [] := by
    by_contra hP
    refine hs' (hs.trans (List.all_eq_true.mpr fun k hk ↦ ?_))
    rw [h.2.2.2.2 k (List.mem_range.mp hk)]
    exact h.1.passes_of_points_ne_nil (by lia [h.2.1]) hg hP (List.mem_range.mp hk)
  change out₀.Searched g.check (doubleRowPoints g.check a (pref ++ [cur])) o
  rw [doubleRowPoints_append_singleton _ _ hg, hP, List.append_nil]
  exact hinv.none_of_cons

end DoubleRows

attribute [local irreducible] DoubleRowsInvariant in
/-- The loop of `find_double_points` over the second coordinates `b` of the first coordinate
`1 ≤ a ≤ ⌊√H⌋`, with the records of `a`, prints the points over the triples of the double points of
the row (`JPoints.doubleRow`), in their order, only the first under `-1`: those that `relprime` or
the sieve drops have none. The flag returned says whether it stopped at a point under `-1`. -/
@[spec]
theorem findDoublePointsRows_spec (g : SiftGlobals) (ssp0 : Array Stype) (wheight : ℤ)
    (out : Output) (a : ℤ) :
    ⦃ DoubleSetup g ∧ 1 ≤ a ∧ a ≤ wheight ∧ wheight = g.check.H.sqrt ∧
      ∀ n < g.sievePrimes3, ssp0[n]! = doubleRecord g a n ⦄
    findDoublePointsRows g ssp0 wheight out a
    ⦃ fun r ↦ r.2 = out.appendPoints g.check (firstIf g.check.onePoint
          ((doubleRow g.check.H a).flatMap g.check.points)) ∧
        r.1 = (g.check.onePoint && !((doubleRow g.check.H a).flatMap g.check.points).isEmpty) ⦄ :=
    by
  vcgen [findDoublePointsRows] invariants
  · DoubleRowsInvariant g out a
  · DoubleRowsInvariant g out a
  all_goals with_reducible first
    | exact DoubleRowsInvariant.init _
    | exact DoubleRowsInvariant.post_some ‹_› ‹_›
    | exact DoubleRowsInvariant.post_none_of_min_eq ‹_› (min_eq_of_lt ‹_› ‹_›) ‹_› ‹_›
    | exact DoubleRowsInvariant.post_none_of_min_eq ‹_› (min_eq_of_not_lt ‹_› ‹_›) ‹_› ‹_›
    | exact doubleRows_pre_relprime ‹_›
    | exact doubleRows_pre_sieve ‹_› ‹_›
    | exact doubleRows_pre_check_of_min_eq ‹_› (min_eq_of_lt ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact doubleRows_pre_check_of_min_eq ‹_› (min_eq_of_not_lt ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact DoubleRowsInvariant.stop_of_min_eq ‹_› (min_eq_of_lt ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DoubleRowsInvariant.stop_of_min_eq ‹_› (min_eq_of_not_lt ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_›
    | exact DoubleRowsInvariant.next ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DoubleRowsInvariant.coprime_false ‹_› ‹_› ‹_›
    | exact DoubleRowsInvariant.sieve_false ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›


/-- The points over the triples of the double points whose first coordinates are the squares of the
squares `k²`, `1 ≤ k ≤ n`, in their order: those that `find_double_points` searches for a monic
quintic. -/
def squareRowsPoints (gl : CheckGlobals) (n : ℕ) : List (ℤ × ℤ × ℤ × ℤ) :=
  (List.range' 1 n).flatMap fun k : ℕ ↦ (doubleRow gl.H ((k : ℤ) * k)).flatMap gl.points

theorem squareRowsPoints_add_one_sub_one (gl : CheckGlobals) {aa : ℤ} (h : 1 ≤ aa) :
    squareRowsPoints gl (aa + 1 - 1).toNat =
      squareRowsPoints gl (aa - 1).toNat ++ (doubleRow gl.H (aa * aa)).flatMap gl.points := by
  have hc : (aa + 1 - 1).toNat = (aa - 1).toNat + 1 := by lia
  have ha : ((1 + (aa - 1).toNat : ℕ) : ℤ) = aa := by lia
  rw [squareRowsPoints, hc, List.range'_1_concat, List.flatMap_append, List.flatMap_singleton, ha,
    ← squareRowsPoints]

theorem exists_squareRowsPoints_eq_append (gl : CheckGlobals) {aa : ℤ} (h : 1 ≤ aa) {n : ℕ}
    (hn : aa ≤ n) : ∃ R, squareRowsPoints gl n = squareRowsPoints gl (aa - 1).toNat ++
      (doubleRow gl.H (aa * aa)).flatMap gl.points ++ R := by
  refine ⟨(List.range' (1 + aa.toNat) (n - aa.toNat)).flatMap fun k : ℕ ↦
    (doubleRow gl.H ((k : ℤ) * k)).flatMap gl.points, ?_⟩
  have hk : (aa + 1 - 1).toNat = aa.toNat := by lia
  rw [← squareRowsPoints_add_one_sub_one gl h, squareRowsPoints, squareRowsPoints,
    ← List.flatMap_append, hk, List.range'_append_1]
  congr 2
  lia

/-- The invariant of the loop of `JPoints.findDoublePointsSquares` over `aa = 1, 2, …` while
`aa² ≤ w`, from the output `out₀`: while it goes on, the records hold the primes of the plan,
`(aa - 1)² ≤ w`, the output is `out₀` with the points over the rows of the squares before `aa²`
(`JPoints.squareRowsPoints`), none under `-1`, and after the loop `w < aa²`; once it has returned at
a point under `-1`, the loop is over and the output is `out₀` with the first point over the rows of
the squares up to `w`. -/
def DoubleSquaresInvariant (g : SiftGlobals) (out₀ : Output) (w : ℤ) :
    Std.WP.WhileInvariant (Option (Bool × Output) × Array Stype × Output × ℤ) Prop :=
  .mk fun exit st ↦ st.1.elim
    (DoubleRecordsWF g st.2.1 ∧ 1 ≤ st.2.2.2 ∧ (st.2.2.2 - 1) * (st.2.2.2 - 1) ≤ w ∧
      out₀.Searched g.check (squareRowsPoints g.check (st.2.2.2 - 1).toNat) st.2.2.1 ∧
      (exit = true → w < st.2.2.2 * st.2.2.2))
    fun r ↦ exit = true ∧ r.2 = out₀.appendPoints g.check
      (firstIf g.check.onePoint (squareRowsPoints g.check w.toNat.sqrt)) ∧
      r.1 = (g.check.onePoint && !(squareRowsPoints g.check w.toNat.sqrt).isEmpty)

section DoubleSquares

variable {g : SiftGlobals} {ssp0 : Array Stype} {w : ℤ} {out₀ : Output}

-- The precondition of `JPoints.findDoublePointsSquares_spec`.
private abbrev DoubleSquaresPre (g : SiftGlobals) (ssp0 : Array Stype) (w : ℤ) : Prop :=
  DoubleSetup g ∧ w = g.check.H.sqrt ∧ DoubleRecordsWF g ssp0

-- The postcondition of `JPoints.findDoublePointsSquares_spec`.
private abbrev DoubleSquaresPost (g : SiftGlobals) (out₀ : Output) (w : ℤ) (r : Bool × Output) :
    Prop :=
  r.2 = out₀.appendPoints g.check
      (firstIf g.check.onePoint (squareRowsPoints g.check w.toNat.sqrt)) ∧
    r.1 = (g.check.onePoint && !(squareRowsPoints g.check w.toNat.sqrt).isEmpty)

private theorem DoubleSquaresInvariant.init (h : DoubleSquaresPre g ssp0 w) :
    DoubleSquaresInvariant g out₀ w false (none, ssp0, out₀, 1) :=
  ⟨h.2.2, le_rfl, by lia, by simpa [squareRowsPoints] using Output.searched_nil out₀ g.check,
    nofun⟩

private theorem DoubleSquaresInvariant.post_some {x : Option (Bool × Output)} {s : Array Stype}
    {o : Output} {aa : ℤ} (h : DoubleSquaresInvariant g out₀ w true (x, s, o, aa))
    {r : Bool × Output} (hx : x = some r) : DoubleSquaresPost g out₀ w r := by
  subst hx
  exact h.2

private theorem DoubleSquaresInvariant.post_none {x : Option (Bool × Output)} {s : Array Stype}
    {o : Output} {aa : ℤ} (h : DoubleSquaresInvariant g out₀ w true (x, s, o, aa))
    (hx : x = none) : DoubleSquaresPost g out₀ w (false, o) := by
  subst hx
  obtain ⟨-, h1, h2, h3, h4⟩ := h
  have hc : ((aa - 1).toNat : ℤ) = aa - 1 := by lia
  have hw : (w.toNat : ℤ) = w := by lia [mul_self_nonneg (aa - 1)]
  have hs : (aa - 1).toNat = w.toNat.sqrt := Nat.eq_sqrt.mpr
    ⟨by zify; rwa [hc, hw], by zify; rw [hc, hw, sub_add_cancel]; exact h4 rfl⟩
  have := h3.post
  dsimp only at this
  rwa [hs] at this

private theorem DoubleSquaresInvariant.none_of_false {x : Option (Bool × Output)}
    {s : Array Stype} {o : Output} {aa : ℤ}
    (h : DoubleSquaresInvariant g out₀ w false (x, s, o, aa)) :
    DoubleRecordsWF g s ∧ 1 ≤ aa ∧ (aa - 1) * (aa - 1) ≤ w ∧
      out₀.Searched g.check (squareRowsPoints g.check (aa - 1).toNat) o := by
  cases x with
  | none => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | some r => exact absurd h.1 Bool.false_ne_true

-- The verification conditions of `JPoints.findDoublePointsSquares`, each in its shape.

private theorem doubleSquares_pre_setup (hpre : DoubleSquaresPre g ssp0 w) {aa : ℤ}
    {x : Option (Bool × Output)} {s : Array Stype} {o : Output} {mb : ℕ}
    (h : (w + 1 - aa).toNat = mb ∧ DoubleSquaresInvariant g out₀ w false (x, s, o, aa)) :
    0 ≤ aa * aa ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g s :=
  ⟨mul_self_nonneg aa, hpre.1.sievePrimes3_le, h.2.none_of_false.1⟩

private theorem doubleSquares_pre_rows (hpre : DoubleSquaresPre g ssp0 w) {aa : ℤ}
    (hc : aa * aa ≤ w) {s : Array Stype} {b : Bool}
    (hs : DoubleRecordsWF g s ∧
      (b = true → ∀ n < g.sievePrimes3, s[n]! = doubleRecord g (aa * aa) n) ∧
      (b = false → false = true ∧ ∃ n < g.sievePrimes3, aa * aa % sievingPrime g.pnn n = 0 ∧
        g.curve.hasInfinity[g.pnn[n]!]! = false))
    {x : Option (Bool × Output)} {s₀ : Array Stype} {o : Output} {mb : ℕ}
    (h : (w + 1 - aa).toNat = mb ∧ DoubleSquaresInvariant g out₀ w false (x, s₀, o, aa)) :
    DoubleSetup g ∧ 1 ≤ aa * aa ∧ aa * aa ≤ w ∧ w = g.check.H.sqrt ∧
      ∀ n < g.sievePrimes3, s[n]! = doubleRecord g (aa * aa) n := by
  have h1 := h.2.none_of_false.2.1
  refine ⟨hpre.1, by lia [Int.mul_le_mul h1 h1 zero_le_one (by lia)], hc, hpre.2.1, hs.2.1 ?_⟩
  cases b
  · exact absurd (hs.2.2 rfl).1 Bool.false_ne_true
  · rfl

private theorem DoubleSquaresInvariant.stop {aa : ℤ} (hc : aa * aa ≤ w) {s : Array Stype}
    {o out' : Output} {r : Bool}
    (hr : out' = o.appendPoints g.check (firstIf g.check.onePoint
        ((doubleRow g.check.H (aa * aa)).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleRow g.check.H (aa * aa)).flatMap g.check.points).isEmpty))
    (hrt : r = true) {x : Option (Bool × Output)} {s₀ : Array Stype} {mb : ℕ}
    (h : (w + 1 - aa).toNat = mb ∧ DoubleSquaresInvariant g out₀ w false (x, s₀, o, aa)) :
    DoubleSquaresInvariant g out₀ w true (some (true, out'), s, out', aa) := by
  obtain ⟨-, h1, -, hL⟩ := h.2.none_of_false
  have hf := hr.2 ▸ hrt
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hf
  have hn : aa ≤ (w.toNat.sqrt : ℤ) := by
    have := Nat.le_sqrt.mpr (show aa.toNat * aa.toNat ≤ w.toNat by zify; lia [mul_self_nonneg aa])
    lia
  obtain ⟨R, hR⟩ := exists_squareRowsPoints_eq_append g.check h1 hn
  have := hL.stop hr.1 hf.1 hf.2 R
  rw [← hR] at this
  exact ⟨rfl, this.1, this.2⟩

private theorem DoubleSquaresInvariant.next {aa : ℤ} (hc : aa * aa ≤ w) {s : Array Stype}
    {b : Bool} (hs : DoubleRecordsWF g s ∧ (b = true → ∀ n < g.sievePrimes3,
      s[n]! = doubleRecord g (aa * aa) n) ∧ (b = false → false = true ∧ ∃ n < g.sievePrimes3,
        aa * aa % sievingPrime g.pnn n = 0 ∧ g.curve.hasInfinity[g.pnn[n]!]! = false))
    {o out' : Output} {r : Bool}
    (hr : out' = o.appendPoints g.check (firstIf g.check.onePoint
        ((doubleRow g.check.H (aa * aa)).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleRow g.check.H (aa * aa)).flatMap g.check.points).isEmpty))
    (hrt : ¬r = true) {x : Option (Bool × Output)} {s₀ : Array Stype} {mb : ℕ}
    (h : (w + 1 - aa).toNat = mb ∧ DoubleSquaresInvariant g out₀ w false (x, s₀, o, aa)) :
    (w + 1 - (aa + 1)).toNat < mb ∧
      DoubleSquaresInvariant g out₀ w false (none, s, out', aa + 1) := by
  obtain ⟨-, h1, -, hL⟩ := h.2.none_of_false
  have hP : g.check.onePoint = true →
      (doubleRow g.check.H (aa * aa)).flatMap g.check.points = [] := fun hop ↦ by
    simpa [hr.2, hop] using hrt
  refine ⟨by lia [Int.mul_le_mul_of_nonneg_left h1 (by lia : 0 ≤ aa)], hs.1, by lia, by lia, ?_,
    nofun⟩
  rw [squareRowsPoints_add_one_sub_one g.check h1]
  exact hL.append hr.1 hP

private theorem DoubleSquaresInvariant.exit {aa : ℤ} (hc : ¬aa * aa ≤ w)
    {x : Option (Bool × Output)} {s : Array Stype} {o : Output} {mb : ℕ}
    (h : (w + 1 - aa).toNat = mb ∧ DoubleSquaresInvariant g out₀ w false (x, s, o, aa)) :
    DoubleSquaresInvariant g out₀ w true (none, s, o, aa) :=
  ⟨h.2.none_of_false.1, h.2.none_of_false.2.1, h.2.none_of_false.2.2.1, h.2.none_of_false.2.2.2,
    fun _ ↦ by lia⟩

end DoubleSquares

attribute [local irreducible] DoubleSquaresInvariant in
/-- The loop of `find_double_points` over the squares `a = aa²`, `aa = 1, 2, …` while `a ≤ ⌊√H⌋`,
prints the points over the rows of the double points of the squares up to `⌊√H⌋`
(`JPoints.squareRowsPoints`), in their order, only the first under `-1`. The flag returned says
whether it stopped at a point under `-1`. -/
@[spec]
theorem findDoublePointsSquares_spec (g : SiftGlobals) (ssp0 : Array Stype) (wheight : ℤ)
    (out : Output) :
    ⦃ DoubleSetup g ∧ wheight = g.check.H.sqrt ∧ DoubleRecordsWF g ssp0 ⦄
    findDoublePointsSquares g ssp0 wheight out
    ⦃ fun r ↦ r.2 = out.appendPoints g.check
          (firstIf g.check.onePoint (squareRowsPoints g.check wheight.toNat.sqrt)) ∧
        r.1 = (g.check.onePoint && !(squareRowsPoints g.check wheight.toNat.sqrt).isEmpty) ⦄ := by
  vcgen [findDoublePointsSquares] invariants
  · DoubleSquaresInvariant g out wheight
  · .ofMeasure fun st : Option (Bool × Output) × Array Stype × Output × ℤ ↦
      (wheight + 1 - st.2.2.2).toNat
  all_goals try dsimp only at *
  all_goals try vc_simp
  all_goals with_reducible first
    | exact DoubleSquaresInvariant.init ‹_›
    | exact DoubleSquaresInvariant.post_some ‹_› ‹_›
    | exact DoubleSquaresInvariant.post_none ‹_› ‹_›
    | exact doubleSquares_pre_setup ‹_› ‹_›
    | exact doubleSquares_pre_rows ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSquaresInvariant.stop ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSquaresInvariant.next ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSquaresInvariant.exit ‹_› ‹_›


/-- The points over the triples of the double points whose first coordinates are the squares of
the `a` of `L`, in their order. -/
def doubleRowsPoints (gl : CheckGlobals) (L : List ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  L.flatMap fun a ↦ (doubleRow gl.H a).flatMap gl.points

/-- The invariant of the loop of `JPoints.findDoublePointsAll` over the first coordinates `a`, from
the output `out₀`: while it goes on, the records hold the primes of the plan and the output is
`out₀` with the points over the rows of the `a` of `pref` (`JPoints.doubleRowsPoints`), none under
`-1`; once it has returned at a point under `-1`, the output is `out₀` with the first point over the
rows of all `1 ≤ a ≤ w`. -/
def DoubleAllInvariant (g : SiftGlobals) (out₀ : Output) (w : ℤ) (pref suff : List ℤ)
    (st : Option (Bool × Output) × Array Stype × Output) : Prop :=
  st.1.elim
    (DoubleRecordsWF g st.2.1 ∧ out₀.Searched g.check (doubleRowsPoints g.check pref) st.2.2)
    fun r ↦ suff = [] ∧ r.2 = out₀.appendPoints g.check (firstIf g.check.onePoint
        (doubleRowsPoints g.check ((1 : ℤ)...=w).toList)) ∧
      r.1 = (g.check.onePoint && !(doubleRowsPoints g.check ((1 : ℤ)...=w).toList).isEmpty)

theorem doubleRowsPoints_append (gl : CheckGlobals) (L₁ L₂ : List ℤ) :
    doubleRowsPoints gl (L₁ ++ L₂) = doubleRowsPoints gl L₁ ++ doubleRowsPoints gl L₂ :=
  List.flatMap_append

theorem doubleRowsPoints_singleton (gl : CheckGlobals) (a : ℤ) :
    doubleRowsPoints gl [a] = (doubleRow gl.H a).flatMap gl.points :=
  List.flatMap_singleton ..

/-- The rows of a first coordinate `a ≠ 0` that `find_double_points` skips, at a sieving prime that
divides `a` and modulo which the curve has no points at infinity, have no points over their
triples (`JPoints.DoubleSetup.hasInfinity_of_points_ne_nil`). -/
theorem DoubleSetup.flatMap_doubleRow_points_eq_nil {g : SiftGlobals} (hg : DoubleSetup g) {a : ℤ}
    (ha : a ≠ 0) {n : ℕ} (hn : n < g.sievePrimes3) (hd : a % sievingPrime g.pnn n = 0)
    (hi : g.curve.hasInfinity[g.pnn[n]!]! = false) :
    (doubleRow g.check.H a).flatMap g.check.points = [] := by
  refine List.flatMap_eq_nil_iff.mpr fun t ht ↦ ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have hab := (of_decide_eq_true (List.mem_filter.mp hb).2).2.2
  by_contra hp
  simp [hg.hasInfinity_of_points_ne_nil ha hab hp hn hd] at hi

section DoubleAll

variable {g : SiftGlobals} {ssp0 : Array Stype} {w : ℤ} {out₀ : Output}

-- The precondition of `JPoints.findDoublePointsAll_spec`.
private abbrev DoubleAllPre (g : SiftGlobals) (ssp0 : Array Stype) (w : ℤ) : Prop :=
  DoubleSetup g ∧ w = g.check.H.sqrt ∧ DoubleRecordsWF g ssp0

private theorem mem_of_toList_rcc_eq_append_cons {pref suff : List ℤ} {cur : ℤ}
    (hl : ForIn.toList ((1 : ℤ)...=w) = pref ++ cur :: suff) : 1 ≤ cur ∧ cur ≤ w := by
  have : cur ∈ ((1 : ℤ)...=w).toList := by simp [← Std.Internal.ForIn.toList_rcc, hl]
  simpa [Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff] using this

private theorem DoubleAllInvariant.none_of_cons {pref suff : List ℤ} {cur : ℤ}
    {x : Option (Bool × Output)} {s : Array Stype} {o : Output}
    (h : DoubleAllInvariant g out₀ w pref (cur :: suff) (x, s, o)) :
    DoubleRecordsWF g s ∧ out₀.Searched g.check (doubleRowsPoints g.check pref) o :=
  (Option.eq_none_and_of_elim_cons h).2

private theorem DoubleAllInvariant.init (h : DoubleAllPre g ssp0 w) (l : List ℤ) :
    DoubleAllInvariant g out₀ w [] l (none, ssp0, out₀) :=
  ⟨h.2.2, Output.searched_nil out₀ g.check⟩

private theorem DoubleAllInvariant.post_some {l : List ℤ} {x : Option (Bool × Output)}
    {s : Array Stype} {o : Output} (h : DoubleAllInvariant g out₀ w l [] (x, s, o))
    {r₁ : Bool} {r₂ : Output} (hx : x = some (r₁, r₂)) :
    r₂ = out₀.appendPoints g.check (firstIf g.check.onePoint
        (doubleRowsPoints g.check ((1 : ℤ)...=w).toList)) ∧
      r₁ = (g.check.onePoint && !(doubleRowsPoints g.check ((1 : ℤ)...=w).toList).isEmpty) := by
  subst hx
  exact h.2

private theorem DoubleAllInvariant.post_none {x : Option (Bool × Output)} {s : Array Stype}
    {o : Output} (h : DoubleAllInvariant g out₀ w (ForIn.toList ((1 : ℤ)...=w)) [] (x, s, o))
    (hx : x = none) :
    o = out₀.appendPoints g.check (firstIf g.check.onePoint
        (doubleRowsPoints g.check ((1 : ℤ)...=w).toList)) ∧
      false = (g.check.onePoint && !(doubleRowsPoints g.check ((1 : ℤ)...=w).toList).isEmpty) := by
  subst hx
  rw [← Std.Internal.ForIn.toList_rcc]
  exact h.2.post

private theorem doubleAll_pre_setup (hpre : DoubleAllPre g ssp0 w) {pref suff : List ℤ}
    {cur : ℤ} (hl : ForIn.toList ((1 : ℤ)...=w) = pref ++ cur :: suff)
    {x : Option (Bool × Output)} {s : Array Stype} {o : Output}
    (h : DoubleAllInvariant g out₀ w pref (cur :: suff) (x, s, o)) :
    0 ≤ cur ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g s :=
  ⟨by lia [(mem_of_toList_rcc_eq_append_cons hl).1], hpre.1.sievePrimes3_le, h.none_of_cons.1⟩

private theorem doubleAll_pre_rows (hpre : DoubleAllPre g ssp0 w) {pref suff : List ℤ}
    {cur : ℤ} (hl : ForIn.toList ((1 : ℤ)...=w) = pref ++ cur :: suff) {s : Array Stype}
    {b : Bool} (hs : DoubleRecordsWF g s ∧
      (b = true → ∀ n < g.sievePrimes3, s[n]! = doubleRecord g cur n) ∧
      (b = false → true = true ∧ ∃ n < g.sievePrimes3, cur % sievingPrime g.pnn n = 0 ∧
        g.curve.hasInfinity[g.pnn[n]!]! = false)) (hb : b = true) :
    DoubleSetup g ∧ 1 ≤ cur ∧ cur ≤ w ∧ w = g.check.H.sqrt ∧
      ∀ n < g.sievePrimes3, s[n]! = doubleRecord g cur n :=
  ⟨hpre.1, (mem_of_toList_rcc_eq_append_cons hl).1, (mem_of_toList_rcc_eq_append_cons hl).2,
    hpre.2.1, hs.2.1 hb⟩

private theorem DoubleAllInvariant.stop {pref suff : List ℤ} {cur : ℤ}
    (hl : ForIn.toList ((1 : ℤ)...=w) = pref ++ cur :: suff)
    {x : Option (Bool × Output)} {s₀ s : Array Stype} {o out' : Output}
    (h : DoubleAllInvariant g out₀ w pref (cur :: suff) (x, s₀, o)) {r : Bool}
    (hr : out' = o.appendPoints g.check (firstIf g.check.onePoint
        ((doubleRow g.check.H cur).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleRow g.check.H cur).flatMap g.check.points).isEmpty))
    (hrt : r = true) :
    DoubleAllInvariant g out₀ w (ForIn.toList ((1 : ℤ)...=w)) [] (some (true, out'), s, out') := by
  have hf := hr.2 ▸ hrt
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hf
  have := h.none_of_cons.2.stop hr.1 hf.1 hf.2 (doubleRowsPoints g.check suff)
  rw [← doubleRowsPoints_singleton, ← doubleRowsPoints_append, ← doubleRowsPoints_append,
    List.append_assoc, List.singleton_append, ← hl, Std.Internal.ForIn.toList_rcc] at this
  exact ⟨rfl, this.1, this.2⟩

private theorem DoubleAllInvariant.next {pref suff : List ℤ} {cur : ℤ}
    {x : Option (Bool × Output)} {s₀ s : Array Stype} {o out' : Output}
    (h : DoubleAllInvariant g out₀ w pref (cur :: suff) (x, s₀, o)) {b : Bool}
    (hs : DoubleRecordsWF g s ∧
      (b = true → ∀ n < g.sievePrimes3, s[n]! = doubleRecord g cur n) ∧
      (b = false → true = true ∧ ∃ n < g.sievePrimes3, cur % sievingPrime g.pnn n = 0 ∧
        g.curve.hasInfinity[g.pnn[n]!]! = false)) {r : Bool}
    (hr : out' = o.appendPoints g.check (firstIf g.check.onePoint
        ((doubleRow g.check.H cur).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleRow g.check.H cur).flatMap g.check.points).isEmpty))
    (hrt : ¬r = true) : DoubleAllInvariant g out₀ w (pref ++ [cur]) suff (none, s, out') := by
  have hP : g.check.onePoint = true →
      (doubleRow g.check.H cur).flatMap g.check.points = [] := fun hop ↦ by
    simpa [hr.2, hop] using hrt
  refine ⟨hs.1, ?_⟩
  rw [doubleRowsPoints_append, doubleRowsPoints_singleton]
  exact h.none_of_cons.2.append hr.1 hP

private theorem DoubleAllInvariant.skip (hpre : DoubleAllPre g ssp0 w) {pref suff : List ℤ}
    {cur : ℤ} (hl : ForIn.toList ((1 : ℤ)...=w) = pref ++ cur :: suff)
    {x : Option (Bool × Output)} {s₀ s : Array Stype} {o : Output}
    (h : DoubleAllInvariant g out₀ w pref (cur :: suff) (x, s₀, o)) {b : Bool}
    (hs : DoubleRecordsWF g s ∧
      (b = true → ∀ n < g.sievePrimes3, s[n]! = doubleRecord g cur n) ∧
      (b = false → true = true ∧ ∃ n < g.sievePrimes3, cur % sievingPrime g.pnn n = 0 ∧
        g.curve.hasInfinity[g.pnn[n]!]! = false)) (hb : ¬b = true) :
    DoubleAllInvariant g out₀ w (pref ++ [cur]) suff (none, s, o) := by
  obtain ⟨n, hn, hd, hi⟩ := (hs.2.2 (by simpa using hb)).2
  refine ⟨hs.1, ?_⟩
  rw [doubleRowsPoints_append, doubleRowsPoints_singleton,
    hpre.1.flatMap_doubleRow_points_eq_nil (by lia [(mem_of_toList_rcc_eq_append_cons hl).1]) hn
      hd hi, List.append_nil]
  exact h.none_of_cons.2

end DoubleAll

attribute [local irreducible] DoubleAllInvariant in
/-- The loop of `find_double_points` over the first coordinates `1 ≤ a ≤ ⌊√H⌋` prints the points
over the rows of the double points of these `a` (`JPoints.doubleRowsPoints`), in their order, only
the first under `-1`: the rows that it skips have none. The flag returned says whether it stopped at
a point under `-1`. -/
@[spec]
theorem findDoublePointsAll_spec (g : SiftGlobals) (ssp0 : Array Stype) (wheight : ℤ)
    (out : Output) :
    ⦃ DoubleSetup g ∧ wheight = g.check.H.sqrt ∧ DoubleRecordsWF g ssp0 ⦄
    findDoublePointsAll g ssp0 wheight out
    ⦃ fun r ↦ r.2 = out.appendPoints g.check
          (firstIf g.check.onePoint (doubleRowsPoints g.check ((1 : ℤ)...=wheight).toList)) ∧
        r.1 = (g.check.onePoint &&
          !(doubleRowsPoints g.check ((1 : ℤ)...=wheight).toList).isEmpty) ⦄ := by
  vcgen [findDoublePointsAll] invariants
  · DoubleAllInvariant g out wheight
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact DoubleAllInvariant.init ‹_› _
    | exact DoubleAllInvariant.post_some ‹_› ‹_›
    | exact DoubleAllInvariant.post_none ‹_› ‹_›
    | exact doubleAll_pre_setup ‹_› ‹_› ‹_›
    | exact doubleAll_pre_rows ‹_› ‹_› ‹_› ‹_›
    | exact DoubleAllInvariant.stop ‹_› ‹_› ‹_› ‹_›
    | exact DoubleAllInvariant.next ‹_› ‹_› ‹_› ‹_›
    | exact DoubleAllInvariant.skip ‹_› ‹_› ‹_› ‹_› ‹_›


/-- The invariant of the loop of `find_double_points` that writes the primes into the records: the
`NUM_PRIMES` records, those of the sieving primes of `pref` with their primes. -/
def DoubleRecordsInvariant (g : SiftGlobals) (pref _ : List ℕ) (s : Array Stype) : Prop :=
  s.size = numPrimes ∧ ∀ n < pref.length, s[n]!.p = sievingPrime g.pnn n

theorem flatMap_doubleTriples_points (gl : CheckGlobals) :
    (doubleTriples gl.H).flatMap gl.points =
      doubleRowsPoints gl ((1 : ℤ)...=(gl.H.sqrt : ℤ)).toList := by
  rw [doubleTriples, List.flatMap_assoc, Int.toList_rcc_one_natCast, doubleRowsPoints,
    List.flatMap_map]

/-- For a monic quintic, a first coordinate `s²` of a double point with a point over it is the
square of a square: `F(t, s)` is a square (`JPoints.isSquare_sexticForm_of_hasPointOver`), so
that `s` is one (`JPoints.isSquare_of_isSquare_sexticForm`). -/
theorem CheckGlobals.isSquare_of_flatMap_doubleRow_ne_nil {gl : CheckGlobals} (hgl : gl.WF)
    (hq : (gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1) = true) {s : ℕ} (hs : 1 ≤ s)
    (h : (doubleRow gl.H s).flatMap gl.points ≠ []) : IsSquare s := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have h6 : gl.coeffList.getD 6 0 = 0 := getD_eq_zero_of_degree_lt (by lia [hgl.degree_coeffList])
  have h5 : gl.coeffList.getD 5 0 = 1 :=
    (Array.getD_toList_eq_getElem! gl.curve.coeffs 5).trans hq.2
  have := isSquare_of_isSquare_sexticForm h6 (h5 ▸ isUnit_one) (by lia)
    (of_decide_eq_true (List.mem_filter.mp hb).2).2.2
    (isSquare_sexticForm_of_hasPointOver (by lia) (hasPointOver_of_pointsOver_ne_nil
      (List.ne_nil_of_mem hpt)))
  exact Int.isSquare_natCast_iff.mp this

/-- For a monic quintic, the points over the double points are those over the rows of the squares
of the squares up to `⌊√H⌋` (`JPoints.squareRowsPoints`), which `find_double_points` searches. -/
theorem CheckGlobals.squareRowsPoints_sqrt_sqrt {gl : CheckGlobals} (hgl : gl.WF)
    (hq : (gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1) = true) :
    squareRowsPoints gl gl.H.sqrt.sqrt = (doubleTriples gl.H).flatMap gl.points := by
  rw [doubleTriples, List.flatMap_assoc, squareRowsPoints,
    ← Nat.flatMap_range'_sqrt_mul_self fun s hs _ h ↦
      gl.isSquare_of_flatMap_doubleRow_ne_nil hgl hq hs h]
  simp only [Nat.cast_mul]

section DoublePoints

variable {g : SiftGlobals} {out : Output}

private theorem doubleRecordsInvariant_init (l : List ℕ) :
    DoubleRecordsInvariant g [] l (Array.replicate numPrimes {}) :=
  ⟨Array.size_replicate .., by simp⟩

private theorem DoubleRecordsInvariant.set (hg : DoubleSetup g) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff) {s : Array Stype}
    (h : DoubleRecordsInvariant g pref (cur :: suff) s) :
    DoubleRecordsInvariant g (pref ++ [cur]) suff
      (s.set! cur { p := primeTable[g.pnn[cur]!]!, ap := s[cur]!.ap, ptr := s[cur]!.ptr }) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcs : cur < s.size := by lia [hg.sievePrimes3_le, h.1]
  refine ⟨by simp [h.1], fun n hn ↦ ?_⟩
  rcases eq_or_ne cur n with rfl | hne
  · rw [Array.getElem!_set!_self _ _ _ hcs]
  · rw [Array.getElem!_set!_ne _ _ _ _ hne, h.2 n (by simp at hn; lia)]

/-- `floor(sqrt(height))` in doubles, converted to a `long`, is `⌊√H⌋` for the height bound of the
globals of the sieve (`JPoints.Double.toInt_toInt64_floor_sqrt_ofInt`). -/
theorem DoubleSetup.toInt_toInt64_floor_sqrt_ofInt (hg : DoubleSetup g) :
    (Double.ofInt g.check.height).sqrt.floor.toInt64.toInt = g.check.H.sqrt :=
  Double.toInt_toInt64_floor_sqrt_ofInt (by lia [hg.check.one_le_height])
    hg.check.height_le_maxHeight

private theorem doublePoints_pre (hg : DoubleSetup g) {s : Array Stype}
    (h : DoubleRecordsInvariant g (ForIn.toList [:g.sievePrimes3]) [] s) :
    DoubleSetup g ∧ (Double.ofInt g.check.height).sqrt.floor.toInt64.toInt = g.check.H.sqrt ∧
      DoubleRecordsWF g s :=
  ⟨hg, hg.toInt_toInt64_floor_sqrt_ofInt, h.1, fun n hn ↦ h.2 n (by simpa using hn)⟩

private theorem doublePoints_post_squares (hg : DoubleSetup g)
    (hq : (g.check.curve.degree == 5 && g.check.curve.coeffs[5]! == 1) = true) {w : ℤ}
    (hw : w = g.check.H.sqrt) {r : Bool} {o : Output}
    (h : o = out.appendPoints g.check
        (firstIf g.check.onePoint (squareRowsPoints g.check w.toNat.sqrt)) ∧
      r = (g.check.onePoint && !(squareRowsPoints g.check w.toNat.sqrt).isEmpty)) :
    o = out.appendPoints g.check (firstIf g.check.onePoint
        ((doubleTriples g.check.H).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleTriples g.check.H).flatMap g.check.points).isEmpty) := by
  rwa [hw, Int.toNat_natCast, g.check.squareRowsPoints_sqrt_sqrt hg.check hq] at h

private theorem doublePoints_post_all {w : ℤ} (hw : w = g.check.H.sqrt) {r : Bool} {o : Output}
    (h : o = out.appendPoints g.check
        (firstIf g.check.onePoint (doubleRowsPoints g.check ((1 : ℤ)...=w).toList)) ∧
      r = (g.check.onePoint && !(doubleRowsPoints g.check ((1 : ℤ)...=w).toList).isEmpty)) :
    o = out.appendPoints g.check (firstIf g.check.onePoint
        ((doubleTriples g.check.H).flatMap g.check.points)) ∧
      r = (g.check.onePoint && !((doubleTriples g.check.H).flatMap g.check.points).isEmpty) := by
  rwa [hw, ← flatMap_doubleTriples_points] at h

end DoublePoints

attribute [local irreducible] DoubleRecordsInvariant in
/-- `find_double_points` prints the points over the triples `(s², 2st, t²)` of the double points of
the search (`JPoints.doubleTriples`), in their order, only the first under `-1`, for the globals of
the sieve that it reads (`JPoints.DoubleSetup`): its loops over the squares `s` of a monic quintic,
or over all `s`, keep every row with a point, and its sieve of the pairs every pair with one. The
flag returned says whether it stopped at a point under `-1`. -/
theorem findDoublePoints_spec_of_doubleSetup (g : SiftGlobals) (out : Output) :
    ⦃ DoubleSetup g ⦄
    findDoublePoints g out
    ⦃ fun r ↦ r.2 = out.appendPoints g.check (firstIf g.check.onePoint
          ((doubleTriples g.check.H).flatMap g.check.points)) ∧
        r.1 = (g.check.onePoint && !((doubleTriples g.check.H).flatMap g.check.points).isEmpty) ⦄ :=
    by
  vcgen [findDoublePoints] invariants
  · DoubleRecordsInvariant g
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact doubleRecordsInvariant_init _
    | exact DoubleRecordsInvariant.set ‹_› ‹_› ‹_›
    | exact doublePoints_pre ‹_› ‹_›
    | exact doublePoints_post_squares ‹_› ‹_› (DoubleSetup.toInt_toInt64_floor_sqrt_ofInt ‹_›) ‹_›
    | exact doublePoints_post_all (DoubleSetup.toInt_toInt64_floor_sqrt_ofInt ‹_›) ‹_›

end JPoints

end
