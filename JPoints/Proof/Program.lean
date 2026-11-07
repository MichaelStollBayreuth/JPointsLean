/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Check
public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import JPoints.Proof.Setup
public import Std.WP

import JPoints.Mathlib.Algebra.Group.Nat.Even
import JPoints.Mathlib.Data.List.Basic
import JPoints.Proof.Containers
import JPoints.Proof.DoubleArith
import JPoints.Proof.Order
import JPoints.Proof.Region
import JPoints.Proof.Search
import JPoints.Proof.Sound
import JPoints.Proof.TwoAdic
import JPoints.Proof.UnitPoints
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import JPoints.Proof.Walk
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Std.Tactic.Do

/-!
# The contracts of the search of `find_points` and of `main`

What the search prints, in the terms of the reference layer: `find_points` prints the text of the
choice of the sieve (`JPoints.choiceText`) and then the points over the triples of the specification
(`JPoints.orderedTriples`), only the first under `-1` (`JPoints.findPoints_spec`): the points over
`(0, 0, 1)` (`JPoints.findPointsAtInfinity_spec`), the double points, and the points of the main
search over the units of work (`JPoints.runUnits_spec`), each the first coordinate `a` of the rows
of `run_a` (`JPoints.runA_spec`), whose tests drop no point (`JPoints.flatMap_rowPoints_rowsFrom`,
`JPoints.bandsPoints_rowStart`); and under `-q` the search of `main` prints these points for the
globals of the exact check that it sets (`JPoints.checkGlobalsOf`,
`JPoints.Program.mainSearch_spec`; under Sturm's theorem, unless the sieve has no primes at all,
which `-N` with a value of at most `0` gives), without `-q` the message of the curve searched, the
text of the choice for the globals of the choice that it sets (`JPoints.choiceGlobalsOf`), these
points and the closing messages (`JPoints.Program.mainSearch_spec_of_quiet_eq_false`).

## Main definitions

* `JPoints.FindPointsUnitsInvariant`, `JPoints.RunAInvariant`, `JPoints.RunUnitsInvariant`: the
  invariants of the loop of `find_points` that lowers the number of the units of work, of the loop
  of `run_a` and of that of `run_units`.
* `JPoints.checkGlobalsOf`, `JPoints.choiceGlobalsOf`: the globals of the exact check and of the
  choice of the sieve that `main` sets.

## Main statements

* `JPoints.findPointsAtInfinity_spec`: the points over `(0, 0, 1)`.
* `JPoints.findPointsUnits_spec`: the number of the units of work.
* `JPoints.runA_spec`: the rows of a first coordinate.
* `JPoints.runUnits_spec`: the main search.
* `JPoints.findPointsSetup_spec`: the set-up of the search after the choice.
* `JPoints.findPoints_spec`: the search.
* `JPoints.Program.mainSearch_spec`: the search of `main` under `-q`.
* `JPoints.Program.mainSearch_spec_of_quiet_eq_false`: the search of `main` without `-q`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. The compositions are
proved by `vcgen` from the contracts of the components, the loops with the named invariants, which
are irreducible in the proofs; each verification condition is discharged by a lemma stated in its
own shape, which `exact` applies to the hypotheses found by `‹_›`, at reducible transparency where
the shape allows it, so that the dispatch depends neither on the order of the conditions nor on the
names of their hypotheses. The lemmas name the structures that the programs build by private
abbreviations, which unfold at reducible transparency. The contract of the search of `main` without
`-q` (`JPoints.Program.mainSearch_spec_of_quiet_eq_false`) is proved from contracts by value of
`normalise_curve`, `tube_init` and `twoadic_init`, which name the results that it prints, together
with their contracts; it is not marked `@[spec]`, so that `vcgen` keeps one contract of the search
of `main`, the one under `-q`. Both contracts of the search of `main` abstract `find_points`, with
its contract (`JPoints.findPoints_spec`), before `vcgen`: the kernel, which reduces the pattern
matches on the results of the calls, would otherwise evaluate the call on the globals that `main`
builds, in a time that grows with the constants of the model (`SAMPLE_PAIRS`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The points over `(0, 0, 1)` and the units of work -/

private theorem findPointsAtInfinity_pre {gl : CheckGlobals} (hgl : gl.WF)
    (h : (gl.curve.degree == 6 && mpzPerfectSquareP gl.curve.coeffs[6]!) = true) :
    gl.WF ∧ (0, 0, 1) ∈ boxTriples gl.H ∧ gl.curve.coeffs[6]! * (4 : ℤ) ≠ 0 ∧
      (kummerK2 0 0 1 : ℚ) * (((gl.curve.coeffs[5]! * gl.curve.coeffs[5]! -
          gl.curve.coeffs[6]! * (4 : ℤ) * gl.curve.coeffs[4]! : ℤ) : ℚ) /
          ((gl.curve.coeffs[6]! * (4 : ℤ) : ℤ) : ℚ)) ^ 2 +
        kummerK1 (gl.coeffList.getD · 0) 0 0 1 * (((gl.curve.coeffs[5]! * gl.curve.coeffs[5]! -
          gl.curve.coeffs[6]! * (4 : ℤ) * gl.curve.coeffs[4]! : ℤ) : ℚ) /
          ((gl.curve.coeffs[6]! * (4 : ℤ) : ℤ) : ℚ)) +
        kummerK0 (gl.coeffList.getD · 0) 0 0 1 = 0 := by
  obtain ⟨h6, hr⟩ := CheckGlobals.kummerRoots_zero_zero_one_of_mpzPerfectSquareP hgl h
  exact checkOnePointFinal_pre_of_mem_kummerRoots hgl
    (zero_zero_one_mem_boxTriples (CheckGlobals.one_le_H hgl)) (mul_ne_zero h6 four_ne_zero)
    (hr ▸ List.mem_singleton_self _)

private theorem findPointsAtInfinity_post {gl : CheckGlobals} {x : ℚ}
    (hr : kummerRoots (gl.coeffList.getD · 0) 0 0 1 = [x]) {out : Output} {found : Bool}
    {out' : Output}
    (hf : (found, out').2 = out.appendPoints gl ([pointOfRoot 0 0 1 x].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      (found, out').1 =
        decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot 0 0 1 x))) :
    out' = out.appendPoints gl (firstIf gl.onePoint (gl.points (0, 0, 1))) ∧
      (found && gl.onePoint) = (gl.onePoint && !(gl.points (0, 0, 1)).isEmpty) := by
  obtain ⟨hout, hfound⟩ := hf
  rw [CheckGlobals.points_eq_filter_map, hr, List.map_singleton,
    firstIf_eq_self_of_length_le_one _ ((List.length_filter_le _ _).trans_eq rfl)]
  refine ⟨hout, ?_⟩
  dsimp only at hfound
  rw [hfound, List.filter_singleton]
  cases decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot 0 0 1 x)) <;>
    cases gl.onePoint <;> rfl

private theorem findPointsAtInfinity_post_none {gl : CheckGlobals} (hgl : gl.WF)
    (h : ¬(gl.curve.degree == 6 && mpzPerfectSquareP gl.curve.coeffs[6]!) = true)
    {out : Output} :
    out = out.appendPoints gl (firstIf gl.onePoint (gl.points (0, 0, 1))) ∧
      false = (gl.onePoint && !(gl.points (0, 0, 1)).isEmpty) := by
  simp [CheckGlobals.points_zero_zero_one_eq_nil hgl h]

/-- The search of `find_points` over `(0, 0, 1)` prints the point over it, if any: for a sextic
whose leading coefficient `f₆` is a square the root `(f₅² - 4 f₆ f₄) / (4 f₆)` of the Kummer
equation, checked by `check_one_point_final`; otherwise there is none, since a quintic has none
(`K₁ = K₂ = 0`) and a point over `(0, 0, 1)` lifts only for a square `f₆`. The flag returned says
whether it stopped at a point under `-1`. -/
@[spec]
theorem findPointsAtInfinity_spec (gl : CheckGlobals) (out : Output) :
    ⦃ gl.WF ⦄
    findPointsAtInfinity gl out
    ⦃ fun r ↦ r.2 = out.appendPoints gl (firstIf gl.onePoint (gl.points (0, 0, 1))) ∧
        r.1 = (gl.onePoint && !(gl.points (0, 0, 1)).isEmpty) ⦄ := by
  vcgen [findPointsAtInfinity]
  all_goals with_reducible first
    | exact findPointsAtInfinity_pre ‹_› ‹_›
    | exact findPointsAtInfinity_post
        (CheckGlobals.kummerRoots_zero_zero_one_of_mpzPerfectSquareP ‹_› ‹_›).2 ‹_›
    | exact findPointsAtInfinity_post_none ‹_› ‹_›

/-! ### The number of the units of work -/

/-- The invariant of the loop of `JPoints.findPointsUnits` that lowers the number of the units of
work while the first coordinate of the last unit exceeds the height bound `H`: the number stays
`u₀`, whose last unit has a first coordinate of at most `H`, so that the loop never runs. -/
def FindPointsUnitsInvariant (curve : SearchCurve) (height u₀ : ℤ) :
    Std.WP.WhileInvariant ℤ Prop :=
  .mk fun _ u ↦ u = u₀ ∧ unitA curve (u₀ - 1) ≤ height

-- The last unit `⌊√H⌋` or `H` of the units of work has a first coordinate of at most `H`.
private theorem unitA_sub_one_le (curve : SearchCurve) {height : ℤ} (h : 0 ≤ height) :
    unitA curve ((if (curve.degree == 5 && curve.coeffs[5]! == 1) = true then
      (height.toNat.sqrt : ℤ) + 1 else height + 1) - 1) ≤ height := by
  simp only [unitA]
  split_ifs
  · rw [add_sub_cancel_right, ← Nat.cast_mul]
    lia [Nat.sqrt_le height.toNat]
  · lia

private theorem FindPointsUnitsInvariant.init {curve : SearchCurve} {height : ℤ}
    (h : 1 ≤ height ∧ height ≤ maxHeight) :
    FindPointsUnitsInvariant curve height (if (curve.degree == 5 && curve.coeffs[5]! == 1) = true
        then (height.toNat.sqrt : ℤ) + 1 else height + 1) false
      (if (curve.degree == 5 && curve.coeffs[5]! == 1) = true then
        (Double.ofInt height).sqrt.floor.toInt64.toInt + 1 else height + 1) := by
  rw [Double.toInt_toInt64_floor_sqrt_ofInt (by lia) h.2]
  exact ⟨rfl, unitA_sub_one_le curve (by lia)⟩

private theorem FindPointsUnitsInvariant.post {curve : SearchCurve} {height u₀ u : ℤ}
    (h : FindPointsUnitsInvariant curve height u₀ true u) : u = u₀ :=
  h.1

private theorem FindPointsUnitsInvariant.sub_one {curve : SearchCurve} {height u₀ u : ℤ} {m : ℕ}
    (hc : (decide (0 < u) && decide (height < unitA curve (u - 1))) = true)
    (h : u.toNat = m ∧ FindPointsUnitsInvariant curve height u₀ false u) :
    (u - 1).toNat < m ∧ FindPointsUnitsInvariant curve height u₀ false (u - 1) := by
  obtain ⟨-, rfl, h⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  lia

private theorem FindPointsUnitsInvariant.exit {curve : SearchCurve} {height u₀ u : ℤ} {m : ℕ}
    (h : u.toNat = m ∧ FindPointsUnitsInvariant curve height u₀ false u) :
    FindPointsUnitsInvariant curve height u₀ true u :=
  h.2

attribute [local irreducible] FindPointsUnitsInvariant in
/-- The number of the units of work of `find_points`: `⌊√H⌋ + 1` for a monic quintic, whose units
are the squares, since the floor of the square root in doubles of the `H ≤ MAX_HEIGHT` is exact
(`JPoints.Double.toInt_toInt64_floor_sqrt_ofInt`), and `H + 1` otherwise, which the loop that
lowers it then keeps. -/
@[spec]
theorem findPointsUnits_spec (curve : SearchCurve) (height : ℤ) :
    ⦃ 1 ≤ height ∧ height ≤ maxHeight ⦄
    findPointsUnits curve height
    ⦃ fun r ↦ r = if curve.degree == 5 && curve.coeffs[5]! == 1 then
        (height.toNat.sqrt : ℤ) + 1 else height + 1 ⦄ := by
  vcgen [findPointsUnits] invariants
  · FindPointsUnitsInvariant curve height (if curve.degree == 5 && curve.coeffs[5]! == 1 then
        (height.toNat.sqrt : ℤ) + 1 else height + 1)
  · .ofMeasure fun u : ℤ ↦ u.toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact FindPointsUnitsInvariant.init ‹_›
    | exact FindPointsUnitsInvariant.post ‹_›
    | exact FindPointsUnitsInvariant.sub_one ‹_› ‹_›
    | exact FindPointsUnitsInvariant.exit ‹_›

/-! ### The rows of a first coordinate -/

private theorem abs_add_mul_le_of_lt_toNat {H b₀ m : ℤ} (hb₀ : -H ≤ b₀) (hm : 0 < m) {k : ℕ}
    (hk : k < ((H - b₀) / m + 1).toNat) : |b₀ + k * m| ≤ H := by
  obtain ⟨h1, h2, -⟩ := (mem_rowsFrom_iff hm).mp (mem_rowsFrom_of_lt hk)
  exact abs_le.mpr ⟨by lia, h2⟩

private theorem one_le_rowStart_add_mul {H a m : ℤ} (hm : 1 ≤ m) (k : ℕ) (ha : a = 0) :
    1 ≤ (if a == 0 then m else -H.tdiv m * m) + k * m := by
  simp only [ha, beq_self_eq_true, ↓reduceIte]
  lia [Int.mul_nonneg (Int.natCast_nonneg k) (by lia : (0 : ℤ) ≤ m)]

/-- The invariant of the loop of `run_a` over the rows `b₀ + k m` of the first coordinate `a` in the
box, from the state `s`: while no point has stopped the search, after the rows `k` of `pref` the
state is consistent and its output is that of `s` with the points that the sieve found in the rows
that the condition at 2 leaves (`JPoints.rowPoints`), none under `-1`; once a point has stopped it
under `-1`, the state is consistent and its output is that of `s` with the first point over the
triples of the first coordinate `a` (`JPoints.unitTriples`), as `JPoints.runA_spec` says. -/
noncomputable def RunAInvariant (bg : BandGlobals) (sd : SiftData) (s : SiftState) (a b₀ m : ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ s' ↦ s'.WF bg sd ∧ s'.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint (((pref.map fun k : ℕ ↦ b₀ + k * m).filter
          (aliveKeeps bg.sift a)).flatMap (rowPoints bg.sift sd a))) ∧
      (bg.sift.check.onePoint = true → ((pref.map fun k : ℕ ↦ b₀ + k * m).filter
        (aliveKeeps bg.sift a)).flatMap (rowPoints bg.sift sd a) = []))
    (fun r _ ↦ r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint
          ((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points)) ∧
      r.1 = (bg.sift.check.onePoint &&
        !((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points).isEmpty))

section RunA

variable {bg : BandGlobals} {sd : SiftData} {s : SiftState} {a b₀ m : ℤ}

-- The points that the sieve finds in the rows `b₀ + k m` of `k ∈ pref` that the condition at 2
-- leaves.
private abbrev runAPoints (bg : BandGlobals) (sd : SiftData) (a b₀ m : ℤ) (pref : List ℕ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  ((pref.map fun k : ℕ ↦ b₀ + k * m).filter (aliveKeeps bg.sift a)).flatMap (rowPoints bg.sift sd a)

-- The postcondition of `JPoints.runA_spec`.
private abbrev RunAPost (bg : BandGlobals) (sd : SiftData) (s : SiftState) (a : ℤ)
    (r : Bool × SiftState) : Prop :=
  r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
      ((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points)) ∧
    r.1 = (bg.sift.check.onePoint &&
      !((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points).isEmpty)

private theorem runAInvariant_none {pref suff : List ℕ} {s' : SiftState} :
    RunAInvariant bg sd s a b₀ m pref suff (none, s') ↔ s'.WF bg sd ∧
      s'.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint (runAPoints bg sd a b₀ m pref)) ∧
      (bg.sift.check.onePoint = true → runAPoints bg sd a b₀ m pref = []) := by
  simp [RunAInvariant]

private theorem runAInvariant_some {pref suff : List ℕ} {r : Bool × SiftState} {s' : SiftState} :
    RunAInvariant bg sd s a b₀ m pref suff (some r, s') ↔ suff = [] ∧ RunAPost bg sd s a r := by
  simp [RunAInvariant]

private theorem RunAInvariant.none_of_cons {pref suff : List ℕ} {cur : ℕ}
    {st : Option (Bool × SiftState) × SiftState}
    (h : RunAInvariant bg sd s a b₀ m pref (cur :: suff) st) :
    RunAInvariant bg sd s a b₀ m pref (cur :: suff) (none, st.2) := by
  obtain ⟨x, s'⟩ := st
  cases x with
  | none => exact h
  | some r => simp [runAInvariant_some] at h

private theorem runAPoints_append_cons {pref suff : List ℕ} {cur : ℕ}
    (h : aliveKeeps bg.sift a (b₀ + cur * m) = true) :
    runAPoints bg sd a b₀ m (pref ++ cur :: suff) = runAPoints bg sd a b₀ m pref ++
      rowPoints bg.sift sd a (b₀ + cur * m) ++ runAPoints bg sd a b₀ m suff := by
  simp [runAPoints, h]

private theorem runAPoints_append_singleton {pref : List ℕ} {cur : ℕ}
    (h : aliveKeeps bg.sift a (b₀ + cur * m) = true) :
    runAPoints bg sd a b₀ m (pref ++ [cur]) =
      runAPoints bg sd a b₀ m pref ++ rowPoints bg.sift sd a (b₀ + cur * m) := by
  simp [runAPoints, h]

private theorem aliveKeeps_of_not {g : SiftGlobals} {a b : ℤ}
    (h : ¬(g.twoAdic.use2 && a != 0 && !g.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) =
      true) : aliveKeeps g a b = true := by
  rw [aliveKeeps_eq_not, Bool.not_eq_true']
  exact Bool.eq_false_iff.mpr h

-- The verification conditions of `JPoints.runA`, each in its shape.

private theorem runA_pre_rowStep
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height) :
    1 ≤ bg.sift.check.height ∧ ∀ n < bg.sift.sievePrimes3, bg.sift.pnn[n]! < numPrimes :=
  h.1.one_le_height_and_pnn_lt

private theorem runA_pre_siftBands
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height)
    (hm : m = (rowStep bg.sift a).run ∧ 1 ≤ m ∧ m ≤ bg.sift.check.height + 1)
    (hmode : (bg.sieveMode != 0) = true) :
    IsSieveSetup bg sd ∧ s.WF bg sd ∧ ¬bg.sieveMode = 0 ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ∧
      1 ≤ m ∧ (-bg.sift.check.height ≤ if a == 0 then m else -bg.sift.check.height.tdiv m * m) ∧
      (a = 0 → 1 ≤ if a == 0 then m else -bg.sift.check.height.tdiv m * m) :=
  ⟨h.1, h.2.1, bne_iff_ne.mp hmode, h.2.2.1, h.2.2.2, hm.2.1,
    neg_le_rowStart (by lia [h.1.check.one_le_height]) hm.2.1, fun h0 ↦ by simpa [h0] using hm.2.1⟩

private theorem runA_post_siftBands
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height)
    (hm : m = (rowStep bg.sift a).run ∧ 1 ≤ m ∧ m ≤ bg.sift.check.height + 1)
    {r : Bool × SiftState}
    (hr : r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
        (bandsPoints bg sd a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m)) ∧
      r.1 = (bg.sift.check.onePoint && !(bandsPoints bg sd a
        (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m).isEmpty)) :
    RunAPost bg sd s a r := by
  rwa [bandsPoints_rowStart h.1 h.2.2.1 h.2.2.2 hm.1] at hr

private theorem RunAInvariant.init
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height) (l : List ℕ) :
    RunAInvariant bg sd s a b₀ m [] l (none, s) :=
  runAInvariant_none.mpr ⟨h.2.1, by simp [runAPoints], by simp [runAPoints]⟩

private theorem RunAInvariant.post_some {l : List ℕ} {st : Option (Bool × SiftState) × SiftState}
    {r : Bool × SiftState} (h : RunAInvariant bg sd s a b₀ m l [] st) (hx : st.1 = some r) :
    RunAPost bg sd s a r := by
  obtain ⟨x, s'⟩ := st
  obtain rfl : x = some r := hx
  exact (runAInvariant_some.mp h).2

private theorem RunAInvariant.post_none
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height)
    (hm : m = (rowStep bg.sift a).run ∧ 1 ≤ m ∧ m ≤ bg.sift.check.height + 1)
    {st : Option (Bool × SiftState) × SiftState}
    (hinv : RunAInvariant bg sd s a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
      (ForIn.toList [:((bg.sift.check.height - if a == 0 then m else
        -bg.sift.check.height.tdiv m * m) / m + 1).toNat]) [] st)
    (hx : st.1 = none) : RunAPost bg sd s a (false, st.2) := by
  obtain ⟨x, s'⟩ := st
  obtain rfl : x = none := hx
  obtain ⟨hwf, hout, hnil⟩ := runAInvariant_none.mp hinv
  have hP : runAPoints bg sd a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
      (ForIn.toList [:((bg.sift.check.height - if a == 0 then m else
        -bg.sift.check.height.tdiv m * m) / m + 1).toNat]) =
      (unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points := by
    rw [Std.Legacy.Range.toList_eq_range]
    exact flatMap_rowPoints_rowsFrom h.1 h.2.2.1 h.2.2.2 hm.1
  rw [hP] at hout hnil
  refine ⟨hwf, hout, ?_⟩
  cases hop : bg.sift.check.onePoint
  · rfl
  · simp [hnil hop]

private theorem RunAInvariant.skip {pref suff : List ℕ} {cur : ℕ}
    {st : Option (Bool × SiftState) × SiftState}
    (hinv : RunAInvariant bg sd s a b₀ m pref (cur :: suff) st)
    (hskip : (bg.sift.twoAdic.use2 && a != 0 && !bg.sift.twoAdic.alive2[(a % 64).toNat * 64 +
      ((b₀ + cur * m) % 64).toNat]!) = true) :
    RunAInvariant bg sd s a b₀ m (pref ++ [cur]) suff (none, st.2) := by
  have hna : aliveKeeps bg.sift a (b₀ + cur * m) = false := by
    simpa [aliveKeeps_eq_not] using hskip
  have hP : runAPoints bg sd a b₀ m (pref ++ [cur]) = runAPoints bg sd a b₀ m pref := by
    simp [runAPoints, hna]
  exact runAInvariant_none.mpr (hP ▸ runAInvariant_none.mp hinv.none_of_cons)

private theorem RunAInvariant.pre_sift
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height)
    (hm : m = (rowStep bg.sift a).run ∧ 1 ≤ m ∧ m ≤ bg.sift.check.height + 1)
    {pref suff : List ℕ} {cur : ℕ} {st : Option (Bool × SiftState) × SiftState}
    (hl : ForIn.toList [:((bg.sift.check.height - if a == 0 then m else
      -bg.sift.check.height.tdiv m * m) / m + 1).toNat] = pref ++ cur :: suff)
    (hinv : RunAInvariant bg sd s a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m pref
      (cur :: suff) st) :
    IsSieveSetup bg sd ∧ st.2.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ∧
      |(if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m| ≤ bg.sift.check.height ∧
      (a = 0 → 1 ≤ (if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m) :=
  ⟨h.1, (runAInvariant_none.mp hinv.none_of_cons).1, h.2.2.1, h.2.2.2,
    abs_add_mul_le_of_lt_toNat (neg_le_rowStart (by lia [h.1.check.one_le_height]) hm.2.1)
      (by lia) (Std.Legacy.Range.lt_of_toList_eq_append_cons hl), one_le_rowStart_add_mul hm.2.1 _⟩

private theorem RunAInvariant.next {pref suff : List ℕ} {cur : ℕ}
    {st : Option (Bool × SiftState) × SiftState}
    (hinv : RunAInvariant bg sd s a b₀ m pref (cur :: suff) st)
    (hskip : ¬(bg.sift.twoAdic.use2 && a != 0 && !bg.sift.twoAdic.alive2[(a % 64).toNat * 64 +
      ((b₀ + cur * m) % 64).toNat]!) = true) {found : Bool} {s' : SiftState}
    (hsift : SiftState.WF bg sd (found, s').2 ∧ (found, s').2.out = st.2.out.appendPoints
        bg.sift.check (firstIf bg.sift.check.onePoint (rowPoints bg.sift sd a (b₀ + cur * m))) ∧
      (found, s').1 = (bg.sift.check.onePoint &&
        !(rowPoints bg.sift sd a (b₀ + cur * m)).isEmpty))
    (hstop : ¬(found && bg.sift.check.onePoint) = true) :
    RunAInvariant bg sd s a b₀ m (pref ++ [cur]) suff (none, s') := by
  obtain ⟨hwf, hout, hfound⟩ := hsift
  obtain ⟨-, h2, h3⟩ := runAInvariant_none.mp hinv.none_of_cons
  rw [runAInvariant_none, runAPoints_append_singleton (aliveKeeps_of_not hskip)]
  refine ⟨hwf, ?_, fun hop ↦ ?_⟩
  · rw [hout, h2, Output.appendPoints_appendPoints, firstIf_append_of_imp h3]
  · have hR : rowPoints bg.sift sd a (b₀ + cur * m) = [] := by
      simp only at hfound
      simpa [hop, hfound] using hstop
    rw [hR, h3 hop, List.append_nil]

private theorem RunAInvariant.stop
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height)
    (hm : m = (rowStep bg.sift a).run ∧ 1 ≤ m ∧ m ≤ bg.sift.check.height + 1)
    {pref suff : List ℕ} {cur : ℕ} {st : Option (Bool × SiftState) × SiftState}
    (hl : ForIn.toList [:((bg.sift.check.height - if a == 0 then m else
      -bg.sift.check.height.tdiv m * m) / m + 1).toNat] = pref ++ cur :: suff)
    (hinv : RunAInvariant bg sd s a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m pref
      (cur :: suff) st)
    (hskip : ¬(bg.sift.twoAdic.use2 && a != 0 && !bg.sift.twoAdic.alive2[(a % 64).toNat * 64 +
      (((if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m) % 64).toNat]!) = true)
    {found : Bool} {s' : SiftState}
    (hsift : SiftState.WF bg sd (found, s').2 ∧ (found, s').2.out = st.2.out.appendPoints
        bg.sift.check (firstIf bg.sift.check.onePoint (rowPoints bg.sift sd a
          ((if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m))) ∧
      (found, s').1 = (bg.sift.check.onePoint && !(rowPoints bg.sift sd a
          ((if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m)).isEmpty))
    (hstop : (found && bg.sift.check.onePoint) = true) :
    RunAInvariant bg sd s a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
      (ForIn.toList [:((bg.sift.check.height - if a == 0 then m else
        -bg.sift.check.height.tdiv m * m) / m + 1).toNat]) [] (some (true, s'), s') := by
  obtain ⟨hwf, hout, hfound⟩ := hsift
  simp only at hwf hout hfound
  obtain ⟨-, h2, h3⟩ := runAInvariant_none.mp hinv.none_of_cons
  have hU := flatMap_rowPoints_rowsFrom h.1 h.2.2.1 h.2.2.2 hm.1
  rw [rowsFrom, ← Std.Legacy.Range.toList_eq_range, hl] at hU
  rw [← runAPoints, runAPoints_append_cons (aliveKeeps_of_not hskip)] at hU
  have hop : bg.sift.check.onePoint = true := ((Bool.and_eq_true _ _).mp hstop).2
  have hR : rowPoints bg.sift sd a
      ((if a == 0 then m else -bg.sift.check.height.tdiv m * m) + cur * m) ≠ [] := by
    intro hR
    rw [hfound, hR] at hstop
    simp at hstop
  refine runAInvariant_some.mpr ⟨rfl, hwf, ?_, ?_⟩
  · dsimp only
    rw [hout, h2, Output.appendPoints_appendPoints, ← hU, firstIf_append_of_ne_nil hop h3 hR]
  · have : (unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points ≠ [] := by
      rw [← hU]
      exact fun h ↦ hR (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
    simpa [hop, List.isEmpty_iff] using this

attribute [local irreducible] RunAInvariant in
/-- `run_a` prints the points over the triples of the main search with the first coordinate
`0 ≤ a ≤ H` (`JPoints.unitTriples`), in their order, only the first under `-1`: in the box, the
rows `(a, b)` of the step `m` of `row_step` that the condition at 2 leaves, each sieved by
`JPoints.sift`; in the tube or the real region, the rows sieved by `JPoints.siftBands`; the rows and
the third coordinates that the tests drop have no points over them. The flag returned says whether
it stopped at a point under `-1`. -/
@[spec]
theorem runA_spec (bg : BandGlobals) (sd : SiftData) (s : SiftState) (a : ℤ) :
    ⦃ IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ⦄
    runA bg sd s a
    ⦃ fun r ↦ r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check
          (firstIf bg.sift.check.onePoint
            ((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points)) ∧
        r.1 = (bg.sift.check.onePoint &&
          !((unitTriples bg.sift.check.H a.toNat).flatMap bg.sift.check.points).isEmpty) ⦄ := by
  vcgen [runA] invariants
  · RunAInvariant bg sd s a (if a == 0 then m else -bg.sift.check.height.tdiv m * m) m
  all_goals with_reducible first
    | exact runA_pre_rowStep ‹_›
    | exact runA_pre_siftBands ‹_› ‹_› ‹_›
    | exact runA_post_siftBands ‹_› ‹_› ‹_›
    | exact RunAInvariant.init ‹_› _
    | exact RunAInvariant.post_some ‹_› ‹_›
    | exact RunAInvariant.post_none ‹_› ‹_› ‹_› ‹_›
    | exact RunAInvariant.skip ‹_› ‹_›
    | exact RunAInvariant.pre_sift ‹_› ‹_› ‹_› ‹_›
    | exact RunAInvariant.stop ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact RunAInvariant.next ‹_› ‹_› ‹_› ‹_›

end RunA

/-! ### The units of work -/

/-- The invariant of the loop of `run_units` over the units of work from the state `s`: after the
units `k` of `pref`, the state is consistent and its output is that of `s` with the points over the
triples of their first coordinates (`JPoints.unitA`, `JPoints.unitTriples`), and under `-1` there
are none unless the loop has stopped at one, when no unit is left (`suff = []`). -/
def RunUnitsInvariant (bg : BandGlobals) (sd : SiftData) (s : SiftState) (pref suff : List ℕ)
    (s' : SiftState) : Prop :=
  s'.WF bg sd ∧ s'.out = s.out.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
      (pref.flatMap fun k : ℕ ↦
        (unitTriples bg.sift.check.H (unitA bg.sift.check.curve k).toNat).flatMap
          bg.sift.check.points)) ∧
    (bg.sift.check.onePoint = true → suff ≠ [] → pref.flatMap (fun k : ℕ ↦
      (unitTriples bg.sift.check.H (unitA bg.sift.check.curve k).toNat).flatMap
        bg.sift.check.points) = [])

section RunUnits

variable {bg : BandGlobals} {sd : SiftData} {s : SiftState} {units : ℤ}

private theorem RunUnitsInvariant.init
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ units = if bg.sift.check.curve.degree == 5 &&
      bg.sift.check.curve.coeffs[5]! == 1 then (bg.sift.check.height.toNat.sqrt : ℤ) + 1
      else bg.sift.check.height + 1) (l : List ℕ) :
    RunUnitsInvariant bg sd s [] l s :=
  ⟨h.2.1, by simp, by simp⟩

private theorem RunUnitsInvariant.post
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ units = if bg.sift.check.curve.degree == 5 &&
      bg.sift.check.curve.coeffs[5]! == 1 then (bg.sift.check.height.toNat.sqrt : ℤ) + 1
      else bg.sift.check.height + 1) {s' : SiftState}
    (hinv : RunUnitsInvariant bg sd s (ForIn.toList [:units.toNat]) [] s') (t : Totals) :
    (t, s').2.WF bg sd ∧ (t, s').2.out = s.out.appendPoints bg.sift.check
      (firstIf bg.sift.check.onePoint
        ((mainTriples bg.sift.check.H).flatMap bg.sift.check.points)) := by
  obtain ⟨hwf, hout, -⟩ := hinv
  rw [Std.Legacy.Range.toList_eq_range, flatMap_range_unitTriples_unitA h.1.check h.2.2] at hout
  exact ⟨hwf, hout⟩

private theorem RunUnitsInvariant.pre_runA
    (h : IsSieveSetup bg sd ∧ s.WF bg sd ∧ units = if bg.sift.check.curve.degree == 5 &&
      bg.sift.check.curve.coeffs[5]! == 1 then (bg.sift.check.height.toNat.sqrt : ℤ) + 1
      else bg.sift.check.height + 1) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:units.toNat] = pref ++ cur :: suff) {s' : SiftState}
    (hinv : RunUnitsInvariant bg sd s pref (cur :: suff) s') :
    IsSieveSetup bg sd ∧ s'.WF bg sd ∧ 0 ≤ unitA bg.sift.check.curve cur ∧
      unitA bg.sift.check.curve cur ≤ bg.sift.check.height := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hH := h.1.check.one_le_height
  refine ⟨h.1, hinv.1, ?_⟩
  rw [h.2.2] at hc
  by_cases hq : (bg.sift.check.curve.degree == 5 && bg.sift.check.curve.coeffs[5]! == 1) = true
  · simp only [hq, ↓reduceIte] at hc
    have := Nat.le_sqrt.mp (show cur ≤ bg.sift.check.height.toNat.sqrt by lia)
    simp only [unitA, hq, ↓reduceIte]
    exact ⟨by positivity, by lia⟩
  · simp only [hq, Bool.false_eq_true, ↓reduceIte] at hc
    simp only [unitA, hq, Bool.false_eq_true, ↓reduceIte]
    lia

private theorem RunUnitsInvariant.stop {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:units.toNat] = pref ++ cur :: suff) {s' : SiftState}
    (hinv : RunUnitsInvariant bg sd s pref (cur :: suff) s') {found : Bool} {s'' : SiftState}
    (hrun : (found, s'').2.WF bg sd ∧ (found, s'').2.out = s'.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint ((unitTriples bg.sift.check.H
          (unitA bg.sift.check.curve cur).toNat).flatMap bg.sift.check.points)) ∧
      (found, s'').1 = (bg.sift.check.onePoint && !((unitTriples bg.sift.check.H
          (unitA bg.sift.check.curve cur).toNat).flatMap bg.sift.check.points).isEmpty))
    (hstop : (found && bg.sift.check.onePoint) = true) :
    RunUnitsInvariant bg sd s (ForIn.toList [:units.toNat]) [] s'' := by
  obtain ⟨hwf, hout, hfound⟩ := hrun
  simp only at hwf hout hfound
  obtain ⟨-, h2, h3⟩ := hinv
  have hop : bg.sift.check.onePoint = true := ((Bool.and_eq_true _ _).mp hstop).2
  have hV : (unitTriples bg.sift.check.H (unitA bg.sift.check.curve cur).toNat).flatMap
      bg.sift.check.points ≠ [] := by
    intro hV
    rw [hfound, hV] at hstop
    simp at hstop
  refine ⟨hwf, ?_, fun _ h ↦ absurd rfl h⟩
  rw [hout, h2, Output.appendPoints_appendPoints, hl, List.flatMap_append, List.flatMap_cons,
    ← List.append_assoc, firstIf_append_of_ne_nil hop (fun _ ↦ h3 hop (by simp)) hV]

private theorem RunUnitsInvariant.next {pref suff : List ℕ} {cur : ℕ} {s' : SiftState}
    (hinv : RunUnitsInvariant bg sd s pref (cur :: suff) s') {found : Bool} {s'' : SiftState}
    (hrun : (found, s'').2.WF bg sd ∧ (found, s'').2.out = s'.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint ((unitTriples bg.sift.check.H
          (unitA bg.sift.check.curve cur).toNat).flatMap bg.sift.check.points)) ∧
      (found, s'').1 = (bg.sift.check.onePoint && !((unitTriples bg.sift.check.H
          (unitA bg.sift.check.curve cur).toNat).flatMap bg.sift.check.points).isEmpty))
    (hstop : ¬(found && bg.sift.check.onePoint) = true) :
    RunUnitsInvariant bg sd s (pref ++ [cur]) suff s'' := by
  obtain ⟨hwf, hout, hfound⟩ := hrun
  simp only at hwf hout hfound
  obtain ⟨-, h2, h3⟩ := hinv
  have h3' := fun hop ↦ h3 hop (List.cons_ne_nil _ _)
  refine ⟨hwf, ?_, fun hop _ ↦ ?_⟩
  · rw [hout, h2, Output.appendPoints_appendPoints, firstIf_append_of_imp h3', List.flatMap_append,
      List.flatMap_singleton]
  · have hV : (unitTriples bg.sift.check.H (unitA bg.sift.check.curve cur).toNat).flatMap
        bg.sift.check.points = [] := by
      simpa [hop, hfound, List.isEmpty_iff] using hstop
    rw [List.flatMap_append, List.flatMap_singleton, hV, h3' hop, List.append_nil]

attribute [local irreducible] RunUnitsInvariant in
/-- `run_units` prints the points over the triples of the main search off the conic
(`JPoints.mainTriples`), in their order, only the first under `-1`, for the number of the units of
work of `find_points` (`JPoints.findPointsUnits_spec`): the units are the first coordinates
`0 ≤ a ≤ H`, the squares for a monic quintic, and the others have no points over their triples. -/
@[spec]
theorem runUnits_spec (bg : BandGlobals) (sd : SiftData) (s : SiftState) (units : ℤ) :
    ⦃ IsSieveSetup bg sd ∧ s.WF bg sd ∧
      units = if bg.sift.check.curve.degree == 5 && bg.sift.check.curve.coeffs[5]! == 1 then
        (bg.sift.check.height.toNat.sqrt : ℤ) + 1 else bg.sift.check.height + 1 ⦄
    runUnits bg sd s units
    ⦃ fun r ↦ r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint
          ((mainTriples bg.sift.check.H).flatMap bg.sift.check.points)) ⦄ := by
  vcgen [runUnits] invariants
  · RunUnitsInvariant bg sd s
  all_goals with_reducible first
    | exact RunUnitsInvariant.init ‹_› _
    | exact RunUnitsInvariant.post ‹_› ‹_› _
    | exact RunUnitsInvariant.pre_runA ‹_› ‹_› ‹_›
    | exact RunUnitsInvariant.stop ‹_› ‹_› ‹_› ‹_›
    | exact RunUnitsInvariant.next ‹_› ‹_› ‹_›

end RunUnits

/-! ### The search -/

section FindPointsSetup

variable {g : SearchGlobals} {plan₀ : Plan} {sd : SiftData} {out : Output}

-- The plan and the condition at 2 that the search reads after the choice of the plan `plan`.
private abbrev setupPlan (g : SearchGlobals) (plan : Plan) : Plan × TwoAdic :=
  if plan.sievePrimes3 == 0 then ({ plan with sieveMode := 0 }, { g.choice.two with use2 := false })
  else (plan, g.choice.two)

-- The globals of the sieve that `JPoints.findPointsSetup` sets up.
private abbrev setupSiftGlobals (g : SearchGlobals) (ct : CurveTables) (sieve : SieveTables)
    (p : Plan) (two : TwoAdic) : SiftGlobals :=
  { tables := g.tables, curve := ct, sieve, check := g.check, arraySize := g.arraySize
    twoAdic := two, pnn := p.pnn, sievePrimes1 := p.sievePrimes1
    sievePrimes2 := p.sievePrimes2, sievePrimes3 := p.sievePrimes3, begmask := g.begmask
    endmask := g.endmask }

-- The globals of the sieve by bands that `JPoints.findPointsSetup` sets up.
private abbrev setupBandGlobals (g : SearchGlobals) (ct : CurveTables) (sieve : SieveTables)
    (p : Plan) (two : TwoAdic) : BandGlobals :=
  { sift := setupSiftGlobals g ct sieve p two, sieveMode := p.sieveMode, tubeCut := p.tubeCut
    neg := g.neg, kd := g.kd }

private theorem isSearchSetup_setupBandGlobals {ct : CurveTables} {prec : Array Entry}
    {plan : Plan} {sieve : SieveTables} {sd' : SiftData} (hg : IsSearchGlobals g)
    (hc : IsChoice g.choice ct prec plan) (hs : sieve.WF ct plan.pnn plan.sievePrimes2)
    {p : Plan} {two : TwoAdic} (hp : p.pnn = plan.pnn ∧ p.sievePrimes1 = plan.sievePrimes1 ∧
      p.sievePrimes2 = plan.sievePrimes2 ∧ p.sievePrimes3 = plan.sievePrimes3)
    (hmode : p.sieveMode ≤ 2) (h1 : p.sieveMode = 1 → g.choice.input.dbounded = true)
    (h0 : plan.sievePrimes3 = 0 → p.sieveMode = 0 ∧ two.use2 = false)
    (htwo : two.Sound g.check.coeffList) (hsd : sd'.WF (setupSiftGlobals g ct sieve p two)) :
    IsSearchSetup g (setupBandGlobals g ct sieve p two) sd' := by
  obtain ⟨pnn, sp1, sp2, sp3, mode, cut⟩ := p
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
  have hct : ct.WF g.check.coeffList g.check.curve.degree g.choice.input.numPrimes.toNat plan.pnn
      plan.sievePrimes3 := by
    rw [CheckGlobals.coeffList, ← hg.curve_eq]
    exact hc.curveTables
  exact { toIsSieveStages := hc.toIsSieveStages, check_eq := rfl, tables_eq := rfl
          curveTables := hct, sieveMode_le := hmode
          dbounded_of_sieveMode_eq_one := fun h ↦ hg.dbounded_eq ▸ h1 h
          sieveMode_eq_zero_of_sievePrimes3_eq_zero := fun h ↦ (h0 h).1
          use2_eq_false_of_sievePrimes3_eq_zero := fun h ↦ (h0 h).2
          sieve := hs, siftData := hsd
          twoAdic := htwo, neg_eq := rfl, kd_eq := rfl, arraySize_eq := rfl, begmask_eq := rfl
          endmask_eq := rfl }

private theorem isSearchSetup_setupPlan {ct : CurveTables} {prec : Array Entry}
    {plan : Plan} {sieve : SieveTables} {sd' : SiftData} (hg : IsSearchGlobals g)
    (hc : IsChoice g.choice ct prec plan) (hs : sieve.WF ct plan.pnn plan.sievePrimes2)
    (hsd : sd'.WF (setupSiftGlobals g ct sieve (setupPlan g plan).1 (setupPlan g plan).2)) :
    IsSearchSetup g (setupBandGlobals g ct sieve (setupPlan g plan).1 (setupPlan g plan).2)
      sd' := by
  by_cases h0 : plan.sievePrimes3 = 0
  · have hp : setupPlan g plan =
        ({ plan with sieveMode := 0 }, { g.choice.two with use2 := false }) := by
      simp [setupPlan, h0]
    rw [hp] at hsd ⊢
    exact isSearchSetup_setupBandGlobals hg hc hs ⟨rfl, rfl, rfl, rfl⟩ (by simp) (by simp)
      (fun _ ↦ ⟨rfl, rfl⟩) (TwoAdic.sound_of_use2_eq_false rfl _) hsd
  · have hp : setupPlan g plan = (plan, g.choice.two) := by simp [setupPlan, h0]
    rw [hp] at hsd ⊢
    exact isSearchSetup_setupBandGlobals hg hc hs ⟨rfl, rfl, rfl, rfl⟩ (hc.sieveMode_le h0)
      (hc.dbounded_of_sieveMode_eq_one h0) (fun h ↦ absurd h h0) hg.two hsd

-- The postcondition of `JPoints.initFmodpsquare_spec` for the globals of the search.
private abbrev ChoicePost (g : SearchGlobals) (plan₀ : Plan)
    (r : CurveTables × Array Entry × Plan × String) : Prop :=
  IsChoice g.choice r.1 r.2.1 r.2.2.1 ∧ r.2.2.2 = choiceText g.tables g.choice plan₀

-- The verification conditions of `JPoints.findPointsSetup`, each in its shape.

private theorem findPointsSetup_pre_choice
    (h : IsSearchGlobals g ∧ plan₀.pnn.size = numPrimes + 1 ∧ sd.Sized) :
    g.tables.WF ∧ g.choice.input.WF ∧ g.choice.curve.coeffs.size = 7 ∧
      degree g.choice.curve.coeffs.toList = g.choice.curve.degree ∧ 5 ≤ g.choice.curve.degree ∧
      plan₀.pnn.size = numPrimes + 1 := by
  obtain ⟨hg, hp, -⟩ := h
  rw [hg.curve_eq]
  exact ⟨hg.tables, hg.input, hg.check.size_coeffs, hg.check.degree_coeffList,
    hg.check.five_le_degree, hp⟩

private theorem findPointsSetup_pre_sieve
    (h : IsSearchGlobals g ∧ plan₀.pnn.size = numPrimes + 1 ∧ sd.Sized) {ct : CurveTables}
    {prec : Array Entry} {plan : Plan} {text : String}
    (hc : ChoicePost g plan₀ (ct, prec, plan, text)) :
    g.tables.WF ∧ plan.sievePrimes2 ≤ numPrimes ∧
      (∀ n < plan.sievePrimes2, plan.pnn[n]! < numPrimes) ∧
      ∀ n < plan.sievePrimes2, sievingPrime plan.pnn n ≤ maxTablePrime := by
  have hn := h.1.input.numPrimes_le
  have := hc.1.sievePrimes2_le_sievePrimes3
  have := hc.1.sievePrimes3_le_numPrimes
  exact ⟨h.1.tables, by lia, fun n hn' ↦ by lia [hc.1.pnn_lt (n := n) (by lia)],
    fun _ ↦ hc.1.sievingPrime_le_maxTablePrime⟩

private theorem findPointsSetup_rate {ct : CurveTables} {prec : Array Entry} {plan : Plan}
    {text : String} (hc : ChoicePost g plan₀ (ct, prec, plan, text))
    (h : (decide (0 < plan.sievePrimes3) && prec[0]!.r.beq Double.zero) = true) : False := by
  simp [hc.1.beq_zero_eq_false] at h

private theorem findPointsSetup_pre_sift
    (h : IsSearchGlobals g ∧ plan₀.pnn.size = numPrimes + 1 ∧ sd.Sized) {ct : CurveTables}
    {prec : Array Entry} {plan : Plan} {text : String}
    (hc : ChoicePost g plan₀ (ct, prec, plan, text)) :
    sd.Sized ∧ (setupPlan g plan).1.sievePrimes1 ≤ (setupPlan g plan).1.sievePrimes2 ∧
      (setupPlan g plan).1.sievePrimes2 ≤ (setupPlan g plan).1.sievePrimes3 ∧
      (setupPlan g plan).1.sievePrimes3 ≤ numPrimes ∧
      ∀ n < (setupPlan g plan).1.sievePrimes3, (setupPlan g plan).1.pnn[n]! < numPrimes := by
  have hn := h.1.input.numPrimes_le
  have := hc.1.sievePrimes3_le_numPrimes
  have hp : (setupPlan g plan).1 = { plan with sieveMode := (setupPlan g plan).1.sieveMode } := by
    simp only [setupPlan]
    split <;> rfl
  rw [hp]
  exact ⟨h.2.2, hc.1.sievePrimes1_le_sievePrimes2, hc.1.sievePrimes2_le_sievePrimes3, by lia,
    fun n hn' ↦ by lia [hc.1.pnn_lt hn']⟩

private theorem findPointsSetup_post
    (h : IsSearchGlobals g ∧ plan₀.pnn.size = numPrimes + 1 ∧ sd.Sized) {ct : CurveTables}
    {prec : Array Entry} {plan : Plan} {text : String}
    (hc : ChoicePost g plan₀ (ct, prec, plan, text)) {sieve : SieveTables}
    (hs : sieve.WF ct plan.pnn plan.sievePrimes2) {sd' : SiftData}
    (hsd : sd'.WF (setupSiftGlobals g ct sieve (setupPlan g plan).1 (setupPlan g plan).2)) :
    (∃ bg sd'', (some (setupBandGlobals g ct sieve (setupPlan g plan).1 (setupPlan g plan).2, sd'),
        out.print text).1 = some (bg, sd'') ∧ IsSearchSetup g bg sd'') ∧
      out.print text = out.print (choiceText g.tables g.choice plan₀) :=
  ⟨⟨_, _, rfl, isSearchSetup_setupPlan h.1 hc.1 hs hsd⟩, congr(out.print $(hc.2))⟩

/-- The set-up of the search of `find_points` makes the globals of the sieve by bands and the static
data of the sieve that the search reads (`JPoints.IsSearchSetup`), for every value of the `Float`s
of the cost model, and prints the text of the choice (`JPoints.choiceText`): the end of the search
at a best rate of `0` is never taken. -/
@[spec]
theorem findPointsSetup_spec (g : SearchGlobals) (plan : Plan) (sd : SiftData) (out : Output) :
    ⦃ IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ⦄
    findPointsSetup g plan sd out
    ⦃ fun r ↦ (∃ bg sd', r.1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
        r.2 = out.print (choiceText g.tables g.choice plan) ⦄ := by
  vcgen [findPointsSetup]
  -- the precondition of `init_sift` reads the fields of the literal of the globals of the sieve,
  -- which `exact` reduces at the default transparency only
  all_goals first
    | with_reducible first
      | exact findPointsSetup_pre_choice ‹_›
      | exact findPointsSetup_pre_sieve ‹_› ‹_›
      | exact (findPointsSetup_rate ‹_› ‹_›).elim
      | exact findPointsSetup_post ‹_› ‹_› ‹_› ‹_›
    | exact findPointsSetup_pre_sift ‹_› ‹_›

end FindPointsSetup

section FindPoints

variable {g : SearchGlobals} {plan : Plan} {sd : SiftData} {t : TubeState} {out₀ : Output}

private theorem isSearchSetup_of_eq_some {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    {bg : BandGlobals} {sd' : SiftData} (hx : setup = some (bg, sd')) : IsSearchSetup g bg sd' := by
  obtain ⟨⟨bg', sd'', h, hs⟩, -⟩ := hsetup
  obtain rfl : setup = _ := h
  cases hx
  exact hs

-- The verification conditions of `JPoints.findPoints`, each in its shape.

private theorem findPoints_pre_setup
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF) :
    IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized :=
  ⟨h.1, h.2.1, h.2.2.1⟩

private theorem findPoints_pre_infinity
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF) : g.check.WF :=
  h.1.check

private theorem findPoints_pre_units
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF) :
    1 ≤ g.check.height ∧ g.check.height ≤ maxHeight :=
  ⟨h.1.check.one_le_height, h.1.check.height_le_maxHeight⟩

private theorem findPoints_pre_double
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF)
    {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    {bg : BandGlobals} {sd' : SiftData} (hx : setup = some (bg, sd')) : ∃ sd, IsSieveSetup bg sd :=
  ⟨sd', g, h.1, isSearchSetup_of_eq_some hsetup hx⟩

private theorem findPoints_none {setup x : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    (hnone : ∀ bg sd, x = some (bg, sd) → False) (hx : setup = x) : False := by
  obtain ⟨⟨bg, sd', h, -⟩, -⟩ := hsetup
  exact hnone bg sd' (hx ▸ h)

private theorem findPoints_pre_runUnits
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF)
    {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    {bg : BandGlobals} {sd' : SiftData} (hx : setup = some (bg, sd')) (out : Output) {units : ℤ}
    (hu : units = if g.check.curve.degree == 5 && g.check.curve.coeffs[5]! == 1 then
      (g.check.height.toNat.sqrt : ℤ) + 1 else g.check.height + 1) :
    IsSieveSetup bg sd' ∧
      SiftState.WF bg sd' { SiftState.initial g.arraySize with tube := t, out } ∧
      units = if bg.sift.check.curve.degree == 5 && bg.sift.check.curve.coeffs[5]! == 1 then
        (bg.sift.check.height.toNat.sqrt : ℤ) + 1 else bg.sift.check.height + 1 := by
  have hs := isSearchSetup_of_eq_some hsetup hx
  refine ⟨⟨g, h.1, hs⟩, ?_, hs.check_eq ▸ hu⟩
  rw [← hs.arraySize_eq]
  exact SiftState.wf_initial ⟨g, h.1, hs⟩ h.2.2.2 out

private theorem findPoints_post_infinity
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF)
    {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan)) {stop : Bool} {out : Output}
    (hinf : (stop, out).2 = out₁.appendPoints g.check
        (firstIf g.check.onePoint (g.check.points (0, 0, 1))) ∧
      (stop, out).1 = (g.check.onePoint && !(g.check.points (0, 0, 1)).isEmpty))
    (hstop : stop = true) :
    out = (out₀.print (choiceText g.tables g.choice plan)).appendPoints g.check
      (firstIf g.check.onePoint ((orderedTriples g.check.H).flatMap g.check.points)) := by
  obtain ⟨hout, hflag⟩ := hinf
  simp only [hstop] at hout hflag
  obtain ⟨hop, hne⟩ : g.check.onePoint = true ∧ g.check.points (0, 0, 1) ≠ [] := by
    simpa [List.isEmpty_iff] using hflag.symm
  have h1 : out₁ = out₀.print (choiceText g.tables g.choice plan) := hsetup.2
  rw [hout, h1, flatMap_orderedTriples (by lia [h.1.check.one_le_height]), List.append_assoc,
    firstIf_append]
  simp [hop, hne]

private theorem findPoints_post_double
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF)
    {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    {bg : BandGlobals} {sd' : SiftData} (hx : setup = some (bg, sd')) {stop : Bool} {out₂ : Output}
    (hinf : (stop, out₂).2 = out₁.appendPoints g.check
        (firstIf g.check.onePoint (g.check.points (0, 0, 1))) ∧
      (stop, out₂).1 = (g.check.onePoint && !(g.check.points (0, 0, 1)).isEmpty))
    (hstop : ¬stop = true) {found : Bool} {out : Output}
    (hdbl : (found, out).2 = out₂.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
        ((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points)) ∧
      (found, out).1 = (bg.sift.check.onePoint &&
        !((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points).isEmpty))
    (hfound : (found && g.check.onePoint) = true) :
    out = (out₀.print (choiceText g.tables g.choice plan)).appendPoints g.check
      (firstIf g.check.onePoint ((orderedTriples g.check.H).flatMap g.check.points)) := by
  rw [(isSearchSetup_of_eq_some hsetup hx).check_eq] at hdbl
  obtain ⟨⟨hout₂, hst⟩, hout, hfd⟩ := And.intro hinf hdbl
  simp only at hout₂ hst hout hfd
  obtain ⟨hf, hop⟩ := (Bool.and_eq_true _ _).mp hfound
  have hL0 : g.check.points (0, 0, 1) = [] := by simpa [hst, hop, List.isEmpty_iff] using hstop
  have hLD : (doubleTriples g.check.H).flatMap g.check.points ≠ [] := by
    simpa [hf, hop, List.isEmpty_iff] using hfd
  have h1 : out₁ = out₀.print (choiceText g.tables g.choice plan) := hsetup.2
  rw [hout, hout₂, h1, Output.appendPoints_appendPoints,
    flatMap_orderedTriples (by lia [h.1.check.one_le_height]),
    firstIf_append_of_ne_nil hop (fun _ ↦ hL0) hLD]

private theorem findPoints_post
    (h : IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF)
    {setup : Option (BandGlobals × SiftData)} {out₁ : Output}
    (hsetup : (∃ bg sd', (setup, out₁).1 = some (bg, sd') ∧ IsSearchSetup g bg sd') ∧
      (setup, out₁).2 = out₀.print (choiceText g.tables g.choice plan))
    {bg : BandGlobals} {sd' : SiftData} (hx : setup = some (bg, sd')) {stop : Bool} {out₂ : Output}
    (hinf : (stop, out₂).2 = out₁.appendPoints g.check
        (firstIf g.check.onePoint (g.check.points (0, 0, 1))) ∧
      (stop, out₂).1 = (g.check.onePoint && !(g.check.points (0, 0, 1)).isEmpty))
    (hstop : ¬stop = true) {found : Bool} {out : Output}
    (hdbl : (found, out).2 = out₂.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
        ((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points)) ∧
      (found, out).1 = (bg.sift.check.onePoint &&
        !((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points).isEmpty))
    (hfound : ¬(found && g.check.onePoint) = true) {totals : Totals} {s : SiftState}
    (hrun : SiftState.WF bg sd' (totals, s).2 ∧ (totals, s).2.out =
      ({ SiftState.initial g.arraySize with tube := t, out } : SiftState).out.appendPoints
        bg.sift.check (firstIf bg.sift.check.onePoint
          ((mainTriples bg.sift.check.H).flatMap bg.sift.check.points))) :
    s.out = (out₀.print (choiceText g.tables g.choice plan)).appendPoints g.check
      (firstIf g.check.onePoint ((orderedTriples g.check.H).flatMap g.check.points)) := by
  rw [(isSearchSetup_of_eq_some hsetup hx).check_eq] at hdbl hrun
  obtain ⟨⟨hout₂, hst⟩, ⟨hout, hfd⟩, -, hs⟩ := And.intro hinf (And.intro hdbl hrun)
  simp only at hout₂ hst hout hfd hs
  have hL0 (hop : g.check.onePoint = true) : g.check.points (0, 0, 1) = [] := by
    simpa [hst, hop, List.isEmpty_iff] using hstop
  have hLD (hop : g.check.onePoint = true) :
      (doubleTriples g.check.H).flatMap g.check.points = [] := by
    simpa [hfd, hop, List.isEmpty_iff] using hfound
  have h1 : out₁ = out₀.print (choiceText g.tables g.choice plan) := hsetup.2
  rw [hs, hout, hout₂, h1, Output.appendPoints_appendPoints, Output.appendPoints_appendPoints,
    firstIf_append_of_imp hLD, firstIf_append_of_imp hL0, ← List.append_assoc,
    flatMap_orderedTriples (by lia [h.1.check.one_le_height])]

/-- `find_points` prints the text of the choice of the sieve (`JPoints.choiceText`) and then the
points over the triples of the specification (`JPoints.orderedTriples`), in their order, only the
first under `-1`: the point over `(0, 0, 1)`, the double points and the points of the main search.
-/
@[spec]
theorem findPoints_spec (g : SearchGlobals) (plan : Plan) (sd : SiftData) (t : TubeState)
    (out : Output) :
    ⦃ IsSearchGlobals g ∧ plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ t.WF ⦄
    findPoints g plan sd t out
    ⦃ fun r ↦ r.2 = (out.print (choiceText g.tables g.choice plan)).appendPoints g.check
        (firstIf g.check.onePoint ((orderedTriples g.check.H).flatMap g.check.points)) ⦄ := by
  vcgen [findPoints]
  all_goals with_reducible first
    | exact findPoints_pre_setup ‹_›
    | exact findPoints_pre_infinity ‹_›
    | exact findPoints_pre_units ‹_›
    | exact findPoints_pre_double ‹_› ‹_› ‹_›
    | exact findPoints_pre_runUnits ‹_› ‹_› ‹_› _ ‹_›
    | exact findPoints_post_infinity ‹_› ‹_› ‹_› ‹_›
    | exact findPoints_post_double ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact findPoints_post ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact (findPoints_none ‹_› ‹_› ‹_›).elim

end FindPoints

/-! ### `main` -/

/-- The globals of the exact check that `main` sets for the globals `input` that `read_input`
leaves: the curve searched of the specification (`JPoints.searchedCurve`), which `normalise_curve`
makes, the coefficients of `kummer_init` for it, and the bounds and the flags of the command line.
-/
def checkGlobalsOf (input : Cli.Input) : CheckGlobals where
  curve := searchedCurve input.coeffs.toList
  kummer := kummerInit (searchedCurve input.coeffs.toList).coeffs
  height := input.height
  dbound := input.dbound
  dbounded := input.dbounded
  allPoints := input.allPoints
  onePoint := input.onePoint
  printFormat := input.printFormat

/-- The globals of the choice of the sieve that `main` sets for the globals `input` that
`read_input` leaves: the command line, the curve searched of the specification
(`JPoints.searchedCurve`), the number of the negative intervals and the statistics of the sample
that `tube_init` leaves for the globals of the exact check (`JPoints.checkGlobalsOf`), and the
condition at 2 of `twoadic_init` from the height bound `500` on. -/
def choiceGlobalsOf (input : Cli.Input) : ChoiceGlobals where
  input
  curve := searchedCurve input.coeffs.toList
  numNeg := (tubeInit (checkGlobalsOf input) {} SiftData.initial TubeState.initial).run.2.2.1.numNeg
  stats := (tubeInit (checkGlobalsOf input) {} SiftData.initial TubeState.initial).run.2.2.2.2.2
  two := if 500 ≤ input.height then
      (twoadicInit (checkGlobalsOf input).curve.coeffs (checkGlobalsOf input).kummer
        TwoAdic.initial).run
    else TwoAdic.initial

namespace Program

/-- The size of the bit array in words that `main` computes for a nonnegative height bound and a
positive number of kilobytes is positive. -/
private theorem one_le_toNat_mainArraySize {height kb : ℤ} (hh : 0 ≤ height) (hk : 1 ≤ kb) :
    1 ≤ (mainArraySize height kb).toNat := by
  simp only [mainArraySize, ceilDiv, longShift, longLength]
  split_ifs <;> simp <;> lia

section MainSearch

variable {t : Tables} {input : Cli.Input}

-- The globals of the exact check that `JPoints.Program.mainSearch` sets for the curve searched.
private abbrev mainCheck (input : Cli.Input) (curve : SearchCurve) : CheckGlobals :=
  { curve, kummer := kummerInit curve.coeffs, height := input.height, dbound := input.dbound
    dbounded := input.dbounded, allPoints := input.allPoints, onePoint := input.onePoint
    printFormat := input.printFormat }

-- The globals of the search that `JPoints.Program.mainSearch` sets.
private abbrev mainGlobals (t : Tables) (input : Cli.Input) (curve : SearchCurve)
    (neg : NegativeIntervals) (stats : TubeStats) (two : TwoAdic) (kd : TubeCoeffs) :
    SearchGlobals :=
  { tables := t, choice := { input, curve, numNeg := neg.numNeg, stats, two }
    check := mainCheck input curve, neg, kd
    arraySize := (mainArraySize input.height input.arraySize).toNat
    begmask := (mainMasks input.height).1, endmask := (mainMasks input.height).2 }

-- The postcondition of `JPoints.normalizeCurve_spec` for the globals of the command line.
private abbrev NormalizePost (input : Cli.Input) (r : SearchCurve × String) : Prop :=
  r.1 = searchedCurve input.coeffs.toList ∧ r.1.coeffs.size = 7 ∧
    degree r.1.coeffs.toList = r.1.degree ∧ 5 ≤ r.1.degree ∧
    (Squarefree (poly input.coeffs.toList) → Squarefree (poly r.1.coeffs.toList)) ∧
    (input.quiet = true → r.2 = "")

-- The postcondition of `JPoints.tubeInit_spec` for the globals of `JPoints.Program.mainSearch`.
private abbrev TubeInitPost (gl : CheckGlobals)
    (r : TubeCoeffs × Plan × NegativeIntervals × SiftData × TubeState × TubeStats) : Prop :=
  r.1 = (tubeInitCoeffs gl.curve gl.kummer).run ∧ r.2.1 = { ({} : Plan) with sieveMode := 0 } ∧
    r.2.2.1 = (realRootsInit gl.curve.coeffs gl.curve.degree).run ∧
    (SiftData.initial.Sized → r.2.2.2.1.Sized) ∧ r.2.2.2.2.1.WF

private theorem mainCheck_wf (hi : input.WF) {curve : SearchCurve} (h7 : curve.coeffs.size = 7)
    (hd : degree curve.coeffs.toList = curve.degree) (h5 : 5 ≤ curve.degree) :
    (mainCheck input curve).WF :=
  ⟨h7, hd, h5, rfl, hi.one_le_height, hi.height_le_maxHeight, fun _ ↦ hi.one_le_dbound,
    hi.allPoints_of_dbounded_eq_false⟩

-- The verification conditions of `JPoints.Program.mainSearch`, each in its shape.

private theorem mainSearch_pre_normalize {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem)) :
    input.coeffs.size = 7 ∧ degree input.coeffs.toList = input.degree.toNat ∧
      5 ≤ input.degree.toNat :=
  ⟨h.2.1.size_coeffs, by lia [h.2.1.degree_coeffs], by lia [h.2.1.five_le_degree]⟩

private theorem mainSearch_pre_tubeInit {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String} (hn : NormalizePost input (curve, text)) :
    (mainCheck input curve).WF ∧ TubeState.initial.WF :=
  ⟨mainCheck_wf h.2.1 hn.2.1 hn.2.2.1 hn.2.2.2.1, TubeState.wf_initial⟩

private theorem mainSearch_pre_twoadic {curve : SearchCurve} {text : String}
    (hn : NormalizePost input (curve, text)) :
    curve.coeffs.size = 7 ∧ 5 ≤ degree curve.coeffs.toList :=
  ⟨hn.2.1, hn.2.2.1 ▸ hn.2.2.2.1⟩

private theorem mainSearch_pre_findPoints {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String} (hn : NormalizePost input (curve, text))
    {kd : TubeCoeffs} {plan : Plan} {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState}
    {stats : TubeStats} (ht : TubeInitPost (mainCheck input curve) (kd, plan, neg, sd, tube, stats))
    {two : TwoAdic} (htwo : two.Sound curve.coeffs.toList) :
    IsSearchGlobals (mainGlobals t input curve neg stats two kd) ∧
      plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ tube.WF := by
  obtain ⟨htab, hi, -, hS⟩ := h
  obtain ⟨-, h7, hd, h5, hsq, -⟩ := hn
  obtain ⟨hkd, hplan, hneg, hsd, htube⟩ := ht
  refine ⟨⟨mainCheck_wf hi h7 hd h5, hi, rfl, rfl, rfl, htab, rfl, hkd, htwo, hneg, ?_,
    one_le_toNat_mainArraySize (by lia [hi.one_le_height]) hi.one_le_arraySize, rfl, rfl,
    hsq hi.squarefree⟩, ?_, hsd SiftData.sized_initial, htube⟩
  · refine hS.imp_right fun hS ↦ ?_
    have hneg : neg = (realRootsInit curve.coeffs curve.degree).run := hneg
    change neg.Sound curve.coeffs.toList
    rw [hneg]
    exact (realRootsInit_spec curve.coeffs curve.degree).le_wp ⟨hS, h7, hd, h5, hsq hi.squarefree⟩
  · have hplan : plan = _ := hplan
    rw [hplan]
    exact Array.size_replicate

private theorem mainSearch_post
    (h : t.WF ∧ input.WF ∧ input.quiet = true ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String} (hn : NormalizePost input (curve, text))
    {neg : NegativeIntervals} {stats : TubeStats} {two : TwoAdic} {kd : TubeCoeffs} {plan : Plan}
    {totals : Totals} {out : Output}
    (hout : (totals, out).2 = (({ text } : Output).print
      (choiceText (mainGlobals t input curve neg stats two kd).tables
        (mainGlobals t input curve neg stats two kd).choice plan)).appendPoints
      (mainGlobals t input curve neg stats two kd).check
      (firstIf (mainGlobals t input curve neg stats two kd).check.onePoint
        ((orderedTriples (mainGlobals t input curve neg stats two kd).check.H).flatMap
          (mainGlobals t input curve neg stats two kd).check.points))) :
    out.text = (checkGlobalsOf input).textOf (firstIf input.onePoint
      ((orderedTriples input.height.toNat).flatMap (checkGlobalsOf input).points)) := by
  obtain ⟨rfl, -, -, -, -, htext⟩ := hn
  simp only at hout htext
  rw [hout, htext h.2.2.1, choiceText_of_quiet h.2.2.1]
  simp only [Output.text_appendPoints, Output.print, String.empty_append]
  rfl

private theorem mainSearch_quiet
    (h : t.WF ∧ input.WF ∧ input.quiet = true ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    (hq : ¬input.quiet = true) : False :=
  hq h.2.2.1

/-- Under `-q`, the search of `main` for the tables `t` of `init_main` and the globals `input` that
`read_input` leaves prints the points over the triples of the specification
(`JPoints.orderedTriples`) of the curve searched, in their order, only the first under `-1`, for the
globals of the exact check that it sets (`JPoints.checkGlobalsOf`); it needs Sturm's theorem for the
intervals of `real_roots_init`, unless the sieve has no primes at all, which `-N` with a value of at
most `0` gives. -/
@[spec]
theorem mainSearch_spec (t : Tables) (input : Cli.Input) :
    ⦃ t.WF ∧ input.WF ∧ input.quiet = true ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem) ⦄
    mainSearch t input
    ⦃ fun r ↦ r = (checkGlobalsOf input).textOf (firstIf input.onePoint
        ((orderedTriples input.height.toNat).flatMap (checkGlobalsOf input).points)) ⦄ := by
  -- `find_points` abstracted, with its contract, so that the kernel never evaluates its call on
  -- the globals that `mainSearch` builds, in a time that grows with the constants of the model
  obtain ⟨fp, hfp⟩ : ∃ fp, fp = findPoints := ⟨_, rfl⟩
  have hspec := @findPoints_spec
  rw [← hfp] at hspec
  rw [mainSearch, ← hfp]
  clear hfp
  vcgen [hspec]
  all_goals with_reducible first
    | exact mainSearch_pre_normalize ‹_›
    | exact mainSearch_pre_tubeInit ‹_› ‹_›
    | exact mainSearch_pre_twoadic ‹_›
    | exact mainSearch_pre_findPoints ‹_› ‹_› ‹_› ‹_›
    | exact mainSearch_pre_findPoints ‹_› ‹_› ‹_› (TwoAdic.sound_initial _)
    | exact mainSearch_post ‹_› ‹_› ‹_›
    | exact (mainSearch_quiet ‹_› ‹_›).elim

-- The verification conditions of `JPoints.Program.mainSearch` without `-q`, each in its shape.

private theorem normalizePost_of_eq {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run) :
    NormalizePost input (curve, text) :=
  hn ▸ (normalizeCurve_spec _ _ _).le_wp (mainSearch_pre_normalize h)

private theorem tubeInitPost_of_eq {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run)
    {kd : TubeCoeffs} {plan : Plan} {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState}
    {stats : TubeStats} (ht : (kd, plan, neg, sd, tube, stats) =
      (tubeInit (mainCheck input curve) {} SiftData.initial TubeState.initial).run) :
    TubeInitPost (mainCheck input curve) (kd, plan, neg, sd, tube, stats) :=
  ht ▸ (tubeInit_spec _ _ _ _).le_wp (mainSearch_pre_tubeInit h (normalizePost_of_eq h hn))

private theorem mainSearch_pre_findPoints_twoadicInit
    (h : t.WF ∧ input.WF ∧ input.quiet = false ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run)
    {kd : TubeCoeffs} {plan : Plan} {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState}
    {stats : TubeStats} (ht : (kd, plan, neg, sd, tube, stats) =
      (tubeInit (mainCheck input curve) {} SiftData.initial TubeState.initial).run)
    {two : TwoAdic} (htwo : two = (twoadicInit curve.coeffs (kummerInit curve.coeffs)
      TwoAdic.initial).run) :
    IsSearchGlobals (mainGlobals t input curve neg stats two kd) ∧
      plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ tube.WF := by
  have hn' := normalizePost_of_eq h hn
  refine mainSearch_pre_findPoints h hn' (tubeInitPost_of_eq h hn ht) (htwo ▸ ?_)
  exact (twoadicInit_spec _ _).le_wp ⟨hn'.2.1, hn'.2.2.1 ▸ hn'.2.2.2.1, rfl⟩

private theorem mainSearch_pre_findPoints_initial
    (h : t.WF ∧ input.WF ∧ input.quiet = false ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run)
    {kd : TubeCoeffs} {plan : Plan} {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState}
    {stats : TubeStats} (ht : (kd, plan, neg, sd, tube, stats) =
      (tubeInit (mainCheck input curve) {} SiftData.initial TubeState.initial).run) :
    IsSearchGlobals (mainGlobals t input curve neg stats TwoAdic.initial kd) ∧
      plan.pnn.size = numPrimes + 1 ∧ sd.Sized ∧ tube.WF :=
  mainSearch_pre_findPoints h (normalizePost_of_eq h hn) (tubeInitPost_of_eq h hn ht)
    (TwoAdic.sound_initial _)

private theorem mainSearch_quiet_eq_false
    (h : t.WF ∧ input.WF ∧ input.quiet = false ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    (hq : input.quiet = true) : False :=
  Bool.false_ne_true (h.2.2.1.symm.trans hq)

private theorem choice_eq_choiceGlobalsOf {curve : SearchCurve}
    (hc : curve = searchedCurve input.coeffs.toList) {kd : TubeCoeffs} {plan : Plan}
    {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState} {stats : TubeStats}
    (ht : (kd, plan, neg, sd, tube, stats) =
      (tubeInit (mainCheck input curve) {} SiftData.initial TubeState.initial).run)
    {two : TwoAdic} (htwo : two = (choiceGlobalsOf input).two) :
    ({ input, curve, numNeg := neg.numNeg, stats, two } : ChoiceGlobals) =
      choiceGlobalsOf input := by
  subst hc htwo
  rw [choiceGlobalsOf]
  congr 1
  · exact congr(($ht).2.2.1.numNeg)
  · exact congr(($ht).2.2.2.2.2)

private theorem mainSearch_post_of_quiet_eq_false
    (h : t.WF ∧ input.WF ∧ input.quiet = false ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run)
    {kd : TubeCoeffs} {plan : Plan} {neg : NegativeIntervals} {sd : SiftData} {tube : TubeState}
    {stats : TubeStats} (ht : (kd, plan, neg, sd, tube, stats) =
      (tubeInit (mainCheck input curve) {} SiftData.initial TubeState.initial).run)
    {two : TwoAdic} (htwo : two = (choiceGlobalsOf input).two) {totals : Totals} {out : Output}
    (hout : (totals, out).2 = (({ text } : Output).print
      (choiceText (mainGlobals t input curve neg stats two kd).tables
        (mainGlobals t input curve neg stats two kd).choice plan)).appendPoints
      (mainGlobals t input curve neg stats two kd).check
      (firstIf (mainGlobals t input curve neg stats two kd).check.onePoint
        ((orderedTriples (mainGlobals t input curve neg stats two kd).check.H).flatMap
          (mainGlobals t input curve neg stats two kd).check.points)))
    {s₁₂ s₂ : String}
    (h₁₂ : s₁₂ = (message { choice := { input, curve, numNeg := neg.numNeg, stats, two }, totals }
      12 0).run)
    (h₂ : s₂ = (message { choice := { input, curve, numNeg := neg.numNeg, stats, two }, totals }
      2 0).run) :
    ∃ totals : Totals, out.text ++ s₁₂ ++ s₂ =
      (normalizeCurve input.coeffs input.degree.toNat false).run.2 ++
        choiceText t (choiceGlobalsOf input) {} ++ (checkGlobalsOf input).textOf
          (firstIf input.onePoint
            ((orderedTriples input.height.toNat).flatMap (checkGlobalsOf input).points)) ++
        (message { choice := choiceGlobalsOf input, totals } 12 0).run ++
        (message { choice := choiceGlobalsOf input, totals } 2 0).run := by
  have hn' := normalizePost_of_eq h hn
  have hplan : plan = _ := (tubeInitPost_of_eq h hn ht).2.1
  have hch := choice_eq_choiceGlobalsOf hn'.1 ht htwo
  have htext : text = (normalizeCurve input.coeffs input.degree.toNat false).run.2 :=
    h.2.2.1 ▸ congr(($hn).2)
  have hc : curve = _ := hn'.1
  refine ⟨totals, ?_⟩
  simp only at hout
  subst hc
  rw [hout, h₁₂, h₂, hch, hplan, htext]
  rfl

private theorem two_eq_of_le {q : Bool}
    (h : t.WF ∧ input.WF ∧ input.quiet = q ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem))
    {curve : SearchCurve} {text : String}
    (hn : (curve, text) = (normalizeCurve input.coeffs input.degree.toNat input.quiet).run)
    (h500 : 500 ≤ input.height) {two : TwoAdic}
    (htwo : two = (twoadicInit curve.coeffs (kummerInit curve.coeffs) TwoAdic.initial).run) :
    two = (choiceGlobalsOf input).two := by
  have hc : curve = searchedCurve input.coeffs.toList := (normalizePost_of_eq h hn).1
  simp [htwo, hc, choiceGlobalsOf, h500, checkGlobalsOf]

private theorem two_eq_of_not_le (h500 : ¬500 ≤ input.height) :
    TwoAdic.initial = (choiceGlobalsOf input).two := by
  simp [choiceGlobalsOf, h500]

/-- Without `-q`, the search of `main` for the tables `t` of `init_main` and the globals `input`
that `read_input` leaves prints the message of `normalise_curve`, the text of the choice of the
sieve (`JPoints.choiceText`) for the globals of the choice that it sets (`JPoints.choiceGlobalsOf`)
from the plan that `tube_init` leaves, the initial plan, then the points over the triples of the
specification (`JPoints.orderedTriples`) of the curve searched, in their order, only the first under
`-1`, for the globals of the exact check that it sets (`JPoints.checkGlobalsOf`), and the numbers of
the survivors of the stages and of the points found (messages 12 and 2) for some totals of the
counters; it needs Sturm's theorem for the intervals of `real_roots_init`, unless the sieve has no
primes at all, which `-N` with a value of at most `0` gives. -/
theorem mainSearch_spec_of_quiet_eq_false (t : Tables) (input : Cli.Input) :
    ⦃ t.WF ∧ input.WF ∧ input.quiet = false ∧ (input.sievePrimes3 = 0 ∨ SturmTheorem) ⦄
    mainSearch t input
    ⦃ fun r ↦ ∃ totals : Totals, r = (normalizeCurve input.coeffs input.degree.toNat false).run.2 ++
        choiceText t (choiceGlobalsOf input) {} ++ (checkGlobalsOf input).textOf
          (firstIf input.onePoint
            ((orderedTriples input.height.toNat).flatMap (checkGlobalsOf input).points)) ++
        (message { choice := choiceGlobalsOf input, totals } 12 0).run ++
        (message { choice := choiceGlobalsOf input, totals } 2 0).run ⦄ := by
  -- `find_points` abstracted, as in `JPoints.Program.mainSearch_spec`
  obtain ⟨fp, hfp⟩ : ∃ fp, fp = findPoints := ⟨_, rfl⟩
  have hspec := @findPoints_spec
  rw [← hfp] at hspec
  rw [mainSearch, ← hfp]
  clear hfp
  vcgen [hspec, Std.WP.Id.triple_eq_run (normalizeCurve _ _ _),
    Std.WP.Id.triple_eq_run (tubeInit _ _ _ _), Std.WP.Id.triple_eq_run (twoadicInit _ _ _)]
  all_goals with_reducible first
    | exact mainSearch_pre_findPoints_twoadicInit ‹_› ‹_› ‹_› ‹_›
    | exact mainSearch_pre_findPoints_initial ‹_› ‹_› ‹_›
    | exact mainSearch_post_of_quiet_eq_false ‹_› ‹_› ‹_› (two_eq_of_le ‹_› ‹_› ‹_› ‹_›) ‹_›
        ‹_› ‹_›
    | exact mainSearch_post_of_quiet_eq_false ‹_› ‹_› ‹_› (two_eq_of_not_le ‹_›) ‹_› ‹_› ‹_›
    | exact (mainSearch_quiet_eq_false ‹_› ‹_›).elim

end MainSearch

end Program

end JPoints

end
