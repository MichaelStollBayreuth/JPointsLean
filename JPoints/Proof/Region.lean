/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.BandRange
public import JPoints.Proof.BandRanges

import JPoints.Mathlib.Data.List.Sort
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.RowSetup
import JPoints.Proof.Values
import Std.Tactic.Do

/-!
# The contract of the sieve by bands

What `sift_bands` prints for the rows of the first coordinate `a` from `b_first` on by the step `m`
in the tube or in the real region (`JPoints.siftBands_spec`): for the rows that the condition at 2
leaves, the points over the triples of each row whose third coordinates the sieve of the row and
the analysis of its band hand to the exact check (`JPoints.bandsPoints`), only the first under
`-1`; and it keeps the state of the thread consistent (`JPoints.SiftState.WF`).

## Main definitions

* `JPoints.siftBandsRowPoints`: the points that the sieve of a row of a band prints.
* `JPoints.rowsPoints`, `JPoints.rowsBelow`: the points of some rows, and the rows before a row.
* `JPoints.BandsCont`, `JPoints.BandsPost`: the state of `sift_bands` after some rows and its
  postcondition.
* `JPoints.TubeState.HoldsPolys`: a state of the analysis with the polynomials of a first
  coordinate.
* `JPoints.SiftBandsRowPre`, `JPoints.SiftBandsPre`: the preconditions of the sieve of a row of a
  band and of the sieve by bands.
* `JPoints.SiftBandsRowInvariant`, `JPoints.SiftBandsInvariant`, `JPoints.SiftBandsBandInvariant`:
  the invariants of the loops.

## Main statements

* `JPoints.run_siftBandsRanges_siftBandsBand`: the ranges of a row of a band.
* `JPoints.siftBandsRow_spec`: a row of a band.
* `JPoints.siftBands_spec`: the sieve by bands.
* `JPoints.rowsBelow_append_rowsFrom`: the rows of the bands in turn.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, each verification condition closed by a lemma stated in its own shape. The analysis of
each band runs from the state of the analysis that the thread keeps, whose cache of products gives
the ranges of the analysis from the initial state (`JPoints.bandRanges`,
`JPoints.run_siftBandsRanges_siftBandsBand`), as `JPoints.TubeState.WF` says. The rows of a band
of `sift_bands` are the rows of the step `m` from its first row up to its last
(`JPoints.bandEnd`), and the bands follow each other at the distance `JPoints.bandStep`, a multiple
of `m` (`JPoints.bandLen_bandStep`), so that the rows of the bands in turn are the rows from
`b_first` on (`JPoints.rowsBelow_append_rowsFrom`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The ranges of a row of a band -/

/-- A consistent state `t` of the analysis of the tube that holds the polynomials of the first
coordinate `a`: those of `JPoints.tubeAInit` from the initial state, for the globals `g` and the
static data `sd`. -/
def TubeState.HoldsPolys (g : BandGlobals) (sd : SiftData) (a : ℤ) (t : TubeState) : Prop :=
  t.WF ∧ (tubeAInit g.kd g.sift.check.height sd.th sd.th2 .initial a).run.EqPolys t

/-- The analysis of the band of the row `b` of the rows from `bFirst` on by the step `m`
(`JPoints.bandOf`), as `sift_bands` runs it from a consistent state `t` of the analysis that holds
the polynomials of the first coordinate `a` (`JPoints.TubeState.HoldsPolys`), gives the row the
ranges of the analysis from the initial state (`JPoints.bandRanges`): the cache reproduces the
products of every cell, and the ranges of a row of the band are those that the analysis of the
band collects. -/
theorem run_siftBandsRanges_siftBandsBand {g : BandGlobals} {sd : SiftData} {t : TubeState}
    {a : ℤ} (ht : t.HoldsPolys g sd a) {bFirst m b bLo bHi : ℤ}
    (hband : bandOf g.sift.check.height bFirst m b = (bLo, bHi)) (hb : bLo ≤ b) (hbH : b ≤ bHi) :
    (siftBandsRanges g sd (siftBandsBand sd t bLo bHi (g.sieveMode == 1)).run.bands a b bLo
      (g.sieveMode == 1)).run = bandRanges g sd a bFirst m b := by
  rw [bandRanges, hband]
  dsimp only
  rw [run_siftBandsRanges, run_siftBandsRanges]
  have hn := bandOf_snd_sub_fst_add_one_le hband
  exact bandRowRanges_congr fun h ↦ by
    rw [h]
    exact rowRanges_siftBandsBand ht.1 (wf_run_tubeAInit_initial ..) ht.2 (by lia) hn (by lia)

/-! ### A row of a band -/

/-- The precondition of `JPoints.siftBandsRow` for the row `(a, b)` of the band from `bLo` on in
the state `s`, whose ranges of words are `R`: the set-up, a consistent state, the bounds of the
row, `R` the ranges that the bands of the state give the row (`JPoints.siftBandsRanges`), in
increasing order within the words of a row, and none when the row holds no range of the tube. -/
abbrev SiftBandsRowPre (g : BandGlobals) (sd : SiftData) (s : SiftState) (a b bLo : ℤ)
    (tube : Bool) (R : ℕ × Array ℤ × Array ℤ) : Prop :=
  IsSieveSetup g sd ∧ s.WF g sd ∧ 0 ≤ a ∧ a ≤ g.sift.check.height ∧ |b| ≤ g.sift.check.height ∧
    (a = 0 → 1 ≤ b) ∧ (siftBandsRanges g sd s.tube.bands a b bLo tube).run = R ∧
    RangesIn sd.wLowAll sd.wHighAll (rangeList R) ∧
    (tube = true → s.tube.bands.bandNr[(b - bLo).toNat]! = 0 → R.1 = 0)

/-- The points that `JPoints.siftBandsRow` prints for the row `(a, b)` with the ranges `R`: those of
the ranges (`JPoints.rangesPoints`) when the condition at 2 leaves the row
(`JPoints.aliveKeeps`), and none otherwise. -/
def siftBandsRowPoints (g : SiftGlobals) (sd : SiftData) (a b : ℤ) (R : ℕ × Array ℤ × Array ℤ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  if aliveKeeps g a b then rangesPoints g sd a b R else []

/-- The invariant of the loop of `JPoints.siftBandsRow` over the ranges `(nr, rlo, rhi)` of the row
`(a, b)`, from the state `s` after `row_setup`, whose state is the result of an early return and the
state of the thread: before a return, the state after the points of the ranges done
(`JPoints.BandRangeCont`); after it, the postcondition with the points of all the ranges. -/
def SiftBandsRowInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ)
    (R : ℕ × Array ℤ × Array ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (BandRangeCont g sd s st.2 (((rangeList R).take pref.length).flatMap
      fun r ↦ rowRangePoints g sd a b r.1 r.2))
    fun r ↦ suff = [] ∧ BandRangePost g sd s (rangesPoints g sd a b R) r

section SiftBandsRow

variable {g : BandGlobals} {sd : SiftData} {s s0 st s' : SiftState} {a b bLo : ℤ} {tube : Bool}
  {R : ℕ × Array ℤ × Array ℤ} {nr : ℕ} {rlo rhi : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
  {o : Option (Bool × SiftState)}

private theorem siftBandsRow_post_skip {L : List (ℤ × ℤ × ℤ × ℤ)} (hs : s.WF g sd) (hL : L = []) :
    SiftState.WF g sd (false, s).2 ∧ (false, s).2.tube = s.tube ∧
      (false, s).2.out = s.out.appendPoints g.sift.check (firstIf g.sift.check.onePoint L) ∧
      false = (g.sift.check.onePoint && !L.isEmpty) := by
  subst hL
  exact ⟨hs, rfl, by simp [firstIf, Output.appendPoints_nil], by simp⟩

private theorem siftBandsRow_post_empty (hpre : SiftBandsRowPre g sd s a b bLo tube R)
    (h : (tube && s.tube.bands.bandNr[(b - bLo).toNat]! == 0) = true) :
    SiftState.WF g sd (false, s).2 ∧ (false, s).2.tube = s.tube ∧
      (false, s).2.out = s.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      false = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine siftBandsRow_post_skip hpre.2.1 ?_
  rw [siftBandsRowPoints, rangesPoints_eq_nil_of_fst_eq_zero (hpre.2.2.2.2.2.2.2.2 h.1 h.2)]
  split_ifs <;> rfl

private theorem siftBandsRow_post_dead (hpre : SiftBandsRowPre g sd s a b bLo tube R)
    (h : (g.sift.twoAdic.use2 && a != 0 &&
      !g.sift.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) = true) :
    SiftState.WF g sd (false, s).2 ∧ (false, s).2.tube = s.tube ∧
      (false, s).2.out = s.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      false = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  refine siftBandsRow_post_skip hpre.2.1 ?_
  rw [siftBandsRowPoints, ite_eq_right (by rw [aliveKeeps_eq_not, h]; decide)]

private theorem siftBandsRow_post_none (hpre : SiftBandsRowPre g sd s a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s.tube.bands a b bLo tube).run)
    (h : (nr == 0) = true) :
    SiftState.WF g sd (false, s).2 ∧ (false, s).2.tube = s.tube ∧
      (false, s).2.out = s.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      false = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  refine siftBandsRow_post_skip hpre.2.1 ?_
  rw [hpre.2.2.2.2.2.2.1] at hR
  rw [siftBandsRowPoints, rangesPoints_eq_nil_of_fst_eq_zero (by rw [← hR]; simpa using h)]
  split_ifs <;> rfl

private theorem siftBandsRow_rowSetup_pre (hpre : SiftBandsRowPre g sd s a b bLo tube R) :
    IsStageSetup g.sift sd ∧ RowSetupCache.WF g.sift sd s.rowptr s.rowSetup ∧ 0 ≤ a ∧
      |b| ≤ g.sift.check.height :=
  ⟨hpre.1.isStageSetup, hpre.2.1.rowSetup, hpre.2.2.1, hpre.2.2.2.2.1⟩

private theorem siftBandsRow_eq_R (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s0.tube.bands a b bLo tube).run) :
    R = (nr, rlo, rhi) := by
  rw [hR, hpre.2.2.2.2.2.2.1]

private theorem siftBandsRowInvariant_init (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hrs : RowSetupPost g.sift sd s0 a b s) {l : List ℕ} :
    SiftBandsRowInvariant g.sift sd s a b R [] l (none, s) := by
  have hc : s.curChunk = s0.curChunk := congr(SiftState.curChunk $(hrs.1))
  have h3 : s.row3 = s0.row3 := congr(SiftState.row3 $(hrs.1))
  refine ⟨rfl, rfl, hc ▸ hpre.2.1.curChunk_lt, h3 ▸ hpre.2.1.row3, ?_, fun _ ↦ by simp⟩
  simp [Output.appendPoints_nil]

private theorem SiftBandsRowInvariant.cont
    (hv : SiftBandsRowInvariant g.sift sd s a b R pref (cur :: suff) (o, st)) :
    o = none ∧ BandRangeCont g.sift sd s st
      (((rangeList R).take pref.length).flatMap fun r ↦ rowRangePoints g.sift sd a b r.1 r.2) :=
  Option.eq_none_and_of_elim_cons hv

private theorem siftBandsRow_range_pre (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s0.tube.bands a b bLo tube).run)
    (hrs : RowSetupPost g.sift sd s0 a b s)
    (hc : ForIn.toList [:nr] = pref ++ cur :: suff)
    (hv : SiftBandsRowInvariant g.sift sd s a b R pref (cur :: suff) (o, st)) :
    IsRowSetup g.sift sd ∧ RowSetupCache.WF g.sift sd st.rowptr st.rowSetup ∧
      st.rowSetup.lastA = a ∧ st.rowSetup.lastB = b ∧ Row3Cache.WF g.sift sd st.row3 ∧
      st.curChunk < sd.numChunks ∧ st.survivors.size = g.sift.arraySize + 1 ∧
      sd.wLowAll ≤ rlo[cur]! ∧ rlo[cur]! < rhi[cur]! ∧ rhi[cur]! ≤ sd.wHighAll ∧ 0 ≤ a ∧
      a ≤ g.sift.check.height ∧ |b| ≤ g.sift.check.height ∧ (a = 0 → 1 ≤ b) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  obtain ⟨e1, e2, -⟩ := BandRangeCont.fields hst
  obtain ⟨-, hsz, hcc, h3, -⟩ := hst
  have hs0 : s.survivors = s0.survivors := congr(SiftState.survivors $(hrs.1))
  have hmem : (rlo[cur]!, rhi[cur]!) ∈ rangeList R := by
    rw [siftBandsRow_eq_R hpre hR]
    exact List.mem_map.mpr ⟨cur, List.mem_range.mpr hcur, rfl⟩
  have hr := hpre.2.2.2.2.2.2.2.1.1 _ hmem
  obtain ⟨-, hw, hA, hB⟩ := hrs
  exact ⟨hpre.1.isRowSetup, e1 ▸ e2 ▸ hw, e2 ▸ hA, e2 ▸ hB, h3, hcc,
    hsz.trans (hs0 ▸ hpre.2.1.size_survivors), hr.1, hr.2.1, hr.2.2, hpre.2.2.1,
    hpre.2.2.2.1, hpre.2.2.2.2.1, hpre.2.2.2.2.2.1⟩

private theorem siftBandsRow_range_return (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s0.tube.bands a b bLo tube).run)
    (hc : ForIn.toList [:nr] = pref ++ cur :: suff)
    (hv : SiftBandsRowInvariant g.sift sd s a b R pref (cur :: suff) (o, st)) {found : Bool}
    (hp : BandRangePost g.sift sd st (rowRangePoints g.sift sd a b rlo[cur]! rhi[cur]!)
      (found, s'))
    (hf : found = true) :
    SiftBandsRowInvariant g.sift sd s a b R (ForIn.toList [:nr]) [] (some (true, s'), s') := by
  obtain rfl := siftBandsRow_eq_R hpre hR
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, -, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hp
  dsimp only at g1 g2 g3 g4 g5 g6
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc] at hout h1
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_found (out := s.out)
    (R := ((rangeList (nr, rlo, rhi)).drop (cur + 1)).flatMap
      fun r ↦ rowRangePoints g.sift sd a b r.1 r.2) h1 g6
    (by rw [hf] at g6 ⊢; exact ((Bool.and_eq_true _ _).mp g6.symm).1)
  rw [← hout, ← g5, ← rangesPoints_eq_append hcur] at f1
  rw [← rangesPoints_eq_append hcur] at f2
  refine ⟨rfl, SiftState.eq_with_survivors_curChunk_of_eq_with hfs g1, g2.trans hsz, g3, g4, f1, f2⟩

private theorem siftBandsRow_range_next (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s0.tube.bands a b bLo tube).run)
    (hc : ForIn.toList [:nr] = pref ++ cur :: suff)
    (hv : SiftBandsRowInvariant g.sift sd s a b R pref (cur :: suff) (o, st)) {found : Bool}
    (hp : BandRangePost g.sift sd st (rowRangePoints g.sift sd a b rlo[cur]! rhi[cur]!)
      (found, s'))
    (hf : ¬found = true) :
    SiftBandsRowInvariant g.sift sd s a b R (pref ++ [cur]) suff (none, s') := by
  obtain rfl := siftBandsRow_eq_R hpre hR
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, -, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hp
  dsimp only at g1 g2 g3 g4 g5 g6
  rw [hl] at hout h1
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_not_found (out := s.out) h1 g6
    (by rw [Bool.eq_false_iff.mpr hf, Bool.false_and]; decide)
  rw [← hout, ← g5] at f1
  have ht : (pref ++ [cur]).length = cur + 1 := by simp [hl]
  refine ⟨SiftState.eq_with_survivors_curChunk_of_eq_with hfs g1, g2.trans hsz, g3, g4, ?_, ?_⟩
  · rw [ht, rangeList_take_succ hcur, List.flatMap_append, List.flatMap_singleton]
    exact f1
  · rw [ht, rangeList_take_succ hcur, List.flatMap_append, List.flatMap_singleton]
    exact f2

private theorem siftBandsRow_post (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hrs : RowSetupPost g.sift sd s0 a b s)
    (hal : ¬(g.sift.twoAdic.use2 && a != 0 &&
      !g.sift.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) = true) {x : Bool}
    (hp : BandRangePost g.sift sd s (rangesPoints g.sift sd a b R) (x, st)) :
    SiftState.WF g sd st ∧ st.tube = s0.tube ∧
      st.out = s0.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      x = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  have hk : aliveKeeps g.sift a b = true := by
    rw [aliveKeeps_eq_not, Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr hal
  simp only [siftBandsRowPoints, hk, ↓reduceIte]
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hp
  dsimp only at g1 g2 g3 g4 g5 g6
  obtain ⟨h1, hw, -⟩ := hrs
  have e : st.tube = s0.tube := congr(SiftState.tube $g1).trans congr(SiftState.tube $h1)
  have hz : st.survivors.size = s0.survivors.size :=
    g2.trans congr(Array.size (SiftState.survivors $h1))
  have hr : st.rowptr = s.rowptr ∧ st.rowSetup = s.rowSetup :=
    ⟨congr(SiftState.rowptr $g1), congr(SiftState.rowSetup $g1)⟩
  refine ⟨⟨hz.trans hpre.2.1.size_survivors, hr.1 ▸ hr.2 ▸ hw, g4, e ▸ hpre.2.1.tube, g3⟩, e,
    g5.trans congr(Output.appendPoints (SiftState.out $h1) _ _), g6⟩

private theorem siftBandsRow_post_some (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hrs : RowSetupPost g.sift sd s0 a b s)
    (hal : ¬(g.sift.twoAdic.use2 && a != 0 &&
      !g.sift.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) = true) {l : List ℕ}
    (hv : SiftBandsRowInvariant g.sift sd s a b R l [] (o, st)) {x : Bool} {y : SiftState}
    (ho : o = some (x, y)) :
    SiftState.WF g sd y ∧ y.tube = s0.tube ∧
      y.out = s0.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      x = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  subst ho
  exact siftBandsRow_post hpre hrs hal hv.2

private theorem siftBandsRow_post_end (hpre : SiftBandsRowPre g sd s0 a b bLo tube R)
    (hR : (nr, rlo, rhi) = (siftBandsRanges g sd s0.tube.bands a b bLo tube).run)
    (hrs : RowSetupPost g.sift sd s0 a b s)
    (hal : ¬(g.sift.twoAdic.use2 && a != 0 &&
      !g.sift.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) = true)
    (hv : SiftBandsRowInvariant g.sift sd s a b R (ForIn.toList [:nr]) [] (o, st))
    (ho : o = none) :
    SiftState.WF g sd st ∧ st.tube = s0.tube ∧
      st.out = s0.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
      false = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) := by
  subst ho
  obtain rfl := siftBandsRow_eq_R hpre hR
  have h : BandRangeCont _ _ _ _ _ := hv
  rw [Std.Legacy.Range.length_toList_zero_start,
    List.take_of_length_le (by simp [rangeList])] at h
  exact siftBandsRow_post hpre hrs hal h.post

end SiftBandsRow

theorem siftBandsRow_spec (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a b bLo : ℤ)
    (tube : Bool) (R : ℕ × Array ℤ × Array ℤ) :
    ⦃ SiftBandsRowPre g sd s0 a b bLo tube R ⦄
    siftBandsRow g sd s0 a b bLo tube
    ⦃ fun r ↦ r.2.WF g sd ∧ r.2.tube = s0.tube ∧ r.2.out = s0.out.appendPoints g.sift.check
          (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a b R)) ∧
        r.1 = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a b R).isEmpty) ⦄ := by
  vcgen [siftBandsRow, Std.WP.Id.triple_eq_run (siftBandsRanges _ _ _ _ _ _ _),
    siftBandsTube_spec, siftBandsRegion_spec] invariants
  · SiftBandsRowInvariant g.sift sd s a b R
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact siftBandsRowInvariant_init ‹_› ‹_›
    | exact siftBandsRow_range_pre ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_post_empty ‹_› ‹_›
    | exact siftBandsRow_post_dead ‹_› ‹_›
    | exact siftBandsRow_post_none ‹_› ‹_› ‹_›
    | exact siftBandsRow_rowSetup_pre ‹_›
    | exact siftBandsRow_range_return ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_range_next ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_post_some ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_post_end ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

/-! ### The bands of `sift_bands` -/

-- `Int.mul_le_of_le_ediv` for a bound by the number of rows from a first one by a step.
private theorem mul_le_of_lt_toNat {k : ℕ} {x m : ℤ} (hm : 0 < m) (hk : k < (x / m + 1).toNat) :
    k * m ≤ x :=
  Int.mul_le_of_le_ediv hm (by lia)

/-! ### The invariants of `sift_bands` -/

/-- The points that `sift_bands` finds in the rows `L` of the first coordinate `a`, for the rows
from `bFirst` on by the step `m`: for the rows that the condition at 2 leaves
(`JPoints.aliveKeeps`), in order, the points of each row (`JPoints.bandRowPoints`). -/
def rowsPoints (g : BandGlobals) (sd : SiftData) (a bFirst m : ℤ) (L : List ℤ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  (L.filter (aliveKeeps g.sift a)).flatMap (bandRowPoints g sd a bFirst m)

theorem bandsPoints_eq_rowsPoints (g : BandGlobals) (sd : SiftData) (a bFirst m : ℤ) :
    bandsPoints g sd a bFirst m =
      rowsPoints g sd a bFirst m (rowsFrom bFirst m g.sift.check.height) :=
  rfl

/-- The rows from `bFirst` on by the step `m` up to `H` before the row `x`. -/
def rowsBelow (H bFirst m x : ℤ) : List ℤ :=
  (rowsFrom bFirst m H).filter (· < x)

/-- The state `s` of the thread in `sift_bands` from the state `s0` after the rows `L`: consistent,
with the points of the rows printed (`JPoints.rowsPoints`), none under `-1`. -/
def BandsCont (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a bFirst m : ℤ) (L : List ℤ)
    (s : SiftState) : Prop :=
  s.WF g sd ∧ s.out = s0.out.appendPoints g.sift.check (rowsPoints g sd a bFirst m L) ∧
    (g.sift.check.onePoint = true → rowsPoints g sd a bFirst m L = [])

/-- The postcondition of `sift_bands` from the state `s0` with the result `r`: a consistent state,
the points of all the rows printed (`JPoints.bandsPoints`), only the first under `-1`, and the flag
of a point under `-1`. -/
def BandsPost (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a bFirst m : ℤ)
    (r : Bool × SiftState) : Prop :=
  r.2.WF g sd ∧ r.2.out = s0.out.appendPoints g.sift.check
      (firstIf g.sift.check.onePoint (bandsPoints g sd a bFirst m)) ∧
    r.1 = (g.sift.check.onePoint && !(bandsPoints g sd a bFirst m).isEmpty)

/-- The invariant of the loop of `JPoints.siftBands` over its bands from the state `s0`, whose state
is the result of an early return and the state of the thread: before a return, the state after the
rows of the bands done (`JPoints.rowsBelow`), whose analysis of the tube holds the polynomials of
`a`; after it, the postcondition. -/
def SiftBandsInvariant (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a bFirst m : ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (BandsCont g sd s0 a bFirst m
        (rowsBelow g.sift.check.height bFirst m (bFirst + pref.length * bandStep m)) st.2 ∧
      st.2.tube.HoldsPolys g sd a)
    fun r ↦ suff = [] ∧ BandsPost g sd s0 a bFirst m r

/-- The invariant of the loop of `JPoints.siftBands` over the rows of the band whose analysis of the
tube is `tb` from the state `s0`, whose state is the result of an early return and the state of the
thread: before a return, the state after the rows of the bands before and the rows of the band
done, with the analysis `tb`; after it, the postcondition. -/
def SiftBandsBandInvariant (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a bFirst m : ℤ)
    (tb : TubeState) : Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (BandsCont g sd s0 a bFirst m (rowsBelow g.sift.check.height bFirst m tb.bands.bandB0 ++
        pref.map fun k : ℕ ↦ tb.bands.bandB0 + k * m) st.2 ∧ st.2.tube = tb)
    fun r ↦ suff = [] ∧ BandsPost g sd s0 a bFirst m r

/-! ### The steps of `sift_bands` -/

private theorem SiftState.WF.with_tube {g : BandGlobals} {sd : SiftData} {s : SiftState}
    (hs : s.WF g sd)
    {t : TubeState} (ht : t.WF) : SiftState.WF g sd { s with tube := t } :=
  ⟨hs.size_survivors, hs.rowSetup, hs.row3, ht, hs.curChunk_lt⟩

theorem TubeState.HoldsPolys.siftBandsBand {g : BandGlobals} {sd : SiftData} {a : ℤ}
    {t : TubeState} (h : t.HoldsPolys g sd a) (bLo bHi : ℤ) (tube : Bool) :
    (JPoints.siftBandsBand sd t bLo bHi tube).run.HoldsPolys g sd a := by
  obtain ⟨ht, hp⟩ := h
  rw [run_siftBandsBand]
  split_ifs
  · obtain ⟨r1, r2⟩ := size_resetBands t.bands bLo bHi
    obtain ⟨w, e⟩ := (ht.with_bands (r1.trans ht.size_bandNr)
      (r2.trans ht.size_bandRg)).run_tubeCell sd.th sd.th2 bLo bHi sd.wLowAll
        sd.wHighAll
    exact ⟨w, hp.trans (TubeState.EqPolys.trans ⟨rfl, rfl, rfl, rfl, rfl⟩ e)⟩
  · exact ⟨ht.with_bands ht.size_bandNr ht.size_bandRg, hp.trans ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem TubeState.HoldsPolys.of_eq_with {g : BandGlobals} {sd : SiftData} {a : ℤ}
    {t : TubeState} (ht : t.WF) {n : ℕ} {c : TubeCellCache} {bd : TubeBands}
    (h : t = { (tubeAInit g.kd g.sift.check.height sd.th sd.th2 .initial a).run with
      tubeNcells := n, cache := c, bands := bd }) : t.HoldsPolys g sd a := by
  refine ⟨ht, ?_⟩
  generalize (tubeAInit g.kd g.sift.check.height sd.th sd.th2 .initial a).run = T at h ⊢
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem run_siftBandsRanges_band {g : BandGlobals} {sd : SiftData} {a bFirst m : ℤ}
    (hm : 0 < m) {T : TubeState} (hT : T.HoldsPolys g sd a) {n k : ℕ}
    (hk : k < ((bandEnd g.sift.check.height (bFirst + n * bandStep m) m -
      (bFirst + n * bandStep m)) / m + 1).toNat) :
    (siftBandsRanges g sd (siftBandsBand sd T (bFirst + n * bandStep m)
        (bandEnd g.sift.check.height (bFirst + n * bandStep m) m) (g.sieveMode == 1)).run.bands a
        (bFirst + n * bandStep m + k * m) (bFirst + n * bandStep m) (g.sieveMode == 1)).run =
      bandRanges g sd a bFirst m (bFirst + n * bandStep m + k * m) := by
  have hkm := mul_le_of_lt_toNat hm hk
  exact run_siftBandsRanges_siftBandsBand hT (bandOf_add_mul hm hkm)
    (by lia [Int.mul_nonneg (Int.natCast_nonneg k) hm.le]) (by lia)

private theorem rowsPoints_append (g : BandGlobals) (sd : SiftData) (a bFirst m : ℤ)
    (L₁ L₂ : List ℤ) :
    rowsPoints g sd a bFirst m (L₁ ++ L₂) =
      rowsPoints g sd a bFirst m L₁ ++ rowsPoints g sd a bFirst m L₂ := by
  simp [rowsPoints]

private theorem rowsPoints_singleton {g : BandGlobals} {sd : SiftData} {a bFirst m b : ℤ}
    (hmode : g.sieveMode ≠ 0) (hw : sd.wLowAll < sd.wHighAll)
    (hb : (bandOf g.sift.check.height bFirst m b).1 ≤ b)
    (hbH : b ≤ (bandOf g.sift.check.height bFirst m b).2) :
    rowsPoints g sd a bFirst m [b] =
      siftBandsRowPoints g.sift sd a b (bandRanges g sd a bFirst m b) := by
  rw [siftBandsRowPoints, ← bandRowPoints_eq_rangesPoints hmode (rangesIn_bandRanges hw hb hbH)]
  simp only [rowsPoints, List.filter_cons, List.filter_nil]
  split_ifs <;> simp

private theorem rowsBelow_prefix {H bFirst m : ℤ} (hm : 0 < m) (x : ℤ) :
    rowsBelow H bFirst m x <+: rowsFrom bFirst m H :=
  (pairwise_lt_rowsFrom hm).filter_lt_prefix x

/-- The state of the thread after all the rows is the end of `sift_bands`. -/
theorem BandsCont.post {g : BandGlobals} {sd : SiftData} {s0 s : SiftState} {a bFirst m : ℤ}
    (h : BandsCont g sd s0 a bFirst m (rowsFrom bFirst m g.sift.check.height) s) :
    BandsPost g sd s0 a bFirst m (false, s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩ <;> rw [bandsPoints_eq_rowsPoints] <;> cases hop : g.sift.check.onePoint
  · exact h2
  · simp [h2, h3 hop]
  · rfl
  · simp [h3 hop]

theorem rowsBelow_append_rowsFrom {H bFirst m : ℤ} (hm : 0 < m) (n : ℕ) :
    rowsBelow H bFirst m (bFirst + n * bandStep m) ++
        rowsFrom (bFirst + n * bandStep m) m (bandEnd H (bFirst + n * bandStep m) m) =
      rowsBelow H bFirst m (bFirst + (n + 1 : ℕ) * bandStep m) := by
  obtain ⟨h1, h2, h3, h4⟩ := bandLen_bandStep hm
  rw [rowsBelow, rowsBelow, show bFirst + ((n + 1 : ℕ) : ℤ) * bandStep m =
    bFirst + n * bandStep m + bandStep m by push_cast; ring]
  exact filter_rowsFrom_append_rowsFrom hm (by lia [Int.mul_nonneg (Int.natCast_nonneg n)
    (show 0 ≤ bandStep m by lia)]) (by rw [add_sub_cancel_left]; exact dvd_mul_of_dvd_right h4 _)
    h1 h2 h3 h4

private theorem rowsBelow_append_prefix {H bFirst m : ℤ} (hm : 0 < m) {n : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hc : ForIn.toList [:((bandEnd H (bFirst + n * bandStep m) m -
      (bFirst + n * bandStep m)) / m + 1).toNat] = pref ++ cur :: suff) :
    rowsBelow H bFirst m (bFirst + n * bandStep m) ++
        (pref ++ [cur]).map (fun k : ℕ ↦ bFirst + n * bandStep m + k * m) <+:
      rowsFrom bFirst m H := by
  refine .trans ?_ ((rowsBelow_append_rowsFrom hm n).symm ▸ rowsBelow_prefix hm _)
  rw [List.prefix_append_right_inj, rowsFrom, ← Std.Legacy.Range.toList_eq_range, hc]
  exact List.IsPrefix.map _ ⟨suff, by simp⟩

/-- The precondition of `JPoints.siftBands`. -/
abbrev SiftBandsPre (g : BandGlobals) (sd : SiftData) (s0 : SiftState) (a bFirst m : ℤ) : Prop :=
  IsSieveSetup g sd ∧ s0.WF g sd ∧ ¬g.sieveMode = 0 ∧ 0 ≤ a ∧ a ≤ g.sift.check.height ∧
    1 ≤ m ∧ -g.sift.check.height ≤ bFirst ∧ (a = 0 → 1 ≤ bFirst)

section SiftBands

variable {g : BandGlobals} {sd : SiftData} {s0 st st' s' : SiftState} {a bFirst m : ℤ}
  {tb : TubeState} {pref suff pref' suff' : List ℕ} {cur cur' : ℕ}
  {o o' : Option (Bool × SiftState)}

private theorem siftBandsInvariant_none {l l' : List ℕ} :
    SiftBandsInvariant g sd s0 a bFirst m l l' (none, st) ↔
      BandsCont g sd s0 a bFirst m
        (rowsBelow g.sift.check.height bFirst m (bFirst + l.length * bandStep m)) st ∧
        st.tube.HoldsPolys g sd a :=
  Iff.rfl

private theorem siftBands_tube_wf (hpre : SiftBandsPre g sd s0 a bFirst m) : s0.tube.WF :=
  hpre.2.1.tube

private theorem siftBandsInvariant_init (hpre : SiftBandsPre g sd s0 a bFirst m) {t : TubeState}
    (ht : t.WF ∧ t = { (tubeAInit g.kd g.sift.check.height sd.th sd.th2 .initial a).run with
      tubeNcells := s0.tube.tubeNcells, cache := s0.tube.cache, bands := s0.tube.bands })
    {l : List ℕ} : SiftBandsInvariant g sd s0 a bFirst m [] l (none, { s0 with tube := t }) := by
  have h0 : rowsBelow g.sift.check.height bFirst m (bFirst + ([] : List ℕ).length *
      bandStep m) = [] := filter_rowsFrom_eq_nil (by lia [hpre.2.2.2.2.2.1]) (by simp)
  refine siftBandsInvariant_none.mpr ⟨⟨hpre.2.1.with_tube ht.1, ?_, fun _ ↦ ?_⟩,
    .of_eq_with ht.1 ht.2⟩
  · rw [h0]
    exact (Output.appendPoints_nil ..).symm
  · rw [h0]
    rfl

private theorem SiftBandsInvariant.cont
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st)) :
    o = none ∧ BandsCont g sd s0 a bFirst m
      (rowsBelow g.sift.check.height bFirst m (bFirst + pref.length * bandStep m)) st ∧
      st.tube.HoldsPolys g sd a :=
  Option.eq_none_and_of_elim_cons hv

private theorem SiftBandsBandInvariant.cont
    (hv : SiftBandsBandInvariant g sd s0 a bFirst m tb pref (cur :: suff) (o, st)) :
    o = none ∧ BandsCont g sd s0 a bFirst m (rowsBelow g.sift.check.height bFirst m
      tb.bands.bandB0 ++ pref.map fun k : ℕ ↦ tb.bands.bandB0 + k * m) st ∧ st.tube = tb :=
  Option.eq_none_and_of_elim_cons hv

private theorem siftBands_post_some {l : List ℕ}
    (hv : SiftBandsInvariant g sd s0 a bFirst m l [] (o, st)) {x : Bool} {y : SiftState}
    (ho : o = some (x, y)) :
    SiftState.WF g sd y ∧ y.out = s0.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (bandsPoints g sd a bFirst m)) ∧
      x = (g.sift.check.onePoint && !(bandsPoints g sd a bFirst m).isEmpty) := by
  subst ho
  exact hv.2

private theorem siftBands_post_end (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m
      (ForIn.toList [:((g.sift.check.height - bFirst) / bandStep m + 1).toNat]) [] (o, st))
    (ho : o = none) :
    SiftState.WF g sd st ∧ st.out = s0.out.appendPoints g.sift.check
        (firstIf g.sift.check.onePoint (bandsPoints g sd a bFirst m)) ∧
      false = (g.sift.check.onePoint && !(bandsPoints g sd a bFirst m).isEmpty) := by
  subst ho
  have hm : 0 < m := by lia [hpre.2.2.2.2.2.1]
  have h : BandsCont _ _ _ _ _ _ _ _ := hv.1
  rw [Std.Legacy.Range.length_toList_zero_start, rowsBelow,
    filter_rowsFrom_eq_self hm (by lia [bandLen_bandStep hm])] at h
  exact h.post

private theorem siftBandsBandInvariant_none {l l' : List ℕ} :
    SiftBandsBandInvariant g sd s0 a bFirst m tb l l' (none, st) ↔
      BandsCont g sd s0 a bFirst m (rowsBelow g.sift.check.height bFirst m tb.bands.bandB0 ++
        l.map fun k : ℕ ↦ tb.bands.bandB0 + k * m) st ∧ st.tube = tb :=
  Iff.rfl

private theorem siftBandsBandInvariant_init
    (hc : ForIn.toList [:((g.sift.check.height - bFirst) / bandStep m + 1).toNat] =
      pref ++ cur :: suff)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    {l : List ℕ} :
    SiftBandsBandInvariant g sd s0 a bFirst m tb [] l (none, { st with tube := tb }) := by
  obtain ⟨-, ⟨h1, h2, h3⟩, hp⟩ := hv.cont
  have hb : tb.bands.bandB0 = bFirst + pref.length * bandStep m := by
    rw [htb, bandB0_siftBandsBand, Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc]
  have ht : tb.WF := by
    rw [htb]
    exact (hp.siftBandsBand ..).1
  refine siftBandsBandInvariant_none.mpr ⟨⟨h1.with_tube ht, ?_, ?_⟩, rfl⟩ <;>
    rw [hb, List.map_nil, List.append_nil]
  · exact h2
  · exact h3

private theorem siftBandsBand_post_some {l l' : List ℕ}
    (hv : SiftBandsBandInvariant g sd s0 a bFirst m tb l [] (o, st)) {x : Bool} {y : SiftState}
    (ho : o = some (x, y)) :
    SiftBandsInvariant g sd s0 a bFirst m l' [] (some (x, y), st') := by
  subst ho
  exact hv

private theorem siftBandsBand_post_end (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hc : ForIn.toList [:((g.sift.check.height - bFirst) / bandStep m + 1).toNat] =
      pref ++ cur :: suff)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb
      (ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
        (bFirst + cur * bandStep m)) / m + 1).toNat]) [] (o', st'))
    (ho : o' = none) :
    SiftBandsInvariant g sd s0 a bFirst m (pref ++ [cur]) suff (none, st') := by
  subst ho
  obtain ⟨-, -, hp⟩ := hv.cont
  obtain ⟨⟨h1, h2, h3⟩, ht⟩ := siftBandsBandInvariant_none.mp hv'
  have e : rowsBelow g.sift.check.height bFirst m (bFirst + cur * bandStep m) ++
      (ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
        (bFirst + cur * bandStep m)) / m + 1).toNat]).map
          (fun k : ℕ ↦ bFirst + cur * bandStep m + k * m) =
      rowsBelow g.sift.check.height bFirst m (bFirst + (pref ++ [cur]).length * bandStep m) := by
    rw [Std.Legacy.Range.toList_eq_range, List.length_append,
      Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc, List.length_singleton]
    exact rowsBelow_append_rowsFrom (by lia [hpre.2.2.2.2.2.1]) cur
  rw [htb, bandB0_siftBandsBand, e] at h2 h3
  exact siftBandsInvariant_none.mpr ⟨⟨h1, h2, h3⟩, ht ▸ htb ▸ hp.siftBandsBand ..⟩

private theorem siftBandsRow_ranges (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hc' : ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m)) / m + 1).toNat] = pref' ++ cur' :: suff')
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb pref' (cur' :: suff') (o', st')) :
    (siftBandsRanges g sd st'.tube.bands a (bFirst + cur * bandStep m + cur' * m)
        (bFirst + cur * bandStep m) (g.sieveMode == 1)).run =
      bandRanges g sd a bFirst m (bFirst + cur * bandStep m + cur' * m) ∧
    bandOf g.sift.check.height bFirst m (bFirst + cur * bandStep m + cur' * m) =
      (bFirst + cur * bandStep m, bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) ∧
    cur' * m ≤ bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m) := by
  have hm : 0 < m := by lia [hpre.2.2.2.2.2.1]
  obtain ⟨-, -, hp⟩ := hv.cont
  obtain ⟨-, -, ht⟩ := hv'.cont
  have hk := Std.Legacy.Range.lt_of_toList_eq_append_cons hc'
  refine ⟨?_, bandOf_add_mul hm (mul_le_of_lt_toNat hm hk), mul_le_of_lt_toNat hm hk⟩
  rw [ht, htb]
  exact run_siftBandsRanges_band hm hp hk

private theorem siftBandsRow_pre (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hc' : ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m)) / m + 1).toNat] = pref' ++ cur' :: suff')
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb pref' (cur' :: suff') (o', st')) :
    IsSieveSetup g sd ∧ SiftState.WF g sd st' ∧ 0 ≤ a ∧ a ≤ g.sift.check.height ∧
      |bFirst + cur * bandStep m + cur' * m| ≤ g.sift.check.height ∧
      (a = 0 → 1 ≤ bFirst + cur * bandStep m + cur' * m) ∧
      RangesIn sd.wLowAll sd.wHighAll (rangeList (siftBandsRanges g sd st'.tube.bands a
        (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
        (g.sieveMode == 1)).run) ∧
      ((g.sieveMode == 1) = true → st'.tube.bands.bandNr[(bFirst + cur * bandStep m + cur' * m -
        (bFirst + cur * bandStep m)).toNat]! = 0 → (siftBandsRanges g sd st'.tube.bands a
        (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
        (g.sieveMode == 1)).run.1 = 0) := by
  have hm : 0 < m := by lia [hpre.2.2.2.2.2.1]
  obtain ⟨hR, hband, hk⟩ := siftBandsRow_ranges hpre hv htb hc' hv'
  obtain ⟨-, ⟨h1, -⟩, -⟩ := hv'.cont
  have h0 := Int.mul_nonneg (Int.natCast_nonneg cur) (show 0 ≤ bandStep m by
    lia [bandLen_bandStep hm])
  have h0' := Int.mul_nonneg (Int.natCast_nonneg cur') hm.le
  have hE : bandEnd g.sift.check.height (bFirst + cur * bandStep m) m ≤ g.sift.check.height := by
    rw [bandEnd]; split_ifs <;> lia
  obtain ⟨hS, -, -, ha, haH, -, hb, hab⟩ := hpre
  refine ⟨hS, h1, ha, haH, abs_le.mpr ⟨by lia, by lia⟩, fun h ↦ by lia [hab h], ?_,
    fun h hz ↦ fst_siftBandsRanges_eq_zero h hz⟩
  rw [hR]
  exact rangesIn_bandRanges (by lia [hS.isRowSetup.one_le_wHighAll_sub_wLowAll])
    (by rw [hband]; lia) (by rw [hband]; lia)

private theorem siftBandsRow_points (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hc' : ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m)) / m + 1).toNat] = pref' ++ cur' :: suff')
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb pref' (cur' :: suff') (o', st')) :
    siftBandsRowPoints g.sift sd a (bFirst + cur * bandStep m + cur' * m)
        (siftBandsRanges g sd st'.tube.bands a (bFirst + cur * bandStep m + cur' * m)
          (bFirst + cur * bandStep m) (g.sieveMode == 1)).run =
      rowsPoints g sd a bFirst m [bFirst + cur * bandStep m + cur' * m] := by
  obtain ⟨hR, hband, hk⟩ := siftBandsRow_ranges hpre hv htb hc' hv'
  have h0' := Int.mul_nonneg (Int.natCast_nonneg cur') (show 0 ≤ m by lia [hpre.2.2.2.2.2.1])
  rw [hR, rowsPoints_singleton hpre.2.2.1
    (by lia [hpre.1.isRowSetup.one_le_wHighAll_sub_wLowAll]) (by rw [hband]; lia)
    (by rw [hband]; lia)]

private theorem siftBandsRow_return (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hc' : ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m)) / m + 1).toNat] = pref' ++ cur' :: suff')
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb pref' (cur' :: suff') (o', st'))
    {found : Bool}
    (hp : SiftState.WF g sd s' ∧ s'.tube = st'.tube ∧ s'.out = st'.out.appendPoints g.sift.check
      (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a
        (bFirst + cur * bandStep m + cur' * m) (siftBandsRanges g sd st'.tube.bands a
          (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
          (g.sieveMode == 1)).run)) ∧
      found = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a
        (bFirst + cur * bandStep m + cur' * m) (siftBandsRanges g sd st'.tube.bands a
          (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
          (g.sieveMode == 1)).run).isEmpty))
    (hf : found = true) :
    SiftBandsBandInvariant g sd s0 a bFirst m tb
      (ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
        (bFirst + cur * bandStep m)) / m + 1).toNat]) [] (some (true, s'), s') := by
  have hW := siftBandsRow_points hpre hv htb hc' hv'
  obtain ⟨-, ⟨-, h2, h3⟩, -⟩ := hv'.cont
  obtain ⟨g1, -, g3, g4⟩ := hp
  rw [hW] at g3 g4
  rw [htb, bandB0_siftBandsBand] at h2 h3
  obtain ⟨r, hr⟩ := rowsBelow_append_prefix (by lia [hpre.2.2.2.2.2.1]) hc'
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_found (out := s0.out)
    (R := rowsPoints g sd a bFirst m r) h3 g4
    (by rw [hf] at g4 ⊢; exact ((Bool.and_eq_true _ _).mp g4.symm).1)
  rw [← h2, ← g3] at f1
  rw [List.map_append, List.map_singleton, ← List.append_assoc] at hr
  rw [← rowsPoints_append, ← rowsPoints_append, hr] at f1 f2
  exact ⟨rfl, g1, f1, f2⟩

private theorem siftBandsRow_next (hpre : SiftBandsPre g sd s0 a bFirst m)
    (hv : SiftBandsInvariant g sd s0 a bFirst m pref (cur :: suff) (o, st))
    (htb : tb = (siftBandsBand sd st.tube (bFirst + cur * bandStep m)
      (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)).run)
    (hc' : ForIn.toList [:((bandEnd g.sift.check.height (bFirst + cur * bandStep m) m -
      (bFirst + cur * bandStep m)) / m + 1).toNat] = pref' ++ cur' :: suff')
    (hv' : SiftBandsBandInvariant g sd s0 a bFirst m tb pref' (cur' :: suff') (o', st'))
    {found : Bool}
    (hp : SiftState.WF g sd s' ∧ s'.tube = st'.tube ∧ s'.out = st'.out.appendPoints g.sift.check
      (firstIf g.sift.check.onePoint (siftBandsRowPoints g.sift sd a
        (bFirst + cur * bandStep m + cur' * m) (siftBandsRanges g sd st'.tube.bands a
          (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
          (g.sieveMode == 1)).run)) ∧
      found = (g.sift.check.onePoint && !(siftBandsRowPoints g.sift sd a
        (bFirst + cur * bandStep m + cur' * m) (siftBandsRanges g sd st'.tube.bands a
          (bFirst + cur * bandStep m + cur' * m) (bFirst + cur * bandStep m)
          (g.sieveMode == 1)).run).isEmpty))
    (hf : ¬found = true) :
    SiftBandsBandInvariant g sd s0 a bFirst m tb (pref' ++ [cur']) suff' (none, s') := by
  have hW := siftBandsRow_points hpre hv htb hc' hv'
  obtain ⟨-, ⟨-, h2, h3⟩, ht⟩ := hv'.cont
  obtain ⟨g1, g2, g3, g4⟩ := hp
  rw [hW] at g3 g4
  have hb := bandB0_siftBandsBand sd st.tube (bFirst + cur * bandStep m)
    (bandEnd g.sift.check.height (bFirst + cur * bandStep m) m) (g.sieveMode == 1)
  rw [← htb] at hb
  rw [hb] at h2 h3
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_not_found (out := s0.out) h3 g4
    (by rw [Bool.eq_false_iff.mpr hf, Bool.false_and]; decide)
  rw [← h2, ← g3, ← rowsPoints_append] at f1
  rw [← rowsPoints_append] at f2
  refine siftBandsBandInvariant_none.mpr ⟨⟨g1, ?_, ?_⟩, g2.trans ht⟩ <;>
    rw [hb, List.map_append, List.map_singleton, ← List.append_assoc]
  · exact f1
  · exact f2

end SiftBands

/-- `sift_bands` in the tube or the real region (`sieve_mode ≠ 0`) prints the points that it finds
in the rows of the first coordinate `0 ≤ a ≤ H` from `b_first ≥ -H` on by the step `m ≥ 1`, from
`b_first ≥ 1` for `a = 0` (`JPoints.bandsPoints`): for each band the analysis of the tube for `a`
and the band, and for each row of the band that the analysis and the condition at 2 leave, its
ranges of words, each sieved word by word in the tube or chunk by chunk in the region; only the
first point under `-1`. The flag returned says whether it stopped at a point under `-1`. -/
@[spec]
theorem siftBands_spec (g : BandGlobals) (sd : SiftData) (s : SiftState) (a bFirst m : ℤ) :
    ⦃ SiftBandsPre g sd s a bFirst m ⦄
    siftBands g sd s a bFirst m
    ⦃ fun r ↦ r.2.WF g sd ∧ r.2.out = s.out.appendPoints g.sift.check
          (firstIf g.sift.check.onePoint (bandsPoints g sd a bFirst m)) ∧
        r.1 = (g.sift.check.onePoint && !(bandsPoints g sd a bFirst m).isEmpty) ⦄ := by
  vcgen [siftBands, siftBandsRow_spec, tubeAInit_spec,
    Std.WP.Id.triple_eq_run (siftBandsBand _ _ _ _ _)] invariants
  | inv1 => SiftBandsInvariant g sd s a bFirst m
  | inv2 tb _ => SiftBandsBandInvariant g sd s a bFirst m tb
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact siftBands_tube_wf ‹_›
    | exact siftBandsInvariant_init ‹_› ‹_›
    | exact siftBands_post_some ‹_› ‹_›
    | exact siftBands_post_end ‹_› ‹_› ‹_›
    | exact siftBandsBandInvariant_init ‹_› ‹_› ‹_›
    | exact siftBandsBand_post_some ‹_› ‹_›
    | exact siftBandsBand_post_end ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_pre ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_return ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRow_next ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end JPoints

end
