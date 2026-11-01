/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.RowRegion
public import JPoints.Proof.Scan
public import JPoints.Proof.Tube

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Order
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The ranges of the rows of a band

The ranges of words that `sift_bands` sieves in a row of a band: those of the real region of the
row (`row_region`, `JPoints.rowRegion_spec`), in increasing order within the words of the row
(`JPoints.RangesIn`); those of the bands of the analysis of the tube, copied or cut to the real
region (`JPoints.siftBandsRanges_spec`, `JPoints.bandRowRanges`); and the bands that the analysis
of a band collects (`JPoints.siftBandsBand_spec`), the same for every consistent state of the
analysis with the polynomials of the first coordinate (`JPoints.rowRanges_siftBandsBand`). The
points that the sieve finds in the ranges of a row (`JPoints.rangesPoints`) are those of the
specification (`JPoints.bandRowPoints_eq_rangesPoints`), and a word that lies in a range of the
tube and, where `sift_bands` reads the real region, in one of its ranges lies in a range of the row
(`JPoints.exists_mem_rangeList_bandRowRanges`).

## Main definitions

* `JPoints.bandRowRanges`: the ranges of a row of a band from those of its bands.
* `JPoints.resetBands`: the bands set up for a band of rows.
* `JPoints.rangesPoints`: the points of the ranges of a row.
* `JPoints.CopyRangesInvariant`: the invariant of a loop.

## Main statements

* `JPoints.siftBandsRanges_spec`: the ranges of a row of a band.
* `JPoints.siftBandsBand_spec`: the analysis of a band.
* `JPoints.rowRanges_siftBandsBand`: the ranges of a row of a band from two states of the
  analysis.
* `JPoints.bandRowPoints_eq_rangesPoints`, `JPoints.rangesIn_bandRanges`: the points of the
  ranges of a row, and the order of the ranges.
* `JPoints.rangesPoints_eq_append`: the points of the ranges of a row around one of them.
* `JPoints.bandRanges_eq_bandRowRanges`, `JPoints.exists_mem_rangeList_bandRowRanges`: the ranges
  of a row from those of the tube and of the real region, and the words that they keep.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants; the values of the components follow from them (`JPoints.run_siftBandsRanges`,
`JPoints.run_siftBandsBand`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The ranges of a row of a band -/

/-- The ranges of words that `sift_bands` sieves in the row `(a, b)` whose ranges in the bands are
`rs`, for the globals `g` and the static data `sd` (`JPoints.siftBandsRanges`): in the tube without
the cut, `rs`; in the tube with the cut, `rs` cut to the ranges of the real region of the row
(`JPoints.cutRanges`, `JPoints.rowRegion`); in the region, the ranges of the real region. -/
def bandRowRanges (g : BandGlobals) (sd : SiftData) (rs : List (ℤ × ℤ)) (a b : ℤ) (tube : Bool) :
    ℕ × Array ℤ × Array ℤ :=
  if tube && !g.tubeCut then (rs.length, (rs.map Prod.fst).toArray, (rs.map Prod.snd).toArray)
  else if tube then
    ((cutRanges rs (rangeList (rowRegion g.neg sd a b).run)).length,
      ((cutRanges rs (rangeList (rowRegion g.neg sd a b).run)).map Prod.fst).toArray,
      ((cutRanges rs (rangeList (rowRegion g.neg sd a b).run)).map Prod.snd).toArray)
  else (rowRegion g.neg sd a b).run

/-- The invariant of the loop of `JPoints.siftBandsRanges` that copies the ranges of the `row`-th
row of the bands. -/
def CopyRangesInvariant (bd : TubeBands) (row : ℕ) :
    Std.WP.Invariant ℕ (Array ℤ × Array ℤ) Prop :=
  fun pref _ st ↦ st.1 = (pref.map (bd.blo row)).toArray ∧ st.2 = (pref.map (bd.bhi row)).toArray

section SiftBandsRanges

variable {g : BandGlobals} {sd : SiftData} {bd : TubeBands} {a b bLo : ℤ} {tube : Bool}
  {row n : ℕ} {lo hi lo' hi' : Array ℤ} {pref suff : List ℕ} {cur : ℕ}

private theorem copyRangesInvariant_step
    (h : CopyRangesInvariant bd row pref (cur :: suff) (lo, hi)) :
    CopyRangesInvariant bd row (pref ++ [cur]) suff (lo.push (bd.blo row cur),
      hi.push (bd.bhi row cur)) := by
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  rw [h1, h2]
  exact ⟨by simp, by simp⟩

private theorem copyRanges_post (hc : (tube && !g.tubeCut) = true)
    (h : CopyRangesInvariant bd (b - bLo).toNat (ForIn.toList [:bd.bandNr[(b - bLo).toNat]!]) []
      (lo, hi)) :
    (bd.bandNr[(b - bLo).toNat]!, lo, hi) =
      bandRowRanges g sd (bd.rowRanges (b - bLo).toNat) a b tube := by
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  rw [bandRowRanges, ite_eq_left hc, h1, h2, TubeBands.length_rowRanges,
    Std.Legacy.Range.toList_eq_range]
  simp [TubeBands.rowRanges]

private theorem cutRanges_post (hc : ¬(tube && !g.tubeCut) = true) (ht : tube = true)
    (hr : (n, lo, hi) = (rowRegion g.neg sd a b).run) {r : ℕ × Array ℤ × Array ℤ}
    (h : r = ((cutRanges (bd.rowRanges (b - bLo).toNat) (rangeList (n, lo, hi))).length,
      ((cutRanges (bd.rowRanges (b - bLo).toNat) (rangeList (n, lo, hi))).map Prod.fst).toArray,
      ((cutRanges (bd.rowRanges (b - bLo).toNat) (rangeList (n, lo, hi))).map Prod.snd).toArray)) :
    r = bandRowRanges g sd (bd.rowRanges (b - bLo).toNat) a b tube := by
  rw [bandRowRanges, ite_eq_right hc, ite_eq_left ht, ← hr, h]

private theorem region_post (hc : ¬(tube && !g.tubeCut) = true) (ht : ¬tube = true)
    {r : ℕ × Array ℤ × Array ℤ} (hr : r = (rowRegion g.neg sd a b).run) :
    r = bandRowRanges g sd (bd.rowRanges (b - bLo).toNat) a b tube := by
  rw [bandRowRanges, ite_eq_right hc, ite_eq_right ht, hr]

end SiftBandsRanges

theorem siftBandsRanges_spec (g : BandGlobals) (sd : SiftData) (bd : TubeBands) (a b bLo : ℤ)
    (tube : Bool) :
    ⦃ True ⦄
    siftBandsRanges g sd bd a b bLo tube
    ⦃ fun r ↦ r = bandRowRanges g sd (bd.rowRanges (b - bLo).toNat) a b tube ⦄ := by
  vcgen [siftBandsRanges, rowCut_spec, Std.WP.Id.triple_eq_run (rowRegion _ _ _ _)] invariants
  · CopyRangesInvariant bd (b - bLo).toNat
  all_goals try dsimp only at *
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact copyRangesInvariant_step ‹_›
    | exact copyRanges_post ‹_› ‹_›
    | exact cutRanges_post ‹_› ‹_› ‹_› ‹_›
    | exact region_post ‹_› ‹_› ‹_›

/-! ### The band of a row -/

/-- The bands `bd` as `sift_bands` sets them up for the band of the rows `bLo..bHi` in the tube
before its analysis: the first row `bLo`, and the counts of the ranges of its rows `0`. -/
def resetBands (bd : TubeBands) (bLo bHi : ℤ) : TubeBands :=
  { bd with
    bandB0 := bLo
    bandNr := (List.range (bHi - bLo + 1).toNat).foldl (fun a (k : ℕ) ↦ a.set! k 0) bd.bandNr }

@[simp]
theorem bandB0_resetBands (bd : TubeBands) (bLo bHi : ℤ) : (resetBands bd bLo bHi).bandB0 = bLo :=
  rfl

@[simp]
theorem bandRg_resetBands (bd : TubeBands) (bLo bHi : ℤ) :
    (resetBands bd bLo bHi).bandRg = bd.bandRg :=
  rfl

theorem size_resetBands (bd : TubeBands) (bLo bHi : ℤ) :
    (resetBands bd bLo bHi).bandNr.size = bd.bandNr.size ∧
      (resetBands bd bLo bHi).bandRg.size = bd.bandRg.size :=
  ⟨Array.size_foldl_range_set! .., rfl⟩

theorem getElem!_bandNr_resetBands (bd : TubeBands) (bLo bHi : ℤ) (r : ℕ) :
    (resetBands bd bLo bHi).bandNr[r]! =
      if r < (bHi - bLo + 1).toNat ∧ r < bd.bandNr.size then 0 else bd.bandNr[r]! :=
  Array.getElem!_foldl_range_set! ..

theorem resetBands_sized {bd : TubeBands} (h1 : bd.bandNr.size = tubeBand)
    (h2 : bd.bandRg.size = 2 * tubeRanges * tubeBand) {bLo bHi : ℤ}
    (hn : (bHi - bLo + 1).toNat ≤ tubeBand) :
    (resetBands bd bLo bHi).Sized (bHi - bLo + 1).toNat ∧
      ∀ r < (bHi - bLo + 1).toNat, (resetBands bd bLo bHi).rowRanges r = [] := by
  have hz (r : ℕ) (hr : r < (bHi - bLo + 1).toNat) : (resetBands bd bLo bHi).bandNr[r]! = 0 := by
    rw [getElem!_bandNr_resetBands, ite_eq_left ⟨hr, by lia⟩]
  refine ⟨⟨(size_resetBands ..).1.trans h1, h2, hn,
    fun {r} hr ↦ by rw [hz r hr]; exact Nat.zero_le _⟩, fun r hr ↦ ?_⟩
  rw [TubeBands.rowRanges, hz r hr, List.range_zero, List.map_nil]

private theorem resetBandsInvariant_step {bd : TubeBands} {bLo : ℤ} {A : Array ℕ} {R : Array ℤ}
    {pref : List ℕ} {cur : ℕ}
    (h : bd = { bandB0 := bLo, bandNr := pref.foldl (fun a (k : ℕ) ↦ a.set! k 0) A, bandRg := R }) :
    ({ bandB0 := bd.bandB0, bandNr := bd.bandNr.set! cur 0, bandRg := bd.bandRg } : TubeBands) =
      { bandB0 := bLo, bandNr := (pref ++ [cur]).foldl (fun a (k : ℕ) ↦ a.set! k 0) A,
        bandRg := R } := by
  subst h
  simp [List.foldl_append]

private theorem siftBandsBand_post_tube {sd : SiftData} {t r : TubeState} {bLo bHi : ℤ}
    {tube : Bool} (ht : tube = true) {bd : TubeBands}
    (hb : bd =
      { bandB0 := bLo
        bandNr := (ForIn.toList [:(bHi - bLo + 1).toNat]).foldl (fun a (k : ℕ) ↦ a.set! k 0)
          t.bands.bandNr
        bandRg := t.bands.bandRg })
    (hr : r = (tubeCell sd.th sd.th2 { t with bands := bd } bLo bHi sd.wLowAll sd.wHighAll).run) :
    r = if tube then (tubeCell sd.th sd.th2 { t with bands := resetBands t.bands bLo bHi }
        bLo bHi sd.wLowAll sd.wHighAll).run
      else { t with bands := { t.bands with bandB0 := bLo } } := by
  rw [ite_eq_left ht, hr, hb, Std.Legacy.Range.toList_eq_range]
  rfl

theorem siftBandsBand_spec (sd : SiftData) (t : TubeState) (bLo bHi : ℤ) (tube : Bool) :
    ⦃ True ⦄
    siftBandsBand sd t bLo bHi tube
    ⦃ fun r ↦ r = if tube then (tubeCell sd.th sd.th2 { t with bands := resetBands t.bands bLo bHi }
        bLo bHi sd.wLowAll sd.wHighAll).run
      else { t with bands := { t.bands with bandB0 := bLo } } ⦄ := by
  vcgen [siftBandsBand, Std.WP.Id.triple_eq_run (tubeCell _ _ _ _ _ _ _)] invariants
  · fun pref _ bd ↦ bd =
      { bandB0 := bLo
        bandNr := pref.foldl (fun a (k : ℕ) ↦ a.set! k 0) t.bands.bandNr
        bandRg := t.bands.bandRg }
  all_goals try dsimp only at *
  all_goals first
    | rfl
    | exact resetBandsInvariant_step ‹_›
    | exact (ite_eq_right ‹_›).symm
    | exact siftBandsBand_post_tube ‹_› ‹_› ‹_›

theorem run_siftBandsRanges (g : BandGlobals) (sd : SiftData) (bd : TubeBands) (a b bLo : ℤ)
    (tube : Bool) :
    (siftBandsRanges g sd bd a b bLo tube).run =
      bandRowRanges g sd (bd.rowRanges (b - bLo).toNat) a b tube :=
  (siftBandsRanges_spec g sd bd a b bLo tube).le_wp trivial

theorem run_siftBandsBand (sd : SiftData) (t : TubeState) (bLo bHi : ℤ) (tube : Bool) :
    (siftBandsBand sd t bLo bHi tube).run = if tube then (tubeCell sd.th sd.th2
        { t with bands := resetBands t.bands bLo bHi } bLo bHi sd.wLowAll sd.wHighAll).run
      else { t with bands := { t.bands with bandB0 := bLo } } :=
  (siftBandsBand_spec sd t bLo bHi tube).le_wp trivial

theorem bandB0_siftBandsBand (sd : SiftData) (t : TubeState) (bLo bHi : ℤ) (tube : Bool) :
    (siftBandsBand sd t bLo bHi tube).run.bands.bandB0 = bLo := by
  rw [run_siftBandsBand]
  split_ifs
  · rw [bandB0_run_tubeCell]
    rfl
  · rfl

theorem fst_siftBandsRanges_eq_zero {g : BandGlobals} {sd : SiftData} {bd : TubeBands}
    {a b bLo : ℤ} {tube : Bool} (ht : tube = true) (hb : bd.bandNr[(b - bLo).toNat]! = 0) :
    (siftBandsRanges g sd bd a b bLo tube).run.1 = 0 := by
  have h : bd.rowRanges (b - bLo).toNat = [] := List.eq_nil_of_length_eq_zero
    ((TubeBands.length_rowRanges ..).trans hb)
  rw [run_siftBandsRanges, h, ht]
  simp [bandRowRanges, cutRanges_nil_left]

theorem bandRowRanges_congr {g : BandGlobals} {sd : SiftData} {rs rs' : List (ℤ × ℤ)} {a b : ℤ}
    {tube : Bool} (h : tube = true → rs = rs') :
    bandRowRanges g sd rs a b tube = bandRowRanges g sd rs' a b tube := by
  cases tube
  · rfl
  · rw [h rfl]

/-- The analysis of the band of the rows `bLo..bHi` from two consistent states of the analysis with
the same polynomials gives each row of the band the same ranges: the bands set up for the band hold
no ranges in its rows, and the analyses of the band agree row by row
(`JPoints.TubeState.BandSim.run_tubeCell`). -/
theorem rowRanges_siftBandsBand {sd : SiftData} {t T : TubeState} (ht : t.WF) (hT : T.WF)
    (hp : T.EqPolys t) {bLo bHi : ℤ} (hlo : bLo ≤ bHi) (hn : bHi - bLo + 1 ≤ tubeBand) {r : ℕ}
    (hr : r < (bHi - bLo + 1).toNat) :
    (siftBandsBand sd t bLo bHi true).run.bands.rowRanges r =
      (siftBandsBand sd T bLo bHi true).run.bands.rowRanges r := by
  obtain ⟨r1, r2⟩ := resetBands_sized hT.size_bandNr hT.size_bandRg (bLo := bLo) (bHi := bHi)
    (by lia)
  obtain ⟨f1, f2⟩ := resetBands_sized ht.size_bandNr ht.size_bandRg (bLo := bLo) (bHi := bHi)
    (by lia)
  have hs : TubeState.BandSim (bHi - bLo + 1).toNat { T with bands := resetBands T.bands bLo bHi }
      { t with bands := resetBands t.bands bLo bHi } :=
    ⟨hT.with_bands r1.size_bandNr r1.size_bandRg, ht.with_bands f1.size_bandNr f1.size_bandRg,
      hp, rfl, r1, f1, fun {r} hr ↦ by rw [r2 r hr, f2 r hr]⟩
  rw [run_siftBandsBand, run_siftBandsBand, ite_eq_left rfl, ite_eq_left rfl]
  exact (hs.run_tubeCell sd.th sd.th2 le_rfl hlo (by rw [bandB0_resetBands]; lia) sd.wLowAll
    sd.wHighAll).rowRanges_eq hr

/-! ### The points of the ranges of a row -/

/-- The points that the sieve of the row `(a, b)` finds in the ranges of words `R = (n, lo, hi)`:
those of each range `[lo[k], hi[k])` (`JPoints.rowRangePoints`), range after range. -/
def rangesPoints (g : SiftGlobals) (sd : SiftData) (a b : ℤ) (R : ℕ × Array ℤ × Array ℤ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  (rangeList R).flatMap fun r ↦ rowRangePoints g sd a b r.1 r.2

theorem rangesPoints_eq_nil_of_fst_eq_zero {g : SiftGlobals} {sd : SiftData} {a b : ℤ}
    {R : ℕ × Array ℤ × Array ℤ} (h : R.1 = 0) : rangesPoints g sd a b R = [] := by
  simp [rangesPoints, rangeList, h]

theorem rangesPoints_eq_append {g : SiftGlobals} {sd : SiftData} {a b : ℤ} {n k : ℕ}
    {lo hi : Array ℤ} (h : k < n) :
    rangesPoints g sd a b (n, lo, hi) =
      ((rangeList (n, lo, hi)).take k).flatMap (fun r ↦ rowRangePoints g sd a b r.1 r.2) ++
        rowRangePoints g sd a b lo[k]! hi[k]! ++
        ((rangeList (n, lo, hi)).drop (k + 1)).flatMap fun r ↦ rowRangePoints g sd a b r.1 r.2 := by
  have e := List.take_append_drop (k + 1) (rangeList (n, lo, hi))
  rw [rangeList_take_succ h] at e
  rw [rangesPoints]
  nth_rw 1 [← e]
  simp

theorem flatMap_rowRangePoints (g : SiftGlobals) (sd : SiftData) (a b : ℤ) {rs : List (ℤ × ℤ)}
    (hrs : rs.Pairwise fun r s ↦ r.2 ≤ s.1) :
    rs.flatMap (fun r ↦ rowRangePoints g sd a b r.1 r.2) =
      ((intRange g.check.H).filter fun c ↦ colKeeps g sd a b c && !conic a b c &&
        rs.any fun r ↦ decide (r.1 ≤ c >>> longShift ∧ c >>> longShift < r.2)).flatMap
        fun c ↦ g.check.points (a, b, c) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.pairwise_cons] at hrs
    rw [List.flatMap_cons, ih hrs.2, rowRangePoints, ← List.flatMap_append,
      List.filter_append_filter_of_pairwise (pairwise_lt_intRange _) fun x _ y _ hx hy ↦ ?_]
    · congr 1
      refine List.filter_congr fun c _ ↦ ?_
      rw [List.any_cons]
      cases colKeeps g sd a b c <;> cases conic a b c <;> simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hx hy
      obtain ⟨-, s, hs, hs'⟩ := hy
      have := hrs.1 s hs
      rw [Int.shiftRight_eq_div_pow] at hx hs'
      simp only [longShift] at hx hs'
      lia

theorem bandRowPoints_eq_rangesPoints {g : BandGlobals} {sd : SiftData} {a bFirst m b : ℤ}
    (hmode : g.sieveMode ≠ 0)
    (hr : RangesIn sd.wLowAll sd.wHighAll (rangeList (bandRanges g sd a bFirst m b))) :
    bandRowPoints g sd a bFirst m b =
      rangesPoints g.sift sd a b (bandRanges g sd a bFirst m b) := by
  rw [rangesPoints, flatMap_rowRangePoints _ _ _ _ hr.2, bandRowPoints]
  congr 1
  refine List.filter_congr fun c _ ↦ ?_
  have h0 : (g.sieveMode == 0) = false := beq_eq_false_iff_ne.mpr hmode
  simp only [bandKeeps, h0, Bool.false_or, rangeList, List.any_map, Function.comp_def]
  cases colKeeps g.sift sd a b c <;> cases conic a b c <;> simp

theorem rangesIn_rowRanges_siftBandsBand {sd : SiftData} (hw : sd.wLowAll < sd.wHighAll)
    {T : TubeState} (hT : T.WF) {bLo bHi b : ℤ} (hb : bLo ≤ b) (hbH : b ≤ bHi)
    (hn : bHi - bLo + 1 ≤ tubeBand) :
    RangesIn sd.wLowAll sd.wHighAll
      ((siftBandsBand sd T bLo bHi true).run.bands.rowRanges (b - bLo).toNat) := by
  obtain ⟨r1, r2⟩ := resetBands_sized hT.size_bandNr hT.size_bandRg (bLo := bLo) (bHi := bHi)
    (by lia)
  rw [run_siftBandsBand, ite_eq_left rfl]
  obtain ⟨-, h2, -⟩ := r1.rangesIn_run_tubeCell sd.th sd.th2 (L := sd.wLowAll)
    { T with bands := resetBands T.bands bLo bHi } bLo bHi sd.wLowAll sd.wHighAll
    (le_refl bLo) (by rw [bandB0_resetBands]; lia) le_rfl hw
    fun r hr _ _ ↦ by rw [r2 r hr]; exact rangesIn_nil _ _
  exact h2 _ (by lia) (by rw [bandB0_resetBands]; lia) (by rw [bandB0_resetBands]; lia)

theorem rangesIn_bandRowRanges {g : BandGlobals} {sd : SiftData} (hw : sd.wLowAll < sd.wHighAll)
    {rs : List (ℤ × ℤ)} {a b : ℤ} {tube : Bool}
    (hrs : tube = true → RangesIn sd.wLowAll sd.wHighAll rs) :
    RangesIn sd.wLowAll sd.wHighAll (rangeList (bandRowRanges g sd rs a b tube)) := by
  have hreg := (rowRegion_spec g.neg sd a b).le_wp hw
  simp only [bandRowRanges]
  split_ifs with h1 h2
  · rw [rangeList_ofList]
    exact hrs (by simp_all)
  · rw [rangeList_ofList]
    exact (hrs h2).cutRanges hreg
  · exact hreg

theorem rangesIn_bandRanges {g : BandGlobals} {sd : SiftData} (hw : sd.wLowAll < sd.wHighAll)
    {a bFirst m b : ℤ} (hb : (bandOf g.sift.check.height bFirst m b).1 ≤ b)
    (hbH : b ≤ (bandOf g.sift.check.height bFirst m b).2) :
    RangesIn sd.wLowAll sd.wHighAll (rangeList (bandRanges g sd a bFirst m b)) := by
  have hn := bandOf_snd_le (Prod.ext rfl rfl : bandOf g.sift.check.height bFirst m b =
    ((bandOf g.sift.check.height bFirst m b).1, (bandOf g.sift.check.height bFirst m b).2))
  rw [bandRanges]
  dsimp only
  rw [run_siftBandsRanges]
  refine rangesIn_bandRowRanges hw fun ht ↦ ?_
  rw [ht]
  exact rangesIn_rowRanges_siftBandsBand hw (wf_run_tubeAInit_initial ..) hb hbH hn


/-! ### The words that the ranges of a row keep -/

/-- The ranges of the row `b` of the band `bLo..bHi` that holds it (`JPoints.bandRanges`) are those
that `JPoints.bandRowRanges` makes of the ranges of the row that the analysis of the band collects
from the polynomials of the first coordinate. -/
theorem bandRanges_eq_bandRowRanges {g : BandGlobals} {sd : SiftData}
    {a bFirst m b bLo bHi : ℤ} (hband : bandOf g.sift.check.height bFirst m b = (bLo, bHi)) :
    bandRanges g sd a bFirst m b = bandRowRanges g sd ((siftBandsBand sd
        (tubeAInit g.kd g.sift.check.height sd.th sd.th2 .initial a).run bLo bHi
        (g.sieveMode == 1)).run.bands.rowRanges (b - bLo).toNat) a b (g.sieveMode == 1) := by
  rw [bandRanges, hband]
  exact run_siftBandsRanges ..

theorem bandKeeps_eq_true_iff {g : BandGlobals} {sd : SiftData} {a bFirst m b c : ℤ} :
    bandKeeps g sd a bFirst m b c = true ↔ g.sieveMode = 0 ∨
      ∃ r ∈ rangeList (bandRanges g sd a bFirst m b),
        r.1 ≤ c >>> longShift ∧ c >>> longShift < r.2 := by
  simp [bandKeeps, rangeList]

/-- A word that lies in a range of the ranges `rs` of the row `(a, b)` in the bands of the tube and,
where `sift_bands` reads the real region (in the region, and in the tube with the cut), in a range
of the real region of the row (`JPoints.rowRegion`), lies in a range that `sift_bands` sieves in the
row (`JPoints.bandRowRanges`): the cut keeps the words of both (`JPoints.exists_mem_cutRanges`). -/
theorem exists_mem_rangeList_bandRowRanges {g : BandGlobals} {sd : SiftData}
    (hw : sd.wLowAll < sd.wHighAll) {rs : List (ℤ × ℤ)} {a b : ℤ} {tube : Bool} {x : ℤ}
    (hrs : tube = true → RangesIn sd.wLowAll sd.wHighAll rs)
    (hT : tube = true → ∃ r ∈ rs, r.1 ≤ x ∧ x < r.2)
    (hR : (tube && !g.tubeCut) = false →
      ∃ r ∈ rangeList (rowRegion g.neg sd a b).run, r.1 ≤ x ∧ x < r.2) :
    ∃ r ∈ rangeList (bandRowRanges g sd rs a b tube), r.1 ≤ x ∧ x < r.2 := by
  have hreg := (rowRegion_spec g.neg sd a b).le_wp hw
  simp only [bandRowRanges]
  split_ifs with h1 h2
  · rw [rangeList_ofList]
    exact hT (by simp_all)
  · rw [rangeList_ofList]
    exact exists_mem_cutRanges (hrs h2).2 hreg.2 (hT h2) (hR (by simp [h1]))
  · exact hR (by simp_all)

end JPoints

end
