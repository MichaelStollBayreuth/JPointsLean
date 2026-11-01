/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Sample
public import JPoints.Proof.Globals
public import Std.WP

import JPoints.Proof.Tube
import JPoints.Proof.Values
import Std.Tactic.Do

/-!
# The contracts of the sample of the tube

What `tube_sample` leaves of the state of the analysis of the tube and of the static data of the
sieve: the analysis of each band of its sample (`JPoints.tubeSampleBand_spec`) and the sample
(`JPoints.tubeSample_spec`) keep the state of the analysis consistent (`JPoints.TubeState.WF`), and
the static data keep the sizes of their arrays, since the sample sets only the bound on the fourth
coordinate, its square and the words of a whole row (`JPoints.SiftData.Sized.with_sample`). The
values of the doubles and of the sums of the sample, which the cost model reads, are not
constrained.

## Main definitions

* `JPoints.TubeSampleBandInvariant`, `JPoints.TubeSampleInvariant`,
  `JPoints.TubeSampleRowsInvariant`: the invariants of the loops.

## Main statements

* `JPoints.tubeSampleBand_spec`: the analysis of a band of the sample.
* `JPoints.tubeSample_spec`: the sample.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` from the
contracts of `tube_a_init` and `tube_cell` (`JPoints.tubeAInit_spec`, `JPoints.tubeCell_spec`) with
named invariants, each verification condition discharged by a lemma in its own shape.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### A band of the sample -/

/-- The invariant of the loop of `JPoints.tubeSampleBand` that sets the counts of the rows of the
band to `0`: the arrays of the bands keep their sizes, `TUBE_BAND` counts and
`2 TUBE_RANGES TUBE_BAND` ends of ranges. -/
def TubeSampleBandInvariant : Std.WP.Invariant ℕ TubeBands Prop :=
  fun _ _ bd ↦ bd.bandNr.size = tubeBand ∧ bd.bandRg.size = 2 * tubeRanges * tubeBand

theorem tubeSampleBandInvariant_initial {t : TubeState} {P : Prop} (h : t.WF ∧ P)
    (pref suff : List ℕ) (b : ℤ) :
    TubeSampleBandInvariant pref suff { t.bands with bandB0 := b } :=
  ⟨h.1.size_bandNr, h.1.size_bandRg⟩

theorem TubeSampleBandInvariant.set! {pref suff : List ℕ} {bd : TubeBands}
    (h : TubeSampleBandInvariant pref suff bd) (pref' suff' : List ℕ) (k n : ℕ) :
    TubeSampleBandInvariant pref' suff' { bd with bandNr := bd.bandNr.set! k n } :=
  ⟨(Array.size_set! ..).trans h.1, h.2⟩

theorem TubeSampleBandInvariant.wf {pref suff : List ℕ} {bd : TubeBands}
    (h : TubeSampleBandInvariant pref suff bd) {t : TubeState} {P : Prop} (ht : t.WF ∧ P)
    (n : ℕ) : { t with tubeNcells := n, bands := bd }.WF :=
  (ht.1.with_tubeNcells n).with_bands h.1 h.2

attribute [local irreducible] TubeSampleBandInvariant in
/-- The analysis of a band of the sample of `tube_sample` (`JPoints.tubeSampleBand`) keeps the
state of the analysis of the tube consistent: `tube_a_init` and `tube_cell` keep it so
(`JPoints.tubeAInit_spec`, `JPoints.tubeCell_spec`), and the counts of the rows of the band are
written within their array. -/
@[spec]
theorem tubeSampleBand_spec (g : CheckGlobals) (kd : TubeCoeffs) (sd : SiftData) (t : TubeState)
    (a bLo bHi wLow wHigh : ℤ) :
    ⦃ t.WF ⦄
    tubeSampleBand g kd sd t a bLo bHi wLow wHigh
    ⦃ fun r ↦ r.WF ⦄ := by
  vcgen [tubeSampleBand] invariants
  · TubeSampleBandInvariant
  all_goals try dsimp only at *
  all_goals first
    | exact tubeSampleBandInvariant_initial ‹_› _ _ _
    | exact TubeSampleBandInvariant.set! ‹_› _ _ _ _
    | exact TubeSampleBandInvariant.wf ‹_› ‹_› _
    | exact ‹TubeState.WF _ ∧ _›.1

/-! ### The sample -/

/-- The invariant of the loop of `JPoints.tubeSample` over the bands of its sample: the state of
the analysis of the tube stays consistent (`JPoints.TubeState.WF`); the sums are not
constrained. -/
def TubeSampleInvariant : Std.WP.Invariant ℕ (TubeState × TubeSampleSums) Prop :=
  fun _ _ st ↦ st.1.WF

/-- The invariant of the loop of `JPoints.tubeSample` over the rows of a band, which changes only
the sums of the sample: no condition. -/
def TubeSampleRowsInvariant : Std.WP.Invariant ℕ TubeSampleSums Prop :=
  fun _ _ _ ↦ True

theorem TubeState.WF.tubeSampleInvariant {t : TubeState} (ht : t.WF) (pref suff : List ℕ)
    (s : TubeSampleSums) : TubeSampleInvariant pref suff (t, s) :=
  ht

theorem TubeSampleInvariant.wf {pref suff : List ℕ} {t : TubeState} {s : TubeSampleSums}
    (h : TubeSampleInvariant pref suff (t, s)) : t.WF :=
  h

theorem tubeSampleRowsInvariant (pref suff : List ℕ) (s : TubeSampleSums) :
    TubeSampleRowsInvariant pref suff s :=
  trivial

theorem SiftData.Sized.with_sample {sd : SiftData} (h : sd.Sized) (th th2 : Double) (lo hi : ℤ) :
    { sd with th, th2, wLowAll := lo, wHighAll := hi }.Sized :=
  ⟨h.size_allOnes, h.size_recip3, h.size_pr, h.size_rowlen, h.size_blocklen, h.size_invp⟩

theorem TubeSampleInvariant.post {pref suff : List ℕ} {t : TubeState} {s : TubeSampleSums}
    (h : TubeSampleInvariant pref suff (t, s)) (sd : SiftData) (th th2 : Double) (lo hi : ℤ) :
    (sd.Sized → { sd with th, th2, wLowAll := lo, wHighAll := hi }.Sized) ∧ t.WF :=
  ⟨fun hs ↦ hs.with_sample th th2 lo hi, h⟩

attribute [local irreducible] TubeSampleInvariant TubeSampleRowsInvariant in
/-- `tube_sample` keeps the state of the analysis of the tube consistent, band by band
(`JPoints.tubeSampleBand_spec`), and the static data that it returns have the sizes of the arrays
of those it is given: it sets only the bound `th` on the fourth coordinate, its square and the words
of a whole row. -/
@[spec]
theorem tubeSample_spec (g : CheckGlobals) (kd : TubeCoeffs) (neg : NegativeIntervals)
    (sd : SiftData) (t : TubeState) :
    ⦃ t.WF ⦄
    tubeSample g kd neg sd t
    ⦃ fun r ↦ (sd.Sized → r.1.Sized) ∧ r.2.1.WF ⦄ := by
  vcgen [tubeSample, Std.WP.Id.triple_eq_run (tubeSampleRow _ _ _ _ _ _ _)] invariants
  · TubeSampleInvariant
  · TubeSampleRowsInvariant
  all_goals try dsimp only at *
  all_goals first
    | exact TubeState.WF.tubeSampleInvariant ‹_› _ _ _
    | exact TubeSampleInvariant.wf ‹_›
    | exact tubeSampleRowsInvariant _ _ _
    | exact TubeSampleInvariant.post ‹_› _ _ _ _ _

end JPoints

end
