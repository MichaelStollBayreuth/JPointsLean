/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.SiftRange

import JPoints.Proof.Bits
import JPoints.Proof.Containers
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The sieve of a range of words of a row of a band

The contracts of the sieve of a range `[lo, hi)` of words of a row in `sift_bands`: in the tube
word by word (`tube_word`, `JPoints.tubeWord_spec`, and `sift_bands_tube`,
`JPoints.siftBandsTube_spec`), and in the real region chunk by chunk (`sift_range`,
`JPoints.siftRange_spec`, and `sift_bands_region`, `JPoints.siftBandsRegion_spec`), the chunk of a
word found by `seek_chunk` (`JPoints.seekChunk_spec`). Both print the points of the row in the
words of the range (`JPoints.rowRangePoints`), only the first under `-1`, and change no field of
the state of the thread but the bit array, the last chunk, the data of the third stage, the
counters and the output (`JPoints.BandRangePost`).

## Main definitions

* `JPoints.TubeWordPre`, `JPoints.TubeWordPost`: the precondition and the postcondition of
  `tube_word`.
* `JPoints.BandRangePre`, `JPoints.BandRangeCont`, `JPoints.BandRangePost`: the precondition and
  the postcondition of the sieve of a range, and the state before a point is returned.
* `JPoints.TubeWordInvariant`, `JPoints.SiftBandsTubeInvariant`,
  `JPoints.SiftBandsRegionInvariant`: the invariants of the loops.

## Main statements

* `JPoints.seekChunk_spec`: the chunk of a word.
* `JPoints.tubeWord_spec`: a word of the tube.
* `JPoints.siftBandsTube_spec`, `JPoints.siftBandsRegion_spec`: a range of words in the tube and
  in the real region.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, each verification condition closed by a lemma stated in its own shape. A range of the
region may run over several chunks: each chunk from that of `lo` on is sieved on the part of the
range that it holds (`JPoints.siftRange_spec`), until the chunk lies beyond `hi`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The chunk of a word -/

namespace IsRowSetup

variable {g : SiftGlobals} {sd : SiftData} (h : IsRowSetup g sd) {k : ℕ}
include h

theorem wHigh_chunk_eq_wLow_chunk (hk : k + 1 < sd.numChunks) :
    (sd.chunks[k]!).wHigh = (sd.chunks[k + 1]!).wLow := by
  rw [h.wHigh_chunk_eq_min (by lia), h.wLow_chunk_eq_min hk]

theorem wLow_chunk_zero (hk : 0 < sd.numChunks) : (sd.chunks[0]!).wLow = sd.wLowAll := by
  have := h.one_le_wHighAll_sub_wLowAll
  rw [h.wLow_chunk_eq_min hk]
  simp only [Nat.zero_mul, Nat.cast_zero, Int.add_zero]
  lia

theorem wHigh_chunk_last (hk : k + 1 = sd.numChunks) : (sd.chunks[k]!).wHigh = sd.wHighAll := by
  rw [h.wHigh_chunk_eq_min (by lia), hk, h.min_numChunks]

theorem succ_lt_numChunks {i : ℤ} (hk : k < sd.numChunks) (hi : i < sd.wHighAll)
    (hw : (sd.chunks[k]!).wHigh ≤ i) : k + 1 < sd.numChunks := by
  by_contra hc
  have := h.wHigh_chunk_last (k := k) (by lia)
  lia

theorem pos_of_lt_wLow_chunk {i : ℤ} (hk : k < sd.numChunks) (hi : sd.wLowAll ≤ i)
    (hw : i < (sd.chunks[k]!).wLow) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h.wLow_chunk_zero hk] at hw; lia
  · exact hk0

end IsRowSetup

section SeekChunk

variable {g : SiftGlobals} {sd : SiftData} {i : ℤ} {cur c mb : ℕ}

private theorem seekUp_step
    (hpre : IsRowSetup g sd ∧ cur < sd.numChunks ∧ sd.wLowAll ≤ i ∧ i < sd.wHighAll)
    (hw : (sd.chunks[c]!).wHigh ≤ i)
    (h : sd.numChunks - c = mb ∧ c < sd.numChunks ∧ (false = true → i < (sd.chunks[c]!).wHigh)) :
    sd.numChunks - (c + 1) < mb ∧ c + 1 < sd.numChunks ∧
      (false = true → i < (sd.chunks[c + 1]!).wHigh) := by
  have := hpre.1.succ_lt_numChunks h.2.1 hpre.2.2.2 hw
  exact ⟨by lia, this, fun h ↦ absurd h Bool.false_ne_true⟩

private theorem seekDown_step
    (hpre : IsRowSetup g sd ∧ cur < sd.numChunks ∧ sd.wLowAll ≤ i ∧ i < sd.wHighAll)
    (hw : i < (sd.chunks[c]!).wLow)
    (h : c = mb ∧ c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧
      (false = true → (sd.chunks[c]!).wLow ≤ i)) :
    c - 1 < mb ∧ c - 1 < sd.numChunks ∧ i < (sd.chunks[c - 1]!).wHigh ∧
      (false = true → (sd.chunks[c - 1]!).wLow ≤ i) := by
  have := hpre.1.pos_of_lt_wLow_chunk h.2.1 hpre.2.2.1 hw
  have e := hpre.1.wHigh_chunk_eq_wLow_chunk (k := c - 1) (by lia)
  rw [Nat.sub_add_cancel this] at e
  exact ⟨by lia, by lia, by rw [e]; exact hw, fun h ↦ absurd h Bool.false_ne_true⟩

private theorem seek_init {P : Prop}
    (h : P ∧ cur < sd.numChunks ∧ sd.wLowAll ≤ i ∧ i < sd.wHighAll) :
    cur < sd.numChunks ∧ (false = true → i < (sd.chunks[cur]!).wHigh) :=
  ⟨h.2.1, fun h ↦ absurd h Bool.false_ne_true⟩

private theorem seekUp_exit (hw : ¬(sd.chunks[c]!).wHigh ≤ i)
    (h : sd.numChunks - c = mb ∧ c < sd.numChunks ∧ (false = true → i < (sd.chunks[c]!).wHigh)) :
    c < sd.numChunks ∧ (True → i < (sd.chunks[c]!).wHigh) :=
  ⟨h.2.1, fun _ ↦ by lia⟩

private theorem seekDown_init (h : c < sd.numChunks ∧ (True → i < (sd.chunks[c]!).wHigh)) :
    c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧ (false = true → (sd.chunks[c]!).wLow ≤ i) :=
  ⟨h.1, h.2 trivial, fun h ↦ absurd h Bool.false_ne_true⟩

private theorem seekDown_exit (hw : ¬i < (sd.chunks[c]!).wLow)
    (h : c = mb ∧ c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧
      (false = true → (sd.chunks[c]!).wLow ≤ i)) :
    c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧ (True → (sd.chunks[c]!).wLow ≤ i) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia⟩

private theorem seek_post (h : c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧
    (True → (sd.chunks[c]!).wLow ≤ i)) :
    c < sd.numChunks ∧ (sd.chunks[c]!).wLow ≤ i ∧ i < (sd.chunks[c]!).wHigh :=
  ⟨h.1, h.2.2 trivial, h.2.1⟩

end SeekChunk

/-- `seek_chunk` finds the chunk of the word `i` of the row from the chunk `cur` on, moving up
while the word lies above the chunk and then down while it lies below. -/
@[spec]
theorem seekChunk_spec (g : SiftGlobals) (sd : SiftData) (cur : ℕ) (i : ℤ) :
    ⦃ IsRowSetup g sd ∧ cur < sd.numChunks ∧ sd.wLowAll ≤ i ∧ i < sd.wHighAll ⦄
    seekChunk sd cur i
    ⦃ fun r ↦ r < sd.numChunks ∧ (sd.chunks[r]!).wLow ≤ i ∧ i < (sd.chunks[r]!).wHigh ⦄ := by
  vcgen [seekChunk] invariants
  · .mk fun exit c ↦ c < sd.numChunks ∧ (exit = true → i < (sd.chunks[c]!).wHigh)
  · Std.WP.Variant.ofMeasure fun c : ℕ ↦ sd.numChunks - c
  · .mk fun exit c ↦ c < sd.numChunks ∧ i < (sd.chunks[c]!).wHigh ∧
      (exit = true → (sd.chunks[c]!).wLow ≤ i)
  · Std.WP.Variant.ofMeasure fun c : ℕ ↦ c
  all_goals try vc_simp
  all_goals first
    | exact seek_init ‹_›
    | exact seekUp_step ‹_› ‹_› ‹_›
    | exact seekUp_exit ‹_› ‹_›
    | exact seekDown_init ‹_›
    | exact seekDown_step ‹_› ‹_› ‹_›
    | exact seekDown_exit ‹_› ‹_›
    | exact seek_post ‹_›

/-! ### A word of the tube -/

/-- The precondition of `JPoints.tubeWord`. -/
abbrev TubeWordPre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b i : ℤ) (mask : UInt64)
    (c0 : ℤ) : Prop :=
  IsRowSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧
    s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧ s.curChunk < sd.numChunks ∧
    sd.wLowAll ≤ i ∧ i < sd.wHighAll ∧ 0 ≤ a ∧ a ≤ g.check.height ∧ |b| ≤ g.check.height ∧
    (a = 0 → 1 ≤ b) ∧ mask = (siftMask g a b).2 ∧ c0 = (siftMask g a b).1

/-- The invariant of the loop of `JPoints.tubeWord` over the primes of the first two stages: the
bits of the word left are those of the mask of the row within the row, without the bit of `c0`,
that the sieve tables of the primes below the cursor admit (`JPoints.CurveTables.admits12`). -/
def TubeWordInvariant (g : SiftGlobals) (sd : SiftData) (a b i c0 : ℤ) :
    Std.WP.Invariant ℕ UInt64 Prop :=
  fun pref _ w ↦ ∀ j < 64, w.toBitVec.getLsbD j = (maskKeeps g a b (64 * i + j) &&
    rangeKeeps g sd (64 * i + j) && (64 * i + j != c0) &&
    pref.all fun n ↦ g.curve.admits12 g.pnn[n]! a b (64 * i + j))

section TubeWord

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {a b i c0 : ℤ} {mask : UInt64}

theorem tubeWordInvariant_init (hpre : TubeWordPre g sd s a b i mask c0) {m0 : UInt64}
    (hm : ∀ j < 64, m0.toBitVec.getLsbD j = (mask.toBitVec.getLsbD j &&
      (i != sd.wLowAll || g.begmask.toBitVec.getLsbD j) &&
      (i != sd.wHighAll - 1 || g.endmask.toBitVec.getLsbD j) &&
      !(c0 >>> longShift == i && j == (c0 % 64).toNat))) {l : List ℕ} :
    TubeWordInvariant g sd a b i c0 [] l m0 := by
  intro j hj
  have hi : (64 * i + j) >>> longShift = i := by
    rw [Int.shiftRight_eq_div_pow]; simp only [longShift]; lia
  have hj' : ((64 * i + j) % 64).toNat = j := by lia
  have hc : (c0 >>> longShift == i && j == (c0 % 64).toNat) = (64 * i + j == c0) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, Int.shiftRight_eq_div_pow, longShift]
    lia
  obtain ⟨-, -, -, -, -, -, h1, h2, -, -, -, -, hmask, -⟩ := hpre
  rw [hm j hj, hc, maskKeeps, hj', ← hmask, rangeKeeps, hi, hj', decide_eq_true ⟨h1, h2⟩]
  simp only [List.all_nil, Bool.and_true, Bool.true_and, bne]
  cases mask.toBitVec.getLsbD j <;> cases (i == sd.wLowAll) <;> cases (i == sd.wHighAll - 1) <;>
    cases (64 * i + j == c0) <;> rfl

theorem _root_.UInt64.getLsbD_not_one_shiftLeft {n j : ℕ} (hn : n < 64) (hj : j < 64) :
    (~~~((1 : UInt64) <<< UInt64.ofNat n)).toBitVec.getLsbD j = !(j == n) := by
  rw [UInt64.toBitVec_not, BitVec.getLsbD_not, ← Nat.toUInt64_eq, UInt64.getLsbD_one_shiftLeft hn]
  by_cases h : j = n <;> simp [hj, h]

theorem tubeWordInvariant_step (hpre : TubeWordPre g sd s a b i mask c0) {cur : ℕ}
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ i ∧ i < (sd.chunks[cur]!).wHigh)
    {pref suff : List ℕ} {n : ℕ} (hc : ForIn.toList [:g.sievePrimes2] = pref ++ n :: suff)
    {w : UInt64} (h : TubeWordInvariant g sd a b i c0 pref (n :: suff) w) :
    TubeWordInvariant g sd a b i c0 (pref ++ [n]) suff (w &&& (g.sieve.sieveTab[n]!)[
      ({ s with curChunk := cur } : SiftState).rowptr[n]! +
      (sd.res0[(i - (sd.chunks[cur]!).wLow).toNat * sd.npr + n]! + (sd.chunks[cur]!).res[n]! -
        if sd.pr[n]! ≤ sd.res0[(i - (sd.chunks[cur]!).wLow).toNat * sd.npr + n]! +
          (sd.chunks[cur]!).res[n]! then sd.pr[n]! else 0)]!) := by
  obtain ⟨hs, hw, hA, hB, -, -, -, -, ha, -⟩ := hpre
  have hn := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 : n < g.sievePrimes3 := by lia [hs.sievePrimes2_le_sievePrimes3]
  have hres := hs.wordResidues hch.1 (k := (i - (sd.chunks[cur]!).wLow).toNat)
    (by lia [hs.range_chunk_le hch.1]) n hn3
  rw [show (sd.chunks[cur]!).wLow + ((i - (sd.chunks[cur]!).wLow).toNat : ℤ) = i by lia] at hres
  have hr : sd.res0[(i - (sd.chunks[cur]!).wLow).toNat * sd.npr + n]! + (sd.chunks[cur]!).res[n]! -
      (if sd.pr[n]! ≤ sd.res0[(i - (sd.chunks[cur]!).wLow).toNat * sd.npr + n]! +
        (sd.chunks[cur]!).res[n]! then sd.pr[n]! else 0) = (i % sd.pr[n]!).toNat := by
    rw [← hres.2.2, Nat.mod_eq_ite_of_lt_two_mul (by lia)]
    split_ifs <;> lia
  intro j hj
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, h j hj, hr,
    hs.toIsStageSetup.getLsbD_sieveTab_eq_admits12 hw hA hB ha hn i hj]
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

theorem _root_.UInt64.getLsbD_not_one_shiftLeft_emod (c : ℤ) {j : ℕ} (hj : j < 64) :
    (~~~((1 : UInt64) <<< UInt64.ofNat (c % 64).toNat)).toBitVec.getLsbD j =
      !(j == (c % 64).toNat) :=
  UInt64.getLsbD_not_one_shiftLeft (by lia) hj

end TubeWord

/-- The postcondition of `JPoints.tubeWord` for the state `s`, the word `i` of the row `(a, b)` and
the result `r`: the fields of the state other than the last chunk, the data of the third stage, the
counters and the output those of `s`, a chunk of the row, consistent data of the third stage, the
points of the row in the word printed (`JPoints.rowRangePoints`), only the first under `-1`, and
the flag of a point under `-1`. -/
def TubeWordPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b i : ℤ)
    (r : Bool × SiftState) : Prop :=
  r.2 = { s with
      curChunk := r.2.curChunk, row3 := r.2.row3, numSurv1 := r.2.numSurv1,
      numSurv2 := r.2.numSurv2, numSurv3 := r.2.numSurv3, out := r.2.out } ∧
    r.2.curChunk < sd.numChunks ∧ Row3Cache.WF g sd r.2.row3 ∧
    r.2.out = s.out.appendPoints g.check
      (firstIf g.check.onePoint (rowRangePoints g sd a b i (i + 1))) ∧
    r.1 = (g.check.onePoint && !(rowRangePoints g sd a b i (i + 1)).isEmpty)

section TubeWordPost

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {a b i c0 : ℤ} {mask w : UInt64}
  {cur : ℕ}

theorem range_all_eq_stage1Keeps_and_stage2Keeps (g : SiftGlobals) (a b c : ℤ)
    (h : g.sievePrimes1 ≤ g.sievePrimes2) :
    ((List.range g.sievePrimes2).all fun n ↦ g.curve.admits12 g.pnn[n]! a b c) =
      (stage1Keeps g a b c && stage2Keeps g a b c) := by
  have e := List.range'_append_1 (s := 0) (m := g.sievePrimes1)
    (n := g.sievePrimes2 - g.sievePrimes1)
  rw [Nat.zero_add, Nat.add_sub_cancel' h] at e
  rw [stage1Keeps, stage2Keeps, ← List.all_append, List.range_eq_range', List.range_eq_range', e]

theorem TubeWordInvariant.wordPoints_eq (hpre : TubeWordPre g sd s a b i mask c0)
    (h : TubeWordInvariant g sd a b i c0 (ForIn.toList [:g.sievePrimes2]) [] w) :
    g.check.wordPoints (fun c ↦ w.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c &&
      stage3Keeps g a b c) a b i = rowRangePoints g sd a b i (i + 1) := by
  obtain ⟨hs, -, -, -, -, -, -, -, ha, -, -, hab, -, hc0⟩ := hpre
  rw [← hs.wordPoints_eq_rowRangePoints, CheckGlobals.wordPoints, CheckGlobals.wordPoints]
  congr 1
  refine List.filter_congr fun c hc ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hj' := List.mem_range.mp hj
  rw [toNat_emod_64 hj', h j hj', Std.Legacy.Range.toList_eq_range,
    range_all_eq_stage1Keeps_and_stage2Keeps g a b _ hs.sievePrimes1_le_sievePrimes2, colKeeps]
  cases hr : rangeKeeps g sd (64 * i + j)
  · simp
  · rw [hc0, bne_siftMask_fst_eq_not_conic ha hab (of_decide_eq_true (hs.rangeKeeps_eq _ ▸ hr))]
    cases maskKeeps g a b (64 * i + j) <;> cases stage1Keeps g a b (64 * i + j) <;>
      cases stage2Keeps g a b (64 * i + j) <;> cases stage3Keeps g a b (64 * i + j) <;>
      cases coprimeKeeps a b (64 * i + j) <;> cases conic a b (64 * i + j) <;> rfl

theorem tubeWord_seek_pre (hpre : TubeWordPre g sd s a b i mask c0) :
    IsRowSetup g sd ∧ s.curChunk < sd.numChunks ∧ sd.wLowAll ≤ i ∧ i < sd.wHighAll :=
  ⟨hpre.1, hpre.2.2.2.2.2.1, hpre.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.1⟩

theorem tubeWord_checkBits_pre (hpre : TubeWordPre g sd s a b i mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ i ∧ i < (sd.chunks[cur]!).wHigh)
    (h : TubeWordInvariant g sd a b i c0 (ForIn.toList [:g.sievePrimes2]) [] w) :
    IsStageSetup g sd ∧ Row3Cache.WF g sd ({ s with curChunk := cur } : SiftState).row3 ∧
      WordResidues g sd ((i - (sd.chunks[cur]!).wLow).toNat * sd.npr) (sd.chunks[cur]!).res i ∧
      0 ≤ a ∧ a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
      ∀ c ∈ wordCols i, w.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height := by
  obtain ⟨hs, -, -, -, h3, -, -, -, ha, haH, hbH, hab, -⟩ := hpre
  have hres := hs.wordResidues hch.1 (k := (i - (sd.chunks[cur]!).wLow).toNat)
    (by lia [hs.range_chunk_le hch.1])
  rw [show (sd.chunks[cur]!).wLow + ((i - (sd.chunks[cur]!).wLow).toNat : ℤ) = i by lia] at hres
  refine ⟨hs.toIsStageSetup, h3, hres, ha, haH, hbH, hab, fun c hc hbit ↦ ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hj' := List.mem_range.mp hj
  rw [toNat_emod_64 hj', h j hj'] at hbit
  simp only [Bool.and_eq_true] at hbit
  exact of_decide_eq_true (hs.rangeKeeps_eq _ ▸ hbit.1.1.2)

theorem tubeWord_post_found (hpre : TubeWordPre g sd s a b i mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ i ∧ i < (sd.chunks[cur]!).wHigh)
    (h : TubeWordInvariant g sd a b i c0 (ForIn.toList [:g.sievePrimes2]) [] w)
    {r : Bool × SiftState}
    (hr : r.2 = { ({ s with curChunk := cur } : SiftState) with
        row3 := r.2.row3, numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2,
        numSurv3 := r.2.numSurv3, out := r.2.out } ∧
      Row3Cache.WF g sd r.2.row3 ∧
      r.2.out = ({ s with curChunk := cur } : SiftState).out.appendPoints g.check
        (firstIf g.check.onePoint (g.check.wordPoints (fun c ↦ w.toBitVec.getLsbD (c % 64).toNat &&
          coprimeKeeps a b c && stage3Keeps g a b c) a b i)) ∧
      r.1 = (g.check.onePoint && !(g.check.wordPoints (fun c ↦
        w.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c && stage3Keeps g a b c)
          a b i).isEmpty)) :
    TubeWordPost g sd s a b i r := by
  rw [h.wordPoints_eq hpre] at hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hc : r.2.curChunk = cur := congr(SiftState.curChunk $h1)
  refine ⟨?_, hc ▸ hch.1, h2, h3, h4⟩
  rw [hc]
  exact h1

theorem tubeWord_post_zero (hpre : TubeWordPre g sd s a b i mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ i ∧ i < (sd.chunks[cur]!).wHigh)
    (h : TubeWordInvariant g sd a b i c0 (ForIn.toList [:g.sievePrimes2]) [] w)
    (hw : ¬(w != 0) = true) :
    TubeWordPost g sd s a b i (false, { s with curChunk := cur }) := by
  have hw0 : w = 0 := by simpa using hw
  have he : rowRangePoints g sd a b i (i + 1) = [] := by
    rw [← h.wordPoints_eq hpre, hw0]
    simp [CheckGlobals.wordPoints]
  refine ⟨rfl, hch.1, hpre.2.2.2.2.1, ?_, ?_⟩ <;> simp [he, firstIf, Output.appendPoints_nil]

end TubeWordPost

attribute [local irreducible] TubeWordInvariant TubeWordPost in
/-- `tube_word` prints the points of the row `(a, b)` in its word `i` (`JPoints.rowRangePoints`),
only the first under `-1`: the chunk of the word (`JPoints.seekChunk_spec`), the word of the mask
of the row cut to the row and without the bit of `c0`, and-ed with the words of the sieve tables of
the first two stages at its residues, and its bits handed to `check_bits`
(`JPoints.checkBits_spec`). It changes no other field of the state but the last chunk, the data of
the third stage, the counters and the output. -/
@[spec]
theorem tubeWord_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b i : ℤ) (mask : UInt64)
    (c0 : ℤ) :
    ⦃ TubeWordPre g sd s a b i mask c0 ⦄
    tubeWord g sd s a b i mask c0
    ⦃ fun r ↦ TubeWordPost g sd s a b i r ⦄ := by
  vcgen [tubeWord, seekChunk_spec g sd] invariants
  -- one invariant for each of the eight initial words
  all_goals try exact TubeWordInvariant g sd a b i c0
  all_goals first
    | (refine tubeWordInvariant_init ‹_› fun j hj ↦ ?_
       simp_all only [UInt64.toBitVec_and, BitVec.getLsbD_and,
         UInt64.getLsbD_not_one_shiftLeft_emod, bne, Bool.not_eq_true, Bool.not_true,
         Bool.not_false, Bool.true_and, Bool.and_true, Bool.false_or, Bool.true_or,
         Bool.false_and, longLength, Nat.cast_ofNat])
    | exact tubeWordInvariant_step (mask := mask) ‹_› ‹_› ‹_› ‹_›
    | exact tubeWord_seek_pre ‹_›
    | exact tubeWord_checkBits_pre (mask := mask) ‹_› ‹_› ‹_›
    | exact tubeWord_post_found (mask := mask) ‹_› ‹_› ‹_› ‹_›
    | exact tubeWord_post_zero (mask := mask) ‹_› ‹_› ‹_› ‹_›

/-! ### A range of the tube -/

/-- The precondition of the sieve of a range `[lo, hi)` of words of the row `(a, b)` by
`JPoints.siftBandsTube` and `JPoints.siftBandsRegion`. -/
abbrev BandRangePre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : ℤ)
    (mask : UInt64) (c0 : ℤ) : Prop :=
  IsRowSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧
    s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧ s.curChunk < sd.numChunks ∧
    s.survivors.size = g.arraySize + 1 ∧ sd.wLowAll ≤ lo ∧ lo < hi ∧ hi ≤ sd.wHighAll ∧ 0 ≤ a ∧
    a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧ mask = (siftMask g a b).2 ∧
    c0 = (siftMask g a b).1

/-- The state `s'` of the sieve of a range of words from the state `s`, after the points `L`: the
fields other than the bit array, the last chunk, the data of the third stage, the counters and the
output those of `s`, a bit array of the size of that of `s`, a chunk of the row, consistent data of
the third stage, and the points `L` printed, none under `-1`. -/
def BandRangeCont (g : SiftGlobals) (sd : SiftData) (s s' : SiftState)
    (L : List (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  s' = { s with
      survivors := s'.survivors, curChunk := s'.curChunk, row3 := s'.row3,
      numSurv1 := s'.numSurv1, numSurv2 := s'.numSurv2, numSurv3 := s'.numSurv3, out := s'.out } ∧
    s'.survivors.size = s.survivors.size ∧ s'.curChunk < sd.numChunks ∧
    Row3Cache.WF g sd s'.row3 ∧ s'.out = s.out.appendPoints g.check L ∧
    (g.check.onePoint = true → L = [])

/-- The postcondition of the sieve of a range of words that prints the points `L` from the state
`s`, with the result `r`: the fields as in `JPoints.BandRangeCont`, the points `L` printed, only the
first under `-1`, and the flag of a point under `-1`. -/
def BandRangePost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (L : List (ℤ × ℤ × ℤ × ℤ))
    (r : Bool × SiftState) : Prop :=
  r.2 = { s with
      survivors := r.2.survivors, curChunk := r.2.curChunk, row3 := r.2.row3,
      numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2, numSurv3 := r.2.numSurv3,
      out := r.2.out } ∧
    r.2.survivors.size = s.survivors.size ∧ r.2.curChunk < sd.numChunks ∧
    Row3Cache.WF g sd r.2.row3 ∧ r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint L) ∧
    r.1 = (g.check.onePoint && !L.isEmpty)

/-- The invariant of the loop of `JPoints.siftBandsTube` over the words of the range from `lo` on,
whose state is the result of an early return and the state of the thread: before a return, the
state after the points of the words done (`JPoints.BandRangeCont`); after it, the postcondition
with the points of the whole range. -/
def SiftBandsTubeInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (BandRangeCont g sd s st.2 (rowRangePoints g sd a b lo (lo + pref.length)))
    fun r ↦ suff = [] ∧ BandRangePost g sd s (rowRangePoints g sd a b lo hi) r

/-- A state whose rows, statics of `row_setup` and state of the tube are those of `s` is `s` with
its own bit array, last chunk, data of the third stage, counters and output. -/
theorem SiftState.eq_with_of_rowptr_rowSetup_tube {s s' : SiftState}
    (h : s'.rowptr = s.rowptr ∧ s'.rowSetup = s.rowSetup ∧ s'.tube = s.tube) :
    s' = { s with
      survivors := s'.survivors, curChunk := s'.curChunk, row3 := s'.row3,
      numSurv1 := s'.numSurv1, numSurv2 := s'.numSurv2, numSurv3 := s'.numSurv3,
      out := s'.out } := by
  obtain ⟨h1, h2, h3⟩ := h
  cases s'
  simp_all

/-- A state `s'` that is `st` with its own bit array, last chunk, data of the third stage, counters
and output is so `s`, when the rows, the statics of `row_setup` and the state of the tube of `st`
are those of `s`. -/
theorem SiftState.eq_with_of_eq_with {s st s' : SiftState}
    (h : st.rowptr = s.rowptr ∧ st.rowSetup = s.rowSetup ∧ st.tube = s.tube)
    {sv : Array UInt64} {c : ℕ} {r3 : Row3Cache} {n1 n2 n3 : ℕ} {out : Output}
    (h' : s' = { st with
      survivors := sv, curChunk := c, row3 := r3, numSurv1 := n1, numSurv2 := n2, numSurv3 := n3,
      out := out }) :
    s' = { s with
      survivors := s'.survivors, curChunk := s'.curChunk, row3 := s'.row3,
      numSurv1 := s'.numSurv1, numSurv2 := s'.numSurv2, numSurv3 := s'.numSurv3,
      out := s'.out } :=
  SiftState.eq_with_of_rowptr_rowSetup_tube ⟨congr(SiftState.rowptr $h').trans h.1,
    congr(SiftState.rowSetup $h').trans h.2.1, congr(SiftState.tube $h').trans h.2.2⟩

section SiftBandsTube

variable {g : SiftGlobals} {sd : SiftData} {s st s' : SiftState} {a b lo hi c0 : ℤ}
  {mask : UInt64} {pref suff : List ℕ} {cur : ℕ} {o : Option (Bool × SiftState)}

theorem BandRangeCont.fields {L : List (ℤ × ℤ × ℤ × ℤ)} (h : BandRangeCont g sd s st L) :
    st.rowptr = s.rowptr ∧ st.rowSetup = s.rowSetup ∧ st.tube = s.tube := by
  obtain ⟨h1, -⟩ := h
  exact ⟨congr(SiftState.rowptr $h1), congr(SiftState.rowSetup $h1), congr(SiftState.tube $h1)⟩

/-- A state of the sieve of a range of words before a point is returned is that of its end. -/
theorem BandRangeCont.post {L : List (ℤ × ℤ × ℤ × ℤ)} (h : BandRangeCont g sd s st L) :
    BandRangePost g sd s L (false, st) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩ <;> cases hop : g.check.onePoint
  · exact h5
  · simp [h5, h6 hop]
  · rfl
  · simp [h6 hop]

private theorem siftBandsTubeInvariant_init (hpre : BandRangePre g sd s a b lo hi mask c0)
    {l : List ℕ} :
    SiftBandsTubeInvariant g sd s a b lo hi [] l
      (none, { s with numSurv1 := s.numSurv1 + (hi - lo).toNat }) := by
  refine ⟨rfl, rfl, hpre.2.2.2.2.2.1, hpre.2.2.2.2.1, ?_, fun _ ↦ ?_⟩ <;>
    simp [rowRangePoints_self]

private theorem SiftBandsTubeInvariant.cont
    (hv : SiftBandsTubeInvariant g sd s a b lo hi pref (cur :: suff) (o, st)) :
    o = none ∧ BandRangeCont g sd s st (rowRangePoints g sd a b lo (lo + pref.length)) := by
  rcases o with _ | r
  · exact ⟨rfl, hv⟩
  · exact absurd hv.1 (List.cons_ne_nil _ _)

private theorem siftBandsTube_tubeWord_pre (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hc : ForIn.toList [:(hi - lo).toNat] = pref ++ cur :: suff)
    (hv : SiftBandsTubeInvariant g sd s a b lo hi pref (cur :: suff) (o, st)) :
    TubeWordPre g sd st a b (lo + cur) mask c0 := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  obtain ⟨e1, e2, -⟩ := hst.fields
  obtain ⟨-, -, hcc, h3, -⟩ := hst
  obtain ⟨hs, hw, hA, hB, -, -, -, hlo, -, hhi, ha, haH, hbH, hab, hm, hc0⟩ := hpre
  exact ⟨hs, e1 ▸ e2 ▸ hw, e2 ▸ hA, e2 ▸ hB, h3, hcc, by lia, by lia, ha, haH, hbH, hab, hm, hc0⟩

private theorem siftBandsTubeInvariant_return (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hc : ForIn.toList [:(hi - lo).toNat] = pref ++ cur :: suff)
    (hv : SiftBandsTubeInvariant g sd s a b lo hi pref (cur :: suff) (o, st)) {found : Bool}
    (hp : TubeWordPost g sd st a b (lo + cur) (found, s'))
    (hf : (found && g.check.onePoint) = true) :
    SiftBandsTubeInvariant g sd s a b lo hi (ForIn.toList [:(hi - lo).toNat]) [] (some (true, s'),
      s') := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, -, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_found (out := s.out)
    (R := rowRangePoints g sd a b (lo + cur + 1) hi) h1 g5 hf
  rw [← hout, ← g4] at f1
  rw [hl, rowRangePoints_append _ _ _ _ (by lia) (by lia),
    rowRangePoints_append _ _ _ _ (by lia) (by lia [hpre.2.2.2.2.2.2.2.2.1])] at f1 f2
  have hs' : s'.survivors = st.survivors := congr(SiftState.survivors $g1)
  refine ⟨rfl, SiftState.eq_with_of_eq_with hfs g1, hs' ▸ hsz, g2, g3, f1, f2⟩

private theorem siftBandsTubeInvariant_next
    (hc : ForIn.toList [:(hi - lo).toNat] = pref ++ cur :: suff)
    (hv : SiftBandsTubeInvariant g sd s a b lo hi pref (cur :: suff) (o, st)) {found : Bool}
    (hp : TubeWordPost g sd st a b (lo + cur) (found, s'))
    (hf : ¬(found && g.check.onePoint) = true) :
    SiftBandsTubeInvariant g sd s a b lo hi (pref ++ [cur]) suff (none, s') := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, -, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_not_found (out := s.out) h1 g5 hf
  rw [← hout, ← g4] at f1
  rw [hl, rowRangePoints_append _ _ _ _ (by lia) (by lia)] at f1 f2
  have hs' : s'.survivors = st.survivors := congr(SiftState.survivors $g1)
  have hl' : lo + ((pref ++ [cur]).length : ℤ) = lo + cur + 1 := by simp [hl]; lia
  refine ⟨SiftState.eq_with_of_eq_with hfs g1, hs' ▸ hsz, g2, g3, hl' ▸ f1,
    hl' ▸ f2⟩

private theorem siftBandsTubeInvariant_post_some
    (hv : SiftBandsTubeInvariant g sd s a b lo hi (ForIn.toList [:(hi - lo).toNat]) [] (o, st))
    {x : Bool} {y : SiftState} (ho : o = some (x, y)) :
    BandRangePost g sd s (rowRangePoints g sd a b lo hi) (x, y) := by
  subst ho
  exact hv.2

private theorem siftBandsTubeInvariant_post_none (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hv : SiftBandsTubeInvariant g sd s a b lo hi (ForIn.toList [:(hi - lo).toNat]) [] (o, st))
    (ho : o = none) :
    BandRangePost g sd s (rowRangePoints g sd a b lo hi) (false, st) := by
  subst ho
  have h : BandRangeCont _ _ _ _ _ := hv
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero,
    show lo + ((hi - lo).toNat : ℤ) = hi by lia [hpre.2.2.2.2.2.2.2.2.1]] at h
  exact h.post

end SiftBandsTube

theorem siftBandsTube_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : ℤ)
    (mask : UInt64) (c0 : ℤ) :
    ⦃ BandRangePre g sd s a b lo hi mask c0 ⦄
    siftBandsTube g sd s a b lo hi mask c0
    ⦃ fun r ↦ BandRangePost g sd s (rowRangePoints g sd a b lo hi) r ⦄ := by
  vcgen [siftBandsTube] invariants
  · SiftBandsTubeInvariant g sd s a b lo hi
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact siftBandsTubeInvariant_init ‹_›
    | exact siftBandsTube_tubeWord_pre ‹_› ‹_› ‹_›
    | exact siftBandsTubeInvariant_return ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsTubeInvariant_next ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsTubeInvariant_post_some ‹_› ‹_›
    | exact siftBandsTubeInvariant_post_none ‹_› ‹_› ‹_›


/-! ### A range of the region -/

/-- The invariant of the loop of `JPoints.siftBandsRegion` over the chunks from `cur` on, the chunk
of the first word `lo` of the range, whose state is the result of an early return and the state of
the thread: before a return, the state after the points of the words of the range below the chunks
left (`JPoints.BandRangeCont`); after it, the postcondition with the points of the whole range. -/
def SiftBandsRegionInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : ℤ)
    (cur : ℕ) : Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (BandRangeCont g sd s st.2 (rowRangePoints g sd a b lo
      (min hi (min (sd.wLowAll + ((cur + pref.length) * g.arraySize : ℕ)) sd.wHighAll))))
    fun r ↦ suff = [] ∧ BandRangePost g sd s (rowRangePoints g sd a b lo hi) r

section SiftBandsRegion

variable {g : SiftGlobals} {sd : SiftData} {s st s' : SiftState} {a b lo hi c0 : ℤ}
  {mask : UInt64} {pref suff : List ℕ} {cur c : ℕ} {o : Option (Bool × SiftState)}

theorem IsRowSetup.wHigh_chunk_le (h : IsRowSetup g sd) {k k' : ℕ} (hk : k ≤ k')
    (hk' : k' < sd.numChunks) : (sd.chunks[k]!).wHigh ≤ (sd.chunks[k']!).wHigh := by
  rw [h.wHigh_chunk_eq_min (by lia), h.wHigh_chunk_eq_min hk']
  have : ((k + 1) * g.arraySize : ℕ) ≤ ((k' + 1) * g.arraySize : ℕ) := by
    exact Nat.mul_le_mul_right _ (by lia)
  lia

private theorem siftBandsRegion_seek_pre (hpre : BandRangePre g sd s a b lo hi mask c0) :
    IsRowSetup g sd ∧ s.curChunk < sd.numChunks ∧ sd.wLowAll ≤ lo ∧ lo < sd.wHighAll :=
  ⟨hpre.1, hpre.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.1, by
    lia [hpre.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2.1]⟩

private theorem siftBandsRegionInvariant_init (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ lo ∧ lo < (sd.chunks[cur]!).wHigh)
    {l : List ℕ} :
    SiftBandsRegionInvariant g sd s a b lo hi cur [] l (none, { s with curChunk := cur }) := by
  have e : rowRangePoints g sd a b lo
      (min hi (min (sd.wLowAll + ((cur + ([] : List ℕ).length) * g.arraySize : ℕ)) sd.wHighAll)) =
      [] := by
    rw [List.length_nil, Nat.add_zero, ← hpre.1.wLow_chunk_eq_min hch.1]
    exact rowRangePoints_of_le _ _ _ _ (by lia)
  refine ⟨rfl, rfl, hch.1, hpre.2.2.2.2.1, ?_, fun _ ↦ e⟩
  rw [e]
  simp [Output.appendPoints_nil]

private theorem SiftBandsRegionInvariant.cont
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur pref (c :: suff) (o, st)) :
    o = none ∧ BandRangeCont g sd s st (rowRangePoints g sd a b lo
      (min hi (min (sd.wLowAll + ((cur + pref.length) * g.arraySize : ℕ)) sd.wHighAll))) := by
  rcases o with _ | r
  · exact ⟨rfl, hv⟩
  · exact absurd hv.1 (List.cons_ne_nil _ _)

private theorem siftBandsRegionInvariant_break (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hc : ForIn.toList [cur:sd.numChunks] = pref ++ c :: suff)
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur pref (c :: suff) (o, st))
    (hb : (!decide ((sd.chunks[c]!).wLow < hi)) = true) :
    SiftBandsRegionInvariant g sd s a b lo hi cur (ForIn.toList [cur:sd.numChunks]) []
      (none, st) := by
  have hcl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hcn := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨-, hst⟩ := hv.cont
  have hw : hi ≤ (sd.chunks[c]!).wLow := by simpa using hb
  have e1 :
      min hi (min (sd.wLowAll + ((cur + pref.length) * g.arraySize : ℕ)) sd.wHighAll) = hi := by
    rw [hcl, ← hpre.1.wLow_chunk_eq_min hcn]; lia
  have e2 : min hi (min (sd.wLowAll + ((cur + (ForIn.toList [cur:sd.numChunks]).length) *
      g.arraySize : ℕ)) sd.wHighAll) = hi := by
    rw [Std.Legacy.Range.length_toList, Nat.add_sub_cancel' (by lia), hpre.1.min_numChunks]
    lia [hpre.2.2.2.2.2.2.2.2.2.1]
  rw [e1] at hst
  change BandRangeCont g sd s st (rowRangePoints g sd a b lo (min hi (min (sd.wLowAll +
    ((cur + (ForIn.toList [cur:sd.numChunks]).length) * g.arraySize : ℕ)) sd.wHighAll)))
  rw [e2]
  exact hst

private theorem siftBandsRegion_siftRange_pre (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ lo ∧ lo < (sd.chunks[cur]!).wHigh)
    (hc : ForIn.toList [cur:sd.numChunks] = pref ++ c :: suff)
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur pref (c :: suff) (o, st))
    (hb : ¬(!decide ((sd.chunks[c]!).wLow < hi)) = true) :
    SiftRangePre g sd st a b c
      (if (sd.chunks[c]!).wLow < lo then lo else (sd.chunks[c]!).wLow)
      (if hi < (sd.chunks[c]!).wHigh then hi else (sd.chunks[c]!).wHigh) mask c0 := by
  have hcl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hcn := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hw : (sd.chunks[c]!).wLow < hi := by simpa using hb
  obtain ⟨-, hst⟩ := hv.cont
  obtain ⟨e1, e2, -⟩ := hst.fields
  obtain ⟨-, hsz, -, h3, -⟩ := hst
  obtain ⟨hs, hrw, hA, hB, -, -, hsv, hlo, -, hhi, ha, haH, hbH, hab, hm, hc0⟩ := hpre
  have hm1 := hs.wHigh_chunk_le (show cur ≤ c by lia) hcn
  have hm2 := hs.wLow_add_range_chunk hcn
  refine ⟨hs, hcn, ?_, ?_, ?_, ?_, e1 ▸ e2 ▸ hrw, e2 ▸ hA, e2 ▸ hB, h3, hsz.trans hsv, ha, haH, hbH,
    hab, hm, hc0⟩ <;> split_ifs <;> lia

private theorem rowRangePoints_chunk_step (h : IsRowSetup g sd) (hcn : c < sd.numChunks)
    (hw : (sd.chunks[c]!).wLow < hi) :
    rowRangePoints g sd a b lo (min hi (min (sd.wLowAll + (c * g.arraySize : ℕ)) sd.wHighAll)) ++
        rowRangePoints g sd a b (if (sd.chunks[c]!).wLow < lo then lo else (sd.chunks[c]!).wLow)
          (if hi < (sd.chunks[c]!).wHigh then hi else (sd.chunks[c]!).wHigh) =
      rowRangePoints g sd a b lo
        (min hi (min (sd.wLowAll + ((c + 1) * g.arraySize : ℕ)) sd.wHighAll)) := by
  have hm2 := h.wLow_add_range_chunk hcn
  rw [← h.wLow_chunk_eq_min hcn, ← h.wHigh_chunk_eq_min hcn,
    show (if hi < (sd.chunks[c]!).wHigh then hi else (sd.chunks[c]!).wHigh) =
      min hi (sd.chunks[c]!).wHigh by split_ifs <;> lia]
  split_ifs with hl
  · rw [rowRangePoints_of_le _ _ _ _ (by lia), List.nil_append]
  · rw [show min hi (sd.chunks[c]!).wLow = (sd.chunks[c]!).wLow by lia,
      rowRangePoints_append _ _ _ _ (by lia) (by lia)]

private theorem siftBandsRegionInvariant_next (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hc : ForIn.toList [cur:sd.numChunks] = pref ++ c :: suff)
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur pref (c :: suff) (o, st))
    (hb : ¬(!decide ((sd.chunks[c]!).wLow < hi)) = true) {found : Bool}
    (hp : SiftPost g sd st (rowRangePoints g sd a b
      (if (sd.chunks[c]!).wLow < lo then lo else (sd.chunks[c]!).wLow)
      (if hi < (sd.chunks[c]!).wHigh then hi else (sd.chunks[c]!).wHigh)) (found, s'))
    (hf : ¬(found && g.check.onePoint) = true) :
    SiftBandsRegionInvariant g sd s a b lo hi cur (pref ++ [c]) suff (none, s') := by
  have hcl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hcn := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hw : (sd.chunks[c]!).wLow < hi := by simpa using hb
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, hcc, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_not_found (out := s.out) h1 g5 hf
  rw [← hout, ← g4] at f1
  rw [hcl, rowRangePoints_chunk_step hpre.1 hcn hw] at f1 f2
  have hl : cur + (pref ++ [c]).length = c + 1 := by simp; lia
  have hs' : s'.curChunk = st.curChunk := congr(SiftState.curChunk $g1)
  refine ⟨SiftState.eq_with_of_eq_with hfs g1, g2.trans hsz, hs' ▸ hcc, g3,
    hl ▸ f1, hl ▸ f2⟩

private theorem siftBandsRegionInvariant_return (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ lo ∧ lo < (sd.chunks[cur]!).wHigh)
    (hc : ForIn.toList [cur:sd.numChunks] = pref ++ c :: suff)
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur pref (c :: suff) (o, st))
    (hb : ¬(!decide ((sd.chunks[c]!).wLow < hi)) = true) {found : Bool}
    (hp : SiftPost g sd st (rowRangePoints g sd a b
      (if (sd.chunks[c]!).wLow < lo then lo else (sd.chunks[c]!).wLow)
      (if hi < (sd.chunks[c]!).wHigh then hi else (sd.chunks[c]!).wHigh)) (found, s'))
    (hf : (found && g.check.onePoint) = true) :
    SiftBandsRegionInvariant g sd s a b lo hi cur (ForIn.toList [cur:sd.numChunks]) []
      (some (true, s'), s') := by
  have hcl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hcn := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hw : (sd.chunks[c]!).wLow < hi := by simpa using hb
  obtain ⟨-, hst⟩ := hv.cont
  have hfs := hst.fields
  obtain ⟨-, hsz, hcc, -, hout, h1⟩ := hst
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  have hm1 := hpre.1.wHigh_chunk_le (show cur ≤ c by lia) hcn
  have he := hpre.1.wHigh_chunk_eq_min hcn
  obtain ⟨f1, f2⟩ := Output.appendPoints_firstIf_of_found (out := s.out)
    (R := rowRangePoints g sd a b
      (min hi (min (sd.wLowAll + ((c + 1) * g.arraySize : ℕ)) sd.wHighAll)) hi) h1 g5 hf
  rw [← hout, ← g4] at f1
  rw [hcl, rowRangePoints_chunk_step hpre.1 hcn hw,
    rowRangePoints_append _ _ _ _ (by lia) (by lia)] at f1 f2
  have hs' : s'.curChunk = st.curChunk := congr(SiftState.curChunk $g1)
  refine ⟨rfl, SiftState.eq_with_of_eq_with hfs g1, g2.trans hsz, hs' ▸ hcc, g3,
    f1, f2⟩

private theorem siftBandsRegionInvariant_post_some
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur (ForIn.toList [cur:sd.numChunks]) []
      (o, st)) {x : Bool} {y : SiftState} (ho : o = some (x, y)) :
    BandRangePost g sd s (rowRangePoints g sd a b lo hi) (x, y) := by
  subst ho
  exact hv.2

private theorem siftBandsRegionInvariant_post_none (hpre : BandRangePre g sd s a b lo hi mask c0)
    (hch : cur < sd.numChunks ∧ (sd.chunks[cur]!).wLow ≤ lo ∧ lo < (sd.chunks[cur]!).wHigh)
    (hv : SiftBandsRegionInvariant g sd s a b lo hi cur (ForIn.toList [cur:sd.numChunks]) []
      (o, st)) (ho : o = none) :
    BandRangePost g sd s (rowRangePoints g sd a b lo hi) (false, st) := by
  subst ho
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  dsimp only at h1 h2 h3 h4 h5 h6
  have e2 : min hi (min (sd.wLowAll + ((cur + (ForIn.toList [cur:sd.numChunks]).length) *
      g.arraySize : ℕ)) sd.wHighAll) = hi := by
    rw [Std.Legacy.Range.length_toList, Nat.add_sub_cancel' (by lia), hpre.1.min_numChunks]
    lia [hpre.2.2.2.2.2.2.2.2.2.1]
  rw [e2] at h5 h6
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · cases hop : g.check.onePoint
    · exact h5
    · simp [h5, h6 hop]
  · cases hop : g.check.onePoint
    · rfl
    · simp [h6 hop]

end SiftBandsRegion

theorem siftBandsRegion_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : ℤ)
    (mask : UInt64) (c0 : ℤ) :
    ⦃ BandRangePre g sd s a b lo hi mask c0 ⦄
    siftBandsRegion g sd s a b lo hi mask c0
    ⦃ fun r ↦ BandRangePost g sd s (rowRangePoints g sd a b lo hi) r ⦄ := by
  vcgen [siftBandsRegion, seekChunk_spec g sd] invariants
  | inv1 cur _ => SiftBandsRegionInvariant g sd s a b lo hi cur
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact siftBandsRegion_seek_pre ‹_›
    | exact siftBandsRegionInvariant_init ‹_› ‹_›
    | exact siftBandsRegionInvariant_break ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRegion_siftRange_pre ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRegionInvariant_next ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRegionInvariant_return ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftBandsRegionInvariant_post_some ‹_› ‹_›
    | exact siftBandsRegionInvariant_post_none ‹_› ‹_› ‹_› ‹_›

end JPoints

end
