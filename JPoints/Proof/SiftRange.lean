/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Walk

import JPoints.Proof.Containers
import Mathlib.Data.Int.ModEq
import Std.Tactic.Do

/-!
# The sieve of a range of words of a chunk

The contract of `sift_range` (`JPoints.siftRange_spec`), which the sieve by bands calls on the parts
of the ranges of the real region of a row that lie in a chunk: it prints the points of the row in
the words of the range (`JPoints.rowRangePoints`), as `sift0` does for a whole chunk, with the walks
of the first stage over the range made from those of the chunk (`walk_parts`,
`JPoints.walkParts_spec`). The pieces: the fill with the pass of the first first-stage prime
(`JPoints.siftRangeFill_spec`) and the masks of the range (`JPoints.siftRangeMasks_spec`).

## Main definitions

* `JPoints.RangeFillPre`, `JPoints.SiftRangePre`: the preconditions of the fill and of the sieve of
  a range.

## Main statements

* `JPoints.siftRangeFill_spec`, `JPoints.siftRangeMasks_spec`: the fill and the masks of a range.
* `JPoints.siftRange_spec`: the sieve of a range of words of a chunk.
* `JPoints.IsRowSetup.range_chunk_lt`: a chunk has fewer than `2 ^ 48` words.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with the
invariants of `JPoints.Proof.Walk`, each verification condition closed by a lemma stated in its own
shape. The range may be empty, `hi ≤ lo`, as long as both ends lie among the words of the chunk.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-- The precondition of `JPoints.siftRangeFill` for the bit array `sv`, the chunk `ch` and the `len`
words from the position `surv0 = off` on: what the stages read (`JPoints.IsStageSetup`), the walks
of the chunk (`JPoints.ChunkWalks`), the words within a bit array of `array_size` words and below
`2 ^ 48`, and within `sv`. -/
abbrev RangeFillPre (g : SiftGlobals) (sd : SiftData) (sv : Array UInt64) (ch : ChunkSpec)
    (surv0 off len : ℕ) : Prop :=
  IsStageSetup g sd ∧ ChunkWalks g sd ch ∧ surv0 = off ∧ off ≤ g.arraySize ∧
    len ≤ g.arraySize ∧ len < 2 ^ 48 ∧ surv0 + len ≤ sv.size

section RangeFill

variable {g : SiftGlobals} {sd : SiftData} {rowptr : Array ℕ} {sv S : Array UInt64}
  {ch : ChunkSpec} {surv0 off len : ℕ} {mask : UInt64}

private theorem rangeFill_parts_pre (hpre : RangeFillPre g sd sv ch surv0 off len)
    (h : ¬(g.sievePrimes1 == 0) = true) :
    (∃ g' : SiftGlobals, IsStageSetup g' sd ∧ 0 < g'.sievePrimes3 ∧ off ≤ g'.arraySize ∧
      len ≤ g'.arraySize) ∧ 0 < (ch.walk[0]!).first ∧ (ch.walk[0]!).first ≤ sd.pr[0]! ∧
      len < 2 ^ 48 := by
  obtain ⟨hs, hw, -, hoff, hlen, hlen48, -⟩ := hpre
  have h0 : 0 < g.sievePrimes1 := Nat.pos_of_ne_zero (by simpa using h)
  have hw0 := hw 0 h0
  exact ⟨⟨g, hs, by lia [hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3], hoff,
    hlen⟩, hw0.first_pos, by lia [hw0.first_add_head_le], hlen48⟩

private theorem rangeFill_walk_pre (hpre : RangeFillPre g sd sv ch surv0 off len) {w : WalkSpec}
    (hw : w.IsWalk sd.pr[0]! len ((ch.walk[0]!).first + off)) :
    w.WF sd.pr[0]! ∧ surv0 + (w.head + w.nper * sd.pr[0]! + w.tail) ≤ sv.size :=
  ⟨hw.toWF, hw.length_eq ▸ hpre.2.2.2.2.2.2⟩

private theorem rangeFill_walk_post (hpre : RangeFillPre g sd sv ch surv0 off len)
    (h : ¬(g.sievePrimes1 == 0) = true) {w : WalkSpec}
    (hw : w.IsWalk sd.pr[0]! len ((ch.walk[0]!).first + off))
    (hS : S.size = sv.size ∧
      (∀ t < w.head + w.nper * sd.pr[0]! + w.tail,
        S[surv0 + t]! = fillOp mask sv[surv0 + t]!
          (g.sieve.sieveTab[0]!)[rowptr[0]! + (w.first + t) % sd.pr[0]!]!) ∧
      ∀ m, m < surv0 ∨ surv0 + (w.head + w.nper * sd.pr[0]! + w.tail) ≤ m → S[m]! = sv[m]!) :
    FillPost g sd rowptr sv ch surv0 len mask S 1 := by
  obtain ⟨-, hcw, rfl, -⟩ := hpre
  have h0 : 0 < g.sievePrimes1 := Nat.pos_of_ne_zero (by simpa using h)
  obtain ⟨h1, h2, h3⟩ := hS
  rw [hw.length_eq] at h2 h3
  refine ⟨h1, h0, fun t ht j ↦ ?_, h3⟩
  have e : ((ch.walk[0]!).first + surv0 + t : ℤ) % sd.pr[0]! =
      (ch.wLow + (surv0 + t : ℕ)) % sd.pr[0]! := by
    have := Int.ModEq.add_right ((surv0 + t : ℕ) : ℤ) (hcw 0 h0).first_emod
    rw [Nat.cast_add, ← Int.add_assoc] at this
    exact this
  rw [h2 t ht, fillOp, UInt64.toBitVec_and, BitVec.getLsbD_and, hw.mod_eq, List.range_one,
    tabBits_singleton, e]

end RangeFill

/-- The fill of `sift_range` leaves in each word of the range the bits of the mask and of the row of
the sieve table of the first first-stage prime, by its walk over the range (`walk_parts`), and the
first-stage prime to go on with. -/
@[spec]
theorem siftRangeFill_spec (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (sv : Array UInt64)
    (ch : ChunkSpec) (surv0 off len : ℕ) (mask : UInt64) :
    ⦃ IsStageSetup g sd ∧ ChunkWalks g sd ch ∧ surv0 = off ∧ off ≤ g.arraySize ∧
      len ≤ g.arraySize ∧ len < 2 ^ 48 ∧ surv0 + len ≤ sv.size ⦄
    siftRangeFill g sd rowptr sv ch surv0 off len mask
    ⦃ fun r ↦ FillPost g sd rowptr sv ch surv0 len mask r.1 r.2 ⦄ := by
  vcgen [siftRangeFill, walkParts_spec, walk_spec] invariants
  · FillInvariant sv surv0 mask
  all_goals with_reducible first
    | exact fillInvariant_nil
    | exact fillInvariant_post ‹_›
    | exact fillInvariant_step ‹_› ‹_› (by lia)
    | exact rangeFill_parts_pre ‹_› ‹_›
    | exact rangeFill_walk_pre ‹_› ‹_›
    | exact rangeFill_walk_post ‹_› ‹_› ‹_› ‹_›

/-- The masks of `sift_range` and-ed into the first word of the row (`begmask`) and into its last
word (`endmask`) when the range holds them, and the bit of `c0` cleared in its word when the range
holds it. -/
@[spec]
theorem siftRangeMasks_spec (g : SiftGlobals) (sd : SiftData) (sv : Array UInt64)
    (k range off len : ℕ) (cw c0 : ℤ) :
    ⦃ off + len ≤ sv.size ⦄
    siftRangeMasks g sd sv k range off len cw c0
    ⦃ fun r ↦ r.size = sv.size ∧ ∀ t < len, ∀ j, (r[off + t]!).toBitVec.getLsbD j =
        (sv[off + t]!.toBitVec.getLsbD j &&
          (!(k == 0 && off == 0 && off + t == 0) || g.begmask.toBitVec.getLsbD j) &&
          (!(k == sd.numChunks - 1 && decide (range ≤ off + len) && off + t == range - 1) ||
            g.endmask.toBitVec.getLsbD j) &&
          !(decide ((off : ℤ) ≤ cw ∧ cw < (off + len : ℕ)) && off + t == cw.toNat &&
            j == (c0 % 64).toNat)) ⦄ := by
  vcgen [siftRangeMasks]
  all_goals
    try refine ⟨by simp, ?_⟩
    intro t ht j
    have ht' : off + t < sv.size := by lia
    have hn : (c0 % (longLength : ℤ)).toNat < 64 := by simp only [longLength]; lia
    try simp only [Array.getLsbD_getElem!_set!_and_not, Array.size_set!, ht', hn]
    try simp only [Array.getLsbD_getElem!_set!_and, Array.size_set!, ht']
    simp only [longLength, Nat.cast_ofNat] at *
    grind

/-- The precondition of `JPoints.siftRange` for the state `s`, the row `(a, b)`, the words
`[lo, hi)` of the `k`-th chunk, the mask `mask` and the excluded third coordinate `c0`: what the
sieve of a row reads (`JPoints.IsRowSetup`), a chunk of the row and both ends among its words, the
rows of the sieve tables of the row (`JPoints.RowSetupCache.WF` with `(last_a, last_b) = (a, b)`),
consistent data of the third stage, a bit array of `array_size + 1` words, `0 ≤ a ≤ H`, `|b| ≤ H`,
`b ≥ 1` for `a = 0`, and the mask and `c0` of the row (`JPoints.siftMask`). -/
abbrev SiftRangePre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (k : ℕ)
    (lo hi : ℤ) (mask : UInt64) (c0 : ℤ) : Prop :=
  IsRowSetup g sd ∧ k < sd.numChunks ∧ (sd.chunks[k]!).wLow ≤ lo ∧ lo ≤ (sd.chunks[k]!).wHigh ∧
    (sd.chunks[k]!).wLow ≤ hi ∧ hi ≤ (sd.chunks[k]!).wHigh ∧
    RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧ s.rowSetup.lastB = b ∧
    Row3Cache.WF g sd s.row3 ∧ s.survivors.size = g.arraySize + 1 ∧ 0 ≤ a ∧
    a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧ mask = (siftMask g a b).2 ∧
    c0 = (siftMask g a b).1

-- The postcondition of `JPoints.siftRangeMasks`.
private abbrev RangeMasksPost (g : SiftGlobals) (sd : SiftData) (sv : Array UInt64)
    (k range off len : ℕ) (cw c0 : ℤ) (M : Array UInt64) : Prop :=
  M.size = sv.size ∧ ∀ t < len, ∀ j, (M[off + t]!).toBitVec.getLsbD j =
    (sv[off + t]!.toBitVec.getLsbD j &&
      (!(k == 0 && off == 0 && off + t == 0) || g.begmask.toBitVec.getLsbD j) &&
      (!(k == sd.numChunks - 1 && decide (range ≤ off + len) && off + t == range - 1) ||
        g.endmask.toBitVec.getLsbD j) &&
      !(decide ((off : ℤ) ≤ cw ∧ cw < (off + len : ℕ)) && off + t == cw.toNat &&
        j == (c0 % 64).toNat))

private theorem rangeMasks_beg_eq {k off t : ℕ} :
    (k == 0 && off == 0 && off + t == 0) = (k == 0 && off + t == 0) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  lia

private theorem rangeMasks_end_eq {k N range off len t : ℕ} (ht : t < len) :
    (k == N && decide (range ≤ off + len) && off + t == range - 1) =
      (k == N && off + t == range - 1) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  lia

private theorem rangeMasks_c0_eq {wLow c0 : ℤ} {off len t j : ℕ} (ht : t < len) (hj : j < 64) :
    (decide ((off : ℤ) ≤ c0 >>> longShift - wLow ∧ c0 >>> longShift - wLow < (off + len : ℕ)) &&
      off + t == (c0 >>> longShift - wLow).toNat && j == (c0 % 64).toNat) =
      (64 * (wLow + (off + t : ℕ)) + j == c0) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Int.shiftRight_eq_div_pow,
    longShift]
  lia

section SiftRange

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {a b : ℤ} {k : ℕ} {lo hi : ℤ}
  {mask : UInt64} {c0 : ℤ}

theorem SiftRangePre.off_add_len_le (hpre : SiftRangePre g sd s a b k lo hi mask c0) :
    (lo - (sd.chunks[k]!).wLow).toNat + (hi - lo).toNat ≤
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat := by
  obtain ⟨-, -, h1, h2, h3, h4, -⟩ := hpre
  lia

private theorem siftRange_bits (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {F M S' : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat mask F n)
    (hM : RangeMasksPost g sd F k ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat
      (lo - (sd.chunks[k]!).wLow).toNat (hi - lo).toNat (c0 >>> longShift - (sd.chunks[k]!).wLow)
      c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat (ForIn.toList [n:g.sievePrimes1]) [] S')
    {m : ℕ} (hm1 : (lo - (sd.chunks[k]!).wLow).toNat ≤ m)
    (hm2 : m < (lo - (sd.chunks[k]!).wLow).toNat + (hi - lo).toNat) {j : ℕ} (hj : j < 64) :
    (S'[m]!).toBitVec.getLsbD j = (maskKeeps g a b (64 * ((sd.chunks[k]!).wLow + m) + j) &&
      stage1Keeps g a b (64 * ((sd.chunks[k]!).wLow + m) + j) &&
      rangeKeeps g sd (64 * ((sd.chunks[k]!).wLow + m) + j) &&
      (64 * ((sd.chunks[k]!).wLow + m) + j != c0)) := by
  have hlen := hpre.off_add_len_le
  obtain ⟨h, hk, -, -, -, -, hw, hA, hB, -, -, ha, -, -, -, hmask, -⟩ := hpre
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm1
  have ht : t < (hi - lo).toNat := by lia
  rw [hS.2 t ht j, hM.2 t ht j, hF.2.2.1 t ht j, h.rangeKeeps_chunk hk (by lia) hj,
    rangeMasks_beg_eq, rangeMasks_end_eq ht, rangeMasks_c0_eq ht hj, maskKeeps, ← hmask,
    toNat_emod_64 hj, ← h.tabBits_range_eq_stage1Keeps hw hA hB ha _ hj,
    ← tabBits_range_append hF.2.1, bne]
  ac_rfl

theorem IsRowSetup.range_chunk_lt (h : IsRowSetup g sd) (hk : k < sd.numChunks) :
    ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat < 2 ^ 48 := by
  have := h.check.height_le_maxHeight
  have := h.check.one_le_height
  have := maxHeight_lt_two_pow_32
  have hlo := h.siftData.wLow_chunk hk
  have hhi := h.siftData.wHigh_chunk hk
  have e1 := h.siftData.wHighAll_eq
  have e2 := h.siftData.wLowAll_eq
  simp only [Int.shiftRight_eq_div_pow, longShift] at e1 e2
  lia

private theorem siftRange_fill_pre (hpre : SiftRangePre g sd s a b k lo hi mask c0) :
    IsStageSetup g sd ∧ ChunkWalks g sd (sd.chunks[k]!) ∧
      (lo - (sd.chunks[k]!).wLow).toNat ≤ g.arraySize ∧ (hi - lo).toNat ≤ g.arraySize ∧
      (hi - lo).toNat < 2 ^ 48 ∧
      (lo - (sd.chunks[k]!).wLow).toNat + (hi - lo).toNat ≤ s.survivors.size := by
  have hlen := hpre.off_add_len_le
  obtain ⟨h, hk, -, -, -, -, -, -, -, -, hsize, -⟩ := hpre
  have := h.range_chunk_le hk
  have := h.range_chunk_lt hk
  exact ⟨h.toIsStageSetup, h.chunkWalks hk, by lia, by lia, by lia, by lia⟩

private theorem siftRange_masks_pre (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {F : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat mask F n) :
    (lo - (sd.chunks[k]!).wLow).toNat + (hi - lo).toNat ≤ F.size := by
  rw [hF.1]
  exact (siftRange_fill_pre hpre).2.2.2.2.2

private theorem siftRange_parts_pre (hpre : SiftRangePre g sd s a b k lo hi mask c0) {n cur : ℕ}
    {pref suff : List ℕ} (hc : ForIn.toList [n:g.sievePrimes1] = pref ++ cur :: suff) :
    (∃ g' : SiftGlobals, IsStageSetup g' sd ∧ cur < g'.sievePrimes3 ∧
      (lo - (sd.chunks[k]!).wLow).toNat ≤ g'.arraySize ∧ (hi - lo).toNat ≤ g'.arraySize) ∧
      0 < ((sd.chunks[k]!).walk[cur]!).first ∧ ((sd.chunks[k]!).walk[cur]!).first ≤ sd.pr[cur]! ∧
      (hi - lo).toNat < 2 ^ 48 := by
  obtain ⟨hs, hw, hoff, hlen, hlen48, -⟩ := siftRange_fill_pre hpre
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hw0 := hw cur hcur
  exact ⟨⟨g, hs, by lia [hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3], hoff,
    hlen⟩, hw0.first_pos, by lia [hw0.first_add_head_le], hlen48⟩

private theorem siftRange_walk_pre (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {M sv : Array UInt64} {F : Array UInt64} {n0 cur : ℕ} {pref suff : List ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat mask F n0)
    (hM : RangeMasksPost g sd F k ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat
      (lo - (sd.chunks[k]!).wLow).toNat (hi - lo).toNat (c0 >>> longShift - (sd.chunks[k]!).wLow)
      c0 M)
    (hv : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat pref (cur :: suff) sv) {w : WalkSpec}
    (hw : w.IsWalk sd.pr[cur]! (hi - lo).toNat
      (((sd.chunks[k]!).walk[cur]!).first + ((lo - (sd.chunks[k]!).wLow).toNat : ℕ))) :
    w.WF sd.pr[cur]! ∧
      (lo - (sd.chunks[k]!).wLow).toNat + (w.head + w.nper * sd.pr[cur]! + w.tail) ≤ sv.size := by
  refine ⟨hw.toWF, ?_⟩
  rw [hw.length_eq, hv.1, hM.1, hF.1]
  exact (siftRange_fill_pre hpre).2.2.2.2.2

private theorem siftRange_walk_step (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {M sv T : Array UInt64} {n cur : ℕ} {pref suff : List ℕ}
    (hc : ForIn.toList [n:g.sievePrimes1] = pref ++ cur :: suff)
    (hv : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat pref (cur :: suff) sv) {w : WalkSpec}
    (hw : w.IsWalk sd.pr[cur]! (hi - lo).toNat
      (((sd.chunks[k]!).walk[cur]!).first + ((lo - (sd.chunks[k]!).wLow).toNat : ℕ)))
    (hT : T.size = sv.size ∧
      (∀ t < w.head + w.nper * sd.pr[cur]! + w.tail, T[(lo - (sd.chunks[k]!).wLow).toNat + t]! =
        andOp sv[(lo - (sd.chunks[k]!).wLow).toNat + t]!
          (g.sieve.sieveTab[cur]!)[s.rowptr[cur]! + (w.first + t) % sd.pr[cur]!]!) ∧
      ∀ m, (m < (lo - (sd.chunks[k]!).wLow).toNat ∨ (lo - (sd.chunks[k]!).wLow).toNat +
          (w.head + w.nper * sd.pr[cur]! + w.tail) ≤ m) → T[m]! = sv[m]!) :
    WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat (pref ++ [cur]) suff T := by
  have hcw := (siftRange_fill_pre hpre).2.1 cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)
  exact walksInvariant_step hv hw (Int.ModEq.add_right _ hcw.first_emod) hT

private theorem siftRange_scan_pre (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {F M S' : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat mask F n)
    (hM : RangeMasksPost g sd F k ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat
      (lo - (sd.chunks[k]!).wLow).toNat (hi - lo).toNat (c0 >>> longShift - (sd.chunks[k]!).wLow)
      c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat (ForIn.toList [n:g.sievePrimes1]) [] S') :
    ScanPre g sd { s with survivors := S' } a b (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      ((lo - (sd.chunks[k]!).wLow).toNat + (hi - lo).toNat) := by
  have hlen := hpre.off_add_len_le
  obtain ⟨h, hk, -, -, -, -, hw, hA, hB, h3, -, ha, haH, hbH, ha0, -⟩ := id hpre
  exact ⟨h.toIsStageSetup, hw, hA, hB, h3, ha, haH, hbH, ha0,
    fun i _ hi ↦ h.wordResidues hk (by lia [h.range_chunk_le hk]),
    fun i hi1 hi2 c hc hbit ↦
      h.abs_le_of_getLsbD (fun j hj ↦ siftRange_bits hpre hF hM hS hi1 hi2 hj) hc hbit⟩

private theorem siftRange_post (hpre : SiftRangePre g sd s a b k lo hi mask c0)
    {F M S' : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat mask F n)
    (hM : RangeMasksPost g sd F k ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat
      (lo - (sd.chunks[k]!).wLow).toNat (hi - lo).toNat (c0 >>> longShift - (sd.chunks[k]!).wLow)
      c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat (ForIn.toList [n:g.sievePrimes1]) [] S') {r : Bool × SiftState}
    (hr : ScanPost g sd { s with survivors := S' } (scanPoints g S' a b (sd.chunks[k]!)
      (List.range' (lo - (sd.chunks[k]!).wLow).toNat ((lo - (sd.chunks[k]!).wLow).toNat +
        (hi - lo).toNat - (lo - (sd.chunks[k]!).wLow).toNat))) r) :
    SiftPost g sd s (rowRangePoints g sd a b lo hi) r := by
  obtain ⟨h, hk, hlo, -, -, -, -, -, -, -, -, ha, -, -, ha0, -, hc0⟩ := id hpre
  rw [h.scanPoints_eq_rowRangePoints ha ha0 hc0 (Nat.le_add_right _ _)
    (fun t ht1 ht2 j hj ↦ siftRange_bits hpre hF hM hS ht1 ht2 hj),
    rowRangePoints_off_len _ _ _ _ hlo] at hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hsv : r.2.survivors = S' := congr(SiftState.survivors $h1)
  exact ⟨SiftState.with_survivors_trans h1, by rw [hsv, hS.1, hM.1, hF.1], h2, h3, h4⟩

end SiftRange

attribute [local irreducible] WalksInvariant ScanPost in
/-- `sift_range` prints the points of the row `(a, b)` in the words `[lo, hi)` of the `k`-th chunk
(`JPoints.rowRangePoints`), only the first under `-1`: the fill and the masks of the positions of
the range, the walks of the first stage over them from the walks of the chunk (`walk_parts`), and
the words of the range passed to the second stage (`JPoints.scanWords_spec`). It changes no other
field of the state but the bit array, the data of the third stage, the counters and the output
(`JPoints.SiftPost`). The flag returned says whether it stopped at a point under `-1`. -/
@[spec]
theorem siftRange_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (k : ℕ)
    (lo hi : ℤ) (mask : UInt64) (c0 : ℤ) :
    ⦃ SiftRangePre g sd s a b k lo hi mask c0 ⦄
    siftRange g sd s a b k lo hi mask c0
    ⦃ fun r ↦ SiftPost g sd s (rowRangePoints g sd a b lo hi) r ⦄ := by
  vcgen [siftRange, siftRangeFill_spec, siftRangeMasks_spec, walkParts_spec, walk_spec,
    scanWords_spec] invariants
  · WalksInvariant g sd s.rowptr survivors (sd.chunks[k]!) (lo - (sd.chunks[k]!).wLow).toNat
      (hi - lo).toNat
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact siftRange_fill_pre ‹_›
    | exact siftRange_masks_pre ‹_› ‹_›
    | exact walksInvariant_nil
    | exact siftRange_scan_pre ‹_› ‹_› ‹_› ‹_›
    | exact siftRange_post ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftRange_parts_pre ‹_› ‹_›
    | exact siftRange_walk_pre ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftRange_walk_step ‹_› ‹_› ‹_› ‹_› ‹_›

end JPoints

end
