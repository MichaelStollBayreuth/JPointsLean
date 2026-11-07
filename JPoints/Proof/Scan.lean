/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.CheckPoint

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Order
import Mathlib.Data.List.Sort
import Std.Tactic.Do

/-!
# The words of a row past the first stage

What the sieve of a row of `j-points` reads of the set-up of the main search
(`JPoints.IsRowSetup`), the points that it finds in a range of words of a row
(`JPoints.rowRangePoints`), and the contract of `scan_words` (`JPoints.scanWords_spec`), which hands
the words of the bit array left by the first stage to `check_point` and prints the points of their
bits (`JPoints.scanPoints`). A word whose bits are those that the first stage, the mask of the row,
the masks of the ends of the row and the excluded third coordinate `c0` leave gives the points of
the row in the word (`JPoints.IsRowSetup.wordPoints_eq_of_getLsbD`), and the words of a range of
positions those of the range of words (`JPoints.IsRowSetup.scanPoints_eq_rowRangePoints`).

## Main definitions

* `JPoints.IsRowSetup`: what the sieve of a row reads of the set-up.
* `JPoints.rowRangePoints`: the points of a row in a range of words.
* `JPoints.scanPoints`: the points that `scan_words` finds.
* `JPoints.ScanCont`, `JPoints.ScanPost`, `JPoints.ScanInvariant`, `JPoints.ScanPre`: the invariant
  and the conditions of the loop of `scan_words`.

## Main statements

* `JPoints.scanWords_spec`: the words of a range of positions of a chunk.
* `JPoints.rowPoints_eq_rowRangePoints`, `JPoints.rowRangePoints_append`,
  `JPoints.IsRowSetup.flatMap_range'_wordPoints`: the points of a row by ranges of words.
* `JPoints.IsRowSetup.scanPoints_eq_rowRangePoints`: the points of the words that the first stage
  leaves.
* `JPoints.IsRowSetup.rangeKeeps_eq`: the test of the third coordinates of a row by its range.
* `JPoints.bne_siftMask_fst_eq_not_conic`: the excluded third coordinate `c0` is that of the conic.

## Implementation notes

The contract is a triple of `Std.WP` on the component in `Id`, proved by `vcgen` with a named
invariant, each verification condition closed by a lemma stated in its own shape; the structure
literals of the states in the conditions are reduced by `dsimp only` first. Two lists of points are
compared as the filters of increasing lists with the same members (`List.Pairwise.eq_of_mem_iff`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-- What the sieve of a row reads of the set-up of the main search, for the globals `g` and the
static data `sd` of the sieve: what the stages read (`JPoints.IsStageSetup`), a bit array of at
least one word, and the masks `begmask` and `endmask` of the first and the last word of a row as
`main` sets them (`JPoints.Program.mainMasks`). -/
structure IsRowSetup (g : SiftGlobals) (sd : SiftData) : Prop extends IsStageSetup g sd where
  /-- The bit array has a word. -/
  one_le_arraySize : 1 ≤ g.arraySize
  /-- The mask of the first word of a row. -/
  begmask_eq : g.begmask = (Program.mainMasks g.check.height).1
  /-- The mask of the last word of a row. -/
  endmask_eq : g.endmask = (Program.mainMasks g.check.height).2

theorem IsSieveSetup.isRowSetup {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) :
    IsRowSetup bg.sift sd := by
  refine ⟨h.isStageSetup, ?_, ?_, ?_⟩ <;> obtain ⟨g, hg, hs⟩ := h
  · exact hs.arraySize_eq ▸ hg.one_le_arraySize
  · rw [hs.begmask_eq, hg.begmask_eq, hs.check_eq]
  · rw [hs.endmask_eq, hg.endmask_eq, hs.check_eq]

theorem IsRowSetup.rangeKeeps_eq {g : SiftGlobals} {sd : SiftData} (h : IsRowSetup g sd) (c : ℤ) :
    rangeKeeps g sd c = decide (|c| ≤ g.check.height) :=
  rangeKeeps_eq_decide_abs_le h.siftData.wLowAll_eq h.siftData.wHighAll_eq h.begmask_eq
    h.endmask_eq c

/-- The points that the sieve of the row `(a, b)` finds in the words `lo ≤ i < hi` of the row, for
the globals `g` and the static data `sd` of the sieve: the points over the triples `(a, b, c)`
(`JPoints.CheckGlobals.points`) whose third coordinate the sieve of a row hands to the exact check
(`JPoints.colKeeps`), off the conic, with its word `⌊c / 64⌋` in `[lo, hi)`, `c` increasing. -/
def rowRangePoints (g : SiftGlobals) (sd : SiftData) (a b lo hi : ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  ((intRange g.check.H).filter fun c ↦ colKeeps g sd a b c && !conic a b c &&
    decide (lo ≤ c >>> longShift ∧ c >>> longShift < hi)).flatMap fun c ↦ g.check.points (a, b, c)

theorem rowRangePoints_append (g : SiftGlobals) (sd : SiftData) (a b : ℤ) {lo mid hi : ℤ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    rowRangePoints g sd a b lo mid ++ rowRangePoints g sd a b mid hi =
      rowRangePoints g sd a b lo hi := by
  simp only [rowRangePoints, Int.shiftRight_longShift]
  rw [← List.flatMap_append, List.filter_append_filter_of_pairwise (pairwise_lt_intRange _)
    fun x _ y _ hx hy ↦ by simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hy; lia]
  congr 1
  refine List.filter_congr fun c _ ↦ ?_
  rw [← Bool.and_or_distrib_left, ← Bool.decide_or]
  exact congr(_ && $(decide_eq_decide.mpr (by lia)))

private theorem rangeKeeps_of_colKeeps {g : SiftGlobals} {sd : SiftData} {a b c : ℤ}
    (h : colKeeps g sd a b c = true) : rangeKeeps g sd c = true := by
  simp only [colKeeps, Bool.and_eq_true] at h
  exact h.1.2

private theorem le_and_lt_of_rangeKeeps {g : SiftGlobals} {sd : SiftData} {c : ℤ}
    (h : rangeKeeps g sd c = true) :
    sd.wLowAll ≤ c >>> longShift ∧ c >>> longShift < sd.wHighAll := by
  simp only [rangeKeeps, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- The word `⌊c / 64⌋` of a third coordinate `c` of absolute value at most the height bound lies
among the words of a row, from `JPoints.SiftData.wLowAll` below `JPoints.SiftData.wHighAll`. -/
theorem IsRowSetup.wLowAll_le_and_lt_wHighAll {g : SiftGlobals} {sd : SiftData}
    (h : IsRowSetup g sd) {c : ℤ} (hc : |c| ≤ g.check.height) :
    sd.wLowAll ≤ c >>> longShift ∧ c >>> longShift < sd.wHighAll :=
  le_and_lt_of_rangeKeeps ((h.rangeKeeps_eq c).trans (decide_eq_true hc))

theorem rowPoints_eq_rowRangePoints (g : SiftGlobals) (sd : SiftData) (a b : ℤ) :
    rowPoints g sd a b = rowRangePoints g sd a b sd.wLowAll sd.wHighAll := by
  simp only [rowPoints, rowRangePoints]
  congr 1
  refine List.filter_congr fun c _ ↦ ?_
  cases h : colKeeps g sd a b c
  · rfl
  · simp [le_and_lt_of_rangeKeeps (rangeKeeps_of_colKeeps h)]

theorem IsRowSetup.wordPoints_eq_rowRangePoints {g : SiftGlobals} {sd : SiftData}
    (h : IsRowSetup g sd) (a b i : ℤ) :
    g.check.wordPoints (fun c ↦ colKeeps g sd a b c && !conic a b c) a b i =
      rowRangePoints g sd a b i (i + 1) := by
  simp only [CheckGlobals.wordPoints, rowRangePoints]
  congr 1
  have hH := h.check.one_le_height
  refine ((List.pairwise_map.mpr (List.pairwise_lt_range.imp fun hij ↦ by lia)).filter
    _).eq_of_mem_iff ((pairwise_lt_intRange _).filter _) fun x ↦ ?_
  simp only [List.mem_filter, List.mem_map, List.mem_range, mem_intRange_iff, Bool.and_eq_true,
    decide_eq_true_eq, Int.shiftRight_longShift]
  refine ⟨fun ⟨⟨j, hj, hx⟩, hk⟩ ↦ ?_, fun ⟨_, hk, hx⟩ ↦ ⟨⟨(x - 64 * i).toNat, by lia, by lia⟩, hk⟩⟩
  have := of_decide_eq_true (h.rangeKeeps_eq x ▸ rangeKeeps_of_colKeeps hk.1)
  rw [abs_le] at this ⊢
  exact ⟨by lia, hk, by lia⟩

theorem rowRangePoints_self (g : SiftGlobals) (sd : SiftData) (a b lo : ℤ) :
    rowRangePoints g sd a b lo lo = [] := by
  simp [rowRangePoints]

theorem IsRowSetup.flatMap_range'_wordPoints {g : SiftGlobals} {sd : SiftData}
    (h : IsRowSetup g sd) (a b w : ℤ) (s n : ℕ) :
    (List.range' s n).flatMap (fun i : ℕ ↦
        g.check.wordPoints (fun c ↦ colKeeps g sd a b c && !conic a b c) a b (w + i)) =
      rowRangePoints g sd a b (w + s) (w + s + n) := by
  induction n generalizing s with
  | zero => simp [rowRangePoints_self]
  | succ n ih =>
    rw [List.range'_succ, List.flatMap_cons, ih, h.wordPoints_eq_rowRangePoints,
      ← rowRangePoints_append g sd a b (lo := w + s) (mid := w + s + 1)
        (hi := w + s + (n + 1 : ℕ)) (by lia) (by lia)]
    congr 2 <;> push_cast <;> ring

theorem rowRangePoints_eq_nil_of_le (g : SiftGlobals) (sd : SiftData) (a b : ℤ) {lo hi : ℤ}
    (h : hi ≤ lo) : rowRangePoints g sd a b lo hi = [] := by
  simp only [rowRangePoints, List.flatMap_eq_nil_iff, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  intro c ⟨_, _, h1, h2⟩
  lia

/-- The words `lo ≤ i < hi` of a chunk from the word `wLow ≤ lo` on, as the positions
`off ≤ m < off + len` of `sift_range`, `off = lo - wLow` and `len = hi - lo` (`0` for `hi < lo`). -/
theorem rowRangePoints_off_len (g : SiftGlobals) (sd : SiftData) (a b : ℤ) {wLow lo hi : ℤ}
    (h : wLow ≤ lo) :
    rowRangePoints g sd a b (wLow + ((lo - wLow).toNat : ℕ))
        (wLow + ((lo - wLow).toNat + (hi - lo).toNat : ℕ)) =
      rowRangePoints g sd a b lo hi := by
  rcases le_or_gt lo hi with hlh | hlh
  · congr 1 <;> push_cast <;> lia
  · rw [rowRangePoints_eq_nil_of_le _ _ _ _ (by lia), rowRangePoints_eq_nil_of_le _ _ _ _ hlh.le]

theorem bne_siftMask_fst_eq_not_conic {g : SiftGlobals} {a b c : ℤ} (ha : 0 ≤ a)
    (hab : a = 0 → 1 ≤ b) (hc : |c| ≤ g.check.height) :
    (c != (siftMask g a b).1) = !conic a b c := by
  rw [abs_le] at hc
  simp only [siftMask, conic]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [longLength]
    lia
  · have h4 : (0 : ℤ) < 4 * a := by lia
    rw [Int.tmod_eq_emod_of_nonneg (mul_self_nonneg b),
      Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg b), Bool.eq_iff_iff]
    by_cases hd : b * b % (4 * a) = 0
    · obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hd
      have e : b ^ 2 = 4 * a * c ↔ c = q := by
        rw [sq, hq]
        exact ⟨fun h ↦ (mul_left_cancel₀ h4.ne' h).symm, fun h ↦ by rw [h]⟩
      simp [hq, Int.mul_ediv_cancel_left _ h4.ne', ha'.ne', e]
    · have e : b ^ 2 ≠ 4 * a * c := fun h ↦ hd (by rw [← sq, h, Int.mul_emod_right])
      simp [hd, e, longLength]
      lia

theorem IsRowSetup.wordPoints_eq_of_getLsbD {g : SiftGlobals} {sd : SiftData}
    (h : IsRowSetup g sd) {a b c0 : ℤ} (ha : 0 ≤ a) (hab : a = 0 → 1 ≤ b)
    (hc0 : c0 = (siftMask g a b).1) {sv : Array UInt64} {t : ℕ} {i : ℤ}
    (hbits : ∀ j < 64, (sv[t]!).toBitVec.getLsbD j = (maskKeeps g a b (64 * i + j) &&
      stage1Keeps g a b (64 * i + j) && rangeKeeps g sd (64 * i + j) && (64 * i + j != c0))) :
    g.check.wordPoints (fun c ↦ sv[t]!.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c &&
        coprimeKeeps a b c && stage3Keeps g a b c) a b i =
      g.check.wordPoints (fun c ↦ colKeeps g sd a b c && !conic a b c) a b i := by
  simp only [CheckGlobals.wordPoints]
  congr 1
  refine List.filter_congr fun c hc ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hj' := List.mem_range.mp hj
  rw [Int.toNat_mul_add_emod_of_lt (by lia), hbits j hj', colKeeps]
  cases hr : rangeKeeps g sd (64 * i + j)
  · simp
  · rw [hc0, bne_siftMask_fst_eq_not_conic ha hab (of_decide_eq_true (h.rangeKeeps_eq _ ▸ hr))]
    cases maskKeeps g a b (64 * i + j) <;> cases stage1Keeps g a b (64 * i + j) <;>
      cases stage2Keeps g a b (64 * i + j) <;> cases stage3Keeps g a b (64 * i + j) <;>
      cases coprimeKeeps a b (64 * i + j) <;> cases conic a b (64 * i + j) <;> rfl

/-- The points that `scan_words` finds in the words of the positions `l` of the chunk `ch` of the
row `(a, b)` with the bit array `sv`, for the globals `g` of the sieve: for each position `i` in
turn, the points over the triples of the third coordinates of the word `w_low + i` whose bits
`sv[i]` has and that the second stage, the test of coprimality and the third stage keep
(`JPoints.CheckGlobals.wordPoints`), as `JPoints.checkPoint` prints them. -/
def scanPoints (g : SiftGlobals) (sv : Array UInt64) (a b : ℤ) (ch : ChunkSpec) (l : List ℕ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  l.flatMap fun i : ℕ ↦ g.check.wordPoints (fun c ↦ sv[i]!.toBitVec.getLsbD (c % 64).toNat &&
    stage2Keeps g a b c && coprimeKeeps a b c && stage3Keeps g a b c) a b (ch.wLow + i)

/-- The state `s'` of `scan_words` after some words, from the state `s`, with the points `L` of
these words: `s` with its own data of the third stage, counters and output, consistent data of the
third stage (`JPoints.Row3Cache.WF`), the points printed after the output of `s`, and none under
`-1`. -/
def ScanCont (g : SiftGlobals) (sd : SiftData) (s s' : SiftState) (L : List (ℤ × ℤ × ℤ × ℤ)) :
    Prop :=
  s' = { s with
      row3 := s'.row3, numSurv1 := s'.numSurv1, numSurv2 := s'.numSurv2,
      numSurv3 := s'.numSurv3, out := s'.out } ∧ Row3Cache.WF g sd s'.row3 ∧
    s.out.Searched g.check L s'.out

/-- The postcondition of `JPoints.scanWords` for the state `s`, the points `L` of its words and the
result `r`: the state `s` with its own data of the third stage, counters and output, consistent data
of the third stage (`JPoints.Row3Cache.WF`), the points printed after the output of `s`, only the
first under `-1`, and the flag of a point under `-1`. -/
def ScanPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (L : List (ℤ × ℤ × ℤ × ℤ))
    (r : Bool × SiftState) : Prop :=
  r.2 = { s with
      row3 := r.2.row3, numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2,
      numSurv3 := r.2.numSurv3, out := r.2.out } ∧ Row3Cache.WF g sd r.2.row3 ∧
    r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint L) ∧
    r.1 = (g.check.onePoint && !L.isEmpty)

/-- The invariant of the loop of `JPoints.scanWords` over the positions `[lo, hi)` of the chunk
`ch` of the row `(a, b)`, from the state `s`, whose state is the result of an early return, the
state of the thread and the position: before a return, the position of the cursor and the state
after the words before it (`JPoints.ScanCont`); after it, the postcondition
(`JPoints.ScanPost`). -/
def ScanInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (ch : ChunkSpec)
    (lo hi : ℕ) : Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState × ℕ) Prop :=
  fun pref suff st ↦ st.1.elim
    (st.2.2 = lo + pref.length ∧ ScanCont g sd s st.2.1 (scanPoints g s.survivors a b ch pref))
    fun r ↦ suff = [] ∧
      ScanPost g sd s (scanPoints g s.survivors a b ch (List.range' lo (hi - lo))) r

/-- The precondition of `JPoints.scanWords` for the state `s`, the chunk `ch` and its positions
`[lo, hi)` in the row `(a, b)`: what the stages read (`JPoints.IsStageSetup`), the rows of the sieve
tables of the row (`JPoints.RowSetupCache.WF` with `(last_a, last_b) = (a, b)`), consistent data of
the third stage, `0 ≤ a ≤ H`, `|b| ≤ H`, `b ≥ 1` for `a = 0`, the residues of the words of the
positions (`JPoints.WordResidues`), and the bits of their words within the height bound. -/
abbrev ScanPre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (ch : ChunkSpec)
    (lo hi : ℕ) : Prop :=
  IsStageSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧
    s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧ 0 ≤ a ∧ a ≤ g.check.height ∧
    |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
    (∀ i, lo ≤ i → i < hi → WordResidues g sd (i * sd.npr) ch.res (ch.wLow + i)) ∧
    ∀ i, lo ≤ i → i < hi → ∀ c ∈ wordCols (ch.wLow + i),
      s.survivors[i]!.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height

private theorem scanPoints_append (g : SiftGlobals) (sv : Array UInt64) (a b : ℤ) (ch : ChunkSpec)
    (l₁ l₂ : List ℕ) :
    scanPoints g sv a b ch (l₁ ++ l₂) = scanPoints g sv a b ch l₁ ++ scanPoints g sv a b ch l₂ :=
  List.flatMap_append

private theorem scanPoints_singleton (g : SiftGlobals) (sv : Array UInt64) (a b : ℤ)
    (ch : ChunkSpec)
    (i : ℕ) :
    scanPoints g sv a b ch [i] = g.check.wordPoints (fun c ↦
      sv[i]!.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c && coprimeKeeps a b c &&
        stage3Keeps g a b c) a b (ch.wLow + i) := by
  simp [scanPoints]

-- The postcondition of `JPoints.checkPoint` for the state `s`, the word `nums` of index `i` of
-- the row `(a, b)` and the result `(found, s')`.
private abbrev CheckPointPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64)
    (a b i : ℤ) (found : Bool) (s' : SiftState) : Prop :=
  s' = { s with
      row3 := s'.row3, numSurv1 := s'.numSurv1, numSurv2 := s'.numSurv2,
      numSurv3 := s'.numSurv3, out := s'.out } ∧
    Row3Cache.WF g sd s'.row3 ∧
    s'.out = s.out.appendPoints g.check (firstIf g.check.onePoint (g.check.wordPoints
      (fun c ↦ nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c &&
        coprimeKeeps a b c && stage3Keeps g a b c) a b i)) ∧
    found = (g.check.onePoint && !(g.check.wordPoints (fun c ↦
      nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c && coprimeKeeps a b c &&
        stage3Keeps g a b c) a b i).isEmpty)

section Scan

variable {g : SiftGlobals} {sd : SiftData} {s st s' : SiftState} {a b : ℤ} {ch : ChunkSpec}
  {lo hi : ℕ} {pref suff : List ℕ} {cur surv : ℕ} {o : Option (Bool × SiftState)}

private theorem scanInvariant_init (hpre : ScanPre g sd s a b ch lo hi) {l : List ℕ} :
    ScanInvariant g sd s a b ch lo hi [] l (none, s, lo) :=
  ⟨by simp, rfl, hpre.2.2.2.2.1, by simp [scanPoints], fun _ ↦ rfl⟩

private theorem scanInvariant_post_some {x : Bool} {y : SiftState}
    (hv : ScanInvariant g sd s a b ch lo hi (ForIn.toList [lo:hi]) [] (o, st, surv))
    (ho : o = some (x, y)) :
    ScanPost g sd s (scanPoints g s.survivors a b ch (List.range' lo (hi - lo))) (x, y) := by
  subst ho
  exact hv.2

private theorem scanInvariant_post_none
    (hv : ScanInvariant g sd s a b ch lo hi (ForIn.toList [lo:hi]) [] (o, st, surv))
    (ho : o = none) :
    ScanPost g sd s (scanPoints g s.survivors a b ch (List.range' lo (hi - lo))) (false, st) := by
  subst ho
  obtain ⟨-, h1, h2, h3, h4⟩ := hv
  dsimp only at h1 h2 h3
  rw [Std.Legacy.Range.toList_eq_range'] at h3 h4
  exact ⟨h1, h2, Output.Searched.post ⟨by simpa using h3, h4⟩⟩

private theorem ScanInvariant.cont
    (hv : ScanInvariant g sd s a b ch lo hi pref (cur :: suff) (o, st, surv)) :
    o = none ∧ surv = lo + pref.length ∧
      ScanCont g sd s st (scanPoints g s.survivors a b ch pref) :=
  Option.eq_none_and_of_elim_cons hv

private theorem scanInvariant_pre (hpre : ScanPre g sd s a b ch lo hi)
    (hc : ForIn.toList [lo:hi] = pref ++ cur :: suff)
    (hv : ScanInvariant g sd s a b ch lo hi pref (cur :: suff) (o, st, surv)) :
    IsStageSetup g sd ∧ RowSetupCache.WF g sd st.rowptr st.rowSetup ∧ st.rowSetup.lastA = a ∧
      st.rowSetup.lastB = b ∧ Row3Cache.WF g sd st.row3 ∧
      WordResidues g sd (cur * sd.npr) ch.res (ch.wLow + cur) ∧ 0 ≤ a ∧ a ≤ g.check.height ∧
      |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
      ∀ c ∈ wordCols (ch.wLow + cur),
        st.survivors[surv]!.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height := by
  obtain ⟨-, hsurv, hst, h3, -⟩ := hv.cont
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨h0, hw, hA, hB, -, ha, haH, hbH, ha0, hres, hbits⟩ := hpre
  rw [hst]
  refine ⟨h0, hw, hA, hB, h3, hres cur (by lia) hlt, ha, haH, hbH, ha0, ?_⟩
  rw [hsurv, hcur]
  exact hbits cur (by lia) hlt

private theorem ScanCont.survivors_eq {L : List (ℤ × ℤ × ℤ × ℤ)} (h : ScanCont g sd s st L) :
    st.survivors = s.survivors :=
  congr(SiftState.survivors $(h.1))

private theorem scanInvariant_return (hc : ForIn.toList [lo:hi] = pref ++ cur :: suff)
    (hv : ScanInvariant g sd s a b ch lo hi pref (cur :: suff) (o, st, surv)) {found : Bool}
    (hcp : CheckPointPost g sd st st.survivors[surv]! a b (ch.wLow + cur) found s')
    (hf : (found && g.check.onePoint) = true) :
    ScanInvariant g sd s a b ch lo hi (ForIn.toList [lo:hi]) []
      (some (true, s'), s', surv + 1) := by
  obtain ⟨rfl, hsurv, hst⟩ := hv.cont
  obtain ⟨h1, h2, h3, h4⟩ := hcp
  rw [hst.survivors_eq, hsurv, Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc] at h3 h4
  obtain ⟨e1, e2⟩ := Output.appendPoints_firstIf_of_found (out := s.out)
    (R := scanPoints g s.survivors a b ch suff) hst.2.2.2 h4 hf
  rw [← hst.2.2.1, ← h3, ← scanPoints_singleton, ← scanPoints_append, ← scanPoints_append,
    ← List.append_cons, ← hc, Std.Legacy.Range.toList_eq_range'] at e1
  rw [← scanPoints_singleton, ← scanPoints_append, ← scanPoints_append, ← List.append_cons, ← hc,
    Std.Legacy.Range.toList_eq_range'] at e2
  exact ⟨rfl, SiftState.with_trans hst.1 h1, h2, e1, e2⟩

private theorem scanInvariant_next (hc : ForIn.toList [lo:hi] = pref ++ cur :: suff)
    (hv : ScanInvariant g sd s a b ch lo hi pref (cur :: suff) (o, st, surv)) {found : Bool}
    (hcp : CheckPointPost g sd st st.survivors[surv]! a b (ch.wLow + cur) found s')
    (hf : ¬(found && g.check.onePoint) = true) :
    ScanInvariant g sd s a b ch lo hi (pref ++ [cur]) suff (none, s', surv + 1) := by
  obtain ⟨rfl, hsurv, hst⟩ := hv.cont
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  obtain ⟨h1, h2, h3, h4⟩ := hcp
  rw [hst.survivors_eq, hsurv, hcur] at h3 h4
  obtain ⟨e1, e2⟩ := Output.appendPoints_firstIf_of_not_found (out := s.out) hst.2.2.2 h4 hf
  rw [← hst.2.2.1, ← h3, ← scanPoints_singleton, ← scanPoints_append] at e1
  rw [← scanPoints_singleton, ← scanPoints_append] at e2
  exact ⟨by simp [hsurv]; lia, SiftState.with_trans hst.1 h1, h2, e1, e2⟩

private theorem scanInvariant_skip (hc : ForIn.toList [lo:hi] = pref ++ cur :: suff)
    (hv : ScanInvariant g sd s a b ch lo hi pref (cur :: suff) (o, st, surv))
    (hz : ¬(st.survivors[surv]! != 0) = true) :
    ScanInvariant g sd s a b ch lo hi (pref ++ [cur]) suff (none, st, surv + 1) := by
  obtain ⟨rfl, hsurv, hst⟩ := hv.cont
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hc
  rw [hst.survivors_eq, hsurv, hcur] at hz
  have h0 : s.survivors[cur]! = 0 := by simpa using hz
  refine ⟨by simp [hsurv]; lia, hst.1, hst.2.1, ?_, fun hop ↦ ?_⟩
  · simp [hst.2.2.1, scanPoints_append, scanPoints_singleton, h0, CheckGlobals.wordPoints]
  · simp [scanPoints_append, scanPoints_singleton, hst.2.2.2 hop, h0, CheckGlobals.wordPoints]

end Scan

attribute [local irreducible] ScanInvariant in
/-- `scan_words` passes the words of the positions `[lo, hi)` of the chunk `ch` that are not `0` to
`check_point` (`JPoints.checkPoint_spec`), in order, and prints the points that it finds
(`JPoints.scanPoints`), only the first under `-1`, for the precondition of the second stage of each
word (`JPoints.ScanPre`). It changes no other field of the state but the data of the third stage,
the counters and the output (`JPoints.ScanPost`). -/
@[spec]
theorem scanWords_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ)
    (ch : ChunkSpec) (lo hi : ℕ) :
    ⦃ ScanPre g sd s a b ch lo hi ⦄
    scanWords g sd s a b ch lo hi
    ⦃ fun r ↦ ScanPost g sd s (scanPoints g s.survivors a b ch (List.range' lo (hi - lo))) r ⦄ := by
  vcgen [scanWords] invariants
  · ScanInvariant g sd s a b ch lo hi
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact scanInvariant_init ‹_›
    | exact scanInvariant_post_some ‹_› ‹_›
    | exact scanInvariant_post_none ‹_› ‹_›
    | exact scanInvariant_pre ‹_› ‹_› ‹_›
    | exact scanInvariant_return ‹_› ‹_› ‹_› ‹_›
    | exact scanInvariant_next ‹_› ‹_› ‹_› ‹_›
    | exact scanInvariant_skip ‹_› ‹_› ‹_›

theorem IsRowSetup.scanPoints_eq_rowRangePoints {g : SiftGlobals} {sd : SiftData}
    (h : IsRowSetup g sd) {a b c0 : ℤ} (ha : 0 ≤ a) (hab : a = 0 → 1 ≤ b)
    (hc0 : c0 = (siftMask g a b).1) {sv : Array UInt64} {ch : ChunkSpec} {lo hi : ℕ}
    (hlh : lo ≤ hi)
    (hbits : ∀ t, lo ≤ t → t < hi → ∀ j < 64, (sv[t]!).toBitVec.getLsbD j =
      (maskKeeps g a b (64 * (ch.wLow + t) + j) && stage1Keeps g a b (64 * (ch.wLow + t) + j) &&
        rangeKeeps g sd (64 * (ch.wLow + t) + j) && (64 * (ch.wLow + t) + j != c0))) :
    scanPoints g sv a b ch (List.range' lo (hi - lo)) =
      rowRangePoints g sd a b (ch.wLow + lo) (ch.wLow + hi) := by
  rw [scanPoints, List.flatMap_congr fun t ht ↦ h.wordPoints_eq_of_getLsbD ha hab hc0
    (hbits t (List.mem_range'_1.mp ht).1 (by lia [List.mem_range'_1.mp ht])),
    h.flatMap_range'_wordPoints]
  congr 1
  lia

/-- A bit that the first stage leaves in a word of a chunk is that of a third coordinate within the
height bound. -/
theorem IsRowSetup.abs_le_of_getLsbD {g : SiftGlobals} {sd : SiftData} {a b c0 : ℤ}
    {sv : Array UInt64} {t : ℕ} {i c : ℤ} (h : IsRowSetup g sd)
    (hbits : ∀ j < 64, (sv[t]!).toBitVec.getLsbD j = (maskKeeps g a b (64 * i + j) &&
      stage1Keeps g a b (64 * i + j) && rangeKeeps g sd (64 * i + j) && (64 * i + j != c0)))
    (hc : c ∈ wordCols i) (hbit : (sv[t]!).toBitVec.getLsbD (c % 64).toNat = true) :
    |c| ≤ g.check.height := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  have hj' := List.mem_range.mp hj
  rw [Int.toNat_mul_add_emod_of_lt (by lia), hbits j hj'] at hbit
  simp only [Bool.and_eq_true] at hbit
  exact of_decide_eq_true (h.rangeKeeps_eq _ ▸ hbit.1.2)

end JPoints

end
