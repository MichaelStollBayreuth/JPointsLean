/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Tube
public import Std.WP

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.VCSimp
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Std.Tactic.Do

/-!
# The bands of the tube

What the analysis of the tube writes into the bands of the thread and what `row_cut` makes of
them, row by row: the ranges of a row of the bands (`JPoints.TubeBands.rowRanges`), which
`tube_emit` changes by `JPoints.emitRange` and in no other row (`JPoints.rowRanges_tubeEmit_self`,
`JPoints.rowRanges_tubeEmit_of_ne`), for a band of rows with at most `TUBE_RANGES` ranges each
(`JPoints.TubeBands.Sized`); the words of a cell collected for its rows (`JPoints.emitRows`,
`JPoints.run_tubeEmitRows`); the ranges in increasing order within the words of a row
(`JPoints.RangesIn`), which `tube_emit` keeps when it collects the words of a row in increasing
order (`JPoints.RangesIn.emitRange`); and the ranges of a row cut to the real region
(`JPoints.cutRanges`, `JPoints.rowCut_spec`), in increasing order when both are
(`JPoints.RangesIn.cutRanges`), with every word that lies in a range of both
(`JPoints.exists_mem_cutRanges`).

## Main definitions

* `JPoints.TubeBands.rowRanges`, `JPoints.TubeBands.Sized`: the ranges of a row of the bands.
* `JPoints.emitRange`, `JPoints.emitRows`: the words collected for a row and for the rows of a
  cell.
* `JPoints.RangesIn`: ranges in increasing order within the words of a row.
* `JPoints.rangeList`: the list of the ranges of a triple of their number and their ends.
* `JPoints.cutRanges`: the ranges of a row cut to the real region.

## Main statements

* `JPoints.rowRanges_tubeEmit_self`, `JPoints.rowRanges_tubeEmit_of_ne`,
  `JPoints.TubeBands.Sized.emitRows`: the ranges after `tube_emit` and its loop over the rows.
* `JPoints.RangesIn.emitRange`, `JPoints.RangesIn.cutRanges`: the ranges stay in increasing order.
* `JPoints.exists_mem_cutRanges`: the cut keeps the words of both.
* `JPoints.tubeEmitRows_spec`, `JPoints.rowCut_spec`: the contracts by value.

## Implementation notes

The bands keep the ranges of a row in the flat array `band_rg` at `2 TUBE_RANGES row + 2 k` and
the index after it; a row with at most `TUBE_RANGES` ranges reads and writes only its own entries
(`JPoints.TubeBands.index_inj`), so that the lemmas need that bound on every row they read.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The ranges of the rows of a band -/

/-- The ranges `[BLO(row, k), BHI(row, k))`, `k < band_nr[row]`, of the `row`-th row of the
bands. -/
def TubeBands.rowRanges (bd : TubeBands) (row : ℕ) : List (ℤ × ℤ) :=
  (List.range bd.bandNr[row]!).map fun k ↦ (bd.blo row k, bd.bhi row k)

namespace TubeBands

variable {bd bd' : TubeBands} {row row' k k' : ℕ} {v : ℤ}

theorem index_ne_odd_index (row k row' k' : ℕ) :
    2 * tubeRanges * row + 2 * k ≠ 2 * tubeRanges * row' + 2 * k' + 1 := by
  lia

theorem index_inj (hk : k < tubeRanges) (hk' : k' < tubeRanges)
    (h : 2 * tubeRanges * row + 2 * k = 2 * tubeRanges * row' + 2 * k') : row = row' ∧ k = k' :=
  Nat.eq_and_eq_of_mul_add_eq_mul_add hk hk' (by lia)

theorem blo_setBhi (row k : ℕ) (v : ℤ) (row' k' : ℕ) :
    (bd.setBhi row k v).blo row' k' = bd.blo row' k' := by
  simp only [blo, setBhi]
  rw [Array.getElem!_set!_ne _ _ _ _ (index_ne_odd_index row' k' row k).symm]

theorem bhi_setBlo (row k : ℕ) (v : ℤ) (row' k' : ℕ) :
    (bd.setBlo row k v).bhi row' k' = bd.bhi row' k' := by
  simp only [bhi, setBlo]
  rw [Array.getElem!_set!_ne _ _ _ _ (index_ne_odd_index row k row' k')]

theorem blo_setBlo_ne (hk : k < tubeRanges) (hk' : k' < tubeRanges) (h : ¬(row = row' ∧ k = k'))
    (v : ℤ) : (bd.setBlo row k v).blo row' k' = bd.blo row' k' := by
  simp only [blo, setBlo]
  rw [Array.getElem!_set!_ne _ _ _ _ fun e ↦ h (index_inj hk hk' e)]

theorem bhi_setBhi_ne (hk : k < tubeRanges) (hk' : k' < tubeRanges) (h : ¬(row = row' ∧ k = k'))
    (v : ℤ) : (bd.setBhi row k v).bhi row' k' = bd.bhi row' k' := by
  simp only [bhi, setBhi]
  rw [Array.getElem!_set!_ne _ _ _ _ fun e ↦ h (index_inj hk hk' (by lia))]

theorem blo_setBlo_self (h : 2 * tubeRanges * row + 2 * k < bd.bandRg.size) (v : ℤ) :
    (bd.setBlo row k v).blo row k = v := by
  simp only [blo, setBlo]
  rw [Array.getElem!_set!_self _ _ _ h]

theorem bhi_setBhi_self (h : 2 * tubeRanges * row + 2 * k + 1 < bd.bandRg.size) (v : ℤ) :
    (bd.setBhi row k v).bhi row k = v := by
  simp only [bhi, setBhi]
  rw [Array.getElem!_set!_self _ _ _ h]

theorem bandNr_setBhi (row k : ℕ) (v : ℤ) : (bd.setBhi row k v).bandNr = bd.bandNr := rfl

theorem blo_with_bandNr (bd : TubeBands) (n : Array ℕ) :
    ({ bd with bandNr := n } : TubeBands).blo = bd.blo := rfl

theorem bhi_with_bandNr (bd : TubeBands) (n : Array ℕ) :
    ({ bd with bandNr := n } : TubeBands).bhi = bd.bhi := rfl

theorem size_setBlo (row k : ℕ) (v : ℤ) : (bd.setBlo row k v).bandRg.size = bd.bandRg.size := by
  simp [setBlo]

theorem rowRanges_eq_of (h : bd'.bandNr[row']! = bd.bandNr[row']!)
    (hb : ∀ k < bd.bandNr[row']!, bd'.blo row' k = bd.blo row' k ∧ bd'.bhi row' k = bd.bhi row' k) :
    bd'.rowRanges row' = bd.rowRanges row' := by
  simp only [rowRanges, h]
  exact List.map_congr_left fun k hk ↦ by
    rw [(hb k (List.mem_range.mp hk)).1, (hb k (List.mem_range.mp hk)).2]

theorem length_rowRanges (bd : TubeBands) (row : ℕ) :
    (bd.rowRanges row).length = bd.bandNr[row]! := by
  simp [rowRanges]

theorem getLast!_rowRanges (h : 0 < bd.bandNr[row]!) :
    (bd.rowRanges row).getLast! =
      (bd.blo row (bd.bandNr[row]! - 1), bd.bhi row (bd.bandNr[row]! - 1)) := by
  obtain ⟨n, hn⟩ : ∃ n, bd.bandNr[row]! = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  simp [rowRanges, hn, List.range_succ, List.getLast!_eq_getLast?_getD]

theorem head!_rowRanges (h : 0 < bd.bandNr[row]!) :
    (bd.rowRanges row).head! = (bd.blo row 0, bd.bhi row 0) := by
  obtain ⟨n, hn⟩ : ∃ n, bd.bandNr[row]! = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  rw [rowRanges, hn, List.range_succ_eq_map, List.map_cons]
  rfl

end TubeBands

/-- The ranges of a row after `tube_emit` of the words `[iLo, iHi)` for it
(`JPoints.tubeEmit`), from its ranges `rs`: merged into the last when that reaches `iLo`, the hull
when the row has `TUBE_RANGES` ranges, else a new range. -/
def emitRange (rs : List (ℤ × ℤ)) (iLo iHi : ℤ) : List (ℤ × ℤ) :=
  if 0 < rs.length ∧ iLo ≤ rs.getLast!.2 then
    if rs.getLast!.2 < iHi then rs.dropLast ++ [(rs.getLast!.1, iHi)] else rs
  else if rs.length = tubeRanges then [(rs.head!.1, iHi)]
  else rs ++ [(iLo, iHi)]

theorem bandB0_tubeEmit (bd : TubeBands) (b iLo iHi : ℤ) :
    (tubeEmit bd b iLo iHi).bandB0 = bd.bandB0 := by
  simp only [tubeEmit]
  split_ifs <;> rfl

theorem rowRanges_tubeEmit_of_ne {bd : TubeBands} {b iLo iHi : ℤ} {r : ℕ}
    (hr : r ≠ (b - bd.bandB0).toNat) (hnr : bd.bandNr[r]! ≤ tubeRanges)
    (hnr' : bd.bandNr[(b - bd.bandB0).toNat]! ≤ tubeRanges) :
    (tubeEmit bd b iLo iHi).rowRanges r = bd.rowRanges r := by
  have ht := tubeRanges_pos
  generalize hrow : (b - bd.bandB0).toNat = row at hr hnr'
  have hne (k k' : ℕ) : ¬(row = r ∧ k = k') := fun h ↦ hr h.1.symm
  simp only [tubeEmit, hrow]
  split_ifs with h1 h2 h3
  · refine TubeBands.rowRanges_eq_of rfl fun k hk ↦ ⟨TubeBands.blo_setBhi .., ?_⟩
    exact TubeBands.bhi_setBhi_ne (by lia) (by lia) (hne _ _) _
  · rfl
  · refine TubeBands.rowRanges_eq_of (Array.getElem!_set!_ne _ _ _ _ (Ne.symm hr))
      fun k hk ↦ ⟨TubeBands.blo_setBhi (bd := bd) row 0 iHi r k, ?_⟩
    exact TubeBands.bhi_setBhi_ne (bd := bd) (row' := r) (k' := k) ht (by lia) (hne _ _) iHi
  · refine TubeBands.rowRanges_eq_of (Array.getElem!_set!_ne _ _ _ _ (Ne.symm hr))
      fun k hk ↦ ⟨?_, ?_⟩
    · exact (TubeBands.blo_setBhi ..).trans
        (TubeBands.blo_setBlo_ne (by lia) (by lia) (hne _ _) _)
    · exact (TubeBands.bhi_setBhi_ne (by lia) (by lia) (hne _ _) _).trans
        (TubeBands.bhi_setBlo ..)

namespace TubeBands

variable {bd : TubeBands} {row : ℕ}

theorem rowRanges_setBhi_last (hn : 0 < bd.bandNr[row]!) (hnr : bd.bandNr[row]! ≤ tubeRanges)
    (hidx : 2 * tubeRanges * row + 2 * (bd.bandNr[row]! - 1) + 1 < bd.bandRg.size) (v : ℤ) :
    (bd.setBhi row (bd.bandNr[row]! - 1) v).rowRanges row =
      (bd.rowRanges row).dropLast ++ [(bd.blo row (bd.bandNr[row]! - 1), v)] := by
  obtain ⟨n, hn'⟩ : ∃ n, bd.bandNr[row]! = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn).symm⟩
  rw [hn'] at hidx ⊢
  simp only [rowRanges, bandNr_setBhi, hn', List.range_succ, List.map_append,
    List.map_singleton, Nat.add_sub_cancel, blo_setBhi, bhi_setBhi_self (by simpa using hidx),
    List.dropLast_concat]
  congr 1
  refine List.map_congr_left fun k hk ↦ ?_
  rw [bhi_setBhi_ne (by lia) (by lia [List.mem_range.mp hk]) (by lia [List.mem_range.mp hk])]

theorem rowRanges_hull (hsz : row < bd.bandNr.size)
    (hidx : 2 * tubeRanges * row + 2 * 0 + 1 < bd.bandRg.size) (v : ℤ) :
    ({ bd.setBhi row 0 v with bandNr := bd.bandNr.set! row 1 } : TubeBands).rowRanges row =
      [(bd.blo row 0, v)] := by
  simp only [rowRanges, Array.getElem!_set!_self _ _ _ hsz, List.range_one, List.map_singleton,
    blo_with_bandNr, bhi_with_bandNr, blo_setBhi, bhi_setBhi_self (row := row) (k := 0) hidx]

theorem rowRanges_push (hsz : row < bd.bandNr.size) (hnr : bd.bandNr[row]! < tubeRanges)
    (hidx : 2 * tubeRanges * row + 2 * bd.bandNr[row]! + 1 < bd.bandRg.size) (lo hi : ℤ) :
    ({ (bd.setBlo row bd.bandNr[row]! lo).setBhi row bd.bandNr[row]! hi with
        bandNr := bd.bandNr.set! row (bd.bandNr[row]! + 1) } : TubeBands).rowRanges row =
      bd.rowRanges row ++ [(lo, hi)] := by
  simp only [rowRanges, Array.getElem!_set!_self _ _ _ hsz, List.range_succ, List.map_append,
    List.map_singleton, blo_with_bandNr, bhi_with_bandNr]
  congr 1
  · refine List.map_congr_left fun k hk ↦ ?_
    have hk := List.mem_range.mp hk
    exact congr(($((blo_setBhi ..).trans (blo_setBlo_ne (bd := bd) (by lia) (by lia) (by lia) lo)),
      $((bhi_setBhi_ne (bd := bd.setBlo row bd.bandNr[row]! lo) (by lia) (by lia) (by lia) hi).trans
        (bhi_setBlo ..))))
  · rw [blo_setBhi, blo_setBlo_self (by lia), bhi_setBhi_self (by rw [size_setBlo]; exact hidx)]

end TubeBands

theorem rowRanges_tubeEmit_self {bd : TubeBands} (hrg : bd.bandRg.size = 2 * tubeRanges * tubeBand)
    {b iLo iHi : ℤ} (hrow : (b - bd.bandB0).toNat < tubeBand)
    (hsz : (b - bd.bandB0).toNat < bd.bandNr.size)
    (hnr : bd.bandNr[(b - bd.bandB0).toNat]! ≤ tubeRanges) :
    (tubeEmit bd b iLo iHi).rowRanges (b - bd.bandB0).toNat =
      emitRange (bd.rowRanges (b - bd.bandB0).toNat) iLo iHi := by
  have ht := tubeRanges_pos
  simp only [tubeEmit]
  generalize (b - bd.bandB0).toNat = row at hrow hsz hnr ⊢
  have hidx {k : ℕ} (hk : k < tubeRanges) : 2 * tubeRanges * row + 2 * k + 1 < bd.bandRg.size := by
    rw [hrg]; nlinarith
  rcases Nat.eq_zero_or_pos bd.bandNr[row]! with h0 | h0
  · have hrs : bd.rowRanges row = [] := List.eq_nil_of_length_eq_zero (by
      rw [TubeBands.length_rowRanges, h0])
    rw [ite_eq_right (by lia), ite_eq_right (by lia), TubeBands.rowRanges_push hsz (by lia)
      (hidx (by lia)), emitRange, hrs]
    simp only [List.length_nil, Nat.lt_irrefl, false_and, ↓reduceIte, List.nil_append]
    rw [ite_eq_right (by lia)]
  · rw [emitRange, TubeBands.length_rowRanges, TubeBands.getLast!_rowRanges h0]
    split_ifs with h1 h2 h3
    · exact TubeBands.rowRanges_setBhi_last h0 hnr (hidx (by lia)) iHi
    · rfl
    · rw [TubeBands.rowRanges_hull hsz (hidx ht), TubeBands.head!_rowRanges h0]
    · exact TubeBands.rowRanges_push hsz (by lia) (hidx (by lia)) iLo iHi


/-! ### The words collected -/

/-- The bands `bd` after `tube_emit` of the words `[iLo, iHi)` for each of the rows `bLo..bHi` in
turn, as `JPoints.tubeEmitRows` collects them (`JPoints.run_tubeEmitRows`). -/
def emitRows (bd : TubeBands) (bLo bHi iLo iHi : ℤ) : TubeBands :=
  (List.range (bHi - bLo + 1).toNat).foldl (fun bd (k : ℕ) ↦ tubeEmit bd (bLo + k) iLo iHi) bd

section EmitRows

variable {t : TubeState} {bLo bHi iLo iHi : ℤ} {pref suff : List ℕ} {cur : ℕ} {bd : TubeBands}

theorem emitRowsInvariant_step
    (h : bd = pref.foldl (fun bd (k : ℕ) ↦ tubeEmit bd (bLo + k) iLo iHi) t.bands) :
    tubeEmit bd (bLo + cur) iLo iHi =
      (pref ++ [cur]).foldl (fun bd (k : ℕ) ↦ tubeEmit bd (bLo + k) iLo iHi) t.bands := by
  rw [List.foldl_append, ← h]
  rfl

theorem emitRowsInvariant_post (h : bd = (ForIn.toList [:(bHi - bLo + 1).toNat]).foldl
      (fun bd (k : ℕ) ↦ tubeEmit bd (bLo + k) iLo iHi) t.bands) :
    { k0 := t.k0, k1 := t.k1, k2 := t.k2, ka := t.ka, tubeOk := t.tubeOk,
        tubeNcells := t.tubeNcells, cache := t.cache, bands := bd : TubeState } =
      { t with bands := emitRows t.bands bLo bHi iLo iHi } := by
  rw [h, Std.Legacy.Range.toList_eq_range]
  rfl

end EmitRows

theorem tubeEmitRows_spec (t : TubeState) (bLo bHi iLo iHi : ℤ) :
    ⦃ True ⦄ tubeEmitRows t bLo bHi iLo iHi
    ⦃ fun r ↦ r = { t with bands := emitRows t.bands bLo bHi iLo iHi } ⦄ := by
  vcgen [tubeEmitRows] invariants
  · fun pref _ bd ↦ bd = pref.foldl (fun bd (k : ℕ) ↦ tubeEmit bd (bLo + k) iLo iHi) t.bands
  all_goals try dsimp only at *
  all_goals first
    | rfl
    | exact emitRowsInvariant_step ‹_›
    | exact emitRowsInvariant_post ‹_›

theorem run_tubeEmitRows (t : TubeState) (bLo bHi iLo iHi : ℤ) :
    (tubeEmitRows t bLo bHi iLo iHi).run = { t with bands := emitRows t.bands bLo bHi iLo iHi } :=
  (tubeEmitRows_spec t bLo bHi iLo iHi).le_wp trivial

theorem size_tubeEmit (bd : TubeBands) (b iLo iHi : ℤ) :
    (tubeEmit bd b iLo iHi).bandNr.size = bd.bandNr.size ∧
      (tubeEmit bd b iLo iHi).bandRg.size = bd.bandRg.size := by
  simp only [tubeEmit]
  split_ifs <;> simp [TubeBands.setBhi, TubeBands.setBlo]

theorem size_emitRows (bd : TubeBands) (bLo bHi iLo iHi : ℤ) :
    (emitRows bd bLo bHi iLo iHi).bandNr.size = bd.bandNr.size ∧
      (emitRows bd bLo bHi iLo iHi).bandRg.size = bd.bandRg.size := by
  rw [emitRows]
  generalize List.range _ = l
  induction l generalizing bd with
  | nil => exact ⟨rfl, rfl⟩
  | cons k l ih =>
    obtain ⟨h1, h2⟩ := size_tubeEmit bd (bLo + k) iLo iHi
    obtain ⟨e1, e2⟩ := ih (bd := tubeEmit bd (bLo + k) iLo iHi)
    exact ⟨e1.trans h1, e2.trans h2⟩

/-- The bands `bd` hold a band of `n ≤ TUBE_BAND` rows: arrays of the sizes of
`JPoints.TubeState.WF`, and at most `TUBE_RANGES` ranges in each of the `n` rows. -/
structure TubeBands.Sized (bd : TubeBands) (n : ℕ) : Prop where
  /-- The counts of the rows of a band. -/
  size_bandNr : bd.bandNr.size = tubeBand
  /-- The ends of the ranges of the rows of a band. -/
  size_bandRg : bd.bandRg.size = 2 * tubeRanges * tubeBand
  /-- The band has at most `TUBE_BAND` rows. -/
  le_tubeBand : n ≤ tubeBand
  /-- At most `TUBE_RANGES` ranges in each row of the band. -/
  bandNr_le {row : ℕ} (h : row < n) : bd.bandNr[row]! ≤ tubeRanges

theorem length_emitRange_le {rs : List (ℤ × ℤ)} (h : rs.length ≤ tubeRanges) (iLo iHi : ℤ) :
    (emitRange rs iLo iHi).length ≤ tubeRanges := by
  have := tubeRanges_pos
  simp only [emitRange]
  split_ifs with h1 h2 h3
  · simp only [List.length_append, List.length_dropLast, List.length_singleton]; lia
  · exact h
  · simp only [List.length_singleton]; lia
  · simp only [List.length_append, List.length_singleton]; lia

namespace TubeBands.Sized

variable {bd : TubeBands} {n : ℕ} (h : bd.Sized n) {b : ℤ} (hb : bd.bandB0 ≤ b)
  (hbn : b < bd.bandB0 + n)
include h hb hbn

theorem rowRanges_tubeEmit (iLo iHi : ℤ) {r : ℕ} (hr : r < n) :
    (tubeEmit bd b iLo iHi).rowRanges r =
      if r = (b - bd.bandB0).toNat then emitRange (bd.rowRanges r) iLo iHi else bd.rowRanges r := by
  have hrow : (b - bd.bandB0).toNat < n := by lia
  split_ifs with he
  · subst he
    exact rowRanges_tubeEmit_self h.size_bandRg (by lia [h.le_tubeBand])
      (by lia [h.size_bandNr, h.le_tubeBand]) (h.bandNr_le hrow)
  · exact rowRanges_tubeEmit_of_ne he (h.bandNr_le hr) (h.bandNr_le hrow)

theorem tubeEmit (iLo iHi : ℤ) : (JPoints.tubeEmit bd b iLo iHi).Sized n := by
  obtain ⟨h1, h2⟩ := size_tubeEmit bd b iLo iHi
  refine ⟨h1.trans h.size_bandNr, h2.trans h.size_bandRg, h.le_tubeBand, fun {r} hr ↦ ?_⟩
  rw [← TubeBands.length_rowRanges, h.rowRanges_tubeEmit hb hbn iLo iHi hr]
  split_ifs
  · exact length_emitRange_le (by rw [TubeBands.length_rowRanges]; exact h.bandNr_le hr) _ _
  · rw [TubeBands.length_rowRanges]; exact h.bandNr_le hr

end TubeBands.Sized

theorem TubeBands.Sized.emitRows {bd : TubeBands} {n : ℕ} (h : bd.Sized n) {bLo bHi : ℤ}
    (h0 : bd.bandB0 ≤ bLo) (h1 : bHi < bd.bandB0 + n) (iLo iHi : ℤ) :
    (JPoints.emitRows bd bLo bHi iLo iHi).Sized n ∧
      (JPoints.emitRows bd bLo bHi iLo iHi).bandB0 = bd.bandB0 ∧
      ∀ r < n, (JPoints.emitRows bd bLo bHi iLo iHi).rowRanges r =
        if bLo ≤ bd.bandB0 + r ∧ bd.bandB0 + r ≤ bHi then emitRange (bd.rowRanges r) iLo iHi
        else bd.rowRanges r := by
  have key (j : ℕ) (hj : j ≤ (bHi - bLo + 1).toNat) :
      let F := (List.range j).foldl
        (fun bd (k : ℕ) ↦ JPoints.tubeEmit bd (bLo + (k : ℤ)) iLo iHi) bd
      F.Sized n ∧ F.bandB0 = bd.bandB0 ∧ ∀ r < n, F.rowRanges r =
        if bLo ≤ bd.bandB0 + (r : ℤ) ∧ bd.bandB0 + (r : ℤ) < bLo + (j : ℤ) then
          emitRange (bd.rowRanges r) iLo iHi
        else bd.rowRanges r := by
    induction j with
    | zero => exact ⟨h, rfl, fun r _ ↦ by rw [ite_eq_right (by lia)]; rfl⟩
    | succ j ih =>
      obtain ⟨g1, g2, g3⟩ := ih (by lia)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨g1.tubeEmit (by lia) (by lia) iLo iHi, by rw [bandB0_tubeEmit, g2],
        fun r hr ↦ ?_⟩
      rw [g1.rowRanges_tubeEmit (by lia) (by lia) iLo iHi hr, g3 r hr, g2]
      split_ifs <;> first | rfl | lia
  obtain ⟨g1, g2, g3⟩ := key _ le_rfl
  refine ⟨g1, g2, fun r hr ↦ (g3 r hr).trans ?_⟩
  split_ifs <;> first | rfl | lia

theorem bandB0_emitRows (bd : TubeBands) (bLo bHi iLo iHi : ℤ) :
    (emitRows bd bLo bHi iLo iHi).bandB0 = bd.bandB0 := by
  rw [emitRows]
  generalize List.range _ = l
  induction l generalizing bd with
  | nil => rfl
  | cons k l ih => exact (ih _).trans (bandB0_tubeEmit ..)

/-- The ranges `rs` lie in `[L, U)` in increasing order: each nonempty, and each ending before the
next begins. -/
def RangesIn (L U : ℤ) (rs : List (ℤ × ℤ)) : Prop :=
  (∀ r ∈ rs, L ≤ r.1 ∧ r.1 < r.2 ∧ r.2 ≤ U) ∧ rs.Pairwise fun r s ↦ r.2 ≤ s.1

theorem rangesIn_nil (L U : ℤ) : RangesIn L U [] := ⟨fun _ h ↦ absurd h List.not_mem_nil, .nil⟩

theorem RangesIn.mono {L U U' : ℤ} {rs : List (ℤ × ℤ)} (h : RangesIn L U rs) (hU : U ≤ U') :
    RangesIn L U' rs :=
  ⟨fun r hr ↦ ⟨(h.1 r hr).1, (h.1 r hr).2.1, (h.1 r hr).2.2.trans hU⟩, h.2⟩

theorem RangesIn.concat {L x y : ℤ} {rs : List (ℤ × ℤ)} (h : RangesIn L x rs) (hx : L ≤ x)
    (hxy : x < y) : RangesIn L y (rs ++ [(x, y)]) := by
  refine ⟨fun r hr ↦ ?_, List.pairwise_append.mpr ⟨h.2, List.pairwise_singleton _ _,
    fun r hr s hs ↦ ?_⟩⟩
  · rcases List.mem_append.mp hr with hr | hr
    · have := h.1 r hr; exact ⟨this.1, this.2.1, by lia⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨hx, hxy, le_rfl⟩
  · simp only [List.mem_singleton] at hs; subst hs
    exact (h.1 r hr).2.2

theorem rangesIn_singleton {L U : ℤ} (h : L < U) : RangesIn L U [(L, U)] :=
  (rangesIn_nil L L).concat le_rfl h

theorem RangesIn.of_append_singleton {L U : ℤ} {rs : List (ℤ × ℤ)} {x : ℤ × ℤ}
    (h : RangesIn L U (rs ++ [x])) :
    RangesIn L x.1 rs ∧ L ≤ x.1 ∧ x.1 < x.2 ∧ x.2 ≤ U := by
  have h2 := List.pairwise_append.mp h.2
  refine ⟨⟨fun r hr ↦ ?_, h2.1⟩, h.1 x (by simp)⟩
  have := h.1 r (by simp [hr])
  exact ⟨this.1, this.2.1, h2.2.2 r hr x (by simp)⟩

theorem RangesIn.head!_le {L U : ℤ} {rs : List (ℤ × ℤ)} (hr : RangesIn L U rs) {r : ℤ × ℤ}
    (h : r ∈ rs) :
    rs.head!.1 ≤ r.1 := by
  rcases rs with _ | ⟨y, ys⟩
  · exact absurd h List.not_mem_nil
  · rcases List.mem_cons.mp h with rfl | h
    · exact le_rfl
    · have h1 := (hr.1 y List.mem_cons_self).2.1
      have h2 := (List.pairwise_cons.mp hr.2).1 r h
      change y.1 ≤ r.1
      lia

theorem RangesIn.emitRange {L iLo iHi : ℤ} {rs : List (ℤ × ℤ)} (h : RangesIn L iLo rs)
    (hL : L ≤ iLo) (hw : iLo < iHi) : RangesIn L iHi (JPoints.emitRange rs iLo iHi) := by
  rcases List.eq_nil_or_concat rs with rfl | ⟨init, x, rfl⟩
  · simp only [JPoints.emitRange, List.length_nil, Nat.lt_irrefl, false_and, ↓reduceIte]
    rw [ite_eq_right (by have := tubeRanges_pos; lia)]
    exact (rangesIn_nil L iLo).concat hL hw
  · rw [List.concat_eq_append] at h ⊢
    obtain ⟨hi, hx1, hx2, -⟩ := h.of_append_singleton
    have hl : (init ++ [x]).getLast! = x := by simp
    have hm : (init ++ [x]).head! ∈ init ++ [x] := List.head!_mem_self (by simp)
    simp only [JPoints.emitRange, List.length_append, List.length_singleton, hl,
      List.dropLast_concat]
    split_ifs with g1 g2 g3
    · exact hi.concat hx1 (by lia)
    · exact h.mono hw.le
    · have hh := h.1 _ hm
      exact (rangesIn_nil L _).concat hh.1 (by lia)
    · exact h.concat hL hw

theorem TubeBands.Sized.rangesIn_emitRows {bd : TubeBands} {n : ℕ} (h : bd.Sized n)
    {bLo bHi L iLo iHi : ℤ} (h0 : bd.bandB0 ≤ bLo) (h1 : bHi < bd.bandB0 + n) (hL : L ≤ iLo)
    (hw : iLo < iHi)
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L iLo (bd.rowRanges r))
    {r : ℕ} (hrn : r < n) (hr1 : bLo ≤ bd.bandB0 + r) (hr2 : bd.bandB0 + r ≤ bHi) :
    RangesIn L iHi ((JPoints.emitRows bd bLo bHi iLo iHi).rowRanges r) := by
  rw [(h.emitRows h0 h1 iLo iHi).2.2 r hrn, ite_eq_left ⟨hr1, hr2⟩]
  exact (hr r hrn hr1 hr2).emitRange hL hw

/-- What the analysis of a cell of the rows `bLo..bHi` of a band keeps from the bands `bd` to the
bands `bd'`, for the `n` rows of the band: the sizes of the arrays, the ranges of each row of the
cell in increasing order within `[L, U)`, and the ranges of the other rows. -/
def TubeBands.CellRanges (n : ℕ) (L U : ℤ) (bd : TubeBands) (bLo bHi : ℤ) (bd' : TubeBands) :
    Prop :=
  bd'.Sized n ∧
    (∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L U (bd'.rowRanges r)) ∧
    ∀ r < n, ¬(bLo ≤ bd.bandB0 + r ∧ bd.bandB0 + r ≤ bHi) → bd'.rowRanges r = bd.rowRanges r

namespace TubeBands.CellRanges

variable {n : ℕ} {L U : ℤ} {bd bd₁ bd₂ : TubeBands} {bLo bHi : ℤ}

theorem mono (h : CellRanges n L U bd bLo bHi bd₁) {U' : ℤ} (hU : U ≤ U') :
    CellRanges n L U' bd bLo bHi bd₁ :=
  ⟨h.1, fun r hrn hr1 hr2 ↦ (h.2.1 r hrn hr1 hr2).mono hU, h.2.2⟩

theorem trans_words {M : ℤ} (h : CellRanges n L M bd bLo bHi bd₁)
    (hb : bd₁.bandB0 = bd.bandB0)
    (h' : bd₁.Sized n → (∀ r < n, bLo ≤ bd₁.bandB0 + r → bd₁.bandB0 + r ≤ bHi →
      RangesIn L M (bd₁.rowRanges r)) → CellRanges n L U bd₁ bLo bHi bd₂) :
    CellRanges n L U bd bLo bHi bd₂ := by
  obtain ⟨f1, f2, f3⟩ := h' h.1 (hb ▸ h.2.1)
  rw [hb] at f2 f3
  exact ⟨f1, f2, fun r hrn hc ↦ (f3 r hrn hc).trans (h.2.2 r hrn hc)⟩

theorem rangesIn_of_not {m iLo : ℤ} (h : CellRanges n L U bd bLo m bd₁)
    (hb : bd₁.bandB0 = bd.bandB0) (hm : bLo ≤ m + 1)
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L iLo (bd.rowRanges r))
    (r : ℕ) (hrn : r < n) (hr1 : m + 1 ≤ bd₁.bandB0 + r) (hr2 : bd₁.bandB0 + r ≤ bHi) :
    RangesIn L iLo (bd₁.rowRanges r) := by
  rw [hb] at hr1 hr2
  rw [h.2.2 r hrn (by lia)]
  exact hr r hrn (by lia) hr2

theorem trans_rows {m : ℤ} (h : CellRanges n L U bd bLo m bd₁) (hb : bd₁.bandB0 = bd.bandB0)
    (hm : bLo ≤ m + 1) (hm' : m ≤ bHi) (h' : CellRanges n L U bd₁ (m + 1) bHi bd₂) :
    CellRanges n L U bd bLo bHi bd₂ := by
  obtain ⟨f1, f2, f3⟩ := h'
  rw [hb] at f2 f3
  refine ⟨f1, fun r hrn hr1 hr2 ↦ ?_,
    fun r hrn hc ↦ (f3 r hrn (by lia)).trans (h.2.2 r hrn (by lia))⟩
  by_cases hm : bd.bandB0 + r ≤ m
  · rw [f3 r hrn (by lia)]
    exact h.2.1 r hrn hr1 hm
  · exact f2 r hrn (by lia) hr2

end TubeBands.CellRanges

theorem TubeBands.Sized.cellRanges_self {bd : TubeBands} {n : ℕ} (h : bd.Sized n) {L U bLo bHi : ℤ}
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L U (bd.rowRanges r)) :
    CellRanges n L U bd bLo bHi bd :=
  ⟨h, hr, fun _ _ _ ↦ rfl⟩

theorem TubeBands.Sized.cellRanges_emitRows {bd : TubeBands} {n : ℕ} (h : bd.Sized n)
    {bLo bHi L iLo iHi : ℤ} (h0 : bd.bandB0 ≤ bLo) (h1 : bHi < bd.bandB0 + n) (hL : L ≤ iLo)
    (hw : iLo < iHi)
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L iLo (bd.rowRanges r)) :
    CellRanges n L iHi bd bLo bHi (JPoints.emitRows bd bLo bHi iLo iHi) := by
  obtain ⟨g1, -, g3⟩ := h.emitRows h0 h1 iLo iHi
  exact ⟨g1, fun r hrn hr1 hr2 ↦ h.rangesIn_emitRows h0 h1 hL hw hr hrn hr1 hr2,
    fun r hrn hc ↦ by rw [g3 r hrn, ite_eq_right hc]⟩

/-! ### The ranges of a row cut to the real region -/

/-- The ranges of `rs` cut to those of `gs`, as `row_cut` intersects the ranges of a row of a band
with the ranges of the real region of the row (`JPoints.rowCut`): while both last, the
intersection of the first two kept when it is not empty, and the range that ends first left
behind (that of `gs` when both end together). -/
def cutRanges : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | r :: rs, g :: gs =>
    (if (if r.1 > g.1 then r.1 else g.1) < (if r.2 < g.2 then r.2 else g.2) then
      [(if r.1 > g.1 then r.1 else g.1, if r.2 < g.2 then r.2 else g.2)] else []) ++
    if r.2 < g.2 then cutRanges rs (g :: gs) else cutRanges (r :: rs) gs
  | _, _ => []
termination_by rs gs => rs.length + gs.length

theorem cutRanges_nil_left (gs : List (ℤ × ℤ)) : cutRanges [] gs = [] := by
  simp [cutRanges]

theorem cutRanges_nil_right (rs : List (ℤ × ℤ)) : cutRanges rs [] = [] := by
  rcases rs with _ | ⟨r, rs⟩ <;> simp [cutRanges]

private theorem mem_cutHead {r g o : ℤ × ℤ}
    (h : o ∈ if (if r.1 > g.1 then r.1 else g.1) < (if r.2 < g.2 then r.2 else g.2) then
      [(if r.1 > g.1 then r.1 else g.1, if r.2 < g.2 then r.2 else g.2)] else []) :
    o.1 < o.2 ∧ r.1 ≤ o.1 ∧ g.1 ≤ o.1 ∧ o.2 ≤ r.2 ∧ o.2 ≤ g.2 := by
  generalize hlo : (if r.1 > g.1 then r.1 else g.1) = lo at h
  generalize hhi : (if r.2 < g.2 then r.2 else g.2) = hi at h
  have e1 : r.1 ≤ lo ∧ g.1 ≤ lo := by rw [← hlo]; split_ifs <;> lia
  have e2 : hi ≤ r.2 ∧ hi ≤ g.2 := by rw [← hhi]; split_ifs <;> lia
  by_cases h1 : lo < hi
  · rw [ite_eq_left h1, List.mem_singleton] at h
    subst h
    exact ⟨h1, e1.1, e1.2, e2.1, e2.2⟩
  · rw [ite_eq_right h1] at h
    simp at h

theorem mem_cutRanges {rs gs : List (ℤ × ℤ)} {o : ℤ × ℤ} (h : o ∈ cutRanges rs gs) :
    o.1 < o.2 ∧ ∃ r ∈ rs, ∃ g ∈ gs, r.1 ≤ o.1 ∧ g.1 ≤ o.1 ∧ o.2 ≤ r.2 ∧ o.2 ≤ g.2 := by
  induction rs, gs using cutRanges.induct with
  | case1 r rs g gs ih1 ih2 =>
    rw [cutRanges] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_cutHead h
      exact ⟨h1, r, by simp, g, by simp, h2, h3, h4, h5⟩
    · split_ifs at h
      · obtain ⟨ho, r', hr', g', hg', hh⟩ := ih1 h
        exact ⟨ho, r', .tail _ hr', g', hg', hh⟩
      · obtain ⟨ho, r', hr', g', hg', hh⟩ := ih2 h
        exact ⟨ho, r', hr', g', .tail _ hg', hh⟩
  | case2 rs gs hn =>
    rw [cutRanges.eq_2 _ _ hn] at h
    simp at h

private theorem cutHead_le_of_mem {r g a b : ℤ × ℤ} {rs gs : List (ℤ × ℤ)}
    (hr : (r :: rs).Pairwise fun r s ↦ r.2 ≤ s.1) (hg : (g :: gs).Pairwise fun r s ↦ r.2 ≤ s.1)
    (ha : a ∈ if (if r.1 > g.1 then r.1 else g.1) < (if r.2 < g.2 then r.2 else g.2) then
      [(if r.1 > g.1 then r.1 else g.1, if r.2 < g.2 then r.2 else g.2)] else [])
    (hb : b ∈ if r.2 < g.2 then cutRanges rs (g :: gs) else cutRanges (r :: rs) gs) :
    a.2 ≤ b.1 := by
  obtain ⟨-, -, -, h4, h5⟩ := mem_cutHead ha
  split_ifs at hb
  · obtain ⟨-, r', hr', -, -, h1, -⟩ := mem_cutRanges hb
    lia [(List.pairwise_cons.mp hr).1 r' hr']
  · obtain ⟨-, -, -, g', hg', -, h1, -⟩ := mem_cutRanges hb
    lia [(List.pairwise_cons.mp hg).1 g' hg']

theorem RangesIn.cutRanges {L U : ℤ} {rs gs : List (ℤ × ℤ)} (hr : RangesIn L U rs)
    (hg : RangesIn L U gs) : RangesIn L U (JPoints.cutRanges rs gs) := by
  refine ⟨fun o ho ↦ ?_, ?_⟩
  · obtain ⟨h1, r, hr', g, -, h2, -, h3, -⟩ := mem_cutRanges ho
    have := hr.1 r hr'
    exact ⟨by lia, h1, by lia⟩
  induction rs, gs using JPoints.cutRanges.induct with
  | case1 r rs g gs ih1 ih2 =>
    rw [JPoints.cutRanges]
    refine List.pairwise_append.mpr ⟨by split_ifs <;> simp, ?_,
      fun a ha b hb ↦ cutHead_le_of_mem hr.2 hg.2 ha hb⟩
    split_ifs
    · exact ih1 ⟨fun x hx ↦ hr.1 x (.tail _ hx), (List.pairwise_cons.mp hr.2).2⟩ hg
    · exact ih2 hr ⟨fun x hx ↦ hg.1 x (.tail _ hx), (List.pairwise_cons.mp hg.2).2⟩
  | case2 rs gs hn =>
    rw [JPoints.cutRanges.eq_2 _ _ hn]
    exact .nil

-- The intersection of two ranges that both hold the word `w`, as `JPoints.cutRanges` keeps it.
private theorem exists_mem_cutHead {r g : ℤ × ℤ} {w : ℤ} (hr : r.1 ≤ w ∧ w < r.2)
    (hg : g.1 ≤ w ∧ w < g.2) :
    ∃ o ∈ (if (if r.1 > g.1 then r.1 else g.1) < (if r.2 < g.2 then r.2 else g.2) then
      [(if r.1 > g.1 then r.1 else g.1, if r.2 < g.2 then r.2 else g.2)] else []),
      o.1 ≤ w ∧ w < o.2 := by
  rw [ite_eq_left (by split_ifs <;> lia)]
  exact ⟨_, List.mem_singleton_self _, by dsimp only; split_ifs <;> lia,
    by dsimp only; split_ifs <;> lia⟩

-- A range of `r :: rs` that holds the word `w` lies in `rs` when `w` does not lie in both `r` and
-- `g`, a range of `g :: gs` holds `w`, `r` ends by the end of `g`, and `rs` and `gs` begin after
-- the ends of `r` and `g`.
private theorem mem_of_mem_cons_of_le {r g r' g' : ℤ × ℤ} {rs gs : List (ℤ × ℤ)} {w : ℤ}
    (hr : ∀ s ∈ rs, r.2 ≤ s.1) (hg : ∀ s ∈ gs, g.2 ≤ s.1) (hle : r.2 ≤ g.2) (hr' : r' ∈ r :: rs)
    (hg' : g' ∈ g :: gs) (hw : r'.1 ≤ w ∧ w < r'.2) (hw' : g'.1 ≤ w ∧ w < g'.2)
    (hh : ¬((r.1 ≤ w ∧ w < r.2) ∧ g.1 ≤ w ∧ w < g.2)) : r' ∈ rs := by
  rcases List.mem_cons.mp hr' with rfl | hr'
  · rcases List.mem_cons.mp hg' with rfl | hg'
    · exact absurd ⟨hw, hw'⟩ hh
    · lia [hg g' hg']
  · exact hr'

/-- A word in a range of `rs` and in a range of `gs` lies in a range of the cut of `rs` to `gs`
(`JPoints.cutRanges`), the ranges of each in increasing order: the cut keeps the intersection of
the two ranges that it compares, and it leaves a range behind only when the next ranges of the
other list begin after its end. -/
theorem exists_mem_cutRanges {rs gs : List (ℤ × ℤ)} (hr : rs.Pairwise fun r s ↦ r.2 ≤ s.1)
    (hg : gs.Pairwise fun r s ↦ r.2 ≤ s.1) {w : ℤ} (hw : ∃ r ∈ rs, r.1 ≤ w ∧ w < r.2)
    (hw' : ∃ g ∈ gs, g.1 ≤ w ∧ w < g.2) : ∃ o ∈ cutRanges rs gs, o.1 ≤ w ∧ w < o.2 := by
  induction rs, gs using cutRanges.induct with
  | case1 r rs g gs ih1 ih2 =>
    obtain ⟨⟨r', hr', hw⟩, g', hg', hw'⟩ := And.intro hw hw'
    rw [List.pairwise_cons] at hr hg
    rw [cutRanges]
    by_cases hh : (r.1 ≤ w ∧ w < r.2) ∧ g.1 ≤ w ∧ w < g.2
    · obtain ⟨o, ho, h⟩ := exists_mem_cutHead hh.1 hh.2
      exact ⟨o, List.mem_append_left _ ho, h⟩
    by_cases hlt : r.2 < g.2
    · obtain ⟨o, ho, h⟩ := ih1 hr.2 (List.pairwise_cons.mpr hg)
        ⟨r', mem_of_mem_cons_of_le hr.1 hg.1 hlt.le hr' hg' hw hw' hh, hw⟩ ⟨g', hg', hw'⟩
      exact ⟨o, List.mem_append_right _ (by rwa [ite_eq_left hlt]), h⟩
    · obtain ⟨o, ho, h⟩ := ih2 (List.pairwise_cons.mpr hr) hg.2 ⟨r', hr', hw⟩
        ⟨g', mem_of_mem_cons_of_le hg.1 hr.1 (by lia) hg' hr' hw' hw (by tauto), hw'⟩
      exact ⟨o, List.mem_append_right _ (by rwa [ite_eq_right hlt]), h⟩
  | case2 rs gs hn =>
    obtain ⟨⟨r, hr, -⟩, g, hg, -⟩ := And.intro hw hw'
    exact (hn _ _ _ _ (List.cons_head_tail (List.ne_nil_of_mem hr)).symm
      (List.cons_head_tail (List.ne_nil_of_mem hg)).symm).elim

/-- The ranges `[lo[k], hi[k])`, `k < n`, of the triple `r = (n, lo, hi)` that `row_region`,
`row_cut` and the bands give a row. -/
def rangeList (r : ℕ × Array ℤ × Array ℤ) : List (ℤ × ℤ) :=
  (List.range r.1).map fun k ↦ (r.2.1[k]!, r.2.2[k]!)

/-- The invariant of the loop of `JPoints.rowCut`. -/
def RowCutInvariant (bd : TubeBands) (row nreg : ℕ) (reglo reghi : Array ℤ) :
    Std.WP.WhileInvariant (ℕ × ℕ × ℕ × Array ℤ × Array ℤ) Prop :=
  .mk fun exit st ↦ ∃ P, cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi)) =
      P ++ cutRanges ((bd.rowRanges row).drop st.1) ((rangeList (nreg, reglo, reghi)).drop st.2.1) ∧
    st.2.2.1 = P.length ∧ st.2.2.2.1 = (P.map Prod.fst).toArray ∧
    st.2.2.2.2 = (P.map Prod.snd).toArray ∧ st.1 ≤ bd.bandNr[row]! ∧ st.2.1 ≤ nreg ∧
    (exit = true → ¬(st.1 < bd.bandNr[row]! ∧ st.2.1 < nreg))

section RowCut

variable {bd : TubeBands} {row nreg : ℕ} {reglo reghi : Array ℤ} {i j n mb : ℕ} {lo hi : Array ℤ}

theorem length_rangeList (n : ℕ) (lo hi : Array ℤ) : (rangeList (n, lo, hi)).length = n := by
  simp [rangeList]

theorem rangeList_push {n : ℕ} {lo hi : Array ℤ} (h1 : lo.size = n) (h2 : hi.size = n) (x y : ℤ) :
    rangeList (n + 1, lo.push x, hi.push y) = rangeList (n, lo, hi) ++ [(x, y)] := by
  simp only [rangeList, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left fun k hk ↦ ?_
    have hk := List.mem_range.mp hk
    rw [Array.getElem!_push_lt (by lia), Array.getElem!_push_lt (by lia)]
  · rw [show n = lo.size from h1.symm, Array.getElem!_push_eq, show lo.size = hi.size by
      rw [h1, h2], Array.getElem!_push_eq]

theorem rangeList_ofList (rs : List (ℤ × ℤ)) :
    rangeList (rs.length, (rs.map Prod.fst).toArray, (rs.map Prod.snd).toArray) = rs := by
  refine List.ext_getElem (by simp [rangeList]) fun k h1 h2 ↦ ?_
  simp only [rangeList, List.getElem_map, List.getElem_range] at h1 ⊢
  simp [h2]

theorem rangeList_take_succ {n k : ℕ} {lo hi : Array ℤ} (h : k < n) :
    (rangeList (n, lo, hi)).take (k + 1) =
      (rangeList (n, lo, hi)).take k ++ [(lo[k]!, hi[k]!)] := by
  simp only [rangeList, ← List.map_take, List.take_range, Nat.min_eq_left h, Nat.min_eq_left h.le,
    List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem rowCut_cut_step (hi : i < bd.bandNr[row]!) (hj : j < nreg) :
    cutRanges ((bd.rowRanges row).drop i) ((rangeList (nreg, reglo, reghi)).drop j) =
      (if (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
          (if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) then
        [(if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!,
          if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!)] else []) ++
      if bd.bhi row i < reghi[j]! then
        cutRanges ((bd.rowRanges row).drop (i + 1)) ((rangeList (nreg, reglo, reghi)).drop j)
      else
        cutRanges ((bd.rowRanges row).drop i) ((rangeList (nreg, reglo, reghi)).drop (j + 1)) := by
  have hi' : i < (bd.rowRanges row).length := by rw [TubeBands.length_rowRanges]; exact hi
  have hj' : j < (rangeList (nreg, reglo, reghi)).length := by rw [length_rangeList]; exact hj
  conv_lhs => rw [List.drop_eq_getElem_cons hi', List.drop_eq_getElem_cons hj', cutRanges]
  rw [← List.drop_eq_getElem_cons hi', ← List.drop_eq_getElem_cons hj']
  simp [TubeBands.rowRanges, rangeList]

theorem rowCutInvariant_init :
    RowCutInvariant bd row nreg reglo reghi false (0, 0, 0, #[], #[]) :=
  ⟨[], by simp, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _, fun h ↦ absurd h Bool.false_ne_true⟩

theorem rowCutInvariant_post (h : RowCutInvariant bd row nreg reglo reghi true (i, j, n, lo, hi)) :
    (n, lo, hi) = ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).length,
      ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).map Prod.fst).toArray,
      ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).map Prod.snd).toArray) := by
  obtain ⟨P, hP, hn, hlo, hhi, hi, hj, hx⟩ := h
  dsimp only at hP hn hlo hhi hi hj hx
  have h0 :
      cutRanges ((bd.rowRanges row).drop i) ((rangeList (nreg, reglo, reghi)).drop j) = [] := by
    rcases Nat.lt_or_ge i bd.bandNr[row]! with h1 | h1
    · rw [List.drop_eq_nil_of_le (as := rangeList (nreg, reglo, reghi))
        (by rw [length_rangeList]; lia [hx rfl]), cutRanges_nil_right]
    · rw [List.drop_eq_nil_of_le (as := bd.rowRanges row) (by rw [TubeBands.length_rowRanges]; lia),
        cutRanges_nil_left]
  rw [h0, List.append_nil] at hP
  rw [hP, hn, hlo, hhi]

theorem rowCutInvariant_exit (hc : ¬(decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (h : bd.bandNr[row]! - i + (nreg - j) = mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi)) :
    RowCutInvariant bd row nreg reglo reghi true (i, j, n, lo, hi) := by
  obtain ⟨P, hP, hn, hlo, hhi, hi, hj, -⟩ := h.2
  exact ⟨P, hP, hn, hlo, hhi, hi, hj, fun _ ↦ by simpa using hc⟩

theorem rowCutInvariant_next (hc : (decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (h : RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi)) {i' j' : ℕ}
    (hij : (i', j') = if bd.bhi row i < reghi[j]! then (i + 1, j) else (i, j + 1))
    {Q : List (ℤ × ℤ)}
    (hQ : Q = if (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
        (if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) then
        [(if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!,
          if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!)] else []) :
    RowCutInvariant bd row nreg reglo reghi false
      (i', j', n + Q.length, lo ++ (Q.map Prod.fst).toArray, hi ++ (Q.map Prod.snd).toArray) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨P, hP, hn, hlo, hhi, -, -, -⟩ := h
  dsimp only at hP hn hlo hhi
  rw [rowCut_cut_step hc.1 hc.2, ← hQ] at hP
  refine ⟨P ++ Q, ?_, by simp [hn], by simp [hlo], by simp [hhi], ?_⟩ <;>
    by_cases hb : bd.bhi row i < reghi[j]!
  · rw [ite_eq_left hb] at hP hij
    rw [Prod.mk.injEq] at hij
    rw [hP, List.append_assoc, hij.1, hij.2]
  · rw [ite_eq_right hb] at hP hij
    rw [Prod.mk.injEq] at hij
    rw [hP, List.append_assoc, hij.1, hij.2]
  · rw [ite_eq_left hb, Prod.mk.injEq] at hij
    rw [hij.1, hij.2]
    exact ⟨by lia, by lia, fun h ↦ absurd h Bool.false_ne_true⟩
  · rw [ite_eq_right hb, Prod.mk.injEq] at hij
    rw [hij.1, hij.2]
    exact ⟨by lia, by lia, fun h ↦ absurd h Bool.false_ne_true⟩

theorem rowCutInvariant_push_left
    (hc : (decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (hb : bd.bhi row i < reghi[j]!)
    (h : bd.bandNr[row]! - i + (nreg - j) = mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi))
    (hlt : (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
      if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) :
    bd.bandNr[row]! - (i + 1) + (nreg - j) < mb ∧ RowCutInvariant bd row nreg reglo reghi false
      (i + 1, j, n + 1, lo.push (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!),
        hi.push (if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!)) := by
  have := rowCutInvariant_next hc h.2 (ite_eq_left hb).symm (ite_eq_left hlt).symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨by lia, by simpa using this⟩

theorem rowCutInvariant_push_right
    (hc : (decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (hb : ¬bd.bhi row i < reghi[j]!)
    (h : bd.bandNr[row]! - i + (nreg - j) = mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi))
    (hlt : (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
      if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) :
    bd.bandNr[row]! - i + (nreg - (j + 1)) < mb ∧ RowCutInvariant bd row nreg reglo reghi false
      (i, j + 1, n + 1, lo.push (if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!),
        hi.push (if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!)) := by
  have := rowCutInvariant_next hc h.2 (ite_eq_right hb).symm (ite_eq_left hlt).symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨by lia, by simpa using this⟩

theorem rowCutInvariant_skip_left
    (hc : (decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (hb : bd.bhi row i < reghi[j]!)
    (h : bd.bandNr[row]! - i + (nreg - j) = mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi))
    (hlt : ¬(if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
      if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) :
    bd.bandNr[row]! - (i + 1) + (nreg - j) < mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i + 1, j, n, lo, hi) := by
  have := rowCutInvariant_next hc h.2 (ite_eq_left hb).symm (ite_eq_right hlt).symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨by lia, by simpa using this⟩

theorem rowCutInvariant_skip_right
    (hc : (decide (i < bd.bandNr[row]!) && decide (j < nreg)) = true)
    (hb : ¬bd.bhi row i < reghi[j]!)
    (h : bd.bandNr[row]! - i + (nreg - j) = mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j, n, lo, hi))
    (hlt : ¬(if reglo[j]! < bd.blo row i then bd.blo row i else reglo[j]!) <
      if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!) :
    bd.bandNr[row]! - i + (nreg - (j + 1)) < mb ∧
      RowCutInvariant bd row nreg reglo reghi false (i, j + 1, n, lo, hi) := by
  have := rowCutInvariant_next hc h.2 (ite_eq_right hb).symm (ite_eq_right hlt).symm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨by lia, by simpa using this⟩

end RowCut

theorem rowCut_spec (bd : TubeBands) (row nreg : ℕ) (reglo reghi : Array ℤ) :
    ⦃ True ⦄ rowCut bd row nreg reglo reghi
    ⦃ fun r ↦ r = ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).length,
        ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).map Prod.fst).toArray,
        ((cutRanges (bd.rowRanges row) (rangeList (nreg, reglo, reghi))).map Prod.snd).toArray)
    ⦄ := by
  vcgen [rowCut] invariants
  · RowCutInvariant bd row nreg reglo reghi
  · Std.WP.Variant.ofMeasure fun st : ℕ × ℕ × ℕ × Array ℤ × Array ℤ ↦
      bd.bandNr[row]! - st.1 + (nreg - st.2.1)
  all_goals try vc_simp
  all_goals first
    | exact rowCutInvariant_init
    | exact rowCutInvariant_post ‹_›
    | exact rowCutInvariant_exit ‹_› ‹_›
    | exact rowCutInvariant_push_left ‹_› ‹_› ‹_› ‹_›
    | exact rowCutInvariant_push_right ‹_› ‹_› ‹_› ‹_›
    | exact rowCutInvariant_skip_left ‹_› ‹_› ‹_› ‹_›
    | exact rowCutInvariant_skip_right ‹_› ‹_› ‹_› ‹_›

end JPoints

end
