/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.TubeCell

import JPoints.Mathlib.Algebra.Order.Ring.Rat
import JPoints.Proof.CellSizes
import JPoints.Proof.Constants
import JPoints.Proof.Order
import JPoints.Proof.Reference

/-!
# The words that the analysis of the tube collects

The analysis of a band of rows (`tube_cell` on the cell of the band and of all the words of a row)
collects, in the row of each `b`, the word `⌊c / 64⌋` of every triple `(a, b, c)` of the band whose
Kummer quadratic has a root in `[-W, W]` (`JPoints.TubeRoot`), and keeps the words that the rows
covered before (`JPoints.TubeSetup.cellCovers_run_tubeCell`): a cell that it finds out holds no
such triple (`JPoints.TubeSetup.not_tubeRoot_of_tubeCellDecide`), and every other cell is collected
whole, halved, or collected as a leaf of one word, by `tube_emit`, which keeps the words that the
ranges of a row in increasing order cover (`JPoints.covers_emitRange`). A point over a triple with a
bounded fourth coordinate gives such a root (`JPoints.CheckGlobals.WF.tubeRoot_of_points_ne_nil`),
and the set-up of the sieve the setting of the analysis (`JPoints.IsSieveSetup.tubeSetup`).

## Main definitions

* `JPoints.Covers`: ranges of words that cover a word.
* `JPoints.TubeRoot`: a root of the Kummer quadratic within the bound on the fourth coordinate.
* `JPoints.CellCovers`: what the analysis of a cell does to the words that the rows cover.

## Main statements

* `JPoints.TubeSetup.cellCovers_run_tubeCell`: the analysis of a cell.
* `JPoints.covers_emitRange`, `JPoints.TubeBands.Sized.covers_emitRows`: `tube_emit`.
* `JPoints.CheckGlobals.WF.tubeRoot_of_points_ne_nil`, `JPoints.IsSieveSetup.tubeSetup`: the points
  and the set-up.
-/

@[expose] public section

namespace JPoints

open Double

/-! ### The words that ranges cover -/

/-- The ranges `rs` of words cover the word `w`: it lies in one of them. -/
def Covers (rs : List (ℤ × ℤ)) (w : ℤ) : Prop := ∃ r ∈ rs, r.1 ≤ w ∧ w < r.2

variable {rs : List (ℤ × ℤ)} {L iLo iHi w : ℤ}

theorem RangesIn.head!_le {U : ℤ} (hr : RangesIn L U rs) {r : ℤ × ℤ} (h : r ∈ rs) :
    rs.head!.1 ≤ r.1 := by
  rcases rs with _ | ⟨y, ys⟩
  · exact absurd h List.not_mem_nil
  · rcases List.mem_cons.mp h with rfl | h
    · exact le_rfl
    · have h1 := (hr.1 y List.mem_cons_self).2.1
      have h2 := (List.pairwise_cons.mp hr.2).1 r h
      change y.1 ≤ r.1
      lia

-- `tube_emit` of `[iLo, iHi)` on ranges with a last range `x`: it keeps their words and covers
-- `[iLo, iHi)`.
private theorem covers_emitRange_append {init : List (ℤ × ℤ)} {x : ℤ × ℤ}
    (hr : RangesIn L iLo (init ++ [x])) (hw : iLo < iHi) :
    (Covers (init ++ [x]) w → Covers (emitRange (init ++ [x]) iLo iHi) w) ∧
      (iLo ≤ w → w < iHi → Covers (emitRange (init ++ [x]) iLo iHi) w) := by
  obtain ⟨-, -, hx2, hx3⟩ := hr.of_append_singleton
  have hl : (init ++ [x]).getLast! = x := by simp
  have hm : (init ++ [x]).head! ∈ init ++ [x] := by
    rcases init with _ | ⟨y, ys⟩
    · exact List.mem_singleton.mpr rfl
    · exact List.mem_cons_self ..
  simp only [emitRange, List.length_append, List.length_singleton, hl, List.dropLast_concat]
  split_ifs with g1 g2 g3
  · refine ⟨fun ⟨r, hr', h1, h2⟩ ↦ ?_, fun h1 h2 ↦ ⟨(x.1, iHi), by simp, by lia, h2⟩⟩
    rcases List.mem_append.mp hr' with h | h
    · exact ⟨r, List.mem_append_left _ h, h1, h2⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨(r.1, iHi), by simp, h1, by lia⟩
  · lia
  · refine ⟨fun ⟨r, hr', h1, h2⟩ ↦ ⟨((init ++ [x]).head!.1, iHi), by simp,
      (hr.head!_le hr').trans h1, by linarith [(hr.1 r hr').2.2]⟩,
      fun h1 h2 ↦ ⟨((init ++ [x]).head!.1, iHi), by simp, by lia [hr.1 _ hm], h2⟩⟩
  · exact ⟨fun ⟨r, hr', h1, h2⟩ ↦ ⟨r, List.mem_append_left _ hr', h1, h2⟩,
      fun h1 h2 ↦ ⟨(iLo, iHi), by simp, h1, h2⟩⟩

/-- `tube_emit` of the words `[iLo, iHi)` keeps the words that the ranges of a row in increasing
order within `[L, iLo)` cover, and covers the words `[iLo, iHi)`: it merges them into the last
range, takes the hull of the row from its first range, or adds a range. -/
theorem covers_emitRange (hr : RangesIn L iLo rs) (hw : iLo < iHi) :
    (Covers rs w → Covers (emitRange rs iLo iHi) w) ∧
      (iLo ≤ w → w < iHi → Covers (emitRange rs iLo iHi) w) := by
  rcases List.eq_nil_or_concat rs with rfl | ⟨init, x, rfl⟩
  · simp only [emitRange, List.length_nil, Nat.lt_irrefl, false_and, ↓reduceIte]
    rw [ite_eq_right (by have := tubeRanges_pos; lia)]
    exact ⟨fun ⟨r, hr, _⟩ ↦ absurd hr List.not_mem_nil,
      fun h1 h2 ↦ ⟨(iLo, iHi), by simp, h1, h2⟩⟩
  · rw [List.concat_eq_append] at hr ⊢
    exact covers_emitRange_append hr hw

/-- `tube_emit` of the words `[iLo, iHi)` for the rows `bLo..bHi` of a band keeps the words that
the ranges of each row of the band cover, the ranges of the rows of the cell in increasing order
within `[L, iLo)`, and covers the words `[iLo, iHi)` in the rows of the cell. -/
theorem TubeBands.Sized.covers_emitRows {bd : TubeBands} {n : ℕ} (h : bd.Sized n) {bLo bHi : ℤ}
    (h0 : bd.bandB0 ≤ bLo) (h1 : bHi < bd.bandB0 + n) (hw : iLo < iHi)
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L iLo (bd.rowRanges r)) :
    (∀ r < n, ∀ w, Covers (bd.rowRanges r) w →
        Covers ((JPoints.emitRows bd bLo bHi iLo iHi).rowRanges r) w) ∧
      ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → ∀ w, iLo ≤ w → w < iHi →
        Covers ((JPoints.emitRows bd bLo bHi iLo iHi).rowRanges r) w := by
  obtain ⟨-, -, g3⟩ := h.emitRows h0 h1 iLo iHi
  refine ⟨fun r hrn w hc ↦ ?_, fun r hrn hr1 hr2 w hw1 hw2 ↦ ?_⟩
  · rw [g3 r hrn]
    split_ifs with hc'
    · exact (covers_emitRange (hr r hrn hc'.1 hc'.2) hw).1 hc
    · exact hc
  · rw [g3 r hrn, ite_eq_left ⟨hr1, hr2⟩]
    exact (covers_emitRange (hr r hrn hr1 hr2) hw).2 hw1 hw2

/-! ### The analysis of a cell -/

/-- The Kummer quadratic over `(a, b, c)` of the curve with the coefficients `f` has a rational
root `x` with `|x| ≤ W`: the fourth coordinate of a point over the triple bounded by `W`, which the
analysis of the tube must not rule out. -/
def TubeRoot (f : ℕ → ℤ) (W a b c : ℤ) : Prop :=
  ∃ x : ℚ, |x| ≤ W ∧ (kummerK2 a b c : ℚ) * (x * x) + kummerK1 f a b c * x + kummerK0 f a b c = 0

/-- What the analysis of the cell of the rows `bLo..bHi` and the words `[iLo, iHi)` does from the
bands `bd` to the bands `bd'` of a band of `n` rows: each row keeps the words that it covered, and
the row of `b` covers the word `⌊c / 64⌋` of each triple `(a, b, c)` of the cell whose Kummer
quadratic has a root in `[-W, W]` (`JPoints.TubeRoot`). -/
def CellCovers (f : ℕ → ℤ) (W a : ℤ) (n : ℕ) (bd bd' : TubeBands) (bLo bHi iLo iHi : ℤ) : Prop :=
  (∀ r < n, ∀ w, Covers (bd.rowRanges r) w → Covers (bd'.rowRanges r) w) ∧
    ∀ b c : ℤ, bLo ≤ b → b ≤ bHi → iLo ≤ c >>> longShift → c >>> longShift < iHi →
      TubeRoot f W a b c → Covers (bd'.rowRanges (b - bd.bandB0).toNat) (c >>> longShift)

namespace CellCovers

variable {f : ℕ → ℤ} {W a : ℤ} {n : ℕ} {bd bd₁ bd₂ : TubeBands} {bLo bHi : ℤ}

theorem trans_words {m : ℤ} (h : CellCovers f W a n bd bd₁ bLo bHi iLo m)
    (h' : CellCovers f W a n bd₁ bd₂ bLo bHi m iHi) (hb : bd₁.bandB0 = bd.bandB0)
    (hrow : ∀ b ≥ bLo, b ≤ bHi → (b - bd.bandB0).toNat < n) :
    CellCovers f W a n bd bd₂ bLo bHi iLo iHi := by
  refine ⟨fun r hrn w hc ↦ h'.1 r hrn w (h.1 r hrn w hc), fun b c hb1 hb2 hc1 hc2 hroot ↦ ?_⟩
  by_cases hm : c >>> longShift < m
  · exact h'.1 _ (hrow b hb1 hb2) _ (h.2 b c hb1 hb2 hc1 hm hroot)
  · exact hb ▸ h'.2 b c hb1 hb2 (by lia) hc2 hroot

theorem trans_rows {m : ℤ} (h : CellCovers f W a n bd bd₁ bLo m iLo iHi)
    (h' : CellCovers f W a n bd₁ bd₂ (m + 1) bHi iLo iHi) (hb : bd₁.bandB0 = bd.bandB0)
    (hrow : ∀ b ≥ bLo, b ≤ bHi → (b - bd.bandB0).toNat < n) :
    CellCovers f W a n bd bd₂ bLo bHi iLo iHi := by
  refine ⟨fun r hrn w hc ↦ h'.1 r hrn w (h.1 r hrn w hc), fun b c hb1 hb2 hc1 hc2 hroot ↦ ?_⟩
  by_cases hbm : b ≤ m
  · exact h'.1 _ (hrow b hb1 hb2) _ (h.2 b c hb1 hbm hc1 hc2 hroot)
  · exact hb ▸ h'.2 b c (by lia) hb2 hc1 hc2 hroot

end CellCovers

/-- `tube_emit` of the words `[iLo, iHi')` with `iHi ≤ iHi'` for the rows of a cell of a band covers
the words of the cell. -/
theorem TubeBands.Sized.cellCovers_emitRows {bd : TubeBands} {n : ℕ} (h : bd.Sized n)
    {bLo bHi iHi' : ℤ} (h0 : bd.bandB0 ≤ bLo) (h1 : bHi < bd.bandB0 + n) (hw : iLo < iHi')
    (hH : iHi ≤ iHi')
    (hr : ∀ r < n, bLo ≤ bd.bandB0 + r → bd.bandB0 + r ≤ bHi → RangesIn L iLo (bd.rowRanges r))
    (f : ℕ → ℤ) (W a : ℤ) :
    CellCovers f W a n bd (JPoints.emitRows bd bLo bHi iLo iHi') bLo bHi iLo iHi := by
  obtain ⟨e1, e2⟩ := h.covers_emitRows h0 h1 hw hr
  exact ⟨e1, fun b c hb1 hb2 hc1 hc2 _ ↦ e2 _ (by lia) (by lia) (by lia) _ hc1 (by lia)⟩

namespace TubeCell

variable {H bLo bHi iLo iHi : ℤ} (h : TubeCell H bLo bHi iLo iHi)
include h

theorem left_words (hw : 1 < iHi - iLo) : TubeCell H bLo bHi iLo (iLo + (iHi - iLo) / 2) :=
  ⟨h.neg_le, h.le, h.le_H, h.wLow_le, by lia, by lia [h.le_wHigh]⟩

theorem right_words (hw : 1 < iHi - iLo) : TubeCell H bLo bHi (iLo + (iHi - iLo) / 2) iHi :=
  ⟨h.neg_le, h.le, h.le_H, by lia [h.wLow_le], by lia, h.le_wHigh⟩

theorem lower_rows : TubeCell H bLo (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi :=
  ⟨h.neg_le, by lia [h.le], by lia [h.le, h.le_H], h.wLow_le, h.lt, h.le_wHigh⟩

theorem upper_rows (hr : 1 < bHi - bLo + 1) :
    TubeCell H (bLo + (bHi - bLo + 1 - 1) / 2 + 1) bHi iLo iHi :=
  ⟨by lia [h.neg_le, h.le], by lia, h.le_H, h.wLow_le, h.lt, h.le_wHigh⟩

end TubeCell

namespace TubeSetup

variable {kd : TubeCoeffs} {curve : SearchCurve} {H W : ℤ} {th th2 : Double} {a : ℤ}
  (hS : TubeSetup kd curve H W th th2 a)
include hS

/-- A cell of the analysis of the tube that `tube_cell` finds out holds no triple `(a, b, c)` of
its rows and words whose Kummer quadratic has a root in `[-W, W]`. -/
theorem not_tubeRoot_of_tubeCellDecide {t : TubeState} (ht : t.WF) (h0 : t.k0 = tubeK0 kd a)
    (h1 : t.k1 = tubeK1 kd a) (h2 : t.k2 = tubeK2 kd a) (hka : t.ka = tubeKA kd th th2 a)
    {bLo bHi iLo iHi : ℤ} (hcell : TubeCell H bLo bHi iLo iHi)
    (hout : (tubeCellDecide th th2 t bLo bHi iLo iHi).run.2.1 = true) {b c : ℤ}
    (hb : bLo ≤ b ∧ b ≤ bHi) (hc : iLo ≤ c >>> longShift ∧ c >>> longShift < iHi) :
    ¬ TubeRoot (curve.coeffs.toList.getD · 0) W a b c := by
  intro ⟨x, hx, hq⟩
  rw [run_tubeCellDecide, ht.run_tubeCellProducts (signBit_half_mul_ofInt (by lia [hcell.le]))
    (isZero_cellHalfWidth _), run_tubeCellAnalyze] at hout
  simp only [Int.shiftRight_eq_div_pow, longShift] at hc
  have hb1 : (bLo : ℚ) ≤ b := mod_cast hb.1
  have hb2 : (b : ℚ) ≤ bHi := mod_cast hb.2
  have hc1 : (64 * iLo : ℚ) ≤ c := mod_cast (by lia)
  have hc2 : (c : ℚ) ≤ 64 * iHi - 1 := mod_cast (by lia)
  refine hS.not_root_of_tubeCellAnalyzeGen (hcell.cellCentre hS.H_le) h0 h1 h2 hka hout
    (abs_le.mpr ⟨?_, ?_⟩) (abs_le.mpr ⟨?_, ?_⟩) hx hq <;> push_cast <;> linarith

theorem polys_of_eqPolys {t : TubeState} (hp : (tubeAInit kd H th th2 .initial a).run.EqPolys t) :
    t.k0 = tubeK0 kd a ∧ t.k1 = tubeK1 kd a ∧ t.k2 = tubeK2 kd a ∧ t.ka = tubeKA kd th th2 a ∧
      t.tubeOk = true := by
  have e := run_tubeAInit kd H th th2 (t := .initial) ⟨TubeState.wf_initial.size_k0,
    TubeState.wf_initial.size_k1, TubeState.wf_initial.size_k2, TubeState.wf_initial.size_ka⟩ a
  rw [TubeState.EqPolys, e] at hp
  dsimp only at hp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  rw [hS.tubeOk] at h4
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The analysis of a cell of the rows `bLo..bHi` of a band and the words `[iLo, iHi)`, from a
consistent state with the polynomials of `a` and the ranges of the rows of the cell in increasing
order within `[L, iLo)`, keeps the words that the rows of the band cover and covers the word of
every triple of the cell whose Kummer quadratic has a root in `[-W, W]`
(`JPoints.CellCovers`): a cell that it finds out holds no such triple
(`JPoints.TubeSetup.not_tubeRoot_of_tubeCellDecide`), and every other cell or leaf is collected
whole (`JPoints.TubeBands.Sized.cellCovers_emitRows`) or halved
(`JPoints.CellCovers.trans_words`, `JPoints.CellCovers.trans_rows`). -/
-- lint: allow long-proof: the functional induction of `tube_cell`, a few lines per branch
theorem cellCovers_run_tubeCell {n : ℕ} {L : ℤ} (t : TubeState) (bLo bHi iLo iHi : ℤ)
    (ht : t.WF) (hp : (tubeAInit kd H th th2 .initial a).run.EqPolys t)
    (hcell : TubeCell H bLo bHi iLo iHi) (hs : t.bands.Sized n) (h0 : t.bands.bandB0 ≤ bLo)
    (h1 : bHi < t.bands.bandB0 + n) (hL : L ≤ iLo)
    (hr : ∀ r < n, bLo ≤ t.bands.bandB0 + r → t.bands.bandB0 + r ≤ bHi →
      RangesIn L iLo (t.bands.rowRanges r)) :
    CellCovers (curve.coeffs.toList.getD · 0) W a n t.bands
      (tubeCell th th2 t bLo bHi iLo iHi).run.bands bLo bHi iLo iHi := by
  induction t, bLo, bHi, iLo, iHi using tubeCell.induct with
  | case1 t bLo bHi iLo iHi _ hok =>
    exact absurd (hS.polys_of_eqPolys hp).2.2.2.2 (by simpa using hok)
  | case2 t bLo bHi iLo iHi rows words _ hok ih1 ih2 ih3 ih4 =>
    simp only [rows, words] at ih1 ih2 ih3 ih4
    rw [run_tubeCell_of_tubeOk (by simpa using hok)]
    set D := (tubeCellDecide th th2 { t with tubeNcells := t.tubeNcells + 1 } bLo bHi iLo
      iHi).run
    obtain ⟨hDw, hDp⟩ := (ht.with_tubeNcells (t.tubeNcells + 1)).run_tubeCellDecide th th2 bLo bHi
      iLo iHi
    have hpD := TubeState.EqPolys.trans (t' := { t with tubeNcells := t.tubeNcells + 1 }) hp hDp
    have hd : D.2.2.bands.bandB0 = t.bands.bandB0 := rfl
    have hrow (b : ℤ) (hb1 : bLo ≤ b) (hb2 : b ≤ bHi) : (b - t.bands.bandB0).toNat < n := by lia
    have := hcell.le
    simp only [run_tubeEmitRows]
    split_ifs with g1 g2 g3 g4
    · obtain ⟨p0, p1, p2, p3, -⟩ := hS.polys_of_eqPolys hp
      exact ⟨fun r _ w hc ↦ hc, fun b c hb1 hb2 hc1 hc2 hroot ↦ absurd hroot
        (hS.not_tubeRoot_of_tubeCellDecide (ht.with_tubeNcells _) p0 p1 p2 p3 hcell g1
          ⟨hb1, hb2⟩ ⟨hc1, hc2⟩)⟩
    · exact hs.cellCovers_emitRows h0 h1 hcell.lt le_rfl hr _ _ _
    · have hw : 1 < iHi - iLo := by lia
      obtain ⟨w1, p1⟩ := hDw.run_tubeCell (th := th) (th2 := th2) bLo bHi iLo
        (iLo + (iHi - iLo) / 2)
      have cr := TubeBands.Sized.rangesIn_run_tubeCell th th2 D.2.2 bLo bHi iLo
        (iLo + (iHi - iLo) / 2) hs h0 h1 hL (by lia) hr
      have hb := bandB0_run_tubeCell th th2 D.2.2 bLo bHi iLo (iLo + (iHi - iLo) / 2)
      exact (ih1 D.2.2 g3 hDw hpD (hcell.left_words hw) hs h0 h1 hL hr).trans_words
        (ih2 g3 _ w1 (hpD.trans p1) (hcell.right_words hw) cr.1 (hb ▸ h0) (hb ▸ h1) (by lia)
          fun r hrn hr1 hr2 ↦ cr.2.1 r hrn (hb ▸ hr1) (hb ▸ hr2)) hb hrow
    · have hr1 : 1 < bHi - bLo + 1 := by lia [tubeRows_pos]
      obtain ⟨w1, p1⟩ := hDw.run_tubeCell (th := th) (th2 := th2) bLo
        (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi
      have cr := TubeBands.Sized.rangesIn_run_tubeCell th th2 D.2.2 bLo
        (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi hs h0 (by lia) hL hcell.lt fun r hrn hr1 hr2 ↦
          hr r hrn hr1 (by lia)
      have hb := bandB0_run_tubeCell th th2 D.2.2 bLo (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi
      exact (ih3 D.2.2 g4 hDw hpD hcell.lower_rows hs h0 (by lia) hL fun r hrn hr1 hr2 ↦
        hr r hrn hr1 (by lia)).trans_rows (ih4 g4 _ w1 (hpD.trans p1) (hcell.upper_rows hr1) cr.1
          (by rw [hb]; lia) (hb ▸ h1) hL (cr.rangesIn_of_not hb (by lia) hr)) hb hrow
    · have hw : iHi = iLo + 1 := by
        have := hcell.lt
        by_contra hne
        exact g3 ⟨by lia, by nlinarith [tubeRows_pos]⟩
      exact hs.cellCovers_emitRows h0 h1 (show iLo < iLo + 1 by lia) hw.le hr _ _ _

end TubeSetup

/-! ### The points and the set-up -/

/-- A point over a triple with a bounded fourth coordinate gives a root of the Kummer quadratic of
the triple within the bound: its fourth coordinate over the scale of the triple
(`JPoints.kummerPoints`). -/
theorem CheckGlobals.WF.tubeRoot_of_points_ne_nil {gl : CheckGlobals} (hgl : gl.WF)
    (hd : gl.dbounded = true) {a b c : ℤ} (hp : gl.points (a, b, c) ≠ []) :
    TubeRoot (gl.coeffList.getD · 0) gl.dbound a b c := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hp
  obtain ⟨hk, hpt⟩ := List.mem_filter.mp hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
  have hq := quadratic_eq_zero_of_mem_kummerRoots hx
  rw [sq] at hq
  refine ⟨x, (Rat.abs_le_abs_num x).trans ?_, hq⟩
  have hb := (of_decide_eq_true hpt).2.2.2
  have h1 := hgl.one_le_dbound hd
  simp only [InBounds, CheckGlobals.W, hd, ↓reduceIte, Option.mem_def, Option.some.injEq,
    forall_eq', Option.getD_some] at hb
  have : |x.num| ≤ gl.dbound := by split_ifs at hb <;> lia
  exact_mod_cast this

/-- The set-up of the sieve gives the setting of the analysis of the tube for a first coordinate
`|a| ≤ H` whose `tube_ok` holds: the bound on the fourth coordinate is a `long`, at least `1`. -/
theorem IsSieveSetup.tubeSetup {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    (hd : bg.sift.check.dbounded = true) {a : ℤ} (ha : |a| ≤ bg.sift.check.height)
    (hok : (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run.tubeOk = true) :
    TubeSetup bg.kd bg.sift.check.curve bg.sift.check.height bg.sift.check.dbound sd.th sd.th2
      a := by
  have hgl := h.check
  obtain ⟨g, hg, hs⟩ := h
  rw [run_tubeAInit _ _ _ _ ⟨TubeState.wf_initial.size_k0, TubeState.wf_initial.size_k1,
    TubeState.wf_initial.size_k2, TubeState.wf_initial.size_ka⟩] at hok
  refine ⟨?_, hs.siftData.th_eq, hs.siftData.th2_eq, hgl.one_le_dbound hd, ?_, hgl.one_le_height,
    hgl.height_le_maxHeight, ha.trans hgl.height_le_maxHeight, hok⟩
  · rw [hs.kd_eq, hg.kd_eq, ← hs.check_eq, hgl.kummer_eq]
  · rw [hs.check_eq, hg.dbound_eq]
    exact hg.input.dbound_lt

end JPoints

end
