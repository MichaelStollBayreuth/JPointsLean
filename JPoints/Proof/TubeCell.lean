/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TubeSign
public import JPoints.Proof.TubeCoeffs

import JPoints.Mathlib.Algebra.QuadraticDiscriminant
import JPoints.Proof.CellSizes
import JPoints.Proof.Constants
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The verdict of a cell of the tube

A cell that the analysis of the tube finds out (`tube_cell`, `JPoints.tubeCellAnalyzeGen`) holds no
triple whose Kummer quadratic `Q(x) = k₂ x² + k₁ x + k₀` has a root in `[-W, W]`
(`JPoints.TubeSetup.not_root_of_tubeCellAnalyzeGen`): its signs of `Q(W)` and `Q(-W)` agree with
those of the exact polynomials throughout the cell, and so does its sign of `k₂`, or its test
`2 th hi2 < lo1` gives `|k₁| > 2 W |k₂|` throughout (`JPoints.TubeSetup.two_mul_abs_lt_of_lt`), so
that `quadratic_ne_zero_of_abs_le` applies. The doubles of a cell meet the setting of `poly_sign`
(`JPoints.Double.PolySignSetup`): the centre and the half-sizes of a cell are exact
(`JPoints.CellCentre`, `JPoints.IsBoxCell.cellCentre`); the shifted polynomials approximate the
shifted exact ones (`JPoints.TubeSetup.approxCoeffs_shift2Gen`,
`JPoints.TubeSetup.approxCoeffs_tubeCellCombine`), whose absolute polynomials at the corner of the
cell are those of the far corner of the cell (`JPoints.eval2_combineCoeffs_abs`); and the margin
`err = TUBE_EPS ma`, `TUBE_EPS ≥ 2 ^ (-47)`, covers their errors, divided by `th2` for `k₂` and by
`th` for `k₁` (`JPoints.TubeSetup.onGrid_and_bounds_tubeEps_mul_tubeEvalGen`).

## Main definitions

* `JPoints.TubeSetup`: the setting of the analysis of the tube for a first coordinate.
* `JPoints.IsBoxCell`: a cell within the box.
* `JPoints.CellCentre`: the centre and the half-sizes of a cell as exact doubles.

## Main statements

* `JPoints.TubeSetup.not_root_of_tubeCellAnalyzeGen`: a cell found out holds no root.
* `JPoints.TubeSetup.polySignSetup_combine`, `JPoints.TubeSetup.polySignSetup_k2`,
  `JPoints.TubeSetup.polySignSetup_k1`: the calls of `poly_sign` of a cell.
* `JPoints.eval2_combineCoeffs_shift2Gen`, `JPoints.eval2_combineCoeffs_abs`: the exact
  polynomials of a cell and their majorants.

## Implementation notes

The exact objects are the arrays of the coefficients of `K₀`, `K₁` and `K₂` of
`JPoints.Proof.TubeCoeffs` shifted to the rational centre `(B, C)` of the cell, and those of their
absolute values shifted to `(|B|, |C|)`, evaluated at the half-sizes `(R, S)`. The bound `W` on the
fourth coordinate is a `long`, below `2 ^ 63`, so that `th` and `th2` are finite and the quotients
of the margin are not in the subnormal range. The constants of the margins are units `2 ^ (-53)` of
the absolute polynomial at the far corner: `46` of the `64` of `2 ^ (-47)` for `Q(±W)`, `20` for
`k₂` and `50` for `k₁`.
-/

@[expose] public section

namespace JPoints

open Finset Double

/-! ### The cell -/

/-- The cell of the rows `bLo..bHi` and the words `[iLo, iHi)` of the analysis of the tube within
the box of the height bound `H`: rows `-H ≤ b ≤ H` and words from `⌊-H / 64⌋` below
`⌊H / 64⌋ + 1`, the words of the rows of the box, at least one row and one word. -/
structure IsBoxCell (H bLo bHi iLo iHi : ℤ) : Prop where
  /-- The first row is in the box. -/
  neg_le : -H ≤ bLo
  /-- At least one row. -/
  le : bLo ≤ bHi
  /-- The last row is in the box. -/
  le_H : bHi ≤ H
  /-- The first word is that of a third coordinate of the box or later. -/
  wLow_le : (-H) >>> longShift ≤ iLo
  /-- At least one word. -/
  lt : iLo < iHi
  /-- The words end with those of the third coordinates of the box. -/
  le_wHigh : iHi ≤ (H >>> longShift) + 1

/-- The centre `(bm, cm)` and the half-sizes `rb` and `rc` of a cell of the analysis of the tube as
doubles, exact: the rational centre `(B, C)` and the half-sizes `R ≥ 0` and `S > 0` on the grid
`2 ^ (-1) ℤ`, the far corner `(|B| + R, |C| + S)` too, which lies in the box `[-H, H]` by
`[-H - 63, H + 63]`, and the half-sizes without sign bits. -/
structure CellCentre (bm rb cm rc : Double) (B R C S : ℚ) (H : ℤ) : Prop where
  /-- The first coordinate of the centre. -/
  approx_bm : bm.Approx B |B| 0 1
  /-- The half-size in rows. -/
  approx_rb : rb.Approx R R 0 1
  /-- The second coordinate of the centre. -/
  approx_cm : cm.Approx C |C| 0 1
  /-- The half-size in third coordinates. -/
  approx_rc : rc.Approx S S 0 1
  /-- The first coordinate of the far corner. -/
  approx_fb : (bm.fabs + rb).Approx (|B| + R) (|B| + R) 0 1
  /-- The second coordinate of the far corner. -/
  approx_fc : (cm.fabs + rc).Approx (|C| + S) (|C| + S) 0 1
  /-- The half-size in rows has no sign bit. -/
  signBit_rb : rb.signBit = false
  /-- The half-size in third coordinates is positive. -/
  pos_S : 0 < S
  /-- The far corner lies within the box in rows. -/
  fb_le : |B| + R ≤ H
  /-- The far corner lies within the box in third coordinates. -/
  fc_le : |C| + S ≤ H + 63

namespace IsBoxCell

variable {H bLo bHi iLo iHi : ℤ} (h : IsBoxCell H bLo bHi iLo iHi)
include h

private theorem abs_add_lt_and_abs_sub_lt (hH : H ≤ maxHeight) :
    |bLo + bHi| < 2 ^ 52 ∧ |bHi - bLo| < 2 ^ 52 ∧ |iLo + iHi| < 2 ^ 40 ∧ |iHi - iLo| < 2 ^ 40 ∧
      -H - 63 ≤ 64 * iLo ∧ 64 * iHi - 1 ≤ H + 63 := by
  have h1 := h.wLow_le
  have h2 := h.le_wHigh
  simp only [Int.shiftRight_longShift] at h1 h2
  have := maxHeight_lt_two_pow_32
  have := h.neg_le
  have := h.le
  have := h.le_H
  have := h.lt
  refine ⟨abs_lt.mpr ⟨by lia, by lia⟩, abs_lt.mpr ⟨by lia, by lia⟩, abs_lt.mpr ⟨by lia, by lia⟩,
    abs_lt.mpr ⟨by lia, by lia⟩, by lia, by lia⟩

-- The centre and the half-sizes of the cell as rationals: within `2 ^ 51` and `2 ^ 45`, with the
-- far corner in the box.
private theorem centre_bounds (hH : H ≤ maxHeight) :
    |((bLo + bHi : ℤ) : ℚ) / 2| < 2 ^ 51 ∧ |((bHi - bLo : ℤ) : ℚ) / 2| < 2 ^ 51 ∧
      |32 * ((iLo + iHi : ℤ) : ℚ) - 1 / 2| < 2 ^ 46 ∧
      |32 * ((iHi - iLo : ℤ) : ℚ) - 1 / 2| < 2 ^ 46 ∧
      0 ≤ ((bHi - bLo : ℤ) : ℚ) / 2 ∧ 0 < 32 * ((iHi - iLo : ℤ) : ℚ) - 1 / 2 := by
  obtain ⟨b1, b2, b3, b4, -, -⟩ := h.abs_add_lt_and_abs_sub_lt hH
  have q1 : |((bLo + bHi : ℤ) : ℚ)| < 2 ^ 52 := mod_cast b1
  have q2 : |((bHi - bLo : ℤ) : ℚ)| < 2 ^ 52 := mod_cast b2
  have q3 : |((iLo + iHi : ℤ) : ℚ)| < 2 ^ 40 := mod_cast b3
  have q4 : |((iHi - iLo : ℤ) : ℚ)| < 2 ^ 40 := mod_cast b4
  have q7 : (bLo : ℚ) ≤ bHi := mod_cast h.le
  have q8 : (iLo + 1 : ℚ) ≤ iHi := mod_cast h.lt
  push_cast at q1 q2 q3 q4 ⊢
  obtain ⟨⟨q1, q1'⟩, ⟨q2, q2'⟩, ⟨q3, q3'⟩, ⟨q4, q4'⟩⟩ :=
    And.intro (abs_lt.mp q1) (And.intro (abs_lt.mp q2) (And.intro (abs_lt.mp q3) (abs_lt.mp q4)))
  exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩,
    abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith,
    by linarith⟩

-- The far corner of the cell lies in the box `[-H, H] × [-H - 63, H + 63]`.
private theorem corner_bounds (hH : H ≤ maxHeight) :
    |((bLo + bHi : ℤ) : ℚ) / 2| + ((bHi - bLo : ℤ) : ℚ) / 2 ≤ H ∧
      |32 * ((iLo + iHi : ℤ) : ℚ) - 1 / 2| + (32 * ((iHi - iLo : ℤ) : ℚ) - 1 / 2) ≤ H + 63 := by
  obtain ⟨-, -, -, -, b5, b6⟩ := h.abs_add_lt_and_abs_sub_lt hH
  have q5 : (-H - 63 : ℚ) ≤ 64 * iLo := mod_cast b5
  have q6 : (64 * iHi - 1 : ℚ) ≤ H + 63 := mod_cast b6
  have q9 : (-H : ℚ) ≤ bLo := mod_cast h.neg_le
  have q10 : (bHi : ℚ) ≤ H := mod_cast h.le_H
  push_cast
  constructor
  · rcases abs_cases (((bLo : ℚ) + bHi) / 2) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> linarith
  · rcases abs_cases (32 * ((iLo : ℚ) + iHi) - 1 / 2) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> linarith

theorem left_words (hw : 1 < iHi - iLo) : IsBoxCell H bLo bHi iLo (iLo + (iHi - iLo) / 2) :=
  ⟨h.neg_le, h.le, h.le_H, h.wLow_le, by lia, by lia [h.le_wHigh]⟩

theorem right_words (hw : 1 < iHi - iLo) : IsBoxCell H bLo bHi (iLo + (iHi - iLo) / 2) iHi :=
  ⟨h.neg_le, h.le, h.le_H, by lia [h.wLow_le], by lia, h.le_wHigh⟩

theorem lower_rows : IsBoxCell H bLo (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi :=
  ⟨h.neg_le, by lia [h.le], by lia [h.le, h.le_H], h.wLow_le, h.lt, h.le_wHigh⟩

theorem upper_rows (hr : 1 < bHi - bLo + 1) :
    IsBoxCell H (bLo + (bHi - bLo + 1 - 1) / 2 + 1) bHi iLo iHi :=
  ⟨by lia [h.neg_le, h.le], by lia, h.le_H, h.wLow_le, h.lt, h.le_wHigh⟩

theorem cellCentre (hH : H ≤ maxHeight) :
    CellCentre ((0.5 : Double) * ofInt (bLo + bHi)) ((0.5 : Double) * ofInt (bHi - bLo))
      ((32.0 : Double) * ofInt (iLo + iHi) - 0.5) ((32.0 : Double) * ofInt (iHi - iLo) - 0.5)
      (((bLo + bHi : ℤ) : ℚ) / 2) (((bHi - bLo : ℤ) : ℚ) / 2) (32 * ((iLo + iHi : ℤ) : ℚ) - 1 / 2)
      (32 * ((iHi - iLo : ℤ) : ℚ) - 1 / 2) H := by
  obtain ⟨b1, b2, -, -, -, -⟩ := h.abs_add_lt_and_abs_sub_lt hH
  obtain ⟨c1, c2, c3, c4, hR, hS⟩ := h.centre_bounds hH
  obtain ⟨c7, c8⟩ := h.corner_bounds hH
  have hbm := approx_half_mul_ofInt b1
  have hrb := approx_half_mul_ofInt b2
  have hcm := approx_thirtyTwo_mul_ofInt_sub_half (h.abs_add_lt_and_abs_sub_lt hH).2.2.1
  have hrc := approx_thirtyTwo_mul_ofInt_sub_half (h.abs_add_lt_and_abs_sub_lt hH).2.2.2.1
  have h51 := pow_lt_pow_right₀ (one_lt_two : (1 : ℚ) < 2) (show 51 < 52 by norm_num)
  have h46 := pow_lt_pow_right₀ (one_lt_two : (1 : ℚ) < 2) (show 46 < 52 by norm_num)
  have hfb := approx_add_exact (by rw [abs_abs]; exact hbm.fabs) hrb (by rw [abs_abs]; linarith)
  have hfc := approx_add_exact (by rw [abs_abs]; exact hcm.fabs) hrc (by rw [abs_abs]; linarith)
  rw [abs_of_nonneg hR] at hrb
  rw [abs_of_pos hS] at hrc
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hR)] at hfb
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hS.le)] at hfc
  exact ⟨hbm, hrb, hcm, hrc, hfb, hfc, signBit_half_mul_ofInt (by lia [h.le]), hS, c7, c8⟩

end IsBoxCell

/-! ### The exact polynomials of a cell -/

section Exact

variable (K : KummerCoeffs) (cs : Array ℤ) (W a : ℤ)

private theorem eval2_abs_k1Coeff_four (X Y : ℚ) :
    eval2 (coeffArray fun j k ↦ |k1Coeff cs a j k|) 4 X Y =
      eval2 (coeffArray fun j k ↦ |k1Coeff cs a j k|) 3 X Y :=
  eval2_add_of_forall_eq_zero (D := 3) (m := 1)
    (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ h ↦
      abs_eq_zero.mpr (k1Coeff_eq_zero cs a h)) X Y

private theorem eval2_abs_k2Coeff_four (X Y : ℚ) :
    eval2 (coeffArray fun j k ↦ |k2Coeff a j k|) 4 X Y =
      eval2 (coeffArray fun j k ↦ |k2Coeff a j k|) 2 X Y :=
  eval2_add_of_forall_eq_zero (D := 2) (m := 2)
    (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ h ↦
      abs_eq_zero.mpr (k2Coeff_eq_zero a h)) X Y

variable {W} in
/-- The absolute polynomials of `K₀`, of `K₁` times `W` and of `K₂` times `W²`, each at its own
degree, are at most the absolute polynomial `KA` of the tube at a point `X, Y ≥ 0`. -/
private theorem eval2_abs_le_eval2_kaCoeff (hW : 1 ≤ W) {X Y : ℚ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    eval2 (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 X Y ≤
        eval2 (coeffArray (kaCoeff K cs W a)) 4 X Y ∧
      W * eval2 (coeffArray fun j k ↦ |k1Coeff cs a j k|) 3 X Y ≤
        eval2 (coeffArray (kaCoeff K cs W a)) 4 X Y ∧
      W ^ 2 * eval2 (coeffArray fun j k ↦ |k2Coeff a j k|) 2 X Y ≤
        eval2 (coeffArray (kaCoeff K cs W a)) 4 X Y := by
  have hW' : (1 : ℚ) ≤ W := mod_cast hW
  rw [eval2_kaCoeff K cs W a four_lt_coeffRow, eval2_abs_k1Coeff_four, eval2_abs_k2Coeff_four]
  have hn (φ : ℕ → ℕ → ℚ) (d : ℕ) :=
    eval2_nonneg (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg (φ j k)) d hX hY
  have h0 := hn (k0Coeff K a) 4
  have h1 := hn (k1Coeff cs a) 3
  have h2 := hn (k2Coeff a) 2
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The absolute polynomials of `K₀`, `K₁` and `K₂` shifted to `(|B|, |C|)` and combined with the
weights `W` and `W²` are the absolute polynomial `KA` at the shifted point: the majorants of the
coefficients of `Q(±W)` at the centre of a cell give `KA` at the far corner. -/
theorem eval2_combineCoeffs_abs (B C X Y : ℚ) :
    eval2 (combineCoeffs W (W * W)
      (shift2Gen (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 |B| |C|)
      (shift2Gen (coeffArray fun j k ↦ |k1Coeff cs a j k|) 3 |B| |C|)
      (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 X Y =
      eval2 (coeffArray (kaCoeff K cs W a)) 4 (|B| + X) (|C| + Y) := by
  rw [eval2_combineCoeffs _ _ _ _ _ four_lt_coeffRow, eval2_kaCoeff K cs W a four_lt_coeffRow,
    eval2_shift2Gen_of_le le_rfl four_lt_coeffRow (size_coeffArray _).ge (fun j k h1 h2 ↦ by lia),
    eval2_shift2Gen_of_le (by norm_num) four_lt_coeffRow (size_coeffArray _).ge
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ h ↦
        abs_eq_zero.mpr (k1Coeff_eq_zero cs a h)),
    eval2_shift2Gen_of_le (by norm_num) four_lt_coeffRow (size_coeffArray _).ge
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ h ↦
        abs_eq_zero.mpr (k2Coeff_eq_zero a h))]
  ring

/-- The polynomials `K₀`, `K₁` and `K₂` of the first coordinate `a` shifted to a centre `(B, C)`
and combined with the weights `w` and `W²` give `Q(w) = K₂ w² + K₁ w + K₀` at `(b, c)`, of the
Kummer quadratic over `(a, b, c)`, at the shift `(b - B, c - C)`. -/
theorem eval2_combineCoeffs_shift2Gen (w B C : ℚ) (b c : ℤ) :
    eval2 (combineCoeffs w (W * W)
      (shift2Gen (coeffArray (k0Coeff (kummerInit cs) a)) 4 B C)
      (shift2Gen (coeffArray (k1Coeff cs a)) 3 B C)
      (shift2Gen (coeffArray (k2Coeff a)) 2 B C)) 4 (b - B) (c - C) =
      kummerK2 a b c * (W * W) + kummerK1 (cs.toList.getD · 0) a b c * w +
        kummerK0 (cs.toList.getD · 0) a b c := by
  rw [eval2_combineCoeffs _ _ _ _ _ four_lt_coeffRow,
    eval2_shift2Gen_of_le le_rfl four_lt_coeffRow (size_coeffArray _).ge (fun j k h1 h2 ↦ by lia),
    eval2_shift2Gen_of_le (by norm_num) four_lt_coeffRow (size_coeffArray _).ge
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ ↦ k1Coeff_eq_zero cs a),
    eval2_shift2Gen_of_le (by norm_num) four_lt_coeffRow (size_coeffArray _).ge
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ ↦ k2Coeff_eq_zero a),
    add_sub_cancel, add_sub_cancel, eval2_k0Coeff,
    eval2_add_of_forall_eq_zero (D := 3) (m := 1)
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ ↦ k1Coeff_eq_zero cs a),
    eval2_add_of_forall_eq_zero (D := 2) (m := 2)
      (getElem!_coeffArray_eq_zero four_lt_coeffRow fun _ _ ↦ k2Coeff_eq_zero a),
    eval2_k1Coeff, eval2_k2Coeff]
  ring

private theorem eval2_shift2Gen_k1Coeff (B C : ℚ) (b c : ℤ) :
    eval2 (shift2Gen (coeffArray (k1Coeff cs a)) 3 B C) 3 (b - B) (c - C) =
      kummerK1 (cs.toList.getD · 0) a b c := by
  rw [eval2_shift2Gen _ _ _ _ (by lia [four_lt_coeffRow]) (size_coeffArray _).ge, add_sub_cancel,
    add_sub_cancel, eval2_k1Coeff]

private theorem eval2_shift2Gen_k2Coeff (B C : ℚ) (b c : ℤ) :
    eval2 (shift2Gen (coeffArray (k2Coeff a)) 2 B C) 2 (b - B) (c - C) = kummerK2 a b c := by
  rw [eval2_shift2Gen _ _ _ _ (by lia [four_lt_coeffRow]) (size_coeffArray _).ge, add_sub_cancel,
    add_sub_cancel, eval2_k2Coeff]

end Exact

/-- The quotient of the margin `x` of a cell, on the grid `2 ^ (-156) ℤ` and between `63 K / 2 ^ 53`
and `2 K` for `K < 2 ^ 998`, by a finite `1 ≤ y ≤ 2 ^ 127` with `y ≤ (1 + 2 ^ (-51)) w`: finite,
at most `2 ^ 1000`, and at least `c M / 2 ^ 53` for `c ≤ 60` and every `M ≥ 0` with `w M ≤ K`. -/
private theorem div_margin {x y : Double} {K M w : ℚ} (hx : x.isFinite = true)
    (hxg : OnGrid 156 x.toRat) (hx1 : 63 * K / 2 ^ 53 ≤ x.toRat) (hx2 : x.toRat ≤ 2 * K)
    (hK : K < 2 ^ 998) (hM0 : 0 ≤ M) (hMK : w * M ≤ K) (hy : y.isFinite = true)
    (hy1 : 1 ≤ y.toRat) (hy2 : y.toRat ≤ 2 ^ 127) (hyw : y.toRat ≤ (1 + 1 / 2 ^ 51) * w) {c : ℕ}
    (hc : c ≤ 60) :
    (x / y).isFinite = true ∧ c * M / 2 ^ 53 ≤ (x / y).toRat ∧ (x / y).toRat ≤ 2 ^ 1000 := by
  have hw : 0 < w := by nlinarith
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hw.le hM0) hMK
  have hx0 : 0 ≤ x.toRat := le_trans (by positivity) hx1
  have h4 : (2 : ℚ) ^ 1000 = 4 * 2 ^ 998 := by rw [show 1000 = 2 + 998 from rfl, pow_add]; norm_num
  obtain ⟨hf, hb⟩ := div_bounds hx hx0 hxg
    (by rw [h4]; generalize (2 : ℚ) ^ 998 = T at hK; linarith) hy hy1 hy2 (by norm_num)
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hy0 : 0 < y.toRat := by linarith
  have hq : x.toRat / y.toRat ≤ x.toRat := div_le_self hx0 hy1
  refine ⟨hf, ?_, by rw [h4]; generalize (2 : ℚ) ^ 998 = T at hK; linarith⟩
  have hc' : (c : ℚ) ≤ 60 := mod_cast hc
  have : c * M / 2 ^ 53 ≤ (1 - 1 / 2 ^ 52) * (x.toRat / y.toRat) := by
    rw [mul_div_assoc', le_div_iff₀ hy0]
    have p1 := mul_le_mul_of_nonneg_left hyw hM0
    have p2 := mul_le_mul_of_nonneg_left hc' (mul_nonneg hM0 hy0.le)
    nlinarith
  linarith

namespace CellCentre

variable {bm rb cm rc : Double} {B R C S : ℚ} {H : ℤ} (hc : CellCentre bm rb cm rc B R C S H)
include hc

/-- The far corner of a cell as doubles, exact, and at most `2 ^ 200`. -/
private theorem approx_fabs_add_and_abs_le (hH : H ≤ maxHeight) :
    (bm.fabs + rb).Approx (|B| + R) |(|B| + R)| 0 1 ∧ |(|B| + R)| ≤ 2 ^ 200 ∧
      (cm.fabs + rc).Approx (|C| + S) |(|C| + S)| 0 1 ∧ |(|C| + S)| ≤ 2 ^ 200 := by
  have hR := hc.approx_rb.nonneg
  have hS0 := hc.pos_S
  have e1 : |(|B| + R)| = |B| + R := abs_of_nonneg (by positivity)
  have e2 : |(|C| + S)| = |C| + S := abs_of_nonneg (by positivity)
  have hHq : (H : ℚ) ≤ 2 ^ 32 := mod_cast (by lia [maxHeight_lt_two_pow_32])
  have h200 := pow_le_pow_right₀ (one_le_two : (1 : ℚ) ≤ 2) (show 33 ≤ 200 by norm_num)
  rw [e1, e2]
  exact ⟨by rw [← e1, e1]; exact hc.approx_fb, by linarith [hc.fb_le], hc.approx_fc,
    by linarith [hc.fc_le]⟩

/-- The powers `x ^ j` and `y ^ k`, `j, k ≤ 4`, of the far corner `(x, y)` of a cell, by repeated
products: finite and without sign bits, those of `y` not zero. -/
private theorem isFinite_and_signBit_iterate_mul_fabs_add (hH : H ≤ maxHeight) {j k : ℕ}
    (hj : j ≤ 4) (hk : k ≤ 4) :
    ((· * (bm.fabs + rb))^[j] 1.0).isFinite = true ∧
      ((· * (bm.fabs + rb))^[j] 1.0).signBit = false ∧
      ((· * (cm.fabs + rc))^[k] 1.0).isFinite = true ∧
      ((· * (cm.fabs + rc))^[k] 1.0).signBit = false ∧
      ((· * (cm.fabs + rc))^[k] 1.0).isZero = false := by
  obtain ⟨hfb, hb, hfc, hc'⟩ := hc.approx_fabs_add_and_abs_le hH
  have hx := approx_iterate_mul_one hfb hb hj
  have hy := approx_iterate_mul_one hfc hc' hk
  have hS0 := hc.pos_S
  rw [abs_of_nonneg (show 0 ≤ |C| + S by positivity)] at hy
  exact ⟨hx.isFinite, signBit_iterate_mul_of_isFinite (signBit_add (signBit_fabs _)
    hc.signBit_rb) (by decide) hx.isFinite, hy.isFinite, signBit_iterate_mul_of_isFinite
    (signBit_add (signBit_fabs _) (signBit_eq_false_of_pos (hc.approx_rc.toRat_eq_of_zero ▸
      hS0))) (by decide) hy.isFinite, hy.isZero_eq_false (by positivity) (by lia)⟩

theorem rp_approx (hH : H ≤ maxHeight) {j k : ℕ} (hjk : j + k ≤ 4) :
    ((cellProducts rb rc)[coeffIndex j k]!).Approx (R ^ j * S ^ k) (R ^ j * S ^ k) (j + k)
      (j + k) := by
  have hR := hc.approx_rb.nonneg
  have hHq : (H : ℚ) ≤ 2 ^ 32 := mod_cast (by lia [maxHeight_lt_two_pow_32])
  have h200 : (2 : ℚ) ^ 33 ≤ 2 ^ 200 := pow_le_pow_right₀ one_le_two (by norm_num)
  exact approx_getElem!_cellProducts hc.approx_rb hc.approx_rc
    (by linarith [hc.fb_le, abs_nonneg B]) (by linarith [hc.fc_le, abs_nonneg C]) hjk

theorem rp_signBit (hH : H ≤ maxHeight) {j k : ℕ} (hjk : j + k ≤ 4) :
    ((cellProducts rb rc)[coeffIndex j k]!).signBit = false := by
  have h := hc.rp_approx hH hjk
  rw [cellProducts, getElem!_coeffArray _ (by lia [four_lt_coeffRow])
    (by lia [four_lt_coeffRow])] at h ⊢
  have hy := isFinite_of_isFinite_iterate_mul h.isFinite
  exact signBit_iterate_mul_of_isFinite
    (signBit_eq_false_of_pos (hc.approx_rc.toRat_eq_of_zero ▸ hc.pos_S))
    (signBit_iterate_mul_of_isFinite hc.signBit_rb (by decide) hy) h.isFinite

end CellCentre

/-- `JPoints.shift2` to the exact centre of a cell of approximations of the coefficients of a
polynomial with the coefficients `φ`, of degree `d ≤ 4`, within `n` roundings on the grid
`2 ^ (-g) ℤ`, approximates the shifted polynomial within `n + 4 d` roundings, when its absolute
polynomial at `(|B| + 1, |C| + 1)` is at most `2 ^ 1002`. -/
private theorem CellCentre.approxCoeffs_shift2Gen {bm rb cm rc : Double} {B R C S : ℚ} {H : ℤ}
    (hc : CellCentre bm rb cm rc B R C S H) {p : Array Double} {φ : ℕ → ℕ → ℚ} {d n g : ℕ}
    (hp : ApproxCoeffs p (coeffArray φ) (coeffArray fun j k ↦ |φ j k|) 4 n g) (hd : d ≤ 4)
    (hsz : p.size = numCoeffs) (hn : n + 4 * d ≤ 2 ^ 52) (hg : g + n + 4 * d ≤ 1074)
    (hB : eval2 (coeffArray fun j k ↦ |φ j k|) d (|B| + 1) (|C| + 1) ≤ 2 ^ 1002) :
    ApproxCoeffs (shift2Gen p d bm cm) (shift2Gen (coeffArray φ) d B C)
      (shift2Gen (coeffArray fun j k ↦ |φ j k|) d |B| |C|) 4 (n + 4 * d) (g + n + 4 * d) :=
  hp.shift2Gen hd four_lt_coeffRow hsz.ge (size_coeffArray _).ge (size_coeffArray _).ge
    (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg _) hc.approx_bm hc.approx_cm
    (one_add_pow_mul_lt_two_pow_1022 hn (eval2_nonneg
      (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg _) d (by positivity) (by positivity))
      (hB.trans (pow_le_pow_right₀ one_le_two (by norm_num)))) hg

/-- The setting of the analysis of the tube for the first coordinate `a`: the coefficients `kd`
that `tube_init` computes for the curve searched `curve` and its quartic `K₀`
(`JPoints.kummerInit`), the bound `1 ≤ W < 2 ^ 63` on the fourth coordinate, a `long`, with
`th = (double)W` and `th2 = th * th`, the height bound `1 ≤ H ≤ MAX_HEIGHT`, `|a| ≤ MAX_HEIGHT`,
and `tube_ok` for the polynomials of `a`. -/
structure TubeSetup (kd : TubeCoeffs) (curve : SearchCurve) (H W : ℤ) (th th2 : Double) (a : ℤ) :
    Prop where
  /-- The coefficients of `tube_init`. -/
  kd_eq : kd = (tubeInitCoeffs curve (kummerInit curve.coeffs)).run
  /-- The bound on the fourth coordinate as a double. -/
  th_eq : th = ofInt W
  /-- Its square. -/
  th2_eq : th2 = th * th
  /-- The bound on the fourth coordinate is positive. -/
  one_le_W : 1 ≤ W
  /-- The bound on the fourth coordinate is below `2 ^ 63`. -/
  W_lt : W < 2 ^ 63
  /-- The height bound is positive. -/
  one_le_H : 1 ≤ H
  /-- The height bound is at most `MAX_HEIGHT`. -/
  H_le : H ≤ maxHeight
  /-- The first coordinate is at most `MAX_HEIGHT`. -/
  abs_a_le : |a| ≤ maxHeight
  /-- `tube_ok` for the polynomials of `a`. -/
  tubeOk : (tubeEval (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).run.lt
    tubeBig = true

namespace TubeSetup

variable {kd : TubeCoeffs} {curve : SearchCurve} {H W : ℤ} {th th2 : Double} {a : ℤ}
  (hS : TubeSetup kd curve H W th th2 a)
include hS

private theorem tubeApprox :
    TubeApprox kd th th2 (kummerInit curve.coeffs) curve.coeffs W a ∧
      eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 H
        (H + longLength) < 2 ^ 998 :=
  TubeApprox.of_tubeOk hS.kd_eq hS.th_eq hS.th2_eq hS.one_le_W hS.W_lt hS.one_le_H hS.H_le
    hS.abs_a_le hS.tubeOk

private theorem nonneg_getElem!_coeffArray_kaCoeff (i : ℕ) :
    0 ≤ (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a))[i]! :=
  nonneg_getElem!_coeffArray
    (nonneg_kaCoeff (kummerInit curve.coeffs) curve.coeffs (by lia [hS.one_le_W]) a) i

/-- The absolute polynomial `KA` at `(H, H + 64)` is below `2 ^ 998`, the bound of its value in
doubles below `TUBE_BIG` that `tube_ok` gives. -/
private theorem eval2_kaCoeff_lt :
    eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 H (H + 64) <
      2 ^ 998 := by
  have h3 := hS.tubeApprox.2
  rwa [show ((longLength : ℕ) : ℚ) = 64 by rw [show longLength = 64 from rfl]; norm_num] at h3

/-- The absolute polynomial `KA` at a point of the box `[0, 2 H] × [0, 2 (H + 64)]` is at most
`2 ^ 1002`: sixteen times its value at `(H, H + 64)`, which `tube_ok` bounds. -/
private theorem eval2_kaCoeff_le {X Y : ℚ} (hX0 : 0 ≤ X) (hX : X ≤ 2 * H) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 2 * (H + 64)) :
    eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 X Y ≤ 2 ^ 1002 := by
  have hk := hS.nonneg_getElem!_coeffArray_kaCoeff
  have hH : (1 : ℚ) ≤ H := mod_cast hS.one_le_H
  have h1 := eval2_le_eval2 hk 4 hX0 hX hY0 hY
  have h2 := eval2_mul_mul_le hk 4 one_le_two (s := (H : ℚ)) (t := H + 64) (by linarith)
    (by linarith)
  have h3 := hS.eval2_kaCoeff_lt
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ 2 ^ 4 * 2 ^ 998 := mul_le_mul_of_nonneg_left h3.le (by norm_num)
    _ = 2 ^ 1002 := by rw [← pow_add]

variable {bm rb cm rc : Double} {B R C S : ℚ}

/-- The polynomials of the first coordinate shifted by `JPoints.shift2` to the exact centre of a
cell approximate the exact polynomials shifted there: `K0` within `22` roundings, `K1` within `18`
and `K2` within `9`, the shifted absolute polynomials as the majorants. -/
theorem approxCoeffs_shift2Gen (hc : CellCentre bm rb cm rc B R C S H) :
    ApproxCoeffs (shift2Gen (tubeK0 kd a) 4 bm cm)
        (shift2Gen (coeffArray (k0Coeff (kummerInit curve.coeffs) a)) 4 B C)
        (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
        4 22 75 ∧
      ApproxCoeffs (shift2Gen (tubeK1 kd a) 3 bm cm)
        (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
        (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|) 4 18 71 ∧
      ApproxCoeffs (shift2Gen (tubeK2 kd a) 2 bm cm)
        (shift2Gen (coeffArray (k2Coeff a)) 2 B C)
        (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|) 4 9 9 := by
  obtain ⟨hT, -⟩ := hS.tubeApprox
  have hH : (1 : ℚ) ≤ H := mod_cast hS.one_le_H
  have hW : (1 : ℚ) ≤ W := mod_cast hS.one_le_W
  have hX0 : 0 ≤ |B| + 1 := by positivity
  have hY0 : 0 ≤ |C| + 1 := by positivity
  have hK := hS.eval2_kaCoeff_le hX0 (by linarith [hc.fb_le, hc.approx_rb.nonneg]) hY0
    (by linarith [hc.fc_le, hc.pos_S])
  obtain ⟨e0, e1, e2⟩ := eval2_abs_le_eval2_kaCoeff (kummerInit curve.coeffs) curve.coeffs a
    hS.one_le_W hX0 hY0
  have hn (φ : ℕ → ℕ → ℚ) (d : ℕ) :=
    eval2_nonneg (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg (φ j k)) d hX0 hY0
  have hsz := size_tubeK kd a
  exact ⟨hc.approxCoeffs_shift2Gen hT.k0 le_rfl hsz.1 (by norm_num) (by norm_num) (e0.trans hK),
    hc.approxCoeffs_shift2Gen hT.k1 (by norm_num) hsz.2.1 (by norm_num) (by norm_num)
      ((le_mul_of_one_le_left (hn _ 3) hW).trans (e1.trans hK)),
    hc.approxCoeffs_shift2Gen hT.k2 (by norm_num) hsz.2.2 (by norm_num) (by norm_num)
      ((le_mul_of_one_le_left (hn _ 2) (one_le_pow₀ hW)).trans (e2.trans hK))⟩

/-- The combinations `Q(W)` and `Q(-W)` of the shifted polynomials of the first coordinate
approximate the combinations of the shifted exact polynomials within `24` roundings, the
combination of the shifted absolute polynomials with the weights `W` and `W²` as the majorant. -/
theorem approxCoeffs_tubeCellCombine (hc : CellCentre bm rb cm rc B R C S H) :
    ApproxCoeffs (tubeCellCombine th th2 (shift2Gen (tubeK0 kd a) 4 bm cm)
        (shift2Gen (tubeK1 kd a) 3 bm cm) (shift2Gen (tubeK2 kd a) 2 bm cm)).run.1
        (combineCoeffs W (W * W)
          (shift2Gen (coeffArray (k0Coeff (kummerInit curve.coeffs) a)) 4 B C)
          (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
          (shift2Gen (coeffArray (k2Coeff a)) 2 B C))
        (combineCoeffs W (W * W)
          (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 24 75 ∧
      ApproxCoeffs (tubeCellCombine th th2 (shift2Gen (tubeK0 kd a) 4 bm cm)
        (shift2Gen (tubeK1 kd a) 3 bm cm) (shift2Gen (tubeK2 kd a) 2 bm cm)).run.2
        (combineCoeffs (-W) (W * W)
          (shift2Gen (coeffArray (k0Coeff (kummerInit curve.coeffs) a)) 4 B C)
          (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
          (shift2Gen (coeffArray (k2Coeff a)) 2 B C))
        (combineCoeffs W (W * W)
          (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 24 75 := by
  obtain ⟨hT, -⟩ := hS.tubeApprox
  obtain ⟨r0, r1, r2⟩ := hS.approxCoeffs_shift2Gen hc
  have hH : (1 : ℚ) ≤ H := mod_cast hS.one_le_H
  have hW : (0 : ℚ) ≤ W := mod_cast (by lia [hS.one_le_W])
  have hn (φ : ℕ → ℕ → ℚ) (d : ℕ) (i : ℕ) :=
    getElem!_shift2Gen_nonneg (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg (φ j k)) d
      (abs_nonneg B) (abs_nonneg C) i
  have hK := hS.eval2_kaCoeff_le (X := |B| + 1) (Y := |C| + 1) (by positivity)
    (by linarith [hc.fb_le, hc.approx_rb.nonneg]) (by positivity) (by linarith [hc.fc_le, hc.pos_S])
  rw [← eval2_combineCoeffs_abs] at hK
  have hB := fun j k (hjk : j + k ≤ 4) ↦ one_add_pow_mul_lt_two_pow_1022
    (n := max (max 22 (1 + 18 + 1) + 1) (3 + 9 + 1)) (by norm_num)
    (nonneg_getElem!_combineCoeffs hW (mul_nonneg hW hW) (hn _ 4) (hn _ 3) (hn _ 2) _)
    (((getElem!_le_eval2_one (nonneg_getElem!_combineCoeffs hW (mul_nonneg hW hW) (hn _ 4)
      (hn _ 3) (hn _ 2)) hjk).trans hK).trans (pow_le_pow_right₀ one_le_two (by norm_num)))
  exact ApproxCoeffs.tubeCellCombine r0 (r1.mono le_rfl le_rfl (by norm_num))
    (r2.mono le_rfl le_rfl (by norm_num)) hT.th hT.th2 four_lt_coeffRow (by norm_num) hB

/-- The absolute polynomial `KA` at the far corner of a cell is nonnegative and, at most its value
at `(H, H + 64)`, below `2 ^ 998`. -/
private theorem eval2_kaCoeff_far_le (hc : CellCentre bm rb cm rc B R C S H) :
    0 ≤ eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
        (|C| + S) ∧
      eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
        (|C| + S) < 2 ^ 998 := by
  have hk := hS.nonneg_getElem!_coeffArray_kaCoeff
  have hR := hc.approx_rb.nonneg
  have hS0 := hc.pos_S
  exact ⟨eval2_nonneg hk 4 (by positivity) (by positivity), (eval2_le_eval2 hk 4 (by positivity)
    hc.fb_le (by linarith [abs_nonneg C]) (by linarith [hc.fc_le])).trans_lt hS.eval2_kaCoeff_lt⟩

/-- `tube_eval` of `KA` at the far corner of a cell, when finite, approximates the absolute
polynomial `KA` there within `31` roundings, on the grid `2 ^ (-57) ℤ`. -/
private theorem approx_tubeEvalGen_far (hc : CellCentre bm rb cm rc B R C S H)
    (hm : (tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).isFinite = true) :
    (tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).Approx
      (eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
        (|C| + S))
      (eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
        (|C| + S)) 31 57 := by
  obtain ⟨hfb, hb, hfc, hc'⟩ := hc.approx_fabs_add_and_abs_le hS.H_le
  have hma := approx_tubeEvalGen hS.tubeApprox.1.ka hfb hfc hb hc' le_rfl (by norm_num) hm
  have hR := hc.approx_rb.nonneg
  have hS0 := hc.pos_S
  rwa [abs_of_nonneg (show 0 ≤ |B| + R by positivity),
    abs_of_nonneg (show 0 ≤ |C| + S by positivity),
    show 10 + 4 + 2 + (evalIndices 4).length = 31 by decide] at hma

/-- The margin `err = TUBE_EPS * ma` of a cell, for the value `ma` of `KA` at the far corner that
`tube_eval` computes, when finite: on the grid `2 ^ (-156) ℤ`, at least `63 KA_f / 2 ^ 53` and at
most `2 KA_f`, for the absolute polynomial `KA_f` at the far corner, since `TUBE_EPS ≥ 2 ^ (-47)`
and `ma` approximates `KA_f` within `31` roundings. -/
theorem onGrid_and_bounds_tubeEps_mul_tubeEvalGen (hc : CellCentre bm rb cm rc B R C S H)
    (hf : (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).isFinite =
      true) :
    OnGrid 156 (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).toRat ∧
      63 * eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
          (|C| + S) / 2 ^ 53 ≤
        (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).toRat ∧
      (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).toRat ≤
        2 * eval2 (coeffArray (kaCoeff (kummerInit curve.coeffs) curve.coeffs W a)) 4 (|B| + R)
          (|C| + S) := by
  obtain ⟨-, hm⟩ := isFinite_and_of_isFinite_mul hf
  have hma := hS.approx_tubeEvalGen_far hc hm
  have he0 : 1 / 2 ^ 47 ≤ tubeEps.toRat := tubeEpsMin_eq ▸ tubeEpsMin_le_toRat_tubeEps
  have hg := onGrid_toRat_of_le (j := 47) (x := tubeEps) (by rwa [abs_of_pos (by linarith)])
  have hr := isGridRounding_mul hg hma.onGrid (by norm_num) hf
  refine ⟨hr.onGrid, ?_⟩
  have hK0 := (hS.eval2_kaCoeff_far_le hc).1
  have h1 := hma.two_sub_pow_mul_le_toRat
  have h2 := (le_abs_self _).trans hma.abs_toRat_le
  have hρ := one_add_pow_sub_one_le (n := 31) (by norm_num)
  have hm0 : 0 ≤ (tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).toRat := by
    nlinarith
  have p1 := mul_le_mul_of_nonneg_right he0 hm0
  have p2 := mul_le_mul_of_nonneg_right toRat_tubeEps_le_one hm0
  have p3 := mul_le_mul_of_nonneg_right hρ hK0
  have hr' := abs_le.mp hr.abs_sub_le
  rw [abs_of_nonneg (mul_nonneg (by linarith) hm0)] at hr'
  push_cast at p3
  constructor <;> nlinarith

/-- The bound `th = (double)W` on the fourth coordinate: finite, at least `1` and at most
`2 ^ 64`, within a rounding of `W`, without a sign bit. -/
private theorem isFinite_and_bounds_th :
    th.isFinite = true ∧ 1 ≤ th.toRat ∧ th.toRat ≤ 2 ^ 64 ∧ th.toRat ≤ (1 + 1 / 2 ^ 53) * W ∧
      th.signBit = false ∧ th.isZero = false := by
  have h := hS.tubeApprox.1.th
  have hW : (1 : ℚ) ≤ W := mod_cast hS.one_le_W
  have hW' : (W : ℚ) ≤ 2 ^ 63 := mod_cast hS.W_lt.le
  have h1 := abs_le.mp h.abs_sub_le
  rw [pow_one] at h1
  have hpos := h.toRat_pos (by linarith) (by norm_num)
  refine ⟨h.isFinite, h.onGrid.le_of_pos hpos |>.trans_eq' (by norm_num), by nlinarith,
    by nlinarith, signBit_eq_false_of_pos hpos, isZero_eq_false_iff.mpr hpos.ne'⟩

/-- The square `th2 = th * th` of the bound on the fourth coordinate: finite, at least `1` and
at most `2 ^ 127`, within three roundings of `W²`, without a sign bit. -/
private theorem isFinite_and_bounds_th2 :
    th2.isFinite = true ∧ 1 ≤ th2.toRat ∧ th2.toRat ≤ 2 ^ 127 ∧
      th2.toRat ≤ (1 + 1 / 2 ^ 51) * (W * W) ∧ th2.signBit = false ∧ th2.isZero = false := by
  have h := hS.tubeApprox.1.th2
  have hW : (1 : ℚ) ≤ W := mod_cast hS.one_le_W
  have hW' : (W : ℚ) ≤ 2 ^ 63 := mod_cast hS.W_lt.le
  have hρ := one_add_pow_sub_one_le (n := 3) (by norm_num)
  have h1 := abs_le.mp h.abs_sub_le
  have hWW : 1 ≤ (W : ℚ) * W := by nlinarith
  have hWW' : (W : ℚ) * W ≤ 2 ^ 126 := by nlinarith
  have hpos := h.toRat_pos (by linarith) (by norm_num)
  refine ⟨h.isFinite, h.onGrid.le_of_pos hpos |>.trans_eq' (by norm_num), by nlinarith,
    by nlinarith, signBit_eq_false_of_pos hpos, isZero_eq_false_iff.mpr hpos.ne'⟩

variable {bm rb cm rc : Double} {B R C S : ℚ}

-- `2.0 * th`: finite, positive, within a rounding of `2 th`, on the grid `ℤ`.
private theorem two_mul_th :
    ((2.0 : Double) * th).isFinite = true ∧ ((2.0 : Double) * th).signBit = false ∧
      ((2.0 : Double) * th).isZero = false ∧
      (1 - 1 / 2 ^ 53) * (2 * th.toRat) ≤ ((2.0 : Double) * th).toRat ∧
      OnGrid 0 ((2.0 : Double) * th).toRat := by
  obtain ⟨t1, t2, t3, -, t5, -⟩ := hS.isFinite_and_bounds_th
  have h2f : (2.0 : Double).isFinite = true := by decide +kernel
  have h2v : (2.0 : Double).toRat = 2 := by decide +kernel
  have hf := (isRounding_mul h2f t1).isFinite_of_abs_lt (by
    rw [h2v, abs_of_nonneg (by linarith)]
    calc 2 * th.toRat ≤ 2 * 2 ^ 64 := by linarith
      _ = 2 ^ 65 := (pow_succ' 2 64).symm
      _ < 2 ^ 1022 := pow_lt_pow_right₀ one_lt_two (by norm_num))
  have hg := isGridRounding_mul (k := 0) (l := 0)
    (by rw [h2v]; exact (⟨2, by norm_num⟩ : OnGrid 0 (2 : ℚ))) hS.tubeApprox.1.th.onGrid
    (by norm_num) hf
  rw [h2v] at hg
  have hr := abs_le.mp hg.abs_sub_le
  rw [abs_of_nonneg (by linarith)] at hr
  have hpos : 0 < ((2.0 : Double) * th).toRat := by linarith
  exact ⟨hf, signBit_eq_false_of_pos hpos, isZero_eq_false_iff.mpr hpos.ne', by linarith, hg.onGrid⟩

/-- The margin `err` of a cell has no sign bit, finite or not: `TUBE_EPS > 0` times a sum of
products of coefficients of `KA`, which have no sign bits, and of powers of the far corner. -/
private theorem signBit_err (hc : CellCentre bm rb cm rc B R C S H) :
    (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).signBit =
      false := by
  obtain ⟨t1, -, -, -, t5, t6⟩ := hS.isFinite_and_bounds_th
  obtain ⟨u1, -, -, -, u5, u6⟩ := hS.isFinite_and_bounds_th2
  have hε : 0 < tubeEps.toRat := lt_of_lt_of_le (by rw [tubeEpsMin_eq]; norm_num)
    tubeEpsMin_le_toRat_tubeEps
  refine signBit_mul (signBit_eq_false_of_pos hε) (signBit_foldl_add (by decide) fun jk hjk ↦ ?_)
    (.inl ⟨isFinite_tubeEps, isZero_eq_false_iff.mpr hε.ne'⟩)
  have hjk' := mem_evalIndices.mp hjk
  obtain ⟨x1, x2, y1, y2, y3⟩ :=
    hc.isFinite_and_signBit_iterate_mul_fabs_add hS.H_le (j := jk.1) (k := jk.2) (by lia) (by lia)
  refine signBit_mul ?_ y2 (.inr ⟨y1, y3⟩)
  rw [signBit_mul_of_isFinite (hS.tubeApprox.1.ka hjk').isFinite x1,
    signBit_getElem!_tubeKA t1 t6 t5 u1 u6 u5, x2]
  rfl

/-- The margins `err / th2` of `K₂` and `err / th` of `K₁` of a cell, when the margin `err` is
finite: finite, without sign bits, at most `2 ^ 1000`, and at least `20 M₂ / 2 ^ 53` and
`50 M₁ / 2 ^ 53` for the shifted absolute polynomials `M₂` of `K₂` and `M₁` of `K₁` at the corner
`(R, S)`, since `W² M₂` and `W M₁` are at most `KA` at the far corner. -/
private theorem isFinite_and_bounds_div_th2_and_div_th (hc : CellCentre bm rb cm rc B R C S H)
    (hf : (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)).isFinite =
      true) :
    ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) / th2).isFinite =
        true ∧
      20 * eval2 (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|) 2 R S / 2 ^ 53 ≤
        ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th2).toRat ∧
      ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th2).toRat ≤ 2 ^ 1000 ∧
      ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) / th).isFinite =
        true ∧
      50 * eval2 (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|) 3 R S /
          2 ^ 53 ≤
        ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th).toRat ∧
      ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th).toRat ≤ 2 ^ 1000 := by
  obtain ⟨g1, g2, g3⟩ := hS.onGrid_and_bounds_tubeEps_mul_tubeEvalGen hc hf
  obtain ⟨k0, k1⟩ := hS.eval2_kaCoeff_far_le hc
  obtain ⟨t1, t2, t3, t4, -, -⟩ := hS.isFinite_and_bounds_th
  obtain ⟨u1, u2, u3, u4, -, -⟩ := hS.isFinite_and_bounds_th2
  have hR := hc.approx_rb.nonneg
  have hS0 := hc.pos_S
  obtain ⟨-, e1, e2⟩ := eval2_abs_le_eval2_kaCoeff (kummerInit curve.coeffs) curve.coeffs a
    hS.one_le_W (show 0 ≤ |B| + R by positivity) (show 0 ≤ |C| + S by positivity)
  rw [← eval2_shift2Gen |B| |C| R S (by lia [five_le_coeffRow]) (size_coeffArray _).ge] at e1 e2
  have hn (φ : ℕ → ℕ → ℚ) (d : ℕ) := eval2_nonneg (getElem!_shift2Gen_nonneg
    (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg (φ j k)) d (abs_nonneg B) (abs_nonneg C)) d
    hR hS0.le
  have hW : (0 : ℚ) ≤ W := mod_cast (by lia [hS.one_le_W])
  obtain ⟨d1, d2, d3⟩ := div_margin hf g1 g2 g3 k1 (hn _ 2) (by rw [sq] at e2; exact e2) u1
    u2 u3 u4 (c := 20) (by norm_num)
  obtain ⟨f1, f2, f3⟩ := div_margin hf g1 g2 g3 k1 (hn _ 3) e1 t1 t2
    (t3.trans (pow_le_pow_right₀ (by norm_num) (by norm_num)))
    (t4.trans (mul_le_mul_of_nonneg_right (by norm_num) hW)) (c := 50) (by norm_num)
  exact ⟨d1, mod_cast d2, d3, f1, mod_cast f2, f3⟩

end TubeSetup

-- The arithmetic of the test `2 th hi2 < lo1` of a cell: the bound `hi` on `|k₂|`, the bound `lo`
-- on `|k₁|` with `16 M` of its margin to spare, `lo ≤ 2 M`, and the roundings of `2 th` and of
-- `2 th hi`, `th` within a rounding of `W`, give `2 W |k₂| < |k₁|`.
private theorem two_mul_abs_lt {W th x2 hi dd lo M k1 k2 : ℚ} (hW : 1 ≤ W)
    (hth : (1 - 1 / 2 ^ 53) * W ≤ th) (hx2 : (1 - 1 / 2 ^ 53) * (2 * th) ≤ x2) (hhi : 0 ≤ hi)
    (hdd : (1 - 1 / 2 ^ 53) * (x2 * hi) ≤ dd) (hlt : dd < lo) (hk2 : (1 - 1 / 2 ^ 53) * |k2| ≤ hi)
    (hk1 : lo ≤ (1 + 1 / 2 ^ 53) * (|k1| - 16 * M / 2 ^ 53)) (hlo : lo ≤ 2 * M) :
    2 * W * |k2| < |k1| := by
  have m1 := mul_le_mul_of_nonneg_left hk2 (by linarith : (0 : ℚ) ≤ W)
  have m2 := mul_le_mul_of_nonneg_right hx2 hhi
  have m3 := mul_le_mul_of_nonneg_right hth hhi
  have hWh : 0 ≤ W * hi := mul_nonneg (by linarith) hhi
  have e2 : (1 - 1 / 2 ^ 53 : ℚ) * (2 * th) * hi = 2 * (1 - 1 / 2 ^ 53) * (th * hi) := by ring
  rw [e2] at m2
  have e3 : (1 - 1 / 2 ^ 53 : ℚ) * W * hi = (1 - 1 / 2 ^ 53) * (W * hi) := by ring
  rw [e3] at m3
  have e1 : W * ((1 - 1 / 2 ^ 53 : ℚ) * |k2|) = (1 - 1 / 2 ^ 53) * (W * |k2|) := by ring
  rw [e1] at m1
  linarith

namespace TubeSetup

variable {kd : TubeCoeffs} {curve : SearchCurve} {H W : ℤ} {th th2 : Double} {a : ℤ}
  (hS : TubeSetup kd curve H W th th2 a) {bm rb cm rc : Double} {B R C S : ℚ}
  (hc : CellCentre bm rb cm rc B R C S H)
include hS hc

-- The shifted absolute polynomials at the corner `(R, S)`: those of `K₂` times `W²`, of `K₁`
-- times `W` and the combination of `Q(±W)` at most `KA` at the far corner, below `2 ^ 998`.
private theorem corner_le :
    W ^ 2 * eval2 (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|) 2 R S < 2 ^ 998 ∧
      W * eval2 (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|) 3 R S <
        2 ^ 998 ∧
      eval2 (combineCoeffs W (W * W)
        (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
        (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|)
        (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 R S < 2 ^ 998 := by
  have hR := hc.approx_rb.nonneg
  have hS0 := hc.pos_S
  obtain ⟨-, e1, e2⟩ := eval2_abs_le_eval2_kaCoeff (kummerInit curve.coeffs) curve.coeffs a
    hS.one_le_W (show 0 ≤ |B| + R by positivity) (show 0 ≤ |C| + S by positivity)
  have hk := (hS.eval2_kaCoeff_far_le hc).2
  rw [eval2_shift2Gen _ _ _ _ (by lia [five_le_coeffRow]) (size_coeffArray _).ge,
    eval2_shift2Gen _ _ _ _ (by lia [five_le_coeffRow]) (size_coeffArray _).ge,
    eval2_combineCoeffs_abs]
  exact ⟨e2.trans_lt hk, e1.trans_lt hk, hk⟩

-- The shifted absolute polynomials of `K₂` and `K₁` at the corner `(R, S)`: at most `2 ^ 1000`.
private theorem le_pow_k :
    eval2 (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|) 2 R S ≤ 2 ^ 1000 ∧
      eval2 (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|) 3 R S ≤
        2 ^ 1000 := by
  have hW : (1 : ℚ) ≤ W := mod_cast hS.one_le_W
  have hn (φ : ℕ → ℕ → ℚ) (d : ℕ) := eval2_nonneg (getElem!_shift2Gen_nonneg
    (nonneg_getElem!_coeffArray fun j k ↦ abs_nonneg (φ j k)) d (abs_nonneg B) (abs_nonneg C)) d
    hc.approx_rb.nonneg hc.pos_S.le
  obtain ⟨c2, c1, -⟩ := hS.corner_le hc
  exact ⟨((le_mul_of_one_le_left (hn _ 2) (one_le_pow₀ hW)).trans_lt c2).le.trans
      (pow_le_pow_right₀ one_le_two (by norm_num)),
    ((le_mul_of_one_le_left (hn _ 3) hW).trans_lt c1).le.trans
      (pow_le_pow_right₀ one_le_two (by norm_num))⟩

/-- The call `poly_sign(q, 4, rp, err)` of the analysis of a cell for `Q(w)`, `w = ±W`, has the
setting of `JPoints.Double.PolySignSetup`. -/
theorem polySignSetup_combine {q : Array Double} {w : ℚ}
    (hq : ApproxCoeffs q (combineCoeffs w (W * W)
          (shift2Gen (coeffArray (k0Coeff (kummerInit curve.coeffs) a)) 4 B C)
          (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
          (shift2Gen (coeffArray (k2Coeff a)) 2 B C))
        (combineCoeffs W (W * W)
          (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 24 75) :
    PolySignSetup q (combineCoeffs w (W * W)
          (shift2Gen (coeffArray (k0Coeff (kummerInit curve.coeffs) a)) 4 B C)
          (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
          (shift2Gen (coeffArray (k2Coeff a)) 2 B C))
        (combineCoeffs W (W * W)
          (shift2Gen (coeffArray fun j k ↦ |k0Coeff (kummerInit curve.coeffs) a j k|) 4 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|)
          (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|)) 4 24 75
      (cellProducts rb rc) R S
      (tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) 0 where
  approx := hq
  deg_le := le_rfl
  grid_le := by norm_num
  count_le := by norm_num
  gamma_le := by norm_num
  rp_approx h := hc.rp_approx hS.H_le h
  rp_signBit h := hc.rp_signBit hS.H_le h
  nonneg_R := hc.approx_rb.nonneg
  nonneg_S := hc.pos_S.le
  le_pow := (hS.corner_le hc).2.2.le.trans (pow_le_pow_right₀ one_le_two (by norm_num))
  signBit_e := hS.signBit_err hc
  margin hf := by
    obtain ⟨-, g2, g3⟩ := hS.onGrid_and_bounds_tubeEps_mul_tubeEvalGen hc hf
    obtain ⟨k0, k1⟩ := hS.eval2_kaCoeff_far_le hc
    rw [eval2_combineCoeffs_abs, show (evalIndices 4).length = 15 by decide]
    refine ⟨by push_cast; linarith, ?_⟩
    have : (2 : ℚ) ^ 1000 = 4 * 2 ^ 998 := by rw [show 1000 = 2 + 998 from rfl, pow_add]; norm_num
    rw [this]
    generalize (2 : ℚ) ^ 998 = T at k1
    linarith

/-- The call `poly_sign(p2, 2, rp, err / th2)` of the analysis of a cell for `K₂` has the setting
of `JPoints.Double.PolySignSetup`. -/
theorem polySignSetup_k2 :
    PolySignSetup (shift2Gen (tubeK2 kd a) 2 bm cm) (shift2Gen (coeffArray (k2Coeff a)) 2 B C)
      (shift2Gen (coeffArray fun j k ↦ |k2Coeff a j k|) 2 |B| |C|) 2 9 9 (cellProducts rb rc) R S
      ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) / th2) 0 where
  approx := (hS.approxCoeffs_shift2Gen hc).2.2.mono (by norm_num) le_rfl le_rfl
  deg_le := by norm_num
  grid_le := by norm_num
  count_le := by norm_num
  gamma_le := by norm_num
  rp_approx h := hc.rp_approx hS.H_le (by lia)
  rp_signBit h := hc.rp_signBit hS.H_le (by lia)
  nonneg_R := hc.approx_rb.nonneg
  nonneg_S := hc.pos_S.le
  le_pow := (hS.le_pow_k hc).1
  signBit_e := by
    obtain ⟨u1, -, -, -, u5, u6⟩ := hS.isFinite_and_bounds_th2
    exact signBit_div (hS.signBit_err hc) u5 u1 u6
  margin hf := by
    obtain ⟨-, d2, d3, -⟩ :=
      hS.isFinite_and_bounds_div_th2_and_div_th hc (isFinite_of_isFinite_div hf)
    rw [show (evalIndices 2).length = 6 by decide]
    exact ⟨by push_cast; linarith, d3⟩

/-- The call `poly_sign(p1, 3, rp, err / th)` of the analysis of a cell for `K₁` has the setting
of `JPoints.Double.PolySignSetup`, with `16 M₁ / 2 ^ 53` of the margin to spare. -/
theorem polySignSetup_k1 :
    PolySignSetup (shift2Gen (tubeK1 kd a) 3 bm cm)
      (shift2Gen (coeffArray (k1Coeff curve.coeffs a)) 3 B C)
      (shift2Gen (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 3 |B| |C|) 3 18 71
      (cellProducts rb rc) R S
      ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) / th) 16 where
  approx := (hS.approxCoeffs_shift2Gen hc).2.1.mono (by norm_num) le_rfl le_rfl
  deg_le := by norm_num
  grid_le := by norm_num
  count_le := by norm_num
  gamma_le := by norm_num
  rp_approx h := hc.rp_approx hS.H_le (by lia)
  rp_signBit h := hc.rp_signBit hS.H_le (by lia)
  nonneg_R := hc.approx_rb.nonneg
  nonneg_S := hc.pos_S.le
  le_pow := (hS.le_pow_k hc).2
  signBit_e := by
    obtain ⟨t1, -, -, -, t5, t6⟩ := hS.isFinite_and_bounds_th
    exact signBit_div (hS.signBit_err hc) t5 t1 t6
  margin hf := by
    obtain ⟨-, -, -, -, d2, d3⟩ :=
      hS.isFinite_and_bounds_div_th2_and_div_th hc (isFinite_of_isFinite_div hf)
    rw [show (evalIndices 3).length = 10 by decide]
    exact ⟨by push_cast; linarith, d3⟩

end TubeSetup

namespace TubeSetup

variable {kd : TubeCoeffs} {curve : SearchCurve} {H W : ℤ} {th th2 : Double} {a : ℤ}
  (hS : TubeSetup kd curve H W th th2 a) {bm rb cm rc : Double} {B R C S : ℚ}
  (hc : CellCentre bm rb cm rc B R C S H)
include hS hc

/-- The test `2 th hi2 < lo1` of `tube_cell` on a cell: `|k₁| > 2 W |k₂|` throughout the cell, for
the bound `hi2` of `poly_sign` on `k₂` and its bound `lo1` on `k₁`. -/
theorem two_mul_abs_lt_of_lt (hlt : ((2.0 : Double) * th *
      (polySign (shift2Gen (tubeK2 kd a) 2 bm cm) 2 (cellProducts rb rc)
        ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th2)).run.2.2).lt
      (polySign (shift2Gen (tubeK1 kd a) 3 bm cm) 3 (cellProducts rb rc)
        ((tubeEps * tubeEvalGen (tubeKA kd th th2 a) 4 (bm.fabs + rb) (cm.fabs + rc)) /
          th)).run.2.1 = true)
    {b c : ℤ} (hb : |(b : ℚ) - B| ≤ R) (hcc : |(c : ℚ) - C| ≤ S) :
    2 * W * |(kummerK2 a b c : ℚ)| < |(kummerK1 (curve.coeffs.toList.getD · 0) a b c : ℚ)| := by
  have P2 := hS.polySignSetup_k2 hc
  have P1 := hS.polySignSetup_k1 hc
  obtain ⟨x1, x2, x3, x4, x5⟩ := hS.two_mul_th
  have hds := signBit_mul x2 P2.signBit_hi (.inl ⟨x1, x3⟩)
  have hlo := zero_lt_of_lt hds hlt
  have hdf := isFinite_of_lt hds (P1.isFinite_lo hlo) hlt
  have hB := P2.abs_eval2_le (isFinite_and_of_isFinite_mul hdf).2 hb hcc
  have hC1 := P1.lo_le_abs_eval2 hlo hb hcc
  rw [eval2_shift2Gen_k2Coeff] at hB
  rw [eval2_shift2Gen_k1Coeff] at hC1
  have hh0 := toRat_nonneg P2.signBit_hi
  have hth := (abs_le.mp hS.tubeApprox.1.th.abs_sub_le).1
  rw [pow_one] at hth
  exact two_mul_abs_lt (mod_cast hS.one_le_W) (by linarith) x4 hh0
    (one_sub_mul_le_toRat_mul x5 hdf (by linarith [x4, (hS.isFinite_and_bounds_th).2.1]) hh0)
    ((lt_iff_toRat_lt hdf (P1.isFinite_lo hlo)).mp hlt) hB hC1 (P1.lo_le_two_mul hlo)

/-- A cell that the analysis of the tube finds out holds no root in `[-W, W]` of the Kummer
quadratic of any of its triples: `Q(W)` and `Q(-W)` have the same strict sign throughout, and
either `k₂` has the other sign throughout or `|k₁| > 2 W |k₂|` throughout
(`quadratic_ne_zero_of_abs_le`). -/
theorem not_root_of_tubeCellAnalyzeGen {t : TubeState} (h0 : t.k0 = tubeK0 kd a)
    (h1 : t.k1 = tubeK1 kd a) (h2 : t.k2 = tubeK2 kd a) (hka : t.ka = tubeKA kd th th2 a)
    (hout : (tubeCellAnalyzeGen th th2 t (cellProducts rb rc) bm rb cm rc).2 = true) {b c : ℤ}
    (hb : |(b : ℚ) - B| ≤ R) (hcc : |(c : ℚ) - C| ≤ S) {x : ℚ} (hx : |x| ≤ W) :
    (kummerK2 a b c : ℚ) * (x * x) + kummerK1 (curve.coeffs.toList.getD · 0) a b c * x +
      kummerK0 (curve.coeffs.toList.getD · 0) a b c ≠ 0 := by
  simp only [tubeCellAnalyzeGen, h0, h1, h2, hka, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hout
  obtain ⟨⟨⟨hsp, hsm⟩, heq⟩, hk⟩ := hout
  have hc2 := hS.approxCoeffs_tubeCellCombine hc
  have hQ := ((hS.polySignSetup_combine hc hc2.1).mul_pos_eval2 hsp).2 hb hcc
  have hM := ((hS.polySignSetup_combine hc hc2.2).mul_pos_eval2 hsm).2 hb hcc
  rw [eval2_combineCoeffs_shift2Gen] at hQ hM
  rw [← heq] at hM
  refine quadratic_ne_zero_of_abs_le hQ (by linear_combination hM) ?_ hx
  rcases hk with ⟨hs2, hs2p⟩ | hk
  · have h22 := ((hS.polySignSetup_k2 hc).mul_pos_eval2 hs2).2 hb hcc
    rw [eval2_shift2Gen_k2Coeff] at h22
    left
    rcases fst_polySign_eq hsp with e1 | e1 <;> rcases fst_polySign_eq hs2 with e2 | e2
    · exact absurd (e2.trans e1.symm) hs2p
    · rw [e1]; rw [e2] at h22; push_cast at h22 ⊢; linarith
    · rw [e1]; rw [e2] at h22; push_cast at h22 ⊢; linarith
    · exact absurd (e2.trans e1.symm) hs2p
  · exact .inr (hS.two_mul_abs_lt_of_lt hc hk hb hcc)

end TubeSetup

end JPoints

end
