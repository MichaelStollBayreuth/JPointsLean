/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Sturm
public import JPoints.Spec.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Data.List.SignVariations
public import Std.WP

import JPoints.Mathlib.Algebra.BigOperators.Ring.Finset
import JPoints.Mathlib.Algebra.Polynomial.Sturm.Sequence
import JPoints.Proof.Containers
import JPoints.Proof.Poly
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The Sturm chain of `real_roots_init`

The contracts of the Sturm chain of `real_roots_init` and of the counts of its sign changes: the
rows of the flat array of the chain hold polynomials over `ℚ` (`JPoints.rowPoly`) of the degrees
that the chain records (`JPoints.RowDegree`); `JPoints.realRootsStart` starts the chain with `f` and
`f'` (`JPoints.realRootsStart_spec`), `JPoints.realRootsReduce` replaces a row by its remainder
modulo an earlier one (`JPoints.realRootsReduce_spec`), and `JPoints.realRootsChain` completes the
chain (`JPoints.realRootsChain_spec`), each row from the third on the negated remainder of the two
before it, until the last is a nonzero constant or the next remainder is zero
(`JPoints.SturmChain.WF`), so that the rows are Mathlib's `Polynomial.sturmSeq` of `f` and `f'`
(`JPoints.SturmChain.IsFinished.map_rowPoly_eq_sturmSeq`); and `JPoints.sturmChanges` counts the
sign variations of the values of the rows at a rational number by Horner's rule
(`JPoints.sturmChanges_spec`, `List.signVariations`).

## Main definitions

* `JPoints.rowPoly`, `JPoints.RowDegree`: the polynomial of a row and its degree.
* `JPoints.SturmChain.WF`: a Sturm chain of `f` as far as it is built.
* `JPoints.ReducePre`, `JPoints.ReducePost`: what `JPoints.realRootsReduce` needs and leaves.
* `JPoints.StartRowInvariant`, `JPoints.StartDerivInvariant`, `JPoints.ReduceInvariant`,
  `JPoints.SubtractRowInvariant`, `JPoints.DescentRowInvariant`, `JPoints.ChainInvariant`,
  `JPoints.CopyRowInvariant`, `JPoints.NegateRowInvariant`, `JPoints.HornerRowInvariant`,
  `JPoints.ChangesInvariant`: the invariants of the loops.

## Main statements

* `JPoints.realRootsStart_spec`, `JPoints.realRootsReduce_spec`, `JPoints.realRootsChain_spec`:
  the chain.
* `JPoints.SturmChain.IsFinished.map_rowPoly_eq_sturmSeq`: the finished chain is the Sturm sequence.
* `JPoints.sturmChanges_spec`: the count of the sign changes.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. Each loop has a named
invariant, irreducible in the proof of its contract, and each verification condition is discharged
by a lemma in its own shape. The row `i` of the array `sturm[7][7]` of the C code is the slice
`[7 i, 7 i + 7)` of the flat array of the model; the rows other than the one that a loop writes are
kept by frame conditions on the indices outside its slice.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

open Polynomial

/-! ### The coefficient arrays -/

private theorem getElem!_eq_zero_of_degree_lt {coeffs : Array ℤ} {deg : ℕ}
    (hd : degree coeffs.toList = deg) {k : ℕ} (hk : deg < k) : coeffs[k]! = 0 := by
  rw [← Array.getD_toList_eq_getElem!]
  exact getD_eq_zero_of_degree_lt (hd ▸ hk)

theorem getElem!_degree_ne_zero {coeffs : Array ℤ} {deg : ℕ} (hd : degree coeffs.toList = deg)
    (h0 : 0 < deg) : coeffs[deg]! ≠ 0 := by
  rw [← Array.getD_toList_eq_getElem!, ← hd]
  exact getD_degree_ne_zero (hd ▸ h0)

private theorem degree_lt_size {coeffs : Array ℤ} {deg : ℕ} (hd : degree coeffs.toList = deg)
    (h0 : 0 < deg) : deg < coeffs.size := by
  lia [hd ▸ degree_le_length_sub_one coeffs.toList, Array.length_toList (xs := coeffs)]

private theorem degree_lt_seven {coeffs : Array ℤ} {deg : ℕ}
    (h : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) : deg < 7 := by
  lia [h.2.1 ▸ degree_toList_le_six h.1]

/-! ### The rows of the chain as polynomials -/

/-- The polynomial over `ℚ` that the row `i` of the flat array `s` of the Sturm chain holds: the
coefficient of `X ^ k` at the index `7 i + k`, for `k < 7`. -/
noncomputable def rowPoly (s : Array ℚ) (i : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range 7, C s[i * 7 + k]! * X ^ k

private theorem coeff_rowPoly (s : Array ℚ) (i k : ℕ) :
    (rowPoly s i).coeff k = if k < 7 then s[i * 7 + k]! else 0 := by
  simp only [rowPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]

private theorem rowPoly_congr {s s' : Array ℚ} {i j : ℕ}
    (h : ∀ k < 7, s[i * 7 + k]! = s'[j * 7 + k]!) :
    rowPoly s i = rowPoly s' j :=
  Finset.sum_congr rfl fun k hk ↦ by rw [h k (Finset.mem_range.mp hk)]

/-- The row `i` of the flat array `s` of the Sturm chain holds a polynomial of degree `d`, as
`real_roots_init` keeps them: the entries of the row above the index `d` are zero and the entry at
`d` is not; `d = -1` for the zero polynomial. -/
structure RowDegree (s : Array ℚ) (i : ℕ) (d : ℤ) : Prop where
  /-- The degree is `-1` or more. -/
  neg_one_le : -1 ≤ d
  /-- The degree is at most `6`. -/
  lt_seven : d < 7
  /-- The entries above the degree are zero. -/
  getElem!_eq_zero {k : ℕ} (h : d < k) (hk : k < 7) : s[i * 7 + k]! = 0
  /-- The leading coefficient is not zero. -/
  getElem!_ne_zero (h : 0 ≤ d) : s[i * 7 + d.toNat]! ≠ 0

private theorem RowDegree.coeff_eq_zero {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d) {k : ℕ}
    (hk : d < k) : (rowPoly s i).coeff k = 0 := by
  rw [coeff_rowPoly]
  split_ifs with h7
  · exact h.getElem!_eq_zero hk h7
  · rfl

private theorem RowDegree.rowPoly_eq_zero {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d)
    (hd : d < 0) : rowPoly s i = 0 :=
  Polynomial.ext fun k ↦ by rw [h.coeff_eq_zero (by lia), coeff_zero]

private theorem RowDegree.natDegree_eq {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d)
    (hd : 0 ≤ d) : (rowPoly s i).natDegree = d.toNat := by
  refine natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ h.coeff_eq_zero (by lia)) ?_
  rw [coeff_rowPoly, ite_eq_left (by lia [h.lt_seven])]
  exact h.getElem!_ne_zero hd

private theorem RowDegree.rowPoly_ne_zero {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d)
    (hd : 0 ≤ d) : rowPoly s i ≠ 0 := fun h0 ↦ by
  have := coeff_rowPoly s i d.toNat
  rw [h0, coeff_zero, ite_eq_left (by lia [h.lt_seven])] at this
  exact h.getElem!_ne_zero hd this.symm

private theorem RowDegree.degree_eq {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d)
    (hd : 0 ≤ d) : (rowPoly s i).degree = d.toNat := by
  rw [degree_eq_natDegree (h.rowPoly_ne_zero hd), h.natDegree_eq hd]

private theorem RowDegree.degree_lt {s s' : Array ℚ} {i i' : ℕ} {d d' : ℤ} (h : RowDegree s i d)
    (h' : RowDegree s' i' d') (hd : d < d') : (rowPoly s i).degree < (rowPoly s' i').degree := by
  rw [h'.degree_eq (by lia [h.neg_one_le])]
  rcases lt_or_ge d 0 with hd0 | hd0
  · rw [h.rowPoly_eq_zero hd0, degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [h.degree_eq hd0]
    exact_mod_cast (show d.toNat < d'.toNat by lia)

/-- The degree of a row is that of every row with the same entries. -/
private theorem RowDegree.of_getElem!_eq {s s' : Array ℚ} {i i' : ℕ} {d : ℤ} (h : RowDegree s i d)
    (hs : ∀ k < 7, s'[i' * 7 + k]! = s[i * 7 + k]!) : RowDegree s' i' d where
  neg_one_le := h.neg_one_le
  lt_seven := h.lt_seven
  getElem!_eq_zero hk hk7 := (hs _ hk7).trans (h.getElem!_eq_zero hk hk7)
  getElem!_ne_zero h0 := by
    rw [hs _ (by lia [h.lt_seven])]
    exact h.getElem!_ne_zero h0


/-! ### The Sturm chain -/

/-- The Sturm chain `ch` of `real_roots_init` for the polynomial `f`, as far as it is built: a flat
array of seven rows of seven rationals, the degrees in an array of seven, at least the two
polynomials `f` and `f'`, each row a polynomial of its degree (`JPoints.RowDegree`), the degrees
strictly decreasing and the row `i` of degree at most `6 - i`, and each row from the third on the
negated remainder of the two before it, as in Mathlib's `Polynomial.sturmSeq`. -/
structure SturmChain.WF (f : ℚ[X]) (ch : SturmChain) : Prop where
  /-- The array of the coefficients has seven rows of seven. -/
  size_sturm : ch.sturm.size = 49
  /-- The array of the degrees has seven entries. -/
  size_deg : ch.deg.size = 7
  /-- The chain has at least two polynomials. -/
  two_le_len : 2 ≤ ch.len
  /-- Each row holds a polynomial of its degree. -/
  rowDegree {i : ℕ} (hi : i < ch.len) : RowDegree ch.sturm i ch.deg[i]!
  /-- The row `i` has a degree of at most `6 - i`. -/
  deg_add_lt {i : ℕ} (hi : i < ch.len) : ch.deg[i]! + i < 7
  /-- The degrees decrease strictly. -/
  deg_lt {i : ℕ} (hi : i + 1 < ch.len) : ch.deg[i + 1]! < ch.deg[i]!
  /-- The first row is `f`. -/
  rowPoly_zero : rowPoly ch.sturm 0 = f
  /-- The second row is `f'`. -/
  rowPoly_one : rowPoly ch.sturm 1 = derivative f
  /-- Each row from the third on is the negated remainder of the two before it. -/
  rowPoly_add_two {i : ℕ} (hi : i + 2 < ch.len) :
    rowPoly ch.sturm (i + 2) = -rowPoly ch.sturm i % rowPoly ch.sturm (i + 1)

/-- A finished Sturm chain of `f`, as `real_roots_init` leaves it (`JPoints.realRootsChain_spec`):
well formed, and the negated remainder of its last two polynomials zero, so that it is the Sturm
sequence of `f` and `f'` (`JPoints.SturmChain.IsFinished.map_rowPoly_eq_sturmSeq`). -/
structure SturmChain.IsFinished (f : ℚ[X]) (ch : SturmChain) : Prop extends SturmChain.WF f ch where
  /-- The negated remainder of the last two polynomials is zero. -/
  neg_mod_eq_zero : -rowPoly ch.sturm (ch.len - 2) % rowPoly ch.sturm (ch.len - 1) = 0

/-- The invariant of the first loop of `JPoints.realRootsStart`, which copies the coefficients
`coeffs` into the first row: after `k` steps, the entries below `k` are the coefficients, the
others zero. -/
def StartRowInvariant (coeffs : Array ℤ) : Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ s ↦ s.size = 49 ∧ ∀ n : ℕ, s[n]! = if n < pref.length then (coeffs[n]! : ℚ) else 0

/-- The invariant of the second loop of `JPoints.realRootsStart`, which writes the coefficients of
the derivative of the polynomial of degree `deg` with the coefficients `coeffs` into the second
row: after `k` steps, the first row holds the coefficients, the entries `7 + j` for `j < k` those
of the derivative, the others zero. -/
def StartDerivInvariant (coeffs : Array ℤ) (deg : ℕ) : Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ s ↦ s.size = 49 ∧ ∀ n : ℕ, s[n]! = if n < deg + 1 then (coeffs[n]! : ℚ) else
    if 7 ≤ n ∧ n < 7 + pref.length then (coeffs[n - 6]! : ℚ) * (n - 6 : ℕ) else 0

private theorem startRowInvariant_nil (coeffs : Array ℤ) (suff : List ℕ) :
    StartRowInvariant coeffs [] suff (Array.replicate 49 0) :=
  ⟨by simp, fun n ↦ Array.getElem!_replicate_default 49 n⟩

private theorem StartRowInvariant.append_singleton {coeffs : Array ℤ} {deg : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (h : ForIn.toList [:deg + 1] = pref ++ cur :: suff) (hd : deg < 7) {s : Array ℚ}
    (hinv : StartRowInvariant coeffs pref (cur :: suff) s) :
    StartRowInvariant coeffs (pref ++ [cur]) suff (s.set! cur (coeffs[cur]! : ℚ)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  obtain ⟨hsize, hp⟩ := hinv
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  have := hp n
  grind

private theorem startDerivInvariant_nil {coeffs : Array ℤ} {deg : ℕ} {s : Array ℚ}
    (h : StartRowInvariant coeffs (ForIn.toList [:deg + 1]) [] s) (suff : List ℕ) :
    StartDerivInvariant coeffs deg [] suff s := by
  obtain ⟨hsize, hp⟩ := h
  refine ⟨hsize, fun n ↦ ?_⟩
  rw [hp n, Std.Legacy.Range.length_toList]
  grind

private theorem StartDerivInvariant.append_singleton {coeffs : Array ℤ} {deg : ℕ}
    {pref suff : List ℕ}
    {cur : ℕ} (h : ForIn.toList [1:deg + 1] = pref ++ cur :: suff) (hd : deg < 7) {s : Array ℚ}
    (hinv : StartDerivInvariant coeffs deg pref (cur :: suff) s) :
    StartDerivInvariant coeffs deg (pref ++ [cur]) suff
      (s.set! (7 + (cur - 1)) ((coeffs[cur]! : ℚ) * (cur : ℚ))) := by
  obtain rfl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  obtain ⟨hsize, hp⟩ := hinv
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  rw [Nat.add_sub_cancel_left]
  rcases eq_or_ne (7 + pref.length) n with rfl | hn
  · rw [Array.getElem!_set!_self _ _ _ (by lia)]
    simp only [List.length_append, List.length_singleton]
    rw [ite_eq_right (by lia), ite_eq_left ⟨by lia, by lia⟩,
      show 7 + pref.length - 6 = 1 + pref.length by lia]
  · rw [Array.getElem!_set!_ne _ _ _ _ hn, hp n]
    grind
private theorem StartDerivInvariant.getElem!_eq {coeffs : Array ℤ} {deg : ℕ} {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) (n : ℕ) :
    s[n]! = if n < deg + 1 then (coeffs[n]! : ℚ) else
      if 7 ≤ n ∧ n < 7 + deg then (coeffs[n - 6]! : ℚ) * (n - 6 : ℕ) else 0 := by
  rw [h.2 n, Std.Legacy.Range.length_toList, Nat.add_sub_cancel]

private theorem StartDerivInvariant.getElem!_zero_mul_add {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) {k : ℕ} (hk : k < 7) :
    s[0 * 7 + k]! = coeffs[k]! := by
  rw [h.getElem!_eq, zero_mul, zero_add]
  split_ifs with h1 h2
  · rfl
  · lia
  · rw [getElem!_eq_zero_of_degree_lt hpre.2.1 (by lia), Int.cast_zero]

private theorem StartDerivInvariant.getElem!_one_mul_add {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) (k : ℕ) :
    s[1 * 7 + k]! = coeffs[k + 1]! * (k + 1) := by
  rw [h.getElem!_eq, ite_eq_right (by lia [degree_lt_seven hpre])]
  split_ifs with h2
  · rw [show 1 * 7 + k - 6 = k + 1 by lia]
    push_cast
    rfl
  · rw [getElem!_eq_zero_of_degree_lt hpre.2.1 (by lia), Int.cast_zero, zero_mul]

private theorem StartDerivInvariant.rowDegree_zero {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) :
    RowDegree s 0 deg := by
  have hlt := degree_lt_seven hpre
  refine ⟨by lia, by lia, fun {k} hk hk7 ↦ ?_, fun _ ↦ ?_⟩
  · rw [h.getElem!_zero_mul_add hpre hk7, getElem!_eq_zero_of_degree_lt hpre.2.1 (by lia),
      Int.cast_zero]
  · rw [Int.toNat_natCast, h.getElem!_zero_mul_add hpre hlt]
    exact_mod_cast getElem!_degree_ne_zero hpre.2.1 hpre.2.2

private theorem StartDerivInvariant.rowDegree_one {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) :
    RowDegree s 1 (deg - 1 : ℕ) := by
  have hlt := degree_lt_seven hpre
  refine ⟨by lia, by lia, fun {k} hk hk7 ↦ ?_, fun _ ↦ ?_⟩
  · rw [h.getElem!_one_mul_add hpre k, getElem!_eq_zero_of_degree_lt hpre.2.1 (by lia),
      Int.cast_zero, zero_mul]
  · rw [Int.toNat_natCast, h.getElem!_one_mul_add hpre _, Nat.sub_add_cancel hpre.2.2]
    exact mul_ne_zero (mod_cast getElem!_degree_ne_zero hpre.2.1 hpre.2.2)
      (by have := hpre.2.2; positivity)

private theorem StartDerivInvariant.rowPoly_zero {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) :
    rowPoly s 0 = poly coeffs.toList := by
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_rowPoly, coeff_poly, Array.getD_toList_eq_getElem!]
  split_ifs with hk
  · exact h.getElem!_zero_mul_add hpre hk
  · rw [getElem!_neg coeffs k (by lia)]
    rfl

private theorem StartDerivInvariant.rowPoly_one {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) :
    rowPoly s 1 = derivative (poly coeffs.toList) := by
  have hlt := degree_lt_seven hpre
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_rowPoly, coeff_derivative, coeff_poly, Array.getD_toList_eq_getElem!]
  split_ifs with hk
  · exact h.getElem!_one_mul_add hpre k
  · rw [getElem!_eq_zero_of_degree_lt hpre.2.1 (by lia), Int.cast_zero, zero_mul]

/-- After the two loops of `JPoints.realRootsStart`, the chain holds the polynomial `f` of degree
`deg ≥ 1` with the seven coefficients `coeffs` and its derivative. -/
private theorem StartDerivInvariant.wf {coeffs : Array ℤ} {deg : ℕ}
    (hpre : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg) {s : Array ℚ}
    (h : StartDerivInvariant coeffs deg (ForIn.toList [1:deg + 1]) [] s) :
    SturmChain.WF (poly coeffs.toList) ⟨s, #[deg, deg - 1, 0, 0, 0, 0, 0], 2⟩ := by
  have hlt := degree_lt_seven hpre
  refine ⟨h.1, rfl, le_rfl, fun {i} hi ↦ ?_, fun {i} hi ↦ ?_, fun {i} hi ↦ ?_,
    h.rowPoly_zero hpre, h.rowPoly_one hpre, by simp⟩
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by change i < 2 at hi; lia
    · exact h.rowDegree_zero hpre
    · exact h.rowDegree_one hpre
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by change i < 2 at hi; lia
    · change deg + 0 < 7; lia
    · change deg - 1 + 1 < 7; lia
  · obtain rfl : i = 0 := by change i + 1 < 2 at hi; lia
    change deg - 1 < deg; lia [hpre.2.2]

attribute [local irreducible] StartRowInvariant StartDerivInvariant in
/-- `JPoints.realRootsStart` starts the Sturm chain of the polynomial `f` with the seven
coefficients `coeffs` of degree `deg ≥ 1` with `f` and `f'`. -/
@[spec]
theorem realRootsStart_spec (coeffs : Array ℤ) (deg : ℕ) :
    ⦃ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg ⦄ realRootsStart coeffs deg
    ⦃ fun r ↦ r.WF (poly coeffs.toList) ⦄ := by
  vcgen [realRootsStart] invariants
  | inv1 => StartRowInvariant coeffs
  | inv2 => StartDerivInvariant coeffs deg
  all_goals with_reducible first
    | exact startRowInvariant_nil _ _
    | exact StartRowInvariant.append_singleton ‹_› (degree_lt_seven ‹_›) ‹_›
    | exact startDerivInvariant_nil ‹_› _
    | exact StartDerivInvariant.append_singleton ‹_› (degree_lt_seven ‹_›) ‹_›
    | exact StartDerivInvariant.wf ‹_› ‹_›

/-! ### The remainder -/

/-- What `JPoints.realRootsReduce` needs of the chain `ch` and the rows `i1 < i2 < 7`: an array of
`49` rationals, the divisor in the row `i1` of the degree `ch.deg[i1]` that the chain records, and
the dividend in the row `i2` of degree `d`. -/
structure ReducePre (ch : SturmChain) (i1 i2 : ℕ) (d : ℤ) : Prop where
  /-- The array has seven rows of seven. -/
  size_sturm : ch.sturm.size = 49
  /-- The divisor lies in a row before the dividend. -/
  lt : i1 < i2
  /-- The dividend lies in one of the seven rows. -/
  lt_seven : i2 < 7
  /-- The divisor has the degree that the chain records. -/
  rowDegree_divisor : RowDegree ch.sturm i1 ch.deg[i1]!
  /-- The dividend has the degree `d`. -/
  rowDegree_dividend : RowDegree ch.sturm i2 d

/-- What `JPoints.realRootsReduce` leaves for the chain `ch` and the rows `i1 < i2`: the chain
`ch'` with the remainder of the dividend in the row `i2` modulo the divisor in the row `i1`, of the
degree `d` below that of the divisor, and the other rows, the degrees and the length of `ch`. -/
structure ReducePost (ch : SturmChain) (i1 i2 : ℕ) (ch' : SturmChain) (d : ℤ) : Prop where
  /-- The degrees are unchanged. -/
  deg_eq : ch'.deg = ch.deg
  /-- The length is unchanged. -/
  len_eq : ch'.len = ch.len
  /-- The array has seven rows of seven. -/
  size_sturm : ch'.sturm.size = 49
  /-- The rows other than `i2` are unchanged. -/
  getElem!_eq {n : ℕ} (hn : n < i2 * 7 ∨ i2 * 7 + 7 ≤ n) : ch'.sturm[n]! = ch.sturm[n]!
  /-- The remainder has the degree `d`. -/
  rowDegree : RowDegree ch'.sturm i2 d
  /-- The degree of the remainder is below that of the divisor. -/
  lt : d < ch.deg[i1]!
  /-- The row `i2` holds the remainder. -/
  rowPoly_eq : rowPoly ch'.sturm i2 = rowPoly ch.sturm i2 % rowPoly ch.sturm i1

/-- The invariant of the outer loop of `JPoints.realRootsReduce` for the chain `ch` and the rows
`i1` (the divisor) and `i2` (the dividend), at the array `s` and the degree `d`: the row `i2`
holds a polynomial of degree `d` that differs from the dividend by a multiple of the divisor, the
other rows unchanged; after the loop, `d` is below the degree of the divisor. -/
def ReduceInvariant (ch : SturmChain) (i1 i2 : ℕ) :
    Std.WP.WhileInvariant (Array ℚ × ℤ) Prop :=
  .mk fun exit (s, d) ↦ s.size = 49 ∧ RowDegree s i2 d ∧
    (∀ n, n < i2 * 7 ∨ i2 * 7 + 7 ≤ n → s[n]! = ch.sturm[n]!) ∧
    (∃ Q, rowPoly s i2 = rowPoly ch.sturm i2 - Q * rowPoly ch.sturm i1) ∧
    (exit = true → d < ch.deg[i1]!)

/-- The invariant of the loop of `JPoints.realRootsReduce` that subtracts `q xᵉ` times the row `i1`
of degree `d1` from the row `i2` of degree `d` of the array `s`, for the quotient
`q = s[7 i2 + d] / s[7 i1 + d1]` of the leading coefficients and `e = d - d1`: after `k` steps,
the array `p` is `s` with `q s[7 i1 + j]` subtracted from the entry `7 i2 + e + j` for each
`j < k`. -/
def SubtractRowInvariant (s : Array ℚ) (i1 i2 : ℕ) (d : ℤ) (d1 : ℕ) :
    Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ p ↦ p.size = 49 ∧ ∀ n : ℕ, p[n]! = s[n]! -
    if i2 * 7 + (d.toNat - d1) ≤ n ∧ n - (i2 * 7 + (d.toNat - d1)) < pref.length then
      s[i2 * 7 + d.toNat]! / s[i1 * 7 + d1]! * s[i1 * 7 + (n - (i2 * 7 + (d.toNat - d1)))]!
    else 0

/-- The invariant of the loop of `JPoints.realRootsReduce` that lowers the degree `d` of the row
`i2` of the array `p` from `d₀` past its leading zeros: the entries of the row above `d` are zero,
and after the loop the entry at `d` is not, unless `d = -1`. -/
def DescentRowInvariant (p : Array ℚ) (i2 : ℕ) (d₀ : ℤ) : Std.WP.WhileInvariant ℤ Prop :=
  .mk fun exit d ↦ d ≤ d₀ ∧ -1 ≤ d ∧ (∀ k : ℕ, d < k → k < 7 → p[i2 * 7 + k]! = 0) ∧
    (exit = true → 0 ≤ d → p[i2 * 7 + d.toNat]! ≠ 0)

private theorem reduceInvariant_self {ch : SturmChain} {i1 i2 : ℕ} {d : ℤ}
    (h : ReducePre ch i1 i2 d) :
    ReduceInvariant ch i1 i2 false (ch.sturm, d) :=
  ⟨h.size_sturm, h.rowDegree_dividend, fun _ _ ↦ rfl, ⟨0, by simp⟩, nofun⟩

/-- The row `i1` of an array that agrees with the chain outside the row `i2 > i1` is that of the
chain. -/
private theorem getElem!_row_of_frame {ch : SturmChain} {i1 i2 : ℕ} (hlt : i1 < i2) {s : Array ℚ}
    (h : ∀ n, n < i2 * 7 ∨ i2 * 7 + 7 ≤ n → s[n]! = ch.sturm[n]!) {k : ℕ} (hk : k < 7) :
    s[i1 * 7 + k]! = ch.sturm[i1 * 7 + k]! :=
  h _ (.inl (by lia))

private theorem ReduceInvariant.post {ch : SturmChain} {i1 i2 : ℕ} {d₀ : ℤ}
    (hpre : ReducePre ch i1 i2 d₀)
    {s : Array ℚ} {d : ℤ} (h : ReduceInvariant ch i1 i2 true (s, d)) :
    ReducePost ch i1 i2 ⟨s, ch.deg, ch.len⟩ d := by
  obtain ⟨hs, hd, hf, ⟨Q, hQ⟩, hlt⟩ := h
  have h1 := hpre.rowDegree_divisor
  refine ⟨rfl, rfl, hs, hf _, hd, hlt rfl, ?_⟩
  rw [mod_eq_of_dvd_sub (p₂ := rowPoly s i2) ⟨Q, by rw [hQ]; ring⟩,
    (mod_eq_self_iff (h1.rowPoly_ne_zero (by lia))).mpr (hd.degree_lt h1 (hlt rfl))]

private theorem ReduceInvariant.exit {ch : SturmChain} {i1 i2 : ℕ} {s : Array ℚ} {d : ℤ} {m : ℕ}
    (hd : ¬(ch.deg[i1]! : ℤ) ≤ d) (h : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) :
    ReduceInvariant ch i1 i2 true (s, d) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun _ ↦ by lia⟩

private theorem subtractRowInvariant_nil {ch : SturmChain} {i1 i2 : ℕ} {s : Array ℚ} {d : ℤ} {m : ℕ}
    (h : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) (d1 : ℕ) (suff : List ℕ) :
    SubtractRowInvariant s i1 i2 d d1 [] suff s :=
  ⟨h.2.1, fun n ↦ by simp⟩

private theorem SubtractRowInvariant.append_singleton {ch : SturmChain} {i1 i2 : ℕ} {d₀ : ℤ}
    (hpre : ReducePre ch i1 i2 d₀) {s : Array ℚ} {d : ℤ} {m : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:ch.deg[i1]! + 1] = pref ++ cur :: suff) {p : Array ℚ}
    (hinv : SubtractRowInvariant s i1 i2 d ch.deg[i1]! pref (cur :: suff) p)
    (hr : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) (hd : ch.deg[i1]! ≤ d) :
    SubtractRowInvariant s i1 i2 d ch.deg[i1]! (pref ++ [cur]) suff
      (p.set! (i2 * 7 + (cur + d.toNat - ch.deg[i1]!))
        (p[i2 * 7 + (cur + d.toNat - ch.deg[i1]!)]! -
          s[i2 * 7 + d.toNat]! / s[i1 * 7 + ch.deg[i1]!]! * p[i1 * 7 + cur]!)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  have h7 := hr.2.2.1.lt_seven
  have hi := hpre.lt
  have hi7 := hpre.lt_seven
  have hs : s.size = 49 := hr.2.1
  obtain ⟨hsize, hp⟩ := hinv
  have hpc := hp (i1 * 7 + cur)
  rw [ite_eq_right (by lia), sub_zero] at hpc
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  have hpn := hp n
  have hpw := hp (i2 * 7 + (cur + d.toNat - ch.deg[i1]!))
  simp only [List.length_append, List.length_singleton]
  rcases lt_or_ge n p.size with hn | hn
  · rw [Array.getElem!_set! hn, hpc]
    split_ifs at hpn hpw ⊢ <;> grind
  · rw [getElem!_neg _ n (by simp; lia), getElem!_neg s n (by lia)]
    split_ifs <;> grind

private theorem SubtractRowInvariant.getElem!_eq {s : Array ℚ} {i1 i2 : ℕ} {d : ℤ} {d1 : ℕ}
    {p : Array ℚ}
    (h : SubtractRowInvariant s i1 i2 d d1 (ForIn.toList [:d1 + 1]) [] p) (n : ℕ) :
    p[n]! = s[n]! -
      if i2 * 7 + (d.toNat - d1) ≤ n ∧ n - (i2 * 7 + (d.toNat - d1)) < d1 + 1 then
        s[i2 * 7 + d.toNat]! / s[i1 * 7 + d1]! * s[i1 * 7 + (n - (i2 * 7 + (d.toNat - d1)))]!
      else 0 := by
  rw [h.2 n, Std.Legacy.Range.length_toList_zero_start]

/-- After the loop that subtracts `q xᵉ` times the row `i1` from the row `i2`, the row `i2` holds
its polynomial minus `q xᵉ` times that of the row `i1`, `q` the quotient of the leading
coefficients of the rows `i2` and `i1` and `e` the difference of their degrees
(`JPoints.SubtractRowInvariant`). -/
private theorem SubtractRowInvariant.rowPoly_eq {ch : SturmChain} {i1 i2 : ℕ} {d₀ : ℤ}
    (hpre : ReducePre ch i1 i2 d₀) {s : Array ℚ} {d : ℤ} {m : ℕ}
    (hr : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) {p : Array ℚ}
    (h : SubtractRowInvariant s i1 i2 d ch.deg[i1]! (ForIn.toList [:ch.deg[i1]! + 1]) [] p) :
    rowPoly p i2 = rowPoly s i2 - C (s[i2 * 7 + d.toNat]! / s[i1 * 7 + ch.deg[i1]!]!) *
      (X ^ (d.toNat - ch.deg[i1]!) * rowPoly s i1) := by
  have h1 := hpre.rowDegree_divisor.of_getElem!_eq fun _ ↦ getElem!_row_of_frame hpre.lt hr.2.2.2.1
  have hd7 := hr.2.2.1.lt_seven
  refine Polynomial.ext fun k ↦ ?_
  rw [coeff_rowPoly, coeff_sub, coeff_C_mul, coeff_X_pow_mul', coeff_rowPoly, coeff_rowPoly]
  rcases lt_or_ge k 7 with hk | hk
  · rw [ite_eq_left hk, ite_eq_left hk, h.getElem!_eq,
      show i2 * 7 + k - (i2 * 7 + (d.toNat - ch.deg[i1]!)) = k - (d.toNat - ch.deg[i1]!) by lia]
    by_cases hsk : d.toNat - ch.deg[i1]! ≤ k
    · rw [ite_eq_left hsk, ite_eq_left (show k - (d.toNat - ch.deg[i1]!) < 7 by lia)]
      by_cases hkd : k - (d.toNat - ch.deg[i1]!) < ch.deg[i1]! + 1
      · rw [ite_eq_left ⟨by lia, by lia⟩]
      · rw [ite_eq_right (by lia),
          h1.getElem!_eq_zero (k := k - (d.toNat - ch.deg[i1]!)) (by lia) (by lia), mul_zero]
    · rw [ite_eq_right (by lia), ite_eq_right hsk, mul_zero]
  · rw [ite_eq_right (by lia), ite_eq_right (by lia), zero_sub]
    split_ifs with h2 h3
    · rw [h1.getElem!_eq_zero (k := k - (d.toNat - ch.deg[i1]!)) (by lia) h3, mul_zero,
        neg_zero]
    · simp
    · simp

/-- The subtraction of the multiple of the row `i1` that `JPoints.SubtractRowInvariant` describes
cancels the leading coefficient of the row `i2`, of degree `d`: the descent past the leading zeros
starts at `d - 1`. -/
private theorem descentRowInvariant_sub_one {ch : SturmChain} {i1 i2 : ℕ} {d₀ : ℤ}
    (hpre : ReducePre ch i1 i2 d₀) {s : Array ℚ} {d : ℤ} {m : ℕ} (hd : ch.deg[i1]! ≤ d)
    {p : Array ℚ}
    (h : SubtractRowInvariant s i1 i2 d ch.deg[i1]! (ForIn.toList [:ch.deg[i1]! + 1]) [] p)
    (hr : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) :
    DescentRowInvariant p i2 (d - 1) false (d - 1) := by
  have h1 := hpre.rowDegree_divisor.of_getElem!_eq fun _ ↦ getElem!_row_of_frame hpre.lt hr.2.2.2.1
  have hu := hr.2.2.1
  refine ⟨le_rfl, by lia, fun k hk hk7 ↦ ?_, nofun⟩
  rw [h.getElem!_eq]
  rcases (show k = d.toNat ∨ d < k by lia) with rfl | hk'
  · rw [ite_eq_left ⟨by lia, by lia⟩,
      show i2 * 7 + d.toNat - (i2 * 7 + (d.toNat - ch.deg[i1]!)) = ch.deg[i1]! by lia,
      div_mul_cancel₀ _ (by simpa using h1.getElem!_ne_zero (by lia)), sub_self]
  · rw [hu.getElem!_eq_zero hk' hk7,
      show i2 * 7 + k - (i2 * 7 + (d.toNat - ch.deg[i1]!)) = k - (d.toNat - ch.deg[i1]!) by lia]
    split_ifs
    · rw [h1.getElem!_eq_zero (k := k - (d.toNat - ch.deg[i1]!)) (by lia) (by lia), mul_zero,
        sub_zero]
    · rw [sub_zero]

private theorem DescentRowInvariant.sub_one {p : Array ℚ} {i2 : ℕ} {d₀ d : ℤ} {m : ℕ}
    (hc : (decide (0 ≤ d) && p[i2 * 7 + d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ DescentRowInvariant p i2 d₀ false d) :
    (d - 1 + 1).toNat < m ∧ DescentRowInvariant p i2 d₀ false (d - 1) := by
  obtain ⟨rfl, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  exact ⟨by lia, by lia, by lia, Int.forall_sub_one_lt_of_forall_lt hz fun _ ↦ hc.2, nofun⟩

private theorem DescentRowInvariant.exit {p : Array ℚ} {i2 : ℕ} {d₀ d : ℤ} {m : ℕ}
    (hc : ¬(decide (0 ≤ d) && p[i2 * 7 + d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ DescentRowInvariant p i2 d₀ false d) :
    DescentRowInvariant p i2 d₀ true d := by
  obtain ⟨-, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
  exact ⟨hd, hd', hz, fun _ ↦ hc⟩

/-- One pass of the outer loop of `JPoints.realRootsReduce`: the row after the subtraction of the
multiple of the divisor that cancels the leading coefficient (`JPoints.SubtractRowInvariant`) and
the descent past its leading zeros has a lower degree, and still differs from the dividend by a
multiple of the divisor. -/
private theorem ReduceInvariant.of_descentRowInvariant {ch : SturmChain} {i1 i2 : ℕ} {d₀ : ℤ}
    (hpre : ReducePre ch i1 i2 d₀) {s : Array ℚ} {d d' : ℤ} {m : ℕ} (hdd : ch.deg[i1]! ≤ d)
    {p : Array ℚ}
    (h : SubtractRowInvariant s i1 i2 d ch.deg[i1]! (ForIn.toList [:ch.deg[i1]! + 1]) [] p)
    (hd : DescentRowInvariant p i2 (d - 1) true d')
    (hr : (d + 1).toNat = m ∧ ReduceInvariant ch i1 i2 false (s, d)) :
    (d' + 1).toNat < m ∧ ReduceInvariant ch i1 i2 false (p, d') := by
  have hP := h.rowPoly_eq hpre hr
  obtain ⟨rfl, hs, hu, hf, ⟨Q, hQ⟩, -⟩ := hr
  obtain ⟨hd1, hd2, hz, hnz⟩ := hd
  have hd7 := hu.lt_seven
  have hrow : rowPoly s i1 = rowPoly ch.sturm i1 :=
    rowPoly_congr fun k hk ↦ getElem!_row_of_frame hpre.lt hf hk
  refine ⟨by lia, h.1, ⟨hd2, by lia, fun hk hk7 ↦ hz _ hk hk7, hnz rfl⟩, fun n hn ↦ ?_,
    ⟨Q + C (s[i2 * 7 + d.toNat]! / s[i1 * 7 + ch.deg[i1]!]!) * X ^ (d.toNat - ch.deg[i1]!), ?_⟩,
    nofun⟩
  · rw [h.getElem!_eq, ite_eq_right (by lia), sub_zero, hf n hn]
  · rw [hP, hQ, hrow]
    ring

attribute [local irreducible] ReduceInvariant SubtractRowInvariant DescentRowInvariant in
/-- `JPoints.realRootsReduce` replaces the polynomial in the row `i2` of the chain by its
remainder modulo the polynomial in the row `i1 < i2`, of the degree that the chain records: the
remainder of lower degree, the other rows, the degrees and the length unchanged. -/
@[spec]
theorem realRootsReduce_spec (ch : SturmChain) (i1 i2 : ℕ) (d : ℤ) :
    ⦃ ReducePre ch i1 i2 d ⦄ realRootsReduce ch i1 i2 d
    ⦃ fun r ↦ ReducePost ch i1 i2 r.1 r.2 ⦄ := by
  vcgen [realRootsReduce] invariants
  | inv1 => ReduceInvariant ch i1 i2
  | inv2 => .ofMeasure fun s : Array ℚ × ℤ ↦ (s.2 + 1).toNat
  | inv3 s' d' _ _ _ => SubtractRowInvariant s' i1 i2 d' ch.deg[i1]!
  | inv4 d' _ _ _ p _ => DescentRowInvariant p i2 (d' - 1)
  | inv5 => .ofMeasure fun d : ℤ ↦ (d + 1).toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact reduceInvariant_self ‹_›
    | exact ReduceInvariant.post ‹_› ‹_›
    | exact ReduceInvariant.exit ‹_› ‹_›
    | exact subtractRowInvariant_nil ‹_› _ _
    | exact SubtractRowInvariant.append_singleton ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact descentRowInvariant_sub_one ‹_› ‹_› ‹_› ‹_›
    | exact ReduceInvariant.of_descentRowInvariant ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DescentRowInvariant.sub_one ‹_› ‹_›
    | exact DescentRowInvariant.exit ‹_› ‹_›

/-- The invariant of the loop of `JPoints.realRootsChain` for the polynomial `f`: the chain is
well formed for `f`; after the loop, the negated remainder of its last two polynomials is zero. -/
def ChainInvariant (f : ℚ[X]) : Std.WP.WhileInvariant SturmChain Prop :=
  .mk fun exit ch ↦ ch.WF f ∧
    (exit = true → -rowPoly ch.sturm (ch.len - 2) % rowPoly ch.sturm (ch.len - 1) = 0)

/-- The invariant of the loop of `JPoints.realRootsChain` that copies the row `i0` of the chain
`ch₀` into the row `i2`: after `k` steps, the entries `7 i2 + j` for `j < k` are those of the row
`i0`, the others and the degrees and the length unchanged. -/
def CopyRowInvariant (ch₀ : SturmChain) (i0 i2 : ℕ) : Std.WP.Invariant ℕ SturmChain Prop :=
  fun pref _ ch ↦ ch.deg = ch₀.deg ∧ ch.len = ch₀.len ∧ ch.sturm.size = 49 ∧
    ∀ n : ℕ, ch.sturm[n]! = if i2 * 7 ≤ n ∧ n < i2 * 7 + pref.length then
      ch₀.sturm[i0 * 7 + (n - i2 * 7)]! else ch₀.sturm[n]!

/-- The invariant of the loop of `JPoints.realRootsChain` that negates the row `i2` of the chain
`ch₁`: after `k` steps, the entries `7 i2 + j` for `j < k` are negated, the others and the degrees
and the length unchanged. -/
def NegateRowInvariant (ch₁ : SturmChain) (i2 : ℕ) : Std.WP.Invariant ℕ SturmChain Prop :=
  fun pref _ ch ↦ ch.deg = ch₁.deg ∧ ch.len = ch₁.len ∧ ch.sturm.size = 49 ∧
    ∀ n : ℕ, ch.sturm[n]! = if i2 * 7 ≤ n ∧ n < i2 * 7 + pref.length then
      -ch₁.sturm[n]! else ch₁.sturm[n]!

-- The rows of an array that agrees with the chain `b` on its rows.
private theorem rowPoly_eq_of_getElem!_eq {b : SturmChain} {s : Array ℚ}
    (hrows : ∀ n < b.len * 7, s[n]! = b.sturm[n]!) {i : ℕ} (hi : i < b.len) :
    rowPoly s i = rowPoly b.sturm i :=
  rowPoly_congr fun _ hk ↦ hrows _ (by lia)

/-- A chain that agrees with a well formed chain `b` in its rows, its degrees and its length is
well formed. -/
private theorem SturmChain.WF.of_rows {f : ℚ[X]} {b : SturmChain} (h : b.WF f) {c : SturmChain}
    (hdeg : c.deg = b.deg) (hlen : c.len = b.len) (hsize : c.sturm.size = 49)
    (hrows : ∀ n < b.len * 7, c.sturm[n]! = b.sturm[n]!) : c.WF f := by
  have hrow {i : ℕ} (hi : i < b.len) := rowPoly_eq_of_getElem!_eq hrows hi
  have h2 := h.two_le_len
  refine ⟨hsize, hdeg ▸ h.size_deg, hlen ▸ h2, fun {i} hi ↦ ?_, fun {i} hi ↦ ?_,
    fun {i} hi ↦ ?_, by rw [hrow (by lia), h.rowPoly_zero], by rw [hrow (by lia), h.rowPoly_one],
    fun {i} hi ↦ ?_⟩
  · rw [hdeg]
    exact (h.rowDegree (hlen ▸ hi)).of_getElem!_eq fun k hk ↦ hrows _ (by lia)
  · exact hdeg ▸ h.deg_add_lt (hlen ▸ hi)
  · exact hdeg ▸ h.deg_lt (hlen ▸ hi)
  · rw [hrow (by lia), hrow (by lia), hrow (by lia)]
    exact h.rowPoly_add_two (hlen ▸ hi)

private theorem SturmChain.WF.len_lt {f : ℚ[X]} {b : SturmChain} (h : b.WF f)
    (hc : 0 < b.deg[b.len - 1]!) : b.len < 7 := by
  have := h.deg_add_lt (i := b.len - 1) (by lia [h.two_le_len])
  lia [h.two_le_len]

private theorem chainInvariant_of_wf {f : ℚ[X]} {ch : SturmChain} (h : ch.WF f) :
    ChainInvariant f false ch :=
  ⟨h, nofun⟩

private theorem ChainInvariant.post {f : ℚ[X]} {ch : SturmChain} (h : ChainInvariant f true ch) :
    ch.IsFinished f :=
  ⟨h.1, h.2 rfl⟩

/-- The chain ends when its last polynomial is a nonzero constant, which divides the polynomial
before it. -/
private theorem ChainInvariant.exit {f : ℚ[X]} {b : SturmChain} {m : ℕ}
    (hc : ¬0 < b.deg[b.len - 1]!)
    (h : 7 - b.len = m ∧ ChainInvariant f false b) : ChainInvariant f true b := by
  have hw := h.2.1
  have hd := hw.rowDegree (i := b.len - 1) (by lia [hw.two_le_len])
  have h0 : b.deg[b.len - 1]! = 0 := by lia
  rw [h0] at hd
  refine ⟨hw, fun _ ↦ EuclideanDomain.mod_eq_zero.mpr (isUnit_iff_degree_eq_zero.mpr ?_).dvd⟩
  rw [hd.degree_eq le_rfl]
  rfl

private theorem copyRowInvariant_nil {f : ℚ[X]} {b : SturmChain} {m : ℕ}
    (h : 7 - b.len = m ∧ ChainInvariant f false b) (suff : List ℕ) :
    CopyRowInvariant b (b.len - 2) b.len [] suff b :=
  ⟨rfl, rfl, h.2.1.size_sturm, fun n ↦ by simp⟩

private theorem CopyRowInvariant.append_singleton {f : ℚ[X]} {b : SturmChain} {m : ℕ}
    (hc : 0 < b.deg[b.len - 1]!) (hr : 7 - b.len = m ∧ ChainInvariant f false b)
    {pref suff : List ℕ} {cur : ℕ} (h : ForIn.toList [:7] = pref ++ cur :: suff) {c : SturmChain}
    (hinv : CopyRowInvariant b (b.len - 2) b.len pref (cur :: suff) c) :
    CopyRowInvariant b (b.len - 2) b.len (pref ++ [cur]) suff
      ⟨c.sturm.set! (b.len * 7 + cur) c.sturm[(b.len - 2) * 7 + cur]!, c.deg, c.len⟩ := by
  have hc' := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  have h7 := hr.2.1.len_lt hc
  have h2 := hr.2.1.two_le_len
  obtain ⟨hdeg, hlen, hsize, hp⟩ := hinv
  have hpc := hp ((b.len - 2) * 7 + cur)
  rw [ite_eq_right (by lia)] at hpc
  refine ⟨hdeg, hlen, by simp [hsize], fun n ↦ ?_⟩
  have hpn := hp n
  simp only [List.length_append, List.length_singleton]
  rcases lt_or_ge n c.sturm.size with hn | hn
  · rw [Array.getElem!_set! hn, hpc]
    split_ifs at hpn ⊢ <;> grind
  · rw [getElem!_neg _ n (by simp; lia), getElem!_neg b.sturm n (by lia [hr.2.1.size_sturm])]
    split_ifs <;> grind

/-- After the loop that copies the row `len - 2` into the row `len`, the chain is ready for the
remainder modulo its last polynomial. -/
private theorem CopyRowInvariant.reducePre {f : ℚ[X]} {b : SturmChain} {m : ℕ}
    (hc : 0 < b.deg[b.len - 1]!) {c : SturmChain}
    (h : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c)
    (hr : 7 - b.len = m ∧ ChainInvariant f false b) :
    ReducePre c (b.len - 1) b.len c.deg[b.len - 2]! := by
  have hw := hr.2.1
  have h7 := hw.len_lt hc
  have h2 := hw.two_le_len
  obtain ⟨hdeg, hlen, hsize, hp⟩ := h
  rw [Std.Legacy.Range.length_toList] at hp
  have hd1 := hw.rowDegree (i := b.len - 1) (by lia)
  have hd0 := hw.rowDegree (i := b.len - 2) (by lia)
  rw [← hdeg] at hd1 hd0
  exact ⟨hsize, by lia, h7, hd1.of_getElem!_eq fun k hk ↦ by rw [hp, ite_eq_right (by lia)],
    hd0.of_getElem!_eq fun k hk ↦ by rw [hp, ite_eq_left (by lia), Nat.add_sub_cancel_left]⟩

private theorem CopyRowInvariant.getElem!_eq {b c : SturmChain}
    (h : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c) {n : ℕ}
    (hn : n < b.len * 7 ∨ b.len * 7 + 7 ≤ n) : c.sturm[n]! = b.sturm[n]! := by
  rw [h.2.2.2, Std.Legacy.Range.length_toList, ite_eq_right (by lia)]

private theorem CopyRowInvariant.getElem!_eq_copy {b c : SturmChain}
    (h : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c) {k : ℕ} (hk : k < 7) :
    c.sturm[b.len * 7 + k]! = b.sturm[(b.len - 2) * 7 + k]! := by
  have hp := h.2.2.2 (b.len * 7 + k)
  rw [Std.Legacy.Range.length_toList_zero_start, Nat.add_sub_cancel_left] at hp
  rwa [ite_eq_left (show b.len * 7 ≤ b.len * 7 + k ∧ b.len * 7 + k < b.len * 7 + 7 by lia)] at hp

private theorem CopyRowInvariant.rowPoly_eq {b c : SturmChain}
    (h : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c) :
    rowPoly c.sturm b.len = rowPoly b.sturm (b.len - 2) :=
  rowPoly_congr fun _ hk ↦ h.getElem!_eq_copy hk

/-- After the copy and the remainder, the rows before the row `len` are those of the chain `b`. -/
private theorem ReducePost.getElem!_eq_of_lt {b c ch' : SturmChain} {d : ℤ}
    (hc : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c)
    (h : ReducePost c (b.len - 1) b.len ch' d) {n : ℕ} (hn : n < b.len * 7) :
    ch'.sturm[n]! = b.sturm[n]! :=
  (h.getElem!_eq (.inl hn)).trans (hc.getElem!_eq (.inl hn))

/-- After the copy and the remainder, the row `len` holds the remainder of the polynomial `len - 2`
of the chain `b` modulo the polynomial `len - 1`. -/
private theorem ReducePost.rowPoly_eq_mod {b c ch' : SturmChain} {d : ℤ} (h2 : 2 ≤ b.len)
    (hc : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c)
    (h : ReducePost c (b.len - 1) b.len ch' d) :
    rowPoly ch'.sturm b.len = rowPoly b.sturm (b.len - 2) % rowPoly b.sturm (b.len - 1) := by
  rw [h.rowPoly_eq, hc.rowPoly_eq, rowPoly_congr fun k hk ↦ hc.getElem!_eq (.inl (by lia))]

/-- A zero remainder ends the chain: the negated remainder of its last two polynomials is zero. -/
private theorem ChainInvariant.of_reducePost_of_neg {f : ℚ[X]} {b c ch' : SturmChain} {d : ℤ}
    {m : ℕ}
    (hc : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c)
    (h : ReducePost c (b.len - 1) b.len ch' d) (hd : d < 0)
    (hr : 7 - b.len = m ∧ ChainInvariant f false b) : ChainInvariant f true ch' := by
  have hw := hr.2.1
  have h2 := hw.two_le_len
  have hlen : ch'.len = b.len := h.len_eq.trans hc.2.1
  have hrow {i : ℕ} (hi : i < b.len) :=
    rowPoly_eq_of_getElem!_eq (fun n hn ↦ h.getElem!_eq_of_lt hc hn) hi
  refine ⟨hw.of_rows (h.deg_eq.trans hc.1) hlen h.size_sturm fun n hn ↦
    h.getElem!_eq_of_lt hc hn, fun _ ↦ ?_⟩
  rw [hlen, hrow (by lia), hrow (by lia), neg_mod, ← h.rowPoly_eq_mod h2 hc,
    h.rowDegree.rowPoly_eq_zero hd, neg_zero]

private theorem negateRowInvariant_nil {c ch' : SturmChain} {i2 : ℕ} {d : ℤ}
    (h : ReducePost c (i2 - 1) i2 ch' d) (suff : List ℕ) : NegateRowInvariant ch' i2 [] suff ch' :=
  ⟨rfl, rfl, h.size_sturm, fun n ↦ by simp⟩

private theorem NegateRowInvariant.append_singleton {f : ℚ[X]} {b c ch' : SturmChain} {d : ℤ}
    {m : ℕ}
    (hc0 : 0 < b.deg[b.len - 1]!) (h : ReducePost c (b.len - 1) b.len ch' d)
    (hr : 7 - b.len = m ∧ ChainInvariant f false b) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:d.toNat + 1] = pref ++ cur :: suff) {e : SturmChain}
    (hinv : NegateRowInvariant ch' b.len pref (cur :: suff) e) :
    NegateRowInvariant ch' b.len (pref ++ [cur]) suff
      ⟨e.sturm.set! (b.len * 7 + cur) (-e.sturm[b.len * 7 + cur]!), e.deg, e.len⟩ := by
  have hc' := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have h7 := hr.2.1.len_lt hc0
  have hd7 := h.rowDegree.lt_seven
  have hs := h.size_sturm
  obtain ⟨hdeg, hlen, hsize, hp⟩ := hinv
  have hpc := hp (b.len * 7 + cur)
  rw [ite_eq_right (by lia)] at hpc
  refine ⟨hdeg, hlen, by simp [hsize], fun n ↦ ?_⟩
  have hpn := hp n
  simp only [List.length_append, List.length_singleton]
  rcases lt_or_ge n e.sturm.size with hn | hn
  · rw [Array.getElem!_set! hn, hpc]
    split_ifs at hpn ⊢ <;> grind
  · rw [getElem!_neg _ n (by simp; lia), getElem!_neg ch'.sturm n (by lia)]
    split_ifs <;> simp [show (default : ℚ) = 0 from rfl]

private theorem NegateRowInvariant.getElem!_eq {ch' e : SturmChain} {i2 : ℕ} {d : ℤ}
    (h : NegateRowInvariant ch' i2 (ForIn.toList [:d.toNat + 1]) [] e) (n : ℕ) :
    e.sturm[n]! = if i2 * 7 ≤ n ∧ n < i2 * 7 + (d.toNat + 1) then -ch'.sturm[n]! else
      ch'.sturm[n]! := by
  rw [h.2.2.2, Std.Legacy.Range.length_toList_zero_start]

/-- After the loop that negates the row `i2` of the remainder of degree `d ≥ 0`, the row holds the
negated remainder, of the same degree. -/
private theorem NegateRowInvariant.rowDegree_and_rowPoly_eq {c ch' e : SturmChain} {i2 : ℕ} {d : ℤ}
    (hd : ¬d < 0) (hred : ReducePost c (i2 - 1) i2 ch' d)
    (h : NegateRowInvariant ch' i2 (ForIn.toList [:d.toNat + 1]) [] e) :
    RowDegree e.sturm i2 d ∧ rowPoly e.sturm i2 = -rowPoly ch'.sturm i2 := by
  have hr := hred.rowDegree
  refine ⟨⟨hr.neg_one_le, hr.lt_seven, fun {k} hk hk7 ↦ ?_, fun h0 ↦ ?_⟩, ?_⟩
  · rw [h.getElem!_eq, ite_eq_right (by lia), hr.getElem!_eq_zero hk hk7]
  · rw [h.getElem!_eq, ite_eq_left (by lia), neg_ne_zero]
    exact hr.getElem!_ne_zero h0
  · refine Polynomial.ext fun k ↦ ?_
    rw [coeff_neg, coeff_rowPoly, coeff_rowPoly, h.getElem!_eq]
    split_ifs with h1 h2
    · rfl
    · rw [hr.getElem!_eq_zero (by lia) h1, neg_zero]
    · rw [neg_zero]

-- The polynomials from the third on of the chain `b` with a row `len` appended.
private theorem SturmChain.WF.push_rowPoly_add_two {f : ℚ[X]} {b : SturmChain} (h : b.WF f)
    {s : Array ℚ} (hrows : ∀ n < b.len * 7, s[n]! = b.sturm[n]!)
    (hrp : rowPoly s b.len = -rowPoly b.sturm (b.len - 2) % rowPoly b.sturm (b.len - 1)) {i : ℕ}
    (hi : i + 2 < b.len + 1) : rowPoly s (i + 2) = -rowPoly s i % rowPoly s (i + 1) := by
  have hrowp {j : ℕ} (hj : j < b.len) := rowPoly_eq_of_getElem!_eq hrows hj
  rcases (show i + 2 < b.len ∨ i + 2 = b.len by lia) with hi | hi
  · rw [hrowp hi, hrowp (by lia), hrowp (by lia)]; exact h.rowPoly_add_two hi
  · rw [hi, hrp, hrowp (by lia), hrowp (by lia), show i = b.len - 2 by lia,
      show b.len - 2 + 1 = b.len - 1 by lia]

/-- A chain `b` with the row `len` of the array `s` holding a polynomial of a degree `d` below that
of the last polynomial, the negated remainder of the last two: the chain with that row appended. -/
private theorem SturmChain.WF.push {f : ℚ[X]} {b : SturmChain} (h : b.WF f) (h7 : b.len < 7)
    {s : Array ℚ} (hsize : s.size = 49) (hrows : ∀ n < b.len * 7, s[n]! = b.sturm[n]!) {d : ℕ}
    (hrd : RowDegree s b.len d) (hlt : d < b.deg[b.len - 1]!)
    (hrp : rowPoly s b.len = -rowPoly b.sturm (b.len - 2) % rowPoly b.sturm (b.len - 1)) :
    SturmChain.WF f ⟨s, b.deg.set! b.len d, b.len + 1⟩ := by
  have h2 := h.two_le_len
  have hdl := h.deg_add_lt (i := b.len - 1) (by lia)
  have hne {i : ℕ} (hi : i < b.len) : (b.deg.set! b.len d)[i]! = b.deg[i]! :=
    Array.getElem!_set!_ne _ _ _ _ (by lia)
  have hself : (b.deg.set! b.len d)[b.len]! = d :=
    Array.getElem!_set!_self _ _ _ (by rw [h.size_deg]; lia)
  refine ⟨hsize, by simp [h.size_deg], by lia, fun {i} hi ↦ ?_, fun {i} hi ↦ ?_, fun {i} hi ↦ ?_,
    by rw [rowPoly_eq_of_getElem!_eq hrows (by lia), h.rowPoly_zero],
    by rw [rowPoly_eq_of_getElem!_eq hrows (by lia), h.rowPoly_one],
    h.push_rowPoly_add_two hrows hrp⟩
  all_goals change _ < b.len + 1 at hi
  · rcases (show i < b.len ∨ i = b.len by lia) with hi | rfl
    · rw [hne hi]; exact (h.rowDegree hi).of_getElem!_eq fun k hk ↦ hrows _ (by lia)
    · rwa [hself]
  · rcases (show i < b.len ∨ i = b.len by lia) with hi | rfl
    · rw [hne hi]; exact h.deg_add_lt hi
    · rw [hself]; lia
  · rcases (show i + 1 < b.len ∨ i + 1 = b.len by lia) with hi | hi
    · rw [hne hi, hne (by lia)]; exact h.deg_lt hi
    · rw [hi, hself, hne (by lia), show i = b.len - 1 by lia]; exact hlt

/-- One step of the chain: the negated remainder of the last two polynomials, of a lower degree,
appended to the chain. -/
private theorem ChainInvariant.of_negateRowInvariant {f : ℚ[X]} {b c ch' e : SturmChain} {d : ℤ}
    {m : ℕ}
    (hc0 : 0 < b.deg[b.len - 1]!)
    (hc : CopyRowInvariant b (b.len - 2) b.len (ForIn.toList [:7]) [] c)
    (h : ReducePost c (b.len - 1) b.len ch' d) (hd : ¬d < 0)
    (hn : NegateRowInvariant ch' b.len (ForIn.toList [:d.toNat + 1]) [] e)
    (hr : 7 - b.len = m ∧ ChainInvariant f false b) :
    7 - (e.len + 1) < m ∧
      ChainInvariant f false ⟨e.sturm, e.deg.set! b.len d.toNat, e.len + 1⟩ := by
  obtain ⟨rfl, hw, -⟩ := hr
  have h7 := hw.len_lt hc0
  obtain ⟨hrd, hrp⟩ := hn.rowDegree_and_rowPoly_eq hd h
  rw [← Int.toNat_of_nonneg (not_lt.mp hd)] at hrd
  have hrows (n : ℕ) (hn' : n < b.len * 7) : e.sturm[n]! = b.sturm[n]! := by
    rw [hn.getElem!_eq, ite_eq_right (by lia), h.getElem!_eq_of_lt hc hn']
  rw [hn.1.trans (h.deg_eq.trans hc.1), hn.2.1.trans (h.len_eq.trans hc.2.1)]
  refine ⟨by lia, hw.push h7 hn.2.2.1 hrows hrd (by have := hc.1 ▸ h.lt; lia) ?_, nofun⟩
  rw [hrp, h.rowPoly_eq_mod hw.two_le_len hc, neg_mod]

attribute [local irreducible] ChainInvariant CopyRowInvariant NegateRowInvariant in
/-- `JPoints.realRootsChain` completes the Sturm chain of `f` from its start: the chain stays well
formed, and it ends where the negated remainder of its last two polynomials is zero, as Mathlib's
`Polynomial.sturmSeq` does. -/
@[spec]
theorem realRootsChain_spec (f : ℚ[X]) (ch : SturmChain) :
    ⦃ ch.WF f ⦄ realRootsChain ch
    ⦃ fun r ↦ r.IsFinished f ⦄ := by
  vcgen [realRootsChain] invariants
  | inv1 => ChainInvariant f
  | inv2 => .ofMeasure fun ch : SturmChain ↦ 7 - ch.len
  | inv3 b _ _ _ => CopyRowInvariant b (b.len - 2) b.len
  | inv4 b _ _ _ ch' _ _ _ => NegateRowInvariant ch' b.len
  all_goals try vc_simp
  all_goals with_reducible first
    | exact chainInvariant_of_wf ‹_›
    | exact ChainInvariant.post ‹_›
    | exact ChainInvariant.exit ‹_› ‹_›
    | exact copyRowInvariant_nil ‹_› _
    | exact CopyRowInvariant.append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact CopyRowInvariant.reducePre ‹_› ‹_› ‹_›
    | exact ChainInvariant.of_reducePost_of_neg ‹_› ‹_› ‹_› ‹_›
    | exact negateRowInvariant_nil ‹_› _
    | exact NegateRowInvariant.append_singleton ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ChainInvariant.of_negateRowInvariant ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The polynomials of a finished chain for `f` (`JPoints.realRootsChain_spec`) are the Sturm
sequence of `f` and `f'`. -/
theorem SturmChain.IsFinished.map_rowPoly_eq_sturmSeq {f : ℚ[X]} {ch : SturmChain}
    (h : ch.IsFinished f) :
    (List.range ch.len).map (rowPoly ch.sturm) = sturmSeq f (derivative f) := by
  rw [map_range_eq_sturmSeq h.two_le_len (fun i hi ↦ (h.rowDegree hi).rowPoly_ne_zero (by lia))
    (fun i hi ↦ h.rowPoly_add_two hi) h.neg_mod_eq_zero, h.rowPoly_zero, h.rowPoly_one]

/-! ### The sign changes -/

/-- The sign of the integer `v.num.sign` of `sturm_changes`, as a rational number, is that of
`v`. -/
private theorem sign_intCast_sign_num (v : ℚ) :
    SignType.sign ((v.num.sign : ℤ) : ℚ) = SignType.sign v := by
  rcases lt_trichotomy v 0 with h | rfl | h
  · rw [Int.sign_eq_neg_one_of_neg (Rat.num_neg.mpr h), sign_neg h]; simp
  · simp
  · rw [Int.sign_eq_one_of_pos (Rat.num_pos.mpr h), sign_pos h]; simp

private theorem sign_num_eq_zero_iff (v : ℚ) : v.num.sign = 0 ↔ v = 0 := by
  rw [Int.sign_eq_zero_iff_zero, Rat.num_eq_zero]

/-- Replacing the head `v` of a list by the sign `v.num.sign` of `v`, as a rational number, keeps
the sign variations. -/
private theorem signVariations_cons_eq_sign_num (v : ℚ) (l : List ℚ) :
    ((v :: l).signVariations) = (((v.num.sign : ℤ) : ℚ) :: l).signVariations :=
  List.signVariations_congr (by rw [List.map_cons, List.map_cons, sign_intCast_sign_num])

/-- The invariant of Horner's rule in `JPoints.sturmChanges` for the row `i` of the chain `ch` at
`x`: after `j` steps, `v = ∑ m ≤ j, c_(d - m) x ^ (j - m)` for the coefficients `c` of the row and
its degree `d`. -/
def HornerRowInvariant (ch : SturmChain) (i : ℕ) (x : ℚ) : Std.WP.Invariant ℕ ℚ Prop :=
  fun pref _ v ↦ v = ∑ m ∈ Finset.range (pref.length + 1),
    ch.sturm[i * 7 + (ch.deg[i]! - m)]! * x ^ (pref.length - m)

/-- The invariant of the loop of `JPoints.sturmChanges` over the chain `ch` at `x`, with the count
`c` and the last nonzero sign `t` so far: `c` plus the sign variations of `t` followed by the
values of the rows still to come is the number of sign variations of all values; no count before a
nonzero value. -/
def ChangesInvariant (ch : SturmChain) (x : ℚ) : Std.WP.Invariant ℕ (ℕ × ℤ) Prop :=
  fun _ suff s ↦ (s.2 = 1 ∨ s.2 = 0 ∨ s.2 = -1) ∧ (s.2 = 0 → s.1 = 0) ∧
    s.1 + (((s.2 : ℚ) :: suff.map fun i ↦ (rowPoly ch.sturm i).eval x)).signVariations =
      ((List.range ch.len).map fun i ↦ (rowPoly ch.sturm i).eval x).signVariations

private theorem hornerRowInvariant_nil (ch : SturmChain) (i : ℕ) (x : ℚ) (suff : List ℕ) :
    HornerRowInvariant ch i x [] suff ch.sturm[i * 7 + ch.deg[i]!]! := by
  simp [HornerRowInvariant]

private theorem HornerRowInvariant.append_singleton {ch : SturmChain} {i : ℕ} {x : ℚ}
    {pref suff : List ℕ} {cur : ℕ} (h : ForIn.toList [:ch.deg[i]!] = pref ++ cur :: suff)
    {v : ℚ} (hinv : HornerRowInvariant ch i x pref (cur :: suff) v) :
    HornerRowInvariant ch i x (pref ++ [cur]) suff
      (v * x + ch.sturm[i * 7 + (ch.deg[i]! - 1 - cur)]!) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  rw [HornerRowInvariant] at hinv ⊢
  rw [hinv, List.length_append, List.length_singleton, hc, Nat.sub_sub, Nat.add_comm 1 cur,
    Finset.sum_range_mul_pow_sub_mul_add (fun m ↦ ch.sturm[i * 7 + (ch.deg[i]! - m)]!)]

private theorem eval_rowPoly_eq_sum {s : Array ℚ} {i : ℕ} {d : ℤ} (h : RowDegree s i d) (hd : 0 ≤ d)
    (x : ℚ) : (rowPoly s i).eval x = ∑ k ∈ Finset.range (d.toNat + 1), s[i * 7 + k]! * x ^ k := by
  rw [eval_eq_sum_range' (n := d.toNat + 1) (by rw [h.natDegree_eq hd]; lia)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [coeff_rowPoly, ite_eq_left (by have := Finset.mem_range.mp hk; lia [h.lt_seven])]

/-- After Horner's rule, the value is that of the polynomial of the row at `x`. -/
private theorem HornerRowInvariant.eq_eval {f : ℚ[X]} {ch : SturmChain} (hw : ch.WF f) {i : ℕ}
    (hi : i < ch.len) {x v : ℚ} (h : HornerRowInvariant ch i x (ForIn.toList [:ch.deg[i]!]) [] v) :
    v = (rowPoly ch.sturm i).eval x := by
  rw [HornerRowInvariant, Std.Legacy.Range.length_toList_zero_start] at h
  rw [h, eval_rowPoly_eq_sum (hw.rowDegree hi) (by lia), Int.toNat_natCast,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have := Finset.mem_range.mp hm
  rw [show ch.deg[i]! - (ch.deg[i]! + 1 - 1 - m) = m by lia]

private theorem changesInvariant_nil (ch : SturmChain) (x : ℚ) :
    ChangesInvariant ch x [] (ForIn.toList [:ch.len]) (0, 0) := by
  refine ⟨by simp, fun _ ↦ rfl, ?_⟩
  rw [Std.Legacy.Range.toList_eq_range, Int.cast_zero, List.signVariations_zero_cons, zero_add]

private theorem ChangesInvariant.post {ch : SturmChain} {x : ℚ} {c : ℕ} {t : ℤ}
    (h : ChangesInvariant ch x (ForIn.toList [:ch.len]) [] (c, t)) :
    c = ((List.range ch.len).map fun i ↦ (rowPoly ch.sturm i).eval x).signVariations := by
  rw [← h.2.2, List.map_nil, List.signVariations_singleton, add_zero]

/-- A zero value changes neither the count nor the last sign. -/
private theorem ChangesInvariant.of_eq_zero {f : ℚ[X]} {ch : SturmChain} (hw : ch.WF f) {x : ℚ}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:ch.len] = pref ++ cur :: suff) {c : ℕ}
    {t : ℤ} (hinv : ChangesInvariant ch x pref (cur :: suff) (c, t)) {v : ℚ}
    (hv : HornerRowInvariant ch cur x (ForIn.toList [:ch.deg[cur]!]) [] v)
    (h0 : ¬(v.num.sign != 0) = true) : ChangesInvariant ch x (pref ++ [cur]) suff (c, t) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [hv.eq_eval hw hcur] at h0
  simp only [bne_iff_ne, ne_eq, Decidable.not_not, sign_num_eq_zero_iff] at h0
  obtain ⟨ht, hc, heq⟩ := hinv
  refine ⟨ht, hc, ?_⟩
  rw [← heq, List.map_cons, h0, List.signVariations_cons_zero_cons]

private theorem eq_of_sign_intCast_eq {a b : ℤ} (ha : a = 1 ∨ a = 0 ∨ a = -1)
    (hb : b = 1 ∨ b = 0 ∨ b = -1)
    (h : SignType.sign (a : ℚ) = SignType.sign (b : ℚ)) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all

/-- A nonzero value of a sign other than the last nonzero sign counts one change. -/
private theorem ChangesInvariant.of_ne {f : ℚ[X]} {ch : SturmChain} (hw : ch.WF f) {x : ℚ}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:ch.len] = pref ++ cur :: suff) {c : ℕ}
    {t : ℤ} (hinv : ChangesInvariant ch x pref (cur :: suff) (c, t)) {v : ℚ}
    (hv : HornerRowInvariant ch cur x (ForIn.toList [:ch.deg[cur]!]) [] v)
    (h0 : (v.num.sign != 0) = true) (h1 : (t != 0 && v.num.sign != t) = true) :
    ChangesInvariant ch x (pref ++ [cur]) suff (c + 1, v.num.sign) := by
  have hv' := hv.eq_eval hw (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true] at h0 h1
  simp only [ChangesInvariant] at hinv ⊢
  obtain ⟨ht, -, heq⟩ := hinv
  have hne : SignType.sign (t : ℚ) ≠ SignType.sign v := fun h ↦ h1.2
    (eq_of_sign_intCast_eq (Int.sign_trichotomy _) ht (by rw [sign_intCast_sign_num, h]))
  refine ⟨Int.sign_trichotomy _, fun h ↦ absurd h h0, ?_⟩
  rw [← heq, List.map_cons, ← hv', List.signVariations_cons_cons_of_ne_zero _ (by simpa using h1.1)
    (by rwa [sign_num_eq_zero_iff] at h0), signVariations_cons_eq_sign_num v, ite_eq_right hne]
  ring

/-- A nonzero value of the last nonzero sign, or the first nonzero value, counts no change. -/
private theorem ChangesInvariant.of_not_ne {f : ℚ[X]} {ch : SturmChain} (hw : ch.WF f) {x : ℚ}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:ch.len] = pref ++ cur :: suff) {c : ℕ}
    {t : ℤ} (hinv : ChangesInvariant ch x pref (cur :: suff) (c, t)) {v : ℚ}
    (hv : HornerRowInvariant ch cur x (ForIn.toList [:ch.deg[cur]!]) [] v)
    (h0 : (v.num.sign != 0) = true) (h1 : ¬(t != 0 && v.num.sign != t) = true) :
    ChangesInvariant ch x (pref ++ [cur]) suff (c, v.num.sign) := by
  have hv' := hv.eq_eval hw (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, not_and, Decidable.not_not] at h0 h1
  simp only [ChangesInvariant] at hinv ⊢
  obtain ⟨ht, hc, heq⟩ := hinv
  have hv0 : v ≠ 0 := by rwa [sign_num_eq_zero_iff] at h0
  refine ⟨Int.sign_trichotomy _, fun h ↦ absurd h h0, ?_⟩
  rw [← heq, List.map_cons, ← hv']
  by_cases ht0 : t = 0
  · rw [hc ht0, ht0, Int.cast_zero, List.signVariations_zero_cons,
      signVariations_cons_eq_sign_num v]
  · rw [List.signVariations_cons_cons_of_ne_zero _ (by simpa using ht0) hv0,
      signVariations_cons_eq_sign_num v, ← h1 ht0, ite_eq_left (sign_intCast_sign_num v),
      add_zero]

attribute [local irreducible] HornerRowInvariant ChangesInvariant in
/-- `JPoints.sturmChanges` counts the sign variations of the values of the polynomials of the
chain at `x`, zeros skipped, by Horner's rule (`List.signVariations`). -/
@[spec]
theorem sturmChanges_spec (f : ℚ[X]) (ch : SturmChain) (x : ℚ) :
    ⦃ ch.WF f ⦄ sturmChanges ch x
    ⦃ fun r ↦ r =
        ((List.range ch.len).map fun i ↦ (rowPoly ch.sturm i).eval x).signVariations ⦄ := by
  vcgen [sturmChanges] invariants
  | inv1 => ChangesInvariant ch x
  | inv2 _ cur _ _ _ _ _ => HornerRowInvariant ch cur x
  all_goals try vc_simp
  all_goals with_reducible first
    | exact changesInvariant_nil ch x
    | exact ChangesInvariant.post ‹_›
    | exact hornerRowInvariant_nil ch _ x _
    | exact HornerRowInvariant.append_singleton ‹_› ‹_›
    | exact ChangesInvariant.of_eq_zero ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ChangesInvariant.of_ne ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ChangesInvariant.of_not_ne ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end JPoints

end
