/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.TaylorShift
public import JPoints.Proof.TubeBands
public import Std.WP

import JPoints.Proof.CellSizes
import JPoints.Proof.Containers
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The contracts of the analysis of the tube

What the analysis of the tube does to a consistent state of the analysis (`JPoints.TubeState.WF`):
`tube_a_init` sets the polynomials of a first coordinate as from the initial state and keeps the
rest (`JPoints.tubeAInit_spec`), and `tube_cell` changes only the counter of the cells, the cache of
products and the bands (`JPoints.tubeCell_spec`); both keep the state consistent, which
`tube_sample` and `sift_bands` need from band to band. The cache of the products of a cell holds,
after the products of a cell, those of its half-sizes (`JPoints.TubeState.WF.run_tubeCellProducts`),
whatever it held before: the analysis of a band of rows from the state that the thread holds gives
the bands of the analysis from a reference state with the same polynomials, row by row
(`JPoints.TubeState.BandSim.run_tubeCell`), and collects the words of each row in increasing order
(`JPoints.TubeBands.Sized.rangesIn_run_tubeCell`).

## Main definitions

* `JPoints.cellProduct`, `JPoints.cellProducts`: the products of the half-sizes of a cell.
* `JPoints.tubeK0`, `JPoints.tubeK1`, `JPoints.tubeK2`, `JPoints.tubeKA`: the polynomials of a
  first coordinate.
* `JPoints.TubeState.EqPolys`, `JPoints.TubeState.BandSim`: states of the analysis that agree.
* `JPoints.ProductsInvariant`, `JPoints.ProductsRowInvariant`, `JPoints.ZeroPolysInvariant`,
  `JPoints.BoundCoeffsInvariant`: the invariants of the loops.

## Main statements

* `JPoints.tubeAInit_spec`, `JPoints.TubeState.WF.run_tubeAInit`, `JPoints.run_tubeAInit_initial`:
  the polynomials of a first coordinate.
* `JPoints.TubeState.eqPolys_iff_eq_with`: the states with the polynomials of a state.
* `JPoints.tubeCell_spec`: the analysis of a cell.
* `JPoints.TubeState.WF.run_tubeCellProducts`: the products of a cell.
* `JPoints.TubeState.BandSim.run_tubeCell`, `JPoints.TubeBands.Sized.rangesIn_run_tubeCell`: the
  analysis of a band of rows.

## Implementation notes

The contracts of the components with loops are triples of `Std.WP` proved by `vcgen` with named
invariants; those of `tube_cell` follow from statements about its value, proved by its functional
induction (`JPoints.tubeCell.induct`) on the unfolding `JPoints.run_tubeCell_of_tubeOk`. The
comparison of half-sizes by `!=`, under which `-0.0` equals `0.0`, reuses a cache bit for bit
since the half-sizes of the cells are never `-0.0` and those in words never zero
(`JPoints.Proof.CellSizes`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The products of the half-sizes of a cell -/

/-- The product `rb ^ j rc ^ k` of the half-sizes `rb` and `rc` of a cell at the index
`i = P(j, k) = L j + k` (`L = JPoints.coeffRow`, `k < L`), as `tube_cell` computes it by repeated
products (`JPoints.tubeCellProducts`): `1.0` times `rb`, `j` times, then times `rc`, `k` times. -/
def cellProduct (rb rc : Double) (i : ℕ) : Double :=
  (· * rc)^[i % coeffRow] ((· * rb)^[i / coeffRow] 1.0)

/-- The products of the half-sizes `rb` and `rc` of a cell (`JPoints.cellProduct`) at every index
of an array of `JPoints.numCoeffs` coefficients, as `tube_cell` keeps them in its statics. -/
def cellProducts (rb rc : Double) : Array Double :=
  coeffArray fun j k ↦ (· * rc)^[k] ((· * rb)^[j] 1.0)

theorem size_cellProducts (rb rc : Double) : (cellProducts rb rc).size = numCoeffs :=
  size_coeffArray _

/-- The invariant of the outer loop of `JPoints.tubeCellProducts` over `j`, whose state is the
array of the products and the power `rbj` of `rb`: the array of `n` entries, `rbj = rb ^ j` by
repeated products, and the products of the rows `j' < j` written. -/
def ProductsInvariant (rb rc : Double) (n : ℕ) : Std.WP.Invariant ℕ (Array Double × Double) Prop :=
  fun pref _ st ↦ st.1.size = n ∧ st.2 = (· * rb)^[pref.length] 1.0 ∧
    ∀ i < coeffRow * pref.length, st.1[i]! = cellProduct rb rc i

/-- The invariant of the inner loop of `JPoints.tubeCellProducts` over `k`, for the row `j` and
the power `rbj` of `rb`, whose state is the array of the products and the product `rck`: the array
of `n` entries, `rck = rbj rc ^ k` by repeated products, and the products up to `P(j, k)` written.
-/
def ProductsRowInvariant (rb rc : Double) (n j : ℕ) (rbj : Double) :
    Std.WP.Invariant ℕ (Array Double × Double) Prop :=
  fun pref _ st ↦ st.1.size = n ∧ st.2 = (· * rc)^[pref.length] rbj ∧
    ∀ i < coeffRow * j + pref.length, st.1[i]! = cellProduct rb rc i

section Products

variable {rb rc : Double} {n : ℕ} {pref suff pref' suff' : List ℕ} {cur cur' : ℕ}
  {A B : Array Double} {x y : Double}

theorem productsInvariant_nil (h : B.size = n) {l : List ℕ} :
    ProductsInvariant rb rc n [] l (B, 1.0) :=
  -- not `rfl`, whose check makes the external checker `nanoda` evaluate the literal `1.0`, which
  -- overflows its stack
  ⟨h, (Function.iterate_zero_apply ..).symm, fun i hi ↦ by simp at hi⟩

theorem productsRowInvariant_nil (hc : ForIn.toList [:coeffRow] = pref ++ cur :: suff)
    (h : ProductsInvariant rb rc n pref (cur :: suff) (A, x)) {l : List ℕ} :
    ProductsRowInvariant rb rc n cur x [] l (A, x) :=
  ⟨h.1, rfl, fun i hi ↦ h.2.2 i (by
    simpa [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc] using hi)⟩

theorem cellProduct_coeffIndex {j k : ℕ} (hk : k < coeffRow) :
    cellProduct rb rc (coeffIndex j k) = (· * rc)^[k] ((· * rb)^[j] 1.0) := by
  rw [cellProduct, coeffIndex_mod_coeffRow hk, coeffIndex_div_coeffRow hk]

theorem productsRowInvariant_step (hn : n = numCoeffs)
    (hc : ForIn.toList [:coeffRow] = pref ++ cur :: suff)
    (hc' : ForIn.toList [:coeffRow] = pref' ++ cur' :: suff')
    (hx : ProductsInvariant rb rc n pref (cur :: suff) (A, x))
    (h : ProductsRowInvariant rb rc n cur x pref' (cur' :: suff') (B, y)) :
    ProductsRowInvariant rb rc n cur x (pref' ++ [cur']) suff'
      (B.set! (coeffIndex cur cur') y, y * rc) := by
  have hj := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hk := Std.Legacy.Range.lt_of_toList_eq_append_cons hc'
  have hjl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hkl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc'
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  have hidx : coeffIndex cur cur' < B.size := by
    have : coeffRow * cur + cur' < coeffRow * coeffRow := by nlinarith
    simp only [coeffIndex, numCoeffs] at hn ⊢
    lia
  refine ⟨by simpa using h1, ?_, fun i hi ↦ ?_⟩
  · simp only [h2, hkl, List.length_append, List.length_singleton, Function.iterate_succ_apply']
  · rw [List.length_append, List.length_singleton, hkl] at hi
    obtain ⟨-, hx2, -⟩ := hx
    dsimp only at hx2 ⊢
    rcases Nat.lt_or_ge i (coeffRow * cur + cur') with hlt | hge
    · rw [Array.getElem!_set!_ne _ _ _ _ (by simp only [coeffIndex]; lia)]
      exact h3 i (by lia)
    · rw [show i = coeffIndex cur cur' by rw [coeffIndex]; lia, Array.getElem!_set!_self _ _ _ hidx,
        cellProduct_coeffIndex hk, h2, hkl, hx2, hjl]

theorem productsInvariant_step (hc : ForIn.toList [:coeffRow] = pref ++ cur :: suff)
    (hx : ProductsInvariant rb rc n pref (cur :: suff) (A, x))
    (h : ProductsRowInvariant rb rc n cur x (ForIn.toList [:coeffRow]) [] (B, y)) :
    ProductsInvariant rb rc n (pref ++ [cur]) suff (B, x * rb) := by
  have hjl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  obtain ⟨h1, -, h3⟩ := h
  obtain ⟨-, hx2, -⟩ := hx
  dsimp only at h1 h3 hx2 ⊢
  refine ⟨h1, ?_, fun i hi ↦ h3 i ?_⟩
  · simp only [hx2, hjl, List.length_append, List.length_singleton,
      Function.iterate_succ_apply']
  · simp only [List.length_append, List.length_singleton, hjl,
      Std.Legacy.Range.length_toList] at hi ⊢
    lia

theorem productsInvariant_post (hn : n = numCoeffs)
    (h : ProductsInvariant rb rc n (ForIn.toList [:coeffRow]) [] (B, x)) :
    B = cellProducts rb rc := by
  obtain ⟨h1, -, h3⟩ := h
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at h3
  refine Array.ext_getElem! (by simp [size_cellProducts, h1, hn]) fun i hi ↦ ?_
  have hi' : i < numCoeffs := by simp_all
  rw [h3 i (by simpa [numCoeffs] using hi'), cellProducts, getElem!_coeffArray_of_lt _ hi']
  rfl

theorem productsInvariant_post_recompute {c : TubeCellCache} (hn : c.rp.size = numCoeffs)
    (hc : (!rb.beq c.lastRb || !rc.beq c.lastRc) = true)
    (h : ProductsInvariant rb rc c.rp.size (ForIn.toList [:coeffRow]) [] (B, x)) :
    { rp := B, lastRb := rb, lastRc := rc } = if (!rb.beq c.lastRb || !rc.beq c.lastRc) = true then
      { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } else c := by
  rw [ite_eq_left hc, productsInvariant_post hn h]

theorem products_post_keep {c : TubeCellCache}
    (hc : ¬(!rb.beq c.lastRb || !rc.beq c.lastRc) = true) :
    c = if (!rb.beq c.lastRb || !rc.beq c.lastRc) = true then
      { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } else c :=
  (ite_eq_right hc).symm

end Products

theorem tubeCellProducts_spec (c : TubeCellCache) (rb rc : Double) :
    ⦃ c.rp.size = numCoeffs ⦄
    tubeCellProducts c rb rc
    ⦃ fun r ↦ r = if (!rb.beq c.lastRb || !rc.beq c.lastRc) = true then
        { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } else c ⦄ := by
  vcgen [tubeCellProducts] invariants
  | inv1 => ProductsInvariant rb rc c.rp.size
  | inv2 _ cur _ _ _ x _ => ProductsRowInvariant rb rc c.rp.size cur x
  all_goals try dsimp only at *
  all_goals first
    | exact productsInvariant_nil rfl
    | exact productsRowInvariant_nil ‹_› ‹_›
    | exact productsRowInvariant_step ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact productsInvariant_step ‹_› ‹_› ‹_›
    | exact productsInvariant_post_recompute ‹_› ‹_› ‹_›
    | exact products_post_keep ‹_›

theorem run_tubeCellProducts {c : TubeCellCache} (h : c.rp.size = numCoeffs) (rb rc : Double) :
    (tubeCellProducts c rb rc).run = if (!rb.beq c.lastRb || !rc.beq c.lastRc) = true then
      { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } else c :=
  (tubeCellProducts_spec c rb rc).le_wp h

/-! ### The cache of the products -/

theorem run_tubeCellProducts_initial_of_ne {rb rc : Double} (h : rb ≠ -1.0) :
    (tubeCellProducts .initial rb rc).run =
      { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } := by
  rw [run_tubeCellProducts (by simp [TubeCellCache.initial]), ite_eq_left]
  have : rb.beq (-1.0) = false := by
    by_contra hb
    exact h (Double.eq_of_beq (Bool.not_eq_false _ ▸ hb) (by decide))
  simp [TubeCellCache.initial, this]

theorem TubeState.WF.rp_eq_cellProducts {t : TubeState} (ht : t.WF) (h : t.cache.lastRb ≠ -1.0) :
    t.cache.rp = cellProducts t.cache.lastRb t.cache.lastRc := by
  rw [(ht.lastRb_eq_or_rp_eq.resolve_left h).2, run_tubeCellProducts_initial_of_ne h]

theorem TubeState.WF.with_cache {t : TubeState} (ht : t.WF) {c : TubeCellCache}
    (hc : c.rp.size = numCoeffs) (hl : c.lastRb = -1.0 ∨ c.lastRb ≠ -0.0 ∧
      c.rp = (tubeCellProducts .initial c.lastRb c.lastRc).run.rp) :
    { t with cache := c }.WF :=
  ⟨ht.size_k0, ht.size_k1, ht.size_k2, ht.size_ka, hc, hl, ht.size_bandNr, ht.size_bandRg⟩

theorem TubeState.WF.with_tubeCellProducts {t : TubeState} (ht : t.WF) {rb : Double}
    (hrb : rb ≠ -0.0) (rc : Double) :
    { t with cache := (tubeCellProducts t.cache rb rc).run }.WF := by
  rw [run_tubeCellProducts ht.size_rp]
  split_ifs
  · refine ht.with_cache (size_cellProducts rb rc) ?_
    by_cases h : rb = -1.0
    · exact .inl h
    · exact .inr ⟨hrb, by rw [run_tubeCellProducts_initial_of_ne h]⟩
  · exact ht

/-- From a consistent state whose cache holds products of other half-sizes or none, the cache after
the products of a cell with the half-sizes `rb` without a sign bit and `rc` not a zero holds the
products of `(rb, rc)` with these half-sizes: a cache that the comparison `!=` finds equal holds
them bit for bit. -/
theorem TubeState.WF.run_tubeCellProducts {t : TubeState} (ht : t.WF) {rb rc : Double}
    (hrb : rb.signBit = false) (hrc : rc.isZero = false) :
    (tubeCellProducts t.cache rb rc).run =
      { rp := cellProducts rb rc, lastRb := rb, lastRc := rc } := by
  rw [JPoints.run_tubeCellProducts ht.size_rp]
  split_ifs with h
  · rfl
  · simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or,
      Bool.not_eq_false] at h
    have hne : t.cache.lastRb ≠ -1.0 := fun he ↦ by
      rw [he, Double.beq_neg_one_eq_false hrb] at h
      exact Bool.false_ne_true h.1
    have hb := Double.eq_of_beq_of_signBit_eq_false h.1 hrb
      (ht.lastRb_eq_or_rp_eq.resolve_left hne).1
    have hc := Double.eq_of_beq ((Double.beq_comm _ _).trans h.2) hrc
    have hp := ht.rp_eq_cellProducts hne
    rw [← hb, hc] at hp
    rw [← hp, hb, ← hc]

/-! ### The polynomials of a first coordinate -/

/-- The coefficients of `K0` that `tube_a_init` sets for the first coordinate `a` from zeros
(`JPoints.tubeAInitK0`), whatever `K0` held before. -/
def tubeK0 (kd : TubeCoeffs) (a : ℤ) : Array Double :=
  tubeAInitK0 kd (.replicate numCoeffs 0.0) (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
    (Double.ofInt a * Double.ofInt a * Double.ofInt a)
    (Double.ofInt a * Double.ofInt a * Double.ofInt a * Double.ofInt a)

/-- The coefficients of `K1` that `tube_a_init` sets for the first coordinate `a` from zeros
(`JPoints.tubeAInitK1K2`). -/
def tubeK1 (kd : TubeCoeffs) (a : ℤ) : Array Double :=
  (tubeAInitK1K2 kd (.replicate numCoeffs 0.0) (.replicate numCoeffs 0.0) (Double.ofInt a)
    (Double.ofInt a * Double.ofInt a) (Double.ofInt a * Double.ofInt a * Double.ofInt a)).1

/-- The coefficients of `K2` that `tube_a_init` sets for the first coordinate `a` from zeros
(`JPoints.tubeAInitK1K2`). -/
def tubeK2 (kd : TubeCoeffs) (a : ℤ) : Array Double :=
  (tubeAInitK1K2 kd (.replicate numCoeffs 0.0) (.replicate numCoeffs 0.0) (Double.ofInt a)
    (Double.ofInt a * Double.ofInt a) (Double.ofInt a * Double.ofInt a * Double.ofInt a)).2

/-- The coefficients `|K0| + th |K1| + th2 |K2|` of `KA` that `tube_a_init` sets for the first
coordinate `a`, coefficient by coefficient. -/
def tubeKA (kd : TubeCoeffs) (th th2 : Double) (a : ℤ) : Array Double :=
  Array.ofFn fun i : Fin numCoeffs ↦
    (tubeK0 kd a)[i]!.fabs + th * (tubeK1 kd a)[i]!.fabs + th2 * (tubeK2 kd a)[i]!.fabs

/-- The invariant of the loop of `JPoints.tubeAInit` that sets the coefficients of `K0`, `K1` and
`K2` to `0.0`: the arrays of `JPoints.numCoeffs` entries, the first ones `0.0`. -/
def ZeroPolysInvariant : Std.WP.Invariant ℕ (Array Double × Array Double × Array Double) Prop :=
  fun pref _ st ↦ st.1.size = numCoeffs ∧ st.2.1.size = numCoeffs ∧ st.2.2.size = numCoeffs ∧
    ∀ i < pref.length, st.1[i]! = 0.0 ∧ st.2.1[i]! = 0.0 ∧ st.2.2[i]! = 0.0

/-- The invariant of the loop of `JPoints.tubeAInit` that sets the coefficients of `KA`: the array
of `JPoints.numCoeffs` entries, the first ones those of `JPoints.tubeKA`. -/
def BoundCoeffsInvariant (kd : TubeCoeffs) (th th2 : Double) (a : ℤ) :
    Std.WP.Invariant ℕ (Array Double) Prop :=
  fun pref _ ka ↦ ka.size = numCoeffs ∧ ∀ i < pref.length, ka[i]! =
    (tubeKA kd th th2 a)[i]!

section AInit

variable {kd : TubeCoeffs} {th th2 : Double} {a : ℤ} {t : TubeState} {pref suff : List ℕ}
  {cur : ℕ} {k0 k1 k2 ka : Array Double}

theorem zeroPolysInvariant_nil
    (h : t.k0.size = numCoeffs ∧ t.k1.size = numCoeffs ∧ t.k2.size = numCoeffs ∧
      t.ka.size = numCoeffs) {l : List ℕ} :
    ZeroPolysInvariant [] l (t.k0, t.k1, t.k2) :=
  ⟨h.1, h.2.1, h.2.2.1, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

theorem zeroPolysInvariant_step (hc : ForIn.toList [:numCoeffs] = pref ++ cur :: suff)
    (h : ZeroPolysInvariant pref (cur :: suff) (k0, k1, k2)) :
    ZeroPolysInvariant (pref ++ [cur]) suff
      (k0.set! cur 0.0, k1.set! cur 0.0, k2.set! cur 0.0) := by
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨h0, h1, h2, h3⟩ := h
  dsimp only at h0 h1 h2 h3
  refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, fun i hi ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hl] at hi
  dsimp only
  rcases Nat.lt_or_ge i cur with hlt | hge
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia),
      Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h3 i (by lia)
  · rw [show i = cur by lia, Array.getElem!_set!_self _ _ _ (by lia),
      Array.getElem!_set!_self _ _ _ (by lia), Array.getElem!_set!_self _ _ _ (by lia)]
    exact ⟨rfl, rfl, rfl⟩

theorem ZeroPolysInvariant.eq (h : ZeroPolysInvariant (ForIn.toList [:numCoeffs]) [] (k0, k1, k2)) :
    k0 = .replicate numCoeffs 0.0 ∧ k1 = .replicate numCoeffs 0.0 ∧
      k2 = .replicate numCoeffs 0.0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  dsimp only at h0 h1 h2 h3
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at h3
  refine ⟨Array.ext_getElem! (by simp [h0]) fun i hi ↦ ?_,
    Array.ext_getElem! (by simp [h1]) fun i hi ↦ ?_,
    Array.ext_getElem! (by simp [h2]) fun i hi ↦ ?_⟩
  · simp [(h3 i (h0 ▸ hi)).1, h0 ▸ hi]
  · simp [(h3 i (h1 ▸ hi)).2.1, h1 ▸ hi]
  · simp [(h3 i (h2 ▸ hi)).2.2, h2 ▸ hi]

theorem ZeroPolysInvariant.tubeAInitK0_eq
    (h : ZeroPolysInvariant (ForIn.toList [:numCoeffs]) [] (k0, k1, k2)) :
    tubeAInitK0 kd k0 (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
      (Double.ofInt a * Double.ofInt a * Double.ofInt a)
      (Double.ofInt a * Double.ofInt a * Double.ofInt a * Double.ofInt a) = tubeK0 kd a := by
  rw [h.eq.1, tubeK0]

theorem ZeroPolysInvariant.tubeAInitK1K2_eq
    (h : ZeroPolysInvariant (ForIn.toList [:numCoeffs]) [] (k0, k1, k2)) :
    tubeAInitK1K2 kd k1 k2 (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
      (Double.ofInt a * Double.ofInt a * Double.ofInt a) = (tubeK1 kd a, tubeK2 kd a) := by
  rw [h.eq.2.1, h.eq.2.2, tubeK1, tubeK2]

theorem boundCoeffsInvariant_nil
    (h : t.k0.size = numCoeffs ∧ t.k1.size = numCoeffs ∧ t.k2.size = numCoeffs ∧
      t.ka.size = numCoeffs) {l : List ℕ} :
    BoundCoeffsInvariant kd th th2 a [] l t.ka :=
  ⟨h.2.2.2, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

theorem getElem!_tubeKA {i : ℕ} (hi : i < numCoeffs) :
    (tubeKA kd th th2 a)[i]! =
      (tubeK0 kd a)[i]!.fabs + th * (tubeK1 kd a)[i]!.fabs + th2 * (tubeK2 kd a)[i]!.fabs := by
  simp [tubeKA, hi]

theorem boundCoeffsInvariant_step (hc : ForIn.toList [:numCoeffs] = pref ++ cur :: suff)
    (h : BoundCoeffsInvariant kd th th2 a pref (cur :: suff) ka) :
    BoundCoeffsInvariant kd th th2 a (pref ++ [cur]) suff (ka.set! cur ((tubeK0 kd a)[cur]!.fabs +
      th * (tubeK1 kd a)[cur]!.fabs + th2 * (tubeK2 kd a)[cur]!.fabs)) := by
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨h0, h1⟩ := h
  refine ⟨by simpa using h0, fun i hi ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hl] at hi
  rcases Nat.lt_or_ge i cur with hlt | hge
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h1 i (by lia)
  · rw [show i = cur by lia, Array.getElem!_set!_self _ _ _ (by lia),
      getElem!_tubeKA hcur]

theorem BoundCoeffsInvariant.eq
    (h : BoundCoeffsInvariant kd th th2 a (ForIn.toList [:numCoeffs]) [] ka) :
    ka = tubeKA kd th th2 a := by
  obtain ⟨h0, h1⟩ := h
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at h1
  exact Array.ext_getElem! (by simp [h0, tubeKA]) fun i hi ↦ h1 i (h0 ▸ hi)

theorem tubeAInit_post {height : ℤ}
    (hz : ZeroPolysInvariant (ForIn.toList [:numCoeffs]) [] (k0, k1, k2))
    (hb : BoundCoeffsInvariant kd th th2 a (ForIn.toList [:numCoeffs]) [] ka) {v : Double}
    (hv : v = (tubeEval ka 4 (Double.ofInt height) (Double.ofInt (height + longLength))).run) :
    { k0 := tubeAInitK0 kd k0 (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
          (Double.ofInt a * Double.ofInt a * Double.ofInt a)
          (Double.ofInt a * Double.ofInt a * Double.ofInt a * Double.ofInt a),
        k1 := (tubeAInitK1K2 kd k1 k2 (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
          (Double.ofInt a * Double.ofInt a * Double.ofInt a)).1,
        k2 := (tubeAInitK1K2 kd k1 k2 (Double.ofInt a) (Double.ofInt a * Double.ofInt a)
          (Double.ofInt a * Double.ofInt a * Double.ofInt a)).2,
        ka := ka, tubeOk := v.lt tubeBig, tubeNcells := t.tubeNcells, cache := t.cache,
        bands := t.bands : TubeState } = { t with
      k0 := tubeK0 kd a, k1 := tubeK1 kd a, k2 := tubeK2 kd a,
      ka := tubeKA kd th th2 a,
      tubeOk := (tubeEval (tubeKA kd th th2 a) 4 (Double.ofInt height)
        (Double.ofInt (height + longLength))).run.lt tubeBig } := by
  rw [hz.tubeAInitK0_eq, hz.tubeAInitK1K2_eq, hv, hb.eq]

end AInit

theorem tubeAInit_value (kd : TubeCoeffs) (height : ℤ) (th th2 : Double) (t : TubeState) (a : ℤ) :
    ⦃ t.k0.size = numCoeffs ∧ t.k1.size = numCoeffs ∧ t.k2.size = numCoeffs ∧
      t.ka.size = numCoeffs ⦄
    tubeAInit kd height th th2 t a
    ⦃ fun r ↦ r = { t with
        k0 := tubeK0 kd a, k1 := tubeK1 kd a, k2 := tubeK2 kd a,
        ka := tubeKA kd th th2 a,
        tubeOk := (tubeEval (tubeKA kd th th2 a) 4 (Double.ofInt height)
          (Double.ofInt (height + longLength))).run.lt tubeBig } ⦄ := by
  vcgen [tubeAInit, Std.WP.Id.triple_eq_run (tubeEval _ _ _ _)] invariants
  · ZeroPolysInvariant
  · BoundCoeffsInvariant kd th th2 a
  all_goals first
    | exact zeroPolysInvariant_nil ‹_›
    | exact zeroPolysInvariant_step ‹_› ‹_›
    | exact boundCoeffsInvariant_nil ‹_›
    | (rw [ZeroPolysInvariant.tubeAInitK0_eq ‹_›, ZeroPolysInvariant.tubeAInitK1K2_eq ‹_›]
       exact boundCoeffsInvariant_step ‹_› ‹_›)
    | exact tubeAInit_post ‹_› ‹_› ‹_›

theorem size_tubeK (kd : TubeCoeffs) (a : ℤ) :
    (tubeK0 kd a).size = numCoeffs ∧ (tubeK1 kd a).size = numCoeffs ∧
      (tubeK2 kd a).size = numCoeffs := by
  simp [tubeK0, tubeK1, tubeK2, tubeAInitK0, tubeAInitK1K2]

theorem TubeState.WF.run_tubeAInit {t : TubeState} (ht : t.WF) (kd : TubeCoeffs) (height : ℤ)
    (th th2 : Double) (a : ℤ) :
    (tubeAInit kd height th th2 t a).run = { t with
        k0 := tubeK0 kd a, k1 := tubeK1 kd a, k2 := tubeK2 kd a,
        ka := tubeKA kd th th2 a,
        tubeOk := (tubeEval (tubeKA kd th th2 a) 4 (Double.ofInt height)
          (Double.ofInt (height + longLength))).run.lt tubeBig } :=
  (tubeAInit_value kd height th th2 t a).le_wp ⟨ht.size_k0, ht.size_k1, ht.size_k2, ht.size_ka⟩

/-- `tube_a_init` on the initial state of the analysis. -/
theorem run_tubeAInit_initial (kd : TubeCoeffs) (height : ℤ) (th th2 : Double) (a : ℤ) :
    (tubeAInit kd height th th2 .initial a).run = { TubeState.initial with
        k0 := tubeK0 kd a, k1 := tubeK1 kd a, k2 := tubeK2 kd a,
        ka := tubeKA kd th th2 a,
        tubeOk := (tubeEval (tubeKA kd th th2 a) 4 (Double.ofInt height)
          (Double.ofInt (height + longLength))).run.lt tubeBig } :=
  TubeState.wf_initial.run_tubeAInit kd height th th2 a

theorem size_tubeKA (kd : TubeCoeffs) (th th2 : Double) (a : ℤ) :
    (tubeKA kd th th2 a).size = numCoeffs := by
  rw [tubeKA, Array.size_ofFn]

theorem TubeState.WF.with_polys {t : TubeState} (ht : t.WF) (kd : TubeCoeffs) (th th2 : Double)
    (a : ℤ) (ok : Bool) :
    { t with
        k0 := tubeK0 kd a, k1 := tubeK1 kd a, k2 := tubeK2 kd a,
        ka := tubeKA kd th th2 a,
        tubeOk := ok }.WF := by
  obtain ⟨h0, h1, h2⟩ := size_tubeK kd a
  refine ⟨?_, ?_, ?_, ?_, ht.size_rp, ht.lastRb_eq_or_rp_eq, ht.size_bandNr, ht.size_bandRg⟩ <;>
    dsimp only
  exacts [h0, h1, h2, size_tubeKA ..]

/-- `tube_a_init` on a consistent state `t` of the analysis sets the polynomials `K0`, `K1`, `K2`
and `KA` of the first coordinate `a` and `tube_ok` as from the initial state, since it writes the
arrays of `t` whole, and keeps the counter of the cells, the cache of `tube_cell` and the bands of
`t`; the state stays consistent. -/
@[spec]
theorem tubeAInit_spec (kd : TubeCoeffs) (height : ℤ) (th th2 : Double) (t : TubeState) (a : ℤ) :
    ⦃ t.WF ⦄
    tubeAInit kd height th th2 t a
    ⦃ fun r ↦ r.WF ∧ r = { (tubeAInit kd height th th2 .initial a).run with
        tubeNcells := t.tubeNcells, cache := t.cache, bands := t.bands } ⦄ :=
  Std.WP.Id.triple_of_run fun ht ↦ by
    have e := ht.run_tubeAInit kd height th th2 a
    refine ⟨e ▸ ht.with_polys kd th th2 a _, ?_⟩
    generalize hT : (tubeAInit kd height th th2 .initial a).run = T
    rw [e, ← hT, run_tubeAInit_initial]

theorem wf_run_tubeAInit_initial (kd : TubeCoeffs) (height : ℤ) (th th2 : Double) (a : ℤ) :
    (tubeAInit kd height th th2 .initial a).run.WF :=
  ((tubeAInit_spec kd height th th2 .initial a).le_wp TubeState.wf_initial).1

theorem TubeState.WF.with_bands {t : TubeState} (ht : t.WF) {bd : TubeBands}
    (h1 : bd.bandNr.size = tubeBand) (h2 : bd.bandRg.size = 2 * tubeRanges * tubeBand) :
    { t with bands := bd }.WF :=
  ⟨ht.size_k0, ht.size_k1, ht.size_k2, ht.size_ka, ht.size_rp, ht.lastRb_eq_or_rp_eq, h1, h2⟩

theorem TubeState.WF.with_emitRows {t : TubeState} (ht : t.WF) (bLo bHi iLo iHi : ℤ) :
    { t with bands := emitRows t.bands bLo bHi iLo iHi }.WF :=
  ht.with_bands ((size_emitRows ..).1.trans ht.size_bandNr)
    ((size_emitRows ..).2.trans ht.size_bandRg)

/-! ### The analysis of a cell -/

theorem run_tubeCellDecide (th th2 : Double) (t : TubeState) (bLo bHi iLo iHi : ℤ) :
    (tubeCellDecide th th2 t bLo bHi iLo iHi).run =
      ((tubeCellAnalyze th th2
          { t with cache := (tubeCellProducts t.cache (0.5 * Double.ofInt (bHi - bLo))
            (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run }
          (tubeCellProducts t.cache (0.5 * Double.ofInt (bHi - bLo))
            (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run.rp
          (0.5 * Double.ofInt (bLo + bHi)) (0.5 * Double.ofInt (bHi - bLo))
          (32.0 * Double.ofInt (iLo + iHi) - 0.5) (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run.1,
        (tubeCellAnalyze th th2
          { t with cache := (tubeCellProducts t.cache (0.5 * Double.ofInt (bHi - bLo))
            (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run }
          (tubeCellProducts t.cache (0.5 * Double.ofInt (bHi - bLo))
            (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run.rp
          (0.5 * Double.ofInt (bLo + bHi)) (0.5 * Double.ofInt (bHi - bLo))
          (32.0 * Double.ofInt (iLo + iHi) - 0.5) (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run.2,
        { t with cache := (tubeCellProducts t.cache (0.5 * Double.ofInt (bHi - bLo))
          (32.0 * Double.ofInt (iHi - iLo) - 0.5)).run }) := rfl

theorem run_tubeCell_of_tubeOk_eq_false {th th2 : Double} {t : TubeState} (h : t.tubeOk = false)
    (bLo bHi iLo iHi : ℤ) :
    (tubeCell th th2 t bLo bHi iLo iHi).run = { t with
      tubeNcells := t.tubeNcells + 1, bands := emitRows t.bands bLo bHi iLo iHi } := by
  rw [tubeCell, ite_eq_left (by simp [h]), run_tubeEmitRows]

theorem run_tubeCell_of_tubeOk {th th2 : Double} {t : TubeState} (h : t.tubeOk = true)
    (bLo bHi iLo iHi : ℤ) :
    (tubeCell th th2 t bLo bHi iLo iHi).run =
      let d := (tubeCellDecide th th2 { t with tubeNcells := t.tubeNcells + 1 } bLo bHi iLo
        iHi).run
      if d.2.1 = true then d.2.2
      else if d.1 = true then (tubeEmitRows d.2.2 bLo bHi iLo iHi).run
      else if iHi - iLo > 1 ∧ bHi - bLo + 1 ≤ tubeRows * (iHi - iLo) then
        (tubeCell th th2 (tubeCell th th2 d.2.2 bLo bHi iLo (iLo + (iHi - iLo) / 2)).run bLo bHi
          (iLo + (iHi - iLo) / 2) iHi).run
      else if bHi - bLo + 1 > tubeRows then
        (tubeCell th th2 (tubeCell th th2 d.2.2 bLo (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi).run
          (bLo + (bHi - bLo + 1 - 1) / 2 + 1) bHi iLo iHi).run
      else (tubeEmitRows d.2.2 bLo bHi iLo (iLo + 1)).run := by
  rw [tubeCell, ite_eq_right (by simp [h])]
  rfl

/-- The state `t'` of the analysis of the tube has the polynomials of `t` and its `tube_ok`, the
fields that `tube_cell` reads and does not write. -/
def TubeState.EqPolys (t t' : TubeState) : Prop :=
  t'.k0 = t.k0 ∧ t'.k1 = t.k1 ∧ t'.k2 = t.k2 ∧ t'.ka = t.ka ∧ t'.tubeOk = t.tubeOk

namespace TubeState.EqPolys

variable {t t' : TubeState} (h : t.EqPolys t')
include h

theorem k0_eq : t'.k0 = t.k0 := h.1

theorem k1_eq : t'.k1 = t.k1 := h.2.1

theorem k2_eq : t'.k2 = t.k2 := h.2.2.1

theorem ka_eq : t'.ka = t.ka := h.2.2.2.1

theorem tubeOk_eq : t'.tubeOk = t.tubeOk := h.2.2.2.2

end TubeState.EqPolys

theorem TubeState.EqPolys.refl (t : TubeState) : t.EqPolys t :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem TubeState.EqPolys.trans {t t' t'' : TubeState} (h : t.EqPolys t') (h' : t'.EqPolys t'') :
    t.EqPolys t'' :=
  ⟨h'.k0_eq.trans h.k0_eq, h'.k1_eq.trans h.k1_eq, h'.k2_eq.trans h.k2_eq,
    h'.ka_eq.trans h.ka_eq, h'.tubeOk_eq.trans h.tubeOk_eq⟩

/-- A state with the polynomials and the flag `tube_ok` of `t` is `t` with its own counter of the
cells, cache and bands. -/
theorem TubeState.eqPolys_iff_eq_with {t r : TubeState} :
    t.EqPolys r ↔
      r = { t with tubeNcells := r.tubeNcells, cache := r.cache, bands := r.bands } := by
  refine ⟨fun ⟨h0, h1, h2, ha, hok⟩ ↦ ?_, fun h ↦ ?_⟩
  · cases r
    simp_all
  · rw [h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem TubeState.EqPolys.eq_with {t r : TubeState} (h : t.EqPolys r) :
    r = { t with tubeNcells := r.tubeNcells, cache := r.cache, bands := r.bands } :=
  TubeState.eqPolys_iff_eq_with.mp h

theorem TubeState.WF.with_tubeNcells {t : TubeState} (ht : t.WF) (n : ℕ) :
    { t with tubeNcells := n }.WF :=
  ⟨ht.size_k0, ht.size_k1, ht.size_k2, ht.size_ka, ht.size_rp, ht.lastRb_eq_or_rp_eq,
    ht.size_bandNr, ht.size_bandRg⟩

theorem TubeState.WF.run_tubeCellDecide {t : TubeState} (ht : t.WF) (th th2 : Double)
    (bLo bHi iLo iHi : ℤ) :
    (tubeCellDecide th th2 t bLo bHi iLo iHi).run.2.2.WF ∧
      t.EqPolys (tubeCellDecide th th2 t bLo bHi iLo iHi).run.2.2 := by
  rw [JPoints.run_tubeCellDecide]
  exact ⟨ht.with_tubeCellProducts (Double.half_mul_ofInt_ne_negZero _) _, rfl, rfl, rfl, rfl, rfl⟩

private theorem wf_eqPolys_comp {t d r r' : TubeState} (hd : t.EqPolys d)
    (e : r.WF ∧ d.EqPolys r) (f : r.WF → r'.WF ∧ r.EqPolys r') : r'.WF ∧ t.EqPolys r' :=
  ⟨(f e.1).1, hd.trans (e.2.trans (f e.1).2)⟩

theorem TubeState.WF.run_tubeCell {t : TubeState} (ht : t.WF) (th th2 : Double)
    (bLo bHi iLo iHi : ℤ) :
    (tubeCell th th2 t bLo bHi iLo iHi).run.WF ∧
      t.EqPolys (tubeCell th th2 t bLo bHi iLo iHi).run := by
  induction t, bLo, bHi, iLo, iHi using tubeCell.induct with
  | case1 t bLo bHi iLo iHi _ h =>
    rw [run_tubeCell_of_tubeOk_eq_false (by simpa using h)]
    exact ⟨(ht.with_tubeNcells (t.tubeNcells + 1)).with_emitRows bLo bHi iLo iHi, rfl, rfl, rfl,
      rfl, rfl⟩
  | case2 t bLo bHi iLo iHi _ _ _ h ih1 ih2 ih3 ih4 =>
    rw [run_tubeCell_of_tubeOk (by simpa using h)]
    obtain ⟨hd, hd'⟩ :=
      (ht.with_tubeNcells (t.tubeNcells + 1)).run_tubeCellDecide th th2 bLo bHi iLo iHi
    dsimp only
    split_ifs with h1 h2 h3 h4
    · exact ⟨hd, hd'⟩
    · rw [run_tubeEmitRows]
      exact ⟨hd.with_emitRows bLo bHi iLo _, hd'⟩
    · exact wf_eqPolys_comp hd' (ih1 _ h3 hd) (ih2 h3 _)
    · exact wf_eqPolys_comp hd' (ih3 _ h4 hd) (ih4 h4 _)
    · rw [run_tubeEmitRows]
      exact ⟨hd.with_emitRows bLo bHi iLo _, hd'⟩

theorem bandB0_run_tubeCell (th th2 : Double) (t : TubeState) (bLo bHi iLo iHi : ℤ) :
    (tubeCell th th2 t bLo bHi iLo iHi).run.bands.bandB0 = t.bands.bandB0 := by
  induction t, bLo, bHi, iLo, iHi using tubeCell.induct with
  | case1 t bLo bHi iLo iHi _ h =>
    rw [run_tubeCell_of_tubeOk_eq_false (by simpa using h)]
    exact bandB0_emitRows ..
  | case2 t bLo bHi iLo iHi _ _ _ h ih1 ih2 ih3 ih4 =>
    rw [run_tubeCell_of_tubeOk (by simpa using h)]
    dsimp only
    split_ifs with h1 h2 h3 h4
    · rfl
    · rw [run_tubeEmitRows]; exact bandB0_emitRows ..
    · exact (ih2 h3 _).trans (ih1 _ h3)
    · exact (ih4 h4 _).trans (ih3 _ h4)
    · rw [run_tubeEmitRows]; exact bandB0_emitRows ..

theorem tubeCellAnalyze_congr {t t' : TubeState} (h : t.EqPolys t') (th th2 : Double) :
    tubeCellAnalyze th th2 t' = tubeCellAnalyze th th2 t := by
  obtain ⟨h0, h1, h2, ha, -⟩ := h
  funext rp bm rb cm rc
  simp only [tubeCellAnalyze, h0, h1, h2, ha]

/-- The state `t'` of the analysis of the tube that the thread holds and the reference state `t`
agree for a band of `n` rows: both consistent, with the same polynomials, the same first row, the
bands of the band of `n` rows, and the same ranges in each of its rows. -/
structure TubeState.BandSim (n : ℕ) (t t' : TubeState) : Prop where
  /-- The reference state is consistent. -/
  wf : t.WF
  /-- The state of the thread is consistent. -/
  wf' : t'.WF
  /-- The same polynomials. -/
  polys : t.EqPolys t'
  /-- The same first row of the band. -/
  bandB0_eq : t'.bands.bandB0 = t.bands.bandB0
  /-- The reference bands hold the band. -/
  sized : t.bands.Sized n
  /-- The bands of the thread hold the band. -/
  sized' : t'.bands.Sized n
  /-- The same ranges in each row of the band. -/
  rowRanges_eq {r : ℕ} (hr : r < n) : t'.bands.rowRanges r = t.bands.rowRanges r

namespace TubeState.BandSim

variable {n : ℕ} {t t' : TubeState}

theorem emitRows (h : BandSim n t t') {bLo bHi : ℤ} (h0 : t.bands.bandB0 ≤ bLo)
    (h1 : bHi < t.bands.bandB0 + n) (iLo iHi : ℤ) :
    BandSim n { t with bands := JPoints.emitRows t.bands bLo bHi iLo iHi }
      { t' with bands := JPoints.emitRows t'.bands bLo bHi iLo iHi } := by
  obtain ⟨g1, g2, g3⟩ := h.sized.emitRows h0 h1 iLo iHi
  obtain ⟨f1, f2, f3⟩ := h.sized'.emitRows (h.bandB0_eq ▸ h0) (h.bandB0_eq ▸ h1) iLo iHi
  refine ⟨h.wf.with_emitRows .., h.wf'.with_emitRows .., h.polys, ?_, g1, f1, fun {r} hr ↦ ?_⟩
  · exact f2.trans (h.bandB0_eq.trans g2.symm)
  · dsimp only
    rw [f3 r hr, g3 r hr, h.bandB0_eq, h.rowRanges_eq hr]

theorem with_tubeNcells (h : BandSim n t t') (m m' : ℕ) :
    BandSim n { t with tubeNcells := m } { t' with tubeNcells := m' } :=
  ⟨h.wf.with_tubeNcells m, h.wf'.with_tubeNcells m', h.polys, h.bandB0_eq, h.sized, h.sized',
    h.rowRanges_eq⟩

theorem with_cache (h : BandSim n t t') {c : TubeCellCache} (hw : { t with cache := c }.WF)
    (hw' : { t' with cache := c }.WF) :
    BandSim n { t with cache := c } { t' with cache := c } :=
  ⟨hw, hw', h.polys, h.bandB0_eq, h.sized, h.sized', h.rowRanges_eq⟩

theorem run_tubeCellDecide (h : BandSim n t t') (th th2 : Double) {bLo bHi : ℤ}
    (hb : bLo ≤ bHi) (iLo iHi : ℤ) :
    (tubeCellDecide th th2 t' bLo bHi iLo iHi).run.1 =
        (tubeCellDecide th th2 t bLo bHi iLo iHi).run.1 ∧
      (tubeCellDecide th th2 t' bLo bHi iLo iHi).run.2.1 =
        (tubeCellDecide th th2 t bLo bHi iLo iHi).run.2.1 ∧
      BandSim n (tubeCellDecide th th2 t bLo bHi iLo iHi).run.2.2
        (tubeCellDecide th th2 t' bLo bHi iLo iHi).run.2.2 := by
  have hrb := Double.signBit_half_mul_ofInt (show 0 ≤ bHi - bLo by lia)
  have hrc := Double.isZero_thirtyTwo_mul_ofInt_sub_half (iHi - iLo)
  have w := h.wf.with_tubeCellProducts (Double.half_mul_ofInt_ne_negZero (bHi - bLo))
    (32.0 * Double.ofInt (iHi - iLo) - 0.5)
  have w' := h.wf'.with_tubeCellProducts (Double.half_mul_ofInt_ne_negZero (bHi - bLo))
    (32.0 * Double.ofInt (iHi - iLo) - 0.5)
  rw [h.wf.run_tubeCellProducts hrb hrc] at w
  rw [h.wf'.run_tubeCellProducts hrb hrc] at w'
  rw [JPoints.run_tubeCellDecide, JPoints.run_tubeCellDecide, h.wf.run_tubeCellProducts hrb hrc,
    h.wf'.run_tubeCellProducts hrb hrc]
  generalize (⟨_, _, _⟩ : TubeCellCache) = c at w w' ⊢
  rw [tubeCellAnalyze_congr (t := { t with cache := c }) (t' := { t' with cache := c }) h.polys]
  exact ⟨rfl, rfl, h.with_cache w w'⟩

-- lint: allow long-proof: the functional induction of `tube_cell`, one line or two per branch
theorem run_tubeCell (h : BandSim n t t') (th th2 : Double) {bLo bHi : ℤ}
    (h0 : t.bands.bandB0 ≤ bLo) (hlo : bLo ≤ bHi) (h1 : bHi < t.bands.bandB0 + n) (iLo iHi : ℤ) :
    BandSim n (tubeCell th th2 t bLo bHi iLo iHi).run (tubeCell th th2 t' bLo bHi iLo iHi).run := by
  induction t, bLo, bHi, iLo, iHi using tubeCell.induct generalizing t' with
  | case1 t bLo bHi iLo iHi _ hok =>
    have hf : t.tubeOk = false := by simpa using hok
    rw [run_tubeCell_of_tubeOk_eq_false hf,
      run_tubeCell_of_tubeOk_eq_false (h.polys.tubeOk_eq ▸ hf)]
    exact (h.with_tubeNcells (t.tubeNcells + 1) (t'.tubeNcells + 1)).emitRows h0 h1 iLo iHi
  | case2 t bLo bHi iLo iHi rows words _ hok ih1 ih2 ih3 ih4 =>
    simp only [rows, words] at ih1 ih2 ih3 ih4
    have ht : t.tubeOk = true := by simpa using hok
    rw [run_tubeCell_of_tubeOk ht, run_tubeCell_of_tubeOk (h.polys.tubeOk_eq ▸ ht)]
    obtain ⟨e1, e2, hs⟩ := (h.with_tubeNcells (t.tubeNcells + 1)
      (t'.tubeNcells + 1)).run_tubeCellDecide th th2 hlo iLo iHi
    simp only [e1, e2, run_tubeEmitRows]
    split_ifs with g1 g2 g3 g4
    · exact hs
    · exact hs.emitRows h0 h1 iLo iHi
    · exact ih2 g3 _ (ih1 _ g3 hs h0 hlo h1) (by rwa [bandB0_run_tubeCell]) hlo
        (by rwa [bandB0_run_tubeCell])
    · have := tubeRows_pos
      exact ih4 g4 _ (ih3 _ g4 hs h0 (by lia) ((show _ ≤ bHi by lia).trans_lt h1))
        (by rw [bandB0_run_tubeCell]; exact h0.trans (by lia)) (by lia)
        (by rw [bandB0_run_tubeCell]; exact h1)
    · exact hs.emitRows h0 h1 iLo (iLo + 1)

end TubeState.BandSim

/-- The analysis of a cell of the rows `bLo..bHi` of a band and of the words `[iLo, iHi)` keeps the
ranges of each of its rows in increasing order, and within `[L, iHi)` when they were within
`[L, iLo)`, since it collects the words of a row in increasing order; it changes no other row
(`JPoints.TubeBands.CellRanges`). -/
-- lint: allow long-proof: the functional induction of `tube_cell`, one line or two per branch
theorem TubeBands.Sized.rangesIn_run_tubeCell (th th2 : Double) {n : ℕ} {L : ℤ} (t : TubeState)
    (bLo bHi iLo iHi : ℤ) (hs : t.bands.Sized n) (h0 : t.bands.bandB0 ≤ bLo)
    (h1 : bHi < t.bands.bandB0 + n) (hL : L ≤ iLo) (hw : iLo < iHi)
    (hr : ∀ r < n, bLo ≤ t.bands.bandB0 + r → t.bands.bandB0 + r ≤ bHi →
      RangesIn L iLo (t.bands.rowRanges r)) :
    TubeBands.CellRanges n L iHi t.bands bLo bHi (tubeCell th th2 t bLo bHi iLo iHi).run.bands := by
  induction t, bLo, bHi, iLo, iHi using tubeCell.induct with
  | case1 t bLo bHi iLo iHi _ hok =>
    rw [run_tubeCell_of_tubeOk_eq_false (by simpa using hok)]
    exact hs.cellRanges_emitRows h0 h1 hL hw hr
  | case2 t bLo bHi iLo iHi rows words _ hok ih1 ih2 ih3 ih4 =>
    simp only [rows, words] at ih1 ih2 ih3 ih4
    rw [run_tubeCell_of_tubeOk (by simpa using hok)]
    set D := (tubeCellDecide th th2 { t with tubeNcells := t.tubeNcells + 1 } bLo bHi iLo
      iHi).run
    have hd : D.2.2.bands = t.bands := rfl
    simp only [run_tubeEmitRows]
    split_ifs with g1 g2 g3 g4
    · exact (hs.cellRanges_self hr).mono hw.le
    · exact hs.cellRanges_emitRows h0 h1 hL hw hr
    · have hb := bandB0_run_tubeCell th th2 D.2.2 bLo bHi iLo (iLo + (iHi - iLo) / 2)
      exact (ih1 D.2.2 g3 hs h0 h1 hL (by lia) hr).trans_words hb fun hs' hr' ↦
        ih2 g3 _ hs' (hb ▸ h0) (hb ▸ h1) (by lia) (by lia) hr'
    · have e := ih3 D.2.2 g4 hs h0 (by lia) hL hw fun r hrn hr1 hr2 ↦ hr r hrn hr1 (by lia)
      have hb := bandB0_run_tubeCell th th2 D.2.2 bLo (bLo + (bHi - bLo + 1 - 1) / 2) iLo iHi
      exact e.trans_rows hb (by lia) (by lia) (ih4 g4 _ e.1 (by rw [hb]; lia)
        (by rw [hb]; exact h1) hL hw (e.rangesIn_of_not hb (by lia) hr))
    · exact (hs.cellRanges_emitRows h0 h1 hL (by lia) hr).mono (by lia)

/-- `tube_cell` on a consistent state `t` of the analysis keeps it consistent: it writes the
products of the cache whole, for the half-size `rb = 0.5 (b_hi - b_lo)` of a cell, never `-0.0`,
and the counts and the ends of the ranges of the bands within their arrays; and it changes only
the counter of the cells, the cache and the bands. -/
@[spec]
theorem tubeCell_spec (th th2 : Double) (t : TubeState) (bLo bHi iLo iHi : ℤ) :
    ⦃ t.WF ⦄
    tubeCell th th2 t bLo bHi iLo iHi
    ⦃ fun r ↦ r.WF ∧
        r = { t with tubeNcells := r.tubeNcells, cache := r.cache, bands := r.bands } ⦄ :=
  Std.WP.Id.triple_of_run fun ht ↦
    ⟨(ht.run_tubeCell th th2 bLo bHi iLo iHi).1,
      (ht.run_tubeCell th th2 bLo bHi iLo iHi).2.eq_with⟩

end JPoints

end
