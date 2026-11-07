/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.DoubleError
public import JPoints.Proof.Tube
public import JPoints.Proof.TubeRun

import JPoints.Proof.Constants
import JPoints.Proof.Containers

/-!
# The rounding errors of the analysis of a cell of the tube

The doubles of `tube_cell` (`JPoints.tubeCellAnalyze`) as approximations of exact values with
majorants (`JPoints.Double.Approx`), so that the error of each is bounded by its count of
roundings times its majorant. `shift2` of approximations of the coefficients of a polynomial by an
exact centre `(x, y)` on the grid `2 ^ (-1) ℤ` approximates the Taylor coefficients of the exact
polynomial at `(X, Y)`, with those of the majorants at `(|X|, |Y|)` as majorants, within `4 deg`
roundings more (`JPoints.Double.ApproxCoeffs.shift2Gen`); the combinations `Q(W)` and `Q(-W)`
approximate the combinations of the exact coefficients
(`JPoints.Double.ApproxCoeffs.tubeCellCombine`); the products of the half-sizes of a cell
approximate their powers (`JPoints.Double.approx_getElem!_cellProducts`); and `tube_sum` and
`tube_eval`, when finite, approximate the sums of the exact terms
(`JPoints.Double.approx_tubeSumGen`, `JPoints.Double.approx_tubeEvalGen`).

## Main definitions

* `JPoints.addMulCounts`: the counts of roundings after a step of a Taylor shift.
* `JPoints.Double.ApproxOn`, `JPoints.Double.ApproxCoeffs`: approximations of the entries of an
  array.
* `JPoints.combineCoeffs`: the coefficients of `x₀ + w x₁ + w₂ x₂`.

## Main statements

* `JPoints.foldl_addMulCounts_shift1Pairs_le`, `JPoints.foldl_addMulCounts_shift2_le`: the counts
  of `shift1` and `shift2`.
* `JPoints.Double.ApproxOn.foldl_addMulAt`, `JPoints.Double.ApproxCoeffs.shift2Gen`: the shifts.
* `JPoints.Double.approx_getElem!_cellProducts`, `JPoints.Double.approx_tubeSumGen`,
  `JPoints.Double.approx_tubeEvalGen`, `JPoints.Double.ApproxCoeffs.tubeCellCombine`: the products,
  the sums and the combinations.

## Implementation notes

The count of a double is the number of roundings on the longest path to it, as
`JPoints.Double.Approx.add` and `JPoints.Double.Approx.mul` compose them. A step
`p[i] := p[i] + x p[i']` of a Taylor shift gives the entry `i` the larger of its count and that of
the product, plus one (`JPoints.addMulCounts`). Along the rounds of `shift1` on a line of degree
`D` the count of the entry `j` grows by `2 (D - j)` in the first round and by one in each later
one, so that the shift adds at most `2 D` to the counts of its line
(`JPoints.foldl_addMulCounts_shift1Pairs_le`); the columns and the rows of `shift2` are disjoint
lines, so that each pass adds at most `2 deg` (`JPoints.foldl_addMulCounts_shift2_le`), where a
uniform count would add two for each of the `deg (deg + 1) (deg + 2) / 3` steps. The grid of an
entry grows with its count, by one for each product with a point on the grid `2 ^ (-1) ℤ`
(`JPoints.Double.ApproxOn`). The shifted coefficients and the combinations are finite by a bound
on their majorants, which only grow along the steps; the sums of `tube_sum` and `tube_eval` are
assumed finite, as the tests of `tube_cell` and `tube_ok` give it, and so are their terms.
-/

@[expose] public section

namespace JPoints

/-! ### The counts of roundings of a Taylor shift -/

/-- The counts of roundings of the entries of an array after a step `p[i] := p[i] + x p[i']` of a
Taylor shift by an exact `x` (`JPoints.addMulAt`), from the counts `c` before: the entry `i` takes
the larger of its count and that of the product, `c i' + 1`, plus one for the sum, as
`JPoints.Double.Approx.add` and `JPoints.Double.Approx.mul` count them. -/
def addMulCounts (c : ℕ → ℕ) (ii : ℕ × ℕ) : ℕ → ℕ :=
  Function.update c ii.1 (max (c ii.1) (c ii.2 + 1) + 1)

section Counts

variable {c : ℕ → ℕ} {ii : ℕ × ℕ} {l : ℕ}

private theorem addMulCounts_self (c : ℕ → ℕ) (ii : ℕ × ℕ) :
    addMulCounts c ii ii.1 = max (c ii.1) (c ii.2 + 1) + 1 :=
  Function.update_self ..

private theorem addMulCounts_of_ne (h : ii.1 ≠ l) : addMulCounts c ii l = c l :=
  Function.update_of_ne (Ne.symm h) ..

private theorem le_addMulCounts (c : ℕ → ℕ) (ii : ℕ × ℕ) (l : ℕ) : c l ≤ addMulCounts c ii l := by
  by_cases h : ii.1 = l
  · subst h; rw [addMulCounts_self]; lia
  · rw [addMulCounts_of_ne h]

private theorem le_foldl_addMulCounts (L : List (ℕ × ℕ)) (c : ℕ → ℕ) (l : ℕ) :
    c l ≤ L.foldl addMulCounts c l := by
  induction L generalizing c with
  | nil => exact le_rfl
  | cons ii L ih => exact (le_addMulCounts c ii l).trans (ih _)

private theorem foldl_addMulCounts_of_forall_ne {L : List (ℕ × ℕ)} (h : ∀ ii ∈ L, ii.1 ≠ l)
    (c : ℕ → ℕ) : L.foldl addMulCounts c l = c l := by
  induction L generalizing c with
  | nil => rfl
  | cons ii L ih =>
    rw [List.foldl_cons, ih (fun jj hj ↦ h jj (List.mem_cons_of_mem _ hj)),
      addMulCounts_of_ne (h ii List.mem_cons_self)]

variable {base s : ℕ}

-- The first round of `shift1` leaves the counts of the entries from the `E`-th on as they are.
private theorem foldl_addMulCounts_round_of_le (hs : 0 < s) {E i : ℕ} (hi : E ≤ i) (c : ℕ → ℕ) :
    ((roundIndices E).map fun j ↦ (base + j * s, base + (j + 1) * s)).foldl addMulCounts c
      (base + i * s) = c (base + i * s) := by
  refine foldl_addMulCounts_of_forall_ne (fun jj hjj ↦ ?_) c
  simp only [List.mem_map] at hjj
  obtain ⟨j, hj, rfl⟩ := hjj
  lia [Nat.mul_lt_mul_of_pos_right ((lt_of_mem_roundIndices hj).trans_le hi) hs]

/-- A round of a shift by `x`, the synthetic division by `X - x` of the line `base + j s`,
`j ≤ E`: from counts below `m + 2 (E - j)` at `j < E` and at most `m` at `E`, at most
`m + 2 (E - j)`. -/
private theorem foldl_addMulCounts_round_le (hs : 0 < s) {E m : ℕ} {c : ℕ → ℕ}
    (hc : ∀ j < E, c (base + j * s) + 1 ≤ m + 2 * (E - j)) (hE : c (base + E * s) ≤ m) {j : ℕ}
    (hj : j < E) :
    ((roundIndices E).map fun j ↦ (base + j * s, base + (j + 1) * s)).foldl addMulCounts c
      (base + j * s) ≤ m + 2 * (E - j) := by
  induction E generalizing m c j with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ E ih =>
    rw [roundIndices_succ, List.map_cons, List.foldl_cons]
    have h1 := addMulCounts_self c (base + E * s, base + (E + 1) * s)
    have h2 (j : ℕ) (hj : j < E) := addMulCounts_of_ne (c := c)
      (ii := (base + E * s, base + (E + 1) * s)) (l := base + j * s)
      (by dsimp only; lia [Nat.mul_lt_mul_of_pos_right hj hs])
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · refine (ih (m := m + 2) (fun j' hj' ↦ ?_) (by lia [hc E (by lia)]) hj).trans (by lia)
      lia [h2 j' hj', hc j' (by lia)]
    · rw [foldl_addMulCounts_round_of_le hs le_rfl]
      lia [hc j (by lia)]

-- The shift of the line from `base + s` on leaves the count of the entry at `base` as it is.
private theorem foldl_addMulCounts_shift1Pairs_add (hs : 0 < s) (D : ℕ) (c : ℕ → ℕ) :
    (shift1Pairs (base + s) D s).foldl addMulCounts c base = c base := by
  refine foldl_addMulCounts_of_forall_ne (fun jj hjj ↦ ?_) c
  simp only [shift1Pairs, List.mem_map] at hjj
  obtain ⟨j, -, rfl⟩ := hjj
  dsimp only
  lia

/-- A shift `shift1` by `x` of the line `base + j s`, `j ≤ D`: from counts below `n + 2 (D - j)` at
`j < D` and at most `n` at `D`, at most `n + 2 D`, two roundings for each power of `x`. -/
theorem foldl_addMulCounts_shift1Pairs_le (hs : 0 < s) {D n : ℕ} {c : ℕ → ℕ}
    (hc : ∀ j < D, c (base + j * s) + 1 ≤ n + 2 * (D - j)) (hD : c (base + D * s) ≤ n) {j : ℕ}
    (hj : j ≤ D) : (shift1Pairs base D s).foldl addMulCounts c (base + j * s) ≤ n + 2 * D := by
  induction D generalizing base n c j with
  | zero =>
    obtain rfl : j = 0 := by lia
    simpa [shift1Pairs, shiftIndices] using hD
  | succ D ih =>
    have e (j : ℕ) : base + s + j * s = base + (j + 1) * s := by ring
    have hR {j : ℕ} (hj : j < D + 1) := foldl_addMulCounts_round_le hs hc hD hj
    rw [shift1Pairs_succ, List.foldl_append]
    rcases j with _ | j
    · rw [Nat.zero_mul, add_zero, foldl_addMulCounts_shift1Pairs_add hs]
      lia [hR (j := 0) (by lia)]
    · rw [← e]
      refine (ih (base := base + s) (n := n + 1) (fun j' hj' ↦ ?_) ?_ (by lia)).trans (by lia)
      · rw [e]; lia [hR (j := j' + 1) (by lia)]
      · rw [e, foldl_addMulCounts_round_of_le hs le_rfl]; lia

-- One more line of the shifts of disjoint lines: the counts stay below `N + 2 Dm`, and those of
-- the lines after it at most `N`.
private theorem foldl_addMulCounts_flatMap_succ {σ : ℕ} (hσ : 0 < σ) {b D : ℕ → ℕ}
    {M Dm N m : ℕ} (hm : m < M)
    (hdisj : ∀ i < M, ∀ i' < M, ∀ j ≤ D i, ∀ j' ≤ D i', b i + j * σ = b i' + j' * σ → i = i')
    (hD : D m ≤ Dm) {c : ℕ → ℕ} (h1 : ∀ l, c l ≤ N + 2 * Dm)
    (h2 : ∀ i, m ≤ i → i < M → ∀ j ≤ D i, c (b i + j * σ) ≤ N) :
    (∀ l, (shift1Pairs (b m) (D m) σ).foldl addMulCounts c l ≤ N + 2 * Dm) ∧
      ∀ i, m + 1 ≤ i → i < M → ∀ j ≤ D i,
        (shift1Pairs (b m) (D m) σ).foldl addMulCounts c (b i + j * σ) ≤ N := by
  have hmem {jj : ℕ × ℕ} (h : jj ∈ shift1Pairs (b m) (D m) σ) : ∃ j < D m, jj.1 = b m + j * σ := by
    simp only [shift1Pairs, List.mem_map] at h
    obtain ⟨j, hj, rfl⟩ := h
    exact ⟨j, lt_of_mem_shiftIndices hj, rfl⟩
  refine ⟨fun l ↦ ?_, fun i hi hiM j hj ↦ ?_⟩
  · by_cases hl : ∃ j ≤ D m, l = b m + j * σ
    · obtain ⟨j, hj, rfl⟩ := hl
      exact (foldl_addMulCounts_shift1Pairs_le hσ (n := N) (fun j' hj' ↦ by
        lia [h2 m le_rfl hm j' (by lia)]) (h2 m le_rfl hm _ le_rfl) hj).trans (by lia)
    · rw [foldl_addMulCounts_of_forall_ne (fun jj hjj ↦ ?_)]
      · exact h1 l
      obtain ⟨j', hj', e⟩ := hmem hjj
      exact fun h ↦ hl ⟨j', hj'.le, h ▸ e⟩
  · rw [foldl_addMulCounts_of_forall_ne (fun jj hjj ↦ ?_)]
    · exact h2 i (by lia) hiM j hj
    obtain ⟨j', hj', e⟩ := hmem hjj
    exact fun h ↦ absurd (hdisj m hm i hiM j' hj'.le j hj (e ▸ h)) (by lia)

/-- The shifts by `x` of the disjoint lines `b i + j σ`, `j ≤ D i ≤ Dm`, `i < M`, one after the
other, from counts at most `N`: at most `N + 2 Dm`. -/
private theorem foldl_addMulCounts_flatMap_le {σ : ℕ} (hσ : 0 < σ) {b D : ℕ → ℕ} {M Dm N : ℕ}
    (hdisj : ∀ i < M, ∀ i' < M, ∀ j ≤ D i, ∀ j' ≤ D i', b i + j * σ = b i' + j' * σ → i = i')
    (hD : ∀ i < M, D i ≤ Dm) {c : ℕ → ℕ} (hc : ∀ l, c l ≤ N) (l : ℕ) :
    ((List.range M).flatMap fun i ↦ shift1Pairs (b i) (D i) σ).foldl addMulCounts c l ≤
      N + 2 * Dm := by
  rw [List.foldl_flatMap]
  suffices key : ∀ m ≤ M, (∀ l, (List.range m).foldl (fun c i ↦
      (shift1Pairs (b i) (D i) σ).foldl addMulCounts c) c l ≤ N + 2 * Dm) ∧
      ∀ i, m ≤ i → i < M → ∀ j ≤ D i, (List.range m).foldl (fun c i ↦
        (shift1Pairs (b i) (D i) σ).foldl addMulCounts c) c (b i + j * σ) ≤ N from
    (key M le_rfl).1 l
  intro m hm
  induction m with
  | zero => exact ⟨fun l ↦ (hc l).trans (by lia), fun i _ _ j _ ↦ hc _⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (by lia)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact foldl_addMulCounts_flatMap_succ hσ (by lia) hdisj (hD m (by lia)) ih1 ih2

/-- `shift2` of degree `deg < L`, from counts at most `n`: at most `n + 4 deg`, each column and each
row of the shift a `shift1` of degree at most `deg`. -/
theorem foldl_addMulCounts_shift2_le {deg : ℕ} (hdeg : deg < coeffRow) {c : ℕ → ℕ} {n : ℕ}
    (hc : ∀ l, c l ≤ n) (l : ℕ) :
    (shift2RowPairs deg).foldl addMulCounts ((shift2ColPairs deg).foldl addMulCounts c) l ≤
      n + 4 * deg := by
  have hcol := foldl_addMulCounts_flatMap_le (b := fun k ↦ k) (D := fun k ↦ deg - k)
    (M := deg + 1) (Dm := deg) (by lia : 0 < coeffRow)
    (fun _ hk _ hk' _ _ _ _ h ↦ eq_of_add_mul_coeffRow_eq (by lia) (by lia) h) (fun k _ ↦ by lia) hc
  have hrow := foldl_addMulCounts_flatMap_le (b := fun j ↦ coeffRow * j) (D := fun j ↦ deg - j)
    (M := deg + 1) (Dm := deg) one_pos
    (fun _ _ _ _ _ hk _ hk' h ↦ eq_of_coeffRow_mul_add_eq (by lia) (by lia) h) (fun j _ ↦ by lia)
    hcol l
  rw [shift2RowPairs, shift2ColPairs]
  lia

end Counts

/-! ### The approximations of the Taylor shifts -/

namespace Double

/-- The doubles `p[l]` approximate the rationals `v[l]` with the majorants `a[l]` at the indices
`l` with `S l`, each to within its count `c l` of roundings, on the grid `2 ^ (-(g + c l)) ℤ`:
the grid of an entry of a Taylor shift by a point on the grid `2 ^ (-1) ℤ` grows by at most one
with each rounding. -/
def ApproxOn (S : ℕ → Prop) (p : Array Double) (v a : Array ℚ) (c : ℕ → ℕ) (g : ℕ) : Prop :=
  ∀ l, S l → (p[l]!).Approx v[l]! a[l]! (c l) (g + c l)

variable {S : ℕ → Prop} {p : Array Double} {v a : Array ℚ} {c : ℕ → ℕ} {g : ℕ} {x : Double}
  {X : ℚ}

/-- A step `p[i] := p[i] + x p[i']` of a Taylor shift by the exact `x`, on the grid `2 ^ (-1) ℤ`,
keeps the approximations, with the counts of `JPoints.addMulCounts`, the values and the majorants
stepped by `X` and `|X|`, when the new majorant stays below `2 ^ 1022` by the margin of its
count. -/
theorem ApproxOn.addMulAt (h : ApproxOn S p v a c g)
    (hS : ∀ l, S l → l < p.size ∧ l < v.size ∧ l < a.size) (hx : x.Approx X |X| 0 1)
    {i i' : ℕ} (hi : S i) (hi' : S i')
    (hlt : (1 + 1 / 2 ^ 53) ^ max (c i) (c i' + 1) * (a[i]! + |X| * a[i']!) < 2 ^ 1022)
    (hg : g + max (c i) (c i' + 1) + 1 ≤ 1074) :
    ApproxOn S (JPoints.addMulAt x p (i, i')) (JPoints.addMulAt X v (i, i'))
      (JPoints.addMulAt |X| a (i, i')) (addMulCounts c (i, i')) g := by
  intro l hl
  simp only [JPoints.addMulAt]
  by_cases hli : i = l
  · subst hli
    obtain ⟨h1, h2, h3⟩ := hS i hl
    rw [Array.getElem!_set!_self _ _ _ h1, Array.getElem!_set!_self _ _ _ h2,
      Array.getElem!_set!_self _ _ _ h3, addMulCounts_self]
    have hm := hx.mul_of_lt (h i' hi') (by lia) <| lt_of_le_of_lt (mul_le_mul
      (one_add_pow_le_one_add_pow (by lia)) (le_add_of_nonneg_left (h i hi).nonneg)
      (mul_nonneg (abs_nonneg X) (h i' hi').nonneg) (by positivity)) hlt
    exact (((h i hi).mono (k' := g + max (c i) (c i' + 1)) le_rfl le_rfl (by lia)).add_of_lt
      (hm.mono le_rfl (by lia : 0 + c i' + 1 ≤ c i' + 1) (by lia)) (by lia) hlt).mono le_rfl
        le_rfl (by lia)
  · rw [Array.getElem!_set!_ne _ _ _ _ hli, Array.getElem!_set!_ne _ _ _ _ hli,
      Array.getElem!_set!_ne _ _ _ _ hli, addMulCounts_of_ne hli]
    exact h l hl

/-- The steps `L` of a Taylor shift by the exact `x`, on the grid `2 ^ (-1) ℤ`, keep the
approximations at the indices `S` that the steps read and write, with the counts of
`JPoints.addMulCounts`, the values and the majorants stepped by `X` and `|X|`, when every final
majorant stays below `2 ^ 1022` by the margin of its final count, and every final grid within the
normal range: a majorant and a count only grow along the steps. -/
theorem ApproxOn.foldl_addMulAt (hS : ∀ l, S l → l < p.size ∧ l < v.size ∧ l < a.size)
    (hx : x.Approx X |X| 0 1) (ha : ∀ i : ℕ, 0 ≤ a[i]!) {L : List (ℕ × ℕ)}
    (hL : ∀ ii ∈ L, S ii.1 ∧ S ii.2) (h : ApproxOn S p v a c g)
    (hB : ∀ l, S l → (1 + 1 / 2 ^ 53) ^ L.foldl addMulCounts c l *
      (L.foldl (JPoints.addMulAt |X|) a)[l]! < 2 ^ 1022)
    (hg : ∀ l, S l → g + L.foldl addMulCounts c l ≤ 1074) :
    ApproxOn S (L.foldl (JPoints.addMulAt x) p) (L.foldl (JPoints.addMulAt X) v)
      (L.foldl (JPoints.addMulAt |X|) a) (L.foldl addMulCounts c) g := by
  induction L generalizing p v a c with
  | nil => exact h
  | cons ii L ih =>
    obtain ⟨hi, hi'⟩ := hL ii List.mem_cons_self
    have ha' := (le_getElem!_foldl_addMulAt (abs_nonneg X) [ii] ha).1
    have hc := le_foldl_addMulCounts L (addMulCounts c ii) ii.1
    rw [addMulCounts_self] at hc
    have hA := (le_getElem!_foldl_addMulAt (abs_nonneg X) L ha').2 ii.1
    simp only [JPoints.addMulAt, List.foldl_cons, List.foldl_nil,
      Array.getElem!_set!_self _ _ _ (hS ii.1 hi).2.2] at hA
    simp only [List.foldl_cons] at hB hg ⊢
    refine ih (fun l hl ↦ ?_) ha' (fun jj hjj ↦ hL jj (List.mem_cons_of_mem _ hjj))
      (h.addMulAt hS hx hi hi' ?_ (by lia [hg ii.1 hi])) hB hg
    · simpa [JPoints.addMulAt] using hS l hl
    · exact lt_of_le_of_lt (mul_le_mul (one_add_pow_le_one_add_pow (by lia)) hA
        (add_nonneg (ha _) (mul_nonneg (abs_nonneg X) (ha _))) (by positivity)) (hB ii.1 hi)

/-- The doubles `p[P(j, k)]`, `j + k ≤ deg`, of the coefficients of a polynomial in two variables
approximate the rationals `v[P(j, k)]` with the majorants `a[P(j, k)]` to within `n` roundings,
on the grid `2 ^ (-g) ℤ` (`JPoints.Double.Approx`). -/
def ApproxCoeffs (p : Array Double) (v a : Array ℚ) (deg n g : ℕ) : Prop :=
  ∀ ⦃j k : ℕ⦄, j + k ≤ deg →
    (p[coeffIndex j k]!).Approx v[coeffIndex j k]! a[coeffIndex j k]! n g

theorem ApproxCoeffs.mono {deg n g : ℕ} (h : ApproxCoeffs p v a deg n g) {deg' n' g' : ℕ}
    (hdeg : deg' ≤ deg) (hn : n ≤ n') (hg : g ≤ g') : ApproxCoeffs p v a deg' n' g' :=
  fun _ _ hjk ↦ (h (hjk.trans hdeg)).mono le_rfl hn hg

-- The bound on the counts and the majorants of the column steps of `shift2` from those of the
-- whole shift.
private theorem pow_mul_getElem!_foldl_le {deg : ℕ} (ha : ∀ i : ℕ, 0 ≤ a[i]!) {Y : ℚ} {l N : ℕ}
    (hc : (shift2RowPairs deg).foldl addMulCounts ((shift2ColPairs deg).foldl addMulCounts c) l ≤
      N) :
    (1 + 1 / 2 ^ 53 : ℚ) ^ (shift2ColPairs deg).foldl addMulCounts c l *
        ((shift2ColPairs deg).foldl (JPoints.addMulAt |X|) a)[l]! ≤
      (1 + 1 / 2 ^ 53) ^ N * (JPoints.shift2Gen a deg |X| |Y|)[l]! := by
  have h1 := le_getElem!_foldl_addMulAt (abs_nonneg X) (shift2ColPairs deg) ha
  have h2 := (le_getElem!_foldl_addMulAt (abs_nonneg Y) (shift2RowPairs deg) h1.1).2 l
  exact mul_le_mul (one_add_pow_le_one_add_pow ((le_foldl_addMulCounts _ _ l).trans hc)) h2 (h1.1 l)
    (by positivity)

-- `shift2` on the coefficients of degree at most `deg`, with the counts of its steps.
private theorem approxOn_shift2Gen {deg n : ℕ}
    (hp : ApproxOn (fun l ↦ ∃ j k, j + k ≤ deg ∧ coeffIndex j k = l) p v a (fun _ ↦ n) g)
    (hS : ∀ l, (∃ j k, j + k ≤ deg ∧ coeffIndex j k = l) → l < p.size ∧ l < v.size ∧ l < a.size)
    (hdeg : deg < coeffRow) (ha : ∀ i : ℕ, 0 ≤ a[i]!) {y : Double} {Y : ℚ}
    (hx : x.Approx X |X| 0 1) (hy : y.Approx Y |Y| 0 1)
    (hB : ∀ l, (∃ j k, j + k ≤ deg ∧ coeffIndex j k = l) →
      (1 + 1 / 2 ^ 53) ^ (n + 4 * deg) * (JPoints.shift2Gen a deg |X| |Y|)[l]! < 2 ^ 1022)
    (hg : g + n + 4 * deg ≤ 1074) :
    ApproxOn (fun l ↦ ∃ j k, j + k ≤ deg ∧ coeffIndex j k = l) (JPoints.shift2Gen p deg x y)
      (JPoints.shift2Gen v deg X Y) (JPoints.shift2Gen a deg |X| |Y|)
      ((shift2RowPairs deg).foldl addMulCounts ((shift2ColPairs deg).foldl addMulCounts
        fun _ ↦ n)) g := by
  have hcnt := foldl_addMulCounts_shift2_le hdeg (c := fun _ ↦ n) (fun _ ↦ le_rfl)
  have h1 := hp.foldl_addMulAt hS hx ha (L := shift2ColPairs deg) (fun ii hii ↦ by
      obtain ⟨j, k, hjk, rfl⟩ := mem_shift2ColPairs hii
      exact ⟨⟨j, k, by lia, rfl⟩, ⟨j + 1, k, hjk, rfl⟩⟩)
    (fun l hl ↦ (pow_mul_getElem!_foldl_le ha (hcnt l)).trans_lt (hB l hl))
    (fun l hl ↦ by lia [le_foldl_addMulCounts (shift2RowPairs deg)
      ((shift2ColPairs deg).foldl addMulCounts fun _ ↦ n) l, hcnt l])
  exact h1.foldl_addMulAt (fun l hl ↦ by simpa only [size_foldl_addMulAt] using hS l hl) hy
    (le_getElem!_foldl_addMulAt (abs_nonneg X) _ ha).1 (L := shift2RowPairs deg) (fun ii hii ↦ by
      obtain ⟨j, k, hjk, rfl⟩ := mem_shift2RowPairs hii
      exact ⟨⟨j, k, by lia, rfl⟩, ⟨j, k + 1, hjk, rfl⟩⟩)
    (fun l hl ↦ lt_of_le_of_lt (mul_le_mul_of_nonneg_right (one_add_pow_le_one_add_pow (hcnt l))
      (getElem!_shift2Gen_nonneg ha deg (abs_nonneg X) (abs_nonneg Y) l)) (hB l hl))
    (fun l hl ↦ by lia [hcnt l])

/-- `shift2` of degree `deg ≤ D < L` by the exact `x` and `y`, on the grid `2 ^ (-1) ℤ`, keeps the
approximations of the coefficients of degree at most `D`, with `4 deg` roundings more (two for
each power of a coordinate, `JPoints.foldl_addMulCounts_shift2_le`), the values shifted by `X` and
`Y`, the majorants by `|X|` and `|Y|`, when the polynomial of the majorants at
`(|X| + 1, |Y| + 1)`, which bounds every shifted majorant
(`JPoints.getElem!_shift2Gen_le_eval2`), stays below `2 ^ 1022` by the margin of the count. -/
theorem ApproxCoeffs.shift2Gen {D deg n g : ℕ} (hp : ApproxCoeffs p v a D n g) (hdeg : deg ≤ D)
    (hD : D < coeffRow) (hps : numCoeffs ≤ p.size) (hvs : numCoeffs ≤ v.size)
    (has : numCoeffs ≤ a.size) (ha : ∀ i : ℕ, 0 ≤ a[i]!) {y : Double} {Y : ℚ}
    (hx : x.Approx X |X| 0 1) (hy : y.Approx Y |Y| 0 1)
    (hB : (1 + 1 / 2 ^ 53) ^ (n + 4 * deg) * eval2 a deg (|X| + 1) (|Y| + 1) < 2 ^ 1022)
    (hg : g + n + 4 * deg ≤ 1074) :
    ApproxCoeffs (JPoints.shift2Gen p deg x y) (JPoints.shift2Gen v deg X Y)
      (JPoints.shift2Gen a deg |X| |Y|) D (n + 4 * deg) (g + n + 4 * deg) := by
  intro j k hjk
  by_cases h : j + k ≤ deg
  · have hcnt := foldl_addMulCounts_shift2_le (deg := deg) (by lia) (c := fun _ ↦ n)
      (fun _ ↦ le_rfl)
    refine (approxOn_shift2Gen (fun l ⟨j, k, hjk, e⟩ ↦ e ▸ (hp (hjk.trans hdeg)).mono le_rfl
      le_rfl (by lia)) (fun l ⟨j, k, hjk, e⟩ ↦ ?_) (by lia) ha hx hy (fun l ⟨j, k, hjk, e⟩ ↦ ?_)
      hg _ ⟨j, k, h, rfl⟩).mono le_rfl (hcnt _) (by lia [hcnt (coeffIndex j k)])
    · have := coeffIndex_lt_numCoeffs (j := j) (k := k) (by lia) (by lia)
      lia
    · exact e ▸ lt_of_le_of_lt (mul_le_mul_of_nonneg_left (getElem!_shift2Gen_le_eval2 ha (by lia)
        has (abs_nonneg X) (abs_nonneg Y) hjk) (by positivity)) hB
  · rw [getElem!_shift2Gen_of_lt (by lia) (by lia) (by lia), getElem!_shift2Gen_of_lt (by lia)
      (by lia) (by lia), getElem!_shift2Gen_of_lt (by lia) (by lia) (by lia)]
    exact (hp hjk).mono le_rfl (by lia) (by lia)

/-! ### Powers and products of the half-sizes of a cell -/

-- A product of powers of numbers `0 ≤ R, C ≤ 2 ^ 200` of degree at most `4`, with the margin of
-- its count, is far below `2 ^ 1022`.
private theorem one_add_pow_mul_pow_mul_pow_lt {R C : ℚ} (hR0 : 0 ≤ R) (hR : R ≤ 2 ^ 200)
    (hC0 : 0 ≤ C) (hC : C ≤ 2 ^ 200) {i j : ℕ} (h : i + j ≤ 4) :
    (1 + 1 / 2 ^ 53 : ℚ) ^ (0 + i + j) * (1 * R ^ i * C ^ j) < 2 ^ 1022 := by
  have h1 : 1 * R ^ i * C ^ j ≤ (2 ^ 200) ^ 4 :=
    calc 1 * R ^ i * C ^ j ≤ (2 ^ 200) ^ i * (2 ^ 200) ^ j := by
          rw [one_mul]
          exact mul_le_mul (pow_le_pow_left₀ hR0 hR i) (pow_le_pow_left₀ hC0 hC j)
            (by positivity) (by positivity)
      _ = (2 ^ 200) ^ (i + j) := by rw [pow_add]
      _ ≤ (2 ^ 200) ^ 4 := pow_le_pow_right₀ (by norm_num) h
  exact one_add_pow_mul_lt_two_pow_1022 (by lia) (by positivity)
    (h1.trans (by rw [← pow_mul]; exact pow_le_pow_right₀ one_le_two (by norm_num)))

/-- The products `rb ^ j rc ^ k` of the half-sizes of a cell that `tube_cell` keeps
(`JPoints.cellProducts`), for exact half-sizes `R, C ≥ 0` on the grid `2 ^ (-1) ℤ` of at most
`2 ^ 200` and `j + k ≤ 4`, approximate `R ^ j C ^ k` within `j + k` roundings. -/
theorem approx_getElem!_cellProducts {rb rc : Double} {R C : ℚ} (hR : rb.Approx R R 0 1)
    (hC : rc.Approx C C 0 1) (hR' : R ≤ 2 ^ 200) (hC' : C ≤ 2 ^ 200) {j k : ℕ} (hjk : j + k ≤ 4) :
    ((cellProducts rb rc)[coeffIndex j k]!).Approx (R ^ j * C ^ k) (R ^ j * C ^ k) (j + k)
      (j + k) := by
  have h5 := five_le_coeffRow
  have hb {i i' : ℕ} (h : i + i' ≤ 4) :=
    one_add_pow_mul_pow_mul_pow_lt hR.nonneg hR' hC.nonneg hC' h
  rw [cellProducts, getElem!_coeffArray _ (by lia) (by lia)]
  have h1 := (Approx.of_toRat_eq isFinite_one toRat_one (.intCast 1)).iterate_mul hR j
    (fun i hi ↦ by
      have := hb (i := i) (i' := 0) (by lia)
      rwa [pow_zero, mul_one, Nat.add_zero, ← abs_one] at this) (by lia)
  rw [abs_one] at h1
  have h2 := h1.iterate_mul hC k (fun i hi ↦ hb (by lia)) (by lia)
  simpa only [zero_add, mul_one, one_mul] using h2

/-! ### `tube_sum` and `tube_eval` -/

open Finset in
/-- `tube_sum`, when finite, of finite doubles `q[P(j, k)]` on the grid `2 ^ (-gq) ℤ` and
products `rp[P(j, k)]` approximating `R ^ j C ^ k` within `j + k` roundings, approximates the sum
of `|q[P(j, k)]| R ^ j C ^ k` over `(j, k) ≠ (0, 0)`, itself its majorant, within
`deg + (deg + 1) (deg + 2) / 2` roundings: `deg + 1` for a term, one for each sum. -/
theorem approx_tubeSumGen {q rp : Array Double} {deg gq : ℕ} {R C : ℚ}
    (hq : ∀ ⦃j k : ℕ⦄, j + k ≤ deg →
      (q[coeffIndex j k]!).isFinite = true ∧ OnGrid gq (q[coeffIndex j k]!).toRat)
    (hrp : ∀ ⦃j k : ℕ⦄, j + k ≤ deg →
      (rp[coeffIndex j k]!).Approx (R ^ j * C ^ k) (R ^ j * C ^ k) (j + k) (j + k))
    (hg : gq + deg ≤ 1074) (hf : (tubeSumGen q deg rp).isFinite = true) :
    (tubeSumGen q deg rp).Approx
      (∑ j ∈ range (deg + 1), ∑ k ∈ range (deg - j + 1),
        |(q[coeffIndex j k]!).toRat| * (R ^ j * C ^ k) - |(q[coeffIndex 0 0]!).toRat|)
      (∑ j ∈ range (deg + 1), ∑ k ∈ range (deg - j + 1),
        |(q[coeffIndex j k]!).toRat| * (R ^ j * C ^ k) - |(q[coeffIndex 0 0]!).toRat|)
      (deg + (evalIndices deg).length) (gq + deg) := by
  have h := Approx.foldl_add (L := (evalIndices deg).tail)
    (tv := fun jk ↦ |(q[coeffIndex jk.1 jk.2]!).toRat| * (R ^ jk.1 * C ^ jk.2))
    (ta := fun jk ↦ |(q[coeffIndex jk.1 jk.2]!).toRat| * (R ^ jk.1 * C ^ jk.2)) (C := deg + 1)
    (Approx.of_toRat_eq isFinite_zero toRat_zero (.zero (gq + deg))) (fun jk hjk hT ↦ ?_)
    hg hf
  · have e := sum_map_tail_evalIndices deg
      fun jk ↦ |(q[coeffIndex jk.1 jk.2]!).toRat| * (R ^ jk.1 * C ^ jk.2)
    dsimp only at e
    rw [abs_zero, zero_add, e, pow_zero, pow_zero, mul_one, mul_one] at h
    refine h.mono le_rfl ?_ le_rfl
    rw [List.length_tail, Nat.zero_max]
    lia [length_evalIndices_pos deg]
  · have hjk' := mem_evalIndices.mp (List.mem_of_mem_tail hjk)
    obtain ⟨hq1, hq2⟩ := hq hjk'
    have hfa := Approx.of_toRat_eq ((isFinite_fabs _).trans hq1) (toRat_fabs _) hq2.abs
    exact (hfa.mul (hrp hjk') (by lia) hT).mono (by rw [abs_abs]) (by lia) (by lia)

/-- The powers `x ^ j`, `j ≤ 4`, by repeated products from `1.0`, of an exact `x` on the grid
`2 ^ (-1) ℤ` with `|X| ≤ 2 ^ 200`, approximate `X ^ j` within `j` roundings. -/
theorem approx_iterate_mul_one {x : Double} {X : ℚ} (hx : x.Approx X |X| 0 1)
    (hX : |X| ≤ 2 ^ 200) {j : ℕ} (hj : j ≤ 4) :
    ((· * x)^[j] 1.0).Approx (X ^ j) (|X| ^ j) j j := by
  have h := (Approx.of_toRat_eq isFinite_one toRat_one (.intCast 1)).iterate_mul hx j
    (fun i hi ↦ by
      have := one_add_pow_mul_pow_mul_pow_lt (abs_nonneg X) hX le_rfl (by norm_num)
        (i := i) (j := 0) (by lia)
      rwa [pow_zero, mul_one, Nat.add_zero, ← abs_one] at this) (by lia)
  simpa only [abs_one, one_mul, zero_add, mul_one] using h

/-- `tube_eval`, when finite, at exact `x` and `y` on the grid `2 ^ (-1) ℤ` of absolute value at
most `2 ^ 200`, of a polynomial of degree `deg ≤ 4` whose coefficients approximate `v` with the
majorants `a` within `n` roundings, approximates the value of `v` at `(X, Y)` with the value of
`a` at `(|X|, |Y|)` as its majorant, within `n + deg + 2` roundings for a term and one for each
sum. -/
theorem approx_tubeEvalGen {qa : Array Double} {v a : Array ℚ} {deg n g : ℕ}
    (hqa : ApproxCoeffs qa v a deg n g) {x y : Double} {X Y : ℚ} (hx : x.Approx X |X| 0 1)
    (hy : y.Approx Y |Y| 0 1) (hX : |X| ≤ 2 ^ 200) (hY : |Y| ≤ 2 ^ 200) (hdeg : deg ≤ 4)
    (hg : g + deg ≤ 1074) (hf : (tubeEvalGen qa deg x y).isFinite = true) :
    (tubeEvalGen qa deg x y).Approx (eval2 v deg X Y) (eval2 a deg |X| |Y|)
      (n + deg + 2 + (evalIndices deg).length) (g + deg) := by
  have h := Approx.foldl_add (L := evalIndices deg)
    (tv := fun jk ↦ v[coeffIndex jk.1 jk.2]! * X ^ jk.1 * Y ^ jk.2)
    (ta := fun jk ↦ a[coeffIndex jk.1 jk.2]! * |X| ^ jk.1 * |Y| ^ jk.2) (C := n + deg + 2)
    (Approx.of_toRat_eq isFinite_zero toRat_zero (.zero (g + deg))) (fun jk hjk hT ↦ ?_) hg hf
  · rw [sum_map_evalIndices, sum_map_evalIndices, abs_zero, zero_add, zero_add] at h
    exact h.mono le_rfl (by lia) le_rfl
  · have hjk' := mem_evalIndices.mp hjk
    obtain ⟨hT1, -⟩ := isFinite_and_of_isFinite_mul hT
    exact (((hqa hjk').mul (approx_iterate_mul_one hx hX (by lia)) (by lia) hT1).mul
      (approx_iterate_mul_one hy hY (by lia)) (by lia) hT).mono le_rfl (by lia) (by lia)

end Double

/-! ### The combinations `Q(W)` and `Q(-W)` -/

/-- The coefficients of `x₀ + w x₁ + w₂ x₂` for arrays `x₀`, `x₁`, `x₂` of the coefficients of
polynomials in two variables, as `tube_cell` combines the shifted `k₀`, `k₁` and `k₂` into `Q(W)`
and `Q(-W)`. -/
def combineCoeffs (w w2 : ℚ) (x0 x1 x2 : Array ℚ) : Array ℚ :=
  Array.ofFn fun i : Fin numCoeffs ↦ x0[i]! + w * x1[i]! + w2 * x2[i]!

private theorem getElem!_combineCoeffs (w w2 : ℚ) (x0 x1 x2 : Array ℚ) {i : ℕ}
    (hi : i < numCoeffs) :
    (combineCoeffs w w2 x0 x1 x2)[i]! = x0[i]! + w * x1[i]! + w2 * x2[i]! := by
  simp [combineCoeffs, hi]

theorem nonneg_getElem!_combineCoeffs {w w2 : ℚ} (hw : 0 ≤ w) (hw2 : 0 ≤ w2)
    {x0 x1 x2 : Array ℚ} (h0 : ∀ i : ℕ, 0 ≤ x0[i]!) (h1 : ∀ i : ℕ, 0 ≤ x1[i]!)
    (h2 : ∀ i : ℕ, 0 ≤ x2[i]!) (i : ℕ) :
    0 ≤ (combineCoeffs w w2 x0 x1 x2)[i]! := by
  by_cases hi : i < numCoeffs
  · rw [getElem!_combineCoeffs _ _ _ _ _ hi]
    have := h0 i; have := h1 i; have := h2 i
    positivity
  · rw [getElem!_neg _ _ (by simpa [combineCoeffs] using hi)]
    exact le_rfl

open Finset in
theorem eval2_combineCoeffs (w w2 : ℚ) (x0 x1 x2 : Array ℚ) {deg : ℕ} (hdeg : deg < coeffRow)
    (s t : ℚ) :
    eval2 (combineCoeffs w w2 x0 x1 x2) deg s t =
      eval2 x0 deg s t + w * eval2 x1 deg s t + w2 * eval2 x2 deg s t := by
  simp only [eval2, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j hj ↦ sum_congr rfl fun k hk ↦ ?_
  simp only [mem_range] at hj hk
  rw [getElem!_combineCoeffs _ _ _ _ _ (coeffIndex_lt_numCoeffs (by lia) (by lia))]
  ring

namespace Double

private theorem one_add_pow_mul_le {n N : ℕ} {x y : ℚ} (hn : n ≤ N) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1 + 1 / 2 ^ 53 : ℚ) ^ n * x ≤ (1 + 1 / 2 ^ 53) ^ N * y :=
  mul_le_mul (one_add_pow_le_one_add_pow hn) hxy hx (by positivity)

variable {x0 x1 x2 t t2 : Double} {v0 v1 v2 a0 a1 a2 W W2 A A2 : ℚ} {n0 n1 n2 c c2 g : ℕ}

-- An entry of `Q(W)` and of `Q(-W)`: `x₀ ± t x₁ + t₂ x₂`.
private theorem approx_add_mul_add_mul (h0 : x0.Approx v0 a0 n0 g) (h1 : x1.Approx v1 a1 n1 g)
    (h2 : x2.Approx v2 a2 n2 g) (ht : t.Approx W A c 0) (ht2 : t2.Approx W2 A2 c2 0)
    (hg : g ≤ 1074)
    (hB : (1 + 1 / 2 ^ 53) ^ max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) *
      (a0 + A * a1 + A2 * a2) < 2 ^ 1022) :
    (x0 + t * x1 + t2 * x2).Approx (v0 + W * v1 + W2 * v2) (a0 + A * a1 + A2 * a2)
        (max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) + 1) g ∧
      (x0 - t * x1 + t2 * x2).Approx (v0 - W * v1 + W2 * v2) (a0 + A * a1 + A2 * a2)
        (max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) + 1) g := by
  have p0 := h0.nonneg
  have p1 := mul_nonneg ht.nonneg h1.nonneg
  have p2 := mul_nonneg ht2.nonneg h2.nonneg
  have q1 := (ht.mul_of_lt h1 (by lia) ((one_add_pow_mul_le (by lia) p1 (by linarith)).trans_lt
    hB)).mono le_rfl le_rfl (by lia : 0 + g ≤ g)
  have q2 := (ht2.mul_of_lt h2 (by lia) ((one_add_pow_mul_le (by lia) p2 (by linarith)).trans_lt
    hB)).mono le_rfl le_rfl (by lia : 0 + g ≤ g)
  have hB1 : (1 + 1 / 2 ^ 53 : ℚ) ^ max n0 (c + n1 + 1) * (a0 + A * a1) < 2 ^ 1022 :=
    (one_add_pow_mul_le (by lia) (by linarith) (by linarith)).trans_lt hB
  exact ⟨(h0.add_of_lt q1 hg hB1).add_of_lt q2 hg hB, (h0.sub_of_lt q1 hg hB1).add_of_lt q2 hg hB⟩

variable {p0 p1 p2 : Array Double} {v0 v1 v2 a0 a1 a2 : Array ℚ} {deg : ℕ}

/-- The coefficients of `Q(W)` and of `Q(-W)` that `tube_cell` combines from approximations of the
shifted `k₀`, `k₁` and `k₂` on a common grid and approximations `th` of `W` and `th2` of `W₂` on
the grid `ℤ` approximate the combinations `v₀ ± W v₁ + W₂ v₂`
(`JPoints.combineCoeffs`), with the majorants combined by the majorants of `th` and `th2`, when
the combined majorants stay below `2 ^ 1022` by the margin of the count. -/
theorem ApproxCoeffs.tubeCellCombine (h0 : ApproxCoeffs p0 v0 a0 deg n0 g)
    (h1 : ApproxCoeffs p1 v1 a1 deg n1 g) (h2 : ApproxCoeffs p2 v2 a2 deg n2 g)
    (ht : t.Approx W A c 0) (ht2 : t2.Approx W2 A2 c2 0) (hdeg : deg < coeffRow) (hg : g ≤ 1074)
    (hB : ∀ ⦃j k : ℕ⦄, j + k ≤ deg →
      (1 + 1 / 2 ^ 53) ^ max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) *
        (combineCoeffs A A2 a0 a1 a2)[coeffIndex j k]! < 2 ^ 1022) :
    ApproxCoeffs (JPoints.tubeCellCombine t t2 p0 p1 p2).run.1 (combineCoeffs W W2 v0 v1 v2)
        (combineCoeffs A A2 a0 a1 a2) deg (max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) + 1) g ∧
      ApproxCoeffs (JPoints.tubeCellCombine t t2 p0 p1 p2).run.2 (combineCoeffs (-W) W2 v0 v1 v2)
        (combineCoeffs A A2 a0 a1 a2) deg (max (max n0 (c + n1 + 1) + 1) (c2 + n2 + 1) + 1) g := by
  rw [run_tubeCellCombine]
  refine ⟨fun j k hjk ↦ ?_, fun j k hjk ↦ ?_⟩ <;>
  · have hl := coeffIndex_lt_numCoeffs (j := j) (k := k) (by lia) (by lia)
    have hB' := hB hjk
    rw [getElem!_combineCoeffs _ _ _ _ _ hl] at hB'
    rw [List.getElem!_toArray_map_range hl, getElem!_combineCoeffs _ _ _ _ _ hl,
      getElem!_combineCoeffs _ _ _ _ _ hl]
    first
      | exact (approx_add_mul_add_mul (h0 hjk) (h1 hjk) (h2 hjk) ht ht2 hg hB').1
      | (rw [neg_mul, ← sub_eq_add_neg]
         exact (approx_add_mul_add_mul (h0 hjk) (h1 hjk) (h2 hjk) ht ht2 hg hB').2)

end Double

end JPoints

end
