/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TaylorShift
public import Std.WP

import JPoints.Proof.Containers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import JPoints.Proof.Values
import Std.Tactic.Do

/-!
# The values of the loops of the analysis of the tube

The values of the components of `tube_cell` with loops, as folds that the error analysis of the
tube follows step by step: `shift1` and `shift2` are the folds `JPoints.shift1Gen` and
`JPoints.shift2Gen` over doubles (`JPoints.shift1_spec`, `JPoints.shift2_spec`); `tube_eval` and
`tube_sum` are sums over the pairs `(j, k)` with `j + k ≤ deg` in the order of their loops
(`JPoints.evalIndices`), `tube_sum` without the constant term (`JPoints.run_tubeEval`,
`JPoints.run_tubeSum`); the combinations of `Q(W)` and `Q(-W)` are the lists of their
coefficients (`JPoints.run_tubeCellCombine`); `poly_sign` is its comparisons on the sum of
`tube_sum` (`JPoints.run_polySign`); and the analysis of a cell is its verdict on these values
(`JPoints.tubeCellAnalyzeGen`, `JPoints.run_tubeCellAnalyze`).

## Main definitions

* `JPoints.evalIndices`, `JPoints.tubeEvalGen`, `JPoints.tubeSumGen`: the sums of `tube_eval` and
  `tube_sum`.
* `JPoints.tubeCellAnalyzeGen`: the verdict of the analysis of a cell.
* `JPoints.Shift1Invariant`, `JPoints.Shift1RoundInvariant`, `JPoints.TubeSumInvariant`,
  `JPoints.TubeSumRowInvariant`, `JPoints.TubeEvalInvariant`, `JPoints.TubeEvalRowInvariant`,
  `JPoints.TubeCellCombineInvariant`: the invariants of the loops.

## Main statements

* `JPoints.shift1_spec`, `JPoints.shift2_spec`: the Taylor shifts.
* `JPoints.run_tubeSum`, `JPoints.run_tubeEval`: the sums.
* `JPoints.run_tubeCellCombine`, `JPoints.run_polySign`: the combinations and the signs.
* `JPoints.run_tubeCellAnalyze`: the analysis of a cell.

## Implementation notes

The contracts are triples of `Std.WP` proved by `vcgen` with named invariants, each a fold of
the steps done so far; the value lemmas `run_…` follow from them. The verdict of
`tube_cell_analyze` is proved by `vcgen` against a definition of its value
(`JPoints.tubeCellAnalyzeGen`), since the unfolding of its `do` block by the simp lemmas of `Id`
gives a term too deep for the kernel.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### `shift1` and `shift2` -/

/-- The invariant of the outer loop of `JPoints.shift1` over `i`: the array the steps of the rounds
`i' < i` made from `p`. -/
def Shift1Invariant (p : Array Double) (base deg s : ℕ) (x : Double) :
    Std.WP.Invariant ℕ (Array Double) Prop :=
  fun pref _ q ↦ q = (pref.flatMap fun i ↦ (List.range (deg - i)).map fun t ↦
    (base + (deg - 1 - t) * s, base + (deg - 1 - t + 1) * s)).foldl (addMulAt x) p

/-- The invariant of the inner loop of `JPoints.shift1` over `t`, from the array `q` of the outer
loop: the array the steps `t' < t` of the round made from `q`. -/
def Shift1RoundInvariant (q : Array Double) (base deg s : ℕ) (x : Double) :
    Std.WP.Invariant ℕ (Array Double) Prop :=
  fun pref _ q' ↦ q' = (pref.map fun t ↦
    (base + (deg - 1 - t) * s, base + (deg - 1 - t + 1) * s)).foldl (addMulAt x) q

section Shift1

variable {p q q' : Array Double} {base deg s : ℕ} {x : Double} {pref suff pref' suff' : List ℕ}
  {cur cur' : ℕ}

theorem shift1Invariant_nil {l : List ℕ} : Shift1Invariant p base deg s x [] l p := rfl

theorem shift1RoundInvariant_nil {l : List ℕ} : Shift1RoundInvariant q base deg s x [] l q := rfl

theorem shift1Invariant_step (hq : Shift1Invariant p base deg s x pref (cur :: suff) q)
    (h : Shift1RoundInvariant q base deg s x (ForIn.toList [:deg - cur]) [] q') :
    Shift1Invariant p base deg s x (pref ++ [cur]) suff q' := by
  rw [Shift1RoundInvariant, Std.Legacy.Range.toList_eq_range] at h
  rw [Shift1Invariant, List.flatMap_append, List.foldl_append, ← hq, h, List.flatMap_singleton]

theorem shift1RoundInvariant_step
    (h : Shift1RoundInvariant q base deg s x pref' (cur' :: suff') q') :
    Shift1RoundInvariant q base deg s x (pref' ++ [cur']) suff'
      (q'.set! (base + (deg - 1 - cur') * s)
        (q'[base + (deg - 1 - cur') * s]! + x * q'[base + (deg - 1 - cur' + 1) * s]!)) := by
  rw [Shift1RoundInvariant, List.map_append, List.foldl_append, ← h]
  rfl

theorem shift1Invariant_post (h : Shift1Invariant p base deg s x (ForIn.toList [:deg]) [] q) :
    q = shift1Gen p base deg s x := by
  rw [h, Std.Legacy.Range.toList_eq_range, shift1Gen, shift1Pairs, shiftIndices, List.map_flatMap]
  simp only [List.map_map]
  rfl

end Shift1

@[spec]
theorem shift1_spec (p : Array Double) (base deg s : ℕ) (x : Double) :
    ⦃ True ⦄ shift1 p base deg s x ⦃ fun r ↦ r = shift1Gen p base deg s x ⦄ := by
  vcgen [shift1] invariants
  | inv1 => Shift1Invariant p base deg s x
  | inv2 _ _ _ _ q _ => Shift1RoundInvariant q base deg s x
  all_goals first
    | exact shift1Invariant_nil
    | exact shift1RoundInvariant_nil
    | exact shift1Invariant_step ‹_› ‹_›
    | exact shift1RoundInvariant_step ‹_›
    | exact shift1Invariant_post ‹_›

/-- The invariant of the loop of `JPoints.shift2` over the columns `k`: the array of the shifts of
the columns `k' < k` of `q` by `bm`. -/
def Shift2ColsInvariant (q : Array Double) (deg : ℕ) (bm : Double) :
    Std.WP.Invariant ℕ (Array Double) Prop :=
  fun pref _ q' ↦ q' = pref.foldl (fun q k ↦ shift1Gen q k (deg - k) coeffRow bm) q

/-- The invariant of the loop of `JPoints.shift2` over the rows `j`: the array of the shifts of
the rows `j' < j` by `cm`, after the shifts of all the columns of `q` by `bm`. -/
def Shift2RowsInvariant (q : Array Double) (deg : ℕ) (bm cm : Double) :
    Std.WP.Invariant ℕ (Array Double) Prop :=
  fun pref _ q' ↦ q' = pref.foldl (fun q j ↦ shift1Gen q (coeffRow * j) (deg - j) 1 cm)
    (shiftLines q (fun k ↦ k) (fun k ↦ deg - k) coeffRow (deg + 1) bm)

section Shift2

variable {q q' q'' : Array Double} {deg : ℕ} {bm cm : Double} {pref suff : List ℕ} {cur : ℕ}

theorem shift2ColsInvariant_step (h : Shift2ColsInvariant q deg bm pref (cur :: suff) q')
    (h' : q'' = shift1Gen q' cur (deg - cur) coeffRow bm) :
    Shift2ColsInvariant q deg bm (pref ++ [cur]) suff q'' := by
  rw [Shift2ColsInvariant, List.foldl_append, ← h, h']
  rfl

theorem shift2ColsInvariant_post (h : Shift2ColsInvariant q deg bm (ForIn.toList [:deg + 1]) [] q')
    {l : List ℕ} : Shift2RowsInvariant q deg bm cm [] l q' := by
  rw [Shift2ColsInvariant, Std.Legacy.Range.toList_eq_range] at h
  exact h

theorem shift2RowsInvariant_step (h : Shift2RowsInvariant q deg bm cm pref (cur :: suff) q')
    (h' : q'' = shift1Gen q' (coeffRow * cur) (deg - cur) 1 cm) :
    Shift2RowsInvariant q deg bm cm (pref ++ [cur]) suff q'' := by
  rw [Shift2RowsInvariant, List.foldl_append, ← h, h']
  rfl

theorem shift2RowsInvariant_post
    (h : Shift2RowsInvariant q deg bm cm (ForIn.toList [:deg + 1]) [] q') :
    q' = shift2Gen q deg bm cm := by
  rw [Shift2RowsInvariant, Std.Legacy.Range.toList_eq_range] at h
  rw [h, shift2Gen_eq_shiftLines]
  rfl

end Shift2

@[spec]
theorem shift2_spec (q : Array Double) (deg : ℕ) (bm cm : Double) :
    ⦃ True ⦄ shift2 q deg bm cm ⦃ fun r ↦ r = shift2Gen q deg bm cm ⦄ := by
  vcgen [shift2, shift1_spec] invariants
  | inv1 => Shift2ColsInvariant q deg bm
  | inv2 => Shift2RowsInvariant q deg bm cm
  all_goals first
    | rfl
    | exact shift2ColsInvariant_step ‹_› ‹_›
    | exact shift2ColsInvariant_post ‹_›
    | exact shift2RowsInvariant_step ‹_› ‹_›
    | exact shift2RowsInvariant_post ‹_›

/-! ### `tube_sum` and `tube_eval` -/

/-- The pairs `(j, k)` with `j + k ≤ deg` in the order of the loops of `tube_eval` and `tube_sum`:
`j` up from `0`, and for each `j`, `k` up from `0` to `deg - j`. -/
def evalIndices (deg : ℕ) : List (ℕ × ℕ) :=
  (List.range (deg + 1)).flatMap fun j ↦ (List.range (deg - j + 1)).map (j, ·)

/-- `tube_sum` as a fold: `0.0` plus `|q[P(j, k)]| rp[P(j, k)]` over the pairs `(j, k)` of
`JPoints.evalIndices` but the first, `(0, 0)`, in their order. -/
def tubeSumGen (q : Array Double) (deg : ℕ) (rp : Array Double) : Double :=
  (evalIndices deg).tail.foldl (fun sum jk ↦
    sum + q[coeffIndex jk.1 jk.2]!.fabs * rp[coeffIndex jk.1 jk.2]!) 0.0

/-- `tube_eval` as a fold: `0.0` plus `qa[P(j, k)] x ^ j y ^ k` over the pairs `(j, k)` of
`JPoints.evalIndices` in their order, the powers by repeated products from `1.0`. -/
def tubeEvalGen (qa : Array Double) (deg : ℕ) (x y : Double) : Double :=
  (evalIndices deg).foldl (fun sum jk ↦
    sum + qa[coeffIndex jk.1 jk.2]! * (· * x)^[jk.1] 1.0 * (· * y)^[jk.2] 1.0) 0.0

theorem mem_evalIndices {deg : ℕ} {jk : ℕ × ℕ} : jk ∈ evalIndices deg ↔ jk.1 + jk.2 ≤ deg := by
  simp only [evalIndices, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨j, hj, k, hk, rfl⟩; dsimp only; lia
  · intro h; exact ⟨jk.1, by lia, jk.2, by lia, rfl⟩

theorem evalIndices_eq_cons (deg : ℕ) : evalIndices deg = (0, 0) :: (evalIndices deg).tail := by
  rw [evalIndices, List.range_succ_eq_map (n := deg), List.flatMap_cons, Nat.sub_zero,
    List.range_succ_eq_map (n := deg)]
  rfl

-- The sum of a list of the values of `g` on a `List.flatMap`, by the blocks of the `List.flatMap`.
private theorem sum_map_flatMap {M : Type*} [AddCommMonoid M] (l : List ℕ) (F : ℕ → List (ℕ × ℕ))
    (g : ℕ × ℕ → M) : ((l.flatMap F).map g).sum = (l.map fun j ↦ ((F j).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]

-- A sum over `List.range` as a sum over `Finset.range`.
private theorem sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (h : ℕ → M) :
    ((List.range n).map h).sum = ∑ i ∈ Finset.range n, h i := by
  rw [Finset.sum_eq_multiset_sum]; rfl

theorem sum_map_evalIndices {M : Type*} [AddCommMonoid M] (deg : ℕ) (g : ℕ × ℕ → M) :
    ((evalIndices deg).map g).sum =
      ∑ j ∈ Finset.range (deg + 1), ∑ k ∈ Finset.range (deg - j + 1), g (j, k) := by
  rw [evalIndices, sum_map_flatMap, sum_map_range]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [List.map_map, ← sum_map_range]; rfl

theorem sum_map_tail_evalIndices {M : Type*} [AddCommGroup M] (deg : ℕ) (g : ℕ × ℕ → M) :
    ((evalIndices deg).tail.map g).sum =
      ∑ j ∈ Finset.range (deg + 1), ∑ k ∈ Finset.range (deg - j + 1), g (j, k) - g (0, 0) := by
  have := sum_map_evalIndices deg g
  rw [evalIndices_eq_cons, List.map_cons, List.sum_cons] at this
  rw [← this, add_sub_cancel_left]

theorem length_evalIndices_pos (deg : ℕ) : 0 < (evalIndices deg).length := by
  rw [evalIndices_eq_cons, List.length_cons]
  lia

/-- The function of the fold of `JPoints.tubeSumGen`. -/
def tubeSumAdd (q rp : Array Double) (sum : Double) (jk : ℕ × ℕ) : Double :=
  sum + q[coeffIndex jk.1 jk.2]!.fabs * rp[coeffIndex jk.1 jk.2]!

/-- The invariant of the outer loop of `JPoints.tubeSum` over `j`: the sum over the rows
`j' < j`. -/
def TubeSumInvariant (q : Array Double) (deg : ℕ) (rp : Array Double) :
    Std.WP.Invariant ℕ Double Prop :=
  fun pref _ sum ↦ sum = (pref.flatMap fun j ↦ (ForIn.toList
    [(if (j == 0) = true then 1 else 0):deg - j + 1]).map (j, ·)).foldl (tubeSumAdd q rp) 0.0

/-- The invariant of the inner loop of `JPoints.tubeSum` over `k` in the row `j`, from the sum
`s0` of the rows before: the sum with the terms `k' < k` of the row. -/
def TubeSumRowInvariant (q rp : Array Double) (j : ℕ) (s0 : Double) :
    Std.WP.Invariant ℕ Double Prop :=
  fun pref _ sum ↦ sum = (pref.map (j, ·)).foldl (tubeSumAdd q rp) s0

-- The rows of `tube_sum` are those of `tube_eval` without the first pair.
private theorem flatMap_toList_eq_tail (deg : ℕ) :
    ((List.range (deg + 1)).flatMap fun j ↦ (ForIn.toList
      [(if (j == 0) = true then 1 else 0):deg - j + 1]).map (j, ·)) = (evalIndices deg).tail := by
  have h0 : (List.range (deg + 1)).tail = List.range' 1 deg := by
    rw [List.range_eq_range', List.range'_succ, List.tail_cons]
  rw [evalIndices, List.range_succ_eq_map (n := deg), List.flatMap_cons, List.flatMap_cons,
    List.tail_append_of_ne_nil (by simp), List.flatMap_map, List.flatMap_map, ← List.map_tail,
    Nat.sub_zero, h0]
  simp only [Std.Legacy.Range.toList_eq_range', beq_self_eq_true, ↓reduceIte, Nat.add_sub_cancel,
    Nat.succ_ne_zero, beq_iff_eq, Nat.sub_zero, ← List.range_eq_range']

section TubeSum

variable {q rp : Array Double} {deg : ℕ} {pref suff pref' suff' : List ℕ} {cur cur' : ℕ}
  {sum s0 : Double}

theorem tubeSumRowInvariant_step (h : TubeSumRowInvariant q rp cur s0 pref' (cur' :: suff') sum) :
    TubeSumRowInvariant q rp cur s0 (pref' ++ [cur']) suff'
      (sum + q[coeffIndex cur cur']!.fabs * rp[coeffIndex cur cur']!) := by
  rw [TubeSumRowInvariant, List.map_append, List.foldl_append, ← h]
  rfl

theorem tubeSumInvariant_step (hs : TubeSumInvariant q deg rp pref (cur :: suff) s0)
    (h : TubeSumRowInvariant q rp cur s0
      (ForIn.toList [(if (cur == 0) = true then 1 else 0):deg - cur + 1]) [] sum) :
    TubeSumInvariant q deg rp (pref ++ [cur]) suff sum := by
  rw [TubeSumInvariant, List.flatMap_append, List.foldl_append, ← hs, h, List.flatMap_singleton]

theorem tubeSumInvariant_post (h : TubeSumInvariant q deg rp (ForIn.toList [:deg + 1]) [] sum) :
    sum = tubeSumGen q deg rp := by
  rw [h, Std.Legacy.Range.toList_eq_range, flatMap_toList_eq_tail]
  rfl

end TubeSum

@[spec]
theorem tubeSum_spec (q : Array Double) (deg : ℕ) (rp : Array Double) :
    ⦃ True ⦄ tubeSum q deg rp ⦃ fun r ↦ r = tubeSumGen q deg rp ⦄ := by
  vcgen [tubeSum] invariants
  | inv1 => TubeSumInvariant q deg rp
  | inv2 _ cur _ _ s0 _ => TubeSumRowInvariant q rp cur s0
  all_goals first
    | rfl
    | exact tubeSumRowInvariant_step ‹_›
    | exact tubeSumInvariant_step ‹_› ‹_›
    | exact tubeSumInvariant_post ‹_›

theorem run_tubeSum (q : Array Double) (deg : ℕ) (rp : Array Double) :
    (tubeSum q deg rp).run = tubeSumGen q deg rp :=
  (tubeSum_spec q deg rp).le_wp trivial


/-- The function of the fold of `JPoints.tubeEvalGen`. -/
def tubeEvalAdd (qa : Array Double) (x y : Double) (sum : Double) (jk : ℕ × ℕ) : Double :=
  sum + qa[coeffIndex jk.1 jk.2]! * (· * x)^[jk.1] 1.0 * (· * y)^[jk.2] 1.0

/-- The invariant of the outer loop of `JPoints.tubeEval` over `j`, whose state is the sum and the
power `xj` of `x`: the sum over the rows `j' < j`, and `xj = x ^ j` by repeated products. -/
def TubeEvalInvariant (qa : Array Double) (deg : ℕ) (x y : Double) :
    Std.WP.Invariant ℕ (Double × Double) Prop :=
  fun pref _ st ↦ st.1 = (pref.flatMap fun j ↦ (List.range (deg - j + 1)).map (j, ·)).foldl
    (tubeEvalAdd qa x y) 0.0 ∧ st.2 = (· * x)^[pref.length] 1.0

/-- The invariant of the inner loop of `JPoints.tubeEval` over `k` in the row `j`, from the sum
`s0` of the rows before, whose state is the sum and the power `yk` of `y`: the sum with the terms
`k' < k` of the row, and `yk = y ^ k` by repeated products. -/
def TubeEvalRowInvariant (qa : Array Double) (x y : Double) (j : ℕ) (s0 : Double) :
    Std.WP.Invariant ℕ (Double × Double) Prop :=
  fun pref _ st ↦ st.1 = (pref.map (j, ·)).foldl (tubeEvalAdd qa x y) s0 ∧
    st.2 = (· * y)^[pref.length] 1.0

section TubeEval

variable {qa : Array Double} {deg : ℕ} {x y : Double} {pref suff pref' suff' : List ℕ}
  {cur cur' : ℕ} {sum s0 xj yk : Double}

theorem tubeEvalRowInvariant_step (hc : ForIn.toList [:deg + 1] = pref ++ cur :: suff)
    (hx : TubeEvalInvariant qa deg x y pref (cur :: suff) (s0, xj))
    (hc' : ForIn.toList [:deg - cur + 1] = pref' ++ cur' :: suff')
    (h : TubeEvalRowInvariant qa x y cur s0 pref' (cur' :: suff') (sum, yk)) :
    TubeEvalRowInvariant qa x y cur s0 (pref' ++ [cur']) suff'
      (sum + qa[coeffIndex cur cur']! * xj * yk, yk * y) := by
  have e1 := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have e2 := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, hx2⟩ := hx
  dsimp only at h1 h2 hx2 ⊢
  refine ⟨?_, ?_⟩
  · rw [List.map_append, List.foldl_append, ← h1, hx2, h2, e1, e2]
    rfl
  · rw [h2, List.length_append, List.length_singleton, Function.iterate_succ_apply']

theorem tubeEvalInvariant_step (hx : TubeEvalInvariant qa deg x y pref (cur :: suff) (s0, xj))
    (h : TubeEvalRowInvariant qa x y cur s0 (ForIn.toList [:deg - cur + 1]) [] (sum, yk)) :
    TubeEvalInvariant qa deg x y (pref ++ [cur]) suff (sum, xj * x) := by
  obtain ⟨h1, -⟩ := h
  obtain ⟨hx1, hx2⟩ := hx
  dsimp only at h1 hx1 hx2 ⊢
  refine ⟨?_, ?_⟩
  · rw [List.flatMap_append, List.foldl_append, ← hx1, h1, Std.Legacy.Range.toList_eq_range,
      List.flatMap_singleton]
  · rw [hx2, List.length_append, List.length_singleton, Function.iterate_succ_apply']

theorem tubeEvalInvariant_post
    (h : TubeEvalInvariant qa deg x y (ForIn.toList [:deg + 1]) [] (sum, xj)) :
    sum = tubeEvalGen qa deg x y := by
  obtain ⟨h1, -⟩ := h
  dsimp only at h1
  rw [h1, Std.Legacy.Range.toList_eq_range]
  rfl

end TubeEval

@[spec]
theorem tubeEval_spec (qa : Array Double) (deg : ℕ) (x y : Double) :
    ⦃ True ⦄ tubeEval qa deg x y ⦃ fun r ↦ r = tubeEvalGen qa deg x y ⦄ := by
  vcgen [tubeEval] invariants
  | inv1 => TubeEvalInvariant qa deg x y
  | inv2 _ cur _ _ s0 _ _ => TubeEvalRowInvariant qa x y cur s0
  all_goals first
    -- not `rfl` for the powers from `1.0`, as in `JPoints.productsInvariant_nil`
    | exact ⟨rfl, (Function.iterate_zero_apply ..).symm⟩
    | exact tubeEvalRowInvariant_step ‹_› ‹_› ‹_› ‹_›
    | exact tubeEvalInvariant_step ‹_› ‹_›
    | exact tubeEvalInvariant_post ‹_›

theorem run_tubeEval (qa : Array Double) (deg : ℕ) (x y : Double) :
    (tubeEval qa deg x y).run = tubeEvalGen qa deg x y :=
  (tubeEval_spec qa deg x y).le_wp trivial


/-! ### The combinations `Q(±W)` and the signs -/

/-- The invariant of the loop of `JPoints.tubeCellCombine` over `j`, whose state is the arrays `q`
and `m`: the combinations `p0[j'] ± th p1[j'] + th2 p2[j']` for the `j' < j`, in order. -/
def TubeCellCombineInvariant (th th2 : Double) (p0 p1 p2 : Array Double) :
    Std.WP.Invariant ℕ (Array Double × Array Double) Prop :=
  fun pref _ st ↦ st.1 = (pref.map fun j ↦ p0[j]! + th * p1[j]! + th2 * p2[j]!).toArray ∧
    st.2 = (pref.map fun j ↦ p0[j]! - th * p1[j]! + th2 * p2[j]!).toArray

section Combine

variable {th th2 : Double} {p0 p1 p2 q m : Array Double} {pref suff : List ℕ} {cur : ℕ}

theorem tubeCellCombineInvariant_step
    (h : TubeCellCombineInvariant th th2 p0 p1 p2 pref (cur :: suff) (q, m)) :
    TubeCellCombineInvariant th th2 p0 p1 p2 (pref ++ [cur]) suff
      (q.push (p0[cur]! + th * p1[cur]! + th2 * p2[cur]!),
        m.push (p0[cur]! - th * p1[cur]! + th2 * p2[cur]!)) := by
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  exact ⟨by simp [h1], by simp [h2]⟩

theorem tubeCellCombineInvariant_post
    (h : TubeCellCombineInvariant th th2 p0 p1 p2 (ForIn.toList [:numCoeffs]) [] (q, m)) :
    (q, m) = (((List.range numCoeffs).map fun j ↦ p0[j]! + th * p1[j]! + th2 * p2[j]!).toArray,
      ((List.range numCoeffs).map fun j ↦ p0[j]! - th * p1[j]! + th2 * p2[j]!).toArray) := by
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  rw [h1, h2, Std.Legacy.Range.toList_eq_range]

end Combine

@[spec]
theorem tubeCellCombine_spec (th th2 : Double) (p0 p1 p2 : Array Double) :
    ⦃ True ⦄ tubeCellCombine th th2 p0 p1 p2
    ⦃ fun r ↦ r = (((List.range numCoeffs).map fun j ↦ p0[j]! + th * p1[j]! + th2 * p2[j]!).toArray,
        ((List.range numCoeffs).map fun j ↦ p0[j]! - th * p1[j]! + th2 * p2[j]!).toArray) ⦄ := by
  vcgen [tubeCellCombine] invariants
  · TubeCellCombineInvariant th th2 p0 p1 p2
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact tubeCellCombineInvariant_post ‹_›
    | exact tubeCellCombineInvariant_step ‹_›

theorem run_tubeCellCombine (th th2 : Double) (p0 p1 p2 : Array Double) :
    (tubeCellCombine th th2 p0 p1 p2).run =
      (((List.range numCoeffs).map fun j ↦ p0[j]! + th * p1[j]! + th2 * p2[j]!).toArray,
        ((List.range numCoeffs).map fun j ↦ p0[j]! - th * p1[j]! + th2 * p2[j]!).toArray) :=
  (tubeCellCombine_spec th th2 p0 p1 p2).le_wp trivial

theorem run_polySign (q : Array Double) (deg : ℕ) (rp : Array Double) (err : Double) :
    (polySign q deg rp err).run =
      (if (0.0 : Double) < q[0]!.fabs - (tubeSumGen q deg rp + err) then
        (if (0.0 : Double) < q[0]! then 1 else -1) else 0,
        q[0]!.fabs - (tubeSumGen q deg rp + err), q[0]!.fabs + (tubeSumGen q deg rp + err)) := by
  simp only [polySign, Id.run_bind, run_tubeSum]
  split_ifs <;> rfl


/-- The verdict of `JPoints.tubeCellAnalyze` from the values of its parts: whether `Q(W)` and
`Q(-W)` have different signs throughout the cell, and whether the cell is out. -/
def tubeCellAnalyzeGen (th th2 : Double) (t : TubeState) (rp : Array Double)
    (bm rb cm rc : Double) : Bool × Bool :=
  let p0 := shift2Gen t.k0 4 bm cm
  let p1 := shift2Gen t.k1 3 bm cm
  let p2 := shift2Gen t.k2 2 bm cm
  let err := tubeEps * tubeEvalGen t.ka 4 (bm.fabs + rb) (cm.fabs + rc)
  let r2 := (polySign p2 2 rp (err / th2)).run
  let qm := (tubeCellCombine th th2 p0 p1 p2).run
  let sp := (polySign qm.1 4 rp err).run.1
  let sm := (polySign qm.2 4 rp err).run.1
  (sp != 0 && sm != 0 && sp != sm, sp != 0 && sm != 0 && sp == sm &&
    (r2.1 != 0 && r2.1 != sp || decide (2.0 * th * r2.2.2 < (polySign p1 3 rp (err / th)).run.2.1)))

@[spec]
theorem tubeCellAnalyze_spec (th th2 : Double) (t : TubeState) (rp : Array Double)
    (bm rb cm rc : Double) :
    ⦃ True ⦄ tubeCellAnalyze th th2 t rp bm rb cm rc
    ⦃ fun r ↦ r = tubeCellAnalyzeGen th th2 t rp bm rb cm rc ⦄ := by
  vcgen [tubeCellAnalyze, shift2_spec, tubeEval_spec, Std.WP.Id.triple_eq_run (polySign _ _ _ _),
    Std.WP.Id.triple_eq_run (tubeCellCombine _ _ _ _ _)]
  all_goals
    simp only [Prod.ext_iff] at *
    casesm* _ ∧ _
    subst_vars
    simp_all [tubeCellAnalyzeGen]

theorem run_tubeCellAnalyze (th th2 : Double) (t : TubeState) (rp : Array Double)
    (bm rb cm rc : Double) :
    (tubeCellAnalyze th th2 t rp bm rb cm rc).run = tubeCellAnalyzeGen th th2 t rp bm rb cm rc :=
  (tubeCellAnalyze_spec th th2 t rp bm rb cm rc).le_wp trivial

end JPoints

end
