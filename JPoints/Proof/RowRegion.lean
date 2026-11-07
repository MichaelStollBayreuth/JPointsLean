/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Scan
public import JPoints.Proof.TubeBands

import JPoints.Proof.Containers
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The words that the real region of a row keeps

What `row_region` (`JPoints.rowRegion`) leaves of a row: every word of the row lies in one of its
ranges, or in the words wholly inside an excluded interval of the third coordinate, raised and
lowered by its margins, that one of the intervals on which `f` is negative gives
(`JPoints.rowRegion_cover`). The steps of `row_region` each keep what this needs: the excluded
intervals come from the intervals of `neg`, by the two branches of the roots for `a > 0`
(`JPoints.rowRegionPositive_spec`, `JPoints.RegionPositive`) and by `c / b` for `a = 0`
(`JPoints.rowRegionZero_spec`, `JPoints.RegionZero`); the margins move each end
(`JPoints.rowRegionMargins_spec`); the insertion sort moves the pairs of ends only among
themselves (`JPoints.rowRegionSort_spec`); and the placing of the ranges covers the words between
the words taken out (`JPoints.rowRegionWords_cover`), in increasing order within the words of the
row (`JPoints.rowRegion_spec`). Which third coordinates an excluded interval may take out without
losing a point is the subject of `JPoints.Proof.RowRegionEnds`.

## Main definitions

* `JPoints.rowRegionVertex`, `JPoints.rowRegionValue`, `JPoints.rowRegionFrom`,
  `JPoints.rowRegionUpTo`, `JPoints.rowRegionMargin`, `JPoints.rowRegionMarginLo`,
  `JPoints.rowRegionMarginHi`: the doubles of `row_region`.
* `JPoints.RegionPositive`, `JPoints.RegionZero`, `JPoints.RegionInterval`: the excluded
  intervals.
* `JPoints.RegionExcludes`, `JPoints.RegionCovers`: the words taken out and the words kept.
* `JPoints.RegionIntervalsInvariant`, `JPoints.RegionMarginsInvariant`,
  `JPoints.RegionSortInvariant`, `JPoints.RegionSortInnerInvariant`,
  `JPoints.RegionCoverInvariant`, `JPoints.RowRegionWordsInvariant`, with
  `JPoints.RegionMarginsPart` and `JPoints.RegionSortedAmong`: the invariants of the loops.

## Main statements

* `JPoints.rowRegionPositive_spec`, `JPoints.rowRegionZero_spec`, `JPoints.rowRegionMargins_spec`,
  `JPoints.rowRegionSort_spec`, `JPoints.rowRegionWords_cover`: the steps.
* `JPoints.rowRegion_cover`, `JPoints.exists_mem_rangeList_rowRegion_or_regionExcludes`: the words
  that `row_region` keeps.
* `JPoints.rowRegionWords_spec`, `JPoints.rowRegion_spec`: the ranges of the real region of a row in
  increasing order.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, dispatched by lemmas stated in the shapes of the verification conditions. The doubles
of `row_region` are abbreviations, reducibly equal to the terms of the model, so that the lemmas
about them apply to the verification conditions as they are.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-- The vertex `m = 0.5 * B / A` of `C(t) = B t - A t²` that `row_region` computes for the row
`(a, b)`, `A = (double)a` and `B = (double)b`. -/
abbrev rowRegionVertex (a b : ℤ) : Double := 0.5 * Double.ofInt b / Double.ofInt a

/-- The value `B x - A x x` of `C(t) = B t - A t²` at `x` that `row_region` computes for the row
`(a, b)` in doubles, `A = (double)a` and `B = (double)b`: an end of an excluded interval of the
third coordinate. -/
abbrev rowRegionValue (a b : ℤ) (x : Double) : Double :=
  Double.ofInt b * x - Double.ofInt a * x * x

/-- The start `l = max(nl, m)` of the part of the interval `i` of `neg` on the branch of the
larger root, as `row_region` computes it for the row `(a, b)`. -/
abbrev rowRegionFrom (neg : NegativeIntervals) (a b : ℤ) (i : ℕ) : Double :=
  if rowRegionVertex a b < neg.shrunkLo[i]! then neg.shrunkLo[i]! else rowRegionVertex a b

/-- The end `h = min(nh, m)` of the part of the interval `i` of `neg` on the branch of the smaller
root, as `row_region` computes it for the row `(a, b)`. -/
abbrev rowRegionUpTo (neg : NegativeIntervals) (a b : ℤ) (i : ℕ) : Double :=
  if neg.shrunkHi[i]! < rowRegionVertex a b then neg.shrunkHi[i]! else rowRegionVertex a b

/-- `(lo, hi)` is an excluded interval of the third coordinate that `row_region` takes from the
interval `i` of `neg` for the row `(a, b)`, `a > 0` (`JPoints.rowRegionPositive`): on the branch of
the larger root, when `l < nh`, from `C(nh)` (`-∞` for `nh = ∞`) to `C(l)`; on the branch of the
smaller root, when `nl < h`, from `C(nl)` (`-∞` for `nl = -∞`) to `C(h)`, for
`l = JPoints.rowRegionFrom` and `h = JPoints.rowRegionUpTo` and `C = JPoints.rowRegionValue`. -/
def RegionPositive (neg : NegativeIntervals) (a b : ℤ) (i : ℕ) (lo hi : Double) : Prop :=
  (rowRegionFrom neg a b i < neg.shrunkHi[i]! ∧
    lo = (if neg.shrunkHi[i]!.beq Double.huge then -Double.huge else
      rowRegionValue a b neg.shrunkHi[i]!) ∧ hi = rowRegionValue a b (rowRegionFrom neg a b i)) ∨
  (neg.shrunkLo[i]! < rowRegionUpTo neg a b i ∧
    lo = (if neg.shrunkLo[i]!.beq (-Double.huge) then -Double.huge else
      rowRegionValue a b neg.shrunkLo[i]!) ∧ hi = rowRegionValue a b (rowRegionUpTo neg a b i))

/-- The invariant of the loops of `JPoints.rowRegionPositive` and `JPoints.rowRegionZero` over the
intervals on which `f` is negative, whose state is the two arrays of the ends of the excluded
intervals: as many lower as upper ends, each pair of the ends of an interval of the first `n`
intervals by the description `E`. -/
def RegionIntervalsInvariant (n : ℕ) (E : ℕ → Double → Double → Prop) :
    Std.WP.Invariant ℕ (Array Double × Array Double) Prop :=
  fun _ _ st ↦ st.1.size = st.2.size ∧ ∀ j < st.1.size, ∃ i < n, E i st.1[j]! st.2[j]!

section Ends

variable {n : ℕ} {E : ℕ → Double → Double → Prop} {pref suff pref' suff' : List ℕ}
  {xlo xhi : Array Double}

theorem regionIntervalsInvariant_nil (n : ℕ) (E : ℕ → Double → Double → Prop) (pref suff : List ℕ) :
    RegionIntervalsInvariant n E pref suff (#[], #[]) :=
  ⟨rfl, fun _ hj ↦ absurd hj (Nat.not_lt_zero _)⟩

theorem RegionIntervalsInvariant.post (h : RegionIntervalsInvariant n E pref suff (xlo, xhi)) :
    xlo.size = xhi.size ∧ ∀ j < xlo.size, ∃ i < n, E i xlo[j]! xhi[j]! :=
  h

theorem RegionIntervalsInvariant.keep {st : Array Double × Array Double}
    (h : RegionIntervalsInvariant n E pref suff st) : RegionIntervalsInvariant n E pref' suff' st :=
  h

theorem RegionIntervalsInvariant.push (h : RegionIntervalsInvariant n E pref suff (xlo, xhi))
    {i : ℕ} (hi : i < n) {lo hi' : Double} (he : E i lo hi') :
    RegionIntervalsInvariant n E pref' suff' (xlo.push lo, xhi.push hi') := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], fun j hj ↦ ?_⟩
  simp only [Array.size_push] at hj
  rcases (show j < xlo.size ∨ j = xlo.size by lia) with hj | rfl
  · rw [Array.getElem!_push_lt hj, Array.getElem!_push_lt (h1 ▸ hj)]
    exact h2 j hj
  · rw [Array.getElem!_push_eq, h1, Array.getElem!_push_eq]
    exact ⟨i, hi, he⟩

end Ends

section Positive

variable {neg : NegativeIntervals} {a b : ℤ} {pref suff pref' suff' : List ℕ} {cur : ℕ}
  {xlo xhi : Array Double}

theorem RegionIntervalsInvariant.push_both (hl : ForIn.toList [:neg.numNeg] = pref ++ cur :: suff)
    (h : RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) pref (cur :: suff) (xlo, xhi))
    (h1 : rowRegionFrom neg a b cur < neg.shrunkHi[cur]!)
    (h2 : neg.shrunkLo[cur]! < rowRegionUpTo neg a b cur) :
    RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) (pref ++ [cur]) suff
      ((xlo.push (if neg.shrunkHi[cur]!.beq Double.huge then -Double.huge else
          rowRegionValue a b neg.shrunkHi[cur]!)).push
        (if neg.shrunkLo[cur]!.beq (-Double.huge) then -Double.huge else
          rowRegionValue a b neg.shrunkLo[cur]!),
       (xhi.push (rowRegionValue a b (rowRegionFrom neg a b cur))).push
        (rowRegionValue a b (rowRegionUpTo neg a b cur))) :=
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  (h.push (pref' := []) (suff' := []) hc (.inl ⟨h1, rfl, rfl⟩)).push hc (.inr ⟨h2, rfl, rfl⟩)

theorem RegionIntervalsInvariant.push_from (hl : ForIn.toList [:neg.numNeg] = pref ++ cur :: suff)
    (h : RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) pref (cur :: suff) (xlo, xhi))
    (h1 : rowRegionFrom neg a b cur < neg.shrunkHi[cur]!) :
    RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) (pref ++ [cur]) suff
      (xlo.push (if neg.shrunkHi[cur]!.beq Double.huge then -Double.huge else
          rowRegionValue a b neg.shrunkHi[cur]!),
       xhi.push (rowRegionValue a b (rowRegionFrom neg a b cur))) :=
  h.push (Std.Legacy.Range.lt_of_toList_eq_append_cons hl) (.inl ⟨h1, rfl, rfl⟩)

theorem RegionIntervalsInvariant.push_upTo (hl : ForIn.toList [:neg.numNeg] = pref ++ cur :: suff)
    (h : RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) pref (cur :: suff) (xlo, xhi))
    (h2 : neg.shrunkLo[cur]! < rowRegionUpTo neg a b cur) :
    RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b) (pref ++ [cur]) suff
      (xlo.push (if neg.shrunkLo[cur]!.beq (-Double.huge) then -Double.huge else
          rowRegionValue a b neg.shrunkLo[cur]!),
       xhi.push (rowRegionValue a b (rowRegionUpTo neg a b cur))) :=
  h.push (Std.Legacy.Range.lt_of_toList_eq_append_cons hl) (.inr ⟨h2, rfl, rfl⟩)

end Positive

attribute [local irreducible] RegionIntervalsInvariant RegionPositive in
/-- The excluded intervals of the third coordinate that `row_region` computes for the row `(a, b)`,
`a > 0`, come from the intervals of `neg` (`JPoints.RegionPositive`). -/
theorem rowRegionPositive_spec (neg : NegativeIntervals) (a b : ℤ) :
    ⦃ True ⦄ rowRegionPositive neg a b
    ⦃ fun r ↦ r.1.size = r.2.size ∧
        ∀ j < r.1.size, ∃ i < neg.numNeg, RegionPositive neg a b i r.1[j]! r.2[j]! ⦄ := by
  vcgen [rowRegionPositive] invariants
  · RegionIntervalsInvariant neg.numNeg (RegionPositive neg a b)
  all_goals with_reducible first
    | exact regionIntervalsInvariant_nil _ _ _ _
    | exact RegionIntervalsInvariant.post ‹_›
    | exact RegionIntervalsInvariant.push_both ‹_› ‹_› ‹_› ‹_›
    | exact RegionIntervalsInvariant.push_from ‹_› ‹_› ‹_›
    | exact RegionIntervalsInvariant.push_upTo ‹_› ‹_› ‹_›
    | exact RegionIntervalsInvariant.keep ‹_›

/-! ### The ends for `a = 0` -/

/-- `(lo, hi)` is the excluded interval of the third coordinate that `row_region` takes from the
interval `(nl, nh)` with the index `i` of `neg` for the row `(0, b)` (`JPoints.rowRegionZero`):
from `B nl` (`-∞` for `nl = -∞`) to `B nh` (`∞` for `nh = ∞`), `B = (double)b`. -/
def RegionZero (neg : NegativeIntervals) (b : ℤ) (i : ℕ) (lo hi : Double) : Prop :=
  lo = (if neg.shrunkLo[i]!.beq (-Double.huge) then -Double.huge else
    Double.ofInt b * neg.shrunkLo[i]!) ∧
  hi = (if neg.shrunkHi[i]!.beq Double.huge then Double.huge else Double.ofInt b * neg.shrunkHi[i]!)

section Zero

variable {neg : NegativeIntervals} {b : ℤ} {pref suff : List ℕ} {cur : ℕ} {xlo xhi : Array Double}

theorem RegionIntervalsInvariant.push_zero (hl : ForIn.toList [:neg.numNeg] = pref ++ cur :: suff)
    (h : RegionIntervalsInvariant neg.numNeg (RegionZero neg b) pref (cur :: suff) (xlo, xhi)) :
    RegionIntervalsInvariant neg.numNeg (RegionZero neg b) (pref ++ [cur]) suff
      (xlo.push (if neg.shrunkLo[cur]!.beq (-Double.huge) then -Double.huge else
          Double.ofInt b * neg.shrunkLo[cur]!),
       xhi.push (if neg.shrunkHi[cur]!.beq Double.huge then Double.huge else
          Double.ofInt b * neg.shrunkHi[cur]!)) :=
  h.push (Std.Legacy.Range.lt_of_toList_eq_append_cons hl) ⟨rfl, rfl⟩

end Zero

attribute [local irreducible] RegionIntervalsInvariant RegionZero in
/-- The excluded intervals of the third coordinate that `row_region` computes for the row `(0, b)`
come from the intervals of `neg` (`JPoints.RegionZero`). -/
theorem rowRegionZero_spec (neg : NegativeIntervals) (b : ℤ) :
    ⦃ True ⦄ rowRegionZero neg b
    ⦃ fun r ↦ r.1.size = r.2.size ∧
        ∀ j < r.1.size, ∃ i < neg.numNeg, RegionZero neg b i r.1[j]! r.2[j]! ⦄ := by
  vcgen [rowRegionZero] invariants
  · RegionIntervalsInvariant neg.numNeg (RegionZero neg b)
  all_goals with_reducible first
    | exact regionIntervalsInvariant_nil _ _ _ _
    | exact RegionIntervalsInvariant.post ‹_›
    | exact RegionIntervalsInvariant.push_zero ‹_› ‹_›

/-! ### The margins -/

/-- The margin `1.0e-9 * (fabs(x) + 1.0) + 1.0` of `row_region` for the end `x` of an excluded
interval. -/
abbrev rowRegionMargin (x : Double) : Double := 1.0e-9 * (x.fabs + 1.0) + 1.0

/-- A lower end `x` of an excluded interval raised by its margin, as `row_region` raises it: an
infinite end kept. -/
abbrev rowRegionMarginLo (x : Double) : Double :=
  if -Double.huge < x then x + rowRegionMargin x else x

/-- An upper end `x` of an excluded interval lowered by its margin, as `row_region` lowers it: an
infinite end kept. -/
abbrev rowRegionMarginHi (x : Double) : Double :=
  if x < Double.huge then x - rowRegionMargin x else x

/-- The array `a` is `a₀` with the first `k` entries moved by `g`: of the size of `a₀`, an entry
`g a₀[i]` below `k` and `a₀[i]` from `k` on. -/
def RegionMarginsPart (a₀ : Array Double) (k : ℕ) (g : Double → Double) (a : Array Double) :
    Prop :=
  a.size = a₀.size ∧ ∀ i < a₀.size, a[i]! = if i < k then g a₀[i]! else a₀[i]!

/-- The invariant of the loop of `JPoints.rowRegionMargins` over the excluded intervals of the
ends `xlo₀` and `xhi₀`: the ends of the intervals done raised and lowered by their margins
(`JPoints.RegionMarginsPart`), the others as they were. -/
def RegionMarginsInvariant (xlo₀ xhi₀ : Array Double) :
    Std.WP.Invariant ℕ (Array Double × Array Double) Prop :=
  fun pref _ st ↦ RegionMarginsPart xlo₀ pref.length rowRegionMarginLo st.1 ∧
    RegionMarginsPart xhi₀ pref.length rowRegionMarginHi st.2

section Margins

variable {a₀ a : Array Double} {k : ℕ} {g : Double → Double}

theorem regionMarginsPart_zero (a₀ : Array Double) (g : Double → Double) :
    RegionMarginsPart a₀ 0 g a₀ :=
  ⟨rfl, fun _ _ ↦ by simp⟩

theorem RegionMarginsPart.set (h : RegionMarginsPart a₀ k g a) {y : Double} (hy : y = g a[k]!) :
    RegionMarginsPart a₀ (k + 1) g (a.set! k y) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Array.size_set!, h1], fun i hi ↦ ?_⟩
  rcases eq_or_ne k i with rfl | hki
  · rw [Array.getElem!_set!_self _ _ _ (h1 ▸ hi), hy, h2 k hi]
    simp
  · rw [Array.getElem!_set!_ne _ _ _ _ hki, h2 i hi]
    simp only [show i < k + 1 ↔ i < k by lia]

theorem RegionMarginsPart.keep (h : RegionMarginsPart a₀ k g a) (hy : a[k]! = g a[k]!) :
    RegionMarginsPart a₀ (k + 1) g a := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i hi ↦ ?_⟩
  rcases eq_or_ne k i with rfl | hki
  · rw [hy, h2 k hi]
    simp
  · rw [h2 i hi]
    simp only [show i < k + 1 ↔ i < k by lia]

end Margins

section MarginsStep

variable {xlo₀ xhi₀ xlo xhi : Array Double} {pref suff : List ℕ}

theorem RegionMarginsPart.set_lo (h : RegionMarginsPart xlo₀ pref.length rowRegionMarginLo xlo)
    (h1 : -Double.huge < xlo[pref.length]!) :
    RegionMarginsPart xlo₀ (pref.length + 1) rowRegionMarginLo
      (xlo.set! pref.length (xlo[pref.length]! + rowRegionMargin xlo[pref.length]!)) :=
  h.set (by simp only [rowRegionMarginLo, h1, ↓reduceIte])

theorem RegionMarginsPart.keep_lo (h : RegionMarginsPart xlo₀ pref.length rowRegionMarginLo xlo)
    (h1 : ¬-Double.huge < xlo[pref.length]!) :
    RegionMarginsPart xlo₀ (pref.length + 1) rowRegionMarginLo xlo :=
  h.keep (by simp only [rowRegionMarginLo, h1, ↓reduceIte])

theorem RegionMarginsPart.set_hi (h : RegionMarginsPart xhi₀ pref.length rowRegionMarginHi xhi)
    (h1 : xhi[pref.length]! < Double.huge) :
    RegionMarginsPart xhi₀ (pref.length + 1) rowRegionMarginHi
      (xhi.set! pref.length (xhi[pref.length]! - rowRegionMargin xhi[pref.length]!)) :=
  h.set (by simp only [rowRegionMarginHi, h1, ↓reduceIte])

theorem RegionMarginsPart.keep_hi (h : RegionMarginsPart xhi₀ pref.length rowRegionMarginHi xhi)
    (h1 : ¬xhi[pref.length]! < Double.huge) :
    RegionMarginsPart xhi₀ (pref.length + 1) rowRegionMarginHi xhi :=
  h.keep (by simp only [rowRegionMarginHi, h1, ↓reduceIte])

end MarginsStep

section MarginsVC

variable {xlo₀ xhi₀ xlo xhi : Array Double} {n : ℕ} {pref suff : List ℕ} {cur : ℕ}

theorem RegionMarginsInvariant.step_set_set (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionMarginsInvariant xlo₀ xhi₀ pref (cur :: suff) (xlo, xhi))
    (h1 : -Double.huge < xlo[cur]!) (h2 : xhi[cur]! < Double.huge) :
    RegionMarginsInvariant xlo₀ xhi₀ (pref ++ [cur]) suff
      (xlo.set! cur (xlo[cur]! + rowRegionMargin xlo[cur]!),
        xhi.set! cur (xhi[cur]! - rowRegionMargin xhi[cur]!)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simp only [RegionMarginsInvariant, List.length_append, List.length_singleton]
  exact ⟨h.1.set_lo h1, h.2.set_hi h2⟩

theorem RegionMarginsInvariant.step_set_keep (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionMarginsInvariant xlo₀ xhi₀ pref (cur :: suff) (xlo, xhi))
    (h1 : -Double.huge < xlo[cur]!) (h2 : ¬xhi[cur]! < Double.huge) :
    RegionMarginsInvariant xlo₀ xhi₀ (pref ++ [cur]) suff
      (xlo.set! cur (xlo[cur]! + rowRegionMargin xlo[cur]!), xhi) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simp only [RegionMarginsInvariant, List.length_append, List.length_singleton]
  exact ⟨h.1.set_lo h1, h.2.keep_hi h2⟩

theorem RegionMarginsInvariant.step_keep_set (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionMarginsInvariant xlo₀ xhi₀ pref (cur :: suff) (xlo, xhi))
    (h1 : ¬-Double.huge < xlo[cur]!) (h2 : xhi[cur]! < Double.huge) :
    RegionMarginsInvariant xlo₀ xhi₀ (pref ++ [cur]) suff
      (xlo, xhi.set! cur (xhi[cur]! - rowRegionMargin xhi[cur]!)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simp only [RegionMarginsInvariant, List.length_append, List.length_singleton]
  exact ⟨h.1.keep_lo h1, h.2.set_hi h2⟩

theorem RegionMarginsInvariant.step_keep_keep (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionMarginsInvariant xlo₀ xhi₀ pref (cur :: suff) (xlo, xhi))
    (h1 : ¬-Double.huge < xlo[cur]!) (h2 : ¬xhi[cur]! < Double.huge) :
    RegionMarginsInvariant xlo₀ xhi₀ (pref ++ [cur]) suff (xlo, xhi) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simp only [RegionMarginsInvariant, List.length_append, List.length_singleton]
  exact ⟨h.1.keep_lo h1, h.2.keep_hi h2⟩

theorem regionMarginsInvariant_nil (xlo₀ xhi₀ : Array Double) (suff : List ℕ) :
    RegionMarginsInvariant xlo₀ xhi₀ [] suff (xlo₀, xhi₀) :=
  ⟨regionMarginsPart_zero _ _, regionMarginsPart_zero _ _⟩

theorem RegionMarginsInvariant.post
    (h : RegionMarginsInvariant xlo₀ xhi₀ (ForIn.toList [:n]) [] (xlo, xhi)) :
    RegionMarginsPart xlo₀ n rowRegionMarginLo xlo ∧
      RegionMarginsPart xhi₀ n rowRegionMarginHi xhi := by
  have h := h
  rwa [RegionMarginsInvariant, Std.Legacy.Range.length_toList, Nat.sub_zero] at h

end MarginsVC

attribute [local irreducible] RegionMarginsInvariant in
/-- `row_region` raises the first `n` lower ends and lowers the first `n` upper ends of the
excluded intervals by their margins. -/
theorem rowRegionMargins_spec (xlo xhi : Array Double) (n : ℕ) :
    ⦃ True ⦄ rowRegionMargins xlo xhi n
    ⦃ fun r ↦ RegionMarginsPart xlo n rowRegionMarginLo r.1 ∧
        RegionMarginsPart xhi n rowRegionMarginHi r.2 ⦄ := by
  vcgen [rowRegionMargins] invariants
  · RegionMarginsInvariant xlo xhi
  all_goals with_reducible first
    | exact regionMarginsInvariant_nil _ _ _
    | exact RegionMarginsInvariant.post ‹_›
    | exact RegionMarginsInvariant.step_set_set ‹_› ‹_› ‹_› ‹_›
    | exact RegionMarginsInvariant.step_set_keep ‹_› ‹_› ‹_› ‹_›
    | exact RegionMarginsInvariant.step_keep_set ‹_› ‹_› ‹_› ‹_›
    | exact RegionMarginsInvariant.step_keep_keep ‹_› ‹_› ‹_› ‹_›

/-! ### The sort -/

/-- Each of the first `n` pairs of entries of `u` and `v` is one of the first `n` pairs of entries
of `xlo₀` and `xhi₀`: what the insertion sort of `row_region` keeps. -/
def RegionSortedAmong (xlo₀ xhi₀ : Array Double) (n : ℕ) (u v : Array Double) : Prop :=
  ∀ k < n, ∃ j < n, u[k]! = xlo₀[j]! ∧ v[k]! = xhi₀[j]!

/-- The invariant of the outer loop of `JPoints.rowRegionSort`: the arrays keep their sizes, and
their pairs of entries are among those given (`JPoints.RegionSortedAmong`). -/
def RegionSortInvariant (xlo₀ xhi₀ : Array Double) (n : ℕ) :
    Std.WP.Invariant ℕ (Array Double × Array Double) Prop :=
  fun _ _ st ↦ n ≤ xlo₀.size ∧ st.1.size = xlo₀.size ∧ st.2.size = xlo₀.size ∧
    RegionSortedAmong xlo₀ xhi₀ n st.1 st.2

/-- The invariant of the inner loop of `JPoints.rowRegionSort`, whose state is the two arrays and
the index `j`: the arrays keep their sizes, `j` stays below `n`, and their pairs of entries are
among those given (`JPoints.RegionSortedAmong`). -/
def RegionSortInnerInvariant (xlo₀ xhi₀ : Array Double) (n : ℕ) :
    Std.WP.WhileInvariant (Array Double × Array Double × ℕ) Prop :=
  .mk fun _ s ↦ n ≤ xlo₀.size ∧ s.1.size = xlo₀.size ∧ s.2.1.size = xlo₀.size ∧ s.2.2 < n ∧
    RegionSortedAmong xlo₀ xhi₀ n s.1 s.2.1

section RowSort

variable {xlo₀ xhi₀ u v u' v' : Array Double} {n : ℕ} {pref suff : List ℕ} {cur : ℕ}

theorem RegionSortedAmong.set (h : RegionSortedAmong xlo₀ xhi₀ n u v) {k : ℕ} (hu : k < u.size)
    (hv : k < v.size)
    {x y : Double} (hxy : ∃ j < n, x = xlo₀[j]! ∧ y = xhi₀[j]!) :
    RegionSortedAmong xlo₀ xhi₀ n (u.set! k x) (v.set! k y) := fun k' hk' ↦ by
  rcases eq_or_ne k k' with rfl | hk
  · rw [Array.getElem!_set!_self _ _ _ hu, Array.getElem!_set!_self _ _ _ hv]
    exact hxy
  · rw [Array.getElem!_set!_ne _ _ _ _ hk, Array.getElem!_set!_ne _ _ _ _ hk]
    exact h k' hk'

theorem regionSortInvariant_init (h : n ≤ xlo₀.size ∧ xhi₀.size = xlo₀.size) (pref suff : List ℕ) :
    RegionSortInvariant xlo₀ xhi₀ n pref suff (xlo₀, xhi₀) :=
  ⟨h.1, rfl, h.2, fun k hk ↦ ⟨k, hk, rfl, rfl⟩⟩

theorem RegionSortInvariant.post (h : RegionSortInvariant xlo₀ xhi₀ n pref suff (u, v)) :
    u.size = xlo₀.size ∧ v.size = xlo₀.size ∧ RegionSortedAmong xlo₀ xhi₀ n u v :=
  h.2

theorem RegionSortInvariant.inner (hl : ForIn.toList [1:n] = pref ++ cur :: suff)
    (h : RegionSortInvariant xlo₀ xhi₀ n pref (cur :: suff) (u, v)) :
    RegionSortInnerInvariant xlo₀ xhi₀ n false (u, v, cur) := by
  simp only [RegionSortInnerInvariant, Std.WP.WhileInvariant.mk_apply]
  exact ⟨h.1, h.2.1, h.2.2.1, Std.Legacy.Range.lt_of_toList_eq_append_cons hl, h.2.2.2⟩

theorem RegionSortInnerInvariant.step {j mb : ℕ} {l : Double}
    (hc : (decide (0 < j) && decide (l < u[j - 1]!)) = true)
    (h : j = mb ∧ RegionSortInnerInvariant xlo₀ xhi₀ n false (u, v, j)) :
    j - 1 < mb ∧ RegionSortInnerInvariant xlo₀ xhi₀ n false
      (u.set! j u[j - 1]!, v.set! j v[j - 1]!, j - 1) := by
  simp only [RegionSortInnerInvariant, Std.WP.WhileInvariant.mk_apply] at h ⊢
  obtain ⟨rfl, h0, h1, h2, h3, h4⟩ := h
  have hj : 0 < j := by simp_all
  exact ⟨by lia, h0, by simp [h1], by simp [h2], by lia, h4.set (by lia) (by lia) (h4 _ (by lia))⟩

theorem RegionSortInnerInvariant.exit {s : Array Double × Array Double × ℕ} {mb : ℕ}
    (h : s.2.2 = mb ∧ RegionSortInnerInvariant xlo₀ xhi₀ n false s) :
    RegionSortInnerInvariant xlo₀ xhi₀ n true s :=
  h.2

theorem RegionSortInnerInvariant.post (hl : ForIn.toList [1:n] = pref ++ cur :: suff)
    (h : RegionSortInvariant xlo₀ xhi₀ n pref (cur :: suff) (u, v)) {j : ℕ}
    (hin : RegionSortInnerInvariant xlo₀ xhi₀ n true (u', v', j)) :
    RegionSortInvariant xlo₀ xhi₀ n (pref ++ [cur]) suff
      (u'.set! j u[cur]!, v'.set! j v[cur]!) := by
  simp only [RegionSortInnerInvariant, Std.WP.WhileInvariant.mk_apply] at hin
  obtain ⟨h0, h1, h2, h3, h4⟩ := hin
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  exact ⟨h0, by simp [h1], by simp [h2], h4.set (by lia) (by lia) (h.2.2.2 cur hc)⟩

end RowSort

attribute [local irreducible] RegionSortInvariant RegionSortInnerInvariant in
/-- The insertion sort of `row_region` keeps the sizes of the arrays and permutes nothing but their
first `n` pairs of entries among themselves. -/
theorem rowRegionSort_spec (xlo xhi : Array Double) (n : ℕ) :
    ⦃ n ≤ xlo.size ∧ xhi.size = xlo.size ⦄ rowRegionSort xlo xhi n
    ⦃ fun r ↦ r.1.size = xlo.size ∧ r.2.size = xlo.size ∧
        RegionSortedAmong xlo xhi n r.1 r.2 ⦄ := by
  vcgen [rowRegionSort] invariants
  · RegionSortInvariant xlo xhi n
  · RegionSortInnerInvariant xlo xhi n
  · Std.WP.Variant.ofMeasure fun s : Array Double × Array Double × ℕ ↦ s.2.2
  all_goals try vc_simp
  all_goals with_reducible first
    | exact regionSortInvariant_init ‹_› _ _
    | exact RegionSortInvariant.post ‹_›
    | exact RegionSortInvariant.inner ‹_› ‹_›
    | exact RegionSortInnerInvariant.step ‹_› ‹_›
    | exact RegionSortInnerInvariant.exit ‹_›
    | exact RegionSortInnerInvariant.post ‹_› ‹_› ‹_›

/-! ### The words -/

/-- `row_region` takes the word `v` out of the row for the excluded interval `(xl, xh)`: the
interval does not lie beyond the row, and `v` lies in its words `[wl, wh)`
(`JPoints.rowRegionEnds`). -/
def RegionExcludes (sd : SiftData) (xl xh : Double) (v : ℤ) : Prop :=
  ¬rowBeyond ≤ xl ∧ ¬xh ≤ -rowBeyond ∧ (rowRegionEnds sd xl xh).1 ≤ v ∧
    v < (rowRegionEnds sd xl xh).2

/-- Every word of the row below `w` lies in a range of `r` or is taken out of the row for one of the
first `k` excluded intervals `(xlo[i], xhi[i])` (`JPoints.RegionExcludes`). -/
def RegionCovers (sd : SiftData) (xlo xhi : Array Double) (k : ℕ) (w : ℤ)
    (r : ℕ × Array ℤ × Array ℤ) : Prop :=
  ∀ v, sd.wLowAll ≤ v → v < w →
    (∃ q ∈ rangeList r, q.1 ≤ v ∧ v < q.2) ∨ ∃ i < k, RegionExcludes sd xlo[i]! xhi[i]! v

/-- The invariant of the loop of `JPoints.rowRegionWords` over the excluded intervals, whose state
is the first word `w` not yet placed and the ranges: `w` in the row, as many lower as upper ends of
the ranges as their number, and every word below `w` covered (`JPoints.RegionCovers`). -/
def RegionCoverInvariant (sd : SiftData) (xlo xhi : Array Double) :
    Std.WP.Invariant ℕ (ℤ × ℕ × Array ℤ × Array ℤ) Prop :=
  fun pref _ st ↦ sd.wLowAll ≤ st.1 ∧ st.2.2.1.size = st.2.1 ∧ st.2.2.2.size = st.2.1 ∧
    RegionCovers sd xlo xhi pref.length st.1 st.2

section Words

variable {sd : SiftData} {xlo xhi : Array Double} {n : ℕ} {pref suff : List ℕ} {cur : ℕ}
  {w : ℤ} {nr : ℕ} {lo hi : Array ℤ}

theorem regionCoverInvariant_nil (sd : SiftData) (xlo xhi : Array Double) (suff : List ℕ) :
    RegionCoverInvariant sd xlo xhi [] suff (sd.wLowAll, 0, #[], #[]) :=
  ⟨le_rfl, rfl, rfl, fun _ h1 h2 ↦ absurd h2 (not_lt.mpr h1)⟩

theorem RegionCoverInvariant.skip {st : ℤ × ℕ × Array ℤ × Array ℤ}
    (h : RegionCoverInvariant sd xlo xhi pref (cur :: suff) st) :
    RegionCoverInvariant sd xlo xhi (pref ++ [cur]) suff st := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv1 hv2 ↦ (h4 v hv1 hv2).imp_right fun ⟨i, hi, he⟩ ↦ ⟨i, ?_, he⟩⟩
  simp only [List.length_append, List.length_singleton]
  lia

-- A word in the words `[wl, wh)` wholly inside the excluded interval `cur`.
private theorem regionExcludes_of_le_of_lt {e : ℤ × ℤ}
    (he : rowRegionEnds sd xlo[cur]! xhi[cur]! = e)
    (h1 : ¬(decide (rowBeyond ≤ xlo[cur]!) || decide (xhi[cur]! ≤ -rowBeyond)) = true) {v : ℤ}
    (hv1 : e.1 ≤ v) (hv2 : v < e.2) : RegionExcludes sd xlo[cur]! xhi[cur]! v := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1
  exact ⟨h1.1, h1.2, he ▸ hv1, he ▸ hv2⟩

-- The bounds of the first word `wl = max(e.1, w)` after the words `[w, wl)` that a step of
-- `JPoints.rowRegionWords` places, and of the next first word `min(W, e.2)`.
private theorem ite_bounds (e : ℤ × ℤ) (w W : ℤ) :
    e.1 ≤ (if e.1 < w then w else e.1) ∧ w ≤ (if e.1 < w then w else e.1) ∧
      (if W < e.2 then W else e.2) ≤ e.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> lia

-- A step of the loop of `JPoints.rowRegionWords` for the excluded interval `cur`, whose words `e`
-- it takes out (`hex`), which gives the ranges `r` and moves the first word not yet placed from `w`
-- to `wh ≤ e.2`: the words below `w` stay covered, those of `[w, wl)` lie in a range of `r`, and
-- those of `[wl, wh)`, `e.1 ≤ wl`, are taken out by the interval.
private theorem regionCoverInvariant_step (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionCoverInvariant sd xlo xhi pref (cur :: suff) (w, nr, lo, hi)) {e : ℤ × ℤ}
    (hex : ∀ v, e.1 ≤ v → v < e.2 → RegionExcludes sd xlo[cur]! xhi[cur]! v)
    {wl wh : ℤ} (hA : e.1 ≤ wl) (hA' : w ≤ wl) (hB : wh ≤ e.2) (h2 : ¬wh ≤ wl)
    {r : ℕ × Array ℤ × Array ℤ} (hs1 : r.2.1.size = r.1) (hs2 : r.2.2.size = r.1)
    (hr : ∀ q ∈ rangeList (nr, lo, hi), q ∈ rangeList r)
    (hnew : ∀ v, w ≤ v → v < wl → ∃ q ∈ rangeList r, q.1 ≤ v ∧ v < q.2) :
    RegionCoverInvariant sd xlo xhi (pref ++ [cur]) suff (wh, r) := by
  obtain ⟨hw, -, -, hc⟩ := h
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by lia, hs1, hs2, fun v hv1 hv2 ↦ ?_⟩
  simp only [List.length_append, List.length_singleton]
  by_cases hvw : v < w
  · rcases hc v hv1 hvw with ⟨q, hq, hq'⟩ | ⟨i, hi, hi'⟩
    · exact .inl ⟨q, hr q hq, hq'⟩
    · exact .inr ⟨i, by lia, hi'⟩
  by_cases hvl : v < wl
  · exact .inl (hnew v (by lia) hvl)
  · exact .inr ⟨pref.length, by lia, hex v (by lia) (by lia)⟩

theorem RegionCoverInvariant.push (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionCoverInvariant sd xlo xhi pref (cur :: suff) (w, nr, lo, hi)) {e : ℤ × ℤ}
    (he : rowRegionEnds sd xlo[cur]! xhi[cur]! = e)
    (h1 : ¬(decide (rowBeyond ≤ xlo[cur]!) || decide (xhi[cur]! ≤ -rowBeyond)) = true)
    (h2 : ¬(if sd.wHighAll < e.2 then sd.wHighAll else e.2) ≤ (if e.1 < w then w else e.1)) :
    RegionCoverInvariant sd xlo xhi (pref ++ [cur]) suff
      ((if sd.wHighAll < e.2 then sd.wHighAll else e.2), nr + 1, lo.push w,
        hi.push (if e.1 < w then w else e.1)) := by
  have hs1 : lo.size = nr := h.2.1
  have hs2 : hi.size = nr := h.2.2.1
  obtain ⟨hA, hA', hB⟩ := ite_bounds e w sd.wHighAll
  refine regionCoverInvariant_step hl h (fun _ ↦ regionExcludes_of_le_of_lt he h1) hA hA' hB h2
    (by simp [hs1]) (by simp [hs2])
    (fun q hq ↦ by rw [rangeList_push hs1 hs2]; exact List.mem_append_left _ hq)
    fun v hv1 hv2 ↦ ⟨(w, if e.1 < w then w else e.1), ?_, hv1, hv2⟩
  rw [rangeList_push hs1 hs2]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem RegionCoverInvariant.place (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : RegionCoverInvariant sd xlo xhi pref (cur :: suff) (w, nr, lo, hi)) {e : ℤ × ℤ}
    (he : rowRegionEnds sd xlo[cur]! xhi[cur]! = e)
    (h1 : ¬(decide (rowBeyond ≤ xlo[cur]!) || decide (xhi[cur]! ≤ -rowBeyond)) = true)
    (h2 : ¬(if sd.wHighAll < e.2 then sd.wHighAll else e.2) ≤ (if e.1 < w then w else e.1))
    (h3 : ¬w < if e.1 < w then w else e.1) :
    RegionCoverInvariant sd xlo xhi (pref ++ [cur]) suff
      ((if sd.wHighAll < e.2 then sd.wHighAll else e.2), nr, lo, hi) :=
  have hb := ite_bounds e w sd.wHighAll
  regionCoverInvariant_step hl h (fun _ ↦ regionExcludes_of_le_of_lt he h1) hb.1 hb.2.1 hb.2.2 h2
    h.2.1 h.2.2.1 (fun _ hq ↦ hq) fun _ hv1 hv2 ↦ absurd (hv1.trans_lt hv2) h3

theorem RegionCoverInvariant.post_push
    (h : RegionCoverInvariant sd xlo xhi (ForIn.toList [:n]) [] (w, nr, lo, hi)) :
    RegionCovers sd xlo xhi n sd.wHighAll (nr + 1, lo.push w, hi.push sd.wHighAll) := by
  obtain ⟨-, hs1, hs2, hc⟩ := h
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at hc
  intro v hv1 hv2
  rw [rangeList_push hs1 hs2]
  by_cases hvw : v < w
  · exact (hc v hv1 hvw).imp_left fun ⟨q, hq, hq'⟩ ↦ ⟨q, List.mem_append_left _ hq, hq'⟩
  · exact .inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by lia, hv2⟩

theorem RegionCoverInvariant.post
    (h : RegionCoverInvariant sd xlo xhi (ForIn.toList [:n]) [] (w, nr, lo, hi))
    (hw : ¬w < sd.wHighAll) : RegionCovers sd xlo xhi n sd.wHighAll (nr, lo, hi) := by
  obtain ⟨-, -, -, hc⟩ := h
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at hc
  exact fun v hv1 hv2 ↦ hc v hv1 (by lia)

end Words

attribute [local irreducible] RegionCoverInvariant in
/-- `row_region` covers every word of the row by its ranges, but for the words of its first `n`
excluded intervals (`JPoints.RegionCovers`). -/
theorem rowRegionWords_cover (sd : SiftData) (xlo xhi : Array Double) (n : ℕ) :
    ⦃ True ⦄ rowRegionWords sd xlo xhi n
    ⦃ fun r ↦ RegionCovers sd xlo xhi n sd.wHighAll r ⦄ := by
  vcgen [rowRegionWords] invariants
  · RegionCoverInvariant sd xlo xhi
  all_goals with_reducible first
    | exact regionCoverInvariant_nil _ _ _ _
    | exact RegionCoverInvariant.post_push ‹_›
    | exact RegionCoverInvariant.post ‹_› ‹_›
    | exact RegionCoverInvariant.push ‹_› ‹_› rfl ‹_› ‹_›
    | exact RegionCoverInvariant.place ‹_› ‹_› rfl ‹_› ‹_› ‹_›
    | exact RegionCoverInvariant.skip ‹_›

/-! ### The order of the ranges -/

/-- The invariant of the loop of `JPoints.rowRegionWords` over the excluded intervals, whose state
is the first word `w` not yet placed, the number of the ranges and their ends: `w` among the words
of the row, the ranges below `w` in increasing order. -/
def RowRegionWordsInvariant (sd : SiftData) :
    Std.WP.Invariant ℕ (ℤ × ℕ × Array ℤ × Array ℤ) Prop :=
  fun _ _ st ↦ sd.wLowAll ≤ st.1 ∧ st.1 ≤ sd.wHighAll ∧ st.2.2.1.size = st.2.1 ∧
    st.2.2.2.size = st.2.1 ∧ RangesIn sd.wLowAll st.1 (rangeList st.2)

section RowRegionWords

variable {sd : SiftData} {p s p' s' : List ℕ} {w : ℤ} {nr : ℕ} {lo hi : Array ℤ}

private theorem RowRegionWordsInvariant.keep (h : RowRegionWordsInvariant sd p s (w, nr, lo, hi)) :
    RowRegionWordsInvariant sd p' s' (w, nr, lo, hi) :=
  h

private theorem rowRegionWordsInvariant_push (h : RowRegionWordsInvariant sd p s (w, nr, lo, hi))
    {e1 e2 : ℤ}
    (hlt : ¬(if sd.wHighAll < e2 then sd.wHighAll else e2) ≤ (if e1 < w then w else e1))
    (hw : w < if e1 < w then w else e1) :
    RowRegionWordsInvariant sd p' s' (if sd.wHighAll < e2 then sd.wHighAll else e2, nr + 1,
      lo.push w, hi.push (if e1 < w then w else e1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  refine ⟨by split_ifs at * <;> lia, by split_ifs at * <;> lia, by simp [h3], by simp [h4], ?_⟩
  dsimp only
  rw [rangeList_push h3 h4]
  exact (h5.concat h1 hw).mono (by lia)

private theorem rowRegionWordsInvariant_skip (h : RowRegionWordsInvariant sd p s (w, nr, lo, hi))
    {e1 e2 : ℤ}
    (hlt : ¬(if sd.wHighAll < e2 then sd.wHighAll else e2) ≤ (if e1 < w then w else e1))
    (hw : ¬w < if e1 < w then w else e1) :
    RowRegionWordsInvariant sd p' s'
      (if sd.wHighAll < e2 then sd.wHighAll else e2, nr, lo, hi) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  refine ⟨by split_ifs at * <;> lia, by split_ifs at * <;> lia, h3, h4, h5.mono ?_⟩
  split_ifs at * <;> lia

private theorem rowRegionWordsInvariant_post_push
    (h : RowRegionWordsInvariant sd p s (w, nr, lo, hi)) (hw : w < sd.wHighAll) :
    RangesIn sd.wLowAll sd.wHighAll (rangeList (nr + 1, lo.push w, hi.push sd.wHighAll)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  rw [rangeList_push h3 h4]
  exact h5.concat h1 hw

private theorem rowRegionWordsInvariant_post
    (h : RowRegionWordsInvariant sd p s (w, nr, lo, hi)) (hw : ¬w < sd.wHighAll) :
    RangesIn sd.wLowAll sd.wHighAll (rangeList (nr, lo, hi)) := by
  obtain ⟨-, h2, -, -, h5⟩ := h
  exact h5.mono (by lia)

end RowRegionWords

theorem rowRegionWords_spec (sd : SiftData) (xlo xhi : Array Double) (n : ℕ) :
    ⦃ sd.wLowAll < sd.wHighAll ⦄
    rowRegionWords sd xlo xhi n
    ⦃ fun r ↦ RangesIn sd.wLowAll sd.wHighAll (rangeList r) ⦄ := by
  vcgen [rowRegionWords] invariants
  · RowRegionWordsInvariant sd
  all_goals try dsimp only at *
  all_goals first
    | exact ⟨le_rfl, le_of_lt ‹_›, rfl, rfl, rangesIn_nil _ _⟩
    | exact rowRegionWordsInvariant_post_push ‹_› ‹_›
    | exact rowRegionWordsInvariant_post ‹_› ‹_›
    | exact rowRegionWordsInvariant_push ‹_› ‹_› ‹_›
    | exact rowRegionWordsInvariant_skip ‹_› ‹_› ‹_›
    | exact RowRegionWordsInvariant.keep ‹_›

theorem rowRegion_spec (neg : NegativeIntervals) (sd : SiftData) (a b : ℤ) :
    ⦃ sd.wLowAll < sd.wHighAll ⦄
    rowRegion neg sd a b
    ⦃ fun r ↦ RangesIn sd.wLowAll sd.wHighAll (rangeList r) ⦄ := by
  vcgen [rowRegion, rowRegionWords_spec, Std.WP.Id.triple_eq_run (rowRegionPositive _ _ _),
    Std.WP.Id.triple_eq_run (rowRegionZero _ _), Std.WP.Id.triple_eq_run (rowRegionMargins _ _ _),
    Std.WP.Id.triple_eq_run (rowRegionSort _ _ _)]
  all_goals first
    | assumption
    | exact rangesIn_singleton ‹_›

/-! ### The cover -/

/-- `(lo, hi)` is an excluded interval of the third coordinate that `row_region` takes from the
interval `i` of `neg` for the row `(a, b)`: by `JPoints.RegionPositive` for `a > 0`, by
`JPoints.RegionZero` otherwise. -/
def RegionInterval (neg : NegativeIntervals) (a b : ℤ) (i : ℕ) (lo hi : Double) : Prop :=
  (0 < a ∧ RegionPositive neg a b i lo hi) ∨ (¬0 < a ∧ RegionZero neg b i lo hi)

section Cover

variable {sd : SiftData} {E : ℕ → Double → Double → Prop} {n₀ : ℕ}
  {xlo₀ xhi₀ xlo₁ xhi₁ xlo xhi : Array Double}

theorem rowRegionSort_pre_of_parts
    (h0 : xlo₀.size = xhi₀.size ∧ ∀ j < xlo₀.size, ∃ i < n₀, E i xlo₀[j]! xhi₀[j]!)
    (h1 : RegionMarginsPart xlo₀ xlo₀.size rowRegionMarginLo xlo₁ ∧
      RegionMarginsPart xhi₀ xlo₀.size rowRegionMarginHi xhi₁) :
    xlo₀.size ≤ xlo₁.size ∧ xhi₁.size = xlo₁.size :=
  ⟨h1.1.1.ge, by rw [h1.2.1, h1.1.1, h0.1]⟩

theorem regionCovers_of_parts
    (h0 : xlo₀.size = xhi₀.size ∧ ∀ j < xlo₀.size, ∃ i < n₀, E i xlo₀[j]! xhi₀[j]!)
    (h1 : RegionMarginsPart xlo₀ xlo₀.size rowRegionMarginLo xlo₁ ∧
      RegionMarginsPart xhi₀ xlo₀.size rowRegionMarginHi xhi₁)
    (h2 : xlo.size = xlo₁.size ∧ xhi.size = xlo₁.size ∧
      RegionSortedAmong xlo₁ xhi₁ xlo₀.size xlo xhi)
    {r : ℕ × Array ℤ × Array ℤ} (h3 : RegionCovers sd xlo xhi xlo₀.size sd.wHighAll r) {v : ℤ}
    (hv1 : sd.wLowAll ≤ v) (hv2 : v < sd.wHighAll) :
    (∃ q ∈ rangeList r, q.1 ≤ v ∧ v < q.2) ∨
      ∃ i < n₀, ∃ lo hi, E i lo hi ∧
        RegionExcludes sd (rowRegionMarginLo lo) (rowRegionMarginHi hi) v := by
  refine (h3 v hv1 hv2).imp_right fun ⟨k, hk, hx⟩ ↦ ?_
  obtain ⟨j, hj, hlo, hhi⟩ := h2.2.2 k hk
  obtain ⟨i, hi, he⟩ := h0.2 j hj
  have hl := h1.1.2 j hj
  have hh := h1.2.2 j (h0.1 ▸ hj)
  rw [ite_eq_left hj] at hl hh
  exact ⟨i, hi, _, _, he, by rwa [hlo, hhi, hl, hh] at hx⟩

theorem exists_mem_rangeList_singleton {v : ℤ} (hv1 : sd.wLowAll ≤ v) (hv2 : v < sd.wHighAll) :
    ∃ q ∈ rangeList (1, #[sd.wLowAll], #[sd.wHighAll]), q.1 ≤ v ∧ v < q.2 :=
  ⟨(sd.wLowAll, sd.wHighAll), by simp [rangeList], hv1, hv2⟩

end Cover

/-- `row_region` keeps every word of the row that no excluded interval takes out: a word of the row
lies in one of its ranges, or in the words of an excluded interval `(lo, hi)` from an interval of
`neg` (`JPoints.RegionInterval`), raised and lowered by its margins
(`JPoints.rowRegionMarginLo`, `JPoints.rowRegionMarginHi`). -/
theorem rowRegion_cover (neg : NegativeIntervals) (sd : SiftData) (a b : ℤ) :
    ⦃ sd.wLowAll < sd.wHighAll ⦄ rowRegion neg sd a b
    ⦃ fun r ↦ ∀ v, sd.wLowAll ≤ v → v < sd.wHighAll → (∃ q ∈ rangeList r, q.1 ≤ v ∧ v < q.2) ∨
        ∃ i < neg.numNeg, ∃ lo hi, RegionInterval neg a b i lo hi ∧
          RegionExcludes sd (rowRegionMarginLo lo) (rowRegionMarginHi hi) v ⦄ := by
  vcgen [rowRegion, rowRegionPositive_spec, rowRegionZero_spec, rowRegionMargins_spec,
    rowRegionSort_spec, rowRegionWords_cover]
  all_goals first
    | exact .inl (exists_mem_rangeList_singleton ‹_› ‹_›)
    | exact rowRegionSort_pre_of_parts ‹_› ‹_›
    | exact (regionCovers_of_parts ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).imp_right
        fun ⟨i, hi, lo, hi', he, hx⟩ ↦ ⟨i, hi, lo, hi', .inl ⟨‹_›, he⟩, hx⟩
    | exact (regionCovers_of_parts ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).imp_right
        fun ⟨i, hi, lo, hi', he, hx⟩ ↦ ⟨i, hi, lo, hi', .inr ⟨‹_›, he⟩, hx⟩

theorem exists_mem_rangeList_rowRegion_or_regionExcludes {neg : NegativeIntervals} {sd : SiftData}
    (hw : sd.wLowAll < sd.wHighAll) (a b : ℤ) {v : ℤ} (hv1 : sd.wLowAll ≤ v)
    (hv2 : v < sd.wHighAll) :
    (∃ q ∈ rangeList (rowRegion neg sd a b).run, q.1 ≤ v ∧ v < q.2) ∨
      ∃ i < neg.numNeg, ∃ lo hi, RegionInterval neg a b i lo hi ∧
        RegionExcludes sd (rowRegionMarginLo lo) (rowRegionMarginHi hi) v :=
  (rowRegion_cover neg sd a b).le_wp hw v hv1 hv2

end JPoints

end
