/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence

/-!
# Sturm sequences under a map of fields, and computed remainder sequences

Candidates for `Mathlib.Algebra.Polynomial.Sturm.Sequence`: the Sturm sequence commutes with a map
of fields (`Polynomial.sturmSeq_map`), and a list `g 0, …, g (n - 1)` of nonzero polynomials, each
from the third on the negated remainder of the two before it, whose next negated remainder is zero,
is the Sturm sequence of its first two entries (`Polynomial.map_range_eq_sturmSeq`): the sequence
that a program computes by the Euclidean algorithm, until a zero remainder.

## Main statements

* `Polynomial.sturmSeq_map`: the Sturm sequence of the images under a map of fields.
* `Polynomial.map_range_eq_sturmSeq`: a remainder sequence ending at a zero remainder is the Sturm
  sequence.

## References

`Polynomial.sturmSeq_map` is adapted from `Ratpoints/Mathlib/Algebra/Polynomial/Sturm/Sequence.lean`
of [RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

namespace Polynomial

section Map

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

/-- The Sturm sequence commutes with a map of fields. -/
theorem sturmSeq_map (φ : K →+* L) (p q : K[X]) :
    sturmSeq (p.map φ) (q.map φ) = (sturmSeq p q).map (map φ) := by
  induction p, q using sturmSeq.induct with
  | case1 q => simp
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp, sturmSeq_cons ((Polynomial.map_ne_zero_iff φ.injective).mpr hp),
      List.map_cons, ← ih, map_mod, Polynomial.map_neg]

end Map

variable {K : Type*} [Field K] [DecidableEq K]

-- The entries `g j, …, g (n - 1)` of a remainder sequence are the Sturm sequence of the first two.
private theorem map_range'_eq_sturmSeq {g : ℕ → K[X]} {n : ℕ} (h0 : ∀ i < n, g i ≠ 0)
    (hrem : ∀ i, i + 2 < n → g (i + 2) = -g i % g (i + 1)) (hlast : -g (n - 2) % g (n - 1) = 0)
    (j : ℕ) (hj : j + 2 ≤ n) : (List.range' j (n - j)).map g = sturmSeq (g j) (g (j + 1)) := by
  induction h : n - j generalizing j with
  | zero => lia
  | succ m ih =>
    rw [List.range'_succ, List.map_cons, sturmSeq_cons (h0 j (by lia))]
    rcases Nat.lt_or_ge (j + 2) n with hjn | hjn
    · rw [← hrem j hjn, ← ih (j + 1) (by lia) (by lia)]
    · obtain rfl : j = n - 2 := by lia
      rw [show n - 2 + 1 = n - 1 by lia, hlast, sturmSeq_zero_right, ite_eq_right (h0 _ (by lia)),
        show m = 1 by lia]
      simp

/-- A list `g 0, …, g (n - 1)` of nonzero polynomials, each from the third on the negated
remainder of the two before it, whose next negated remainder is zero, is the Sturm sequence of its
first two entries. -/
theorem map_range_eq_sturmSeq {g : ℕ → K[X]} {n : ℕ} (hn : 2 ≤ n) (h0 : ∀ i < n, g i ≠ 0)
    (hrem : ∀ i, i + 2 < n → g (i + 2) = -g i % g (i + 1)) (hlast : -g (n - 2) % g (n - 1) = 0) :
    (List.range n).map g = sturmSeq (g 0) (g 1) := by
  rw [List.range_eq_range', ← map_range'_eq_sturmSeq h0 hrem hlast 0 (by lia), Nat.sub_zero]

end Polynomial

end
