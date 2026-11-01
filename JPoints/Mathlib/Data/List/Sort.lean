/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Sort

/-!
# The elements of a sorted list below a bound

A candidate for `Mathlib.Data.List.Sort`: the elements below a bound of a list sorted by `<` form
a prefix of the list, next to `List.Pairwise.eq_of_mem_iff`.

## Main statements

* `List.Pairwise.filter_lt_prefix`: the elements of a sorted list below a bound form a prefix.
-/

@[expose] public section

namespace List

variable {α : Type*} [Preorder α] [DecidableLT α]

theorem Pairwise.filter_lt_prefix {l : List α} (hl : l.Pairwise (· < ·)) (x : α) :
    l.filter (· < x) <+: l := by
  induction l with
  | nil => exact nil_prefix
  | cons y l ih =>
    rw [pairwise_cons] at hl
    rw [filter_cons]
    split_ifs with h
    · exact (prefix_cons_inj y).mpr (ih hl.2)
    · rw [filter_eq_nil_iff.mpr fun z hz ↦ ?_]
      · exact nil_prefix
      · simp only [decide_eq_true_eq] at h ⊢
        exact fun hz' ↦ h ((hl.1 z hz).trans hz')

end List

end
