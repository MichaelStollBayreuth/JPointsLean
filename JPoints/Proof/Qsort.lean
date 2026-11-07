/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Qsort

/-!
# The sort of the C library permutes what it sorts

`msort_with_tmp` of glibc permutes the list that it sorts (`JPoints.msortWithTmp_perm`), whatever
the comparison, a NaN that makes it inconsistent included: each step merges the two halves that it
sorts. So `qsort` keeps the size of the array (`JPoints.size_qsort`) and permutes the elements that
it sorts (`JPoints.take_toList_qsort_perm`, `JPoints.toList_qsort_perm`), which is all that the
choice of the sieving primes needs of the order of `prec` and of the candidates.

## Main statements

* `JPoints.msortWithTmp_perm`, `JPoints.take_toList_qsort_perm`, `JPoints.toList_qsort_perm`:
  the sorts permute.
-/

@[expose] public section

namespace JPoints

theorem msortWithTmp_perm {α : Type} (cmp : α → α → Int) (b : List α) :
    (msortWithTmp cmp b).Perm b := by
  fun_induction msortWithTmp cmp b with
  | case1 b h => exact .refl b
  | case2 b h n1 ih1 ih2 =>
    exact (List.merge_perm_append _).trans
      ((ih1.append ih2).trans (by rw [List.take_append_drop]))

private theorem length_msortWithTmp {α : Type} (cmp : α → α → Int) (b : List α) :
    (msortWithTmp cmp b).length = b.length :=
  (msortWithTmp_perm cmp b).length_eq

theorem size_qsort {α : Type} (cmp : α → α → Int) {base : Array α} {nmemb : Nat}
    (h : nmemb ≤ base.size) : (qsort cmp base nmemb).size = base.size := by
  simp [qsort, length_msortWithTmp]
  lia

theorem take_toList_qsort_perm {α : Type} (cmp : α → α → Int) {base : Array α} {nmemb : Nat}
    (h : nmemb ≤ base.size) :
    ((qsort cmp base nmemb).toList.take nmemb).Perm (base.toList.take nmemb) := by
  have hl := length_msortWithTmp cmp (base.toList.take nmemb)
  rw [List.length_take, Nat.min_eq_left (by simpa using h)] at hl
  simp only [qsort, Array.toList_append, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  rw [List.take_append_of_le_length (Nat.le_of_eq hl.symm),
    List.take_of_length_le (Nat.le_of_eq hl)]
  exact msortWithTmp_perm cmp _

theorem toList_qsort_perm {α : Type} (cmp : α → α → Int) (base : Array α) :
    (qsort cmp base base.size).toList.Perm base.toList := by
  have h := take_toList_qsort_perm cmp (Nat.le_refl base.size)
  rwa [List.take_of_length_le (by simp [size_qsort cmp (Nat.le_refl base.size)]),
    List.take_of_length_le (by simp)] at h

end JPoints

end
