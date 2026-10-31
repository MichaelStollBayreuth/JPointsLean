/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The sort of the C library

`qsort` of the C library as `j-points` calls it, on the rates of the primes (`prec`) and on the
candidates of the cost model: the merge sort `msort_with_tmp` of glibc, which halves the array, the
first half the smaller one, sorts the halves and merges them, taking the first element of the first
half while the comparison of it with the first element of the second half is at most `0`. The model
is generic in the element and in the comparison, which returns an integer as the comparison of the
C code returns an `int`.

## Main definitions

* `JPoints.msortWithTmp`: the merge sort of glibc on a list.
* `JPoints.qsort`: `qsort` on the first elements of an array.

## Implementation notes

The model assumes that `qsort` sorts by `msort_with_tmp`, as glibc 2.41 does (and glibc 2.39, as
on Ubuntu 24.04): `qsort_r` of `stdlib/qsort.c` merges into a buffer of the size of the array (on
the stack up to 1024 bytes, else from `malloc`; the elements of `j-points`, of 32 and 16 bytes, are
sorted in place, not through pointers, which glibc does only for elements above 32 bytes, with the
same merge), and falls back to a heap sort only when `malloc` fails, which the model, where no
allocation fails, leaves out. The split is that of glibc, `n / 2` elements in the first half, and
not that of `List.mergeSort`, `(n + 1) / 2`: for a comparison that is a total preorder every stable
sort gives the same order, but `j-points` compares doubles by the sign of their difference, under
which a NaN, and the difference `∞ - ∞`, compares as a tie with everything, and on such keys the
order depends on the comparisons made. The examples are the orders that glibc 2.41 gives on keys
with NaNs and infinities.
-/

@[expose] public section

namespace JPoints

/-- The list `b` sorted by `msort_with_tmp` of glibc for the comparison `cmp`: a list of at most
one element as it is; otherwise the first `n / 2` elements and the others, for the length `n`,
each sorted so, and merged by `List.merge`, which takes the first element `x` of the first half
before the first element `y` of the second when `cmp x y ≤ 0`, and the rest of one half when the
other is used up. For a comparison that is a total preorder, the stable sort by it. -/
def msortWithTmp {α : Type} (cmp : α → α → Int) (b : List α) : List α :=
  if _ : b.length ≤ 1 then b
  else
    let n1 := b.length / 2
    (msortWithTmp cmp (b.take n1)).merge (msortWithTmp cmp (b.drop n1)) fun x y ↦ cmp x y ≤ 0
termination_by b.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; lia

/-- `qsort(base, nmemb, size, cmp)` of glibc: the first `nmemb` elements of the array `base` sorted
by `JPoints.msortWithTmp` for the comparison `cmp`, the others as they are. This assumes that
`qsort` sorts by `msort_with_tmp`, as glibc 2.39 to 2.41 do unless the allocation of their buffer
fails, when they fall back to a heap sort, which the model leaves out. -/
def qsort {α : Type} (cmp : α → α → Int) (base : Array α) (nmemb : Nat) : Array α :=
  (msortWithTmp cmp (base.extract 0 nmemb).toList).toArray ++ base.extract nmemb base.size

/-! ### Examples

The orders that `qsort` of glibc 2.41 gives, from a test program that sorts the records `entry` of
`j-points` by their doubles `r` with its comparison `compare_entries`, `a` before `b` unless the
difference `a.r - b.r` is positive, `1`, `-1` or `0` by its sign; here the keys are integers and
NaNs (`none`), and a NaN key compares as a tie with every key, as its difference does. -/

-- The comparison of `compare_entries` on keys that are integers or NaNs (`none`).
private def compareSign (a b : Option Int) : Int :=
  match a, b with
  | some x, some y => if x - y > 0 then 1 else if x - y < 0 then -1 else 0
  | _, _ => 0

-- The positions of the keys `ks` in the order in which `qsort` leaves them.
private def order (ks : List (Option Int)) : List Nat :=
  ((qsort (fun a b ↦ compareSign a.1 b.1) ks.zipIdx.toArray ks.length).map (·.2)).toList

#guard order [] == [] && order [some 1] == [0] && order [none, some 3, some 1] == [0, 2, 1]

-- Ties keep the order of the array.
#guard order [some 2, some 3, some 1, some 0, some 2, some 1, some 3, some 1] ==
  [3, 2, 5, 7, 0, 4, 1, 6]

-- Keys with NaNs; on the first, the split `(n + 1) / 2` of `List.mergeSort` gives `[2, 0, 1]`.
#guard order [some 2, none, some 0] == [0, 1, 2]
#guard order [some 3, none, some 0, some 1, some 3, some 1, some 2, none, some 1, some 2] ==
  [2, 3, 5, 6, 0, 1, 4, 7, 8, 9]

-- Only the first `nmemb` elements are sorted.
#guard qsort (fun a b ↦ a - b) #[3, 1, 2, 0, -1] 3 == #[1, 2, 3, 0, -1]

end JPoints

end
