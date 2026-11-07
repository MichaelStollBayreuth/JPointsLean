/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Std.Internal.ForIn.Lemmas

/-!
# Lemmas on arrays, lists, ranges and numbers for the contracts

Lemmas that Lean core lacks, under their names in the namespaces of core, on arrays (the entries
after `Array.set!`, `Array.push` and `Array.replicate`, an array determined by its entries read by
`getElem!`, the entries after a loop of `Array.set!`, flags set twice, the first entries of the list
of an array, the list of an array read by `List.getD`), natural numbers (a step of Horner's rule,
the residue by one conditional subtraction, the residue that completes a sum to a multiple, the next
position in a ring, the remainder and the quotient by a reciprocal, the multiples rounded up, the
positions of the entries of tables of blocks, the values of a loop with a step, the binary logarithm
of `2 ^ n k` beside core's `Nat.log2_two_mul`), lists (a list read by its indices, tests that agree
on a list, two filters of a list in order, the numbers below a bound in a residue class, the array
of a list of values), ranges (the list of a loop over `[a:m]` and its cursor, the lists of the loops
over `[0:n:2]` and `[1:m:2]`), integers (residues, the residue of `n i + t`, the halving shift and
the odd parts, the Euclidean remainder by its bounds, the quotient rounded up, the list of a range
from `1`, the step of a loop that lowers a degree, the remainder of C, which truncates, against the
Euclidean one, the test `!=` of natural numbers as integers), the invariants of the loops with an
early return, strings (the concatenation of the texts of a list) and `Except`. The lemmas on 64-bit
words are in `JPoints.Proof.Bits`.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` calls of the proofs see only the lemmas
of core, untouched by the updates of Mathlib.

## References

Adapted from `Ratpoints/Proof/Containers.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

universe u v

/-! ### Arrays -/

namespace Array

theorem getElem!_set! {α : Type u} [Inhabited α] {xs : Array α} {i j : Nat} {x : α}
    (hj : j < xs.size) : (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  grind

theorem getElem!_mem {α : Type u} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]! ∈ xs :=
  (getElem!_pos xs i h).symm ▸ getElem_mem h

theorem getElem!_push_lt {α : Type u} [Inhabited α] {xs : Array α} {x : α} {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  grind

theorem getElem!_push_eq {α : Type u} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  simp

theorem getElem!_replicate_default {α : Type u} [Inhabited α] (n K : Nat) :
    (Array.replicate n (default : α))[K]! = default := by
  by_cases h : K < n
  · simp [h]
  · exact getElem!_neg _ K (by simpa using h)

/-- An array is determined by its size and its entries read by `getElem!`. -/
theorem ext_getElem! {α : Type u} [Inhabited α] {xs ys : Array α} (hs : xs.size = ys.size)
    (h : ∀ i < xs.size, xs[i]! = ys[i]!) : xs = ys :=
  ext hs fun i hi hi' ↦ by rw [← getElem!_pos xs i hi, ← getElem!_pos ys i hi', h i hi]

theorem size_foldl_range_set! {α : Type u} (x : α) (n : Nat) (xs : Array α) :
    ((List.range n).foldl (fun a k ↦ a.set! k x) xs).size = xs.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, size_set!, ih]

/-- Setting the entries below `n` to `x`, one after the other, sets those of them within the
array. -/
theorem getElem!_foldl_range_set! {α : Type u} [Inhabited α] (x : α) (n : Nat) (xs : Array α)
    (i : Nat) :
    ((List.range n).foldl (fun a k ↦ a.set! k x) xs)[i]! =
      if i < n ∧ i < xs.size then x else xs[i]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hi : n = i
    · subst hi
      by_cases hs : n < xs.size
      · rw [getElem!_set!_self _ _ _ (by rw [size_foldl_range_set!]; exact hs)]
        simp [hs]
      · rw [set!_eq_setIfInBounds, setIfInBounds_eq_of_size_le (by
          rw [size_foldl_range_set!]; exact Nat.le_of_not_lt hs), ih]
        simp [hs]
    · rw [getElem!_set!_ne _ _ _ _ hi, ih]
      grind

/-- Setting an entry twice keeps the second value. -/
theorem set!_set! {α : Type u} (xs : Array α) (i : Nat) (a b : α) :
    (xs.set! i a).set! i b = xs.set! i b := by
  simp only [set!_eq_setIfInBounds, setIfInBounds_setIfInBounds]

/-- The entry set to the default value is the default value, also beyond the array. -/
theorem getElem!_set!_default {α : Type u} [Inhabited α] (xs : Array α) (i : Nat) :
    (xs.set! i default)[i]! = default := by
  by_cases h : i < xs.size
  · exact Array.getElem!_set!_self _ _ _ h
  · rw [getElem!_neg _ _ (by rw [Array.size_set!]; exact h)]

/-- A flag set to `false` is not `true`, also beyond the array. -/
theorem getElem!_set!_false_ne_true (xs : Array Bool) (i : Nat) : (xs.set! i false)[i]! ≠ true :=
  fun h ↦ Bool.false_ne_true ((getElem!_set!_default xs i).symm.trans h)

/-- A flag set to `false` and then to `true` is set to a `b` that is `true`. -/
theorem set!_set!_eq_set!_of_eq_true {xs : Array Bool} {i : Nat} {b : Bool} (h : b = true) :
    (xs.set! i false).set! i true = xs.set! i b := by
  rw [set!_set!, h]

/-- A flag set to `false` is set to a `b` that is not `true`. -/
theorem set!_eq_set!_of_not_eq_true {xs : Array Bool} {i : Nat} {b : Bool} (h : ¬b = true) :
    xs.set! i false = xs.set! i b := by
  rw [Bool.eq_false_iff.2 h]

theorem getElem!_take_toList {α : Type u} [Inhabited α] {xs : Array α} {m j : Nat} (hj : j < m)
    (hm : m ≤ xs.size) : (xs.toList.take m)[j]! = xs[j]! := by
  rw [getElem!_pos _ j (by simp; lia), List.getElem_take, getElem_toList,
    getElem!_pos xs j (by lia)]

theorem getElem_take_toList {α : Type u} [Inhabited α] {xs : Array α} {m j : Nat}
    (hj : j < (xs.toList.take m).length) : (xs.toList.take m)[j] = xs[j]! := by
  simp only [List.length_take, length_toList, Nat.lt_min] at hj
  rw [List.getElem_take, getElem_toList, getElem!_pos xs j hj.2]

theorem mem_take_toList_of_lt {α : Type u} [Inhabited α] {xs : Array α} {m j : Nat} (hj : j < m)
    (hm : m ≤ xs.size) : xs[j]! ∈ xs.toList.take m := by
  rw [← getElem!_take_toList hj hm, getElem!_pos _ j (by simp; lia)]
  exact List.getElem_mem _

theorem exists_eq_of_mem_take_toList {α : Type u} [Inhabited α] {xs : Array α} {m : Nat}
    {p : α} (hp : p ∈ xs.toList.take m) : ∃ j < m, j < xs.size ∧ p = xs[j]! := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  simp only [List.length_take, length_toList, Nat.lt_min] at hj
  exact ⟨j, hj.1, hj.2, by rw [List.getElem_take, getElem_toList, getElem!_pos xs j hj.2]⟩

theorem getD_toList_eq_getElem! (xs : Array Int) (i : Nat) : xs.toList.getD i 0 = xs[i]! := by
  rw [← getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

end Array

/-! ### Natural numbers -/

namespace Nat

/-- One step of Horner's rule with an argument at most `p` and a coefficient below `p` multiplies a
bound on the accumulator by `p`. -/
theorem mul_add_lt_mul_of_lt {s a c P p : Nat} (hs : s < P) (ha : a ≤ p) (hc : c < p) :
    s * a + c < P * p :=
  calc s * a + c < s * p + p := Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left s ha) hc
    _ = (s + 1) * p := (Nat.succ_mul s p).symm
    _ ≤ P * p := Nat.mul_le_mul_right p hs

/-- A residue `a < 2 q` modulo `q` by one conditional subtraction. -/
theorem mod_eq_ite_of_lt_two_mul {a q : Nat} (h : a < 2 * q) :
    a % q = if q ≤ a then a - q else a := by
  split
  · rw [Nat.mod_eq_sub_mod ‹_›, Nat.mod_eq_of_lt (by lia)]
  · exact Nat.mod_eq_of_lt (by lia)

/-- The position after `a ≤ n` in a ring of the positions `0, …, n`, by a test for the last. -/
theorem ite_eq_add_one_mod_add_one {a n : Nat} (h : a ≤ n) :
    (if a = n then 0 else a + 1) = (a + 1) % (n + 1) := by
  split
  · subst a
    simp
  · exact (Nat.mod_eq_of_lt (by lia)).symm

/-- For `m p = N + δ` and `u δ < N`, the product `m u` is `L + N ⌊u / p⌋` for some `L < N` with
`L p = u δ + N (u mod p)`: the product of `u` with a reciprocal `m` of `p` scaled by `N`, rounded
up when `δ ≥ 0` is small. -/
theorem exists_mul_eq_add_mul_div {u p m N δ : Nat} (hp : 0 < p) (hm : m * p = N + δ)
    (hu : u * δ < N) : ∃ L < N, m * u = L + N * (u / p) ∧ L * p = u * δ + N * (u % p) := by
  have hs := Nat.mod_lt u hp
  have hu' := Nat.div_add_mod u p
  generalize u / p = k, u % p = s at hs hu' ⊢
  have h1 : m * u = (k * δ + m * s) + N * k := by grind
  have h2 : (k * δ + m * s) * p = u * δ + N * s := by grind
  have h3 : N * (s + 1) ≤ N * p := Nat.mul_le_mul_left N hs
  exact ⟨k * δ + m * s, Nat.lt_of_mul_lt_mul_right (a := p) (by grind), h1, h2⟩

/-- The quotient by a reciprocal: for `m p = N + δ` and `u δ < N`, the high part of the product of
`u` with `m` is `⌊u / p⌋`. -/
theorem mul_div_eq_div_of_mul_eq_add {u p m N δ : Nat} (hp : 0 < p) (hm : m * p = N + δ)
    (hu : u * δ < N) : m * u / N = u / p := by
  obtain ⟨L, hL, h1, -⟩ := exists_mul_eq_add_mul_div hp hm hu
  rw [h1, Nat.add_mul_div_left _ _ (by lia), Nat.div_eq_of_lt hL, Nat.zero_add]

/-- The multiple `m ⌈R / m⌉ = m ((R + m - 1) / m)` of `m > 0` is at least `R`. -/
theorem le_mul_add_sub_one_div (R : Nat) {m : Nat} (hm : 0 < m) : R ≤ m * ((R + m - 1) / m) :=
  (Nat.le_mul_iff_le_right hm).mpr (Nat.le_refl _)

/-- The multiple `m ⌈R / m⌉ = m ((R + m - 1) / m)` of `m > 0` is below `R + m`. -/
theorem mul_add_sub_one_div_lt (R : Nat) {m : Nat} (hm : 0 < m) : m * ((R + m - 1) / m) < R + m :=
  Nat.lt_of_le_of_lt (Nat.mul_div_le _ m) (by lia)

/-- The residue `k < m` with `x + k ≡ 0 (mod m)` is `(m - x mod m) mod m`. -/
theorem sub_mod_mod_eq_of_add_mod_eq_zero {m x k : Nat} (hk : k < m) (h : (x + k) % m = 0) :
    (m - x % m) % m = k := by
  have hx := Nat.mod_lt x (by lia : 0 < m)
  rw [Nat.add_mod, Nat.mod_eq_of_lt hk] at h
  rcases Nat.lt_or_ge (x % m + k) m with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [show x % m = 0 by lia, Nat.sub_zero, Nat.mod_self]
    lia
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by lia)] at h
    rw [Nat.mod_eq_of_lt (by lia)]
    lia

/-- `N + (m - r)` is a multiple of `m` exactly when `N` is `r` modulo `m`, for `r < m`. -/
theorem add_sub_mod_eq_zero_iff {N m r : Nat} (hr : r < m) :
    (N + (m - r)) % m = 0 ↔ N % m = r := by
  have hs := Nat.mod_lt N (by lia : 0 < m)
  have h1 := Nat.div_add_mod N m
  rw [show N + (m - r) = N % m + (m - r) + m * (N / m) by lia, Nat.add_mul_mod_self_left]
  rcases Nat.lt_trichotomy (N % m) r with h | h | h
  · rw [Nat.mod_eq_of_lt (by lia)]
    lia
  · rw [h, Nat.add_sub_cancel' (Nat.le_of_lt hr), Nat.mod_self]
    exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  · rw [show N % m + (m - r) = N % m - r + m by lia, Nat.add_mod_right, Nat.mod_eq_of_lt (by lia)]
    lia

/-- The entry `b < M` of block `a` of blocks of `M` entries lies before block `a' > a`. -/
theorem mul_add_lt_mul_add_of_lt {M a b a' b' : Nat} (hb : b < M) (h : a < a') :
    a * M + b < a' * M + b' :=
  Nat.lt_of_lt_of_le (mul_add_lt_mul_of_lt h (Nat.le_refl M) hb) (Nat.le_add_right _ _)

/-- The position `a M + b` of the entry `b < M` of block `a` of blocks of `M` entries determines the
block and the entry. -/
theorem eq_and_eq_of_mul_add_eq_mul_add {M a b a' b' : Nat} (hb : b < M) (hb' : b' < M)
    (h : a * M + b = a' * M + b') : a = a' ∧ b = b' := by
  rcases Nat.lt_trichotomy a a' with h' | rfl | h'
  · exact absurd h (Nat.ne_of_lt (mul_add_lt_mul_add_of_lt hb h'))
  · exact ⟨rfl, Nat.add_left_cancel h⟩
  · exact absurd h (Nat.ne_of_gt (mul_add_lt_mul_add_of_lt hb' h'))

/-- The position `(a M + b) M + c` of the entry `(a, b, c)` of a table of width `M` in its two inner
indices determines the entry. -/
theorem mul_add_mul_add_inj {M a b c a' b' c' : Nat} (hb : b < M) (hb' : b' < M) (hc : c < M)
    (hc' : c' < M) (h : (a * M + b) * M + c = (a' * M + b') * M + c') :
    a = a' ∧ b = b' ∧ c = c' :=
  have h1 := eq_and_eq_of_mul_add_eq_mul_add hc hc' h
  have h2 := eq_and_eq_of_mul_add_eq_mul_add hb hb' h1.1
  ⟨h2.1, h2.2, h1.2⟩

/-- The multiple `(⌊n / p⌋ + 1) p` of `p > 0` lies above `n`. -/
theorem lt_div_add_one_mul (n : Nat) {p : Nat} (hp : 0 < p) : n < (n / p + 1) * p := by
  rw [Nat.add_one_mul]
  exact Nat.lt_div_mul_add hp

/-- The multiple `(⌊n / p⌋ + 1) p` of `p` is at most `n + p`. -/
theorem div_add_one_mul_le (n p : Nat) : (n / p + 1) * p ≤ n + p := by
  rw [Nat.add_one_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self n p) p

/-- The entry `(a, b, c)` of an array of `A × B × C` entries, at `(a B + b) C + c`, lies within the
array. -/
theorem mul_add_mul_add_lt {A B C a b c : Nat} (ha : a < A) (hb : b < B) (hc : c < C) :
    (a * B + b) * C + c < A * B * C := by
  have h1 : a * B + b + 1 ≤ A * B := by
    have := Nat.mul_le_mul_right B (show a + 1 ≤ A by lia)
    rw [Nat.add_mul, Nat.one_mul] at this
    lia
  have := Nat.mul_le_mul_right C h1
  rw [Nat.add_mul (a * B + b) 1, Nat.one_mul] at this
  lia

/-- The entry `w < C` of block `x` of an array of blocks of `C` entries, at `x C + w`, lies before
or after block `y ≠ x`. -/
theorem mul_add_lt_or_le_of_ne {C x y w : Nat} (hxy : x ≠ y) (hw : w < C) :
    x * C + w < y * C ∨ (y + 1) * C ≤ x * C + w := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact .inl (Nat.lt_of_lt_of_le (by rw [Nat.add_mul, Nat.one_mul]; lia)
      (Nat.mul_le_mul_right C (show x + 1 ≤ y by lia)))
  · exact .inr (Nat.le_trans (Nat.mul_le_mul_right C (show y + 1 ≤ x by lia))
      (Nat.le_add_right _ _))

/-- The entry `w < C` of the block `(a, b)`, `b < B`, of an array of blocks of `C` entries, block
`(a, b)` at `(a B + b) C`, lies before or after the block `(a', b') ≠ (a, b)`, `b' < B`. -/
theorem mul_add_mul_add_lt_or_le_of_ne {B C a b a' b' w : Nat} (hb : b < B) (hb' : b' < B)
    (hne : ¬(a = a' ∧ b = b')) (hw : w < C) :
    (a * B + b) * C + w < (a' * B + b') * C ∨ (a' * B + b') * C + C ≤ (a * B + b) * C + w := by
  rw [← Nat.add_one_mul]
  exact mul_add_lt_or_le_of_ne (fun h ↦ hne (eq_and_eq_of_mul_add_eq_mul_add hb hb' h)) hw

/-- The values `i₀ + t p`, `t < ⌈(kp - i₀) / p⌉`, of a loop `for(i = i₀; i < kp; i += p)` are the
`i < kp` with `i ≡ i₀ (mod p)`, for `i₀ < p ≤ kp`. -/
theorem exists_lt_eq_add_mul_iff {i0 p kp : Nat} (hi0 : i0 < p) (hkp : p ≤ kp) (i : Nat) :
    (∃ t < (kp - i0 + p - 1) / p, i = i0 + t * p) ↔ i < kp ∧ i % p = i0 := by
  have hp : 0 < p := by lia
  refine ⟨fun ⟨t, ht, hi⟩ ↦ ?_, fun ⟨hi, hm⟩ ↦ ⟨i / p, ?_, ?_⟩⟩
  · have := (Nat.le_div_iff_mul_le hp).mp ht
    rw [Nat.add_one_mul] at this
    subst hi
    exact ⟨by lia, by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi0]⟩
  · refine (Nat.le_div_iff_mul_le hp).mpr ?_
    rw [Nat.add_one_mul, Nat.mul_comm]
    lia [Nat.mod_add_div i p]
  · have := Nat.mod_add_div i p
    rw [Nat.mul_comm] at this
    lia

/-- `Nat.log2_two_mul` for a power of `2`. -/
theorem log2_two_pow_mul {k : Nat} (hk : k ≠ 0) (n : Nat) : (2 ^ n * k).log2 = n + k.log2 := by
  rw [Nat.log2_eq_iff (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)) hk),
    Nat.add_assoc, Nat.pow_add, Nat.pow_add]
  exact ⟨Nat.mul_le_mul_left _ (Nat.log2_self_le hk),
    Nat.mul_lt_mul_of_pos_left Nat.lt_log2_self (Nat.two_pow_pos n)⟩

end Nat

/-! ### Lists -/

namespace List

/-- The entries of a list read by their indices are the list. -/
theorem map_range_length_getElem! {α : Type u} [Inhabited α] (l : List α) :
    (range l.length).map (fun i ↦ l[i]!) = l := by
  refine ext_getElem (by simp) fun i h _ ↦ ?_
  rw [getElem_map, getElem_range, getElem!_pos l i (by simpa using h)]

theorem all_congr_left {α : Type u} {l : List α} {P Q : α → Bool} (h : ∀ a ∈ l, P a = Q a) :
    l.all P = l.all Q := by
  grind

/-- The elements of a list that pass `p` followed by those that pass `q` are those that pass one of
the two, for a list whose elements are pairwise in an asymmetric relation `R` that holds from every
element that passes `p` to every element that passes `q`: none passes both, and those that pass `p`
come first. -/
theorem filter_append_filter_of_pairwise {α : Type u} {R : α → α → Prop} [Std.Asymm R]
    {l : List α} (hl : l.Pairwise R) {p q : α → Bool}
    (h : ∀ a ∈ l, ∀ b ∈ l, p a = true → q b = true → R a b) :
    l.filter p ++ l.filter q = l.filter fun a ↦ p a || q a := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [pairwise_cons] at hl
    have ih := ih hl.2 fun a ha b hb ↦ h a (.tail _ ha) b (.tail _ hb)
    by_cases hp : p x <;> by_cases hq : q x
    · have hxx := h x mem_cons_self x mem_cons_self hp hq
      exact (Std.Asymm.asymm _ _ hxx hxx).elim
    · simp [hp, hq, ih]
    · have ht : t.filter p = [] := filter_eq_nil_iff.mpr fun a ha hpa ↦ Std.Asymm.asymm _ _
        (hl.1 a ha) (h a (.tail _ ha) x mem_cons_self hpa hq)
      simp [hp, hq, ← ih, ht]
    · simp [hp, hq, ih]

theorem getElem!_toArray_map_range {α : Type u} [Inhabited α] {f : Nat → α} {n i : Nat}
    (hi : i < n) : ((List.range n).map f).toArray[i]! = f i := by
  simp [hi]

/-- The numbers below `N` that are `r` modulo `m`, for `r < m`: `r, r + m, r + 2 m, …`, of which
there are `⌈(N - r) / m⌉`. -/
theorem filter_range_mod_eq {m r : Nat} (hr : r < m) (N : Nat) :
    (List.range N).filter (fun i ↦ i % m == r) =
      (List.range ((N + (m - 1 - r)) / m)).map fun j ↦ r + m * j := by
  induction N with
  | zero =>
    rw [List.range_zero, List.filter_nil, Nat.zero_add, Nat.div_eq_of_lt (by lia), List.range_zero,
      List.map_nil]
  | succ N ih =>
    have e : N + 1 + (m - 1 - r) = N + (m - 1 - r) + 1 := by lia
    have e' : N + (m - 1 - r) + 1 = N + (m - r) := by lia
    rw [List.range_succ, List.filter_append, ih, e]
    by_cases hN : N % m = r
    · rw [Nat.succ_div_of_mod_eq_zero (by rw [e']; exact (Nat.add_sub_mod_eq_zero_iff hr).mpr hN),
        List.range_succ, List.map_append]
      simp only [hN, beq_self_eq_true, List.filter_cons_of_pos, List.filter_nil, List.map_cons,
        List.map_nil]
      have h1 := Nat.div_add_mod N m
      rw [show N + (m - 1 - r) = m - 1 + m * (N / m) by lia, Nat.add_mul_div_left _ _ (by lia),
        Nat.div_eq_of_lt (by lia), Nat.zero_add]
      congr 2
      lia
    · rw [Nat.succ_div_of_mod_ne_zero (by rw [e']; exact mt (Nat.add_sub_mod_eq_zero_iff hr).mp hN)]
      simp [hN]

end List

/-! ### Ranges -/

namespace Std.Legacy.Range

theorem length_toList (a b : Nat) : (ForIn.toList [a:b]).length = b - a := by
  simp [size]

theorem length_toList_zero_start (n : Nat) : (ForIn.toList [:n]).length = n := by
  simp [size]

/-- A property of the numbers below the length of the list of a loop over `[0:N]` holds below `N`:
the form in which the postconditions of the loops over `[0:N]` read their invariants. -/
theorem forall_lt_length_toList {N : Nat} {P : Nat → Prop}
    (h : ∀ m < (ForIn.toList [:N]).length, P m) : ∀ m < N, P m :=
  fun m hm ↦ h m (by rwa [length_toList_zero_start])

theorem toList_eq_range' (m n : Nat) : ForIn.toList [m:n] = List.range' m (n - m) := by
  simp [size]

/-- `ForIn.toList [:n]`, the list of the loop over `[0:n]`, is `List.range n`. -/
theorem toList_eq_range (n : Nat) : ForIn.toList [:n] = List.range n := by
  simp [List.range_eq_range']

/-- The form of `List.eq_of_range'_eq_append_cons` for the list `ForIn.toList [a:m]` of a loop over
`[a:m]`, in which the verification conditions state the cursor: the cursor is `a` plus the length of
the list before it. -/
theorem add_length_eq_of_toList_eq_append_cons {a m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:m] = pref ++ cur :: suff) : a + pref.length = cur := by
  simp only [Std.Internal.ForIn.toList_range, List.range'_eq_append_iff] at h
  obtain ⟨k, -, rfl, h⟩ := h
  simpa using (List.range'_eq_cons_iff.mp h.symm).1

/-- The form of `List.eq_of_range'_eq_append_cons` for the list `ForIn.toList [0:m]` of a loop over
`[0:m]`, in which the verification conditions state the cursor: the cursor is the length of the list
before it. -/
theorem length_eq_of_toList_eq_append_cons {m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [0:m] = pref ++ cur :: suff) : pref.length = cur :=
  (Nat.zero_add _).symm.trans (add_length_eq_of_toList_eq_append_cons h)

/-- The form of `List.mem_of_range'_eq_append_cons` for the list `ForIn.toList [a:m]` of a loop over
`[a:m]`: the cursor is below `m`. -/
theorem lt_of_toList_eq_append_cons {a m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:m] = pref ++ cur :: suff) : cur < m := by
  have : cur ∈ ForIn.toList [a:m] := by simp [h]
  simp only [Std.Internal.ForIn.toList_range, List.mem_range'_1, size] at this
  lia

/-- A number in `[a, b)` is in the list of a loop over `[a:b]`. -/
theorem mem_toList_of_le_of_lt {a b t : Nat} (ha : a ≤ t) (hb : t < b) :
    t ∈ ForIn.toList [a:b] := by
  simp only [Std.Internal.ForIn.toList_range, List.mem_range', size]
  exact ⟨t - a, by lia, by lia⟩

/-- A number below `m` is in the list of a loop over `[0:m]`. -/
theorem mem_toList_of_lt {x m : Nat} (h : x < m) : x ∈ ForIn.toList [0:m] :=
  mem_toList_of_le_of_lt (Nat.zero_le x) h

/-- An odd number below `m` is in the list of a loop over `[1:m:2]`. -/
theorem mem_toList_one_two {m t : Nat} (ht : t < m) (h : t % 2 = 1) :
    t ∈ ForIn.toList [1:m:2] := by
  simp only [Std.Internal.ForIn.toList_range, List.mem_range', size]
  exact ⟨t / 2, by lia, by lia⟩

/-- The list of a loop over `[0:n:2]` is that of the even numbers below `n`. -/
theorem toList_range_two (n : Nat) :
    ForIn.toList [:n:2] = (List.range n).filter (· % 2 == 0) := by
  rw [List.filter_range_mod_eq Nat.two_pos, Std.Internal.ForIn.toList_range]
  exact List.ext_getElem (by simp [Std.Legacy.Range.size]) fun i _ _ ↦ by simp

end Std.Legacy.Range

/-! ### Integers -/

namespace Int

theorem toNat_emod_lt (a : Int) {p : Nat} (hp : 0 < p) : (a % (p : Int)).toNat < p :=
  (toNat_lt' hp).mpr (emod_lt_of_pos a (by lia))

theorem shiftRight_one_eq_ediv_two (x : Int) : x >>> 1 = x / 2 := by
  simp [shiftRight_eq_div_pow]

/-- An odd part `y` of `M >>> 1`, `2 ^ t y = M >>> 1`, for an even `M` is one of `M`. -/
theorem two_pow_succ_mul_eq_of_shiftRight {M y : Int} (he : M % 2 = 0) {t : Nat}
    (ht : (2 : Int) ^ t * y = M >>> 1) : (2 : Int) ^ (t + 1) * y = M := by
  rw [shiftRight_one_eq_ediv_two] at ht
  rw [Int.pow_succ, Int.mul_comm _ 2, Int.mul_assoc, ht]
  lia

/-- A remainder `d - p q` of `d` modulo `p` in `[0, p)` is the Euclidean one. -/
theorem eq_emod_of_eq_sub_mul {d p q r : Int} (hr : r = d - p * q) (h0 : 0 ≤ r) (h1 : r < p) :
    r = d % p := by
  rw [← emod_eq_of_lt h0 h1, hr, sub_mul_emod_self_left]

/-- The quotient rounded up of `mpz_cdiv_q`, `-(-t / d)` for `d > 0`, times `d` is at least `t`. -/
theorem le_mul_neg_ediv_neg (t : Int) {d : Int} (hd : 0 < d) : t ≤ d * -(-t / d) := by
  rw [Int.mul_neg]
  exact Int.le_neg_of_le_neg (mul_ediv_self_le (Int.ne_of_gt hd))

/-- The list of the integers from `1` to `n` is that of the natural numbers from `1` to `n`. -/
theorem toList_rcc_one_natCast (n : Nat) :
    ((1 : Int)...=(n : Int)).toList = (List.range' 1 n).map fun i : Nat ↦ (i : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_1_concat, List.map_append, ← ih, natCast_add_one,
      toList_rcc_succ_right_eq_append (by lia)]
    simp [Int.add_comm]

/-- A property of the natural numbers above `d` that also holds at `d` holds above `d - 1`: the
step of a loop that lowers a degree `d` past a leading zero. -/
theorem forall_sub_one_lt_of_forall_lt {P : Nat → Prop} {d : Int} (h : ∀ n : Nat, d < n → P n)
    (hd : P d.toNat) (n : Nat) (hn : d - 1 < n) : P n := by
  rcases (show n = d.toNat ∨ d < n by lia) with rfl | hn'
  · exact hd
  · exact h n hn'

/-- The residue modulo `n` of `n i + t` for a natural number `t < n`. -/
theorem toNat_mul_add_emod_of_lt {n i : Int} {t : Nat} (ht : (t : Int) < n) :
    ((n * i + t) % n).toNat = t := by
  rw [Int.add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by lia) ht]
  simp

@[simp]
theorem toNat_natCast_emod (a b : Nat) : ((a : Int) % (b : Int)).toNat = a % b :=
  rfl

theorem toNat_emod_add_mod (a : Int) (x : Nat) {p : Nat} (hp : 0 < p) :
    ((a % (p : Int)).toNat + x) % p = ((a + x) % (p : Int)).toNat := by
  rw [← toNat_natCast (((a % (p : Int)).toNat + x) % p)]
  congr 1
  push_cast
  rw [toNat_of_nonneg (emod_nonneg a (by lia)), emod_add_emod]

/-- C's remainder `a.tmod p`, which truncates, plus `p` if it is negative, is the Euclidean
remainder `a % p`, for `p > 0`. -/
theorem ite_tmod_lt_zero_eq_emod (a : Int) {p : Int} (hp : 0 < p) :
    (if a.tmod p < 0 then a.tmod p + p else a.tmod p) = a % p := by
  grind [tmod_eq_emod, emod_nonneg a (Int.ne_of_gt hp), emod_lt_of_pos a hp, emod_emod_of_dvd]

/-- C's remainder `b.tmod p`, which truncates, plus `p` when it is negative is the Euclidean
remainder `b % p`. -/
theorem tmod_add_natCast_eq_emod {b : Int} {p : Nat} (h : b.tmod p < 0) :
    b.tmod p + p = b % p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · simpa [h] using ite_tmod_lt_zero_eq_emod b (p := p) (by lia)

/-- C's remainder `b.tmod p`, which truncates, is the Euclidean remainder `b % p` when it is not
negative. -/
theorem tmod_natCast_eq_emod {b : Int} {p : Nat} (h : ¬b.tmod p < 0) :
    b.tmod p = b % p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · simpa [h] using ite_tmod_lt_zero_eq_emod b (p := p) (by lia)

theorem toNat_emod_mul_emod (a : Int) {p : Nat} (b : Nat) (hp : 0 < p) :
    (a % p * b % p).toNat = (a % p).toNat * b % p := by
  have h := emod_nonneg a (b := p) (by lia)
  apply ofNat_inj.mp
  rw [toNat_of_nonneg (emod_nonneg _ (by lia))]
  push_cast
  rw [toNat_of_nonneg h]

theorem natCast_bne_natCast (a b : Nat) : ((a : Int) != b) = (a != b) :=
  Bool.eq_iff_iff.2 (by simp [Int.ofNat_inj])

end Int

/-! ### Options -/

/-- The value of the invariant of a loop with an early return at a cursor followed by more
elements, `o.elim P fun r ↦ x :: l = [] ∧ Q r`, is that of a loop that has not returned. -/
theorem Option.eq_none_and_of_elim_cons {α : Type u} {β : Type v} {o : Option α} {P : Prop}
    {Q : α → Prop} {x : β} {l : List β} (h : o.elim P fun r ↦ x :: l = [] ∧ Q r) :
    o = none ∧ P := by
  cases o with
  | none => exact ⟨rfl, h⟩
  | some r => exact absurd h.1 (List.cons_ne_nil _ _)

/-! ### Strings -/

/-- The concatenation of the values of `f` on a list determines the list, for values that are not
empty and of which none followed by a text is another followed by a different one. -/
theorem String.join_map_injective {α : Type u} {f : α → String} (hne : ∀ a, f a ≠ "")
    (h : ∀ a b s t, f a ++ s = f b ++ t → a = b ∧ s = t) :
    Function.Injective fun L : List α ↦ String.join (L.map f) := by
  intro L₁ L₂ hL
  induction L₁ generalizing L₂ with
  | nil =>
    obtain _ | ⟨b, L₂⟩ := L₂
    · rfl
    · have : f b ++ String.join (L₂.map f) = "" := by simpa [String.join_cons] using hL.symm
      exact absurd (String.append_eq_empty_iff.mp this).1 (hne b)
  | cons a L₁ ih =>
    obtain _ | ⟨b, L₂⟩ := L₂
    · have : f a ++ String.join (L₁.map f) = "" := by simpa [String.join_cons] using hL
      exact absurd (String.append_eq_empty_iff.mp this).1 (hne a)
    simp only [List.map_cons, String.join_cons] at hL
    obtain ⟨rfl, hJ⟩ := h a b _ _ hL
    rw [ih hJ]

/-! ### Exceptions -/

/-- A choice between a failure and a success succeeds exactly when its condition fails. -/
theorem Except.ite_error_eq_ok_iff {ε α : Type u} {c : Prop} [Decidable c] {e : ε} {a b : α} :
    (if c then .error e else .ok a) = (.ok b : Except ε α) ↔ ¬c ∧ a = b := by
  by_cases hc : c <;> simp [hc]

end
