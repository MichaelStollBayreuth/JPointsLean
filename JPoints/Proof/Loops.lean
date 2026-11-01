/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Std.WP

import JPoints.Proof.Containers

/-!
# Invariants of the loops that fill arrays

The invariants of the loops of the model that write the entries of an array in turn
(`JPoints.SetLoopInvariant`), that push them (`JPoints.PushLoopInvariant`), and that write the
entries of two arrays in turn (`JPoints.Set2Invariant`), each with a predicate on every entry
written, and their steps: the contracts of the loops of `init_sift`, of `row3_setup`, of `row_setup`
and of the choice of the sieve use them.

## Main definitions

* `JPoints.SetLoopInvariant`, `JPoints.PushLoopInvariant`, `JPoints.Set2Invariant`: the invariants
  of the loops that write the entries of an array in turn, that push them, and that write the
  entries of two arrays in turn.

## Main statements

* `JPoints.SetLoopInvariant.set!`, `JPoints.PushLoopInvariant.push`, `JPoints.Set2Invariant.step`:
  the steps of the loops.
* `JPoints.SetLoopInvariant.forall_lt`, `JPoints.SetLoopInvariant.of_toList`,
  `JPoints.PushLoopInvariant.size_eq`, `JPoints.PushLoopInvariant.forall_lt`,
  `JPoints.Set2Invariant.post`: the arrays after the loops.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` and `lia` calls of the proofs see only
the lemmas of core, untouched by the updates of Mathlib.
-/

@[expose] public section

namespace JPoints

/-- The invariant of a loop `for i in [0:m] do a := a.set! i x` over an array `a` of `N` entries:
`a` keeps its size, and its first `k` entries satisfy `P`. -/
def SetLoopInvariant {α : Type} [Inhabited α] (N : Nat) (P : Nat → α → Prop) (k : Nat)
    (a : Array α) : Prop :=
  a.size = N ∧ ∀ i < k, P i a[i]!

theorem setLoopInvariant_nil {α : Type} [Inhabited α] {N : Nat} (P : Nat → α → Prop) {a : Array α}
    (h : a.size = N) : SetLoopInvariant N P ([] : List Nat).length a :=
  ⟨h, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

theorem SetLoopInvariant.set! {α : Type} [Inhabited α] {N m : Nat} {P : Nat → α → Prop}
    {pref suff : List Nat} {cur : Nat} (hl : ForIn.toList [:m] = pref ++ cur :: suff) (hm : m ≤ N)
    {a : Array α} (h : SetLoopInvariant N P pref.length a) {x : α} (hx : P cur x) :
    SetLoopInvariant N P (pref ++ [cur]).length (a.set! cur x) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by rw [Array.size_set!, h.1], fun i hi ↦ ?_⟩
  rw [List.length_append, List.length_singleton] at hi
  rcases (show i < cur ∨ i = cur by lia) with hi | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h.2 i (by lia)
  · rw [Array.getElem!_set!_self _ _ _
      (by lia [h.1, Std.Legacy.Range.lt_of_toList_eq_append_cons hl])]
    exact hx

theorem SetLoopInvariant.forall_lt {α : Type} [Inhabited α] {N m : Nat} {P : Nat → α → Prop}
    {a : Array α} (h : SetLoopInvariant N P (ForIn.toList [:m]).length a) : ∀ i < m, P i a[i]! :=
  Std.Legacy.Range.forall_lt_length_toList h.2

theorem SetLoopInvariant.of_toList {α : Type} [Inhabited α] {N m : Nat} {P : Nat → α → Prop}
    {a : Array α} (h : SetLoopInvariant N P (ForIn.toList [:m]).length a) :
    SetLoopInvariant N P m a := by
  rwa [Std.Legacy.Range.length_toList_zero_start] at h

/-- The invariant of a loop `for i in [0:m] do a := a.push x` that fills the array `a` from empty:
`a` has the `k` entries pushed so far, and they satisfy `P`. -/
def PushLoopInvariant {α : Type} [Inhabited α] (P : Nat → α → Prop) (k : Nat) (a : Array α) :
    Prop :=
  a.size = k ∧ ∀ i < k, P i a[i]!

theorem pushLoopInvariant_nil {α : Type} [Inhabited α] (P : Nat → α → Prop) :
    PushLoopInvariant P ([] : List Nat).length #[] :=
  ⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩

theorem PushLoopInvariant.push {α : Type} [Inhabited α] {m : Nat} {P : Nat → α → Prop}
    {pref suff : List Nat} {cur : Nat} (hl : ForIn.toList [:m] = pref ++ cur :: suff)
    {a : Array α} (h : PushLoopInvariant P pref.length a) {x : α} (hx : P cur x) :
    PushLoopInvariant P (pref ++ [cur]).length (a.push x) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by rw [Array.size_push, h.1, List.length_append, List.length_singleton], fun i hi ↦ ?_⟩
  rw [List.length_append, List.length_singleton] at hi
  rcases (show i < cur ∨ i = cur by lia) with hi | rfl
  · rw [Array.getElem!_push_lt (by lia [h.1])]
    exact h.2 i (by lia)
  · have e : (a.push x)[i]! = x := by rw [← hc, ← h.1]; exact Array.getElem!_push_eq
    rwa [e]

theorem PushLoopInvariant.size_eq {α : Type} [Inhabited α] {m : Nat} {P : Nat → α → Prop}
    {a : Array α} (h : PushLoopInvariant P (ForIn.toList [:m]).length a) : a.size = m := by
  rw [h.1, Std.Legacy.Range.length_toList_zero_start]

theorem PushLoopInvariant.forall_lt {α : Type} [Inhabited α] {m : Nat} {P : Nat → α → Prop}
    {a : Array α} (h : PushLoopInvariant P (ForIn.toList [:m]).length a) : ∀ i < m, P i a[i]! :=
  Std.Legacy.Range.forall_lt_length_toList h.2

/-! ### A loop that sets two arrays -/

section Set2

variable {α β : Type} [Inhabited α] [Inhabited β] {o1 b1 : Array α} {o2 b2 : Array β}
  {P : Nat → α → β → Prop} {N cur : Nat} {pref suff : List Nat}

/-- The invariant of a loop over `[0:N]` that sets the entries `n` of two arrays, from `o1` and `o2`
on: their sizes kept, the property `P` of the entries below the cursor, and the entries from the
cursor on those of `o1` and `o2`. -/
def Set2Invariant (o1 : Array α) (o2 : Array β) (P : Nat → α → β → Prop) :
    Std.WP.Invariant Nat (Array α × Array β) Prop :=
  fun pref _ r ↦ r.1.size = o1.size ∧ r.2.size = o2.size ∧
    (∀ n < pref.length, P n r.1[n]! r.2[n]!) ∧
    ∀ m, pref.length ≤ m → r.1[m]! = o1[m]! ∧ r.2[m]! = o2[m]!

theorem set2Invariant_nil {l : List Nat} : Set2Invariant o1 o2 P [] l (o1, o2) :=
  ⟨rfl, rfl, nofun, fun _ _ ↦ ⟨rfl, rfl⟩⟩

theorem Set2Invariant.cur_eq (hc : ForIn.toList [:N] = pref ++ cur :: suff)
    (h : Set2Invariant o1 o2 P pref (cur :: suff) (b1, b2)) :
    b1[cur]! = o1[cur]! ∧ b2[cur]! = o2[cur]! :=
  h.2.2.2 cur (Nat.le_of_eq (Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc))

/-- The step of a loop with the invariant `JPoints.Set2Invariant` that sets the entry of the cursor
of both arrays to values with the property `P`. -/
theorem Set2Invariant.step (hc : ForIn.toList [:N] = pref ++ cur :: suff)
    (hN : N ≤ o1.size ∧ N ≤ o2.size) (h : Set2Invariant o1 o2 P pref (cur :: suff) (b1, b2))
    {v1 : α} {v2 : β} (hv : P cur v1 v2) :
    Set2Invariant o1 o2 P (pref ++ [cur]) suff (b1.set! cur v1, b2.set! cur v2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  refine ⟨by rw [Array.size_set!, h1], by rw [Array.size_set!, h2], fun n hn ↦ ?_, fun m hm ↦ ?_⟩
  · rw [List.length_append, List.length_singleton] at hn
    by_cases hnc : n = cur
    · subst hnc
      rw [Array.getElem!_set!_self _ _ _ (by lia), Array.getElem!_set!_self _ _ _ (by lia)]
      exact hv
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hnc),
        Array.getElem!_set!_ne _ _ _ _ (Ne.symm hnc)]
      exact h3 n (by lia)
  · rw [List.length_append, List.length_singleton] at hm
    rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h4 m (by lia)

theorem Set2Invariant.post {r : Array α × Array β}
    (h : Set2Invariant o1 o2 P (ForIn.toList [:N]) [] r) :
    r.1.size = o1.size ∧ r.2.size = o2.size ∧ ∀ n < N, P n r.1[n]! r.2[n]! :=
  ⟨h.1, h.2.1, Std.Legacy.Range.forall_lt_length_toList h.2.2.1⟩

end Set2

end JPoints

end
