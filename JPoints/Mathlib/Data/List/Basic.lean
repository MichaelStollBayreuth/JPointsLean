/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Basic

/-!
# A filter before `List.flatMap` that changes nothing

Candidates for `Mathlib.Data.List.Basic`: filtering a list before `List.flatMap f` changes nothing
when every element `x` with `f x ≠ []` passes the filter, the counterpart of
`Finset.prod_filter_of_ne`, next to `List.flatMap_congr`; two filters, one finer than the
other, give the same `List.flatMap f` when the elements that pass the coarser one with `f x ≠ []`
pass the finer one; and the parts of two lists before the first occurrence of a separator are
equal when the lists are, next to `List.append_cons_inj_of_notMem`.

## Main statements

* `List.flatMap_filter_of_ne`: a filter before `List.flatMap` that changes nothing.
* `List.flatMap_filter_eq_flatMap_filter_of_ne`: a finer filter before `List.flatMap` that changes
  nothing.
* `List.append_cons_inj_of_notMem_left`: two lists split at the first occurrence of a separator.

## Implementation notes

The two statements on `List.flatMap` are taken from `Ratpoints/Mathlib/Data/List/Basic.lean` of
RatpointsLean (<https://github.com/MichaelStollBayreuth/RatpointsLean>).
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- Filtering the list `l` by `p` before `List.flatMap f` changes nothing when every element `x`
of `l` with `f x ≠ []` satisfies `p`; compare `Finset.prod_filter_of_ne`. -/
theorem flatMap_filter_of_ne {l : List α} {p : α → Bool} {f : α → List β}
    (h : ∀ x ∈ l, f x ≠ [] → p x) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy ↦ h y (.tail _ hy)
    by_cases hp : p x
    · simp [hp, ih]
    · have hf : f x = [] := by_contra fun hf ↦ hp (h x (.head _) hf)
      simp [hp, ih, hf]

/-- Filtering the list `l` by `p` or by a coarser `q` before `List.flatMap f` gives the same list
when every element `x` of `l` that satisfies `q` with `f x ≠ []` satisfies `p`. -/
theorem flatMap_filter_eq_flatMap_filter_of_ne {l : List α} {p q : α → Bool} {f : α → List β}
    (hpq : ∀ x ∈ l, p x → q x) (hqp : ∀ x ∈ l, q x → f x ≠ [] → p x) :
    (l.filter p).flatMap f = (l.filter q).flatMap f := by
  have : l.filter p = (l.filter q).filter p := by
    rw [filter_filter]
    exact filter_congr fun x hx ↦ by cases h : p x <;> simp [h, hpq x hx]
  rw [this, flatMap_filter_of_ne fun x hx ↦ hqp x (mem_filter.mp hx).1 (mem_filter.mp hx).2]

/-- Two lists that are each a part `l₁`, `l₂` without the separator `a`, then `a` and a rest, are
equal exactly when the parts and the rests are; compare `List.append_cons_inj_of_notMem`, where the
separator is in neither the first part nor the rest of one of them. -/
theorem append_cons_inj_of_notMem_left {a : α} {l₁ l₂ r₁ r₂ : List α} (h₁ : a ∉ l₁)
    (h₂ : a ∉ l₂) : l₁ ++ a :: r₁ = l₂ ++ a :: r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ h ▸ h' ▸ rfl⟩
  induction l₁ generalizing l₂ with
  | nil =>
    obtain _ | ⟨x, l₂⟩ := l₂
    · exact ⟨rfl, (cons.inj h).2⟩
    · exact absurd ((cons.inj h).1 ▸ mem_cons_self) h₂
  | cons x l₁ ih =>
    obtain _ | ⟨y, l₂⟩ := l₂
    · exact absurd ((cons.inj h).1 ▸ mem_cons_self) h₁
    simp only [cons_append, cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := ih (not_mem_of_not_mem_cons h₁) (not_mem_of_not_mem_cons h₂) h
    exact ⟨rfl, rfl⟩

end List

end
