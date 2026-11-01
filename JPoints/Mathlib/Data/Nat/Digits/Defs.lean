/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Digits.Defs

/-!
# The decimal text of natural numbers and integers determines them

Candidates for `Mathlib.Data.Nat.Digits.Defs`, next to `Nat.toDigits_length`, or for Lean core,
next to `Nat.ofDigitChars_toDigits` and `Int.repr_eq_ite`: the digits of a natural number in a base
of at most ten determine it, and the decimal text of an integer (`toString`) is the digits of its
absolute value after a `-` for a negative integer, and determines it.

## Main statements

* `Nat.toDigits_injective`: the digits of a natural number determine it.
* `Int.toList_toString`, `Int.isDigit_or_eq_of_mem_toList_toString`: the characters of the decimal
  text of an integer.
* `Int.toString_injective`: the decimal text of an integer determines it.

## Implementation notes

Mathlib has no file on the text of an integer; the statements on it are next to those on the digits
of a natural number, from which they follow.
-/

@[expose] public section

theorem Nat.toDigits_injective {b : ℕ} (hb : 1 < b) (hb' : b ≤ 10) :
    Function.Injective (Nat.toDigits b) := fun m n h ↦ by
  rw [← Nat.ofDigitChars_toDigits hb hb' (n := m), h, Nat.ofDigitChars_toDigits hb hb']

theorem Int.toList_toString (n : ℤ) :
    (toString n).toList = (if n < 0 then ['-'] else []) ++ Nat.toDigits 10 n.natAbs := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split_ifs with h h' h'
  · lia
  · simp [Nat.toList_repr, show n.toNat = n.natAbs by lia]
  · simp [Nat.toList_repr, show (-n).toNat = n.natAbs by lia]
  · lia

theorem Int.isDigit_or_eq_of_mem_toList_toString {n : ℤ} {ch : Char}
    (h : ch ∈ (toString n).toList) : ch.isDigit ∨ ch = '-' := by
  rw [Int.toList_toString, List.mem_append] at h
  refine h.elim (fun h ↦ .inr ?_) fun h ↦ .inl (Nat.isDigit_of_mem_toDigits (by lia) le_rfl h)
  split_ifs at h <;> simp_all

theorem Int.toString_injective : Function.Injective (toString : ℤ → String) := fun m n h ↦ by
  have h := congr(String.toList $h)
  rw [Int.toList_toString, Int.toList_toString] at h
  have hd (k : ℕ) : '-' ∉ Nat.toDigits 10 k := fun hk ↦
    absurd (Nat.isDigit_of_mem_toDigits (by lia) le_rfl hk) (by decide)
  split_ifs at h with hm hn hn
  · lia [Nat.toDigits_injective (by lia) le_rfl (List.cons.inj h).2]
  · exact (hd n.natAbs (by rw [← List.nil_append (Nat.toDigits 10 n.natAbs), ← h]; simp)).elim
  · exact (hd m.natAbs (by rw [← List.nil_append (Nat.toDigits 10 m.natAbs), h]; simp)).elim
  · lia [Nat.toDigits_injective (by lia) le_rfl h]

end
