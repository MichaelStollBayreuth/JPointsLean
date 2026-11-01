/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Associated

/-!
# The product of a list of distinct primes

A candidate for `Mathlib.Algebra.BigOperators.Associated`: the product of a list without duplicates
of primes that divide `n` divides `n` (`List.Nodup.prod_primes_dvd`), the form for lists of
`Finset.prod_primes_dvd`, in a monoid with zero whose only unit is `1`.
-/

@[expose] public section

namespace List

variable {M₀ : Type*} [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsingleton M₀ˣ]

/-- The product of a list without duplicates of primes that divide `n` divides `n`:
`Finset.prod_primes_dvd` for the elements of the list. -/
theorem Nodup.prod_primes_dvd {l : List M₀} (hl : l.Nodup) (n : M₀) (h : ∀ a ∈ l, Prime a)
    (div : ∀ a ∈ l, a ∣ n) : l.prod ∣ n := by
  classical
  simpa [List.prod_toFinset _ hl] using Finset.prod_primes_dvd (s := l.toFinset) n
    (fun a ha ↦ h a (List.mem_toFinset.1 ha)) fun a ha ↦ div a (List.mem_toFinset.1 ha)

end List

end
