/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Check
public import JPoints.Proof.Globals
public import Std.WP

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.DoublePoints
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Std.Tactic.Do

/-!
# The contracts of the double points and of the step of the rows

What `find_double_points` prints (`JPoints.findDoublePoints_spec`): the points over the triples of
the double points (`JPoints.doubleTriples`), which its sieve of the pairs `(a, b)` keeps, only the
first under `-1`; and what `row_step` returns (`JPoints.rowStep_spec`): a step of at least `1` and
at most `H + 1`, which the test of the rows reads (`JPoints.rowKeeps`), the product of the sieving
primes that divide `a` and modulo which the curve has no points at infinity
(`JPoints.rowStepPrimes`) or `H + 1` past `H` (`JPoints.run_rowStep`).

## Main definitions

* `JPoints.rowStepPrimes`, `JPoints.rowStepProd`: the primes of the step of the rows, and the
  product of those among some indices.
* `JPoints.RowStepInvariant`: the invariant of the loop of `row_step`.

## Main statements

* `JPoints.rowStep_spec`, `JPoints.run_rowStep`: the step of the rows.
* `JPoints.findDoublePoints_spec`: the double points.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. The contract of
`row_step` is proved by `vcgen` with a named invariant, its loop with an early return; that of
`JPoints.findDoublePoints` is on its call with the globals of the sieve by bands, whose set-up
(`JPoints.IsSieveSetup`) it assumes; it is `JPoints.findDoublePoints_spec_of_doubleSetup` for what
the search of the double points reads of the set-up (`JPoints.IsSieveSetup.doubleSetup`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-- The sieving primes whose product is the step of the rows of the first coordinate `a`
(`row_step`), for the globals `g` of the sieve: the primes `prime[pnn[n]]`, `n < sieve_primes3`, in
the order of the plan, that divide `a` and modulo which the curve has no points at infinity
(`has_infinity`). -/
def rowStepPrimes (g : SiftGlobals) (a : ℤ) : List ℕ :=
  ((List.range g.sievePrimes3).filter fun n ↦
      !g.curve.hasInfinity[g.pnn[n]!]! && decide ((sievingPrime g.pnn n : ℤ) ∣ a)).map
    (sievingPrime g.pnn)

/-- The product of the primes of the step of the rows of the first coordinate `a`
(`JPoints.rowStepPrimes`) among the sieving primes of the indices `l`, for the globals `g` of the
sieve: the product that `row_step` has formed after the indices `l`. -/
def rowStepProd (g : SiftGlobals) (a : ℤ) (l : List ℕ) : ℕ :=
  ((l.filter fun n ↦ !g.curve.hasInfinity[g.pnn[n]!]! &&
    decide ((sievingPrime g.pnn n : ℤ) ∣ a)).map (sievingPrime g.pnn)).prod

theorem prod_rowStepPrimes (g : SiftGlobals) (a : ℤ) :
    (rowStepPrimes g a).prod = rowStepProd g a (List.range g.sievePrimes3) := rfl

theorem rowStepProd_append (g : SiftGlobals) (a : ℤ) (l₁ l₂ : List ℕ) :
    rowStepProd g a (l₁ ++ l₂) = rowStepProd g a l₁ * rowStepProd g a l₂ := by
  simp [rowStepProd]

/-- A product of sieving primes is positive. -/
theorem rowStepProd_pos {g : SiftGlobals} (h : ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes)
    (a : ℤ) {l : List ℕ} (hl : ∀ n ∈ l, n < g.sievePrimes3) : 0 < rowStepProd g a l := by
  refine List.prod_pos fun p hp ↦ ?_
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
  lia [three_le_getElem!_primeTable (h n (hl n (List.mem_filter.mp hn).1))]

/-- The invariant of the loop of `JPoints.rowStep` over the sieving primes, with its early return:
before it, the product of the primes of the step among the indices consumed, at most the height
bound `H`; after it, `H + 1`, and the product of all the primes of the step above `H`. -/
def RowStepInvariant (g : SiftGlobals) (a : ℤ) : Std.WP.Invariant ℕ (Option ℤ × ℤ) Prop :=
  fun pref suff st ↦ st.1.elim (st.2 = rowStepProd g a pref ∧ st.2 ≤ g.check.height)
    fun r ↦ suff = [] ∧ r = g.check.height + 1 ∧
      g.check.height < rowStepProd g a (List.range g.sievePrimes3)

section RowStep

variable {g : SiftGlobals} {a : ℤ} {pref suff : List ℕ} {cur : ℕ} {o : Option ℤ} {m : ℤ}

private theorem rowStep_cond_eq (n : ℕ) :
    (!g.curve.hasInfinity[g.pnn[n]!]! && a.tmod (primeTable[g.pnn[n]!]! : ℤ) == 0) =
      (!g.curve.hasInfinity[g.pnn[n]!]! && decide ((sievingPrime g.pnn n : ℤ) ∣ a)) := by
  simp only [Int.dvd_iff_tmod_eq_zero, Bool.beq_eq_decide_eq]

private theorem rowStepProd_concat_of_cond (hc : (!g.curve.hasInfinity[g.pnn[cur]!]! &&
    a.tmod (primeTable[g.pnn[cur]!]! : ℤ) == 0) = true) :
    (rowStepProd g a (pref ++ [cur]) : ℤ) = rowStepProd g a pref * primeTable[g.pnn[cur]!]! := by
  rw [rowStep_cond_eq] at hc
  simp [rowStepProd, hc]

private theorem rowStepProd_concat_of_not_cond (hc : ¬(!g.curve.hasInfinity[g.pnn[cur]!]! &&
    a.tmod (primeTable[g.pnn[cur]!]! : ℤ) == 0) = true) :
    rowStepProd g a (pref ++ [cur]) = rowStepProd g a pref := by
  rw [rowStep_cond_eq] at hc
  simp [rowStepProd, hc]

private theorem rowStepInvariant_init
    (h : 1 ≤ g.check.height ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes) :
    RowStepInvariant g a [] (ForIn.toList [:g.sievePrimes3]) (none, 1) :=
  ⟨by simp [rowStepProd], h.1⟩

private theorem rowStepInvariant_return
    (h : 1 ≤ g.check.height ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes)
    (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    (hi : RowStepInvariant g a pref (cur :: suff) (o, m))
    (hc : (!g.curve.hasInfinity[g.pnn[cur]!]! &&
      a.tmod (primeTable[g.pnn[cur]!]! : ℤ) == 0) = true)
    (hm : g.check.height < m * primeTable[g.pnn[cur]!]!) :
    RowStepInvariant g a (ForIn.toList [:g.sievePrimes3]) []
      (some (g.check.height + 1), m * primeTable[g.pnn[cur]!]!) := by
  rcases o with _ | r
  · obtain ⟨rfl, -⟩ := hi
    refine ⟨rfl, rfl, ?_⟩
    have hlt : ∀ n ∈ suff, n < g.sievePrimes3 := fun n hn ↦ List.mem_range.mp
      (Std.Legacy.Range.toList_eq_range _ ▸ hl ▸ List.mem_append_right _ (.tail _ hn))
    have hpos := rowStepProd_pos h.2 a hlt
    rw [← Std.Legacy.Range.toList_eq_range, hl, ← List.singleton_append, ← List.append_assoc,
      rowStepProd_append, Nat.cast_mul, rowStepProd_concat_of_cond hc]
    exact lt_of_lt_of_le hm (le_mul_of_one_le_right (by lia) (by lia))
  · exact absurd hi.1 (List.cons_ne_nil _ _)

private theorem rowStepInvariant_mul
    (hi : RowStepInvariant g a pref (cur :: suff) (o, m))
    (hc : (!g.curve.hasInfinity[g.pnn[cur]!]! &&
      a.tmod (primeTable[g.pnn[cur]!]! : ℤ) == 0) = true)
    (hm : ¬g.check.height < m * primeTable[g.pnn[cur]!]!) :
    RowStepInvariant g a (pref ++ [cur]) suff (none, m * primeTable[g.pnn[cur]!]!) := by
  rcases o with _ | r
  · obtain ⟨h1, -⟩ := hi
    refine ⟨?_, by simpa using hm⟩
    change m * _ = _
    rw [rowStepProd_concat_of_cond hc, ← h1]
  · exact absurd hi.1 (List.cons_ne_nil _ _)

private theorem rowStepInvariant_skip
    (hi : RowStepInvariant g a pref (cur :: suff) (o, m))
    (hc : ¬(!g.curve.hasInfinity[g.pnn[cur]!]! &&
      a.tmod (primeTable[g.pnn[cur]!]! : ℤ) == 0) = true) :
    RowStepInvariant g a (pref ++ [cur]) suff (none, m) := by
  rcases o with _ | r
  · obtain ⟨h1, h2⟩ := hi
    exact ⟨by rw [rowStepProd_concat_of_not_cond hc]; exact h1, h2⟩
  · exact absurd hi.1 (List.cons_ne_nil _ _)

private theorem rowStepInvariant_post_some {r : ℤ}
    (hi : RowStepInvariant g a (ForIn.toList [:g.sievePrimes3]) [] (o, m)) (ho : o = some r) :
    r = if (rowStepProd g a (List.range g.sievePrimes3) : ℤ) ≤ g.check.height then
      (rowStepProd g a (List.range g.sievePrimes3) : ℤ) else g.check.height + 1 := by
  subst ho
  obtain ⟨-, rfl, h⟩ := hi
  have hn : ¬(rowStepProd g a (List.range g.sievePrimes3) : ℤ) ≤ g.check.height := by lia
  simp only [hn, ↓reduceIte]

private theorem rowStepInvariant_post_none
    (hi : RowStepInvariant g a (ForIn.toList [:g.sievePrimes3]) [] (o, m)) (ho : o = none) :
    m = if (rowStepProd g a (List.range g.sievePrimes3) : ℤ) ≤ g.check.height then
      (rowStepProd g a (List.range g.sievePrimes3) : ℤ) else g.check.height + 1 := by
  subst ho
  obtain ⟨rfl, h⟩ := hi
  rw [Std.Legacy.Range.toList_eq_range] at h ⊢
  simp only [h, ↓reduceIte]

end RowStep

attribute [local irreducible] RowStepInvariant in
/-- The value of `row_step` by its loop: the partial products of the primes of the step, as long as
they stay within the height bound, and `H + 1` as soon as one exceeds it, which the product of all
of them then does. -/
private theorem rowStep_spec_prod (g : SiftGlobals) (a : ℤ) :
    ⦃ 1 ≤ g.check.height ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes ⦄
    rowStep g a
    ⦃ fun m ↦ m = if (rowStepProd g a (List.range g.sievePrimes3) : ℤ) ≤ g.check.height then
      (rowStepProd g a (List.range g.sievePrimes3) : ℤ) else g.check.height + 1 ⦄ := by
  vcgen [rowStep] invariants
  · RowStepInvariant g a
  all_goals with_reducible first
    | exact rowStepInvariant_init ‹_›
    | exact rowStepInvariant_post_some ‹_› ‹_›
    | exact rowStepInvariant_post_none ‹_› ‹_›
    | exact rowStepInvariant_return ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact rowStepInvariant_mul ‹_› ‹_› ‹_›
    | exact rowStepInvariant_skip ‹_› ‹_›

/-- `row_step` returns the product of the sieving primes that divide `a` and modulo which the curve
has no points at infinity (`JPoints.rowStepPrimes`) when it is at most the height bound `H ≥ 1`, and
`H + 1` otherwise: its partial products grow, the primes of the table being at least `3`, so that
one exceeds `H` exactly when the whole product does. -/
theorem run_rowStep {g : SiftGlobals} (hH : 1 ≤ g.check.height)
    (h : ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes) (a : ℤ) :
    (rowStep g a).run = if ((rowStepPrimes g a).prod : ℤ) ≤ g.check.height then
      ((rowStepPrimes g a).prod : ℤ) else g.check.height + 1 :=
  (rowStep_spec_prod g a).le_wp ⟨hH, h⟩

/-- `row_step` returns its own value, which the test of the rows reads (`JPoints.rowKeeps`), at
least `1`, a product of sieving primes, and at most `H + 1`, the value when the product exceeds the
height bound `H` (`JPoints.run_rowStep`), for sieving primes of the table. -/
@[spec]
theorem rowStep_spec (g : SiftGlobals) (a : ℤ) :
    ⦃ 1 ≤ g.check.height ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes ⦄
    rowStep g a
    ⦃ fun m ↦ m = (rowStep g a).run ∧ 1 ≤ m ∧ m ≤ g.check.height + 1 ⦄ := by
  refine ⟨fun ⟨hH, h⟩ ↦ ⟨rfl, ?_⟩⟩
  have := rowStepProd_pos h a (l := List.range g.sievePrimes3) fun n hn ↦ List.mem_range.mp hn
  change 1 ≤ (rowStep g a).run ∧ (rowStep g a).run ≤ g.check.height + 1
  rw [run_rowStep hH h, prod_rowStepPrimes]
  split_ifs <;> lia

/-- `find_double_points` prints the points over the triples `(s², 2st, t²)` of the double points of
the search (`JPoints.doubleTriples`), in their order, only the first under `-1`: its sieve of the
pairs `(s, t)`, the squares `s` of a monic quintic, and the skip of the `s` divisible by a sieving
prime modulo which the curve has no points at infinity keep every pair with a point, since on the
conic `JPoints.Lifts` makes `F(t, s)` a square. The flag returned says whether it stopped at a point
under `-1`. -/
@[spec]
theorem findDoublePoints_spec (bg : BandGlobals) (out : Output) :
    ⦃ ∃ sd, IsSieveSetup bg sd ⦄
    findDoublePoints bg.sift out
    ⦃ fun r ↦ r.2 = out.appendPoints bg.sift.check (firstIf bg.sift.check.onePoint
          ((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points)) ∧
        r.1 = (bg.sift.check.onePoint &&
          !((doubleTriples bg.sift.check.H).flatMap bg.sift.check.points).isEmpty) ⦄ :=
  ⟨fun ⟨_, h⟩ ↦ (findDoublePoints_spec_of_doubleSetup bg.sift out).le_wp h.doubleSetup⟩

end JPoints

end
