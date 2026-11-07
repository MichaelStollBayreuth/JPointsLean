/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.Loops
public import JPoints.Proof.Rates

import JPoints.Proof.Containers
import JPoints.Proof.Qsort
import Mathlib.Tactic.IntervalCases
import Std.Tactic.Do

/-!
# The contracts of the choice of the sieving primes

What `choose_primes` of `j-points` leaves for the search, for every value of the `Float`s of its
cost model: a choice of sieving primes among the primes considered (`JPoints.IsStages`), the
numbers of the primes of the stages increasing and at most the number `-N` of the command line when
it is given, the primes distinct and those of the first two stages at most `MAX_TABLE_PRIME`
(`JPoints.choosePrimes_spec`); and the tables of the curve for the primes chosen, whose rows of the
third stage the end of `init_fmodpsquare` fills (`JPoints.initFmodpsquareTables_spec`).

The choice is a structural fact: whatever the costs, every choice that `choose_primes_mode` keeps
(`JPoints.IsKept`) takes the first `n1` candidates of the ranking of the first stage, which are the
primes of at most `MAX_TABLE_PRIME`, the first `n2 - n1` of the ranking of the second, which are the
candidates of the first that the first stage does not take (`JPoints.IsUsed`), and the first
`n3 - n2` of the ranking of the third, which are the primes that neither takes, each ranking with
its candidates once (`JPoints.CandsWF`), sorted by `qsort`, which permutes them; the ranges of the
numbers keep them within the rankings and the pin of `-N`. So the three parts of a choice are
disjoint (`JPoints.isStages_ite`), and by the records of `prec` (`JPoints.PrecWF`) their indices in
`prec` are those of distinct primes of the table (`JPoints.IsStages.prec`).

## Main definitions

* `JPoints.IsStages`: a choice of sieving primes by the indices of its primes.
* `JPoints.CandsWF`, `JPoints.IsUsed`, `JPoints.TwoStageCands`: the rankings of the stages and the
  flags of the first stage.
* `JPoints.ModeBest.idx`, `JPoints.ModeBest.WF`, `JPoints.IsKept`: the cheapest choice of a mode.
* `JPoints.UsedClearInvariant`, `JPoints.PushInvariant`, `JPoints.PnnUpTo`,
  `JPoints.ChoiceInvariant`, `JPoints.TablesInvariant`: the invariants of the loops.

## Main statements

* `JPoints.choosePrimesModeFirst_spec`, `JPoints.choosePrimesModeList1_spec`,
  `JPoints.choosePrimesModeList2_spec`, `JPoints.choosePrimesModeList3_spec`,
  `JPoints.choosePrimesModeKeep_spec`, `JPoints.choosePrimesModeLoop3_spec`,
  `JPoints.choosePrimesModeLoop2_spec`, `JPoints.choosePrimesModeLoop1_spec`: the parts of
  `choose_primes_mode`.
* `JPoints.choosePrimesMode_spec`, `JPoints.choosePrimes_spec`: the choice of a mode, and the
  choice.
* `JPoints.initFmodpsquareTables_spec`: the tables of the primes chosen.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. No proof reads a `Float`: the costs, the
values of the candidates and the comparisons of the costs, which decide which choice is kept, are
left open, and each contract holds for every outcome of each comparison. So the loop over `n3` keeps
the cheapest choice it is given or a choice of its own (`JPoints.choosePrimesModeLoop3_spec`), and
when no mode is taken, which needs `-1.0 < 0.0` to fail, as IEEE 754 excludes but no proof can,
since none evaluates a `Float` comparison, the plan has no sieving primes and keeps its mode. The
components that compute only `Float`s (`JPoints.choosePrimesModeTerms`,
`JPoints.choosePrimesModeSecond`) have the contract that says nothing, passed to `vcgen` where they
are called.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The first stage -/

/-- The flags `used` of the first stage of the `n1` best candidates of `list1`: one per prime of
the table, set exactly at the indices in `prec` of these candidates. -/
def IsUsed (list1 : Array Cand) (n1 : ℕ) (used : Array Bool) : Prop :=
  used.size = numPrimes ∧ ∀ n, used[n]! = true ↔ ∃ k < n1, list1[k]!.n = n

/-- The invariant of the loop of `JPoints.choosePrimesModeFirst` that clears the flags of the first
`nPrimes` primes, after the first `k`: the flags keep their size, and those set are of primes at or
after `k` among the first `nPrimes`. -/
def UsedClearInvariant (nPrimes k : ℕ) (used : Array Bool) : Prop :=
  used.size = numPrimes ∧ ∀ n, used[n]! = true → k ≤ n ∧ n < nPrimes

private theorem usedClearInvariant_nil {nPrimes : ℕ} {used : Array Bool}
    (hs : used.size = numPrimes)
    (h : ∀ n, used[n]! = true → n < nPrimes) :
    UsedClearInvariant nPrimes ([] : List ℕ).length used :=
  ⟨hs, fun n hn ↦ ⟨Nat.zero_le n, h n hn⟩⟩

theorem UsedClearInvariant.set! {nPrimes : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:nPrimes] = pref ++ cur :: suff) {used : Array Bool}
    (h : UsedClearInvariant nPrimes pref.length used) :
    UsedClearInvariant nPrimes (pref ++ [cur]).length (used.set! cur false) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by rw [Array.size_set!, h.1], fun n hn ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hc]
  by_cases hnc : n = cur
  · subst hnc; exact absurd hn (Array.getElem!_set!_false_ne_true used n)
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hnc)] at hn
    exact ⟨by lia [(h.2 n hn).1], (h.2 n hn).2⟩

private theorem UsedClearInvariant.isUsed_nil {nPrimes : ℕ} {used : Array Bool}
    (h : UsedClearInvariant nPrimes (ForIn.toList [:nPrimes]).length used) (list1 : Array Cand) :
    IsUsed list1 ([] : List ℕ).length used := by
  rw [Std.Legacy.Range.length_toList_zero_start] at h
  exact ⟨h.1, fun n ↦ ⟨fun hn ↦ by lia [h.2 n hn], fun ⟨k, hk, _⟩ ↦ absurd hk (Nat.not_lt_zero k)⟩⟩

theorem IsUsed.set! {list1 : Array Cand} {n1 nPrimes : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:n1] = pref ++ cur :: suff) (hlt : ∀ k < n1, list1[k]!.n < nPrimes)
    (hn : nPrimes ≤ numPrimes) {used : Array Bool} (h : IsUsed list1 pref.length used) :
    IsUsed list1 (pref ++ [cur]).length (used.set! list1[cur]!.n true) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcn := hlt cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  refine ⟨by rw [Array.size_set!, h.1], fun n ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hc]
  by_cases hnc : n = list1[cur]!.n
  · subst hnc
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; lia)]
    exact ⟨fun _ ↦ ⟨cur, by lia, rfl⟩, fun _ ↦ rfl⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hnc), h.2 n, hc]
    exact ⟨fun ⟨k, hk, he⟩ ↦ ⟨k, by lia, he⟩, fun ⟨k, hk, he⟩ ↦
      ⟨k, lt_of_le_of_ne (Nat.le_of_lt_succ hk) fun h ↦ hnc (h ▸ he).symm, he⟩⟩

theorem IsUsed.of_toList {list1 : Array Cand} {n1 : ℕ} {used : Array Bool}
    (h : IsUsed list1 (ForIn.toList [:n1]).length used) : IsUsed list1 n1 used := by
  rwa [Std.Legacy.Range.length_toList_zero_start] at h

attribute [local irreducible] IsUsed UsedClearInvariant in
/-- The first stage of the `n1` best candidates of `list1` sets the flags `used` of their primes
(`JPoints.IsUsed`), after it clears those of the first `nPrimes` primes, the only ones set before;
the costs, the set-up and the density are `Float`s, about which nothing is said. -/
@[spec]
theorem choosePrimesModeFirst_spec (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (two : TwoAdic) (prec : Array Entry) (nPrimes : ℕ) (list1 : Array Cand) (used : Array Bool)
    (n1 : ℕ) :
    ⦃ used.size = numPrimes ∧ nPrimes ≤ numPrimes ∧ (∀ n, used[n]! = true → n < nPrimes) ∧
      ∀ k < n1, list1[k]!.n < nPrimes ⦄
    choosePrimesModeFirst s t c two prec nPrimes list1 used n1
    ⦃ fun r ↦ IsUsed list1 n1 r.used ⦄ := by
  vcgen [choosePrimesModeFirst] invariants
  · fun pref _ u ↦ UsedClearInvariant nPrimes pref.length u
  · fun pref _ s ↦ IsUsed list1 pref.length s.2.2.2
  all_goals try dsimp only at *
  all_goals obtain ⟨hs, hn, hu, hl⟩ := ‹used.size = numPrimes ∧ _›
  all_goals with_reducible first
    | exact usedClearInvariant_nil hs hu
    | exact UsedClearInvariant.set! ‹_› ‹_›
    | exact UsedClearInvariant.isUsed_nil ‹_› list1
    | exact IsUsed.of_toList ‹_›
    | exact IsUsed.set! ‹_› hl hn ‹_›

/-! ### The rankings of the stages -/

/-- The candidates `l` of a stage of the choice of the sieving primes, as `choose_primes_mode`
ranks them: the indices in `prec` of their primes are distinct and satisfy `P`. -/
structure CandsWF (P : ℕ → Prop) (l : Array Cand) : Prop where
  /-- The indices of the primes are distinct. -/
  nodup : (l.toList.map Cand.n).Nodup
  /-- They satisfy `P`. -/
  prop {k : ℕ} (hk : k < l.size) : P l[k]!.n

theorem CandsWF.n_injective {P : ℕ → Prop} {l : Array Cand} (h : CandsWF P l) {i j : ℕ}
    (hi : i < l.size) (hj : j < l.size) (he : l[i]!.n = l[j]!.n) : i = j := by
  refine (h.nodup.getElem_inj_iff (hi := by simpa using hi) (hj := by simpa using hj)).mp ?_
  simpa [getElem!_pos l i hi, getElem!_pos l j hj] using he

private theorem CandsWF.size_le {P : ℕ → Prop} {l : Array Cand} (h : CandsWF P l) {N : ℕ}
    (hP : ∀ k < l.size, P l[k]!.n → l[k]!.n < N) : l.size ≤ N := by
  have hs : l.toList.map Cand.n ⊆ List.range N := fun n hn ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    rw [Array.length_toList] at hk
    rw [Array.getElem_toList, ← getElem!_pos l k hk]
    exact List.mem_range.mpr (hP k hk (h.prop hk))
  simpa using (h.nodup.subperm hs).length_le

/-- The invariant of a loop of `choose_primes_mode` that pushes the candidates of a stage, after the
steps `pref`: the indices in `prec` of the candidates pushed are those `f k` of the steps `k` that
pass the test `q`, in their order. -/
def PushInvariant (f : ℕ → ℕ) (q : ℕ → Bool) (pref : List ℕ) (l : Array Cand) : Prop :=
  l.toList.map Cand.n = (pref.map f).filter q

private theorem pushInvariant_nil (f : ℕ → ℕ) (q : ℕ → Bool) :
    PushInvariant f q ([] : List ℕ) #[] := rfl

theorem PushInvariant.push {f : ℕ → ℕ} {q : ℕ → Bool} {pref : List ℕ} {cur : ℕ}
    (hq : q (f cur) = true) {l : Array Cand} (h : PushInvariant f q pref l) {c : Cand}
    (hc : c.n = f cur) : PushInvariant f q (pref ++ [cur]) (l.push c) := by
  simp only [PushInvariant, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, hc] at h ⊢
  rw [h, List.filter_singleton, hq]
  rfl

theorem PushInvariant.skip {f : ℕ → ℕ} {q : ℕ → Bool} {pref : List ℕ} {cur : ℕ}
    (hq : q (f cur) = false) {l : Array Cand} (h : PushInvariant f q pref l) :
    PushInvariant f q (pref ++ [cur]) l := by
  simpa only [PushInvariant, List.map_append, List.map_cons, List.map_nil, List.filter_append,
    List.filter_singleton, hq, Bool.cond_false, List.append_nil] using h

/-- Candidates pushed by a loop over the steps `L`, sorted by `qsort`: the indices of the steps that
pass the test are distinct when the indices of all steps are, and satisfy `P` when those that pass
do. -/
private theorem PushInvariant.candsWF_qsort {f : ℕ → ℕ} {q : ℕ → Bool} {L : List ℕ} {l : Array Cand}
    (h : PushInvariant f q L l) (hnd : (L.map f).Nodup) {P : ℕ → Prop}
    (hP : ∀ x ∈ L, q (f x) = true → P (f x)) (cmp : Cand → Cand → ℤ) :
    CandsWF P (qsort cmp l l.size) := by
  have hp := toList_qsort_perm cmp l
  refine ⟨(hp.map Cand.n).nodup_iff.mpr (h ▸ hnd.filter q), fun {k} hk ↦ ?_⟩
  have hm : (qsort cmp l l.size)[k]!.n ∈ l.toList.map Cand.n :=
    List.mem_map_of_mem (hp.subset (Array.mem_toList_iff.mpr (Array.getElem!_mem hk)))
  rw [h, List.mem_filter, List.mem_map] at hm
  obtain ⟨⟨x, hx, hxe⟩, hq⟩ := hm
  exact hxe ▸ hP x hx (hxe ▸ hq)

-- The candidates of the first stage before their sort.
private theorem list1_post {prec : Array Entry} {nPrimes : ℕ} {l : Array Cand}
    (h : PushInvariant (fun n ↦ n) (fun n ↦ decide (prec[n]!.p ≤ maxTablePrime))
      (ForIn.toList [:nPrimes]) l) :
    CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) (qsort compareCands l l.size) :=
  h.candsWF_qsort (by rw [Std.Legacy.Range.toList_eq_range, List.map_id']; exact List.nodup_range)
    (fun x hx hq ↦
      ⟨List.mem_range.mp (Std.Legacy.Range.toList_eq_range nPrimes ▸ hx), of_decide_eq_true hq⟩)
    _

/-- The ranking of the first stage: the primes of the first `nPrimes` records of `prec` of at most
`MAX_TABLE_PRIME`, each once. -/
@[spec]
theorem choosePrimesModeList1_spec (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (prec : Array Entry) (nPrimes : ℕ) :
    ⦃ True ⦄ choosePrimesModeList1 s t c prec nPrimes
    ⦃ fun r ↦ CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) r ⦄ := by
  vcgen [choosePrimesModeList1] invariants
  · fun pref _ l ↦ PushInvariant (fun n ↦ n) (fun n ↦ decide (prec[n]!.p ≤ maxTablePrime)) pref l
  all_goals with_reducible first
    | exact pushInvariant_nil _ _
    | exact PushInvariant.push (decide_eq_true ‹_›) ‹_› rfl
    | exact PushInvariant.skip (decide_eq_false ‹_›) ‹_›
    | exact list1_post ‹_›

-- The indices in `prec` of the primes of the candidates `l` in their order.
private theorem map_range_size_getElem!_n (l : Array Cand) :
    (List.range l.size).map (fun k ↦ l[k]!.n) = l.toList.map Cand.n := by
  rw [← List.map_range_length_getElem! l.toList, List.map_map, Array.length_toList]
  exact List.map_congr_left fun k hk ↦ by
    rw [Function.comp_apply, ← Array.getElem!_toList]

-- The candidates of the second stage before their sort.
private theorem list2_post {list1 : Array Cand} {used : Array Bool} {l : Array Cand}
    (hnd : (list1.toList.map Cand.n).Nodup)
    (h : PushInvariant (fun k ↦ list1[k]!.n) (fun n ↦ !used[n]!) (ForIn.toList [:list1.size]) l) :
    CandsWF (fun n ↦ used[n]! = false ∧ ∃ k < list1.size, list1[k]!.n = n)
      (qsort compareCands l l.size) :=
  h.candsWF_qsort (by rwa [Std.Legacy.Range.toList_eq_range, map_range_size_getElem!_n])
    (fun x hx hq ↦
      ⟨by simpa using hq, x, List.mem_range.mp (Std.Legacy.Range.toList_eq_range _ ▸ hx), rfl⟩) _

/-- The ranking of the second stage: the primes of the candidates of `list1` that the first stage
does not take (`used`), each once when those of `list1` are distinct. -/
@[spec]
theorem choosePrimesModeList2_spec (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (list1 : Array Cand) (used : Array Bool) (s1 : Float) :
    ⦃ (list1.toList.map Cand.n).Nodup ⦄ choosePrimesModeList2 s t c list1 used s1
    ⦃ fun r ↦ CandsWF (fun n ↦ used[n]! = false ∧ ∃ k < list1.size, list1[k]!.n = n) r ⦄ := by
  vcgen [choosePrimesModeList2] invariants
  · fun pref _ l ↦ PushInvariant (fun k ↦ list1[k]!.n) (fun n ↦ !used[n]!) pref l
  all_goals with_reducible first
    | exact pushInvariant_nil _ _
    | exact PushInvariant.push ‹_› ‹_› rfl
    | exact PushInvariant.skip (Bool.eq_false_iff.mpr ‹_›) ‹_›
    | exact list2_post ‹_› ‹_›

-- The verification conditions of `JPoints.choosePrimesModeList3`, each in its shape.

private theorem false_eq_any_nil (g : ℕ → Bool) : false = ([] : List ℕ).any g := rfl

private theorem any_append_singleton_of_beq {g : ℕ → Bool} {pref : List ℕ} {k : ℕ} {b : Bool}
    (hc : g k = true) (_ : b = pref.any g) : true = (pref ++ [k]).any g := by
  simp [hc]

private theorem any_append_singleton_of_not_beq {g : ℕ → Bool} {pref : List ℕ} {k : ℕ}
    {b : Bool} (hc : ¬g k = true) (h : b = pref.any g) : b = (pref ++ [k]).any g := by
  simp [h, Bool.eq_false_iff.mpr hc]

private theorem list3_push {used : Array Bool} {list2 : Array Cand} {k2 : ℕ} {pref : List ℕ}
    {cur : ℕ} {l : Array Cand} {in2 : Bool}
    (h : PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n)) pref l)
    (hin : in2 = (ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == cur)
    (hc : (!used[cur]! && !in2) = true) {c : Cand} (hcn : c.n = cur) :
    PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n))
      (pref ++ [cur]) (l.push c) :=
  h.push (hin ▸ hc) hcn

private theorem list3_skip {used : Array Bool} {list2 : Array Cand} {k2 : ℕ} {pref : List ℕ}
    {cur : ℕ} {l : Array Cand} {in2 : Bool}
    (h : PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n)) pref l)
    (hin : in2 = (ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == cur)
    (hc : ¬(!used[cur]! && !in2) = true) :
    PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n))
      (pref ++ [cur]) l :=
  h.skip (hin ▸ Bool.eq_false_iff.mpr hc)

-- The candidates of the third stage before their sort.
private theorem list3_post {nPrimes : ℕ} {used : Array Bool} {list2 : Array Cand} {k2 : ℕ}
    {l : Array Cand}
    (h : PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n))
      (ForIn.toList [:nPrimes]) l) :
    CandsWF (fun n ↦ n < nPrimes ∧ used[n]! = false ∧ ∀ k < k2, list2[k]!.n ≠ n)
      (qsort compareCands l l.size) := by
  refine h.candsWF_qsort
    (by rw [Std.Legacy.Range.toList_eq_range, List.map_id']; exact List.nodup_range)
    (fun x hx hq ↦
      ⟨List.mem_range.mp (Std.Legacy.Range.toList_eq_range nPrimes ▸ hx), ?_, fun k hk he ↦ ?_⟩) _
  · simpa using (Bool.and_eq_true _ _).mp hq |>.1
  · have := ((Bool.and_eq_true _ _).mp hq).2
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
    exact this k (Std.Legacy.Range.toList_eq_range k2 ▸ List.mem_range.mpr hk) he

/-- The ranking of the third stage: the first `nPrimes` primes of `prec` that neither the first
stage (`used`) nor the first `k2` candidates of `list2` take, each once. -/
@[spec]
theorem choosePrimesModeList3_spec (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (nPrimes : ℕ) (used : Array Bool) (list2 : Array Cand) (k2 : ℕ) (rho2 rowbit : Float) :
    ⦃ True ⦄ choosePrimesModeList3 s t c nPrimes used list2 k2 rho2 rowbit
    ⦃ fun r ↦ CandsWF (fun n ↦ n < nPrimes ∧ used[n]! = false ∧ ∀ k < k2, list2[k]!.n ≠ n) r ⦄ := by
  vcgen [choosePrimesModeList3] invariants
  | inv1 => fun pref _ l ↦ PushInvariant (fun n ↦ n)
      (fun n ↦ !used[n]! && !((ForIn.toList [:k2]).any fun k ↦ list2[k]!.n == n)) pref l
  | inv2 _ cur _ _ _ _ => fun pref _ (in2 : Bool) ↦ in2 = pref.any fun k ↦ list2[k]!.n == cur
  all_goals with_reducible first
    | exact pushInvariant_nil _ _
    | exact false_eq_any_nil _
    | exact any_append_singleton_of_beq ‹_› ‹_›
    | exact any_append_singleton_of_not_beq ‹_› ‹_›
    | exact list3_push ‹_› ‹_› ‹_› rfl
    | exact list3_skip ‹_› ‹_› ‹_›
    | exact list3_post ‹_›

/-! ### The stages of a choice -/

/-- The stages of a choice of sieving primes by the indices `f j` of their primes at the positions
`j < sp3`, the first `sp1` those of the first stage and the first `sp2` those of the first two: the
numbers of the primes increase and are at most the number `pin3` of the command line when it is
given (not `-1`), the indices are distinct and below `nPrimes`, and those of the first two stages
satisfy `P`. -/
structure IsStages (nPrimes : ℕ) (pin3 : ℤ) (P : ℕ → Prop) (f : ℕ → ℕ) (sp1 sp2 sp3 : ℕ) :
    Prop where
  /-- The first stage is part of the first two. -/
  sp1_le_sp2 : sp1 ≤ sp2
  /-- The first two stages are part of the three. -/
  sp2_le_sp3 : sp2 ≤ sp3
  /-- The number of primes of the three stages is at most `pin3` when it is given. -/
  sp3_le_pin3 : 0 ≤ pin3 → (sp3 : ℤ) ≤ pin3
  /-- The indices are below `nPrimes`. -/
  lt {j : ℕ} (hj : j < sp3) : f j < nPrimes
  /-- The indices are distinct. -/
  injective {i j : ℕ} (hi : i < sp3) (hj : j < sp3) (h : f i = f j) : i = j
  /-- The indices of the first two stages satisfy `P`. -/
  prop {j : ℕ} (hj : j < sp2) : P (f j)

namespace IsStages

variable {nPrimes : ℕ} {pin3 : ℤ} {P : ℕ → Prop} {f : ℕ → ℕ} {sp1 sp2 sp3 : ℕ}

theorem zero (nPrimes : ℕ) (pin3 : ℤ) (P : ℕ → Prop) (f : ℕ → ℕ) :
    IsStages nPrimes pin3 P f 0 0 0 :=
  ⟨le_rfl, le_rfl, fun h ↦ by simpa using h, fun h ↦ absurd h (Nat.not_lt_zero _),
    fun h ↦ absurd h (Nat.not_lt_zero _), fun h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem congr (h : IsStages nPrimes pin3 P f sp1 sp2 sp3) {g : ℕ → ℕ}
    (hg : ∀ j < sp3, g j = f j) : IsStages nPrimes pin3 P g sp1 sp2 sp3 :=
  ⟨h.sp1_le_sp2, h.sp2_le_sp3, h.sp3_le_pin3, fun {j} hj ↦ hg j hj ▸ h.lt hj,
    fun {i j} hi hj he ↦ h.injective hi hj (by rwa [← hg i hi, ← hg j hj]),
    fun {j} hj ↦ hg j (lt_of_lt_of_le hj h.sp2_le_sp3) ▸ h.prop hj⟩

/-- The pigeonhole principle: the distinct indices below `nPrimes` are at most `nPrimes`. -/
theorem sp3_le (h : IsStages nPrimes pin3 P f sp1 sp2 sp3) : sp3 ≤ nPrimes := by
  simpa using Finset.card_le_card_of_injOn f (s := Finset.range sp3) (t := Finset.range nPrimes)
    (fun j hj ↦ by simpa using h.lt (by simpa using hj))
    (fun i hi j hj he ↦ h.injective (by simpa using hi) (by simpa using hj) he)

/-- Stages whose indices are those of a plan, with the primes of the first two stages at most
`MAX_TABLE_PRIME`, are the stages of the plan of the sieve: their number is at most `nPrimes` by the
pigeonhole principle (`JPoints.IsStages.sp3_le`), and none for `pin3 = 0`. -/
theorem isSieveStages {pnn : Array ℕ}
    (h : IsStages nPrimes pin3 (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! pnn) sp1 sp2
      sp3) :
    IsSieveStages nPrimes pin3 pnn sp1 sp2 sp3 :=
  ⟨h.sp1_le_sp2, h.sp2_le_sp3, h.sp3_le, h.lt, h.injective, h.prop,
    fun h3 ↦ by lia [h.sp3_le_pin3 (by lia)]⟩

/-- The stages by the indices in `prec` of their primes give the stages by their indices in the
table of the primes, when the first `nPrimes` records of `prec` are those of the first `nPrimes`
primes (`JPoints.PrecWF`). -/
theorem prec {prec : Array Entry}
    (h : IsStages nPrimes pin3 (fun m ↦ prec[m]!.p ≤ maxTablePrime) f sp1 sp2 sp3)
    (hp : PrecWF nPrimes prec) {g : ℕ → ℕ} (hg : ∀ j < sp3, g j = prec[f j]!.n) :
    IsStages nPrimes pin3 (fun n ↦ primeTable[n]! ≤ maxTablePrime) g sp1 sp2 sp3 := by
  refine ⟨h.sp1_le_sp2, h.sp2_le_sp3, h.sp3_le_pin3, fun hj ↦ ?_, fun hi hj he ↦ ?_, fun hj ↦ ?_⟩
  · rw [hg _ hj]; exact hp.n_lt (h.lt hj)
  · rw [hg _ hi, hg _ hj] at he
    exact h.injective hi hj (hp.n_injective (h.lt hi) (h.lt hj) he)
  · have hj3 : _ < sp3 := lt_of_lt_of_le hj h.sp2_le_sp3
    rw [hg _ hj3, ← hp.p_eq (h.lt hj3)]
    exact h.prop hj

end IsStages

/-- Stages glued from three parts, the indices `f1 j` for `j < n1`, then `f2 (j - n1)` for
`n1 ≤ j < n2` and `f3 (j - n2)` for `n2 ≤ j < n3`: when each part has distinct indices below
`nPrimes`, the parts are disjoint, and those of the first two parts satisfy `P`. -/
theorem isStages_ite {nPrimes : ℕ} {pin3 : ℤ} {P : ℕ → Prop} {f1 f2 f3 : ℕ → ℕ}
    {n1 n2 n3 : ℕ} (h12 : n1 ≤ n2) (h23 : n2 ≤ n3) (hpin : 0 ≤ pin3 → (n3 : ℤ) ≤ pin3)
    (hlt1 : ∀ j < n1, f1 j < nPrimes) (hlt2 : ∀ j < n2 - n1, f2 j < nPrimes)
    (hlt3 : ∀ j < n3 - n2, f3 j < nPrimes) (hP1 : ∀ j < n1, P (f1 j))
    (hP2 : ∀ j < n2 - n1, P (f2 j)) (hi1 : ∀ i < n1, ∀ j < n1, f1 i = f1 j → i = j)
    (hi2 : ∀ i < n2 - n1, ∀ j < n2 - n1, f2 i = f2 j → i = j)
    (hi3 : ∀ i < n3 - n2, ∀ j < n3 - n2, f3 i = f3 j → i = j)
    (hd12 : ∀ i < n1, ∀ j < n2 - n1, f1 i ≠ f2 j) (hd13 : ∀ i < n1, ∀ j < n3 - n2, f1 i ≠ f3 j)
    (hd23 : ∀ i < n2 - n1, ∀ j < n3 - n2, f2 i ≠ f3 j) :
    IsStages nPrimes pin3 P
      (fun j ↦ if j < n1 then f1 j else if j < n2 then f2 (j - n1) else f3 (j - n2)) n1 n2 n3 := by
  refine ⟨h12, h23, hpin, fun {j} hj ↦ ?_, fun {i j} hi hj he ↦ ?_, fun {j} hj ↦ ?_⟩
  · split_ifs
    · exact hlt1 j ‹_›
    · exact hlt2 _ (by lia)
    · exact hlt3 _ (by lia)
  · split_ifs at he
    all_goals first
      | exact hi1 i ‹_› j ‹_› he
      | lia [hi2 (i - n1) (by lia) (j - n1) (by lia) he]
      | lia [hi3 (i - n2) (by lia) (j - n2) (by lia) he]
      | exact absurd he (hd12 _ ‹_› _ (by lia))
      | exact absurd he.symm (hd12 _ ‹_› _ (by lia))
      | exact absurd he (hd13 _ ‹_› _ (by lia))
      | exact absurd he.symm (hd13 _ ‹_› _ (by lia))
      | exact absurd he (hd23 _ (by lia) _ (by lia))
      | exact absurd he.symm (hd23 _ (by lia) _ (by lia))
  · split_ifs
    · exact hP1 j ‹_›
    · exact hP2 _ (by lia)

/-! ### The cheapest choice kept -/

/-- The index in `prec` of the prime at the position `j` of the cheapest choice `b` of
`choose_primes_mode`: in its first stage, its second, or its third. -/
def ModeBest.idx (b : ModeBest) (j : ℕ) : ℕ :=
  if j < b.b1 then b.best1[j]! else if j < b.b2 then b.best2[j - b.b1]! else b.best3[j - b.b2]!

/-- The cheapest choice `b` of `choose_primes_mode` so far, for the first `nPrimes` records of
`prec` and the number `pin3` of the command line: its arrays have one entry for each prime of the
table, and its stages are those of a choice of primes of at most `MAX_TABLE_PRIME` in the first two
stages (`JPoints.IsStages`) by their indices in `prec` (`JPoints.ModeBest.idx`). -/
structure ModeBest.WF (nPrimes : ℕ) (pin3 : ℤ) (prec : Array Entry) (b : ModeBest) : Prop where
  /-- The size of `best1`. -/
  size_best1 : b.best1.size = numPrimes
  /-- The size of `best2`. -/
  size_best2 : b.best2.size = numPrimes
  /-- The size of `best3`. -/
  size_best3 : b.best3.size = numPrimes
  /-- The stages. -/
  stages : IsStages nPrimes pin3 (fun m ↦ prec[m]!.p ≤ maxTablePrime) b.idx b.b1 b.b2 b.b3

theorem ModeBest.wf_initial (nPrimes : ℕ) (pin3 : ℤ) (prec : Array Entry) :
    ({} : ModeBest).WF nPrimes pin3 prec :=
  ⟨Array.size_replicate, Array.size_replicate, Array.size_replicate, .zero _ _ _ _⟩

/-- The cheapest choice `b` that `JPoints.choosePrimesModeKeep` keeps for the numbers `n1`, `n2`
and `n3` of the primes of the stages: these numbers, and the indices in `prec` of the first `n1`
candidates of `list1`, the first `n2 - n1` of `list2` and the first `n3 - n2` of `list3`, in arrays
of one entry for each prime of the table. -/
structure IsKept (list1 list2 list3 : Array Cand) (n1 n2 n3 : ℕ) (b : ModeBest) : Prop where
  /-- The number of the primes of the first stage. -/
  b1_eq : b.b1 = n1
  /-- The number of the primes of the first two stages. -/
  b2_eq : b.b2 = n2
  /-- The number of the primes of the three stages. -/
  b3_eq : b.b3 = n3
  /-- The primes of the first stage. -/
  best1 : SetLoopInvariant numPrimes (fun k x ↦ x = list1[k]!.n) n1 b.best1
  /-- The primes of the second stage. -/
  best2 : SetLoopInvariant numPrimes (fun k x ↦ x = list2[k]!.n) (n2 - n1) b.best2
  /-- The primes of the third stage. -/
  best3 : SetLoopInvariant numPrimes (fun k x ↦ x = list3[k]!.n) (n3 - n2) b.best3

-- The postcondition of `JPoints.choosePrimesModeKeep`.
private theorem isKept_mk {list1 list2 list3 : Array Cand} {n1 n2 n3 : ℕ} {a1 a2 a3 : Array ℕ}
    (h1 : SetLoopInvariant numPrimes (fun k x ↦ x = list1[k]!.n) (ForIn.toList [:n1]).length a1)
    (h2 : SetLoopInvariant numPrimes (fun k x ↦ x = list2[k]!.n) (ForIn.toList [:n2 - n1]).length
      a2)
    (h3 : SetLoopInvariant numPrimes (fun k x ↦ x = list3[k]!.n) (ForIn.toList [:n3 - n2]).length
      a3) (total : Float) :
    IsKept list1 list2 list3 n1 n2 n3
      { best := total, b1 := n1, b2 := n2, b3 := n3, best1 := a1, best2 := a2, best3 := a3 } :=
  ⟨rfl, rfl, rfl, h1.of_toList, h2.of_toList, h3.of_toList⟩

/-- `JPoints.choosePrimesModeKeep` keeps the choice of the numbers `n1`, `n2` and `n3` of the primes
of the stages (`JPoints.IsKept`). -/
@[spec]
theorem choosePrimesModeKeep_spec (b : ModeBest) (total : Float) (list1 list2 list3 : Array Cand)
    (n1 n2 n3 : ℕ) :
    ⦃ b.best1.size = numPrimes ∧ b.best2.size = numPrimes ∧ b.best3.size = numPrimes ∧
      n1 ≤ numPrimes ∧ n2 - n1 ≤ numPrimes ∧ n3 - n2 ≤ numPrimes ⦄
    choosePrimesModeKeep b total list1 list2 list3 n1 n2 n3
    ⦃ fun r ↦ IsKept list1 list2 list3 n1 n2 n3 r ⦄ := by
  vcgen [choosePrimesModeKeep] invariants
  · fun pref _ s ↦ SetLoopInvariant numPrimes (fun k x ↦ x = list1[k]!.n) pref.length s
  · fun pref _ s ↦ SetLoopInvariant numPrimes (fun k x ↦ x = list2[k]!.n) pref.length s
  · fun pref _ s ↦ SetLoopInvariant numPrimes (fun k x ↦ x = list3[k]!.n) pref.length s
  all_goals obtain ⟨hs1, hs2, hs3, h1, h2, h3⟩ := ‹b.best1.size = numPrimes ∧ _›
  all_goals with_reducible first
    | exact setLoopInvariant_nil _ hs1
    | exact setLoopInvariant_nil _ hs2
    | exact setLoopInvariant_nil _ hs3
    | exact isKept_mk ‹_› ‹_› ‹_› total
    | exact SetLoopInvariant.set! ‹_› h1 ‹_› rfl
    | exact SetLoopInvariant.set! ‹_› h2 ‹_› rfl
    | exact SetLoopInvariant.set! ‹_› h3 ‹_› rfl

/-- The candidates of the first two stages of `choose_primes_mode` after the first stage of the
`n1` best candidates of `list1`: those of the first stage (`list1`) are primes of at most
`MAX_TABLE_PRIME` among the first `nPrimes` records of `prec`, `n1` at most their number, the flags
`used` set at the primes of the first stage (`JPoints.IsUsed`), and those of the second stage
(`list2`) the candidates of `list1` that the first stage does not take, each candidate once. -/
structure TwoStageCands (nPrimes : ℕ) (prec : Array Entry) (list1 : Array Cand) (n1 : ℕ)
    (used : Array Bool) (list2 : Array Cand) : Prop where
  /-- The candidates of the first stage. -/
  cands1 : CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) list1
  /-- The number of the primes of the first stage. -/
  n1_le : n1 ≤ list1.size
  /-- The flags of the first stage. -/
  isUsed : IsUsed list1 n1 used
  /-- The candidates of the second stage. -/
  cands2 : CandsWF (fun n ↦ used[n]! = false ∧ ∃ k < list1.size, list1[k]!.n = n) list2

namespace TwoStageCands

variable {nPrimes : ℕ} {prec : Array Entry} {list1 : Array Cand} {n1 : ℕ} {used : Array Bool}
  {list2 : Array Cand}

private theorem lt_of_list2 (h : TwoStageCands nPrimes prec list1 n1 used list2) {k : ℕ}
    (hk : k < list2.size) : list2[k]!.n < nPrimes ∧ prec[list2[k]!.n]!.p ≤ maxTablePrime := by
  obtain ⟨-, j, hj, he⟩ := h.cands2.prop hk
  exact he ▸ h.cands1.prop hj

private theorem size_list1_le (h : TwoStageCands nPrimes prec list1 n1 used list2) :
    list1.size ≤ nPrimes :=
  h.cands1.size_le fun _ _ hP ↦ hP.1

private theorem size_list2_le (h : TwoStageCands nPrimes prec list1 n1 used list2) :
    list2.size ≤ nPrimes :=
  h.cands2.size_le fun _ hk _ ↦ (h.lt_of_list2 hk).1

end TwoStageCands

-- The indices of the cheapest choice that `JPoints.choosePrimesModeKeep` keeps.
private theorem IsKept.idx_eq {list1 list2 list3 : Array Cand} {n1 n2 n3 : ℕ} {b : ModeBest}
    (hb : IsKept list1 list2 list3 n1 n2 n3 b) (h12 : n1 ≤ n2) {j : ℕ} (hj : j < n3) :
    b.idx j = if j < n1 then list1[j]!.n else if j < n2 then list2[j - n1]!.n
      else list3[j - n2]!.n := by
  simp only [ModeBest.idx, hb.b1_eq, hb.b2_eq]
  split_ifs
  · exact hb.best1.2 j ‹_›
  · exact hb.best2.2 (j - n1) (by lia)
  · exact hb.best3.2 (j - n2) (by lia)

/-- The cheapest choice that `JPoints.choosePrimesModeKeep` keeps from the candidates of the first
two stages (`JPoints.TwoStageCands`) and of the third, which neither the first stage nor the first
`n2 - n1` candidates of the second take, at most `pin3` primes when it is given, is a choice of
primes of at most `MAX_TABLE_PRIME` in the first two stages (`JPoints.ModeBest.WF`): the three
parts of the choice have distinct indices and are disjoint (`JPoints.isStages_ite`). -/
theorem IsKept.wf {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry} {list1 list2 list3 : Array Cand}
    {used : Array Bool} {n1 n2 n3 : ℕ} (h : TwoStageCands nPrimes prec list1 n1 used list2)
    (h3 : CandsWF (fun n ↦ n < nPrimes ∧ used[n]! = false ∧ ∀ k < n2 - n1, list2[k]!.n ≠ n) list3)
    (hn2 : n2 ≤ n1 + list2.size) (hn3 : n3 ≤ n2 + list3.size) (h12 : n1 ≤ n2) (h23 : n2 ≤ n3)
    (hpin : 0 ≤ pin3 → (n3 : ℤ) ≤ pin3) {b : ModeBest}
    (hb : IsKept list1 list2 list3 n1 n2 n3 b) : b.WF nPrimes pin3 prec := by
  have hn1 := h.n1_le
  have hused (i : ℕ) (hi : i < n1) : used[list1[i]!.n]! = true := (h.isUsed.2 _).mpr ⟨i, hi, rfl⟩
  have hl3 (j : ℕ) (hj : j < n3 - n2) := h3.prop (k := j) (by lia)
  refine ⟨hb.best1.1, hb.best2.1, hb.best3.1, ?_⟩
  rw [hb.b1_eq, hb.b2_eq, hb.b3_eq]
  refine (isStages_ite (f1 := fun j ↦ list1[j]!.n) (f2 := fun j ↦ list2[j]!.n)
    (f3 := fun j ↦ list3[j]!.n) h12 h23 hpin (fun j hj ↦ (h.cands1.prop (by lia)).1)
    (fun j hj ↦ (h.lt_of_list2 (by lia)).1) (fun j hj ↦ (hl3 j hj).1)
    (fun j hj ↦ (h.cands1.prop (by lia)).2) (fun j hj ↦ (h.lt_of_list2 (by lia)).2)
    (fun i hi j hj he ↦ h.cands1.n_injective (by lia) (by lia) he)
    (fun i hi j hj he ↦ h.cands2.n_injective (by lia) (by lia) he)
    (fun i hi j hj he ↦ h3.n_injective (by lia) (by lia) he)
    (fun i hi j hj he ↦ absurd ((h.cands2.prop (k := j) (by lia)).1.symm.trans
      (he ▸ hused i hi)) Bool.false_ne_true)
    (fun i hi j hj he ↦ absurd ((hl3 j hj).2.1.symm.trans (he ▸ hused i hi)) Bool.false_ne_true)
    (fun i hi j hj he ↦ (hl3 j hj).2.2 i hi he)).congr fun j hj ↦ hb.idx_eq h12 hj

/-! ### The ranges of the numbers of primes -/

private theorem choosePrimesModeRange1_snd_le (ne : ℕ) (pin1 pin2 pin3 : ℤ) :
    (choosePrimesModeRange1 ne pin1 pin2 pin3).2 ≤ ne ∧
      (0 ≤ pin3 → ((choosePrimesModeRange1 ne pin1 pin2 pin3).2 : ℤ) ≤ pin3) := by
  simp only [choosePrimesModeRange1]
  split_ifs <;> lia

private theorem choosePrimesModeRange2_le (n1 ne2 : ℕ) (pin2 pin3 : ℤ) :
    n1 ≤ (choosePrimesModeRange2 n1 ne2 pin2 pin3).1 ∧
      (choosePrimesModeRange2 n1 ne2 pin2 pin3).2 ≤ n1 + ne2 ∧
      (0 ≤ pin3 → (n1 : ℤ) ≤ pin3 → ((choosePrimesModeRange2 n1 ne2 pin2 pin3).2 : ℤ) ≤ pin3) := by
  simp only [choosePrimesModeRange2]
  split_ifs <;> lia

private theorem choosePrimesModeRange3_snd_le (n2 ne3 : ℕ) (pin3 : ℤ) :
    (choosePrimesModeRange3 n2 ne3 pin3).2 ≤ n2 + ne3 ∧
      (0 ≤ pin3 → (n2 : ℤ) ≤ pin3 → ((choosePrimesModeRange3 n2 ne3 pin3).2 : ℤ) ≤ pin3) := by
  simp only [choosePrimesModeRange3]
  split_ifs <;> lia

/-! ### The loops over the numbers of primes -/

-- The verification conditions of `JPoints.choosePrimesModeLoop3`, each in its shape.

private theorem loop3_pre {list1 list2 list3 : Array Cand} {n1 n2 n3hi : ℕ} {b : ModeBest}
    (h : b.best1.size = numPrimes ∧ b.best2.size = numPrimes ∧ b.best3.size = numPrimes ∧
      n1 ≤ numPrimes ∧ n2 - n1 ≤ numPrimes ∧ n3hi - n2 ≤ numPrimes) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [n2:n3hi + 1] = pref ++ cur :: suff) {x : ModeBest}
    (hx : x = b ∨ ∃ n3, n2 ≤ n3 ∧ n3 ≤ n3hi ∧ IsKept list1 list2 list3 n1 n2 n3 x) :
    x.best1.size = numPrimes ∧ x.best2.size = numPrimes ∧ x.best3.size = numPrimes ∧
      n1 ≤ numPrimes ∧ n2 - n1 ≤ numPrimes ∧ cur - n2 ≤ numPrimes := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, h4, h5, by lia⟩
  all_goals rcases hx with rfl | ⟨n3, -, -, hk⟩
  all_goals first | assumption | exact hk.best1.1 | exact hk.best2.1 | exact hk.best3.1

private theorem loop3_keep {list1 list2 list3 : Array Cand} {n1 n2 n3hi : ℕ} {b : ModeBest}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n2:n3hi + 1] = pref ++ cur :: suff)
    {x : ModeBest} (hk : IsKept list1 list2 list3 n1 n2 cur x) :
    x = b ∨ ∃ n3, n2 ≤ n3 ∧ n3 ≤ n3hi ∧ IsKept list1 list2 list3 n1 n2 n3 x :=
  .inr ⟨cur, by lia [Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl],
    by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hl], hk⟩

/-- The loop over `n3` from `n2` to `n3hi` keeps the cheapest choice `b` or a choice of `n3`
primes in it (`JPoints.IsKept`); which, depends on the `Float`s of the costs. -/
@[spec]
theorem choosePrimesModeLoop3_spec (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (prec : Array Entry) (st1 : FirstStage) (st2 : SecondStage) (list1 list2 list3 : Array Cand)
    (n1 n2 n3lo n3hi : ℕ) (b : ModeBest) :
    ⦃ b.best1.size = numPrimes ∧ b.best2.size = numPrimes ∧ b.best3.size = numPrimes ∧
      n1 ≤ numPrimes ∧ n2 - n1 ≤ numPrimes ∧ n3hi - n2 ≤ numPrimes ⦄
    choosePrimesModeLoop3 s t c prec st1 st2 list1 list2 list3 n1 n2 n3lo n3hi b
    ⦃ fun r ↦ r = b ∨ ∃ n3, n2 ≤ n3 ∧ n3 ≤ n3hi ∧ IsKept list1 list2 list3 n1 n2 n3 r ⦄ := by
  vcgen [choosePrimesModeLoop3] invariants
  · fun _ _ s ↦ s.2.2.2 = b ∨ ∃ n3, n2 ≤ n3 ∧ n3 ≤ n3hi ∧ IsKept list1 list2 list3 n1 n2 n3 s.2.2.2
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact .inl rfl
    | exact loop3_pre ‹_› ‹_› ‹_›
    | exact loop3_keep ‹_› ‹_›
    | assumption

-- The second stage, as a value: no contract reads it.
private theorem choosePrimesModeSecond_true (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs)
    (prec : Array Entry) (st : FirstStage) (s1 : Float) (list2 : Array Cand) (n1 n2 : ℕ) :
    ⦃ True ⦄ choosePrimesModeSecond s t c prec st s1 list2 n1 n2 ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

-- The verification conditions of `JPoints.choosePrimesModeLoop2`, each in its shape.

private theorem loop2_pre {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry} {list1 list2 : Array Cand}
    {n1 n2lo n2hi : ℕ} {used : Array Bool} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧ TwoStageCands nPrimes prec list1 n1 used list2 ∧ n1 ≤ n2lo ∧
      n2hi ≤ n1 + list2.size ∧ (0 ≤ pin3 → (n2hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n2lo:n2hi + 1] = pref ++ cur :: suff)
    {x : ModeBest} (hx : x.WF nPrimes pin3 prec) {list3 : Array Cand}
    (h3 : CandsWF (fun n ↦ n < nPrimes ∧ used[n]! = false ∧ ∀ k < cur - n1, list2[k]!.n ≠ n)
      list3) :
    x.best1.size = numPrimes ∧ x.best2.size = numPrimes ∧ x.best3.size = numPrimes ∧
      n1 ≤ numPrimes ∧ cur - n1 ≤ numPrimes ∧
      (choosePrimesModeRange3 cur list3.size pin3).2 - cur ≤ numPrimes := by
  obtain ⟨-, hc, -, hn2, -, hn⟩ := h
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have := (choosePrimesModeRange3_snd_le cur list3.size pin3).1
  exact ⟨hx.size_best1, hx.size_best2, hx.size_best3, by lia [hc.n1_le, hc.size_list1_le],
    by lia [hc.size_list2_le], by lia [h3.size_le fun _ _ hP ↦ hP.1]⟩

private theorem loop2_post_loop3 {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry}
    {list1 list2 : Array Cand} {n1 n2lo n2hi : ℕ} {used : Array Bool} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧ TwoStageCands nPrimes prec list1 n1 used list2 ∧ n1 ≤ n2lo ∧
      n2hi ≤ n1 + list2.size ∧ (0 ≤ pin3 → (n2hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n2lo:n2hi + 1] = pref ++ cur :: suff)
    {x : ModeBest} (hx : x.WF nPrimes pin3 prec) {list3 : Array Cand}
    (h3 : CandsWF (fun n ↦ n < nPrimes ∧ used[n]! = false ∧ ∀ k < cur - n1, list2[k]!.n ≠ n)
      list3) {y : ModeBest}
    (hy : y = x ∨ ∃ n3, cur ≤ n3 ∧ n3 ≤ (choosePrimesModeRange3 cur list3.size pin3).2 ∧
      IsKept list1 list2 list3 n1 cur n3 y) : y.WF nPrimes pin3 prec := by
  obtain ⟨-, hc, h1, hn2, hpin, -⟩ := h
  rcases hy with rfl | ⟨n3, h23, h3hi, hk⟩
  · exact hx
  have hlo := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hhi := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hr1, hr2⟩ := choosePrimesModeRange3_snd_le cur list3.size pin3
  exact hk.wf hc h3 (by lia) (by lia) (by lia) h23
    fun hp ↦ by lia [hpin hp, hr2 hp (by lia [hpin hp])]

/-- The loop over `n2` from `n2lo` to `n2hi` keeps a cheapest choice of primes of at most
`MAX_TABLE_PRIME` in the first two stages (`JPoints.ModeBest.WF`), from the candidates of the first
two stages (`JPoints.TwoStageCands`) after the first stage `st1` of `n1` primes, for every value
of the `Float`s of the costs. -/
@[spec]
theorem choosePrimesModeLoop2_spec (g : ChoiceGlobals) (s : ModeShape) (t : PrimeTerms)
    (prec : Array Entry) (st1 : FirstStage) (s1 : Float) (list1 list2 : Array Cand)
    (n1 n2lo n2hi : ℕ) (b : ModeBest) :
    ⦃ b.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec ∧
      TwoStageCands g.input.numPrimes.toNat prec list1 n1 st1.used list2 ∧ n1 ≤ n2lo ∧
      n2hi ≤ n1 + list2.size ∧ (0 ≤ g.input.sievePrimes3 → (n2hi : ℤ) ≤ g.input.sievePrimes3) ∧
      g.input.numPrimes.toNat ≤ numPrimes ⦄
    choosePrimesModeLoop2 g s t prec st1 s1 list1 list2 n1 n2lo n2hi b
    ⦃ fun r ↦ r.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec ⦄ := by
  vcgen [choosePrimesModeLoop2, choosePrimesModeSecond_true] invariants
  · fun _ _ b ↦ b.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec
  all_goals with_reducible first
    | exact ‹_ ∧ _›.1
    | exact loop2_pre ‹_› ‹_› ‹_› ‹_›
    | exact loop2_post_loop3 ‹_› ‹_› ‹_› ‹_› ‹_›

-- The verification conditions of `JPoints.choosePrimesModeLoop1`, each in its shape.

private theorem loop1_init {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry} {list1 : Array Cand}
    {n1hi : ℕ} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧
      CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) list1 ∧ n1hi ≤ list1.size ∧
      (0 ≤ pin3 → (n1hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes) :
    (Array.replicate numPrimes false).size = numPrimes ∧
      (∀ n, (Array.replicate numPrimes false)[n]! = true → n < nPrimes) ∧
      b.WF nPrimes pin3 prec :=
  ⟨Array.size_replicate, fun n hn ↦
    absurd ((Array.getElem!_replicate_default (α := Bool) numPrimes n).symm.trans hn)
      Bool.false_ne_true, h.1⟩

private theorem loop1_pre_first {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry}
    {list1 : Array Cand} {n1lo n1hi : ℕ} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧
      CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) list1 ∧ n1hi ≤ list1.size ∧
      (0 ≤ pin3 → (n1hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n1lo:n1hi + 1] = pref ++ cur :: suff)
    {used : Array Bool} {x : ModeBest}
    (hu : used.size = numPrimes ∧ (∀ n, used[n]! = true → n < nPrimes) ∧
      x.WF nPrimes pin3 prec) :
    used.size = numPrimes ∧ nPrimes ≤ numPrimes ∧ (∀ n, used[n]! = true → n < nPrimes) ∧
      ∀ k < cur, list1[k]!.n < nPrimes := by
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  exact ⟨hu.1, h.2.2.2.2, hu.2.1, fun k hk ↦ (h.2.1.prop (by lia)).1⟩

private theorem loop1_pre_loop2 {nPrimes : ℕ} {pin2 pin3 : ℤ} {prec : Array Entry}
    {list1 : Array Cand} {n1lo n1hi : ℕ} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧
      CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) list1 ∧ n1hi ≤ list1.size ∧
      (0 ≤ pin3 → (n1hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n1lo:n1hi + 1] = pref ++ cur :: suff)
    {used : Array Bool} {x : ModeBest}
    (hu : used.size = numPrimes ∧ (∀ n, used[n]! = true → n < nPrimes) ∧
      x.WF nPrimes pin3 prec) {used' : Array Bool} (hu' : IsUsed list1 cur used')
    {list2 : Array Cand}
    (h2 : CandsWF (fun n ↦ used'[n]! = false ∧ ∃ k < list1.size, list1[k]!.n = n) list2) :
    x.WF nPrimes pin3 prec ∧ TwoStageCands nPrimes prec list1 cur used' list2 ∧
      cur ≤ (choosePrimesModeRange2 cur list2.size pin2 pin3).1 ∧
      (choosePrimesModeRange2 cur list2.size pin2 pin3).2 ≤ cur + list2.size ∧
      (0 ≤ pin3 → ((choosePrimesModeRange2 cur list2.size pin2 pin3).2 : ℤ) ≤ pin3) ∧
      nPrimes ≤ numPrimes := by
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hr1, hr2, hr3⟩ := choosePrimesModeRange2_le cur list2.size pin2 pin3
  exact ⟨hu.2.2, ⟨h.2.1, by lia, hu', h2⟩, hr1, hr2,
    fun hp ↦ hr3 hp (by lia [h.2.2.2.1 hp]), h.2.2.2.2⟩

private theorem loop1_post_loop2 {nPrimes : ℕ} {pin3 : ℤ} {prec : Array Entry} {list1 : Array Cand}
    {n1lo n1hi : ℕ} {b : ModeBest}
    (h : b.WF nPrimes pin3 prec ∧
      CandsWF (fun n ↦ n < nPrimes ∧ prec[n]!.p ≤ maxTablePrime) list1 ∧ n1hi ≤ list1.size ∧
      (0 ≤ pin3 → (n1hi : ℤ) ≤ pin3) ∧ nPrimes ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [n1lo:n1hi + 1] = pref ++ cur :: suff)
    {used' : Array Bool} (hu' : IsUsed list1 cur used') {y : ModeBest}
    (hy : y.WF nPrimes pin3 prec) :
    used'.size = numPrimes ∧ (∀ n, used'[n]! = true → n < nPrimes) ∧ y.WF nPrimes pin3 prec := by
  refine ⟨hu'.1, fun n hn ↦ ?_, hy⟩
  obtain ⟨k, hk, rfl⟩ := (hu'.2 n).mp hn
  exact (h.2.1.prop (by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hl])).1

/-- The loop over `n1` from `n1lo` to `n1hi` keeps a cheapest choice of primes of at most
`MAX_TABLE_PRIME` in the first two stages (`JPoints.ModeBest.WF`), from the candidates `list1` of
the first stage, for every value of the `Float`s of the costs: the first stage of each `n1`
(`JPoints.choosePrimesModeFirst_spec`), the ranking of the second
(`JPoints.choosePrimesModeList2_spec`) and the loop over `n2`
(`JPoints.choosePrimesModeLoop2_spec`). -/
@[spec]
theorem choosePrimesModeLoop1_spec (g : ChoiceGlobals) (s : ModeShape) (t : PrimeTerms)
    (prec : Array Entry) (list1 : Array Cand) (n1lo n1hi : ℕ) (b : ModeBest) :
    ⦃ b.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec ∧
      CandsWF (fun n ↦ n < g.input.numPrimes.toNat ∧ prec[n]!.p ≤ maxTablePrime) list1 ∧
      n1hi ≤ list1.size ∧ (0 ≤ g.input.sievePrimes3 → (n1hi : ℤ) ≤ g.input.sievePrimes3) ∧
      g.input.numPrimes.toNat ≤ numPrimes ⦄
    choosePrimesModeLoop1 g s t prec list1 n1lo n1hi b
    ⦃ fun r ↦ r.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec ⦄ := by
  vcgen [choosePrimesModeLoop1] invariants
  · fun _ _ s ↦ s.1.size = numPrimes ∧ (∀ n, s.1[n]! = true → n < g.input.numPrimes.toNat) ∧
      s.2.WF g.input.numPrimes.toNat g.input.sievePrimes3 prec
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact loop1_init ‹_›
    | exact ‹_ ∧ _ ∧ _›.2.2
    | exact loop1_pre_first ‹_› ‹_› ‹_›
    | exact ‹_ ∧ CandsWF _ _ ∧ _›.2.1.nodup
    | exact loop1_pre_loop2 ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact loop1_post_loop2 ‹_› ‹_› ‹_› ‹_›

-- The terms of the primes, as a value: no contract reads them.
private theorem choosePrimesModeTerms_true (c : Cli.Costs) (prec : Array Entry) (nPrimes : ℕ) :
    ⦃ True ⦄ choosePrimesModeTerms c prec nPrimes ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The plan `pnn` of the primes of the first `m` positions of the cheapest choice `b` by their
indices in `prec`: `pnn` keeps its size, and holds at these positions the indices in the table of
the primes of their records. -/
def PnnUpTo (prec : Array Entry) (b : ModeBest) (m : ℕ) (pnn : Array ℕ) : Prop :=
  pnn.size = numPrimes + 1 ∧ ∀ j < m, pnn[j]! = prec[b.idx j]!.n

namespace PnnUpTo

variable {prec : Array Entry} {b : ModeBest} {pnn : Array ℕ}

theorem nil (h : pnn.size = numPrimes + 1) : PnnUpTo prec b ([] : List ℕ).length pnn :=
  ⟨h, fun _ hj ↦ absurd hj (Nat.not_lt_zero _)⟩

theorem set! {m : ℕ} (h : PnnUpTo prec b m pnn) (hm : m < numPrimes + 1) {v : ℕ}
    (hv : v = prec[b.idx m]!.n) : PnnUpTo prec b (m + 1) (pnn.set! m v) := by
  refine ⟨by rw [Array.size_set!, h.1], fun j hj ↦ ?_⟩
  rcases (show j < m ∨ j = m by lia) with hj | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h.2 j hj]
  · rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; exact hm), hv]

-- The steps of the three loops of `JPoints.choosePrimesMode` that write `pnn`, in their shapes.

private theorem set!_first {nPrimes : ℕ} {pin3 : ℤ} (hb : b.WF nPrimes pin3 prec)
    (hn : nPrimes ≤ numPrimes) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:b.b1] = pref ++ cur :: suff) (h : PnnUpTo prec b pref.length pnn) :
    PnnUpTo prec b (pref ++ [cur]).length (pnn.set! cur prec[b.best1[cur]!]!.n) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have := hb.stages.sp3_le
  have := hb.stages.sp1_le_sp2
  have := hb.stages.sp2_le_sp3
  rw [List.length_append, List.length_singleton]
  exact hc ▸ h.set! (by lia) (by simp only [ModeBest.idx, hc, hlt, ↓reduceIte])

private theorem set!_second {nPrimes : ℕ} {pin3 : ℤ} (hb : b.WF nPrimes pin3 prec)
    (hn : nPrimes ≤ numPrimes) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:b.b2 - b.b1] = pref ++ cur :: suff)
    (h : PnnUpTo prec b (b.b1 + pref.length) pnn) :
    PnnUpTo prec b (b.b1 + (pref ++ [cur]).length)
      (pnn.set! (b.b1 + cur) prec[b.best2[cur]!]!.n) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  subst hc
  rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
  refine h.set! (by lia [hb.stages.sp3_le, hb.stages.sp2_le_sp3]) ?_
  simp only [ModeBest.idx, show ¬b.b1 + pref.length < b.b1 by lia,
    show b.b1 + pref.length < b.b2 by lia, ↓reduceIte, Nat.add_sub_cancel_left]

private theorem set!_third {nPrimes : ℕ} {pin3 : ℤ} (hb : b.WF nPrimes pin3 prec)
    (hn : nPrimes ≤ numPrimes) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:b.b3 - b.b2] = pref ++ cur :: suff)
    (h : PnnUpTo prec b (b.b2 + pref.length) pnn) :
    PnnUpTo prec b (b.b2 + (pref ++ [cur]).length)
      (pnn.set! (b.b2 + cur) prec[b.best3[cur]!]!.n) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  subst hc
  rw [List.length_append, List.length_singleton, ← Nat.add_assoc]
  refine h.set! (by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hl, hb.stages.sp3_le]) ?_
  simp only [ModeBest.idx, show ¬b.b2 + pref.length < b.b1 by lia [hb.stages.sp1_le_sp2],
    show ¬b.b2 + pref.length < b.b2 by lia, ↓reduceIte, Nat.add_sub_cancel_left]

private theorem first_second (h : PnnUpTo prec b (ForIn.toList [:b.b1]).length pnn) :
    PnnUpTo prec b (b.b1 + ([] : List ℕ).length) pnn := by
  rwa [Std.Legacy.Range.length_toList_zero_start] at h

private theorem second_third (hb : b.b1 ≤ b.b2)
    (h : PnnUpTo prec b (b.b1 + (ForIn.toList [:b.b2 - b.b1]).length) pnn) :
    PnnUpTo prec b (b.b2 + ([] : List ℕ).length) pnn := by
  rwa [Std.Legacy.Range.length_toList_zero_start, Nat.add_sub_cancel' hb] at h

/-- The plan `pnn` of the primes of the cheapest choice `b` by their indices in `prec` is a choice
of sieving primes by their indices in the table of the primes (`JPoints.IsStages`). -/
private theorem isStages {nPrimes : ℕ} {pin3 : ℤ} (hb : b.WF nPrimes pin3 prec)
    (hp : PrecWF nPrimes prec)
    (h : PnnUpTo prec b (b.b2 + (ForIn.toList [:b.b3 - b.b2]).length) pnn) :
    IsStages nPrimes pin3 (fun n ↦ primeTable[n]! ≤ maxTablePrime) (fun x ↦ pnn[x]!) b.b1 b.b2
      b.b3 ∧ pnn.size = numPrimes + 1 := by
  rw [Std.Legacy.Range.length_toList_zero_start, Nat.add_sub_cancel' hb.stages.sp2_le_sp3]
    at h
  exact ⟨hb.stages.prec hp h.2, h.1⟩

end PnnUpTo

/-- `choose_primes_mode` makes a choice of sieving primes of at most `MAX_TABLE_PRIME` in the
first two stages among the first `nPrimes` primes of the table (`JPoints.IsStages`), for every
value of the `Float`s of the cost model, from records `prec` of the first `nPrimes` primes
(`JPoints.PrecWF`), and leaves the mode of the plan as it is. -/
@[spec]
theorem choosePrimesMode_spec (mode : ℕ) (cut : Bool) (g : ChoiceGlobals) (prec : Array Entry)
    (plan : Plan) :
    ⦃ PrecWF g.input.numPrimes.toNat prec ∧ g.input.numPrimes.toNat ≤ numPrimes ∧
      plan.pnn.size = numPrimes + 1 ⦄
    choosePrimesMode mode cut g prec plan
    ⦃ fun r ↦ IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (r.2.pnn[·]!) r.2.sievePrimes1
        r.2.sievePrimes2 r.2.sievePrimes3 ∧ r.2.sieveMode = plan.sieveMode ∧
        r.2.pnn.size = numPrimes + 1 ⦄ := by
  vcgen [choosePrimesMode, choosePrimesModeTerms_true] invariants
  · fun pref _ pnn ↦ PnnUpTo prec b pref.length pnn
  · fun pref _ pnn ↦ PnnUpTo prec b (b.b1 + pref.length) pnn
  · fun pref _ pnn ↦ PnnUpTo prec b (b.b2 + pref.length) pnn
  all_goals obtain ⟨hp, hn, hs⟩ := ‹PrecWF _ prec ∧ _›
  all_goals with_reducible first
    | exact ⟨ModeBest.wf_initial _ _ _, ‹_›,
        (choosePrimesModeRange1_snd_le _ _ _ _).1, (choosePrimesModeRange1_snd_le _ _ _ _).2, hn⟩
    | exact PnnUpTo.nil hs
    | exact PnnUpTo.first_second ‹_›
    | exact PnnUpTo.second_third ‹ModeBest.WF _ _ _ _›.stages.sp1_le_sp2 ‹_›
    | exact PnnUpTo.isStages ‹_› hp ‹_›
    | exact PnnUpTo.set!_first ‹_› hn ‹_› ‹_›
    | exact PnnUpTo.set!_second ‹_› hn ‹_› ‹_›
    | exact PnnUpTo.set!_third ‹_› hn ‹_› ‹_›

/-! ### The choice -/

/-- The invariant of the loop of `JPoints.choosePrimes` over the modes, for the globals `g`: the
plan `plan` keeps the size of `pnn`, and the numbers `b1`, `b2`, `b3` and the primes `pn` of the
cheapest mode so far are a choice of sieving primes (`JPoints.IsStages`), whose mode, the one of the
plan, is that of a mode priced, unless there are none: the box or the region, or the tube for a
bounded fourth coordinate. -/
structure ChoiceInvariant (g : ChoiceGlobals) (plan : Plan) (b1 b2 b3 : ℕ) (pn : Array ℕ) :
    Prop where
  /-- The size of `pnn`. -/
  size_pnn : plan.pnn.size = numPrimes + 1
  /-- The size of `pn`. -/
  size_pn : pn.size = numPrimes
  /-- The sieving primes. -/
  stages : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
    (fun n ↦ primeTable[n]! ≤ maxTablePrime) (pn[·]!) b1 b2 b3
  /-- The mode. -/
  mode : b3 = 0 ∨ plan.sieveMode ≤ 2 ∧ (plan.sieveMode = 1 → g.input.dbounded = true)

-- The modes that `JPoints.choosePrimes` prices: the box and the region, and the tube only for a
-- bounded fourth coordinate.
private theorem mode_le {g : ChoiceGlobals} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:if g.input.dbounded = true then 4 else 2] = pref ++ cur :: suff) :
    #[0, 2, 1, 1][cur]! ≤ 2 ∧ (#[0, 2, 1, 1][cur]! = 1 → g.input.dbounded = true) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  cases hd : g.input.dbounded <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc
  all_goals interval_cases cur <;> decide

-- The verification conditions of `JPoints.choosePrimes`, each in its shape.

private theorem choiceInvariant_init {g : ChoiceGlobals} {plan : Plan}
    (h : plan.pnn.size = numPrimes + 1) :
    ChoiceInvariant g plan 0 0 0 (.replicate numPrimes 0) :=
  ⟨h, Array.size_replicate, .zero _ _ _ _, .inl rfl⟩

private theorem choiceInvariant_skip {g : ChoiceGlobals} {plan plan' : Plan} {b1 b2 b3 : ℕ}
    {pn : Array ℕ} (h : ChoiceInvariant g plan b1 b2 b3 pn) {P : Prop}
    (hm : P ∧ plan'.sieveMode = plan.sieveMode ∧ plan'.pnn.size = numPrimes + 1) :
    ChoiceInvariant g plan' b1 b2 b3 pn :=
  ⟨hm.2.2, h.size_pn, h.stages, hm.2.1 ▸ h.mode⟩

private theorem choiceInvariant_take {g : ChoiceGlobals} {plan plan' : Plan} {pn' : Array ℕ}
    {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:if g.input.dbounded = true then 4 else 2] = pref ++ cur :: suff)
    (hm : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! plan'.pnn) plan'.sievePrimes1
        plan'.sievePrimes2 plan'.sievePrimes3 ∧
      plan'.sieveMode = plan.sieveMode ∧ plan'.pnn.size = numPrimes + 1)
    (hpn : SetLoopInvariant numPrimes (fun n x ↦ x = plan'.pnn[n]!)
      (ForIn.toList [:plan'.sievePrimes3]).length pn') (cut : Bool) :
    ChoiceInvariant g { plan' with sieveMode := #[0, 2, 1, 1][cur]!, tubeCut := cut }
      plan'.sievePrimes1 plan'.sievePrimes2 plan'.sievePrimes3 pn' :=
  ⟨hm.2.2, hpn.1, hm.1.congr fun j hj ↦ hpn.of_toList.2 j hj, .inr (mode_le hl)⟩

private theorem choosePrimes_pre_copy {g : ChoiceGlobals} {plan plan' : Plan} {b1 b2 b3 : ℕ}
    {pn : Array ℕ} (h : ChoiceInvariant g plan b1 b2 b3 pn) :
    SetLoopInvariant numPrimes (fun n x ↦ x = plan'.pnn[n]!) ([] : List ℕ).length pn :=
  setLoopInvariant_nil _ h.size_pn

private theorem choosePrimes_copy {g : ChoiceGlobals} (hn : g.input.numPrimes.toNat ≤ numPrimes)
    {plan' : Plan} {P : Prop}
    (hm : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! plan'.pnn) plan'.sievePrimes1
        plan'.sievePrimes2 plan'.sievePrimes3 ∧ P)
    {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:plan'.sievePrimes3] = pref ++ cur :: suff) {pn : Array ℕ}
    (h : SetLoopInvariant numPrimes (fun n x ↦ x = plan'.pnn[n]!) pref.length pn) :
    SetLoopInvariant numPrimes (fun n x ↦ x = plan'.pnn[n]!) (pref ++ [cur]).length
      (pn.set! cur plan'.pnn[cur]!) :=
  h.set! hl (hm.1.sp3_le.trans hn) rfl

private theorem choosePrimes_post {g : ChoiceGlobals} {plan : Plan} {b1 b2 b3 : ℕ}
    {pn : Array ℕ} (h : ChoiceInvariant g plan b1 b2 b3 pn) {pnn : Array ℕ}
    (hpnn : SetLoopInvariant (numPrimes + 1) (fun n x ↦ x = pn[n]!) (ForIn.toList [:b3]).length
      pnn) :
    IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (fun x ↦ pnn[x]!) b1 b2 b3 ∧
      (b3 = 0 ∨ plan.sieveMode ≤ 2 ∧ (plan.sieveMode = 1 → g.input.dbounded = true)) :=
  ⟨h.stages.congr fun j hj ↦ hpnn.of_toList.2 j hj, h.mode⟩

/-- `choose_primes` makes a choice of sieving primes of at most `MAX_TABLE_PRIME` in the first two
stages among the first `nPrimes` primes of the table (`JPoints.IsStages`), for every value of the
`Float`s of the cost model, from records `prec` of the first `nPrimes` primes (`JPoints.PrecWF`):
that of the cheapest mode, by `JPoints.choosePrimesMode_spec`, and when it has sieving primes, the
mode of the plan is the box or the region, or the tube for a bounded fourth coordinate. -/
@[spec]
theorem choosePrimes_spec (g : ChoiceGlobals) (prec : Array Entry) (plan : Plan) :
    ⦃ PrecWF g.input.numPrimes.toNat prec ∧ g.input.numPrimes.toNat ≤ numPrimes ∧
      plan.pnn.size = numPrimes + 1 ⦄
    choosePrimes g prec plan
    ⦃ fun r ↦ IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (r.pnn[·]!) r.sievePrimes1 r.sievePrimes2
        r.sievePrimes3 ∧
        (r.sievePrimes3 = 0 ∨ r.sieveMode ≤ 2 ∧ (r.sieveMode = 1 → g.input.dbounded = true)) ⦄ := by
  vcgen [choosePrimes] invariants
  | inv1 => fun _ _ s ↦ ChoiceInvariant g s.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2
  | inv2 _ _ _ _ _ pn _ => fun pref _ pnn ↦
      SetLoopInvariant (numPrimes + 1) (fun n x ↦ x = pn[n]!) pref.length pnn
  | inv3 _ plan' _ _ => fun pref _ pn ↦
      SetLoopInvariant numPrimes (fun n x ↦ x = plan'.pnn[n]!) pref.length pn
  all_goals try dsimp only at *
  all_goals obtain ⟨hp, hn, hs⟩ := ‹PrecWF _ prec ∧ _›
  all_goals with_reducible first
    | exact choiceInvariant_init hs
    | exact setLoopInvariant_nil _ ‹ChoiceInvariant _ _ _ _ _ _›.size_pnn
    | exact choosePrimes_post ‹_› ‹_›
    | exact ‹SetLoopInvariant _ _ _ _›.set! ‹_›
        (by lia [‹ChoiceInvariant _ _ _ _ _ _›.stages.sp3_le]) rfl
    | exact ⟨hp, hn, ‹ChoiceInvariant _ _ _ _ _ _›.size_pnn⟩
    | exact choosePrimes_pre_copy ‹_›
    | exact choiceInvariant_take ‹_› ‹_› ‹_› _
    | exact choosePrimes_copy hn ‹_› ‹_› ‹_›
    | exact choiceInvariant_skip ‹_› ‹_›

/-! ### The tables of the primes chosen -/

/-- The invariant of the loop of `JPoints.initFmodpsquareTables` over the sieving primes, after the
first `k`, for the curve with the coefficients `cs` and the degree `deg` that `init_table` is given
and the first `nPrimes` primes of the table: the table of the third stage keeps its size and
`tabled` its size, the tables of the curve hold at the first `nPrimes` primes, the rows of the third
stage where `tabled` says so, and `tabled` holds at the first `k` sieving primes. -/
structure TablesInvariant (cs : List ℤ) (deg nPrimes : ℕ) (pnn : Array ℕ) (k : ℕ)
    (ct : CurveTables) (tabled : Array Bool) : Prop where
  /-- The size of the table of the third stage. -/
  size_isPointOnJ : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven
  /-- The size of `tabled`. -/
  size_tabled : tabled.size = numPrimes
  /-- The tables of the curve at the primes considered. -/
  primeWF {pn : ℕ} (hpn : pn < nPrimes) : ct.PrimeWF cs pn
  /-- The rows of the third stage of the primes whose rows are filled. -/
  rowsWF {pn : ℕ} (h : tabled[pn]! = true) : ct.RowsWF cs deg pn
  /-- The rows of the first `k` sieving primes are filled. -/
  tabled {j : ℕ} (hj : j < k) : tabled[pnn[j]!]! = true

namespace TablesInvariant

variable {cs : List ℤ} {deg nPrimes : ℕ} {pnn : Array ℕ}

private theorem pre {t : Tables} (ht : t.WF) (hd : deg ≤ 6) (hn : nPrimes ≤ numPrimes)
    {sp3 : ℕ} (hpnn : ∀ n < sp3, pnn[n]! < nPrimes) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) {ct : CurveTables} {tabled : Array Bool}
    (h : TablesInvariant cs deg nPrimes pnn pref.length ct tabled) :
    t.WF ∧ pnn[cur]! < numPrimes ∧ deg ≤ 6 ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven :=
  ⟨ht, by lia [hpnn cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)], hd, h.size_isPointOnJ⟩

-- The flags of the sieving primes after the rows of the next are filled.
private theorem tabled_set! {tabled : Array Bool} (hs : tabled.size = numPrimes) {k : ℕ}
    (h : ∀ j < k, tabled[pnn[j]!]! = true) (hk : pnn[k]! < numPrimes) {j : ℕ} (hj : j < k + 1) :
    (tabled.set! pnn[k]! true)[pnn[j]!]! = true := by
  by_cases hp : pnn[j]! = pnn[k]!
  · rw [hp, Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hk)]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hp)]
    exact h j (lt_of_le_of_ne (Nat.le_of_lt_succ hj) fun he ↦ hp (he ▸ rfl))

theorem initTable (hn : nPrimes ≤ numPrimes) {sp3 : ℕ} (hpnn : ∀ n < sp3, pnn[n]! < nPrimes)
    {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) {ct ct' : CurveTables}
    {tabled : Array Bool} (h : TablesInvariant cs deg nPrimes pnn pref.length ct tabled)
    (hc : ∀ cs', (∀ n ≤ 6, ct.coeffsModP[pnn[cur]! * 8 + n]! = cs'.getD n 0 %
        primeTable[pnn[cur]!]!) →
      ct'.coeffsModP = ct.coeffsModP ∧ ct'.hasInfinity = ct.hasInfinity ∧
        ct'.isFSquare = ct.isFSquare ∧ ct.EqOff ct' pnn[cur]! ∧ ct'.RowsWF cs' deg pnn[cur]!) :
    TablesInvariant cs deg nPrimes pnn (pref ++ [cur]).length ct' (tabled.set! pnn[cur]! true) := by
  have hlt := hpnn cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  have hc' := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  obtain ⟨h1, h2, h3, he, hr⟩ := hc cs fun _ hn ↦ (h.primeWF hlt).coeffsModP hn
  refine ⟨he.size_isPointOnJ.trans h.size_isPointOnJ, by rw [Array.size_set!, h.size_tabled],
    fun hpn ↦ (h.primeWF hpn).of_eq h1 h2 h3, fun {pn} hpn ↦ ?_,
    fun {j} hj ↦ ?_⟩
  · by_cases hp : pn = pnn[cur]!
    · exact hp ▸ hr
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hp)] at hpn
      exact he.rowsWF hp (h.rowsWF hpn)
  · rw [List.length_append, List.length_singleton, hc'] at hj
    exact tabled_set! h.size_tabled (hc' ▸ fun j hj ↦ h.tabled hj) (by lia) hj

theorem skip {pref suff : List ℕ} {cur sp3 : ℕ} (hl : ForIn.toList [:sp3] = pref ++ cur :: suff)
    {ct : CurveTables} {tabled : Array Bool}
    (h : TablesInvariant cs deg nPrimes pnn pref.length ct tabled)
    (hc : ¬(!tabled[pnn[cur]!]!) = true) :
    TablesInvariant cs deg nPrimes pnn (pref ++ [cur]).length ct tabled := by
  have hc' := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨h.size_isPointOnJ, h.size_tabled, h.primeWF, h.rowsWF, fun {j} hj ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hc'] at hj
  rcases (show j < cur ∨ j = cur by lia) with hj | rfl
  · exact h.tabled (hc' ▸ hj)
  · simpa using hc

/-- The tables of the curve and the records of the primes considered that
`JPoints.initFmodpsquareRates_spec` leaves are the invariant before the first sieving prime. -/
theorem of_ratesWF {r : Rates} {ct : CurveTables} (h : r.WF ct cs deg nPrimes) :
    TablesInvariant cs deg nPrimes pnn 0 ct r.tabled :=
  ⟨h.size_isPointOnJ, h.size_tabled, h.primeWF, h.rowsWF, fun hj ↦ absurd hj (Nat.not_lt_zero _)⟩

theorem wf {sp3 : ℕ} {ct : CurveTables} {tabled : Array Bool}
    (h : TablesInvariant cs deg nPrimes pnn (ForIn.toList [:sp3]).length ct tabled) :
    ct.WF cs deg nPrimes pnn sp3 :=
  .of_primeWF (fun _ hpn ↦ h.primeWF hpn)
    fun _ hk ↦ h.rowsWF (h.tabled (by rwa [Std.Legacy.Range.length_toList_zero_start]))

end TablesInvariant

/-- `init_fmodpsquare` fills the rows of the third stage of the sieving primes of the plan `plan`
whose rows `tabled` does not say are filled, for the curve with the coefficients `cs` and the degree
`deg ≤ 6` that `init_table` is given, whose tables at the first `nPrimes` primes of the table `ct`
holds, when the sieving primes are among them: the tables of the curve for the plan
(`JPoints.CurveTables.WF`), each row by `JPoints.initTable_spec` (`JPoints.TablesInvariant`). -/
theorem initFmodpsquareTables_spec_of_tablesInvariant (cs : List ℤ) (nPrimes : ℕ)
    (t : Tables)
    (ct : CurveTables) (deg : ℕ) (plan : Plan) (tabled : Array Bool) :
    ⦃ t.WF ∧ deg ≤ 6 ∧ nPrimes ≤ numPrimes ∧ (∀ n < plan.sievePrimes3, plan.pnn[n]! < nPrimes) ∧
      TablesInvariant cs deg nPrimes plan.pnn ([] : List ℕ).length ct tabled ⦄
    initFmodpsquareTables t ct deg plan tabled
    ⦃ fun r ↦ r.1.WF cs deg nPrimes plan.pnn plan.sievePrimes3 ⦄ := by
  vcgen [initFmodpsquareTables] invariants
  · fun pref _ s ↦ TablesInvariant cs deg nPrimes plan.pnn pref.length s.1 s.2
  all_goals try dsimp only at *
  all_goals obtain ⟨ht, hd, hn, hpnn, -⟩ := ‹t.WF ∧ _›
  all_goals with_reducible first
    | exact ‹_ ∧ _ ∧ _ ∧ _ ∧ _›.2.2.2.2
    | exact TablesInvariant.wf ‹_›
    | exact TablesInvariant.pre ht hd hn hpnn ‹_› ‹_›
    | exact TablesInvariant.initTable hn hpnn ‹_› ‹_› ‹_›
    | exact TablesInvariant.skip ‹_› ‹_› ‹_›

/-- The tables of the primes chosen, by `JPoints.initFmodpsquareTables_spec_of_tablesInvariant` for
every curve and number of primes considered. -/
@[spec]
theorem initFmodpsquareTables_spec (t : Tables) (ct : CurveTables) (deg : ℕ) (plan : Plan)
    (tabled : Array Bool) :
    ⦃ t.WF ∧ deg ≤ 6 ⦄
    initFmodpsquareTables t ct deg plan tabled
    ⦃ fun r ↦ ∀ cs nPrimes, nPrimes ≤ numPrimes →
        (∀ n < plan.sievePrimes3, plan.pnn[n]! < nPrimes) →
        TablesInvariant cs deg nPrimes plan.pnn 0 ct tabled →
        r.1.WF cs deg nPrimes plan.pnn plan.sievePrimes3 ⦄ :=
  ⟨fun ⟨ht, hd⟩ cs nPrimes hn hpnn h ↦
    (initFmodpsquareTables_spec_of_tablesInvariant cs nPrimes t ct deg plan tabled).le_wp
      ⟨ht, hd, hn, hpnn, h⟩⟩

end JPoints

end
