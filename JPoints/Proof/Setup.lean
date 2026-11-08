/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Spec.Sturm
public import Std.WP

import JPoints.Proof.Choice
import JPoints.Proof.Constants
import JPoints.Proof.Loops
import JPoints.Proof.Poly
import JPoints.Proof.Rows
import JPoints.Proof.Sample
import JPoints.Proof.SiftData
import JPoints.Proof.Sturm
import JPoints.Proof.Transform
import JPoints.Proof.TwoAdic
import JPoints.Proof.Values
import Std.Tactic.Do

/-!
# The contracts of the set-up of the search

What the set-up of `j-points` leaves for the search, in the terms of the reference layer and of the
predicates of the globals: the curve searched of `normalise_curve` is that of the specification
(`JPoints.searchedCurve`, `JPoints.normalizeCurve_spec`); the tables of `init_main`
(`JPoints.initMain_spec`); the choice of the sieve by `init_fmodpsquare`, for every value of the
`Float`s of the cost model (`JPoints.IsChoice`, `JPoints.initFmodpsquare_spec`), from the rates of
the primes (`JPoints.initFmodpsquareRates_spec`), the choice of the primes
(`JPoints.choosePrimes_spec`) and the tables of the primes chosen
(`JPoints.initFmodpsquareTables_spec`), with the text that it prints (`JPoints.choiceText`), none
under `-q`; the sieve tables of `init_sieve` (`JPoints.initSieve_spec`); the static data of
`init_sift` (`JPoints.initSift_spec`); the condition at 2 of `twoadic_init`, which admits every
point (`JPoints.twoadicInit_spec`, `JPoints.TwoAdic.sound_initial`); the intervals of
`real_roots_init`, on which `f` is negative by Sturm's theorem (`JPoints.realRootsInit_spec`); and
what `tube_init` leaves (`JPoints.tubeInit_spec`).

## Main definitions

* `JPoints.searchedCurve`: the curve searched of the specification.
* `JPoints.IsChoice`: what the choice of the sieve leaves.
* `JPoints.choiceText`: the text that the choice of the sieve prints.

## Main statements

* `JPoints.fst_run_normalizeCurve`: the curve that `normalise_curve` makes is that of the
  specification.
* `JPoints.normalizeCurve_spec`, `JPoints.initMain_spec`, `JPoints.initFmodpsquare_spec`,
  `JPoints.initSieve_spec`, `JPoints.initSift_spec`, `JPoints.twoadicInit_spec`,
  `JPoints.realRootsInit_spec`, `JPoints.tubeInit_spec`: the contracts of the set-up.
* `JPoints.initFmodpsquare_isChoice`: the choice of the sieve, whatever the `Float`s.
* `JPoints.choiceText_of_quiet`: the choice prints nothing under `-q`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. The contract of
`normalise_curve` follows from its value (`Std.WP.Id.triple_of_run`), which `simp` computes on seven
coefficients, its two loops included, and compares with the cases of `JPoints.searchedCoeffs_eq`.
The components that the set-up calls once with the initial values of the structures that they fill
(`JPoints.CurveTables.initial`, `JPoints.SieveTables.initial`, `JPoints.TwoAdic.initial`) have
contracts on these calls; the others take the sizes of the arrays that they write entry by entry as
preconditions. The messages of the choice, which `JPoints.choiceText` gives by its value, have the
contract that says nothing in the proof of `JPoints.initFmodpsquare_isChoice`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The curve searched -/

/-- The curve searched for the coefficients `cs` of the curve given, as the specification transforms
it (`JPoints.searchedCoeffs`): its coefficients, their degree, and whether the curve given was
reversed and negated. -/
def searchedCurve (cs : List ℤ) : SearchCurve where
  coeffs := (searchedCoeffs cs).1.toArray
  degree := degree (searchedCoeffs cs).1
  reversed := (searchedCoeffs cs).2.1
  negated := (searchedCoeffs cs).2.2

-- The curve of `normalise_curve` for seven coefficients, by the cases of the transformations.
private theorem fst_run_normalizeCurve_mk (c0 c1 c2 c3 c4 c5 c6 : ℤ) (deg : ℕ) (quiet : Bool) :
    (normalizeCurve #[c0, c1, c2, c3, c4, c5, c6] deg quiet).run.1 =
      if (deg = 6 ∧ c0 = 0) ∧ c1.natAbs = 1 then
        if c1 = -1 then ⟨#[c6, -c5, c4, -c3, c2, -c1, c0], 5, true, true⟩
        else ⟨#[c6, c5, c4, c3, c2, c1, c0], 5, true, false⟩
      else if deg = 5 ∧ c5 = -1 then ⟨#[c0, -c1, c2, -c3, c4, -c5, c6], deg, false, true⟩
      else ⟨#[c0, c1, c2, c3, c4, c5, c6], deg, false, false⟩ := by
  simp only [normalizeCurve]
  simp [List.range', Array.swapIfInBounds, Array.swap, Array.setIfInBounds]
  split_ifs <;> simp

/-- `normalise_curve` makes the curve searched of the specification (`JPoints.searchedCurve`) from
seven coefficients and their degree: the conditions of its transformations are those of
`JPoints.searchedCoeffs` (`JPoints.searchedCoeffs_eq`), its swaps reverse the coefficients and its
negations negate the odd ones. -/
theorem fst_run_normalizeCurve {coeffs : Array ℤ} (h7 : coeffs.size = 7) {deg : ℕ}
    (hd : degree coeffs.toList = deg) (quiet : Bool) :
    (normalizeCurve coeffs deg quiet).run.1 = searchedCurve coeffs.toList := by
  obtain ⟨_ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, _ | ⟨c7, l⟩⟩⟩⟩⟩⟩⟩⟩⟩ :=
    coeffs <;> simp at h7
  subst hd
  rw [fst_run_normalizeCurve_mk, searchedCurve, degree_searchedCoeffs (by simp), searchedCoeffs_eq]
  have habs : |c1| = 1 ↔ c1.natAbs = 1 := by rw [Int.abs_eq_natAbs]; norm_cast
  simp [List.range_succ, habs, and_assoc]
  split_ifs <;> simp_all

private theorem snd_run_normalizeCurve_true (coeffs : Array ℤ) (deg : ℕ) :
    (normalizeCurve coeffs deg true).run.2 = "" := by
  simp [normalizeCurve]
  split_ifs <;> rfl

/-- `normalise_curve` makes the curve searched of the specification (`JPoints.searchedCurve`) from
seven coefficients of degree at least `5` (`JPoints.fst_run_normalizeCurve`): seven coefficients of
degree `5` or `6` (`JPoints.length_searchedCoeffs_of_length_eq`, `JPoints.degree_searchedCoeffs`),
of a squarefree polynomial when the polynomial given is
(`JPoints.squarefree_poly_searchedCoeffs`), and its message, none under `-q`. -/
@[spec]
theorem normalizeCurve_spec (coeffs : Array ℤ) (deg : ℕ) (quiet : Bool) :
    ⦃ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ⦄
    normalizeCurve coeffs deg quiet
    ⦃ fun r ↦ r.1 = searchedCurve coeffs.toList ∧ r.1.coeffs.size = 7 ∧
        degree r.1.coeffs.toList = r.1.degree ∧ 5 ≤ r.1.degree ∧
        (Squarefree (poly coeffs.toList) → Squarefree (poly r.1.coeffs.toList)) ∧
        (quiet = true → r.2 = "") ⦄ := by
  refine Std.WP.Id.triple_of_run fun ⟨h7, hd, h5⟩ ↦ ?_
  have hl : coeffs.toList.length = 7 := by simpa using h7
  rw [fst_run_normalizeCurve h7 hd]
  refine ⟨rfl, by simpa [searchedCurve] using length_searchedCoeffs_of_length_eq hl,
    by simp [searchedCurve], ?_, fun h ↦ ?_, fun hq ↦ hq ▸ snd_run_normalizeCurve_true coeffs deg⟩
  · rw [searchedCurve, degree_searchedCoeffs hl.le]
    split_ifs <;> lia
  · simpa [searchedCurve] using squarefree_poly_searchedCoeffs hl.le h

/-! ### The tables of `init_main` -/

attribute [local irreducible] BitsInvariant in
/-- `init_main` fills the tables of the words with one bit set, of the inverses and of the square
roots modulo the primes of the table as the references say (`JPoints.Tables.WF`): the words by the
shifts of its loop (`JPoints.BitsInvariant`), the inverses by `init_inverses`
(`JPoints.initInverses_spec`) and the square roots by `init_squares`
(`JPoints.initSquares_spec`). -/
@[spec]
theorem initMain_spec : ⦃ True ⦄ initMain Tables.initial ⦃ fun t ↦ t.WF ⦄ := by
  vcgen [initMain] invariants
  · BitsInvariant
  all_goals with_reducible first
    | exact bitsInvariant_nil _
    | exact Tables.size_inverses_initial
    | exact Tables.size_squares_initial
    | exact Tables.wf_of_bitsInvariant ‹_› ‹_› ‹_›
    | exact BitsInvariant.append_singleton ‹_› ‹_›

/-! ### The choice of the sieve -/

/-- What the choice of the sieve of `init_fmodpsquare` leaves for the globals `g` of the choice: the
stages of the plan `plan` (`JPoints.IsSieveStages`: distinct sieving primes among the primes
considered, `sieve_primes1 ≤ sieve_primes2 ≤ sieve_primes3 ≤ num_primes`, the primes of the first
two stages at most `MAX_TABLE_PRIME`, and no sieving primes when `-N` is `0`); the tables of the
curve `ct` for the primes considered and the sieving primes (`JPoints.CurveTables.WF`); when there
are sieving primes the mode `0`, `1` or `2` and the tube only for a bounded fourth coordinate, and
otherwise the box. These hold for every value of the `Float`s of the cost model that chose the plan.
The mode is that of a mode priced only when there are sieving primes: `choose_primes` takes a mode
when `best < 0.0` or its cost is below `best`, from `best = -1.0`, comparisons of `Float`s that no
proof evaluates, and `init_fmodpsquare` sets the box when there are none. -/
structure IsChoice (g : ChoiceGlobals) (ct : CurveTables) (plan : Plan) : Prop
    extends IsSieveStages g.input.numPrimes.toNat g.input.sievePrimes3 plan.pnn plan.sievePrimes1
      plan.sievePrimes2 plan.sievePrimes3 where
  /-- The tables of the curve. -/
  curveTables : ct.WF g.curve.coeffs.toList g.curve.degree g.input.numPrimes.toNat plan.pnn
    plan.sievePrimes3
  /-- With sieving primes, the mode is the box, the tube or the region. -/
  sieveMode_le (h : plan.sievePrimes3 ≠ 0) : plan.sieveMode ≤ 2
  /-- With sieving primes, the tube only for a bounded fourth coordinate. -/
  dbounded_of_sieveMode_eq_one (h : plan.sievePrimes3 ≠ 0) :
    plan.sieveMode = 1 → g.input.dbounded = true
  /-- Without sieving primes, the box. -/
  sieveMode_eq_zero (h : plan.sievePrimes3 = 0) : plan.sieveMode = 0

/-- The text that the choice of the sieve of `init_fmodpsquare` prints for the tables `t`, the
globals `g` of the choice and the plan `plan` that it starts from: message 4 and, when there are
sieving primes, messages 7 and 8, unless `-q` is given. -/
def choiceText (t : Tables) (g : ChoiceGlobals) (plan : Plan) : String :=
  (initFmodpsquare t g CurveTables.initial (.replicate numPrimes {}) plan).run.2.2.2.2

-- The messages of the choice, as values: no contract reads them.

private theorem message4_true (g : ChoiceGlobals) (plan : Plan) :
    ⦃ True ⦄ message4 g plan ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

private theorem message7_true (plan : Plan) : ⦃ True ⦄ message7 plan ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

private theorem message8_true (prec : Array Entry) (nPrimes : ℕ) (plan : Plan) :
    ⦃ True ⦄ message8 prec nPrimes plan ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

-- The verification conditions of `JPoints.initFmodpsquare`, each in its shape.

private theorem numPrimes_toNat_le {g : ChoiceGlobals} (h : g.input.WF) :
    g.input.numPrimes.toNat ≤ numPrimes := by
  lia [h.numPrimes_le]

private theorem initFmodpsquare_pre_rates {t : Tables} {g : ChoiceGlobals} {plan : Plan}
    (h : t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧
      degree g.curve.coeffs.toList = g.curve.degree ∧ 5 ≤ g.curve.degree ∧
      plan.pnn.size = numPrimes + 1) :
    t.WF ∧ g.input.numPrimes.toNat ≤ numPrimes ∧ degree g.curve.coeffs.toList ≤ g.curve.degree ∧
      g.curve.degree ≤ 6 ∧ CurveTables.initial.coeffsModP.size = numPrimes * 8 ∧
      CurveTables.initial.hasInfinity.size = numPrimes ∧
      CurveTables.initial.isFSquare.size = numPrimes * maxPrimeEven ∧
      CurveTables.initial.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven ∧
      (Array.replicate numPrimes ({} : Entry)).size = numPrimes :=
  ⟨h.1, numPrimes_toNat_le h.2.1, h.2.2.2.1.le, h.2.2.2.1 ▸ degree_toList_le_six h.2.2.1,
    Array.size_replicate, Array.size_replicate, Array.size_replicate, Array.size_replicate,
    Array.size_replicate⟩

private theorem initFmodpsquare_post {t : Tables} {g : ChoiceGlobals} {plan₀ : Plan}
    (h : t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧
      degree g.curve.coeffs.toList = g.curve.degree ∧ 5 ≤ g.curve.degree ∧
      plan₀.pnn.size = numPrimes + 1) {ct ct' : CurveTables} {r : Rates}
    (hr : r.WF ct g.curve.coeffs.toList g.curve.degree g.input.numPrimes.toNat) {plan : Plan}
    (hs : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! plan.pnn) plan.sievePrimes1
        plan.sievePrimes2 plan.sievePrimes3)
    (hm : plan.sievePrimes3 = 0 ∨ plan.sieveMode ≤ 2 ∧
      (plan.sieveMode = 1 → g.input.dbounded = true))
    (h0 : plan.sievePrimes3 = 0 → plan.sieveMode = 0)
    (ht : ∀ cs nPrimes, nPrimes ≤ numPrimes → (∀ n < plan.sievePrimes3, plan.pnn[n]! < nPrimes) →
      TablesInvariant cs g.curve.degree nPrimes plan.pnn 0 ct r.tabled →
      ct'.WF cs g.curve.degree nPrimes plan.pnn plan.sievePrimes3) :
    IsChoice g ct' plan :=
  ⟨hs.isSieveStages, ht _ _ (numPrimes_toNat_le h.2.1) (fun _ ↦ hs.lt) (.of_ratesWF hr),
    fun h' ↦ (hm.resolve_left h').1, fun h' ↦ (hm.resolve_left h').2, h0⟩

/- The choice without sieving primes: the box, without the condition at 2. -/
private theorem initFmodpsquare_post_box {t : Tables} {g : ChoiceGlobals} {plan₀ : Plan}
    (h : t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧
      degree g.curve.coeffs.toList = g.curve.degree ∧ 5 ≤ g.curve.degree ∧
      plan₀.pnn.size = numPrimes + 1) {ct ct' : CurveTables} {r : Rates}
    (hr : r.WF ct g.curve.coeffs.toList g.curve.degree g.input.numPrimes.toNat) {plan : Plan}
    (hc : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! plan.pnn) plan.sievePrimes1
        plan.sievePrimes2 plan.sievePrimes3 ∧
      (plan.sievePrimes3 = 0 ∨ plan.sieveMode ≤ 2 ∧ (plan.sieveMode = 1 → g.input.dbounded = true)))
    (h0 : (plan.sievePrimes3 == 0) = true)
    (ht : ∀ cs nPrimes, nPrimes ≤ numPrimes → (∀ n < plan.sievePrimes3, plan.pnn[n]! < nPrimes) →
      TablesInvariant cs g.curve.degree nPrimes plan.pnn 0 ct r.tabled →
      ct'.WF cs g.curve.degree nPrimes plan.pnn plan.sievePrimes3) :
    IsChoice g ct' { plan with sieveMode := 0 } ∧ { g.two with use2 := false } =
      if plan.sievePrimes3 = 0 then { g.two with use2 := false } else g.two := by
  have h0' : plan.sievePrimes3 = 0 := by simpa using h0
  exact ⟨initFmodpsquare_post h hr hc.1 (.inl h0') (fun _ ↦ rfl) ht, by simp [h0']⟩

/- The choice with sieving primes. -/
private theorem initFmodpsquare_post_mode {t : Tables} {g : ChoiceGlobals} {plan₀ : Plan}
    (h : t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧
      degree g.curve.coeffs.toList = g.curve.degree ∧ 5 ≤ g.curve.degree ∧
      plan₀.pnn.size = numPrimes + 1) {ct ct' : CurveTables} {r : Rates}
    (hr : r.WF ct g.curve.coeffs.toList g.curve.degree g.input.numPrimes.toNat) {plan : Plan}
    (hc : IsStages g.input.numPrimes.toNat g.input.sievePrimes3
        (fun n ↦ primeTable[n]! ≤ maxTablePrime) (getElem! plan.pnn) plan.sievePrimes1
        plan.sievePrimes2 plan.sievePrimes3 ∧
      (plan.sievePrimes3 = 0 ∨ plan.sieveMode ≤ 2 ∧ (plan.sieveMode = 1 → g.input.dbounded = true)))
    (h0 : ¬(plan.sievePrimes3 == 0) = true)
    (ht : ∀ cs nPrimes, nPrimes ≤ numPrimes → (∀ n < plan.sievePrimes3, plan.pnn[n]! < nPrimes) →
      TablesInvariant cs g.curve.degree nPrimes plan.pnn 0 ct r.tabled →
      ct'.WF cs g.curve.degree nPrimes plan.pnn plan.sievePrimes3) :
    IsChoice g ct' plan ∧
      g.two = if plan.sievePrimes3 = 0 then { g.two with use2 := false } else g.two := by
  have h0' : plan.sievePrimes3 ≠ 0 := by simpa using h0
  exact ⟨initFmodpsquare_post h hr hc.1 hc.2 (fun h' ↦ absurd h' h0') ht, by simp [h0']⟩

/-- `init_fmodpsquare` makes a choice of the sieve (`JPoints.IsChoice`), for every value of the
`Float`s of the cost model, from the tables of `init_main` and a curve of seven coefficients of
degree at least `5`: the tables of the curve and the records of the primes considered
(`JPoints.initFmodpsquareRates_spec`), the plan of `JPoints.choosePrimes_spec` and the tables of
the primes chosen (`JPoints.initFmodpsquareTables_spec`); and the condition at 2 not used when
there are no sieving primes. -/
theorem initFmodpsquare_isChoice (t : Tables) (g : ChoiceGlobals) (plan : Plan) :
    ⦃ t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧ degree g.curve.coeffs.toList = g.curve.degree ∧
      5 ≤ g.curve.degree ∧ plan.pnn.size = numPrimes + 1 ⦄
    initFmodpsquare t g CurveTables.initial (.replicate numPrimes {}) plan
    ⦃ fun r ↦ IsChoice g r.1 r.2.2.1 ∧
        r.2.2.2.1 = if r.2.2.1.sievePrimes3 = 0 then { g.two with use2 := false } else g.two ⦄ := by
  vcgen [initFmodpsquare, message4_true, message7_true, message8_true]
  all_goals try dsimp only at *
  all_goals obtain ⟨ht, hi, h7, hd, h5, hp⟩ := ‹t.WF ∧ g.input.WF ∧ _›
  all_goals with_reducible first
    | exact initFmodpsquare_pre_rates ⟨ht, hi, h7, hd, h5, hp⟩
    | exact ⟨‹Rates.WF _ _ _ _ _›.prec, numPrimes_toNat_le hi, hp⟩
    | exact ⟨ht, hd ▸ degree_toList_le_six h7⟩
    | exact initFmodpsquare_post_box ⟨ht, hi, h7, hd, h5, hp⟩ ‹_› ‹_› ‹_› ‹_›
    | exact initFmodpsquare_post_mode ⟨ht, hi, h7, hd, h5, hp⟩ ‹_› ‹_› ‹_› ‹_›

/-- `init_fmodpsquare` makes a choice of the sieve (`JPoints.IsChoice`), for every value of the
`Float`s of the cost model, from the tables of `init_main` and a curve of seven coefficients of
degree at least `5`, with the condition at 2 not used when there are no sieving primes
(`JPoints.initFmodpsquare_isChoice`), and prints its text (`JPoints.choiceText`). -/
@[spec]
theorem initFmodpsquare_spec (t : Tables) (g : ChoiceGlobals) (plan : Plan) :
    ⦃ t.WF ∧ g.input.WF ∧ g.curve.coeffs.size = 7 ∧ degree g.curve.coeffs.toList = g.curve.degree ∧
      5 ≤ g.curve.degree ∧ plan.pnn.size = numPrimes + 1 ⦄
    initFmodpsquare t g CurveTables.initial (.replicate numPrimes {}) plan
    ⦃ fun r ↦ (IsChoice g r.1 r.2.2.1 ∧
        r.2.2.2.1 = if r.2.2.1.sievePrimes3 = 0 then { g.two with use2 := false } else g.two) ∧
      r.2.2.2.2 = choiceText t g plan ⦄ :=
  ⟨fun h ↦ ⟨(initFmodpsquare_isChoice t g plan).le_wp h, rfl⟩⟩

theorem choiceText_of_quiet {t : Tables} {g : ChoiceGlobals} (h : g.input.quiet = true)
    (plan : Plan) : choiceText t g plan = "" := by
  simp only [choiceText, initFmodpsquare, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Id.run_bind]
  split <;> rfl

/-! ### The sieve tables and the static data of the sieve -/

attribute [local irreducible] SieveInvariant in
/-- `init_sieve` builds the sieve tables of the first `sp2` sieving primes, `prime[pnn[n]]` for
`n < sp2`, from the tables of the curve `ct` (`JPoints.SieveTables.WF`), for primes of the table
whose rows fit `help`, those of at most `MAX_TABLE_PRIME`: the table of each prime by
`JPoints.initSievePrime_spec`, stored in turn (`JPoints.SieveInvariant`). -/
@[spec]
theorem initSieve_spec (t : Tables) (ct : CurveTables) (pnn : Array ℕ) (sp2 : ℕ) :
    ⦃ t.WF ∧ sp2 ≤ numPrimes ∧ (∀ n < sp2, pnn[n]! < numPrimes) ∧
      ∀ n < sp2, sievingPrime pnn n ≤ maxTablePrime ⦄
    initSieve t ct pnn sp2 SieveTables.initial
    ⦃ fun st ↦ st.WF ct pnn sp2 ⦄ := by
  vcgen [initSieve] invariants
  · fun pref _ s ↦ SieveInvariant ct pnn pref.length s
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact sieveInvariant_init ct pnn
    | exact SieveInvariant.post ‹_›
    | exact SieveInvariant.primeArgs ‹_› ‹_› ‹_›
    | exact SieveInvariant.append_singleton ‹_› ‹_› ‹_› ‹_›

-- The precondition of `JPoints.initSiftChunk` in `JPoints.initSift`: the sieving primes that
-- `JPoints.initSiftPrimes` sets.
private theorem initSift_pre_chunk {g : SiftGlobals} {sd r : SiftData}
    (h : r = { sd with
      pr := r.pr, rowlen := r.rowlen, blocklen := r.blocklen, allOnes := r.allOnes,
      recip3 := r.recip3 } ∧ r.PrimesWF g)
    (hnpr : sd.npr = g.sievePrimes3) :
    r.npr = g.sievePrimes3 ∧ ∀ n < g.sievePrimes3, r.pr[n]! = sievingPrime g.pnn n :=
  ⟨congr(SiftData.npr $(h.1)).trans hnpr, fun _ hn ↦ h.2.pr_eq hn⟩

-- The precondition of `JPoints.initSiftResidues` in `JPoints.initSift`: the reciprocals have an
-- entry for every sieving prime.
private theorem initSift_pre_residues {g : SiftGlobals} {sd r : SiftData}
    (h : r = { sd with
      pr := r.pr, rowlen := r.rowlen, blocklen := r.blocklen, allOnes := r.allOnes,
      recip3 := r.recip3 } ∧ r.PrimesWF g)
    (hnpr : sd.npr ≤ numPrimes) (hinvp : sd.invp.size = numPrimes) : r.npr ≤ r.invp.size :=
  h.1 ▸ hinvp ▸ hnpr

-- The postcondition of `JPoints.initSift`: the static data from their parts, through the frames of
-- `JPoints.initSiftPrimes_spec` and `JPoints.initSiftResidues_spec`.
private theorem initSift_post {g : SiftGlobals} {sd r r' : SiftData} {chunks : Array ChunkSpec}
    {N : ℕ} {t : Double}
    (h : r = { sd with
      pr := r.pr, rowlen := r.rowlen, blocklen := r.blocklen, allOnes := r.allOnes,
      recip3 := r.recip3 } ∧ r.PrimesWF g)
    (hc : PushLoopInvariant (fun k c ↦ c.WF g sd.wLowAll sd.wHighAll k) (ForIn.toList [:N]).length
      chunks)
    (h' : r' = { { { r with numChunks := N, th := t, th2 := t * t } with chunks } with
      res0 := r'.res0, invp := r'.invp } ∧ r'.ResiduesWF g)
    (hnpr : sd.npr = g.sievePrimes3) (hlow : sd.wLowAll = (-g.check.height) >>> longShift)
    (hhigh : sd.wHighAll = (g.check.height >>> longShift) + 1)
    (hnum : N = (ceilDiv (sd.wHighAll - sd.wLowAll) g.arraySize).toNat)
    (ht : t = Double.ofInt g.check.dbound) : r'.WF g := by
  obtain ⟨hr, hp⟩ := h
  obtain ⟨hr', hq⟩ := h'
  rw [hr'] at hq ⊢
  rw [hr] at hq ⊢
  exact SiftData.PrimesWF.wf ⟨hp.1, hp.2, hp.3, hp.4, hp.5⟩ hq hnpr hlow hhigh hnum hc.size_eq
    hc.forall_lt ht rfl

attribute [local irreducible] PushLoopInvariant in
/-- `init_sift` computes the static data of the sieve for the globals `g` of the sieve
(`JPoints.SiftData.WF`), from static data whose arrays have the sizes that it writes into
(`JPoints.SiftData.Sized`), for sieving primes of the table: the data of the sieving primes
(`JPoints.initSiftPrimes_spec`), the chunks of a row (`JPoints.initSiftChunk_spec`), and the
residues of the positions in a chunk with the reciprocals of the primes
(`JPoints.initSiftResidues_spec`). -/
@[spec]
theorem initSift_spec (g : SiftGlobals) (sd : SiftData) :
    ⦃ sd.Sized ∧ g.sievePrimes1 ≤ g.sievePrimes2 ∧ g.sievePrimes2 ≤ g.sievePrimes3 ∧
      g.sievePrimes3 ≤ numPrimes ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes ⦄
    initSift g sd
    ⦃ fun r ↦ r.WF g ⦄ := by
  vcgen [initSift] invariants
  · fun pref _ chunks ↦ PushLoopInvariant (fun k c ↦ c.WF g ((-g.check.height) >>> longShift)
      ((g.check.height >>> longShift) + 1) k) pref.length chunks
  all_goals obtain ⟨hs, -, -, h3, hpnn⟩ := ‹SiftData.Sized _ ∧ _›
  all_goals have := hs.size_invp
  all_goals try dsimp only
  all_goals with_reducible first
    | exact ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩, h3, hpnn⟩
    | exact pushLoopInvariant_nil _
    | exact PushLoopInvariant.push ‹_› ‹_› ‹_›
    | exact initSift_pre_chunk ‹_› rfl
    | exact initSift_pre_residues ‹_› ‹_› ‹_›
    | exact initSift_post ‹_› ‹_› ‹_› rfl rfl rfl rfl rfl

/-! ### The condition at 2 and the real region -/

/-- The condition at 2 of `twoadic_init` admits every point of the curve with the coefficients
`coeffs` and the coefficients `k = kummer_init(coeffs)` of its quartic `K₀`: the table modulo
`64`, which keeps the classes of the condition at 2 (`JPoints.twoadicTable_spec`,
`JPoints.TwoAdic.sound_of_isTwoadicTable`), unused when it admits every class. -/
@[spec]
theorem twoadicInit_spec (coeffs : Array ℤ) (k : KummerCoeffs) :
    ⦃ coeffs.size = 7 ∧ 5 ≤ degree coeffs.toList ∧ k = kummerInit coeffs ⦄
    twoadicInit coeffs k TwoAdic.initial
    ⦃ fun r ↦ r.Sound coeffs.toList ⦄ := by
  vcgen [twoadicInit]
  all_goals first
    | exact TwoAdic.sound_of_use2_eq_false rfl _
    | exact ⟨‹_ ∧ _ ∧ k = kummerInit coeffs›.2.2, Array.size_replicate .., Array.size_replicate ..⟩
    | exact TwoAdic.sound_of_isTwoadicTable ‹_›

/-! ### The intervals on which `f` is negative -/

-- The verification conditions of `JPoints.realRootsInit_spec`, each in its shape.

private theorem sturmIsolate_spec_self (ch : SturmChain) (fuel : ℕ) (lo hi : ℚ) (nlo nhi : ℕ)
    (roots : RootIntervals) :
    ⦃ IsolatePre ch lo hi lo hi nlo nhi roots ⦄ sturmIsolate ch fuel lo hi nlo nhi roots
    ⦃ fun r ↦ ∀ roots', r = some roots' → roots'.Isolated ch (sturmChanges ch lo).run hi ⦄ :=
  sturmIsolate_spec ch lo hi fuel lo hi nlo nhi roots

private theorem lt_two_pow_of_log2_add_one_le {B : ℤ} (h : B.natAbs.log2 + 1 ≤ rootBits) :
    B < 2 ^ 480 := by
  have h0 : (B.natAbs : ℤ) < 2 ^ (B.natAbs.log2 + 1) := mod_cast Nat.lt_log2_self
  have h1 : (2 : ℤ) ^ (B.natAbs.log2 + 1) ≤ 2 ^ 480 :=
    pow_le_pow_right₀ (by norm_num) (h.trans rootBits_le_480)
  exact Int.le_natAbs.trans_lt (h0.trans_le h1)

private theorem startPre_of_pre {coeffs : Array ℤ} {deg : ℕ}
    (h : SturmTheorem ∧ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ∧
      Squarefree (poly coeffs.toList)) : coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 1 ≤ deg :=
  ⟨h.2.1, h.2.2.1, by lia [h.2.2.2.1]⟩

private theorem getElem!_ne_zero_of_pre {coeffs : Array ℤ} {deg : ℕ}
    (h : SturmTheorem ∧ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ∧
      Squarefree (poly coeffs.toList)) : ¬coeffs[deg]! = 0 :=
  getElem!_degree_ne_zero h.2.2.1 (by lia [h.2.2.2.1])

private theorem RootIntervals.isolated_initial (ch : SturmChain) (x : ℚ) :
    ({} : RootIntervals).Isolated ch (sturmChanges ch x).run x :=
  ⟨rfl, rfl, zero_add _, nofun, nofun⟩

private theorem NegativeIntervals.sound_initial (cs : List ℤ) : ({} : NegativeIntervals).Sound cs :=
  ⟨by decide, nofun, nofun, nofun⟩

-- The start of the isolation in `real_roots_init`: the interval `(-B, B]` with the counts at its
-- ends and no interval recorded.
private theorem isolatePre_initial {coeffs : Array ℤ} {deg : ℕ}
    (hpre : SturmTheorem ∧ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ∧
      Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hch : ch.IsFinished (poly coeffs.toList)) {B : ℤ}
    (hB : 2 ≤ B ∧ ∀ k < deg, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * (B - 2))
    (hlog : B.natAbs.log2 + 1 ≤ rootBits) {nlo nhi : ℕ}
    (hlo : nlo = (sturmChanges ch (-(B : ℚ))).run) (hhi : nhi = (sturmChanges ch (B : ℚ)).run) :
    IsolatePre ch (-(B : ℚ)) B (-(B : ℚ)) B nlo nhi {} := by
  obtain ⟨hS, h7, hd, h5, hsq⟩ := hpre
  have h2 : (2 : ℚ) ≤ B := mod_cast hB.1
  exact ⟨hch.counts hS h7 hd hsq (fun y hy ↦ abs_lt_of_isRoot_map_poly hd hsq.ne_zero hB hy)
    (lt_two_pow_of_log2_add_one_le hlog), le_rfl, by linarith, le_rfl, hlo.symm, hhi.symm,
    RootIntervals.isolated_initial ch _⟩

private theorem recordPre_of_isolated {coeffs : Array ℤ} {deg : ℕ}
    (hpre : SturmTheorem ∧ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ∧
      Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hch : ch.IsFinished (poly coeffs.toList)) {B : ℤ}
    (hB : 2 ≤ B ∧ ∀ k < deg, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * (B - 2))
    {o : Option RootIntervals}
    (ho : ∀ r, o = some r → r.Isolated ch (sturmChanges ch (-(B : ℚ))).run B)
    {r : RootIntervals} (hr : o = some r) : RecordPre coeffs deg r := by
  obtain ⟨hS, h7, hd, h5, hsq⟩ := hpre
  exact (ho r hr).recordPre hS h7 hd (by lia) hsq hch
    (fun y hy ↦ by rw [Rat.cast_intCast]; exact abs_lt_of_isRoot_map_poly hd hsq.ne_zero hB hy)

/-- Under Sturm's theorem, `real_roots_init` finds intervals on which the squarefree polynomial `f`
with the seven coefficients `coeffs` of degree `deg ≥ 5` is negative
(`JPoints.NegativeIntervals.Sound`): the Sturm chain is Mathlib's Sturm sequence of `f` and `f'`
(`JPoints.realRootsChain_spec`), whose counts isolate the real roots in the Cauchy bound `(-B, B)`
(`JPoints.realRootsBound_spec`, `JPoints.sturmIsolate_spec`), and the gaps between the isolating
intervals of a negative sign, shrunk by the doubles of their ends, lie where `f < 0`
(`JPoints.RootIntervals.Isolated.recordPre`, `JPoints.realRootsRecord_spec`); for a bound of more
than `ROOT_BITS` bits, or a fuel that runs out, there is no interval. -/
@[spec]
theorem realRootsInit_spec (coeffs : Array ℤ) (deg : ℕ) :
    ⦃ SturmTheorem ∧ coeffs.size = 7 ∧ degree coeffs.toList = deg ∧ 5 ≤ deg ∧
      Squarefree (poly coeffs.toList) ⦄
    realRootsInit coeffs deg
    ⦃ fun r ↦ r.Sound coeffs.toList ⦄ := by
  vcgen [realRootsInit, realRootsChain_spec (poly coeffs.toList),
    Std.WP.Id.triple_eq_run (sturmChanges _ _), sturmIsolate_spec_self]
  all_goals with_reducible first
    | exact startPre_of_pre ‹_›
    | exact getElem!_ne_zero_of_pre ‹_›
    | exact isolatePre_initial ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact recordPre_of_isolated ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact NegativeIntervals.sound_initial _

/-! ### The start of the analysis of the tube -/

/-- `tube_init` for the globals `gl` of the exact check returns the coefficients of the analysis of
the tube (`JPoints.tubeInitCoeffs`), the plan with the mode `0`, the intervals of `real_roots_init`
(`JPoints.realRootsInit`), static data of the sieve with the sizes of those it is given (the sample
of `tube_sample` writes no array entry by entry), and a consistent state of the analysis of the tube
(`JPoints.TubeState.WF`), by `JPoints.tubeSample_spec`; the values of the doubles of the sample,
which `init_sift` and the analysis of each band overwrite, are not constrained. -/
@[spec]
theorem tubeInit_spec (gl : CheckGlobals) (plan : Plan) (sd : SiftData) (t : TubeState) :
    ⦃ gl.WF ∧ t.WF ⦄
    tubeInit gl plan sd t
    ⦃ fun r ↦ r.1 = (tubeInitCoeffs gl.curve gl.kummer).run ∧ r.2.1 = { plan with sieveMode := 0 } ∧
        r.2.2.1 = (realRootsInit gl.curve.coeffs gl.curve.degree).run ∧
        (sd.Sized → r.2.2.2.1.Sized) ∧ r.2.2.2.2.1.WF ⦄ := by
  vcgen [tubeInit, Std.WP.Id.triple_eq_run (tubeInitCoeffs _ _),
    Std.WP.Id.triple_eq_run (realRootsInit _ _), tubeSample_spec]
  all_goals try dsimp only at *
  all_goals first
    | exact ‹gl.WF ∧ t.WF›.2
    | exact ⟨‹_›, ‹_›, ‹_›⟩

end JPoints

end
