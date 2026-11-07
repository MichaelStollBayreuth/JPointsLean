/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import Mathlib.Data.Nat.Prime.Defs
public import Std.WP

import JPoints.Mathlib.Data.Int.GCD
import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Loops
import JPoints.Proof.Reduction
import JPoints.Proof.Tables
import JPoints.Proof.VCSimp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.ModEq
import Std.Tactic.Do

/-!
# The contracts of the tests for common factors and of the third stage

What the stages of the sieve of `j-points` read of the set-up of the main search
(`JPoints.IsStageSetup`, with the residues of a word, `JPoints.WordResidues`), and the contracts
of the components of `JPoints.Model.Sift` that test a bit of a word past the second stage: the
test for common factors (`relprime3`, `JPoints.relprime3_spec`, by `relprime2`,
`JPoints.relprime2_spec`, and the binary algorithm of `JPoints.oddGcd`, `JPoints.oddGcd_spec`, whose
loop `relprime` shares, `JPoints.forIn_loop_sub_shiftRight_spec`) decides the coprimality of the
enumeration (`JPoints.coprimeKeeps`); `MOD3` is the remainder below
`2 ^ 16` (`JPoints.mod3_eq`); `row3_setup` keeps the data of the third stage consistent
(`JPoints.row3Setup_spec`, `JPoints.Row3Cache.WF`); and `check_bit` makes the test of the third
stage (`JPoints.checkBit_spec`, `JPoints.stage3Keeps`) through the class test of the tables of the
curve (`JPoints.CurveTables.admits3`).

## Main definitions

* `JPoints.IsStageSetup`: what the stages read of the set-up of the main search.
* `JPoints.WordResidues`: the residues of a word that the stages read.
* `JPoints.OddPartInvariant`, `JPoints.OddGcdInvariant`, `JPoints.CheckBitInvariant`: the
  invariants of the loops.

## Main statements

* `JPoints.forIn_loop_shiftRight_spec`, `JPoints.forIn_loop_sub_shiftRight_spec`,
  `JPoints.oddGcd_spec`, `JPoints.relprime2_spec`, `JPoints.relprime3_spec`: the tests for common
  factors.
* `JPoints.mod3_eq`: the remainder by a reciprocal of the third stage.
* `JPoints.row3SetupInverses_spec`, `JPoints.row3SetupFactors_spec`, `JPoints.row3Setup_spec`: the
  data of the third stage.
* `JPoints.get_row3SetupEntry_eq_admits3`, `JPoints.checkBit_spec`: the third stage of a bit.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, each verification condition closed by a lemma stated in its own shape. The loop that
takes the odd part of an integer has a contract of its own (`JPoints.forIn_loop_shiftRight_spec`),
which `vcgen` is given explicitly, so that the copies of the loop that the branches of `relprime3`
make need no invariants; so has the loop of the binary algorithm
(`JPoints.forIn_loop_sub_shiftRight_spec`), for `JPoints.oddGcd` and the copies in `relprime`. The
loops of `row3_setup` that set arrays have the invariants of `JPoints.Proof.Loops`. The remainders
of C, `Int.tmod`, are the Euclidean ones for the non-negative first coordinates of the calls, and
the conditional corrections of the C code make them Euclidean for the second.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The set-up of the stages -/

/-- What the stages of the sieve read of the globals `g` and the static data `sd` of the sieve as
`find_points` sets them up: the globals of the exact check, the tables of `init_main`, the sieve
tables of the first two stages and the static data of the sieve as `init_sift` computes them, and
the numbers of the sieving primes of the three stages in order, all of them primes of the table. -/
structure IsStageSetup (g : SiftGlobals) (sd : SiftData) : Prop where
  /-- The globals of the exact check. -/
  check : g.check.WF
  /-- The tables of `init_main`. -/
  tables : g.tables.WF
  /-- The sieve tables of the first two stages. -/
  sieve : g.sieve.WF g.curve g.pnn g.sievePrimes2
  /-- The static data of the sieve. -/
  siftData : sd.WF g
  /-- The first stage is part of the first two. -/
  sievePrimes1_le_sievePrimes2 : g.sievePrimes1 ≤ g.sievePrimes2
  /-- The first two stages are part of the three. -/
  sievePrimes2_le_sievePrimes3 : g.sievePrimes2 ≤ g.sievePrimes3
  /-- The sieving primes are primes of the table. -/
  sievePrimes3_le_numPrimes : g.sievePrimes3 ≤ numPrimes
  /-- The indices of the sieving primes are those of primes of the table. -/
  pnn_lt {n : ℕ} (hn : n < g.sievePrimes3) : g.pnn[n]! < numPrimes

/-- The globals and the static data of the main search give the stages what they read. -/
theorem IsSieveSetup.isStageSetup {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) :
    IsStageSetup bg.sift sd := by
  obtain ⟨g, hg, hs⟩ := h
  exact ⟨hs.check_eq ▸ hg.check, hs.tables_eq ▸ hg.tables, hs.sieve, hs.siftData,
    hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3,
    by lia [hs.sievePrimes3_le_numPrimes, hg.input.numPrimes_le], IsSieveSetup.pnn_lt ⟨g, hg, hs⟩⟩

namespace IsStageSetup

variable {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd) {n : ℕ}
  (hn : n < g.sievePrimes3)

include h hn

theorem pr_eq : sd.pr[n]! = primeTable[g.pnn[n]!]! := h.siftData.pr_eq hn

private theorem prime_pr : (sd.pr[n]!).Prime := h.pr_eq hn ▸ prime_getElem!_primeTable (h.pnn_lt hn)

/-- The sieving primes are at least `3`. -/
theorem three_le_pr : 3 ≤ sd.pr[n]! := h.pr_eq hn ▸ three_le_getElem!_primeTable (h.pnn_lt hn)

private theorem pr_lt_maxPrimeEven : sd.pr[n]! < maxPrimeEven :=
  h.pr_eq hn ▸ lt_of_le_of_lt (getElem!_primeTable_le_maxPrime (h.pnn_lt hn))
    maxPrime_lt_maxPrimeEven

/-- The sieving primes are below `256`, so that the product of two residues modulo one of them stays
below `2 ^ 16`, the bound of `MOD3`. -/
private theorem pr_lt_256 : sd.pr[n]! < 256 :=
  lt_of_lt_of_le (h.pr_lt_maxPrimeEven hn) maxPrimeEven_le_256

end IsStageSetup

theorem IsStageSetup.lt_sievePrimes3 {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd)
    {n : ℕ} (hn : n < g.sievePrimes2) : n < g.sievePrimes3 := by
  lia [h.sievePrimes2_le_sievePrimes3]

/-- The sieving primes of the first two stages are at least `3`. -/
theorem IsStageSetup.three_le_pr_of_lt_sievePrimes2 {g : SiftGlobals} {sd : SiftData}
    (h : IsStageSetup g sd) {n : ℕ} (hn : n < g.sievePrimes2) : 3 ≤ sd.pr[n]! :=
  h.three_le_pr (h.lt_sievePrimes3 hn)

/-- The residues `res0[r0 + n] + res[n]` that the second and third stages read for the word of index
`i` of a row, for the globals `g` and the static data `sd` of the sieve: for the `n`-th sieving
prime `p`, `n < sieve_primes3`, two residues below `p` whose sum is `i` modulo `p`, so that one
conditional subtraction gives `i mod p`. -/
def WordResidues (g : SiftGlobals) (sd : SiftData) (r0 : ℕ) (res : Array ℕ) (i : ℤ) : Prop :=
  ∀ n < g.sievePrimes3, sd.res0[r0 + n]! < sd.pr[n]! ∧ res[n]! < sd.pr[n]! ∧
    (sd.res0[r0 + n]! + res[n]!) % sd.pr[n]! = (i % sd.pr[n]!).toNat

/-- The residues `res0[k npr + n] = k mod p` of the position `k ≤ array_size` of a word in its chunk
and `res[n] = w_low mod p` of the first word of the chunk are those of the word `w_low + k`. -/
theorem IsStageSetup.wordResidues {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd)
    {kc k : ℕ} (hkc : kc < sd.numChunks) (hk : k ≤ g.arraySize) :
    WordResidues g sd (k * sd.npr) (sd.chunks[kc]!).res ((sd.chunks[kc]!).wLow + k) := by
  intro n hn
  have hp := h.three_le_pr hn
  rw [h.siftData.res0_eq hk hn, h.siftData.res_chunk hkc hn]
  refine ⟨Nat.mod_lt _ (by lia), Int.toNat_emod_lt _ (by lia), ?_⟩
  rw [Nat.add_comm, Int.toNat_emod_add_mod _ _ (by lia), Int.natCast_mod, Int.add_emod_emod]

/-! ### The tests for common factors -/

/-- The invariant of the loop `while(!(x & 1)) x >>= 1;` from `x`: the value `s` is a positive part
`x = 2 ^ t s` of `x`, odd at the exit. -/
def OddPartInvariant (x : ℤ) : Std.WP.WhileInvariant ℤ Prop :=
  .mk fun exit s ↦ 0 < s ∧ (∃ t : ℕ, 2 ^ t * s = x) ∧ (exit = true → s % 2 = 1)

private theorem oddPartInvariant_init {x : ℤ} (h : 0 < x) : OddPartInvariant x false x :=
  ⟨h, ⟨0, by simp⟩, nofun⟩

private theorem OddPartInvariant.post {x r : ℤ} (h : OddPartInvariant x true r) :
    0 < r ∧ r % 2 = 1 ∧ ∃ t : ℕ, 2 ^ t * r = x :=
  ⟨h.1, h.2.2 rfl, h.2.1⟩

private theorem oddPartInvariant_step {x b : ℤ} {mb : ℕ} (h0 : (b % 2 == 0) = true)
    (h : b.toNat = mb ∧ OddPartInvariant x false b) :
    (b >>> 1).toNat < mb ∧ OddPartInvariant x false (b >>> 1) := by
  obtain ⟨rfl, hb, ⟨t, rfl⟩, -⟩ := h
  have h2 : b % 2 = 0 := by simpa using h0
  have e : b >>> 1 = b / 2 := by simp [Int.shiftRight_eq_div_pow]
  rw [e]
  refine ⟨by lia, by lia, ⟨t + 1, ?_⟩, nofun⟩
  rw [pow_succ, mul_assoc, Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h2)]

private theorem oddPartInvariant_exit {x b : ℤ} {mb : ℕ} (h0 : ¬(b % 2 == 0) = true)
    (h : b.toNat = mb ∧ OddPartInvariant x false b) : OddPartInvariant x true b :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by simp only [beq_iff_eq] at h0; lia⟩

attribute [local irreducible] OddPartInvariant in
/-- The loop `while(!(x & 1)) x >>= 1;` of `relprime2`, `relprime3` and `JPoints.oddGcd` from
`x > 0` leaves the odd part `r` of `x`, `x = 2 ^ t r`. The contract is on the loop itself, so that
`vcgen` applies it in each copy of the loop that the branches of the callers make. -/
@[spec]
theorem forIn_loop_shiftRight_spec (x : ℤ) :
    ⦃ 0 < x ⦄
    (forIn Lean.Loop.mk x fun _ s ↦
      if (s % 2 == 0) = true then pure (ForInStep.yield (s >>> 1)) else pure (ForInStep.done s) :
      Id ℤ)
    ⦃ fun r ↦ 0 < r ∧ r % 2 = 1 ∧ ∃ t : ℕ, 2 ^ t * r = x ⦄ := by
  vcgen invariants
  · OddPartInvariant x
  · Std.WP.Variant.ofMeasure fun s : ℤ ↦ s.toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact oddPartInvariant_init ‹_›
    | exact OddPartInvariant.post ‹_›
    | exact oddPartInvariant_step ‹_› ‹_›
    | exact oddPartInvariant_exit ‹_› ‹_›

/-- The invariant of the loop of `JPoints.oddGcd`, whose state is `(n, m)`: both odd and positive,
with the gcd `g` of the operands, and equal at the exit. -/
def OddGcdInvariant (g : ℕ) : Std.WP.WhileInvariant (ℤ × ℤ) Prop :=
  .mk fun exit s ↦ 0 < s.1 ∧ 0 < s.2 ∧ s.1 % 2 = 1 ∧ s.2 % 2 = 1 ∧ Int.gcd s.1 s.2 = g ∧
    (exit = true → s.1 = s.2)

private theorem oddGcdInvariant_iff {g : ℕ} {e : Bool} {a b : ℤ} :
    OddGcdInvariant g e (a, b) ↔
      0 < a ∧ 0 < b ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ a.gcd b = g ∧ (e = true → a = b) :=
  Iff.rfl

private theorem shiftRight_one_sub_pos {a b : ℤ} {g mb : ℕ} (hab : b < a)
    (h : a.toNat + b.toNat = mb ∧ OddGcdInvariant g false (a, b)) :
    (0 : ℤ) < (a - b) >>> 1 := by
  obtain ⟨-, -, ha, hb, -⟩ := oddGcdInvariant_iff.mp h.2
  rw [Int.shiftRight_one_eq_ediv_two]
  lia

private theorem shiftRight_one_sub_pos' {a b : ℤ} {g mb : ℕ} (hne : (a != b) = true) (hab : ¬b < a)
    (h : a.toNat + b.toNat = mb ∧ OddGcdInvariant g false (a, b)) :
    (0 : ℤ) < (b - a) >>> 1 := by
  obtain ⟨-, -, ha, hb, -⟩ := oddGcdInvariant_iff.mp h.2
  rw [Int.shiftRight_one_eq_ediv_two]
  lia [bne_iff_ne.mp hne]

private theorem oddGcdInvariant_step {a b y : ℤ} {g mb : ℕ} (hab : b < a)
    (hy : 0 < y ∧ y % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * y = (a - b) >>> 1)
    (h : a.toNat + b.toNat = mb ∧ OddGcdInvariant g false (a, b)) :
    y.toNat + b.toNat < mb ∧ OddGcdInvariant g false (y, b) := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨ha, hb, ha2, hb2, rfl, -⟩ := oddGcdInvariant_iff.mp h
  obtain ⟨hy0, hy2, t, ht⟩ := hy
  have h2 := Int.two_pow_succ_mul_eq_of_shiftRight (by lia) ht
  have h1 : y ≤ 2 ^ t * y := le_mul_of_one_le_left hy0.le (one_le_pow₀ (by norm_num))
  refine ⟨by lia, oddGcdInvariant_iff.mpr ⟨hy0, hb, hy2, hb2, ?_, nofun⟩⟩
  rw [← Int.gcd_two_pow_mul_of_emod_two_eq_one hb2 (t + 1), h2, Int.gcd_sub_self_left]

private theorem oddGcdInvariant_step' {a b y : ℤ} {g mb : ℕ} (hne : (a != b) = true) (hab : ¬b < a)
    (hy : 0 < y ∧ y % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * y = (b - a) >>> 1)
    (h : a.toNat + b.toNat = mb ∧ OddGcdInvariant g false (a, b)) :
    a.toNat + y.toNat < mb ∧ OddGcdInvariant g false (a, y) := by
  have hlt : a < b := by have := bne_iff_ne.mp hne; lia
  obtain ⟨rfl, h⟩ := h
  obtain ⟨ha, hb, ha2, hb2, rfl, -⟩ := oddGcdInvariant_iff.mp h
  obtain ⟨h1, h2⟩ := oddGcdInvariant_step (mb := b.toNat + a.toNat) hlt hy
    ⟨rfl, oddGcdInvariant_iff.mpr ⟨hb, ha, hb2, ha2, rfl, nofun⟩⟩
  obtain ⟨hy0, -, hy2, -, h6, -⟩ := oddGcdInvariant_iff.mp h2
  refine ⟨by lia, oddGcdInvariant_iff.mpr ⟨ha, hy0, ha2, hy2, ?_, nofun⟩⟩
  rw [Int.gcd_comm, h6, Int.gcd_comm]

private theorem oddGcdInvariant_init {n m : ℤ} (h : 0 < n ∧ 0 < m ∧ n % 2 = 1 ∧ m % 2 = 1) :
    OddGcdInvariant (n.gcd m) false (n, m) :=
  oddGcdInvariant_iff.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, rfl, nofun⟩

private theorem OddGcdInvariant.post {a b : ℤ} {g : ℕ} (h : OddGcdInvariant g true (a, b)) :
    a = g ∧ b = g := by
  obtain ⟨ha, -, -, -, rfl, he⟩ := oddGcdInvariant_iff.mp h
  obtain rfl := he rfl
  rw [Int.gcd_self]
  lia

private theorem oddGcdInvariant_exit {a b : ℤ} {g mb : ℕ} (hne : ¬(a != b) = true)
    (h : a.toNat + b.toNat = mb ∧ OddGcdInvariant g false (a, b)) :
    OddGcdInvariant g true (a, b) :=
  let ⟨ha, hb, ha2, hb2, hg, _⟩ := oddGcdInvariant_iff.mp h.2
  oddGcdInvariant_iff.mpr ⟨ha, hb, ha2, hb2, hg, fun _ ↦ by simpa using hne⟩

attribute [local irreducible] OddGcdInvariant in
/-- The loop `while (n != m) …` of the binary algorithm of `JPoints.oddGcd` and of `relprime`, from
odd `n, m > 0`, leaves the gcd of the two in both: it replaces the larger of the two by the odd
part of their distance (`JPoints.forIn_loop_shiftRight_spec`), which has the same gcd with the
smaller one, and the sum of the two decreases. The contract is on the loop itself, so that `vcgen`
applies it in each copy of the loop that the branches of `relprime` make. -/
@[spec]
theorem forIn_loop_sub_shiftRight_spec (n m : ℤ) :
    ⦃ 0 < n ∧ 0 < m ∧ n % 2 = 1 ∧ m % 2 = 1 ⦄
    (forIn Lean.Loop.mk (n, m) fun _ (s : ℤ × ℤ) ↦
      if (s.1 != s.2) = true then
        if s.1 > s.2 then do
          let r ← (forIn Lean.Loop.mk ((s.1 - s.2) >>> 1) fun _ (t : ℤ) ↦
            if (t % 2 == 0) = true then pure (ForInStep.yield (t >>> 1))
            else pure (ForInStep.done t) : Id ℤ)
          pure (ForInStep.yield (r, s.2))
        else do
          let r ← (forIn Lean.Loop.mk ((s.2 - s.1) >>> 1) fun _ (t : ℤ) ↦
            if (t % 2 == 0) = true then pure (ForInStep.yield (t >>> 1))
            else pure (ForInStep.done t) : Id ℤ)
          pure (ForInStep.yield (s.1, r))
      else pure (ForInStep.done (s.1, s.2)) : Id (ℤ × ℤ))
    ⦃ fun r ↦ r.1 = (Int.gcd n m : ℤ) ∧ r.2 = (Int.gcd n m : ℤ) ⦄ := by
  vcgen [forIn_loop_shiftRight_spec] invariants
  · OddGcdInvariant (Int.gcd n m)
  · Std.WP.Variant.ofMeasure fun s : ℤ × ℤ ↦ s.1.toNat + s.2.toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact oddGcdInvariant_init ‹_›
    | exact OddGcdInvariant.post ‹_›
    | exact shiftRight_one_sub_pos ‹_› ‹_›
    | exact shiftRight_one_sub_pos' ‹_› ‹_› ‹_›
    | exact oddGcdInvariant_step ‹_› ‹_› ‹_›
    | exact oddGcdInvariant_step' ‹_› ‹_› ‹_› ‹_›
    | exact oddGcdInvariant_exit ‹_› ‹_›

/-- The binary algorithm of `JPoints.oddGcd` computes the gcd of two odd positive integers, by its
loop (`JPoints.forIn_loop_sub_shiftRight_spec`). -/
@[spec]
theorem oddGcd_spec (n m : ℤ) :
    ⦃ 0 < n ∧ 0 < m ∧ n % 2 = 1 ∧ m % 2 = 1 ⦄ oddGcd n m ⦃ fun r ↦ r = (Int.gcd n m : ℤ) ⦄ := by
  vcgen [oddGcd, forIn_loop_sub_shiftRight_spec]
  exact ‹_ ∧ _›.1

section Relprime2

variable {n m : ℤ}

private theorem beq_one_eq_decide_gcd_of_beq_zero (h : 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1))
    (hn : (n == 0) = true) : (m == 1) = decide (n.gcd m = 1) := by
  rw [beq_iff_eq.mp hn, Int.gcd_zero_left, Bool.beq_eq_decide_eq, decide_eq_decide]
  lia

private theorem beq_one_eq_decide_gcd_of_beq_zero' (h : 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1))
    (hm : (m == 0) = true) : (n == 1) = decide (n.gcd m = 1) := by
  rw [beq_iff_eq.mp hm, Int.gcd_zero_right, Bool.beq_eq_decide_eq, decide_eq_decide]
  lia

private theorem pos_of_not_beq_zero (h : 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1))
    (hm : ¬(m == 0) = true) : 0 < m := by
  have : m ≠ 0 := by simpa using hm
  lia

private theorem pos_of_not_beq_zero' (h : 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1))
    (hn : ¬(n == 0) = true) : 0 < n := by
  have : n ≠ 0 := by simpa using hn
  lia

private theorem oddGcd_beq_one_eq_decide_gcd {n' m' g : ℤ}
    (h : 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1))
    (hm : 0 < m' ∧ m' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * m' = m)
    (hn : 0 < n' ∧ n' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * n' = n) (hg : g = (n'.gcd m' : ℤ)) :
    (g == 1) = decide (n.gcd m = 1) := by
  obtain ⟨-, hm2, t, ht⟩ := hm
  obtain ⟨-, hn2, s, hs⟩ := hn
  rw [hg, Int.gcd_eq_gcd_of_two_pow_mul_eq hs ht hn2 hm2 h.2.2, Bool.beq_eq_decide_eq,
    decide_eq_decide]
  lia

private theorem pos_and_emod_two_of_oddPart {x y X Y : ℤ}
    (hx : 0 < x ∧ x % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * x = X)
    (hy : 0 < y ∧ y % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * y = Y) :
    0 < y ∧ 0 < x ∧ y % 2 = 1 ∧ x % 2 = 1 :=
  ⟨hy.1, hx.1, hy.2.1, hx.2.1⟩

end Relprime2

/-- `relprime2` decides whether two non-negative integers, not both even, are coprime: by `m = 1`
when `n = 0` and by `n = 1` when `m = 0`, else by the gcd of their odd parts. -/
@[spec]
theorem relprime2_spec (n m : ℤ) :
    ⦃ 0 ≤ n ∧ 0 ≤ m ∧ (n % 2 = 1 ∨ m % 2 = 1) ⦄ relprime2 n m
    ⦃ fun r ↦ r = decide (Int.gcd n m = 1) ⦄ := by
  vcgen [relprime2, forIn_loop_shiftRight_spec, oddGcd_spec]
  all_goals with_reducible first
    | exact beq_one_eq_decide_gcd_of_beq_zero ‹_› ‹_›
    | exact beq_one_eq_decide_gcd_of_beq_zero' ‹_› ‹_›
    | exact pos_of_not_beq_zero ‹_› ‹_›
    | exact pos_of_not_beq_zero' ‹_› ‹_›
    | exact pos_and_emod_two_of_oddPart ‹_› ‹_›
    | exact oddGcd_beq_one_eq_decide_gcd ‹_› ‹_› ‹_› ‹_›

private theorem coprimeKeeps_eq (a b c : ℤ) :
    coprimeKeeps a b c = decide (Int.gcd (Int.gcd a b) c = 1) := by
  rw [coprimeKeeps, ← Int.coe_gcd, ← Int.coe_gcd, Int.gcd_assoc]
  simp

section Relprime3

variable {a b c : ℤ}

private theorem false_eq_coprimeKeeps (h : (a % 2 == 0 && b % 2 == 0 && c % 2 == 0) = true) :
    false = coprimeKeeps a b c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [coprimeKeeps_eq, eq_comm, decide_eq_false_iff_not]
  intro h1
  have h2 : (2 : ℤ) ∣ (Int.gcd (Int.gcd a b) c : ℤ) :=
    Int.dvd_coe_gcd (Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero h.1.1)
      (Int.dvd_of_emod_eq_zero h.1.2)) (Int.dvd_of_emod_eq_zero h.2)
  rw [h1] at h2
  lia [Int.le_of_dvd one_pos h2]

private theorem eq_coprimeKeeps_of_beq_zero {B C : ℤ} {r : Bool} (ha : (a == 0) = true)
    (hr : r = decide (B.gcd C = 1)) (hB : B.natAbs = b.natAbs) (hC : C.natAbs = c.natAbs) :
    r = coprimeKeeps a b c := by
  rw [hr, coprimeKeeps_eq, beq_iff_eq.mp ha]
  simp [Int.gcd_eq_natAbs_gcd_natAbs, hB, hC, Int.natAbs_abs]

private theorem eq_coprimeKeeps_of_beq_zero' {B C : ℤ} {r : Bool} (hb : (B == 0) = true)
    (hr : r = decide (a.gcd C = 1)) (hB : B.natAbs = b.natAbs) (hC : C.natAbs = c.natAbs) :
    r = coprimeKeeps a b c := by
  have : b = 0 := by have := beq_iff_eq.mp hb; lia
  rw [hr, coprimeKeeps_eq, this]
  simp [Int.gcd_eq_natAbs_gcd_natAbs, hC, Int.natAbs_abs]

private theorem eq_coprimeKeeps_of_beq_zero'' {B C : ℤ} {r : Bool} (hc : (C == 0) = true)
    (hr : r = decide (a.gcd B = 1)) (hB : B.natAbs = b.natAbs) (hC : C.natAbs = c.natAbs) :
    r = coprimeKeeps a b c := by
  have : c = 0 := by have := beq_iff_eq.mp hc; lia
  rw [hr, coprimeKeeps_eq, this]
  simp [Int.gcd_eq_natAbs_gcd_natAbs, hB]

/-- The odd parts `a'`, `b'` of `a` and of `B = ±b`, for a triple not all even, have the gcd of the
triple with the odd part `c'` of `C = ±c`. -/
private theorem gcd_gcd_eq_of_oddPart {a' b' c' B C : ℤ}
    (ha : 0 < a' ∧ a' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * a' = a)
    (hb : 0 < b' ∧ b' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * b' = B)
    (hc : 0 < c' ∧ c' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * c' = C)
    (h0 : ¬(a % 2 == 0 && b % 2 == 0 && c % 2 == 0) = true) (hB : B.natAbs = b.natAbs)
    (hC : C.natAbs = c.natAbs) : Int.gcd (Int.gcd a b) c = Int.gcd (Int.gcd a' b') c' := by
  obtain ⟨-, ha2, r, hr⟩ := ha
  obtain ⟨-, hb2, s, hs⟩ := hb
  obtain ⟨-, -, t, ht⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  rw [show Int.gcd (Int.gcd a b) c = Int.gcd (Int.gcd a B) C by
    simp only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, hB, hC]]
  refine Int.gcd_gcd_eq_of_two_pow_mul_eq hr hs ht ha2 hb2 ?_
  rcases Int.natAbs_eq_natAbs_iff.mp hB with rfl | rfl <;>
    rcases Int.natAbs_eq_natAbs_iff.mp hC with rfl | rfl <;> lia

private theorem beq_one_eq_coprimeKeeps {a' b' c' B C g r : ℤ} (hr : r = (g.gcd c' : ℤ))
    (hg : g = (a'.gcd b' : ℤ)) (ha : 0 < a' ∧ a' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * a' = a)
    (hb : 0 < b' ∧ b' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * b' = B)
    (hc : 0 < c' ∧ c' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * c' = C)
    (h0 : ¬(a % 2 == 0 && b % 2 == 0 && c % 2 == 0) = true) (hB : B.natAbs = b.natAbs)
    (hC : C.natAbs = c.natAbs) : (r == 1) = coprimeKeeps a b c := by
  rw [coprimeKeeps_eq, gcd_gcd_eq_of_oddPart ha hb hc h0 hB hC, hr, hg, Bool.beq_eq_decide_eq,
    decide_eq_decide]
  lia

private theorem true_eq_coprimeKeeps {a' b' B g : ℤ} (hg1 : (g == 1) = true)
    (hg : g = (a'.gcd b' : ℤ))
    (ha : 0 < a' ∧ a' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * a' = a)
    (hb : 0 < b' ∧ b' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * b' = B)
    (h0 : ¬(a % 2 == 0 && b % 2 == 0 && c % 2 == 0) = true) (hB : B.natAbs = b.natAbs) :
    true = coprimeKeeps a b c := by
  have h1 : Int.gcd a' b' = 1 := by lia [beq_iff_eq.mp hg1]
  obtain ⟨-, ha2, r, hr⟩ := ha
  obtain ⟨-, hb2, s, hs⟩ := hb
  rw [coprimeKeeps_eq, eq_comm, decide_eq_true_iff, show Int.gcd (Int.gcd a b) c =
    Int.gcd (Int.gcd a B) c by simp only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, hB]]
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  by_cases hab : a % 2 = 1 ∨ B % 2 = 1
  · rw [Int.gcd_eq_gcd_of_two_pow_mul_eq hr hs ha2 hb2 hab, h1]
    simp
  · have hc : c % 2 = 1 := by rcases Int.natAbs_eq_natAbs_iff.mp hB with rfl | rfl <;> lia
    rw [← hr, ← hs, Int.gcd_gcd_two_pow_mul_of_emod_two_eq_one hc, h1]
    simp

private theorem pos_and_emod_two_of_gcd {a' b' c' C g : ℤ} (hg : g = (a'.gcd b' : ℤ))
    (ha : 0 < a' ∧ a' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * a' = a)
    (hc : 0 < c' ∧ c' % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * c' = C) :
    0 < g ∧ 0 < c' ∧ g % 2 = 1 ∧ c' % 2 = 1 := by
  refine ⟨by rw [hg]; lia [Int.gcd_pos_of_ne_zero_left b' (a := a') (by lia)], hc.1,
    hg ▸ Int.emod_two_eq_one_of_dvd (Int.gcd_dvd_left ..) ha.2.1, hc.2.1⟩

end Relprime3

/-- `relprime3` makes the test of coprimality of the enumeration (`JPoints.coprimeKeeps`) for
`a ≥ 0`: false when all three coordinates are even, by `relprime2` when one of them is `0`, and else
by the gcd of their odd parts, which is that of the triple (`Int.gcd_gcd_eq_of_two_pow_mul_eq`). -/
@[spec]
theorem relprime3_spec (a b c : ℤ) :
    ⦃ 0 ≤ a ⦄ relprime3 a b c ⦃ fun r ↦ r = coprimeKeeps a b c ⦄ := by
  vcgen [relprime3, forIn_loop_shiftRight_spec, oddGcd_spec, relprime2_spec]
  all_goals with_reducible first
    | exact false_eq_coprimeKeeps ‹_›
    | (refine eq_coprimeKeeps_of_beq_zero ‹_› ‹_› ?_ ?_ <;> first | rfl | exact Int.natAbs_neg _)
    | (refine eq_coprimeKeeps_of_beq_zero' ‹_› ‹_› ?_ ?_ <;> first | rfl | exact Int.natAbs_neg _)
    | (refine eq_coprimeKeeps_of_beq_zero'' ‹_› ‹_› ?_ ?_ <;> first | rfl | exact Int.natAbs_neg _)
    | (refine beq_one_eq_coprimeKeeps ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ?_ ?_ <;>
        first | rfl | exact Int.natAbs_neg _)
    | (refine true_eq_coprimeKeeps ‹_› ‹_› ‹_› ‹_› ‹_› ?_; first | rfl | exact Int.natAbs_neg _)
    | exact pos_and_emod_two_of_oddPart ‹_› ‹_›
    | exact pos_and_emod_two_of_gcd ‹_› ‹_› ‹_›
    | (simp only [Bool.and_eq_true, beq_iff_eq] at *; lia)

/-! ### `MOD3` -/

/-- `MOD3` is the remainder modulo the `m`-th third-stage prime `p` for `0 ≤ x < 2 ^ 16`: it is
`MODP` with the reciprocal `⌈2 ^ 32 / p⌉` of `p ≤ 255` (`JPoints.modp_eq_emod`). -/
theorem mod3_eq {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd) {m : ℕ}
    (hm : m < g.sievePrimes3 - g.sievePrimes2) {x : ℤ} (hx0 : 0 ≤ x) (hx : x < 2 ^ 16) :
    mod3 sd g.sievePrimes2 m x = x % sd.pr[g.sievePrimes2 + m]! := by
  have hn : g.sievePrimes2 + m < g.sievePrimes3 := by lia
  have hR : sd.recip3[m]!.toNat =
      (2 ^ 32 + sd.pr[g.sievePrimes2 + m]! - 1) / sd.pr[g.sievePrimes2 + m]! := by
    rw [h.siftData.recip3_eq hm, Nat.toUInt64_eq]
    exact UInt64.toNat_one_shiftLeft_add_ofNat_sub_one_div (by lia [h.pr_lt_256 hn])
  exact modp_eq_emod (by lia [h.three_le_pr hn]) (h.pr_lt_256 hn).le hR hx0 (by lia)

section Mod3

variable {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd) {m : ℕ}
  (hm : m < g.sievePrimes3 - g.sievePrimes2)

include h hm

/-- `MOD3` of the product of two residues modulo the `m`-th third-stage prime is its remainder. -/
private theorem mod3_mul_eq {x y : ℤ} (hx : 0 ≤ x) (hx' : x < sd.pr[g.sievePrimes2 + m]!)
    (hy : 0 ≤ y)
    (hy' : y < sd.pr[g.sievePrimes2 + m]!) :
    mod3 sd g.sievePrimes2 m (x * y) = x * y % sd.pr[g.sievePrimes2 + m]! := by
  have hp := h.pr_lt_256 (n := g.sievePrimes2 + m) (by lia)
  refine mod3_eq h hm (Int.mul_nonneg hx hy) ?_
  calc x * y < 256 * 256 := mul_lt_mul'' (by lia) (by lia) hx hy
    _ = 2 ^ 16 := by norm_num

/-- `MOD3` of `64 r + j`, for the residue `r = (c / 64) mod p` of the word of `c` and its position
`j = c mod 64` in the word, is the remainder of `c` modulo the `m`-th third-stage prime `p`. -/
private theorem mod3_residue_eq {r0 : ℕ} {res : Array ℕ} {c : ℤ}
    (hres : WordResidues g sd r0 res (c / 64))
    {r : ℕ} (hr : r = (sd.res0[r0 + (g.sievePrimes2 + m)]! + res[g.sievePrimes2 + m]!) %
      sd.pr[g.sievePrimes2 + m]!) :
    mod3 sd g.sievePrimes2 m ((r * longLength + (c % (longLength : ℤ)).toNat : ℕ) : ℤ) =
      c % sd.pr[g.sievePrimes2 + m]! := by
  have hn : g.sievePrimes2 + m < g.sievePrimes3 := by lia
  have hp := h.pr_lt_256 hn
  have hp3 := h.three_le_pr hn
  obtain ⟨-, -, hr'⟩ := hres _ hn
  rw [← hr] at hr'
  have hj := Int.emod_nonneg c (b := 64) (by lia)
  have hj' := Int.emod_lt_of_pos c (b := 64) (by lia)
  have hr0 : r < sd.pr[g.sievePrimes2 + m]! := by rw [hr]; exact Nat.mod_lt _ (by lia)
  have e : (((r * longLength + (c % (longLength : ℤ)).toNat : ℕ) : ℤ)) = 64 * (r : ℤ) + c % 64 := by
    simp only [longLength, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hj, Nat.cast_ofNat]
    ring
  rw [mod3_eq h hm (by lia) (by lia), e, hr', Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia))]
  exact (((Int.mod_modEq _ _).mul_left 64).add_right _).trans
    (by rw [Int.ModEq, Int.mul_ediv_add_emod])

end Mod3

/-! ### The data of the third stage -/

-- The entry `v` of `inva3` at the third-stage prime `m` for the first coordinate `a`: the inverse
-- of `a mod p` from `inverses`, or `0` when `p ∣ a`.
private abbrev Row3InverseP (g : SiftGlobals) (sd : SiftData) (a : ℤ) (m : ℕ) (v : ℤ) : Prop :=
  v = if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
    g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
      (a % sd.pr[g.sievePrimes2 + m]!).toNat]!

private theorem row3SetupInverses_step {g : SiftGlobals} {sd : SiftData} {inva3 b : Array ℤ}
    {a : ℤ} {cur : ℕ} {pref suff : List ℕ}
    (h0 : g.sievePrimes3 - g.sievePrimes2 ≤ inva3.size ∧ 0 ≤ a)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    (h : SetLoopInvariant inva3.size (Row3InverseP g sd a) pref.length b) :
    SetLoopInvariant inva3.size (Row3InverseP g sd a) (pref ++ [cur]).length (b.set! cur
      (if (a.tmod sd.pr[g.sievePrimes2 + cur]! == 0) = true then 0 else
        g.tables.inverses[g.pnn[g.sievePrimes2 + cur]! * maxPrimeEven +
          (a.tmod sd.pr[g.sievePrimes2 + cur]!).toNat]!)) :=
  h.set! hc h0.1 (by simp only [Int.tmod_eq_emod_of_nonneg h0.2, beq_iff_eq])

private theorem row3SetupInverses_post {g : SiftGlobals} {sd : SiftData} {inva3 r : Array ℤ}
    {a : ℤ} {N : ℕ}
    (h : SetLoopInvariant inva3.size (Row3InverseP g sd a) (ForIn.toList [:N]).length r) :
    r.size = inva3.size ∧ ∀ m < N, r[m]! = if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
      g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
        (a % sd.pr[g.sievePrimes2 + m]!).toNat]! :=
  ⟨h.1, h.forall_lt⟩

attribute [local irreducible] SetLoopInvariant in
/-- `row3_setup` sets `inva3[m]`, for each third-stage prime `p`, to the inverse of `a mod p` from
`inverses`, or `0` when `p ∣ a`, for `a ≥ 0`, where the remainder of C is the Euclidean one. -/
@[spec]
theorem row3SetupInverses_spec (g : SiftGlobals) (sd : SiftData) (inva3 : Array ℤ) (a : ℤ) :
    ⦃ g.sievePrimes3 - g.sievePrimes2 ≤ inva3.size ∧ 0 ≤ a ⦄
    row3SetupInverses g sd inva3 a
    ⦃ fun r ↦ r.size = inva3.size ∧ ∀ m < g.sievePrimes3 - g.sievePrimes2,
        r[m]! = if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
          g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
            (a % sd.pr[g.sievePrimes2 + m]!).toNat]! ⦄ := by
  vcgen [row3SetupInverses] invariants
  · fun pref _ r ↦ SetLoopInvariant inva3.size (Row3InverseP g sd a) pref.length r
  all_goals with_reducible first
    | exact row3SetupInverses_step ‹_› ‹_› ‹_›
    | exact setLoopInvariant_nil _ rfl
    | exact row3SetupInverses_post ‹_›

section Row3Factors

variable {g : SiftGlobals} {sd : SiftData} {inva3 mult3 b1 : Array ℤ} {tab3 b2 : Array Tab3Ptr}
  {b : ℤ} {cur : ℕ} {pref suff : List ℕ}

-- The entries `(v₁, v₂)` of `mult3` and `tab3` at the third-stage prime `m` for the second
-- coordinate `b` and the inverses `inva3`: those of `JPoints.row3SetupEntry`.
private abbrev Row3FactorP (g : SiftGlobals) (sd : SiftData) (inva3 : Array ℤ) (b : ℤ) (m : ℕ)
    (v₁ : ℤ) (v₂ : Tab3Ptr) : Prop :=
  (v₁, v₂) = row3SetupEntry g sd inva3[m]! b m

private theorem row3SetupFactors_step_pointOnJ
    (hs : g.sievePrimes3 - g.sievePrimes2 ≤ mult3.size ∧
      g.sievePrimes3 - g.sievePrimes2 ≤ tab3.size)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) pref (cur :: suff) (b1, b2))
    {bp : ℤ} (hbp : bp = b % sd.pr[g.sievePrimes2 + cur]!) (hi : (inva3[cur]! != 0) = true) :
    Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) (pref ++ [cur]) suff
      (b1.set! cur inva3[cur]!, b2.set! cur (.pointOnJ ((g.pnn[g.sievePrimes2 + cur]! *
        maxPrimeEven + (mod3 sd g.sievePrimes2 cur (bp * (b1.set! cur inva3[cur]!)[cur]!)).toNat) *
          maxPrimeEven))) := by
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  refine h.step hc hs ?_
  rw [Array.getElem!_set! (by lia [h.1]), hbp]
  simp_all [Row3FactorP, row3SetupEntry]

private theorem row3SetupFactors_step_fSquare
    (hs : g.sievePrimes3 - g.sievePrimes2 ≤ mult3.size ∧
      g.sievePrimes3 - g.sievePrimes2 ≤ tab3.size)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) pref (cur :: suff) (b1, b2))
    {bp : ℤ} (hbp : bp = b % sd.pr[g.sievePrimes2 + cur]!) (hi : ¬(inva3[cur]! != 0) = true)
    (hb : (bp != 0) = true) :
    Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) (pref ++ [cur]) suff
      (b1.set! cur g.tables.inverses[g.pnn[g.sievePrimes2 + cur]! * maxPrimeEven + bp.toNat]!,
        b2.set! cur (.fSquare (g.pnn[g.sievePrimes2 + cur]! * maxPrimeEven))) := by
  refine h.step hc hs ?_
  simp_all [Row3FactorP, row3SetupEntry]

private theorem row3SetupFactors_step_allOnes
    (hs : g.sievePrimes3 - g.sievePrimes2 ≤ mult3.size ∧
      g.sievePrimes3 - g.sievePrimes2 ≤ tab3.size)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) pref (cur :: suff) (b1, b2))
    {bp : ℤ} (hbp : bp = b % sd.pr[g.sievePrimes2 + cur]!) (hi : ¬(inva3[cur]! != 0) = true)
    (hb : ¬(bp != 0) = true) :
    Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b) (pref ++ [cur]) suff
      (b1.set! cur 0, b2.set! cur .allOnes) := by
  refine h.step hc hs ?_
  simp_all [Row3FactorP, row3SetupEntry]

end Row3Factors

/-- `row3_setup` sets the factor `mult3[m]` and the row `tab3[m]` of each third-stage prime as
`JPoints.row3SetupEntry` gives them, the residue of `b` corrected into `[0, p)`. -/
@[spec]
theorem row3SetupFactors_spec (g : SiftGlobals) (sd : SiftData) (inva3 mult3 : Array ℤ)
    (tab3 : Array Tab3Ptr) (b : ℤ) :
    ⦃ g.sievePrimes3 - g.sievePrimes2 ≤ mult3.size ∧ g.sievePrimes3 - g.sievePrimes2 ≤ tab3.size ⦄
    row3SetupFactors g sd inva3 mult3 tab3 b
    ⦃ fun r ↦ r.1.size = mult3.size ∧ r.2.size = tab3.size ∧
        ∀ m < g.sievePrimes3 - g.sievePrimes2,
          (r.1[m]!, r.2[m]!) = row3SetupEntry g sd inva3[m]! b m ⦄ := by
  vcgen [row3SetupFactors] invariants
  · Set2Invariant mult3 tab3 (Row3FactorP g sd inva3 b)
  all_goals with_reducible first
    | exact set2Invariant_nil
    | exact Set2Invariant.post ‹_›
    | exact row3SetupFactors_step_pointOnJ ‹_› ‹_› ‹_› (Int.tmod_add_natCast_eq_emod ‹_›) ‹_›
    | exact row3SetupFactors_step_pointOnJ ‹_› ‹_› ‹_› (Int.tmod_natCast_eq_emod ‹_›) ‹_›
    | exact row3SetupFactors_step_fSquare ‹_› ‹_› ‹_› (Int.tmod_add_natCast_eq_emod ‹_›) ‹_› ‹_›
    | exact row3SetupFactors_step_fSquare ‹_› ‹_› ‹_› (Int.tmod_natCast_eq_emod ‹_›) ‹_› ‹_›
    | exact row3SetupFactors_step_allOnes ‹_› ‹_› ‹_› (Int.tmod_add_natCast_eq_emod ‹_›) ‹_› ‹_›
    | exact row3SetupFactors_step_allOnes ‹_› ‹_› ‹_› (Int.tmod_natCast_eq_emod ‹_›) ‹_› ‹_›

section Row3Setup

variable {g : SiftGlobals} {sd : SiftData} {r : Row3Cache} {a b : ℤ} {inva mult : Array ℤ}
  {tab : Array Tab3Ptr}

-- The data of the third stage of a row `(a, b)`, from the inverses of `a` and the factors and rows
-- of `b`, sized as those of consistent data `r`, are consistent.
private theorem Row3Cache.wf_mk (hr : Row3Cache.WF g sd r) (hsize : inva.size = r.inva3.size)
    (hinv : ∀ m < g.sievePrimes3 - g.sievePrimes2, inva[m]! =
      if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
        g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
          (a % sd.pr[g.sievePrimes2 + m]!).toNat]!)
    (hf : (mult, tab).1.size = r.mult3.size ∧ (mult, tab).2.size = r.tab3.size ∧
      ∀ m < g.sievePrimes3 - g.sievePrimes2,
        ((mult, tab).1[m]!, (mult, tab).2[m]!) = row3SetupEntry g sd inva[m]! b m) :
    Row3Cache.WF g sd { tab3 := tab, mult3 := mult, row3A := a, row3B := b, inva3 := inva } where
  size_tab3 := hf.2.1.trans hr.size_tab3
  size_mult3 := hf.1.trans hr.size_mult3
  size_inva3 := hsize.trans hr.size_inva3
  inva3_eq _ _ hm := hinv _ hm
  mult3_eq _ _ hm := congr(Prod.fst $(hf.2.2 _ hm))
  tab3_eq _ _ hm := congr(Prod.snd $(hf.2.2 _ hm))

private theorem row3Cache_wf_of_inverses
    (h : Row3Cache.WF g sd r ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a)
    (hinv : inva.size = r.inva3.size ∧ ∀ m < g.sievePrimes3 - g.sievePrimes2, inva[m]! =
      if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
        g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
          (a % sd.pr[g.sievePrimes2 + m]!).toNat]!)
    (hf : (mult, tab).1.size = r.mult3.size ∧ (mult, tab).2.size = r.tab3.size ∧
      ∀ m < g.sievePrimes3 - g.sievePrimes2,
        ((mult, tab).1[m]!, (mult, tab).2[m]!) = row3SetupEntry g sd inva[m]! b m) :
    Row3Cache.WF g sd { tab3 := tab, mult3 := mult, row3A := a, row3B := b, inva3 := inva } :=
  Row3Cache.wf_mk h.1 hinv.1 hinv.2 hf

private theorem row3Cache_wf_of_row3A (hA : ¬(a != r.row3A) = true)
    (h : Row3Cache.WF g sd r ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a)
    (hf : (mult, tab).1.size = r.mult3.size ∧ (mult, tab).2.size = r.tab3.size ∧
      ∀ m < g.sievePrimes3 - g.sievePrimes2,
        ((mult, tab).1[m]!, (mult, tab).2[m]!) = row3SetupEntry g sd r.inva3[m]! b m) :
    Row3Cache.WF g sd { tab3 := tab, mult3 := mult, row3A := a, row3B := b, inva3 := r.inva3 } := by
  have hA : a = r.row3A := by simpa using hA
  exact Row3Cache.wf_mk h.1 rfl (fun m hm ↦ hA ▸ h.1.inva3_eq (hA ▸ h.2.2) hm) hf

private theorem size_le_of_row3Cache_wf
    (h : Row3Cache.WF g sd r ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a) :
    g.sievePrimes3 - g.sievePrimes2 ≤ r.mult3.size ∧
      g.sievePrimes3 - g.sievePrimes2 ≤ r.tab3.size :=
  ⟨by lia [h.1.size_mult3], by lia [h.1.size_tab3]⟩

private theorem size_le_inva3_of_row3Cache_wf
    (h : Row3Cache.WF g sd r ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a) :
    g.sievePrimes3 - g.sievePrimes2 ≤ r.inva3.size ∧ 0 ≤ a :=
  ⟨by lia [h.1.size_inva3], h.2.2⟩

end Row3Setup

/-- `row3_setup` leaves consistent data of the third stage (`JPoints.Row3Cache.WF`) for the row
`(a, b)` with `a ≥ 0`: the inverses of `a` recomputed for a new `a` and kept otherwise, as the
consistent data of the row before hold them, and the factors and the rows of `b`. -/
@[spec]
theorem row3Setup_spec (g : SiftGlobals) (sd : SiftData) (r : Row3Cache) (a b : ℤ) :
    ⦃ Row3Cache.WF g sd r ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a ⦄
    row3Setup g sd r a b
    ⦃ fun r' ↦ Row3Cache.WF g sd r' ∧ r'.row3A = a ∧ r'.row3B = b ⦄ := by
  vcgen [row3Setup]
  all_goals with_reducible first
    | exact size_le_inva3_of_row3Cache_wf ‹_›
    | exact size_le_of_row3Cache_wf ‹_›
    | exact row3Cache_wf_of_inverses ‹_› ‹_› ‹_›
    | exact row3Cache_wf_of_row3A ‹_› ‹_› ‹_›

/-! ### The third stage of a bit -/

section CheckBit

variable {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd) {m : ℕ}
  (hm : m < g.sievePrimes3 - g.sievePrimes2)

include h hm

private theorem get_row3SetupEntry_allOnes {a b c : ℤ} (hA : a % sd.pr[g.sievePrimes2 + m]! = 0)
    (hB : b % sd.pr[g.sievePrimes2 + m]! = 0) :
    (row3SetupEntry g sd 0 b m).2.get g.curve sd.allOnes (mod3 sd g.sievePrimes2 m
      (c % sd.pr[g.sievePrimes2 + m]! * (row3SetupEntry g sd 0 b m).1)).toNat =
      g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  have hP := h.pr_eq (n := g.sievePrimes2 + m) (by lia)
  have h00 : mod3 sd g.sievePrimes2 m 0 = 0 := by
    rw [mod3_eq h hm le_rfl (by norm_num), Int.zero_emod]
  simp only [row3SetupEntry, CurveTables.admits3, ← hP]
  simp [hA, hB, Tab3Ptr.get, h00,
    h.siftData.allOnes_eq (show 0 < maxPrimeEven by lia [maxPrime_lt_maxPrimeEven])]

private theorem inverses_eq_refInverse {x : ℤ} (hx : x % sd.pr[g.sievePrimes2 + m]! ≠ 0) :
    g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
      (x % sd.pr[g.sievePrimes2 + m]!).toNat]! =
      refInverse sd.pr[g.sievePrimes2 + m]! (x % sd.pr[g.sievePrimes2 + m]!).toNat ∧
    0 < (x % sd.pr[g.sievePrimes2 + m]!).toNat := by
  have hn : g.sievePrimes2 + m < g.sievePrimes3 := by lia
  have hp3 := h.three_le_pr hn
  have h0 : 0 < (x % (sd.pr[g.sievePrimes2 + m]! : ℤ)).toNat := by
    lia [Int.emod_nonneg x (b := sd.pr[g.sievePrimes2 + m]!) (by lia)]
  have := h.tables.inverses (h.pnn_lt hn) h0 (h.pr_eq hn ▸ Int.toNat_emod_lt x (by lia))
  exact ⟨by rwa [← h.pr_eq hn] at this, h0⟩

private theorem get_row3SetupEntry_fSquare {a b c : ℤ} (hA : a % sd.pr[g.sievePrimes2 + m]! = 0)
    (hB : b % sd.pr[g.sievePrimes2 + m]! ≠ 0) :
    (row3SetupEntry g sd 0 b m).2.get g.curve sd.allOnes (mod3 sd g.sievePrimes2 m
      (c % sd.pr[g.sievePrimes2 + m]! * (row3SetupEntry g sd 0 b m).1)).toNat =
      g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  have hp3 := h.three_le_pr (n := g.sievePrimes2 + m) (by lia)
  obtain ⟨hinv, hB0⟩ := inverses_eq_refInverse h hm hB
  have hI := refInverse_lt (b % (sd.pr[g.sievePrimes2 + m]! : ℤ)).toNat
    (p := sd.pr[g.sievePrimes2 + m]!) (by lia)
  simp only [row3SetupEntry, CurveTables.admits3, ← h.pr_eq (n := g.sievePrimes2 + m) (by lia),
    ↓reduceIte, ne_eq, not_true_eq_false, hB, not_false_eq_true, hinv, Tab3Ptr.get]
  rw [mod3_mul_eq h hm (Int.emod_nonneg c (by lia)) (Int.emod_lt_of_pos c (by lia)) (by lia)
    (by lia), Int.toNat_emod_mul_emod c _ (by lia)]
  simp [hA, hB0.ne']

private theorem get_row3SetupEntry_pointOnJ {a b c : ℤ} (hA : a % sd.pr[g.sievePrimes2 + m]! ≠ 0) :
    (row3SetupEntry g sd g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
      (a % sd.pr[g.sievePrimes2 + m]!).toNat]! b m).2.get g.curve sd.allOnes
      (mod3 sd g.sievePrimes2 m (c % sd.pr[g.sievePrimes2 + m]! *
        (row3SetupEntry g sd g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
          (a % sd.pr[g.sievePrimes2 + m]!).toNat]! b m).1)).toNat =
      g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  have hn : g.sievePrimes2 + m < g.sievePrimes3 := by lia
  have hp3 := h.three_le_pr hn
  obtain ⟨hinv, hA0⟩ := inverses_eq_refInverse h hm hA
  have hI := refInverse_lt (a % (sd.pr[g.sievePrimes2 + m]! : ℤ)).toNat
    (p := sd.pr[g.sievePrimes2 + m]!) (by lia)
  have hI0 := refInverse_ne_zero (h.prime_pr hn) hA0 (Int.toNat_emod_lt a (by lia))
  simp only [row3SetupEntry, CurveTables.admits3, ← h.pr_eq hn, hinv, ne_eq, Nat.cast_eq_zero, hI0,
    not_false_eq_true, ↓reduceIte, Tab3Ptr.get]
  rw [mod3_mul_eq h hm (Int.emod_nonneg c (by lia)) (Int.emod_lt_of_pos c (by lia)) (by lia)
    (by lia), mod3_mul_eq h hm (Int.emod_nonneg b (by lia)) (Int.emod_lt_of_pos b (by lia))
    (by lia) (by lia), Int.toNat_emod_mul_emod c _ (by lia), Int.toNat_emod_mul_emod b _ (by lia)]
  simp [hA0.ne']

/-- The entry of the row of the third stage that `row3_setup` sets for `(a, b)`, at the class of
`c` multiplied by its factor, is the class test of the third stage at `(a, b, c)`. -/
theorem get_row3SetupEntry_eq_admits3 (a b c : ℤ) :
    (row3SetupEntry g sd (if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
        g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
          (a % sd.pr[g.sievePrimes2 + m]!).toNat]!) b m).2.get g.curve sd.allOnes
      (mod3 sd g.sievePrimes2 m (c % sd.pr[g.sievePrimes2 + m]! *
        (row3SetupEntry g sd (if a % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
          g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
            (a % sd.pr[g.sievePrimes2 + m]!).toNat]!) b m).1)).toNat =
      g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  by_cases hA : a % (sd.pr[g.sievePrimes2 + m]! : ℤ) = 0
  · simp only [hA, ↓reduceIte]
    by_cases hB : b % (sd.pr[g.sievePrimes2 + m]! : ℤ) = 0
    · exact get_row3SetupEntry_allOnes h hm hA hB
    · exact get_row3SetupEntry_fSquare h hm hA hB
  · simp only [hA, ↓reduceIte]
    exact get_row3SetupEntry_pointOnJ h hm hA

/-- The entry that `check_bit` reads from the row `tab3[m]` of consistent data of the third stage
for the row `(a, b)`, at the class of `c` multiplied by the factor `mult3[m]`, is the class test of
the third stage at `(a, b, c)` for the `m`-th third-stage prime. -/
private theorem get_tab3_eq_admits3 {row3 : Row3Cache} {a b c : ℤ} {r0 : ℕ} {res : Array ℕ}
    (hw : Row3Cache.WF g sd row3 ∧ row3.row3A = a ∧ row3.row3B = b) (ha : 0 ≤ a)
    (hres : WordResidues g sd r0 res (c / 64)) {r : ℕ}
    (hr : r = (sd.res0[r0 + (g.sievePrimes2 + m)]! + res[g.sievePrimes2 + m]!) %
      sd.pr[g.sievePrimes2 + m]!) :
    row3.tab3[m]!.get g.curve sd.allOnes (mod3 sd g.sievePrimes2 m
      (mod3 sd g.sievePrimes2 m ((r * longLength + (c % (longLength : ℤ)).toNat : ℕ) : ℤ) *
        row3.mult3[m]!)).toNat = g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  have hn : g.sievePrimes2 + m < g.sievePrimes3 := by lia
  obtain ⟨hw, rfl, rfl⟩ := hw
  rw [mod3_residue_eq h hm hres hr, hw.tab3_eq ha hm, hw.mult3_eq ha hm, hw.inva3_eq ha hm]
  exact get_row3SetupEntry_eq_admits3 h hm _ _ c

end CheckBit

/-- The invariant of the loop of `JPoints.checkBit` over the third-stage primes, with its early
return: before a return, every prime below the cursor admits the class of `(a, b, c)`; after it, the
result is the test of the third stage with consistent data of the third stage for the row. -/
def CheckBitInvariant (g : SiftGlobals) (sd : SiftData) (a b c : ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × Row3Cache) × PUnit) Prop :=
  fun pref suff st ↦ st.1.elim (∀ m ∈ pref, g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c)
    fun r ↦ suff = [] ∧ r.1 = stage3Keeps g a b c ∧ Row3Cache.WF g sd r.2 ∧ r.2.row3A = a ∧
      r.2.row3B = b

section CheckBitLoop

variable {g : SiftGlobals} {sd : SiftData} {row3 row3' : Row3Cache} {a b c : ℤ} {r0 : ℕ}
  {res : Array ℕ} {pref suff : List ℕ} {cur : ℕ}

private theorem stage3Keeps_eq_true_iff :
    stage3Keeps g a b c = true ↔
      ∀ m < g.sievePrimes3 - g.sievePrimes2, g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c := by
  simp only [stage3Keeps, List.all_eq_true, List.mem_range'_1]
  exact ⟨fun h m hm ↦ h _ ⟨by lia, by lia⟩, fun h n hn ↦ by
    simpa [show g.sievePrimes2 + (n - g.sievePrimes2) = n by lia] using
      h (n - g.sievePrimes2) (by lia)⟩

private theorem row3_of_not_bne (h : IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧
      WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a)
    (hn : ¬(a != row3.row3A || b != row3.row3B) = true) :
    Row3Cache.WF g sd row3 ∧ row3.row3A = a ∧ row3.row3B = b := by
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hn
  exact ⟨h.2.1, hn.1.symm, hn.2.symm⟩

private theorem row3Setup_pre_of_checkBit (h : IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧
      WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a) :
    Row3Cache.WF g sd row3 ∧ g.sievePrimes3 - g.sievePrimes2 ≤ numPrimes ∧ 0 ≤ a :=
  ⟨h.2.1, by lia [h.1.sievePrimes3_le_numPrimes], h.2.2.2⟩

private theorem residue_eq_sub_of_le (h : IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧
      WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    (hle : sd.pr[g.sievePrimes2 + cur]! ≤ sd.res0[r0 + (g.sievePrimes2 + cur)]! +
      res[g.sievePrimes2 + cur]!) :
    sd.res0[r0 + (g.sievePrimes2 + cur)]! + res[g.sievePrimes2 + cur]! -
        sd.pr[g.sievePrimes2 + cur]! =
      (sd.res0[r0 + (g.sievePrimes2 + cur)]! + res[g.sievePrimes2 + cur]!) %
        sd.pr[g.sievePrimes2 + cur]! := by
  have := h.2.2.1 (g.sievePrimes2 + cur) (by lia [Std.Legacy.Range.lt_of_toList_eq_append_cons hc])
  rw [Nat.mod_eq_ite_of_lt_two_mul (by lia)]
  simp [hle]

private theorem checkBitInvariant_nil {l : List ℕ} : CheckBitInvariant g sd a b c [] l (none, ⟨⟩) :=
  fun _ h ↦ nomatch h

private theorem CheckBitInvariant.forall_mem {st : Option (Bool × Row3Cache) × PUnit}
    (h : CheckBitInvariant g sd a b c pref (cur :: suff) st) :
    ∀ m ∈ pref, g.curve.admits3 g.pnn[g.sievePrimes2 + m]! a b c :=
  (Option.eq_none_and_of_elim_cons h).2

private theorem checkBitInvariant_step (h : IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧
      WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a)
    (hw : Row3Cache.WF g sd row3' ∧ row3'.row3A = a ∧ row3'.row3B = b)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    {st : Option (Bool × Row3Cache) × PUnit}
    (hi : CheckBitInvariant g sd a b c pref (cur :: suff) st)
    {r : ℕ} (hr : r = (sd.res0[r0 + (g.sievePrimes2 + cur)]! + res[g.sievePrimes2 + cur]!) %
      sd.pr[g.sievePrimes2 + cur]!)
    (hget : ¬(!row3'.tab3[cur]!.get g.curve sd.allOnes (mod3 sd g.sievePrimes2 cur
      (mod3 sd g.sievePrimes2 cur ((r * longLength + (c % (longLength : ℤ)).toNat : ℕ) : ℤ) *
        row3'.mult3[cur]!)).toNat) = true) :
    CheckBitInvariant g sd a b c (pref ++ [cur]) suff (none, ⟨⟩) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  rw [get_tab3_eq_admits3 h.1 hcur hw h.2.2.2 h.2.2.1 hr] at hget
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hi.forall_mem m hm
  · rw [List.mem_singleton.mp hm]
    simpa using hget

private theorem checkBitInvariant_return (h : IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧
      WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a)
    (hw : Row3Cache.WF g sd row3' ∧ row3'.row3A = a ∧ row3'.row3B = b)
    (hc : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff)
    {r : ℕ} (hr : r = (sd.res0[r0 + (g.sievePrimes2 + cur)]! + res[g.sievePrimes2 + cur]!) %
      sd.pr[g.sievePrimes2 + cur]!)
    (hget : (!row3'.tab3[cur]!.get g.curve sd.allOnes (mod3 sd g.sievePrimes2 cur
      (mod3 sd g.sievePrimes2 cur ((r * longLength + (c % (longLength : ℤ)).toNat : ℕ) : ℤ) *
        row3'.mult3[cur]!)).toNat) = true) {l : List ℕ} :
    CheckBitInvariant g sd a b c l [] (some (false, row3'), ⟨⟩) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  rw [get_tab3_eq_admits3 h.1 hcur hw h.2.2.2 h.2.2.1 hr] at hget
  refine ⟨rfl, ?_, hw⟩
  rw [eq_comm, Bool.eq_false_iff, ne_eq, stage3Keeps_eq_true_iff]
  exact fun hall ↦ by simp [hall cur hcur] at hget

private theorem checkBitInvariant_post_some {st : Option (Bool × Row3Cache) × PUnit} {x : Bool}
    {y : Row3Cache} {l : List ℕ} (hi : CheckBitInvariant g sd a b c l [] st)
    (hst : st.1 = some (x, y)) :
    x = stage3Keeps g a b c ∧ Row3Cache.WF g sd (x, y).2 ∧ (x, y).2.row3A = a ∧
      (x, y).2.row3B = b := by
  obtain ⟨o, u⟩ := st
  subst hst
  exact hi.2

private theorem checkBitInvariant_post_none
    (hw : Row3Cache.WF g sd row3' ∧ row3'.row3A = a ∧ row3'.row3B = b)
    {st : Option (Bool × Row3Cache) × PUnit}
    (hi : CheckBitInvariant g sd a b c (ForIn.toList [:g.sievePrimes3 - g.sievePrimes2]) [] st)
    (hst : st.1 = none) :
    true = stage3Keeps g a b c ∧ Row3Cache.WF g sd (true, row3').2 ∧ (true, row3').2.row3A = a ∧
      (true, row3').2.row3B = b := by
  obtain ⟨o, u⟩ := st
  subst hst
  refine ⟨(stage3Keeps_eq_true_iff.mpr fun m hm ↦ hi m ?_).symm, hw⟩
  exact Std.Legacy.Range.mem_toList_of_lt hm

end CheckBitLoop

/-- `check_bit` makes the test of the third stage (`JPoints.stage3Keeps`) of the bit `c` of the row
`(a, b)`, `a ≥ 0`, from consistent data of the third stage, which it leaves consistent for the row:
the data set up by `row3_setup` unless they are for the row, and each third-stage prime tested by
the entry of its row at the class of `c` (`JPoints.get_tab3_eq_admits3`). -/
@[spec]
theorem checkBit_spec (g : SiftGlobals) (sd : SiftData) (row3 : Row3Cache) (a b c : ℤ) (r0 : ℕ)
    (res : Array ℕ) :
    ⦃ IsStageSetup g sd ∧ Row3Cache.WF g sd row3 ∧ WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a ⦄
    checkBit g sd row3 a b c r0 res
    ⦃ fun r ↦ r.1 = stage3Keeps g a b c ∧ Row3Cache.WF g sd r.2 ∧ r.2.row3A = a ∧
        r.2.row3B = b ⦄ := by
  vcgen [checkBit] invariants
  · CheckBitInvariant g sd a b c
  · CheckBitInvariant g sd a b c
  -- the data of the third stage that the row already has, in the branch without `row3_setup`
  all_goals try have := row3_of_not_bne ‹_› ‹_›
  all_goals with_reducible first
    | exact row3Setup_pre_of_checkBit ‹_›
    | exact checkBitInvariant_nil
    | exact checkBitInvariant_post_some ‹_› ‹_›
    | exact checkBitInvariant_post_none ‹_› ‹_› ‹_›
    | exact checkBitInvariant_step ‹_› ‹_› ‹_› ‹_› (residue_eq_sub_of_le ‹_› ‹_› ‹_›) ‹_›
    | exact checkBitInvariant_step ‹_› ‹_› ‹_› ‹_› (Nat.mod_eq_of_lt (Nat.lt_of_not_le ‹_›)).symm
        ‹_›
    | exact checkBitInvariant_return ‹_› ‹_› ‹_› (residue_eq_sub_of_le ‹_› ‹_› ‹_›) ‹_›
    | exact checkBitInvariant_return ‹_› ‹_› ‹_› (Nat.mod_eq_of_lt (Nat.lt_of_not_le ‹_›)).symm ‹_›

end JPoints

end
