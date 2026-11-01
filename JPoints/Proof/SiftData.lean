/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.Loops
public import Std.WP

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.RowWords
import JPoints.Proof.Values
import Std.Tactic.Do

/-!
# The contracts of the static data of the sieve

The static data that `init_sift` of `j-points` computes once for the run, in the terms of
`JPoints.SiftData.WF`: the data of the sieving primes, that is the primes, the lengths of the rows
and of the blocks of their sieve tables, the row of the third stage that admits every class and the
reciprocals of the third stage (`JPoints.SiftData.PrimesWF`, `JPoints.initSiftPrimes_spec`); the
chunks of a row, each with the walks of the first-stage primes over it, stated by the value of
`JPoints.initSiftWalk` (`JPoints.initSiftWalk_spec`), and the residues of its first word
(`JPoints.ChunkSpec.WF`, `JPoints.initSiftChunk_spec`); the residues of the positions in a chunk and
the reciprocals of the sieving primes (`JPoints.SiftData.ResiduesWF`,
`JPoints.initSiftResidues_spec`); and the static data from these parts
(`JPoints.SiftData.PrimesWF.wf`), from which `JPoints.initSift_spec` follows.

## Main definitions

* `JPoints.SiftData.PrimesWF`, `JPoints.ChunkSpec.WF`, `JPoints.SiftData.ResiduesWF`: the parts of
  the static data.
* `JPoints.SiftPrimesInvariant`, `JPoints.Recip3Invariant`, `JPoints.ChunkWalksInvariant`,
  `JPoints.ChunkResiduesInvariant`, `JPoints.ResiduesInvariant`, `JPoints.ResiduesLoopInvariant`:
  the invariants of the loops of `init_sift`.

## Main statements

* `JPoints.initSiftPrimes_spec`, `JPoints.initSiftWalk_spec`, `JPoints.initSiftChunk_spec`,
  `JPoints.initSiftResidues_spec`: the contracts of the parts of `init_sift`.
* `JPoints.SiftData.PrimesWF.wf`: the static data from their parts.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. A component that writes some fields of the
static data states the others by a frame, the static data that it is given with the fields that it
writes replaced (`r = { sd with pr := r.pr, … }`), and what it writes by a predicate on its result
alone. The loops that write or push the entries of an array in turn share their invariants
(`JPoints.SetLoopInvariant`, `JPoints.PushLoopInvariant`, with a predicate on each entry), the loops
of `init_sift` by abbreviations of them. The reciprocals of the sieving primes are doubles stored as
`init_sift` computes them, so that no fact about doubles is needed.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The sieving primes -/

/-- The data of the sieving primes in the static data `sd` of the sieve as `init_sift` sets them
for the globals `g` of the sieve, the fields of `JPoints.SiftData.WF` that
`JPoints.initSiftPrimes` writes. -/
structure SiftData.PrimesWF (sd : SiftData) (g : SiftGlobals) : Prop where
  /-- The sieving primes. -/
  pr_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.pr[n]! = sievingPrime g.pnn n
  /-- The lengths of the rows of the sieve tables. -/
  rowlen_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.rowlen[n]! = sd.pr[n]! + 1
  /-- The lengths of the blocks of the rows of one residue class of `a`. -/
  blocklen_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.blocklen[n]! = sd.pr[n]! * (sd.pr[n]! + 1)
  /-- The row of the third stage that admits every class. -/
  allOnes_eq {x : ℕ} (hx : x < maxPrimeEven) : sd.allOnes[x]! = true
  /-- The reciprocals `⌈2 ^ 32 / p⌉` of the primes of the third stage. -/
  recip3_eq {m : ℕ} (hm : m < g.sievePrimes3 - g.sievePrimes2) :
    sd.recip3[m]! = ((1 : UInt64) <<< 32 + (sd.pr[g.sievePrimes2 + m]!).toUInt64 - 1) /
      (sd.pr[g.sievePrimes2 + m]!).toUInt64

/-- The invariant of the loop of `JPoints.initSiftPrimes` over the sieving primes: the arrays
`s = (pr, rowlen, blocklen)` of `JPoints.numPrimes` entries hold the first `k` sieving primes, the
lengths of the rows of their sieve tables and those of their blocks. -/
def SiftPrimesInvariant (g : SiftGlobals) (k : ℕ) (s : Array ℕ × Array ℕ × Array ℕ) : Prop :=
  SetLoopInvariant numPrimes (fun n p ↦ p = sievingPrime g.pnn n) k s.1 ∧
    SetLoopInvariant numPrimes (fun n l ↦ l = sievingPrime g.pnn n + 1) k s.2.1 ∧
    SetLoopInvariant numPrimes (fun n l ↦ l = sievingPrime g.pnn n * (sievingPrime g.pnn n + 1)) k
      s.2.2

/-- The invariant of the loop of `JPoints.initSiftPrimes` over the primes of the third stage: the
array `a` of `JPoints.numPrimes` entries holds the reciprocals `⌈2 ^ 32 / p⌉` of the first `k`
primes `p` of the third stage, as `init_sift` computes them. -/
abbrev Recip3Invariant (g : SiftGlobals) (k : ℕ) (a : Array UInt64) : Prop :=
  SetLoopInvariant numPrimes (fun m x ↦ x = ((1 : UInt64) <<< 32 +
    (sievingPrime g.pnn (g.sievePrimes2 + m)).toUInt64 - 1) /
      (sievingPrime g.pnn (g.sievePrimes2 + m)).toUInt64) k a

theorem siftPrimesInvariant_nil (g : SiftGlobals) {sd : SiftData} (hs : sd.Sized) :
    SiftPrimesInvariant g ([] : List ℕ).length (sd.pr, sd.rowlen, sd.blocklen) :=
  ⟨setLoopInvariant_nil _ hs.size_pr, setLoopInvariant_nil _ hs.size_rowlen,
    setLoopInvariant_nil _ hs.size_blocklen⟩

theorem SiftPrimesInvariant.one_le_getElem!_set! {g : SiftGlobals}
    (h3 : g.sievePrimes3 ≤ numPrimes) (hpnn : ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {pr rowlen blocklen : Array ℕ} (h : SiftPrimesInvariant g pref.length (pr, rowlen, blocklen)) :
    1 ≤ (pr.set! cur primeTable[g.pnn[cur]!]!)[cur]! := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [Array.getElem!_set!_self _ _ _ (by lia [h.1.1])]
  lia [three_le_getElem!_primeTable (hpnn cur hc)]

theorem SiftPrimesInvariant.set! {g : SiftGlobals} (h3 : g.sievePrimes3 ≤ numPrimes)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {pr rowlen blocklen : Array ℕ} (h : SiftPrimesInvariant g pref.length (pr, rowlen, blocklen))
    {l : ℕ} (hlen : l = (pr.set! cur primeTable[g.pnn[cur]!]!)[cur]! + 1) :
    SiftPrimesInvariant g (pref ++ [cur]).length (pr.set! cur primeTable[g.pnn[cur]!]!,
      rowlen.set! cur l, blocklen.set! cur
        ((pr.set! cur primeTable[g.pnn[cur]!]!)[cur]! * (rowlen.set! cur l)[cur]!)) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2, h3'⟩ := h
  have e1 : (pr.set! cur primeTable[g.pnn[cur]!]!)[cur]! = sievingPrime g.pnn cur :=
    Array.getElem!_set!_self _ _ _ (by lia [h1.1])
  have e2 : (rowlen.set! cur l)[cur]! = l := Array.getElem!_set!_self _ _ _ (by lia [h2.1])
  exact ⟨h1.set! hl h3 rfl, h2.set! hl h3 (e1 ▸ hlen), h3'.set! hl h3 (by rw [e1, e2, hlen, e1])⟩

theorem SiftPrimesInvariant.recip3Invariant_set! {g : SiftGlobals}
    (h3 : g.sievePrimes3 ≤ numPrimes) {pr rowlen blocklen : Array ℕ}
    (h : SiftPrimesInvariant g (ForIn.toList [:g.sievePrimes3]).length (pr, rowlen, blocklen))
    {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:g.sievePrimes3 - g.sievePrimes2] = pref ++ cur :: suff) {a : Array UInt64}
    (ha : Recip3Invariant g pref.length a) :
    Recip3Invariant g (pref ++ [cur]).length
      (a.set! cur (((1 : UInt64) <<< 32 + (pr[g.sievePrimes2 + cur]!).toUInt64 - 1) /
        (pr[g.sievePrimes2 + cur]!).toUInt64)) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  exact ha.set! hl (by lia) (by rw [h.1.forall_lt _ (by lia)])

theorem SiftPrimesInvariant.primesWF {g : SiftGlobals} {sd : SiftData}
    (h : SiftPrimesInvariant g (ForIn.toList [:g.sievePrimes3]).length
      (sd.pr, sd.rowlen, sd.blocklen))
    (ha : SetLoopInvariant maxPrimeEven (fun _ b ↦ b = true) (ForIn.toList [:maxPrimeEven]).length
      sd.allOnes)
    (hr : Recip3Invariant g (ForIn.toList [:g.sievePrimes3 - g.sievePrimes2]).length sd.recip3) :
    sd.PrimesWF g where
  pr_eq hn := h.1.forall_lt _ hn
  rowlen_eq hn := (h.2.1.forall_lt _ hn).trans (by rw [h.1.forall_lt _ hn])
  blocklen_eq hn := (h.2.2.forall_lt _ hn).trans (by rw [h.1.forall_lt _ hn])
  allOnes_eq hx := ha.forall_lt _ hx
  recip3_eq hm := by rw [h.1.forall_lt _ (by lia)]; exact hr.forall_lt _ hm

attribute [local irreducible] SetLoopInvariant SiftPrimesInvariant in
/-- `init_sift` sets the data of the sieving primes (`JPoints.SiftData.PrimesWF`) and leaves the
other static data. -/
@[spec]
theorem initSiftPrimes_spec (g : SiftGlobals) (sd : SiftData) :
    ⦃ sd.Sized ∧ g.sievePrimes3 ≤ numPrimes ∧ ∀ n < g.sievePrimes3, g.pnn[n]! < numPrimes ⦄
    initSiftPrimes g sd
    ⦃ fun r ↦ r = { sd with
        pr := r.pr, rowlen := r.rowlen, blocklen := r.blocklen, allOnes := r.allOnes,
        recip3 := r.recip3 } ∧ r.PrimesWF g ⦄ := by
  vcgen [initSiftPrimes] invariants
  | inv1 => fun pref _ s ↦ SiftPrimesInvariant g pref.length s
  | inv2 => fun pref _ a ↦ SetLoopInvariant maxPrimeEven (fun _ b ↦ b = true) pref.length a
  | inv3 => fun pref _ a ↦ Recip3Invariant g pref.length a
  all_goals obtain ⟨hs, h3, hpnn⟩ := ‹sd.Sized ∧ _›
  all_goals with_reducible first
    | exact siftPrimesInvariant_nil g hs
    | exact setLoopInvariant_nil _ hs.size_allOnes
    | exact setLoopInvariant_nil _ hs.size_recip3
    | exact ⟨rfl, SiftPrimesInvariant.primesWF ‹_› ‹_› ‹_›⟩
    | exact SiftPrimesInvariant.recip3Invariant_set! h3 ‹_› ‹_› ‹_›
    | exact SetLoopInvariant.set! ‹_› (Nat.le_refl _) ‹_› rfl
    | exact SiftPrimesInvariant.one_le_getElem!_set! h3 hpnn ‹_› ‹_›
    | exact SiftPrimesInvariant.set! h3 ‹_› ‹_› ‹_›

/-! ### The chunks of a row -/

/-- The walk of `init_sift` for the scalar walk returns its value, by which `JPoints.SiftData.WF`
states the walks of the chunks. -/
@[spec]
theorem initSiftWalk_spec (p : ℕ) (wLow : ℤ) (range : ℕ) :
    ⦃ True ⦄ initSiftWalk p wLow range ⦃ fun r ↦ r = (initSiftWalk p wLow range).run ⦄ :=
  Std.WP.Id.triple_eq_run _

/-- The chunk `c` is the `k`-th chunk of a row of the words from `wLow` to `wHigh` as `init_sift`
sets it for the globals `g` of the sieve: the words from `wLow + k array_size` on, `array_size` of
them or up to `wHigh`, with the walks of the first-stage primes over them (`JPoints.initSiftWalk`)
and the residues of its first word modulo the sieving primes. -/
structure ChunkSpec.WF (c : ChunkSpec) (g : SiftGlobals) (wLow wHigh : ℤ) (k : ℕ) : Prop where
  /-- The first word of the chunk. -/
  wLow_eq : c.wLow = wLow + (k * g.arraySize : ℕ)
  /-- The word after the chunk. -/
  wHigh_eq : c.wHigh = min (wLow + (k * g.arraySize : ℕ) + g.arraySize) wHigh
  /-- The walks of the first-stage primes over the chunk. -/
  walk_eq {n : ℕ} (hn : n < g.sievePrimes1) :
    c.walk[n]! = (initSiftWalk (sievingPrime g.pnn n) c.wLow (c.wHigh - c.wLow).toNat).run
  /-- The residues of the first word of the chunk. -/
  res_eq {n : ℕ} (hn : n < g.sievePrimes3) : c.res[n]! = (c.wLow % sievingPrime g.pnn n).toNat

/-- The invariant of the loop of `JPoints.initSiftChunk` over the first-stage primes, for a chunk
of the words from `lo` to `hi`: the walks of the first `k` of them over the chunk. -/
abbrev ChunkWalksInvariant (g : SiftGlobals) (lo hi : ℤ) (k : ℕ) (walk : Array WalkSpec) : Prop :=
  PushLoopInvariant (fun n x ↦ x = (initSiftWalk (sievingPrime g.pnn n) lo (hi - lo).toNat).run) k
    walk

/-- The invariant of the loop of `JPoints.initSiftChunk` over the sieving primes `sd.pr`, for a
chunk from the word `lo` on: the residues of `lo` modulo the first `k` of them. -/
abbrev ChunkResiduesInvariant (sd : SiftData) (lo : ℤ) (k : ℕ) (res : Array ℕ) : Prop :=
  PushLoopInvariant (fun n x ↦ x = (lo % sd.pr[n]!).toNat) k res

theorem ChunkSpec.wf_mk {g : SiftGlobals} {sd : SiftData} (hnpr : sd.npr = g.sievePrimes3)
    (hpr : ∀ n < g.sievePrimes3, sd.pr[n]! = sievingPrime g.pnn n) {wLow wHigh hi : ℤ} {k : ℕ}
    (hhi : hi = min (wLow + (k * g.arraySize : ℕ) + g.arraySize) wHigh) {walk : Array WalkSpec}
    (hw : ChunkWalksInvariant g (wLow + (k * g.arraySize : ℕ)) hi
      (ForIn.toList [:g.sievePrimes1]).length walk) {res : Array ℕ}
    (hr : ChunkResiduesInvariant sd (wLow + (k * g.arraySize : ℕ)) (ForIn.toList [:sd.npr]).length
      res) :
    ChunkSpec.WF ⟨wLow + (k * g.arraySize : ℕ), hi, walk, res⟩ g wLow wHigh k where
  wLow_eq := rfl
  wHigh_eq := hhi
  walk_eq hn := hw.forall_lt _ hn
  res_eq hn := by rw [← hpr _ hn]; exact hr.forall_lt _ (hnpr ▸ hn)

attribute [local irreducible] PushLoopInvariant in
/-- `init_sift` sets the `k`-th chunk of a row of the words from `wLow` to `wHigh`
(`JPoints.ChunkSpec.WF`), from static data that hold the sieving primes of the globals `g`. -/
@[spec]
theorem initSiftChunk_spec (g : SiftGlobals) (sd : SiftData) (wLow wHigh : ℤ) (k : ℕ) :
    ⦃ sd.npr = g.sievePrimes3 ∧ ∀ n < g.sievePrimes3, sd.pr[n]! = sievingPrime g.pnn n ⦄
    initSiftChunk g sd wLow wHigh k
    ⦃ fun c ↦ c.WF g wLow wHigh k ⦄ := by
  vcgen [initSiftChunk] invariants
  | inv1 => fun pref _ w ↦
      ChunkWalksInvariant g (wLow + (k * g.arraySize : ℕ)) wHigh pref.length w
  | inv2 => fun pref _ r ↦ ChunkResiduesInvariant sd (wLow + (k * g.arraySize : ℕ)) pref.length r
  | inv3 => fun pref _ w ↦ ChunkWalksInvariant g (wLow + (k * g.arraySize : ℕ))
      (wLow + (k * g.arraySize : ℕ) + g.arraySize) pref.length w
  | inv4 => fun pref _ r ↦ ChunkResiduesInvariant sd (wLow + (k * g.arraySize : ℕ)) pref.length r
  all_goals obtain ⟨hnpr, hpr⟩ := ‹sd.npr = _ ∧ _›
  all_goals with_reducible first
    | exact pushLoopInvariant_nil _
    | exact PushLoopInvariant.push ‹_› ‹_› ‹_›
    | exact PushLoopInvariant.push ‹_› ‹_› (congrArg Int.toNat (Int.tmod_add_natCast_eq_emod ‹_›))
    | exact PushLoopInvariant.push ‹_› ‹_› (congrArg Int.toNat (Int.tmod_natCast_eq_emod ‹_›))
    | exact ChunkSpec.wf_mk hnpr hpr (Int.min_eq_right (Int.le_of_lt ‹_›)).symm ‹_› ‹_›
    | exact ChunkSpec.wf_mk hnpr hpr (Int.min_eq_left (Int.not_lt.mp ‹_›)).symm ‹_› ‹_›

/-! ### The residues of the positions and the reciprocals -/

/-- The residues of the positions in a chunk and the reciprocals of the sieving primes in the static
data `sd` of the sieve as `init_sift` sets them for the globals `g` of the sieve, the fields of
`JPoints.SiftData.WF` that `JPoints.initSiftResidues` writes. -/
structure SiftData.ResiduesWF (sd : SiftData) (g : SiftGlobals) : Prop where
  /-- The residues of the positions in a chunk. -/
  res0_eq {k n : ℕ} (hk : k ≤ g.arraySize) (hn : n < sd.npr) :
    sd.res0[k * sd.npr + n]! = k % sd.pr[n]!
  /-- The reciprocals of the sieving primes as doubles. -/
  invp_eq {n : ℕ} (hn : n < sd.npr) : sd.invp[n]! = 1.0 / Double.ofInt sd.pr[n]!

/-- The invariant of the loop of `JPoints.initSiftResidues` over the positions `j` in a chunk for
the `n`-th sieving prime: the table `res0` of `(array_size + 1) npr` entries holds the residues of
all the positions for the sieving primes before the `n`-th, and those of the first `i` positions
for the `n`-th. -/
def ResiduesInvariant (g : SiftGlobals) (sd : SiftData) (n i : ℕ) (res0 : Array ℕ) : Prop :=
  res0.size = (g.arraySize + 1) * sd.npr ∧
    (∀ n' < n, ∀ j ≤ g.arraySize, res0[j * sd.npr + n']! = j % sd.pr[n']!) ∧
    ∀ j < i, res0[j * sd.npr + n]! = j % sd.pr[n]!

/-- The invariant of the loop of `JPoints.initSiftResidues` over the sieving primes: the table
`res0` of `s = (res0, invp)` holds the residues of the positions for the first `n` sieving primes
(`JPoints.ResiduesInvariant`), and `invp` their reciprocals. -/
def ResiduesLoopInvariant (g : SiftGlobals) (sd : SiftData) (n : ℕ) (s : Array ℕ × Array Double) :
    Prop :=
  ResiduesInvariant g sd n 0 s.1 ∧
    SetLoopInvariant sd.invp.size (fun n' x ↦ x = 1.0 / Double.ofInt sd.pr[n']!) n s.2

theorem residuesLoopInvariant_nil (g : SiftGlobals) (sd : SiftData) :
    ResiduesLoopInvariant g sd ([] : List ℕ).length
      (Array.replicate ((g.arraySize + 1) * sd.npr) 0, sd.invp) :=
  ⟨⟨Array.size_replicate .., fun _ h ↦ absurd h (Nat.not_lt_zero _),
    fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩, setLoopInvariant_nil _ rfl⟩

theorem ResiduesLoopInvariant.residuesInvariant {g : SiftGlobals} {sd : SiftData}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sd.npr] = pref ++ cur :: suff)
    {res0 : Array ℕ} {invp : Array Double}
    (h : ResiduesLoopInvariant g sd pref.length (res0, invp)) :
    ResiduesInvariant g sd cur ([] : List ℕ).length res0 :=
  Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl ▸ h.1

theorem ResiduesInvariant.set! {g : SiftGlobals} {sd : SiftData} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:sd.npr] = pref ++ cur :: suff) {pref' suff' : List ℕ} {j : ℕ}
    (hl' : ForIn.toList [:g.arraySize + 1] = pref' ++ j :: suff') {res0 : Array ℕ}
    (h : ResiduesInvariant g sd cur pref'.length res0) :
    ResiduesInvariant g sd cur (pref' ++ [j]).length
      (res0.set! (j * sd.npr + cur) (j % sd.pr[cur]!)) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hj := Std.Legacy.Range.lt_of_toList_eq_append_cons hl'
  have hj' := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl'
  refine ⟨by rw [Array.size_set!, h.1], fun n' hn' i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ fun he ↦ by
      lia [(Nat.eq_and_eq_of_mul_add_eq_mul_add hc (by lia) he).2]]
    exact h.2.1 n' hn' i hi
  · rw [List.length_append, List.length_singleton] at hi
    rcases (show i < j ∨ i = j by lia) with hi | rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ fun he ↦ by
        lia [(Nat.eq_and_eq_of_mul_add_eq_mul_add hc hc he).1]]
      exact h.2.2 i (by lia)
    · exact Array.getElem!_set!_self _ _ _ (h.1 ▸ Nat.mul_add_lt_mul_of_lt hj le_rfl hc)

theorem ResiduesLoopInvariant.set! {g : SiftGlobals} {sd : SiftData}
    (hpre : sd.npr ≤ sd.invp.size) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:sd.npr] = pref ++ cur :: suff) {res0 res0' : Array ℕ}
    {invp : Array Double} (h : ResiduesLoopInvariant g sd pref.length (res0, invp))
    (h' : ResiduesInvariant g sd cur (ForIn.toList [:g.arraySize + 1]).length res0') :
    ResiduesLoopInvariant g sd (pref ++ [cur]).length
      (res0', invp.set! cur (1.0 / Double.ofInt sd.pr[cur]!)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList_zero_start] at h'
  refine ⟨⟨h'.1, fun n' hn' i hi ↦ ?_, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩,
    h.2.set! hl hpre rfl⟩
  rw [List.length_append, List.length_singleton] at hn'
  rcases (show n' < cur ∨ n' = cur by lia) with hn' | rfl
  · exact h'.2.1 n' hn' i hi
  · exact h'.2.2 i (by lia)

theorem ResiduesLoopInvariant.residuesWF {g : SiftGlobals} {sd : SiftData} {res0 : Array ℕ}
    {invp : Array Double}
    (h : ResiduesLoopInvariant g sd (ForIn.toList [:sd.npr]).length (res0, invp)) :
    { sd with res0, invp }.ResiduesWF g where
  res0_eq hk hn := h.1.2.1 _ (by rwa [Std.Legacy.Range.length_toList_zero_start]) _ hk
  invp_eq hn := h.2.forall_lt _ hn

attribute [local irreducible] ResiduesInvariant ResiduesLoopInvariant in
/-- `init_sift` sets the residues of the positions in a chunk and the reciprocals of the sieving
primes (`JPoints.SiftData.ResiduesWF`) and leaves the other static data. -/
@[spec]
theorem initSiftResidues_spec (g : SiftGlobals) (sd : SiftData) :
    ⦃ sd.npr ≤ sd.invp.size ⦄
    initSiftResidues g sd
    ⦃ fun r ↦ r = { sd with res0 := r.res0, invp := r.invp } ∧ r.ResiduesWF g ⦄ := by
  vcgen [initSiftResidues] invariants
  | inv1 => fun pref _ s ↦ ResiduesLoopInvariant g sd pref.length s
  | inv2 cur _ _ _ _ _ => fun pref _ r ↦ ResiduesInvariant g sd cur pref.length r
  all_goals with_reducible first
    | exact residuesLoopInvariant_nil g sd
    | exact ⟨rfl, ResiduesLoopInvariant.residuesWF ‹_›⟩
    | exact ResiduesLoopInvariant.residuesInvariant ‹_› ‹_›
    | exact ResiduesInvariant.set! ‹_› ‹_› ‹_›
    | exact ResiduesLoopInvariant.set! ‹_› ‹_› ‹_› ‹_›

/-! ### The static data -/

/-- The static data `sd` of the sieve are those of `init_sift` for the globals `g` of the sieve when
they hold the data of the sieving primes (`JPoints.SiftData.PrimesWF`), the residues of the
positions and the reciprocals (`JPoints.SiftData.ResiduesWF`), the words and the chunks of a row
(`JPoints.ChunkSpec.WF`) and the bound on the fourth coordinate. -/
theorem SiftData.PrimesWF.wf {g : SiftGlobals} {sd : SiftData} (hp : sd.PrimesWF g)
    (hq : sd.ResiduesWF g) (hnpr : sd.npr = g.sievePrimes3)
    (hlow : sd.wLowAll = (-g.check.height) >>> longShift)
    (hhigh : sd.wHighAll = (g.check.height >>> longShift) + 1)
    (hnum : sd.numChunks = (ceilDiv (sd.wHighAll - sd.wLowAll) g.arraySize).toNat)
    (hsize : sd.chunks.size = sd.numChunks)
    (hc : ∀ k < sd.numChunks, (sd.chunks[k]!).WF g sd.wLowAll sd.wHighAll k)
    (hth : sd.th = Double.ofInt g.check.dbound) (hth2 : sd.th2 = sd.th * sd.th) : sd.WF g where
  npr_eq := hnpr
  pr_eq := hp.pr_eq
  rowlen_eq := hp.rowlen_eq
  blocklen_eq := hp.blocklen_eq
  res0_eq hk hn := hq.res0_eq hk (hnpr ▸ hn)
  allOnes_eq := hp.allOnes_eq
  recip3_eq := hp.recip3_eq
  wLowAll_eq := hlow
  wHighAll_eq := hhigh
  numChunks_eq := hnum
  size_chunks := hsize
  wLow_chunk hk := (hc _ hk).wLow_eq
  wHigh_chunk hk := (hc _ hk).wHigh_eq
  walk_chunk hk _ hn := (hc _ hk).walk_eq hn
  res_chunk hk _ hn := by rw [hp.pr_eq hn]; exact (hc _ hk).res_eq hn
  th_eq := hth
  th2_eq := hth2
  invp_eq hn := hq.invp_eq (hnpr ▸ hn)

end JPoints

end
