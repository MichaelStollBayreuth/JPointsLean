/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Filters
public import JPoints.Proof.Globals
public import JPoints.Proof.TubeBands
public import Mathlib.Data.Nat.Prime.Defs

import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Order
import JPoints.Proof.Quintic
import JPoints.Proof.RealRegion
import JPoints.Proof.Reduction
import JPoints.Proof.Region
import JPoints.Proof.RowRegion
import JPoints.Proof.Search
import JPoints.Proof.TubeCover

/-!
# The soundness of the tests of the main search

Each test by which the main search drops triples keeps every triple over which a point lies, for
the globals and the static data of the sieve that `find_points` sets up (`JPoints.IsSieveSetup`):
the units of work, the squares of a monic quintic (`JPoints.unitKeeps_of_hasPointOver`); the rows,
by the step of `row_step` and the condition at 2 (`JPoints.rowKeeps_of_hasPointOver`); the third
coordinates of a row, by the tables of the three stages (`JPoints.stage1Keeps_of_hasPointOver`,
`JPoints.stage2Keeps_of_hasPointOver`, `JPoints.stage3Keeps_of_hasPointOver`), the mask of the row
(`JPoints.maskKeeps_of_hasPointOver`), the row itself (`JPoints.rangeKeeps_eq`) and coprimality
(`JPoints.colKeeps_of_hasPointOver`); and the analysis of the bands of the tube and of the real
region (`JPoints.bandKeeps_of_points_ne_nil`), by mode: the analysis of the tube
(`JPoints.exists_mem_rowRanges_siftBandsBand_of_points_ne_nil`), the real region of a row
(`JPoints.exists_mem_rangeList_rowRegion_of_points_ne_nil`), and the cut of the tube to the real
region, which keeps the words of both (`JPoints.exists_mem_cutRanges`).

## Main statements

* `JPoints.unitKeeps_of_hasPointOver`, `JPoints.rowKeeps_of_hasPointOver`,
  `JPoints.colKeeps_of_hasPointOver`, `JPoints.bandKeeps_of_points_ne_nil`: the tests keep the
  triples with points.
* `JPoints.aliveKeeps_of_hasPointOver`: the part of the test of the rows of the condition at 2.
* `JPoints.stage1Keeps_of_hasPointOver`, `JPoints.stage2Keeps_of_hasPointOver`,
  `JPoints.stage3Keeps_of_hasPointOver`, `JPoints.maskKeeps_of_hasPointOver`,
  `JPoints.rangeKeeps_eq`: the parts of the test of the third coordinates.
* `JPoints.refAdmits12_of_hasPointOver`: a point reduces to a class that the references of the
  tables admit, at every odd prime.
* `JPoints.CurveTables.admits12_of_hasPointOver`, `JPoints.CurveTables.admits3_of_hasPointOver`:
  the class tests keep the classes of the points at every sieving prime.
* `JPoints.exists_mem_rowRanges_siftBandsBand_of_points_ne_nil`,
  `JPoints.exists_mem_rangeList_rowRegion_of_points_ne_nil`: the parts of the test of the bands,
  the tube and the real region.
* `JPoints.IsSieveSetup.sound_neg`, `JPoints.IsSieveSetup.dbounded_of_sieveMode_eq_one`: what the
  tube and the real region read of the set-up.

## Implementation notes

The tests that do not depend on the bounds of the search are stated for a point of the Kummer
surface that lifts (`JPoints.HasPointOver`), the others for the points of the search
(`JPoints.CheckGlobals.points`). The tests of the stages and the step of the rows are those of the
references of the tables (`JPoints.refAdmits12_of_hasPointOver`, from the reduction of the points
modulo the odd primes of `JPoints.Proof.Reduction`); the squares of a monic quintic are those of
`JPoints.Proof.Quintic`.
-/

@[expose] public section

namespace JPoints

/-- The test of the units of work keeps the first coordinate `a` of a coprime triple over which a
point lies: for a monic quintic `a` is a square (`JPoints.isSquare_of_mem_kummerPoints`). -/
theorem unitKeeps_of_hasPointOver {gl : CheckGlobals} (hgl : gl.WF) {a : ℕ} {b c : ℤ}
    (habc : gcd (a : ℤ) (gcd b c) = 1) (h : HasPointOver gl.coeffList (a, b, c)) :
    unitKeeps gl.curve a = true := by
  rw [unitKeeps]
  by_cases hq : (gl.curve.degree == 5 && gl.curve.coeffs[5]! == 1) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨P, hP, hL⟩ := h
    have h5 : gl.coeffList.getD 5 0 = 1 := (Array.getD_toList_eq_getElem! _ 5).trans hq.2
    simpa [hq] using Int.isSquare_natCast_iff.mp (isSquare_of_mem_kummerPoints (h5 ▸ isUnit_one)
      (getD_eq_zero_of_degree_lt (by lia [hgl.degree_coeffList])) (by positivity) habc hP hL)
  · simp [hq]

/-- A point reduces to an admitted class at every odd prime: for a triple `(a, b, c)` over which a
point of the Kummer surface lies that comes from a rational point of the Jacobian, for every curve
of degree 5 or 6, squarefree or not (`JPoints.refAdmits12_of_mem_kummerPoints`). For `p ∤ a` the
remainder of `f` modulo `X² - (b / a) X + c / a` is that of the square of the polynomial `v` of the
Mumford representation, so that the test of `point_on_j` passes; for `p ∣ a` and `p ∤ b`,
`A₂ ≡ f₆ b⁴` gives the points at infinity, and the square `A₂` of the reversed point gives the
square `f(c / b)`; in the kernel of the reduction the triple lies on the conic `b² ≡ 4ac`. -/
theorem refAdmits12_of_hasPointOver {cs : List ℤ} (h7 : cs.length = 7) {deg : ℕ}
    (hdeg : degree cs = deg) (h5 : 5 ≤ deg) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b c : ℤ}
    (h : HasPointOver cs (a, b, c)) : refAdmits12 cs deg p a b c = true := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hL⟩ := h
  exact refAdmits12_of_mem_kummerPoints hp2 h7.le hdeg h5 hP hL

private theorem refAdmits12_of_isSieveSetup {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c))
    {n : ℕ} (hn : n < bg.sift.sievePrimes3) :
    refAdmits12 bg.sift.check.coeffList bg.sift.check.curve.degree (sievingPrime bg.sift.pnn n)
      a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  have hpn : bg.sift.pnn[n]! < numPrimes := by lia [hs.pnn_lt hn, hg.input.numPrimes_le]
  rw [hs.check_eq] at hp ⊢
  refine refAdmits12_of_hasPointOver (by simpa using hg.check.size_coeffs)
    hg.check.degree_coeffList hg.check.five_le_degree (prime_getElem!_primeTable hpn) ?_ hp
  lia [three_le_getElem!_primeTable hpn]

/-- The class test of the sieve tables of the first two stages keeps the class of a triple over
which a point lies, at every sieving prime: the tables of the curve are the references
(`JPoints.CurveTables.WF.admits12_eq`), which admit the class
(`JPoints.refAdmits12_of_hasPointOver`). -/
theorem CurveTables.admits12_of_hasPointOver {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c))
    {n : ℕ} (hn : n < bg.sift.sievePrimes3) :
    bg.sift.curve.admits12 bg.sift.pnn[n]! a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  rw [hs.curveTables.admits12_eq (by lia [hg.input.numPrimes_le]) hn (hs.pnn_lt hn), ← hs.check_eq]
  exact refAdmits12_of_isSieveSetup ⟨g, hg, hs⟩ hp hn

/-- The class test of the third stage keeps the class of a triple over which a point lies, at every
sieving prime, as that of the first two stages
(`JPoints.CurveTables.admits12_of_hasPointOver`) does. -/
theorem CurveTables.admits3_of_hasPointOver {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c))
    {n : ℕ} (hn : n < bg.sift.sievePrimes3) :
    bg.sift.curve.admits3 bg.sift.pnn[n]! a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  rw [hs.curveTables.admits3_eq (by lia [hg.input.numPrimes_le]) hn (hs.pnn_lt hn), ← hs.check_eq]
  exact refAdmits3_of_refAdmits12 (refAdmits12_of_isSieveSetup ⟨g, hg, hs⟩ hp hn)

theorem stage1Keeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) :
    stage1Keeps bg.sift a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  simp only [stage1Keeps, List.all_eq_true, List.mem_range]
  exact fun n hn ↦ CurveTables.admits12_of_hasPointOver ⟨g, hg, hs⟩ hp
    (by lia [hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3])

theorem stage2Keeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) :
    stage2Keeps bg.sift a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  simp only [stage2Keeps, List.all_eq_true, List.mem_range']
  exact fun n ⟨i, hi, hn⟩ ↦ CurveTables.admits12_of_hasPointOver ⟨g, hg, hs⟩ hp
    (by lia [hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3])

theorem stage3Keeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) :
    stage3Keeps bg.sift a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  simp only [stage3Keeps, List.all_eq_true, List.mem_range']
  exact fun n ⟨i, hi, hn⟩ ↦ CurveTables.admits3_of_hasPointOver ⟨g, hg, hs⟩ hp
    (by lia [hs.sievePrimes1_le_sievePrimes2, hs.sievePrimes2_le_sievePrimes3])

/-- The condition at 2 leaves the row of a coprime triple over which a point lies
(`JPoints.TwoAdic.Sound`). -/
theorem aliveKeeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (habc : gcd a (gcd b c) = 1)
    (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) : aliveKeeps bg.sift a b = true := by
  obtain ⟨g, hg, hs⟩ := h
  by_cases h2 : bg.sift.twoAdic.use2 = true
  · by_cases ha : a = 0
    · simp [aliveKeeps, ha]
    · simp [aliveKeeps, hs.twoAdic.alive2 h2 ha habc (hs.check_eq ▸ hp)]
  · simp [aliveKeeps, h2]

/- A prime of the step of the rows of `a` divides the second coordinate of a triple over which a
point lies: it divides `a`, and the curve has no points at infinity modulo it, so that the class
test of the first two stages admits the class only for `p ∣ b`. -/
private theorem dvd_of_mem_rowStepPrimes {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c))
    {q : ℕ} (hq : q ∈ rowStepPrimes bg.sift a) : (q : ℤ) ∣ b := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq
  obtain ⟨hn, hq⟩ := List.mem_filter.1 hn
  have hp3 := three_le_getElem!_primeTable (h.pnn_lt (List.mem_range.1 hn))
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hq
  have := CurveTables.admits12_of_hasPointOver h hp (List.mem_range.1 hn)
  simp only [CurveTables.admits12, Int.emod_eq_zero_of_dvd hq.2, Int.toNat_zero, ↓reduceIte, hq.1,
    Bool.false_and, Bool.or_false, beq_iff_eq] at this
  exact Int.dvd_of_emod_eq_zero
    (by lia [Int.emod_nonneg b (by lia : (sievingPrime bg.sift.pnn n : ℤ) ≠ 0)])

/- The primes of the step of the rows are distinct: the sieving primes are distinct primes of the
table, which is increasing. -/
private theorem nodup_rowStepPrimes {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    (a : ℤ) : (rowStepPrimes bg.sift a).Nodup := by
  refine List.Nodup.map_on (fun m hm n hn he ↦ ?_) (List.nodup_range.filter _)
  replace hm := List.mem_range.1 (List.mem_filter.1 hm).1
  replace hn := List.mem_range.1 (List.mem_filter.1 hn).1
  have hm' := h.pnn_lt hm
  have hn' := h.pnn_lt hn
  obtain ⟨g, hg, hs⟩ := h
  refine hs.pnn_injective hm hn ?_
  rcases lt_trichotomy bg.sift.pnn[m]! bg.sift.pnn[n]! with hlt | heq | hgt
  · exact absurd he (getElem!_primeTable_lt_getElem!_primeTable hlt hn').ne
  · exact heq
  · exact absurd he (getElem!_primeTable_lt_getElem!_primeTable hgt hm').ne'

/- The product of distinct primes that divide `n` divides `n`. -/
private theorem prod_dvd_of_nodup_of_prime {l : List ℕ} (hl : l.Nodup) (hp : ∀ q ∈ l, q.Prime)
    {n : ℕ} (hn : ∀ q ∈ l, q ∣ n) : l.prod ∣ n := by
  classical
  simpa [List.prod_toFinset _ hl] using Finset.prod_primes_dvd (s := l.toFinset) n
    (fun q hq ↦ (hp q (List.mem_toFinset.1 hq)).prime) fun q hq ↦ hn q (List.mem_toFinset.1 hq)

/- The product of the primes of the step of the rows of `a` divides the second coordinate of a
triple over which a point lies. -/
private theorem prod_rowStepPrimes_dvd {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {a b c : ℤ} (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) :
    ((rowStepPrimes bg.sift a).prod : ℤ) ∣ b := by
  refine Int.natCast_dvd.2 <| prod_dvd_of_nodup_of_prime (nodup_rowStepPrimes h a) (fun q hq ↦ ?_)
    fun q hq ↦ Int.natCast_dvd.1 (dvd_of_mem_rowStepPrimes h hp hq)
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hq
  exact prime_getElem!_primeTable (h.pnn_lt (List.mem_range.1 (List.mem_filter.1 hn).1))

/-- The rows of a point are those that the main search sieves: for a sieving prime `p ∣ a` modulo
which the curve has no points at infinity, `p ∣ b`, since the class test of the first two stages
admits the class of the triple (`JPoints.CurveTables.admits12_of_hasPointOver`), so that the step
of `row_step`, the product of these primes (`JPoints.run_rowStep`), divides `b`, or exceeds the
height bound and `b = 0`; and the class of `(a, b)` modulo `64` is alive under the condition at 2
(`JPoints.aliveKeeps_of_hasPointOver`). -/
theorem rowKeeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (hb : |b| ≤ bg.sift.check.height) (habc : gcd a (gcd b c) = 1)
    (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) : rowKeeps bg.sift a b = true := by
  simp only [rowKeeps, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, aliveKeeps_of_hasPointOver h habc hp⟩
  have hdvd := prod_rowStepPrimes_dvd h hp
  rw [run_rowStep h.check.one_le_height fun n hn ↦ h.pnn_lt hn]
  split_ifs with hle
  · exact hdvd
  obtain rfl : b = 0 := by
    by_contra hb0
    exact hle ((Int.le_of_dvd (abs_pos.2 hb0) ((dvd_abs _ _).2 hdvd)).trans hb)
  exact dvd_zero _

/-- The mask of the row of a point has the bit of its third coordinate: the word of the condition at
2 by `JPoints.TwoAdic.Sound`, and for even `a` and `b` the odd bits, as the third coordinate of a
coprime triple is then odd. -/
theorem maskKeeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (habc : gcd a (gcd b c) = 1)
    (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) : maskKeeps bg.sift a b c = true := by
  obtain ⟨g, hg, hs⟩ := h
  simp only [maskKeeps, siftMask]
  split_ifs with h2 hab
  · simp only [Bool.and_eq_true, bne_iff_ne] at h2
    exact hs.twoAdic.mask2 h2.1 h2.2 habc (hs.check_eq ▸ hp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hab
    have hc : ¬(2 : ℤ) ∣ c := fun hc ↦ by
      have h2 : (2 : ℤ) ∣ gcd a (gcd b c) := dvd_gcd (by lia) (dvd_gcd (by lia) hc)
      rw [habc] at h2
      exact absurd h2 (by decide)
    rw [getLsbD_halfMask (by lia), decide_eq_true_iff]
    lia
  · rw [UInt64.getLsbD_allOnes, decide_eq_true_iff]
    lia

/-- The third coordinates of a row are those of absolute value at most the height bound: the words
from `⌊-H / 64⌋` below `⌊H / 64⌋ + 1`, and of the first and the last word the bits of `begmask` and
`endmask`. -/
theorem rangeKeeps_eq {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) (c : ℤ) :
    rangeKeeps bg.sift sd c = decide (|c| ≤ bg.sift.check.height) := by
  obtain ⟨g, hg, hs⟩ := h
  refine rangeKeeps_eq_decide_abs_le hs.siftData.wLowAll_eq hs.siftData.wHighAll_eq ?_ ?_ c
  · rw [hs.begmask_eq, hg.begmask_eq, hs.check_eq]
  · rw [hs.endmask_eq, hg.endmask_eq, hs.check_eq]

/-- The word `⌊c / 64⌋` of a third coordinate `c` of absolute value at most the height bound lies
among the words of a row, from `JPoints.SiftData.wLowAll` below `JPoints.SiftData.wHighAll`. -/
theorem IsSieveSetup.wLowAll_le_and_lt_wHighAll {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) {c : ℤ} (hc : |c| ≤ bg.sift.check.height) :
    sd.wLowAll ≤ c >>> longShift ∧ c >>> longShift < sd.wHighAll := by
  obtain ⟨g, -, hs⟩ := h
  simp only [hs.siftData.wLowAll_eq, hs.siftData.wHighAll_eq, longShift,
    Int.shiftRight_eq_div_pow]
  have := abs_le.mp hc
  constructor <;> lia

/-- The sieve of a row hands every triple of the search with a point over it to the exact check:
each part of the test keeps it. -/
theorem colKeeps_of_hasPointOver {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c : ℤ} (ht : (a, b, c) ∈ boxTriples bg.sift.check.H)
    (hp : HasPointOver bg.sift.check.coeffList (a, b, c)) : colKeeps bg.sift sd a b c = true := by
  obtain ⟨habc, -, -, -, hc⟩ := mem_boxTriples_iff.mp ht
  have hc' : |c| ≤ bg.sift.check.height := by
    obtain ⟨g, hg, hs⟩ := h
    lia [hs.check_eq ▸ hg.check.one_le_height]
  simp [colKeeps, stage1Keeps_of_hasPointOver h hp, stage2Keeps_of_hasPointOver h hp,
    stage3Keeps_of_hasPointOver h hp, maskKeeps_of_hasPointOver h habc hp, rangeKeeps_eq h,
    coprimeKeeps, habc, hc']

/-- The intervals of `real_roots_init` on which `f` is negative are sound when the search sieves
in the tube or in the real region: the sieve then has primes, so that `-N 0` is not given. -/
theorem IsSieveSetup.sound_neg {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    (hmode : bg.sieveMode ≠ 0) : bg.neg.Sound bg.sift.check.coeffList := by
  obtain ⟨g, hg, hs⟩ := h
  rcases hg.neg with h0 | hn
  · exact absurd (hs.sieveMode_eq_zero_of_sievePrimes3_eq_zero (hs.sievePrimes3_eq_zero h0)) hmode
  · rwa [hs.neg_eq, hs.check_eq]

theorem IsSieveSetup.dbounded_of_sieveMode_eq_one {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) (hmode : bg.sieveMode = 1) : bg.sift.check.dbounded = true := by
  obtain ⟨g, -, hs⟩ := h
  rw [hs.check_eq]
  exact hs.dbounded_of_sieveMode_eq_one hmode

-- The facts about a band `bLo..bHi` of the box and a triple `(a, b, c)` of the box with `b` in the
-- band that the analysis of the tube reads: the bounds of the box, the initial state of the
-- analysis with its bands set up for the band, the cell of the band and of all the words, and the
-- word of `c` among them.
private theorem IsSieveSetup.band_facts {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a b c bLo bHi : ℤ} (hbL : -bg.sift.check.height ≤ bLo) (hb : bLo ≤ b) (hbH : b ≤ bHi)
    (hHH : bHi ≤ bg.sift.check.height) (hn : bHi - bLo + 1 ≤ tubeBand)
    (ht : (a, b, c) ∈ boxTriples bg.sift.check.H) :
    1 ≤ bg.sift.check.height ∧ |a| ≤ bg.sift.check.height ∧ |c| ≤ bg.sift.check.height ∧
      (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run.WF ∧
      (resetBands (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run.bands bLo
        bHi).Sized (bHi - bLo + 1).toNat ∧
      (∀ r < (bHi - bLo + 1).toNat, (resetBands (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2
        .initial a).run.bands bLo bHi).rowRanges r = []) ∧
      TubeCell bg.sift.check.height bLo bHi sd.wLowAll sd.wHighAll ∧
      (sd.wLowAll ≤ c >>> longShift ∧ c >>> longShift < sd.wHighAll) := by
  have hH := h.check.one_le_height
  obtain ⟨-, -, haH, -, hcH⟩ := mem_boxTriples_iff.mp ht
  rw [CheckGlobals.H, Int.toNat_of_nonneg (by lia)] at haH hcH
  have hT := wf_run_tubeAInit_initial bg.kd bg.sift.check.height sd.th sd.th2 a
  have hw := h.wLowAll_le_and_lt_wHighAll hcH
  obtain ⟨g, -, hs⟩ := h
  have e1 := hs.siftData.wLowAll_eq
  have e2 := hs.siftData.wHighAll_eq
  have := abs_le.mp hcH
  obtain ⟨r1, r2⟩ := resetBands_sized hT.size_bandNr hT.size_bandRg (bLo := bLo) (bHi := bHi)
    (by lia)
  refine ⟨hH, haH, hcH, hT, r1, r2, ⟨hbL, by lia, hHH, e1.ge, ?_, e2.le⟩, hw⟩
  rw [e1, e2]; simp only [Int.shiftRight_eq_div_pow, longShift]; lia

/-- The analysis of the tube keeps the third coordinates of the points over the triples of the box
when the fourth coordinate is bounded: for the polynomials of the first coordinate `a`
(`JPoints.tubeAInit`) and a band of at most `TUBE_BAND` rows `bLo ≤ b ≤ bHi` of the box analysed
from them (`JPoints.siftBandsBand`), the word `⌊c / 64⌋` of `c` lies in one of the ranges that the
analysis collects in the row of `b` (`JPoints.TubeBands.rowRanges`): the Kummer quadratic of
`(a, b, c)` has the root `d` of the point, with `|d| ≤ W` (`JPoints.TubeRoot`), which the tests of
`tube_cell` on the cells that hold `(b, c)` do not rule out
(`JPoints.TubeSetup.cellCovers_run_tubeCell`), and where `tube_ok` fails the band is collected
whole. -/
theorem exists_mem_rowRanges_siftBandsBand_of_points_ne_nil {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) (hd : bg.sift.check.dbounded = true) {a b c bLo bHi : ℤ}
    (hbL : -bg.sift.check.height ≤ bLo) (hb : bLo ≤ b) (hbH : b ≤ bHi)
    (hHH : bHi ≤ bg.sift.check.height) (hn : bHi - bLo + 1 ≤ tubeBand)
    (ht : (a, b, c) ∈ boxTriples bg.sift.check.H) (hp : bg.sift.check.points (a, b, c) ≠ []) :
    ∃ r ∈ (siftBandsBand sd (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run
        bLo bHi true).run.bands.rowRanges (b - bLo).toNat,
      r.1 ≤ c >>> longShift ∧ c >>> longShift < r.2 := by
  obtain ⟨hhH, haH, hcH, hT, r1, r2, hcell, hw⟩ := h.band_facts hbL hb hbH hHH hn ht
  have hr (r : ℕ) (hr : r < (bHi - bLo + 1).toNat) (_ : bLo ≤ bLo + r) (_ : bLo + r ≤ bHi) :
      RangesIn sd.wLowAll sd.wLowAll ((resetBands (tubeAInit bg.kd bg.sift.check.height sd.th
        sd.th2 .initial a).run.bands bLo bHi).rowRanges r) := by
    rw [r2 r hr]; exact rangesIn_nil _ _
  rw [run_siftBandsBand, ite_eq_left rfl]
  by_cases hok : (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run.tubeOk = true
  · exact ((h.tubeSetup hd haH hok).cellCovers_run_tubeCell
      { (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run with
        bands := resetBands (tubeAInit bg.kd bg.sift.check.height sd.th sd.th2 .initial a).run.bands
          bLo bHi } bLo bHi _ _ (hT.with_bands r1.size_bandNr r1.size_bandRg)
      (eqPolys_of_eq_with rfl) hcell r1 le_rfl (by simp only [resetBands]; lia) le_rfl hr).2
        b c hb hbH hw.1 hw.2 (h.check.tubeRoot_of_points_ne_nil hd hp)
  · rw [run_tubeCell_of_tubeOk_eq_false (by simpa using hok)]
    exact (r1.covers_emitRows le_rfl (by simp only [resetBands]; lia) hcell.lt hr).2 _
      (by lia) (by simp only [resetBands]; lia) (by simp only [resetBands]; lia) _ hw.1 hw.2

/-- The real region of a row keeps the third coordinates of the points over the triples of the box
off the conic, for intervals on which `f` is negative (`JPoints.NegativeIntervals.Sound`) and a
height bound of at most `2 ^ 26`: the word `⌊c / 64⌋` of `c` lies in one of the ranges of words of
the real region of the row `(a, b)` (`JPoints.rowRegion`). A real root `t` of `a t² - b t + c` is
the first coordinate of a real point of the curve, where `f` takes the value of a square, so that
it lies outside the intervals, whose images under `t ↦ b t - a t²` `row_region` takes out of the
row (`JPoints.NegativeIntervals.Sound.not_regionExcludes_of_hasPointOver`). The bound keeps the
products of `row_region` below `2 ^ 53`, where the rounding of the ends of its excluded intervals
stays within their margins; at larger heights `j-points` can miss points in the real region. -/
theorem exists_mem_rangeList_rowRegion_of_points_ne_nil {bg : BandGlobals} {sd : SiftData}
    (h : IsSieveSetup bg sd) (hH : bg.sift.check.height ≤ 2 ^ 26)
    (hneg : bg.neg.Sound bg.sift.check.coeffList) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples bg.sift.check.H) (hc : b ^ 2 ≠ 4 * a * c)
    (hp : bg.sift.check.points (a, b, c) ≠ []) :
    ∃ r ∈ rangeList (rowRegion bg.neg sd a b).run,
      r.1 ≤ c >>> longShift ∧ c >>> longShift < r.2 := by
  obtain ⟨-, hn, ha, hb, hc'⟩ := mem_boxTriples_iff.mp ht
  have h1 := h.check.one_le_height
  have hH0 : (bg.sift.check.H : ℤ) = bg.sift.check.height := Int.toNat_of_nonneg (by lia)
  rw [hH0] at ha hb hc'
  have h7 : bg.sift.check.coeffList.length ≤ 7 := by simp [h.check.size_coeffs]
  have hb0 : a = 0 → 0 < b := fun ha0 ↦ by
    rcases hn with hn | ⟨-, hn | ⟨rfl, -⟩⟩ <;> simp_all
  have hv := h.wLowAll_le_and_lt_wHighAll hc'
  refine (exists_mem_rangeList_rowRegion_or (by lia [h.isRowSetup.one_le_wHighAll_sub_wLowAll])
    a b hv.1 hv.2).resolve_right fun ⟨i, hi, lo, hi', hI, hx⟩ ↦ ?_
  exact hneg.not_regionExcludes_of_hasPointOver h7 h.squarefree
    (hn.elim le_of_lt fun h ↦ h.1.ge) (((le_abs_self a).trans ha).trans hH) (hb.trans hH)
    (hc'.trans hH) hb0 (hasPointOver_of_pointsOver_ne_nil hp) hi hI hx

/-- The analysis of the band of a row keeps the third coordinates of the points over the triples of
the row off the conic, for the rows from `bFirst` on by the step `m`: in the box every one; in the
tube without the cut by the analysis of the tube
(`JPoints.exists_mem_rowRanges_siftBandsBand_of_points_ne_nil`), where the fourth coordinate is
bounded; in the real region by the real region of the row
(`JPoints.exists_mem_rangeList_rowRegion_of_points_ne_nil`), whose intervals are sound there
(`JPoints.IsSieveSetup.sound_neg`); in the tube with the cut by both, as the cut keeps the words
of both (`JPoints.exists_mem_cutRanges`). -/
theorem bandKeeps_of_points_ne_nil {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {a bFirst m b c : ℤ} (hm : 1 ≤ m) (hbF : -bg.sift.check.height ≤ bFirst) (hb : bFirst ≤ b)
    (hmb : m ∣ b - bFirst) (ht : (a, b, c) ∈ boxTriples bg.sift.check.H) (hc : b ^ 2 ≠ 4 * a * c)
    (hp : bg.sift.check.points (a, b, c) ≠ []) : bandKeeps bg sd a bFirst m b c = true := by
  rcases Nat.eq_zero_or_pos bg.sieveMode with h0 | hpos
  · exact bandKeeps_eq_true_iff.mpr (.inl h0)
  obtain ⟨-, -, -, hbH, -⟩ := mem_boxTriples_iff.mp ht
  have hw : sd.wLowAll < sd.wHighAll := by lia [h.isRowSetup.one_le_wHighAll_sub_wLowAll]
  obtain ⟨bLo, bHi, hband⟩ : ∃ bLo bHi, bandOf bg.sift.check.height bFirst m b = (bLo, bHi) :=
    ⟨_, _, rfl⟩
  have hb1 := bandOf_fst_le (by lia) hband
  have hb2 := le_bandOf_snd (by lia) hmb (by lia [h.check.one_le_height, le_abs_self b]) hband
  rw [bandKeeps_eq_true_iff, bandRanges_eq_bandRowRanges hband]
  refine .inr (exists_mem_rangeList_bandRowRanges hw (fun h1 ↦ ?_) (fun h1 ↦ ?_) fun _ ↦
    exists_mem_rangeList_rowRegion_of_points_ne_nil h h.height_le (h.sound_neg hpos.ne') ht hc hp)
  · rw [h1]
    exact rangesIn_rowRanges_siftBandsBand hw (wf_run_tubeAInit_initial ..) hb1 hb2
      (bandOf_snd_le hband)
  · rw [h1]
    exact exists_mem_rowRanges_siftBandsBand_of_points_ne_nil h
      (h.dbounded_of_sieveMode_eq_one (beq_iff_eq.mp h1))
      (hbF.trans (le_bandOf_fst (by lia) hb hband)) hb1 hb2 (bandOf_snd_le_height hband)
      (bandOf_snd_le hband) ht hp

end JPoints

end
