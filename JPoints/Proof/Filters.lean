/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Program
public import JPoints.Model.Region
public import JPoints.Model.Search
public import JPoints.Proof.Admits
public import JPoints.Proof.Reference
public import Mathlib.Algebra.Group.Nat.Even

import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Order
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Sort

/-!
# The tests of the main search

The tests by which the main search of `j-points` drops triples, each a Boolean function of the
triple computed from what the program reads (its tables, masks and ranges), so that the contracts
of the search can say that it visits the triples that pass them, and each sound, keeping every
triple over which a point lies. The units of work (`JPoints.unitKeeps`): the squares `a` of a monic
quintic. The rows (`JPoints.rowKeeps`): the multiples of the step of the rows, and the classes
modulo `64` that the condition at 2 leaves. The third coordinates of a row (`JPoints.colKeeps`):
those that the sieving primes of the three stages admit (`JPoints.stage1Keeps`,
`JPoints.stage2Keeps`, `JPoints.stage3Keeps`), the mask of the row (`JPoints.maskKeeps`), the words
of the row and the masks of its ends (`JPoints.rangeKeeps`), and the coprime triples
(`JPoints.coprimeKeeps`), which are those of the enumeration; and in the tube and the real region,
the words of the ranges of the analysis of the band of the row (`JPoints.bandKeeps`, from
`JPoints.bandOf` and `JPoints.bandRanges`). The triples on the conic `b² = 4ac` (`JPoints.conic`)
are those of the double points, which the main search leaves out. The points that the sieve of a
row finds are those over the triples that these tests keep (`JPoints.rowPoints`,
`JPoints.bandRowPoints`), in the rows from a first one by the step of the rows (`JPoints.rowsFrom`).

## Main definitions

* `JPoints.unitKeeps`: the units of work.
* `JPoints.aliveKeeps`, `JPoints.rowKeeps`: the rows of a first coordinate.
* `JPoints.rowsFrom`: the rows from a first one by a step.
* `JPoints.stage1Keeps`, `JPoints.stage2Keeps`, `JPoints.stage3Keeps`, `JPoints.maskKeeps`,
  `JPoints.rangeKeeps`, `JPoints.coprimeKeeps`, `JPoints.colKeeps`: the third coordinates of a row.
* `JPoints.conic`: the triples on the conic.
* `JPoints.rowPoints`: the points that the sieve of a row in the box finds.
* `JPoints.bandOf`, `JPoints.bandRanges`, `JPoints.bandKeeps`: the bands of the tube and of the
  real region.
* `JPoints.bandLen`, `JPoints.bandStep`, `JPoints.bandEnd`: the length of a band, the distance
  between the first rows of two bands, and the last row of a band.
* `JPoints.bandRowPoints`, `JPoints.bandsPoints`: the points that the sieve by bands finds.

## Main statements

* `JPoints.aliveKeeps_eq_not`: the test of the rows of the condition at 2 as the program makes it.
* `JPoints.mem_rowsFrom_iff`, `JPoints.rowsFrom_eq_filter_intRange`: the rows from a first one by a
  step.
* `JPoints.filter_rowsFrom_append_rowsFrom`: the rows before a band and those of the band.
* `JPoints.rangeKeeps_eq_decide_abs_le`: the third coordinates of a row are those within the height
  bound.
* `JPoints.bandOf_eq_bandEnd`, `JPoints.bandLen_bandStep`: the band of a row, and the distance of
  the bands, a multiple of the step.
* `JPoints.bandOf_fst_le`, `JPoints.le_bandOf_snd`, `JPoints.bandOf_snd_sub_fst_add_one_le`: a row
  of the step lies in its band, of at most `TUBE_BAND` rows.

## Implementation notes

The tests read the globals and the static data of the sieve (`JPoints.SiftGlobals`,
`JPoints.BandGlobals`, `JPoints.SiftData`); the tests of the stages read the tables of the curve
through `JPoints.CurveTables.admits12` and `JPoints.CurveTables.admits3`, and the bands run the
analysis of the model itself (`JPoints.tubeAInit`, `JPoints.siftBandsBand`,
`JPoints.siftBandsRanges`) on a band from the initial state of the analysis, whose cache of
products the state of the thread reproduces. Their soundness is that of the references of the
tables (`JPoints.refAdmits12_of_hasPointOver`), of the condition at 2, of the step of the rows, of
the squares of a monic quintic, and the error analysis of the doubles of the tube and of the real
region.
-/

@[expose] public section

namespace JPoints

/-! ### The units of work and the rows -/

/-- Whether the main search takes the unit of work of the first coordinate `a`, for the curve
searched `curve`: a square `a` for a monic quintic, whose units are the squares (`JPoints.unitA`),
and every `a` otherwise. -/
def unitKeeps (curve : SearchCurve) (a : ℕ) : Bool :=
  !(curve.degree == 5 && curve.coeffs[5]! == 1) || decide (IsSquare a)

/-- Whether the condition at 2 leaves the row `(a, b)`, for the globals `g` of the sieve: when the
sieve uses it and `a ≠ 0`, the class of `(a, b)` modulo `64` alive (`alive2`), and otherwise
always. The test by which `run_a` and `sift_bands` skip rows. -/
def aliveKeeps (g : SiftGlobals) (a b : ℤ) : Bool :=
  !(g.twoAdic.use2 && a != 0) || g.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!

/-- The test of the condition at 2 is the negation of the test by which `run_a` and `sift_bands`
skip a row. -/
theorem aliveKeeps_eq_not (g : SiftGlobals) (a b : ℤ) :
    aliveKeeps g a b =
      !(g.twoAdic.use2 && a != 0 && !g.twoAdic.alive2[(a % 64).toNat * 64 + (b % 64).toNat]!) := by
  simp [aliveKeeps]

/-- Whether the main search sieves the row `(a, b)`, for the globals `g` of the sieve: its second
coordinate a multiple of the step of the rows of `a` (`JPoints.rowStep`), and the class of `(a, b)`
modulo `64` alive under the condition at 2 (`JPoints.aliveKeeps`). -/
def rowKeeps (g : SiftGlobals) (a b : ℤ) : Bool :=
  decide ((rowStep g a).run ∣ b) && aliveKeeps g a b

/-- The second coordinates `b = b₀ + k m ≤ H` of the rows from `b₀` on by the step `m`, in
increasing order, as `run_a` and `sift_bands` take them: `k < (H - b₀) / m + 1`, none when
`b₀ > H`. -/
def rowsFrom (b₀ m H : ℤ) : List ℤ :=
  (List.range ((H - b₀) / m + 1).toNat).map fun k : ℕ ↦ b₀ + k * m

theorem pairwise_lt_rowsFrom {b₀ m H : ℤ} (hm : 0 < m) :
    (rowsFrom b₀ m H).Pairwise (· < ·) :=
  List.pairwise_map.mpr <| List.pairwise_lt_range.imp fun {i j} h ↦ by
    have := Int.mul_lt_mul_of_pos_right (Int.ofNat_lt.mpr h) hm
    lia

theorem mem_rowsFrom_iff {b₀ m H x : ℤ} (hm : 0 < m) :
    x ∈ rowsFrom b₀ m H ↔ b₀ ≤ x ∧ x ≤ H ∧ m ∣ x - b₀ := by
  simp only [rowsFrom, List.mem_map, List.mem_range]
  refine ⟨fun ⟨k, hk, hx⟩ ↦ ?_, fun ⟨h1, h2, j, hj⟩ ↦ ?_⟩
  · subst hx
    have h1 : (k : ℤ) * m ≤ (H - b₀) / m * m := Int.mul_le_mul_of_nonneg_right (by lia) hm.le
    have h2 : 0 ≤ (k : ℤ) * m := Int.mul_nonneg (by lia) hm.le
    exact ⟨by lia, by lia [Int.ediv_mul_le (H - b₀) (b := m) (by lia)], ⟨k, by ring⟩⟩
  · have hj0 : 0 ≤ j := by
      by_contra! h
      lia [Int.mul_lt_mul_of_pos_left h hm]
    refine ⟨j.toNat, ?_, by lia⟩
    lia [(Int.le_ediv_iff_mul_le hm).mpr (show j * m ≤ H - b₀ by lia)]

/-- The rows from `b₀ ≥ -H` on by the step `m > 0` are the integers of `[-H, H]` from `b₀` on that
are congruent to `b₀` modulo `m`, in increasing order. -/
theorem mem_rowsFrom_of_lt {b₀ m H : ℤ} {k : ℕ} (hk : k < ((H - b₀) / m + 1).toNat) :
    b₀ + k * m ∈ rowsFrom b₀ m H :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem rowsFrom_eq_filter_intRange {b₀ m H : ℤ} (hm : 0 < m) (hb₀ : -H ≤ b₀) :
    rowsFrom b₀ m H = (intRange H.toNat).filter fun b ↦ b₀ ≤ b ∧ m ∣ b - b₀ := by
  refine (pairwise_lt_rowsFrom hm).eq_of_mem_iff ((pairwise_lt_intRange _).filter _) fun x ↦ ?_
  rw [mem_rowsFrom_iff hm, List.mem_filter, mem_intRange_iff, decide_eq_true_iff, abs_le]
  lia

/-- The rows from `b₀` on by the step `m` up to `H` before the row `x`, and those of the band from
`x` on, `x` a row of the step, of `len` rows cut at `H`, are the rows before the first row `x +
step` of the next band, when the step `step` of the bands is a multiple of `m` with
`step - m < len ≤ step`. -/
theorem filter_rowsFrom_append_rowsFrom {b₀ m H x len step : ℤ} (hm : 0 < m) (hx : b₀ ≤ x)
    (hxm : m ∣ x - b₀) (hl1 : 1 ≤ len) (hl : len ≤ step) (hl' : step - m < len) (hs : m ∣ step) :
    (rowsFrom b₀ m H).filter (· < x) ++
        rowsFrom x m (if H < x + len - 1 then H else x + len - 1) =
      (rowsFrom b₀ m H).filter (· < x + step) := by
  refine List.Pairwise.eq_of_mem_iff (List.pairwise_append.mpr ⟨(pairwise_lt_rowsFrom hm).filter _,
    pairwise_lt_rowsFrom hm, fun y hy z hz ↦ ?_⟩) ((pairwise_lt_rowsFrom hm).filter _) fun y ↦ ?_
  · rw [List.mem_filter, decide_eq_true_eq] at hy
    lia [((mem_rowsFrom_iff hm).mp hz).1]
  · simp only [List.mem_append, List.mem_filter, mem_rowsFrom_iff hm, decide_eq_true_eq]
    refine ⟨fun h ↦ ?_, fun ⟨⟨h1, h2, h3⟩, h4⟩ ↦ ?_⟩
    · rcases h with h | ⟨h1, h2, h3⟩
      · exact ⟨h.1, by lia⟩
      · refine ⟨⟨by lia, by split_ifs at h2 <;> lia, by simpa using dvd_add h3 hxm⟩, ?_⟩
        split_ifs at h2 <;> lia
    · rcases lt_or_ge y x with h | h
      · exact .inl ⟨⟨h1, h2, h3⟩, h⟩
      · obtain ⟨u, hu⟩ : m ∣ y - x := by simpa using dvd_sub h3 hxm
        obtain ⟨v, hv⟩ := hs
        have huv : u < v := lt_of_mul_lt_mul_left (by lia) hm.le
        have := Int.mul_le_mul_of_nonneg_left (show u + 1 ≤ v by lia) hm.le
        exact .inr ⟨h, by split_ifs <;> lia, u, hu⟩

theorem filter_rowsFrom_eq_nil {b₀ m H x : ℤ} (hm : 0 < m) (hx : x ≤ b₀) :
    (rowsFrom b₀ m H).filter (· < x) = [] :=
  List.filter_eq_nil_iff.mpr fun y hy ↦ by
    rw [decide_eq_true_eq]
    lia [((mem_rowsFrom_iff hm).mp hy).1]

theorem filter_rowsFrom_eq_self {b₀ m H step : ℤ} (hm : 0 < m) (hs : 0 < step) :
    (rowsFrom b₀ m H).filter (· < b₀ + ((H - b₀) / step + 1).toNat * step) = rowsFrom b₀ m H :=
  List.filter_eq_self.mpr fun y hy ↦ by
    obtain ⟨h1, h2, -⟩ := (mem_rowsFrom_iff hm).mp hy
    rw [decide_eq_true_eq]
    have := Int.lt_ediv_add_one_mul_self (H - b₀) hs
    have : 0 ≤ (H - b₀) / step := Int.ediv_nonneg (by lia) hs.le
    lia

/-! ### The third coordinates of a row -/

/-- Whether every sieving prime of the first stage (the `n`-th, `n < sieve_primes1`) admits the
class of `(a, b, c)`, for the globals `g` of the sieve, by the class test of its sieve table
(`JPoints.CurveTables.admits12`). -/
def stage1Keeps (g : SiftGlobals) (a b c : ℤ) : Bool :=
  (List.range g.sievePrimes1).all fun n ↦ g.curve.admits12 g.pnn[n]! a b c

/-- Whether every sieving prime of the second stage (the `n`-th,
`sieve_primes1 ≤ n < sieve_primes2`) admits the class of `(a, b, c)`, for the globals `g` of the
sieve, by the class test of its sieve table (`JPoints.CurveTables.admits12`). -/
def stage2Keeps (g : SiftGlobals) (a b c : ℤ) : Bool :=
  (List.range' g.sievePrimes1 (g.sievePrimes2 - g.sievePrimes1)).all fun n ↦
    g.curve.admits12 g.pnn[n]! a b c

theorem all_range_admits12_eq_stage1Keeps_and_stage2Keeps (g : SiftGlobals) (a b c : ℤ)
    (h : g.sievePrimes1 ≤ g.sievePrimes2) :
    ((List.range g.sievePrimes2).all fun n ↦ g.curve.admits12 g.pnn[n]! a b c) =
      (stage1Keeps g a b c && stage2Keeps g a b c) := by
  have e := List.range'_append_1 (s := 0) (m := g.sievePrimes1)
    (n := g.sievePrimes2 - g.sievePrimes1)
  rw [Nat.zero_add, Nat.add_sub_cancel' h] at e
  rw [stage1Keeps, stage2Keeps, ← List.all_append, List.range_eq_range', List.range_eq_range', e]

/-- Whether every sieving prime of the third stage (the `n`-th,
`sieve_primes2 ≤ n < sieve_primes3`) admits the class of `(a, b, c)`, for the globals `g` of the
sieve, by the class test of the third stage (`JPoints.CurveTables.admits3`). -/
def stage3Keeps (g : SiftGlobals) (a b c : ℤ) : Bool :=
  (List.range' g.sievePrimes2 (g.sievePrimes3 - g.sievePrimes2)).all fun n ↦
    g.curve.admits3 g.pnn[n]! a b c

/-- Whether the mask of the row `(a, b)` (`JPoints.siftMask`), for the globals `g` of the sieve,
has the bit of the third coordinate `c`, the bit `c mod 64`: the word of the condition at 2, the odd
`c` when `a` and `b` are even, or all `c`. -/
def maskKeeps (g : SiftGlobals) (a b c : ℤ) : Bool :=
  (siftMask g a b).2.toBitVec.getLsbD (c % 64).toNat

/-- Whether the third coordinate `c` lies in a row, for the globals `g` and the static data `sd` of
the sieve: its word `i = ⌊c / 64⌋` among the words `[w_low_all, w_high_all)` of a row, and its bit
`c mod 64` in `begmask` on the first word and in `endmask` on the last, which is `|c| ≤ H`. -/
def rangeKeeps (g : SiftGlobals) (sd : SiftData) (c : ℤ) : Bool :=
  let i := c >>> longShift
  let j := (c % 64).toNat
  decide (sd.wLowAll ≤ i ∧ i < sd.wHighAll) &&
    (i != sd.wLowAll || g.begmask.toBitVec.getLsbD j) &&
    (i != sd.wHighAll - 1 || g.endmask.toBitVec.getLsbD j)

/-- The third coordinates of a row are those of absolute value at most the height bound `H`, for the
words `⌊-H / 64⌋` to `⌊H / 64⌋ + 1` of a row and the masks of its first and its last word as `main`
sets them (`JPoints.Program.mainMasks`): the bits `j ≥ (-H) mod 64` of the first word and the bits
`j ≤ H mod 64` of the last. -/
theorem rangeKeeps_eq_decide_abs_le {g : SiftGlobals} {sd : SiftData}
    (hlo : sd.wLowAll = (-g.check.height) >>> longShift)
    (hhi : sd.wHighAll = (g.check.height >>> longShift) + 1)
    (hbeg : g.begmask = (Program.mainMasks g.check.height).1)
    (hend : g.endmask = (Program.mainMasks g.check.height).2) (c : ℤ) :
    rangeKeeps g sd c = decide (|c| ≤ g.check.height) := by
  have hr : ((-g.check.height) % 64).toNat < 64 := by lia
  have hs : ((-g.check.height - 1) % 64).toNat < 64 := by lia
  simp only [rangeKeeps, hlo, hhi, hbeg, hend, Program.mainMasks, UInt64.getLsbD_allOnes_shiftLeft,
    UInt64.getLsbD_allOnes_shiftRight, Int.shiftRight_eq_div_pow, longShift, longLength,
    Nat.toNat_toUInt64_mod_sixty_four hr, Nat.toNat_toUInt64_mod_sixty_four hs, Nat.cast_ofNat]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, abs_le]
  lia

/-- Whether the triple `(a, b, c)` is coprime, as `relprime3` tests it: the triples of the
enumeration of the specification are. -/
def coprimeKeeps (a b c : ℤ) : Bool := decide (gcd a (gcd b c) = 1)

/-- Whether the sieve of the row `(a, b)` hands the third coordinate `c` to the exact check, for the
globals `g` and the static data `sd` of the sieve: the sieving primes of the three stages admit the
class of `(a, b, c)`, the mask of the row has its bit, it lies in the row, and the triple is
coprime. The triples on the conic, which the sieve of a row also drops, are those of
`JPoints.conic`. -/
def colKeeps (g : SiftGlobals) (sd : SiftData) (a b c : ℤ) : Bool :=
  stage1Keeps g a b c && stage2Keeps g a b c && stage3Keeps g a b c && maskKeeps g a b c &&
    rangeKeeps g sd c && coprimeKeeps a b c

/-- Whether the triple `(a, b, c)` lies on the conic `b² = 4ac`: `(0, 0, 1)` and the triples of the
double points, which the sieve of a row drops at `c₀ = b² / 4a`. -/
def conic (a b c : ℤ) : Bool := decide (b ^ 2 = 4 * a * c)

/-- The points that the sieve of the row `(a, b)` in the box finds, for the globals `g` and the
static data `sd` of the sieve: the points over the triples `(a, b, c)` of the row
(`JPoints.CheckGlobals.points`) whose third coordinate the sieve hands to the exact check
(`JPoints.colKeeps`) off the conic, `c` increasing, as the sieve takes the bits of a row. -/
def rowPoints (g : SiftGlobals) (sd : SiftData) (a b : ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  ((intRange g.check.H).filter fun c ↦ colKeeps g sd a b c && !conic a b c).flatMap
    fun c ↦ g.check.points (a, b, c)

/-! ### The bands of the tube and of the real region -/

/-- The band of `sift_bands` that holds the row `b` of the rows from `bFirst` on by the step `m`,
for the height bound `H`: for `len` the largest multiple of `m` up to `TUBE_BAND` (or `1` when `m`
exceeds `TUBE_BAND`) and the step `len` (or `m`) of the bands, the band from `bFirst` on that holds
`b`, its first and its last row, the last cut at `H`. -/
def bandOf (H bFirst m b : ℤ) : ℤ × ℤ :=
  let band : ℤ := tubeBand
  let len := if m > band then 1 else band - band.tmod m
  let step := if m > band then m else len
  let bLo := bFirst + (b - bFirst) / step * step
  (bLo, if bLo + len - 1 > H then H else bLo + len - 1)

/-- The number of rows of a band of `sift_bands` for the rows by the step `m`: the largest multiple
of `m` up to `TUBE_BAND`, or `1` when `m` exceeds `TUBE_BAND`. -/
abbrev bandLen (m : ℤ) : ℤ :=
  if (tubeBand : ℤ) < m then 1 else tubeBand - (tubeBand : ℤ).tmod m

/-- The distance from the first row of a band of `sift_bands` to that of the next for the rows by
the step `m`: `m` when `m` exceeds `TUBE_BAND`, and the length of a band (`JPoints.bandLen`)
otherwise. -/
abbrev bandStep (m : ℤ) : ℤ :=
  if (tubeBand : ℤ) < m then m else bandLen m

/-- The last row of the band of `sift_bands` from the row `bLo` for the rows by the step `m` and the
height bound `H`: the band (`JPoints.bandLen`) cut at `H`. -/
abbrev bandEnd (H bLo m : ℤ) : ℤ :=
  if H < bLo + bandLen m - 1 then H else bLo + bandLen m - 1

theorem bandLen_bandStep {m : ℤ} (hm : 0 < m) :
    1 ≤ bandLen m ∧ bandLen m ≤ bandStep m ∧ bandStep m - m < bandLen m ∧ m ∣ bandStep m := by
  have := tubeBand_pos
  rw [bandStep, bandLen]
  split_ifs with h
  · exact ⟨le_rfl, by lia, by lia, dvd_rfl⟩
  · rw [Int.tmod_eq_emod_of_nonneg (by lia)]
    have h1 := Int.emod_lt_of_pos (tubeBand : ℤ) hm
    have h2 := Int.emod_nonneg (tubeBand : ℤ) hm.ne'
    exact ⟨by lia, le_rfl, by lia, Int.dvd_self_sub_emod⟩

theorem bandOf_eq_bandEnd (H bFirst m b : ℤ) :
    bandOf H bFirst m b = (bFirst + (b - bFirst) / bandStep m * bandStep m,
      bandEnd H (bFirst + (b - bFirst) / bandStep m * bandStep m) m) := rfl

private theorem bandEnd_sub_lt {H bLo m : ℤ} (hm : 0 < m) : bandEnd H bLo m - bLo < bandStep m := by
  have := bandLen_bandStep hm
  rw [bandEnd]
  split_ifs <;> lia

theorem bandOf_add_mul {H bFirst m : ℤ} (hm : 0 < m) {t k : ℕ}
    (hk : k * m ≤ bandEnd H (bFirst + t * bandStep m) m - (bFirst + t * bandStep m)) :
    bandOf H bFirst m (bFirst + t * bandStep m + k * m) =
      (bFirst + t * bandStep m, bandEnd H (bFirst + t * bandStep m) m) := by
  have h := bandEnd_sub_lt (H := H) (bLo := bFirst + t * bandStep m) hm
  have := bandLen_bandStep hm
  have hs : (bFirst + t * bandStep m + k * m - bFirst) / bandStep m = t := by
    rw [show bFirst + t * bandStep m + k * m - bFirst = k * m + t * bandStep m by ring,
      Int.add_mul_ediv_right _ _ (by lia), Int.ediv_eq_zero_of_lt (by positivity) (by lia),
      zero_add]
  rw [bandOf_eq_bandEnd, hs]

theorem bandOf_fst_le {H bFirst m b bLo bHi : ℤ} (hm : 0 < m)
    (h : bandOf H bFirst m b = (bLo, bHi)) : bLo ≤ b := by
  have hs : 0 < bandStep m := by lia [bandLen_bandStep hm]
  rw [bandOf_eq_bandEnd, Prod.mk.injEq] at h
  generalize bandStep m = s at h hs
  lia [Int.ediv_mul_le (b - bFirst) hs.ne']

/-- A row `b ≤ H` of the step `m` from `bFirst` on lies in its band: it lies below the first row of
the next band, whose distance is a multiple of `m`, so that it lies at most the step of the bands
less `m` after the first row of its band, within the length of a band. -/
theorem le_bandOf_snd {H bFirst m b bLo bHi : ℤ} (hm : 0 < m) (hmb : m ∣ b - bFirst)
    (hbH : b ≤ H) (h : bandOf H bFirst m b = (bLo, bHi)) : b ≤ bHi := by
  obtain ⟨h1, h2, h3, h4⟩ := bandLen_bandStep hm
  rw [bandOf_eq_bandEnd, Prod.mk.injEq, bandEnd] at h
  generalize bandStep m = s at h h2 h3 h4
  generalize bandLen m = len at h h1 h2 h3
  have he := Int.emod_def (b - bFirst) s
  have hlt := Int.emod_lt_of_pos (b - bFirst) (show 0 < s by lia)
  have hle := Int.le_of_dvd (by lia) (dvd_sub h4 (he ▸ dvd_sub hmb (dvd_mul_of_dvd_left h4 _)))
  split_ifs at h <;> lia

theorem le_bandOf_fst {H bFirst m b bLo bHi : ℤ} (hm : 0 < m) (hb : bFirst ≤ b)
    (h : bandOf H bFirst m b = (bLo, bHi)) : bFirst ≤ bLo := by
  have hs : 0 < bandStep m := by lia [bandLen_bandStep hm]
  rw [bandOf_eq_bandEnd, Prod.mk.injEq] at h
  generalize bandStep m = s at h hs
  lia [Int.mul_nonneg (Int.ediv_nonneg (sub_nonneg.mpr hb) hs.le) hs.le]

theorem bandOf_snd_le_height {H bFirst m b bLo bHi : ℤ} (h : bandOf H bFirst m b = (bLo, bHi)) :
    bHi ≤ H := by
  rw [bandOf_eq_bandEnd, Prod.mk.injEq, bandEnd] at h
  split_ifs at h <;> lia

/-- A band of `sift_bands` has at most `TUBE_BAND` rows, the room of the bands of the analysis. -/
theorem bandOf_snd_sub_fst_add_one_le {H bFirst m b bLo bHi : ℤ}
    (h : bandOf H bFirst m b = (bLo, bHi)) :
    bHi - bLo + 1 ≤ tubeBand := by
  have := tubeBand_pos
  have ht := Int.tmod_nonneg (a := (tubeBand : ℤ)) m (by lia)
  rw [bandOf_eq_bandEnd, Prod.mk.injEq, bandEnd, bandStep, bandLen] at h
  split_ifs at h <;> lia

/-- The ranges of words of the row `(a, b)` that `sift_bands` sieves in the tube or in the real
region, for the globals `g` and the static data `sd` of the sieve and the rows from `bFirst` on by
the step `m`: the analysis of the tube for `a` (`JPoints.tubeAInit`) and of the band of `b`
(`JPoints.bandOf`, `JPoints.siftBandsBand`) from the initial state of the analysis, and the ranges
of the row (`JPoints.siftBandsRanges`): their number, and their lower and their upper ends. -/
def bandRanges (g : BandGlobals) (sd : SiftData) (a bFirst m b : ℤ) : ℕ × Array ℤ × Array ℤ :=
  let (bLo, bHi) := bandOf g.sift.check.height bFirst m b
  let tube := g.sieveMode == 1
  let t := (tubeAInit g.kd g.sift.check.height sd.th sd.th2 TubeState.initial a).run
  let t := (siftBandsBand sd t bLo bHi tube).run
  (siftBandsRanges g sd t.bands a b bLo tube).run

/-- Whether the sieve by bands takes the third coordinate `c` of the row `(a, b)`, for the globals
`g` and the static data `sd` of the sieve and the rows from `bFirst` on by the step `m`: in the box
every `c`; in the tube and the real region, those whose word `⌊c / 64⌋` lies in a range of the row
(`JPoints.bandRanges`). -/
def bandKeeps (g : BandGlobals) (sd : SiftData) (a bFirst m b c : ℤ) : Bool :=
  g.sieveMode == 0 ||
    let r := bandRanges g sd a bFirst m b
    (List.range r.1).any fun k ↦ decide (r.2.1[k]! ≤ c >>> longShift ∧ c >>> longShift < r.2.2[k]!)

/-- The points that the sieve by bands finds in the row `(a, b)` of the rows from `bFirst` on by the
step `m`, for the globals `g` and the static data `sd` of the sieve: the points over the triples
`(a, b, c)` of the row (`JPoints.CheckGlobals.points`) whose third coordinate the sieve of the row
hands to the exact check (`JPoints.colKeeps`) and the analysis of its band takes
(`JPoints.bandKeeps`), off the conic, `c` increasing. -/
def bandRowPoints (g : BandGlobals) (sd : SiftData) (a bFirst m b : ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  ((intRange g.sift.check.H).filter fun c ↦
      colKeeps g.sift sd a b c && bandKeeps g sd a bFirst m b c && !conic a b c).flatMap
    fun c ↦ g.sift.check.points (a, b, c)

/-- The points that the sieve by bands finds in the rows of the first coordinate `a` from `bFirst`
on by the step `m`, for the globals `g` and the static data `sd` of the sieve: for the rows up to
the height bound (`JPoints.rowsFrom`) that the condition at 2 leaves (`JPoints.aliveKeeps`), in
order, the points of each row (`JPoints.bandRowPoints`). -/
def bandsPoints (g : BandGlobals) (sd : SiftData) (a bFirst m : ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  ((rowsFrom bFirst m g.sift.check.height).filter (aliveKeeps g.sift a)).flatMap
    (bandRowPoints g sd a bFirst m)

end JPoints

end
