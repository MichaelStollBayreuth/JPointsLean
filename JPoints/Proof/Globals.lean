/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Program
public import JPoints.Proof.Admits
public import JPoints.Proof.Double
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# What the globals of the search hold

The predicates that the contracts of the search pass from the set-up to the components: what
`read_input` leaves (`JPoints.Cli.Input.WF`); what `main` gives the search
(`JPoints.IsSearchGlobals`: the globals of the exact check, the tables of `init_main`, the
condition at 2 that admits every point, `JPoints.TwoAdic.Sound`, the intervals on which `f` is
negative, `JPoints.NegativeIntervals.Sound`, and the coefficients of the analysis of the tube); what
the search reads after the choice of the sieve (`JPoints.IsSearchSetup`: the tables of the curve,
the structure of the plan, the sieve tables and the static data of the sieve,
`JPoints.SiftData.WF`); what the components of the main search may assume of these, without the
globals of the search (`JPoints.IsSieveSetup`); and the state of the thread
(`JPoints.SiftState.WF`), whose caches the sieve keeps consistent from row to row, from the state
when the sieve starts (`JPoints.SiftState.wf_initial`).

## Main definitions

* `JPoints.Cli.Input.WF`: the globals of the command line that `read_input` accepts.
* `JPoints.TwoAdic.Sound`: the condition at 2 admits every point.
* `JPoints.NegativeIntervals.Sound`: `f` is negative on the intervals of `real_roots_init`.
* `JPoints.SiftData.WF`: the static data of the sieve as `init_sift` computes them.
* `JPoints.RowSetupCache.WF`, `JPoints.Row3Cache.WF`, `JPoints.TubeState.WF`,
  `JPoints.SiftState.WF`: the state of the thread.
* `JPoints.row3SetupEntry`: the factor and the row of the third stage that `row3_setup` sets.
* `JPoints.IsSearchGlobals`: the globals of the search as `main` sets them.
* `JPoints.IsSearchSetup`: what the search reads after the choice of the sieve.
* `JPoints.IsSieveSetup`: what the components of the main search may assume.
* `JPoints.SiftData.Sized`: the sizes of the arrays of the static data of the sieve.

## Main statements

* `JPoints.RowSetupCache.wf_initial`, `JPoints.Row3Cache.wf_initial`,
  `JPoints.TubeState.wf_initial`, `JPoints.SiftState.wf_initial`: the state of the thread when the
  sieve starts is consistent.
* `JPoints.SiftData.sized_initial`: the static data when the program starts have the sizes.
* `JPoints.IsSieveSetup.check`, `JPoints.IsSieveSetup.pnn_lt`: the globals of the exact check and
  the sieving primes of a set-up.

## Implementation notes

The caches of the state of the thread (`JPoints.RowSetupCache.WF`, `JPoints.Row3Cache.WF`,
`JPoints.TubeState.WF`) say what the sieve reads of them before it writes them again: the residues
and the rows of the last row of `row_setup` and the data of the last row of the third stage, for a
first coordinate `a ≥ 0`, which the C code reduces by `%` (`Int.tmod` in the model, the remainder
in `[0, p)` for `a ≥ 0`), and the products of the last cell of `tube_cell`; the contracts pass them
from their postconditions to the preconditions of the next call. The predicates on the plan of the
sieve are on what the search reads of it, for every value of the `Float`s of the cost model that
chose it.
-/

@[expose] public section

namespace JPoints

/-! ### The command line -/

/-- The globals `input` of the command line as `read_input` leaves them when it accepts the command
line: seven coefficients of a squarefree polynomial whose degree, at least `5`, is that of their
list; `1 ≤ height ≤ MAX_HEIGHT`; the bound on the fourth coordinate at least `1`, and the fourth
coordinate bounded unless `-a` is given; `num_primes` in `[1, NUM_PRIMES]`; the numbers of sieving
primes `-1` (the choice of the cost model) or in `[0, num_primes]`, each at most the numbers of the
later stages that are not `-1`; and the size of the bit array at least `1`. -/
structure Cli.Input.WF (input : Cli.Input) : Prop where
  /-- Seven coefficients. -/
  size_coeffs : input.coeffs.size = 7
  /-- The degree is that of the coefficients. -/
  degree_coeffs : (JPoints.degree input.coeffs.toList : ℤ) = input.degree
  /-- The degree is at least `5`. -/
  five_le_degree : 5 ≤ input.degree
  /-- The polynomial is squarefree. -/
  squarefree : Squarefree (poly input.coeffs.toList)
  /-- The height bound is positive. -/
  one_le_height : 1 ≤ input.height
  /-- The height bound is at most `MAX_HEIGHT`. -/
  height_le_maxHeight : input.height ≤ maxHeight
  /-- The bound on the fourth coordinate is positive. -/
  one_le_dbound : 1 ≤ input.dbound
  /-- The fourth coordinate is bounded unless `-a` is given. -/
  allPoints_of_dbounded_eq_false : input.dbounded = false → input.allPoints = true
  /-- `num_primes` is positive. -/
  one_le_numPrimes : 1 ≤ input.numPrimes
  /-- `num_primes` is at most `NUM_PRIMES`. -/
  numPrimes_le : input.numPrimes ≤ JPoints.numPrimes
  /-- `sieve_primes1` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes1 : -1 ≤ input.sievePrimes1
  /-- `sieve_primes2` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes2 : -1 ≤ input.sievePrimes2
  /-- `sieve_primes3` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes3 : -1 ≤ input.sievePrimes3
  /-- `sieve_primes1` is at most `num_primes`. -/
  sievePrimes1_le_numPrimes : input.sievePrimes1 ≤ input.numPrimes
  /-- `sieve_primes2` is at most `num_primes`. -/
  sievePrimes2_le_numPrimes : input.sievePrimes2 ≤ input.numPrimes
  /-- `sieve_primes3` is at most `num_primes`. -/
  sievePrimes3_le_numPrimes : input.sievePrimes3 ≤ input.numPrimes
  /-- `sieve_primes1` is at most `sieve_primes2` when that is not `-1`. -/
  sievePrimes1_le_sievePrimes2 : 0 ≤ input.sievePrimes2 → input.sievePrimes1 ≤ input.sievePrimes2
  /-- `sieve_primes1` is at most `sieve_primes3` when that is not `-1`. -/
  sievePrimes1_le_sievePrimes3 : 0 ≤ input.sievePrimes3 → input.sievePrimes1 ≤ input.sievePrimes3
  /-- `sieve_primes2` is at most `sieve_primes3` when that is not `-1`. -/
  sievePrimes2_le_sievePrimes3 : 0 ≤ input.sievePrimes3 → input.sievePrimes2 ≤ input.sievePrimes3
  /-- The size of the bit array is positive. -/
  one_le_arraySize : 1 ≤ input.arraySize

/-! ### The condition at 2 and the real region -/

/-- The condition at 2 `tw` admits every point of the curve with the coefficients `cs` when the
sieve uses it: for a coprime triple `(a, b, c)` with `a ≠ 0` over which a point lies
(`JPoints.HasPointOver`), the class of `(a, b)` modulo `64` is alive (`alive2`) and its word of
`mask2` has the bit of `c mod 64`. -/
structure TwoAdic.Sound (tw : TwoAdic) (cs : List ℤ) : Prop where
  /-- The class of the first two coordinates of a point is alive. -/
  alive2 (h2 : tw.use2 = true) {a b c : ℤ} (ha : a ≠ 0) (habc : gcd a (gcd b c) = 1)
    (h : HasPointOver cs (a, b, c)) : tw.alive2[(a % 64).toNat * 64 + (b % 64).toNat]! = true
  /-- The word of the class of the first two coordinates of a point has the bit of the third. -/
  mask2 (h2 : tw.use2 = true) {a b c : ℤ} (ha : a ≠ 0) (habc : gcd a (gcd b c) = 1)
    (h : HasPointOver cs (a, b, c)) :
    (tw.mask2[(a % 64).toNat * 64 + (b % 64).toNat]!).toBitVec.getLsbD (c % 64).toNat = true

/-- The intervals `neg` on which the polynomial `f` with the coefficients `cs` is negative, as
`real_roots_init` finds them by Sturm's theorem: at most four, the ends of the shrunk ones no NaN,
and `f` negative on the open interval between the values of the ends of each (`JPoints.doubleValue`,
`±∞` for an infinite end). -/
structure NegativeIntervals.Sound (neg : NegativeIntervals) (cs : List ℤ) : Prop where
  /-- At most four intervals, as `f` has at most six real roots. -/
  numNeg_le : neg.numNeg ≤ 4
  /-- The lower ends of the shrunk intervals are no NaN. -/
  not_isNaN_shrunkLo {i : ℕ} (hi : i < neg.numNeg) : ¬IsNaN neg.shrunkLo[i]!.bits
  /-- The upper ends of the shrunk intervals are no NaN. -/
  not_isNaN_shrunkHi {i : ℕ} (hi : i < neg.numNeg) : ¬IsNaN neg.shrunkHi[i]!.bits
  /-- `f` is negative on the shrunk intervals. -/
  eval_neg {i : ℕ} (hi : i < neg.numNeg) {x : ℚ} (hlo : doubleValue neg.shrunkLo[i]!.bits < x)
    (hhi : (x : WithBotTop ℚ) < doubleValue neg.shrunkHi[i]!.bits) : (poly cs).eval x < 0

/-! ### The static data of the sieve -/

/-- The static data `sd` of the sieve as `init_sift` computes them for the globals `g` of the
sieve: the sieving primes of the three stages, the lengths of the rows of their sieve tables and of
the blocks of one residue class of `a`, the residues of the positions in a chunk, the row of the
third stage that admits every class and the reciprocals of the third stage; the words of a whole
row, from `⌊-H / 64⌋` to `⌊H / 64⌋ + 1`, and its chunks of `array_size` words, each with the walks
of the first-stage primes over it (`JPoints.initSiftWalk`) and the residues of its first word; the
bound on the fourth coordinate as a double and its square, and the reciprocals of the primes as
doubles. -/
structure SiftData.WF (sd : SiftData) (g : SiftGlobals) : Prop where
  /-- The number of the sieving primes of all three stages. -/
  npr_eq : sd.npr = g.sievePrimes3
  /-- The sieving primes. -/
  pr_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.pr[n]! = sievingPrime g.pnn n
  /-- The lengths of the rows of the sieve tables. -/
  rowlen_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.rowlen[n]! = sd.pr[n]! + 1
  /-- The lengths of the blocks of the rows of one residue class of `a`. -/
  blocklen_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.blocklen[n]! = sd.pr[n]! * (sd.pr[n]! + 1)
  /-- The residues of the positions in a chunk. -/
  res0_eq {k n : ℕ} (hk : k ≤ g.arraySize) (hn : n < g.sievePrimes3) :
    sd.res0[k * sd.npr + n]! = k % sd.pr[n]!
  /-- The row of the third stage that admits every class. -/
  allOnes_eq {x : ℕ} (hx : x < maxPrimeEven) : sd.allOnes[x]! = true
  /-- The reciprocals `⌈2 ^ 32 / p⌉` of the primes of the third stage. -/
  recip3_eq {m : ℕ} (hm : m < g.sievePrimes3 - g.sievePrimes2) :
    sd.recip3[m]! = ((1 : UInt64) <<< 32 + (sd.pr[g.sievePrimes2 + m]!).toUInt64 - 1) /
      (sd.pr[g.sievePrimes2 + m]!).toUInt64
  /-- The first word of a row. -/
  wLowAll_eq : sd.wLowAll = (-g.check.height) >>> longShift
  /-- The word after a row. -/
  wHighAll_eq : sd.wHighAll = (g.check.height >>> longShift) + 1
  /-- The number of the chunks of a row. -/
  numChunks_eq : sd.numChunks = (ceilDiv (sd.wHighAll - sd.wLowAll) g.arraySize).toNat
  /-- The array of the chunks. -/
  size_chunks : sd.chunks.size = sd.numChunks
  /-- The first word of a chunk. -/
  wLow_chunk {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wLow = sd.wLowAll + (k * g.arraySize : ℕ)
  /-- The word after a chunk. -/
  wHigh_chunk {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wHigh = min (sd.wLowAll + (k * g.arraySize : ℕ) + g.arraySize) sd.wHighAll
  /-- The walks of the first-stage primes over a chunk. -/
  walk_chunk {k : ℕ} (hk : k < sd.numChunks) {n : ℕ} (hn : n < g.sievePrimes1) :
    (sd.chunks[k]!).walk[n]! = (initSiftWalk (sievingPrime g.pnn n) (sd.chunks[k]!).wLow
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat).run
  /-- The residues of the first word of a chunk. -/
  res_chunk {k : ℕ} (hk : k < sd.numChunks) {n : ℕ} (hn : n < g.sievePrimes3) :
    (sd.chunks[k]!).res[n]! = ((sd.chunks[k]!).wLow % sd.pr[n]!).toNat
  /-- The bound on the fourth coordinate as a double. -/
  th_eq : sd.th = Double.ofInt g.check.dbound
  /-- Its square. -/
  th2_eq : sd.th2 = sd.th * sd.th
  /-- The reciprocals of the sieving primes as doubles. -/
  invp_eq {n : ℕ} (hn : n < g.sievePrimes3) : sd.invp[n]! = 1.0 / Double.ofInt sd.pr[n]!

/-! ### The state of the thread -/

/-- The statics `c` of `row_setup` and the rows `rowptr` of the state of the thread, for the
globals `g` and the static data `sd` of the sieve, as the sieve keeps them from row to row: after a
row `(last_a, last_b)` with `last_a ≥ 0` (before the first, `last_a = -1`), for the `n`-th sieving
prime `p = pr[n]` of the first two stages, `n < sieve_primes2`, the residue `bres[n] = last_b mod p`
and the index `rowptr[n] = ((last_a mod p) p + bres[n]) (p + 1)` of the row of `(last_a, last_b)`
in `sieve_tab[n]`, which the sieve of the row reads and from which `row_setup` steps to the next
row of the same `a`; for a step `last_d ≠ 0`, its residues `dres[n] = last_d mod p` and the offsets
`drow[n] = dres[n] (p + 1)`, by which `row_setup` steps again; and arrays of `JPoints.numPrimes`
entries, which hold what `row_setup` writes. -/
structure RowSetupCache.WF (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ)
    (c : RowSetupCache) : Prop where
  /-- The rows have an entry for every prime. -/
  size_rowptr : rowptr.size = numPrimes
  /-- The residues of the second coordinate have an entry for every prime. -/
  size_bres : c.bres.size = numPrimes
  /-- The residues of the step have an entry for every prime. -/
  size_dres : c.dres.size = numPrimes
  /-- The offsets of the step have an entry for every prime. -/
  size_drow : c.drow.size = numPrimes
  /-- The residues of the second coordinate of the last row. -/
  bres_eq (ha : 0 ≤ c.lastA) {n : ℕ} (hn : n < g.sievePrimes2) :
    c.bres[n]! = (c.lastB % sd.pr[n]!).toNat
  /-- The rows of the last row in the sieve tables. -/
  rowptr_eq (ha : 0 ≤ c.lastA) {n : ℕ} (hn : n < g.sievePrimes2) :
    rowptr[n]! = ((c.lastA % sd.pr[n]!).toNat * sd.pr[n]! + c.bres[n]!) * (sd.pr[n]! + 1)
  /-- The residues of the step. -/
  dres_eq (hd : c.lastD ≠ 0) {n : ℕ} (hn : n < g.sievePrimes2) :
    c.dres[n]! = (c.lastD % sd.pr[n]!).toNat
  /-- The offsets of the step in the sieve tables. -/
  drow_eq (hd : c.lastD ≠ 0) {n : ℕ} (hn : n < g.sievePrimes2) :
    c.drow[n]! = c.dres[n]! * (sd.pr[n]! + 1)

/-- The factor `mult3[m]` and the row `tab3[m]` that `row3_setup` sets for the second coordinate
`b` at the `m`-th prime `p = pr[n]` of the third stage, `n = sieve_primes2 + m`, from the entry
`inva` of `inva3`, for the globals `g` and the static data `sd` of the sieve: for `inva ≠ 0`
(`p ∤ a`), the factor `inva` and the row of `(1, (b mod p) inva)` of the exact table of the third
stage, the product reduced by `MOD3` (`JPoints.mod3`); for `p ∣ a` and `p ∤ b`, the inverse of
`b mod p` from `inverses` and the table of the values of `f` that are squares; and for `p` dividing
both, the factor `0` and the row `all_ones`. -/
def row3SetupEntry (g : SiftGlobals) (sd : SiftData) (inva b : ℤ) (m : ℕ) : ℤ × Tab3Ptr :=
  let n := g.sievePrimes2 + m
  let pn := g.pnn[n]!
  let bp := b % sd.pr[n]!
  if inva ≠ 0 then
    (inva, .pointOnJ ((pn * maxPrimeEven + (mod3 sd g.sievePrimes2 m (bp * inva)).toNat) *
      maxPrimeEven))
  else if bp ≠ 0 then
    (g.tables.inverses[pn * maxPrimeEven + bp.toNat]!, .fSquare (pn * maxPrimeEven))
  else (0, .allOnes)

/-- The data `r` of the third stage of the state of the thread, for the globals `g` and the static
data `sd` of the sieve, as the sieve keeps them from bit to bit and from row to row: after a row
`(row3_a, row3_b)` with `row3_a ≥ 0` (before the first, `row3_a = -1`), for the `m`-th prime
`p = pr[n]` of the third stage, `n = sieve_primes2 + m`, `m < sieve_primes3 - sieve_primes2`, the
inverse `inva3[m]` of `row3_a mod p` from `inverses`, or `0` when `p ∣ row3_a`, which `row3_setup`
keeps for the next row of the same `a`, and the factor `mult3[m]` and the row `tab3[m]` of
`(row3_a, row3_b)` (`JPoints.row3SetupEntry`), which `check_bit` reads; and arrays of
`JPoints.numPrimes` entries, which hold what `row3_setup` writes. -/
structure Row3Cache.WF (g : SiftGlobals) (sd : SiftData) (r : Row3Cache) : Prop where
  /-- The rows have an entry for every prime. -/
  size_tab3 : r.tab3.size = numPrimes
  /-- The factors have an entry for every prime. -/
  size_mult3 : r.mult3.size = numPrimes
  /-- The inverses of the first coordinate have an entry for every prime. -/
  size_inva3 : r.inva3.size = numPrimes
  /-- The inverses of the first coordinate of the last row. -/
  inva3_eq (ha : 0 ≤ r.row3A) {m : ℕ} (hm : m < g.sievePrimes3 - g.sievePrimes2) :
    r.inva3[m]! = if r.row3A % sd.pr[g.sievePrimes2 + m]! = 0 then 0 else
      g.tables.inverses[g.pnn[g.sievePrimes2 + m]! * maxPrimeEven +
        (r.row3A % sd.pr[g.sievePrimes2 + m]!).toNat]!
  /-- The factors of the last row. -/
  mult3_eq (ha : 0 ≤ r.row3A) {m : ℕ} (hm : m < g.sievePrimes3 - g.sievePrimes2) :
    r.mult3[m]! = (row3SetupEntry g sd r.inva3[m]! r.row3B m).1
  /-- The rows of the tables of the curve of the last row. -/
  tab3_eq (ha : 0 ≤ r.row3A) {m : ℕ} (hm : m < g.sievePrimes3 - g.sievePrimes2) :
    r.tab3[m]! = (row3SetupEntry g sd r.inva3[m]! r.row3B m).2

/-- The state `t` of the analysis of the tube in the state of the thread, as the analysis keeps it
from cell to cell and from band to band: the arrays of the polynomials of a first coordinate and of
the products of the cache of `tube_cell` with `JPoints.numCoeffs` entries, which `tube_a_init` and
`tube_cell` fill whole; the cache without products (`last_rb = -1.0`, which the half-size `rb ≥ 0`
of a cell never matches), or with the products `rb ^ j rc ^ k` of its half-sizes
`(last_rb, last_rc)` as `JPoints.tubeCellProducts` computes them, with `last_rb` no `-0.0`, so that
a cell whose half-sizes the comparison `!=` of `tube_cell` finds equal to them has these products
bit for bit; and the bands with `TUBE_BAND` counts and `2 TUBE_RANGES TUBE_BAND` ends, which hold
what `tube_emit` writes for the rows of a band. None of this depends on the globals or the static
data of the sieve. -/
structure TubeState.WF (t : TubeState) : Prop where
  /-- The coefficients of `k₀` have an entry for every index. -/
  size_k0 : t.k0.size = numCoeffs
  /-- The coefficients of `k₁` have an entry for every index. -/
  size_k1 : t.k1.size = numCoeffs
  /-- The coefficients of `k₂` have an entry for every index. -/
  size_k2 : t.k2.size = numCoeffs
  /-- The coefficients of the bound have an entry for every index. -/
  size_ka : t.ka.size = numCoeffs
  /-- The products of the cache have an entry for every index. -/
  size_rp : t.cache.rp.size = numCoeffs
  /-- The cache holds no products, or those of its half-sizes. -/
  lastRb_eq_or_rp_eq : t.cache.lastRb = -1.0 ∨ t.cache.lastRb ≠ -0.0 ∧
    t.cache.rp = (tubeCellProducts .initial t.cache.lastRb t.cache.lastRc).run.rp
  /-- The counts of the rows of a band. -/
  size_bandNr : t.bands.bandNr.size = tubeBand
  /-- The ends of the ranges of the rows of a band. -/
  size_bandRg : t.bands.bandRg.size = 2 * tubeRanges * tubeBand

/-- The state `s` of the thread as the sieve keeps it from row to row, for the globals `g` of the
sieve by bands and the static data `sd` of the sieve: the bit array of `array_size + 1` words, the
statics of `row_setup` with the rows (`JPoints.RowSetupCache.WF`), the data of the third stage
(`JPoints.Row3Cache.WF`), the state of the analysis of the tube (`JPoints.TubeState.WF`), and the
chunk looked up last among the chunks of a row. The counters and the output are not constrained. -/
structure SiftState.WF (g : BandGlobals) (sd : SiftData) (s : SiftState) : Prop where
  /-- The bit array holds a chunk. -/
  size_survivors : s.survivors.size = g.sift.arraySize + 1
  /-- The statics of `row_setup` and the rows. -/
  rowSetup : RowSetupCache.WF g.sift sd s.rowptr s.rowSetup
  /-- The data of the third stage. -/
  row3 : Row3Cache.WF g.sift sd s.row3
  /-- The state of the analysis of the tube. -/
  tube : s.tube.WF
  /-- The chunk looked up last is a chunk of the row. -/
  curChunk_lt : s.curChunk < sd.numChunks

/-- The statics of `row_setup` and the rows when the program starts (`last_a = -1`,
`last_d = 0`) are consistent. -/
theorem RowSetupCache.wf_initial (g : SiftGlobals) (sd : SiftData) :
    RowSetupCache.WF g sd (.replicate numPrimes 0) RowSetupCache.initial where
  size_rowptr := Array.size_replicate
  size_bres := Array.size_replicate
  size_dres := Array.size_replicate
  size_drow := Array.size_replicate
  bres_eq h := absurd h (by decide)
  rowptr_eq h := absurd h (by decide)
  dres_eq h := absurd rfl h
  drow_eq h := absurd rfl h

/-- The data of the third stage when the program starts (`row3_a = -1`) are consistent. -/
theorem Row3Cache.wf_initial (g : SiftGlobals) (sd : SiftData) :
    Row3Cache.WF g sd Row3Cache.initial where
  size_tab3 := Array.size_replicate
  size_mult3 := Array.size_replicate
  size_inva3 := Array.size_replicate
  inva3_eq h := absurd h (by decide)
  mult3_eq h := absurd h (by decide)
  tab3_eq h := absurd h (by decide)

/-- The state of the analysis of the tube when the program starts, whose cache holds no products,
is consistent. -/
theorem TubeState.wf_initial : TubeState.initial.WF where
  size_k0 := Array.size_replicate
  size_k1 := Array.size_replicate
  size_k2 := Array.size_replicate
  size_ka := Array.size_replicate
  size_rp := Array.size_replicate
  lastRb_eq_or_rp_eq := .inl rfl
  size_bandNr := Array.size_replicate
  size_bandRg := Array.size_replicate

/-! ### The globals of the search -/

/-- The globals `g` of the search as `main` sets them for the command line that `read_input`
accepts: the globals of the exact check (`JPoints.CheckGlobals.WF`) from the globals of the command
line (`JPoints.Cli.Input.WF`), the tables of `init_main` (`JPoints.Tables.WF`), the curve searched
for the choice, the coefficients of the analysis of the tube (`JPoints.tubeInitCoeffs`), the
condition at 2 that admits every point (`JPoints.TwoAdic.Sound`), the intervals of
`real_roots_init` (`JPoints.realRootsInit`), on which `f` is negative unless `-N 0` leaves the
sieve without primes (`JPoints.NegativeIntervals.Sound`), the size of the bit array and the masks
of the ends of a row (`JPoints.Program.mainMasks`). -/
structure IsSearchGlobals (g : SearchGlobals) : Prop where
  /-- The globals of the exact check. -/
  check : g.check.WF
  /-- The globals of the command line. -/
  input : g.choice.input.WF
  /-- The height bound of the exact check is that of the command line. -/
  height_eq : g.check.height = g.choice.input.height
  /-- The bound on the fourth coordinate of the exact check is that of the command line. -/
  dbound_eq : g.check.dbound = g.choice.input.dbound
  /-- Whether the fourth coordinate is bounded, as the command line says. -/
  dbounded_eq : g.check.dbounded = g.choice.input.dbounded
  /-- The tables of `init_main`. -/
  tables : g.tables.WF
  /-- The choice reads the curve searched. -/
  curve_eq : g.choice.curve = g.check.curve
  /-- The coefficients of the analysis of the tube. -/
  kd_eq : g.kd = (tubeInitCoeffs g.check.curve g.check.kummer).run
  /-- The condition at 2 admits every point. -/
  two : g.choice.two.Sound g.check.coeffList
  /-- The intervals of `real_roots_init`. -/
  neg_eq : g.neg = (realRootsInit g.check.curve.coeffs g.check.curve.degree).run
  /-- `f` is negative on them, unless `-N 0` leaves the sieve without primes. -/
  neg : g.choice.input.sievePrimes3 = 0 ∨ g.neg.Sound g.check.coeffList
  /-- The bit array has a word. -/
  one_le_arraySize : 1 ≤ g.arraySize
  /-- The mask of the first word of a row. -/
  begmask_eq : g.begmask = (Program.mainMasks g.check.height).1
  /-- The mask of the last word of a row. -/
  endmask_eq : g.endmask = (Program.mainMasks g.check.height).2

/-- What the search reads after the choice of the sieve, for the globals `g` of the search, the
globals `bg` of the sieve by bands and the static data `sd` of the sieve that `find_points` sets up
(`JPoints.findPointsSetup`), for every value of the `Float`s of the cost model: the globals of the
exact check and the tables of `init_main` of `g`; the tables of the curve for the primes considered
and the sieving primes (`JPoints.CurveTables.WF`); the plan, with distinct sieving primes among the
primes considered, `sieve_primes1 ≤ sieve_primes2 ≤ sieve_primes3 ≤ num_primes`, the primes of the
first two stages at most `MAX_TABLE_PRIME`, the mode `0`, `1` or `2`, the tube only for a bounded
fourth coordinate, the box without the condition at 2 when there are no sieving primes, and none
under `-N 0`; the sieve tables of the first two stages (`JPoints.SieveTables.WF`); the static data
(`JPoints.SiftData.WF`); the condition at 2 that admits every point (`JPoints.TwoAdic.Sound`); and
the intervals, the coefficients of the tube, the size of the bit array and the masks of `g`. -/
structure IsSearchSetup (g : SearchGlobals) (bg : BandGlobals) (sd : SiftData) : Prop where
  /-- The globals of the exact check. -/
  check_eq : bg.sift.check = g.check
  /-- The tables of `init_main`. -/
  tables_eq : bg.sift.tables = g.tables
  /-- The tables of the curve. -/
  curveTables : bg.sift.curve.WF g.check.coeffList g.check.curve.degree
    g.choice.input.numPrimes.toNat bg.sift.pnn bg.sift.sievePrimes3
  /-- The first stage is part of the first two. -/
  sievePrimes1_le_sievePrimes2 : bg.sift.sievePrimes1 ≤ bg.sift.sievePrimes2
  /-- The first two stages are part of the three. -/
  sievePrimes2_le_sievePrimes3 : bg.sift.sievePrimes2 ≤ bg.sift.sievePrimes3
  /-- The sieving primes are among the primes considered. -/
  sievePrimes3_le_numPrimes : bg.sift.sievePrimes3 ≤ g.choice.input.numPrimes.toNat
  /-- The indices of the sieving primes are those of primes considered. -/
  pnn_lt {n : ℕ} (hn : n < bg.sift.sievePrimes3) : bg.sift.pnn[n]! < g.choice.input.numPrimes.toNat
  /-- The sieving primes are distinct. -/
  pnn_injective {m n : ℕ} (hm : m < bg.sift.sievePrimes3) (hn : n < bg.sift.sievePrimes3)
    (h : bg.sift.pnn[m]! = bg.sift.pnn[n]!) : m = n
  /-- The primes of the first two stages have sieve tables. -/
  sievingPrime_le_maxTablePrime {n : ℕ} (hn : n < bg.sift.sievePrimes2) :
    sievingPrime bg.sift.pnn n ≤ maxTablePrime
  /-- The mode is the box, the tube or the region. -/
  sieveMode_le : bg.sieveMode ≤ 2
  /-- The tube only for a bounded fourth coordinate. -/
  dbounded_of_sieveMode_eq_one : bg.sieveMode = 1 → g.check.dbounded = true
  /-- The box when there are no sieving primes. -/
  sieveMode_eq_zero_of_sievePrimes3_eq_zero : bg.sift.sievePrimes3 = 0 → bg.sieveMode = 0
  /-- No condition at 2 when there are no sieving primes. -/
  use2_eq_false_of_sievePrimes3_eq_zero : bg.sift.sievePrimes3 = 0 → bg.sift.twoAdic.use2 = false
  /-- No sieving primes under `-N 0`. -/
  sievePrimes3_eq_zero : g.choice.input.sievePrimes3 = 0 → bg.sift.sievePrimes3 = 0
  /-- The sieve tables of the first two stages. -/
  sieve : bg.sift.sieve.WF bg.sift.curve bg.sift.pnn bg.sift.sievePrimes2
  /-- The static data of the sieve. -/
  siftData : sd.WF bg.sift
  /-- The condition at 2 admits every point. -/
  twoAdic : bg.sift.twoAdic.Sound g.check.coeffList
  /-- The intervals on which `f` is negative. -/
  neg_eq : bg.neg = g.neg
  /-- The coefficients of the analysis of the tube. -/
  kd_eq : bg.kd = g.kd
  /-- The size of the bit array. -/
  arraySize_eq : bg.sift.arraySize = g.arraySize
  /-- The mask of the first word of a row. -/
  begmask_eq : bg.sift.begmask = g.begmask
  /-- The mask of the last word of a row. -/
  endmask_eq : bg.sift.endmask = g.endmask

/-- The globals `bg` of the sieve by bands and the static data `sd` of the sieve as `find_points`
sets them up after the choice of the sieve (`JPoints.IsSearchSetup`) for globals of the search as
`main` sets them (`JPoints.IsSearchGlobals`): what the components of the main search may assume,
which do not see the globals of the search. -/
def IsSieveSetup (bg : BandGlobals) (sd : SiftData) : Prop :=
  ∃ g, IsSearchGlobals g ∧ IsSearchSetup g bg sd

theorem IsSieveSetup.check {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) :
    bg.sift.check.WF := by
  obtain ⟨g, hg, hs⟩ := h
  exact hs.check_eq ▸ hg.check

/-- The sieving primes of the set-up are primes of the table. -/
theorem IsSieveSetup.pnn_lt {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) {n : ℕ}
    (hn : n < bg.sift.sievePrimes3) : bg.sift.pnn[n]! < numPrimes := by
  obtain ⟨g, hg, hs⟩ := h
  lia [hs.pnn_lt hn, hg.input.numPrimes_le]

/-- The arrays of the static data `sd` of the sieve that `init_sift` writes entry by entry have the
sizes of the static data when the program starts (`JPoints.SiftData.initial`), which `tube_sample`
keeps. -/
structure SiftData.Sized (sd : SiftData) : Prop where
  /-- The row of the third stage that admits every class. -/
  size_allOnes : sd.allOnes.size = maxPrimeEven
  /-- The reciprocals of the third stage. -/
  size_recip3 : sd.recip3.size = numPrimes
  /-- The sieving primes. -/
  size_pr : sd.pr.size = numPrimes
  /-- The lengths of the rows of the sieve tables. -/
  size_rowlen : sd.rowlen.size = numPrimes
  /-- The lengths of the blocks of the rows of one residue class of `a`. -/
  size_blocklen : sd.blocklen.size = numPrimes
  /-- The reciprocals of the sieving primes as doubles. -/
  size_invp : sd.invp.size = numPrimes

theorem SiftData.sized_initial : SiftData.initial.Sized where
  size_allOnes := Array.size_replicate
  size_recip3 := Array.size_replicate
  size_pr := Array.size_replicate
  size_rowlen := Array.size_replicate
  size_blocklen := Array.size_replicate
  size_invp := Array.size_replicate

/-- The state of the thread when its sieve starts, with a consistent state `t` of the analysis of
the tube, is consistent: the bit array of `JPoints.SiftState.initial` has `array_size + 1` words,
the caches are those when the program starts, and a row has a chunk, the first. -/
theorem SiftState.wf_initial {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd)
    {t : TubeState} (ht : t.WF) (out : Output) :
    SiftState.WF bg sd { SiftState.initial bg.sift.arraySize with tube := t, out } := by
  obtain ⟨g, hg, hs⟩ := h
  have hH := hs.check_eq ▸ hg.check.one_le_height
  have hd : 0 ≤ bg.sift.check.height / 64 + 1 - -bg.sift.check.height / 64 - 1 := by lia
  have := Int.tdiv_nonneg hd (b := (bg.sift.arraySize : ℤ)) (by lia)
  refine ⟨by simp [SiftState.initial], RowSetupCache.wf_initial .., Row3Cache.wf_initial .., ht, ?_⟩
  simp only [SiftState.initial, hs.siftData.numChunks_eq, hs.siftData.wLowAll_eq,
    hs.siftData.wHighAll_eq, ceilDiv, Int.shiftRight_eq_div_pow, longShift, Nat.reducePow,
    Nat.cast_ofNat]
  split_ifs <;> lia [hs.arraySize_eq ▸ hg.one_le_arraySize]

end JPoints

end
