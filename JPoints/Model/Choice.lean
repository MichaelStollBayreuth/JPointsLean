/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Input
public import JPoints.Model.Rates
public import JPoints.Model.TwoAdic

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Input
meta import JPoints.Model.Rates
meta import JPoints.Model.TwoAdic

/-!
# The choice of the sieving primes

The second part of `init_fmodpsquare` of `j-points`, from the choice of the sieving primes on, with
the cost model that makes the choice. `choose_primes` (`JPoints.choosePrimes`) prices the ways of a
run, the box, the region and, when the fourth coordinate is bounded, the tube without and with the
cut of its words to the real region, each by `choose_primes_mode` (`JPoints.choosePrimesMode`), and
keeps the cheapest, with its primes: the plan of the sieve (`JPoints.Plan`). `choose_primes_mode`
ranks the primes up to `MAX_TABLE_PRIME` for the first stage by their value for it, the reduction
`-log r` of the survivors per cycle of a pass and of its tables; for each number `n1` of primes of
the first stage it ranks the others for the second stage, and for each number `n2` of primes of the
first two stages all primes left for the third; it prices every admissible `(n1, n2, n3)` and keeps
the cheapest, which the options `-n`, `-M` and `-N` may pin. Then `init_fmodpsquare` fills the
tables of the third stage of the primes chosen (`JPoints.initFmodpsquareTables`) and prints the
messages 4, 7 and 8 of `message` (`JPoints.message4`, `JPoints.message7`, `JPoints.message8`):
the mode, the numbers of primes and the constants set by `-c`; the primes of the stages; and the
rates of the best prime, of the last of each stage and of the worst.

## Main definitions

* `JPoints.TubeStats`: the statistics of the analysis that the cost model reads.
* `JPoints.Plan`: the plan of the sieve that the choice makes.
* `JPoints.ChoiceGlobals`: what the choice reads from the globals.
* `JPoints.Cand`, `JPoints.compareCands`: the candidates of a stage and their order.
* `JPoints.ModeShape`, `JPoints.PrimeTerms`, `JPoints.FirstStage`, `JPoints.SecondStage`,
  `JPoints.ModeBest`: the locals of `choose_primes_mode`.
* `JPoints.choosePrimesModeShape`, `JPoints.choosePrimesModeTerms`: the terms that the mode fixes.
* `JPoints.choosePrimesModeList1`, `JPoints.choosePrimesModeRange1`,
  `JPoints.choosePrimesModeFirst`, `JPoints.choosePrimesModeList2`,
  `JPoints.choosePrimesModeRange2`, `JPoints.choosePrimesModeSecond`,
  `JPoints.choosePrimesModeList3`, `JPoints.choosePrimesModeRange3`: the rankings, the ranges of
  the numbers of primes and the costs of the stages.
* `JPoints.choosePrimesModeLoop3`, `JPoints.choosePrimesModeLoop2`, `JPoints.choosePrimesModeLoop1`:
  the loops over `n3`, `n2` and `n1`; `JPoints.choosePrimesModeKeep`: the cheapest choice kept.
* `JPoints.choosePrimesMode`, `JPoints.choosePrimes`: the cost model of one mode, and the choice.
* `JPoints.message4Mode`, `JPoints.message4Costs`, `JPoints.message4`, `JPoints.message7`,
  `JPoints.message8`: the messages of the choice.
* `JPoints.initFmodpsquareTables`, `JPoints.initFmodpsquare`: the tables of the primes chosen, and
  `init_fmodpsquare`.

## Implementation notes

The cost model runs in Lean's `Float`, IEEE 754 binary64 with the arithmetic of the platform: `+`,
`-`, `*`, `/` and `sqrt` correctly rounded, as the default build computes them on x86-64, which has
no fused multiply-add; `floor`, which is exact; and `log` and `pow` the functions of the C library
that the Lean runtime binds, on glibc an older symbol version of the routines that `j-points` binds
(`log@GLIBC_2.2.5` and `pow@GLIBC_2.2.5`, where `j-points` binds `log@GLIBC_2.29` and
`pow@GLIBC_2.29`), which give the same values on the arguments that occur here (`log` of a rate in
`(0, 1]`, `pow` of a base in `[0, 1]`) and differ in `errno` only. glibc's `log` and `pow` are not
correctly rounded and choose between variants by the processor, so that the choice of the model is
that of `j-points` on the same machine. Every expression keeps the order of the operations of the
C code, a compound assignment its right-hand side evaluated first, and every comparison is that of
the C code, with a NaN unordered. The rates, doubles of `JPoints.Double`, enter as the `Float`s of
the same bits (`JPoints.Double.toFloat`); the integers that the C code converts to doubles are below
`2 ^ 53` and convert exactly. The sorts are `JPoints.qsort`, the merge sort of glibc, which gives
the order of glibc also when a NaN value makes the comparison inconsistent. The properties of a
plan that the choice returns (the numbers of the stages increasing and at most the number of primes
considered, the primes of the first two stages at most `MAX_TABLE_PRIME`, the stages disjoint)
follow from the structure of the code, whatever the values of the `Float`s.

`choose_primes_mode` is split at its loops: the terms that the mode fixes, the ranking of each
stage, the range of the number of primes of each stage, the costs of the first two stages and the
loops over `n1`, `n2` and `n3`, with its locals in structures. The local arrays of `NUM_PRIMES`
entries of which the C code uses a prefix are arrays of `NUM_PRIMES` entries that start as zeros
(the C code leaves them uninitialized, and reads only entries that it wrote); the lists of the
candidates `list1`, `list2` and `list3` are arrays of their entries, whose sizes are the counts
`ne`, `ne2` and `ne3`. The messages are the texts that `printf` prints, a double of the cost model
by `JPoints.Double.ofFloat`; the program prints them in the order of the calls. Lean's
`Float.toBits`, and with it `JPoints.Double.ofFloat`, takes every NaN to the NaN
`0x7ff8000000000000`, so that the bits of a NaN of the cost model are not those of the C code (the
NaN of an invalid operation such as `0 * ∞` is `0xfff8000000000000`, which `printf` prints as
`-nan`); the choice only compares its doubles, and no value that a message prints is a NaN.
-/

@[expose] public section

namespace JPoints

/-! ### The globals of the choice -/

/-- The statistics of the analysis of the plane of `(b, c)` that `tube_sample` measures on a sample
of the rows, for the cost model: the words per row that the tube leaves, as they are and cut to the
real region, the cells of the analysis it visits per row, and the fraction of the rows with a word;
the words per row of the real region, in how many ranges, and the fraction of the rows that meet
it. The defaults are the initial values, which hold until `tube_sample` sets them.

C: `j-points.c:235-236`

Deviation: `Float`s for the doubles, which only the cost model and message 4 read, in a structure,
for the globals. -/
structure TubeStats where
  /-- `tube_words`: the words per row that the tube leaves. -/
  tubeWords : Float := 0.0
  /-- `tube_words_cut`: the words per row that the tube leaves, cut to the real region. -/
  tubeWordsCut : Float := 0.0
  /-- `tube_cells`: the cells of the analysis that the tube visits per row. -/
  tubeCells : Float := 0.0
  /-- `tube_rows`: the fraction of the rows with a word in the tube. -/
  tubeRows : Float := 1.0
  /-- `reg_words`: the words per row of the real region. -/
  regWords : Float := 0.0
  /-- `reg_ranges`: the ranges of words per row of the real region. -/
  regRanges : Float := 0.0
  /-- `reg_rows`: the fraction of the rows that meet the real region. -/
  regRows : Float := 1.0
  deriving Inhabited

/-- The plan of the sieve that `choose_primes` makes: the indices in the table `prime[]` of the
sieving primes, stage by stage (`pnn`); the numbers of the primes of the first stage, of the first
two stages and of all three (`sieve_primes1`, `sieve_primes2`, `sieve_primes3`); the mode of the
sieve, `0` for the box, `1` for the tube and `2` for the region (`sieve_mode`); and whether the
words of the tube are cut to the real region (`tube_cut`). The defaults are the zeros of static
storage.

C: `j-points.c:63`, `j-points.c:229-230`, `j-points.c:270-272`

Deviation: a structure for the globals; natural numbers for the `long` indices of `pnn` and for the
`int` `sieve_mode`; a Boolean for the `int` flag `tube_cut`; natural numbers for the `long`s
`sieve_primes1`, `sieve_primes2` and `sieve_primes3` after the choice, which leaves them
nonnegative (before it they hold what `read_input` leaves, `JPoints.Cli.Input`). -/
structure Plan where
  /-- `pnn`, `JPoints.numPrimes + 1` entries: the indices in `prime[]` of the primes of the first
  stage, then of the second, then of the third. -/
  pnn : Array Nat := .replicate (numPrimes + 1) 0
  /-- `sieve_primes1`: the number of the primes of the first stage. -/
  sievePrimes1 : Nat := 0
  /-- `sieve_primes2`: the number of the primes of the first two stages. -/
  sievePrimes2 : Nat := 0
  /-- `sieve_primes3`: the number of the primes of all three stages. -/
  sievePrimes3 : Nat := 0
  /-- `sieve_mode`: `0` for the box, `1` for the tube, `2` for the region. -/
  sieveMode : Nat := 0
  /-- `tube_cut`: whether the words of the tube are cut to the real region. -/
  tubeCut : Bool := false
  deriving Inhabited, Repr

/-- What the choice of the primes reads from the globals of `j-points`, by the structures that hold
them: the command line (`input`: the height bound, `num_primes`, `dbounded`, the numbers of primes
`sieve_primes1`, `sieve_primes2` and `sieve_primes3` as `read_input` leaves them, `-1` for the
choice of the cost model, `quiet`, and the constants of the cost model in force with their flags);
the curve searched (`curve`: its coefficients and its degree, of which the cost model reads the
degree and `f₅`); the number `num_neg` of the intervals on which `f` is negative; the statistics of
the analysis (`stats`); and the condition at 2 (`two`: `use2`, `density2`, `empty2`).

It models no C code of its own: it gathers globals that other structures and the analysis of the
real roots (`num_neg`) hold. -/
structure ChoiceGlobals where
  /-- The globals of the command line. -/
  input : Cli.Input
  /-- The curve searched. -/
  curve : SearchCurve
  /-- `num_neg`: the number of the intervals on which `f` is negative. -/
  numNeg : Nat
  /-- The statistics of the analysis. -/
  stats : TubeStats
  /-- The globals of the condition at 2. -/
  two : TwoAdic

/-! ### The candidates -/

/-- `cand`, a candidate of a stage of the choice: the index `n` of its prime in `prec` (not in the
table `prime[]`) and its value `v` for the stage, the reduction `-log r` of the survivors per cycle
that the prime costs in the stage per row.

C: `j-points.c:876`

Deviation: a natural number for the `long` index; a `Float` for the double. -/
structure Cand where
  /-- `n`: the index of the prime in `prec`. -/
  n : Nat := 0
  /-- `v`: the value of the prime for the stage. -/
  v : Float := 0.0
  deriving Inhabited

/-- `compare_cands`, the comparison by which `qsort` sorts the candidates by value, the largest
first: the sign of the difference `b.v - a.v`, `1`, `-1` or `0`, the last also when the difference
is a NaN, so that a NaN value compares as a tie with every value.

C: `j-points.c:877-880`

Deviation: the records passed, for the pointers. -/
def compareCands (a b : Cand) : Int :=
  let diff := b.v - a.v
  if diff > 0.0 then 1 else if diff < 0.0 then -1 else 0

/-! ### The terms that the mode fixes -/

/-- The locals of `choose_primes_mode` that its mode fixes before its loops: whether the mode is the
tube (`tube`), the pinned number of primes of the first stage (`pin1`), the words per row (`W`), the
rows of the run (`rows`), the bits per row (`bits`), the cost per row that the choice of the primes
does not change (`fixed`) and the extra cost of a pass (`passx`).

It models no C code of its own: `JPoints.choosePrimesModeShape` computes the locals. -/
structure ModeShape where
  /-- `tube`: whether the mode is the tube. -/
  tube : Bool
  /-- `pin1`: `sieve_primes1`, or `0` in the tube. -/
  pin1 : Int
  /-- `W`: the words per row. -/
  w : Float
  /-- `rows`: the rows of the run. -/
  rows : Float
  /-- `bits`: the bits per row. -/
  bits : Float
  /-- `fixed`: the cost per row that the choice of the primes does not change. -/
  fixed : Float
  /-- `passx`: the extra cost of a pass, over the ranges of the region. -/
  passx : Float

/-- The terms that the mode `mode` (`0` the box, `1` the tube, `2` the region) and the cut `cut` of
the words of the tube fix in `choose_primes_mode`, for the globals `g`: for the box,
`W = 2 ⌊H / 64⌋ + 2` words per row for the height bound `H` and the cost of a row; for the tube,
the words that it leaves (cut or not), at least `0.01`, no pinned first stage, and the cost of its
cells, of its rows (with that of the real region and of the cut for `cut`) and of its words; for the
region, its words, at least `0.01`, the cost of the real region of a row
(`RROW + REXCL · 2 num_neg`), of the rows that meet it and of its ranges, and the extra cost `PASS`
of a pass per range. The rows are `(2H + 1)(H + 1)`, or `(2H + 1)(⌊√H⌋ + 1)` for a monic quintic,
whose `a` is a square, times the fraction of the classes modulo `64` that the condition at 2 does
not empty when it is used; the bits per row `64 W`.

C: `j-points.c:930`, `j-points.c:934-938`, `j-points.c:939`, `j-points.c:940`, `j-points.c:942`,
`j-points.c:951-965`, `j-points.c:968`

Deviation: the globals passed, for the globals that the C code reads, and the locals returned in a
structure (`JPoints.ModeShape`); a natural number for the `int` `mode`, Booleans for the `int` flags
`cut` and `tube`; `Float`s for the doubles, the integers converted to `Float` exactly, `H >>> 6` for
`height>>LONG_SHIFT` on the positive `H`; the test `mpz_cmp_si` of `f₅` with `1` as the equality of
integers; `sqrt` and `floor` of `Float`. -/
def choosePrimesModeShape (mode : Nat) (cut : Bool) (g : ChoiceGlobals) : ModeShape :=
  let c := g.input.costs
  let s := g.stats
  let h := g.input.height
  let rows := Float.ofInt (2 * h + 1) *
    (if g.curve.degree == 5 && g.curve.coeffs[5]! == 1 then (Float.ofInt h).sqrt.floor + 1.0
      else Float.ofInt (h + 1))
  let rrow := c.rrow + c.rexcl * 2.0 * Float.ofNat g.numNeg
  let (w, pin1, fixed, passx) :=
    if mode == 1 then
      let w := if cut then s.tubeWordsCut else s.tubeWords
      let w := if w < 0.01 then 0.01 else w
      (w, 0, s.tubeCells * c.cell + s.tubeRows * (c.trow + (if cut then rrow + c.rcut else 0.0))
        + w * c.tword, 0.0)
    else if mode == 2 then
      (if s.regWords > 0.01 then s.regWords else 0.01, g.input.sievePrimes1,
        rrow + s.regRows * c.row + s.regRanges * c.range, s.regRanges * c.pass)
    else (Float.ofInt (2 * (h >>> longShift) + 2), g.input.sievePrimes1, c.row, 0.0)
  { tube := mode == 1, pin1, w, rows := if g.two.use2 then rows * (1.0 - g.two.empty2) else rows,
    bits := Float.ofNat longLength * w, fixed, passx }

/-- The terms of the cost model per prime, the local arrays `logr`, `tabcost` and `initcost` of
`choose_primes_mode`, at the index of the prime in `prec`: the reduction `-log r` of the survivors,
the set-up of its sieve table and the set-up of its exact table when its rate was sampled.

It models no C code of its own: `JPoints.choosePrimesModeTerms` computes them. -/
structure PrimeTerms where
  /-- `logr`: `-log r` for the rate `r`. -/
  logr : Array Float
  /-- `tabcost`: the set-up of the sieve table of the prime. -/
  tabcost : Array Float
  /-- `initcost`: the set-up of the exact table of the prime when its rate was sampled. -/
  initcost : Array Float

/-- The terms of the cost model for the first `nPrimes` records of `prec` (`num_primes`) and the
constants `c` of the cost model: for the prime `p` with the rate `r`, `-log r`; the set-up
`TABLE p p (p + 1)` of its sieve table of `p²` rows of `p + 1` words; and the set-up `INIT p p` of
its exact table when `p² > SAMPLE_PAIRS`, that is, when its rate was sampled, and `0` otherwise.

C: `j-points.c:943`, `j-points.c:969-974`

Deviation: arrays of `JPoints.numPrimes` `Float`s for the local arrays, which start as zeros (the
C code leaves them uninitialized, and reads only the entries it writes); `Float.log` for `log`,
the `Float` of the bits of the rate. -/
def choosePrimesModeTerms (c : Cli.Costs) (prec : Array Entry) (nPrimes : Nat) :
    Id PrimeTerms := do
  let mut logr := Array.replicate numPrimes 0.0
  let mut tabcost := Array.replicate numPrimes 0.0
  let mut initcost := Array.replicate numPrimes 0.0
  for n in [0:nPrimes] do
    let p := Float.ofNat prec[n]!.p
    logr := logr.set! n (-Float.log prec[n]!.r.toFloat)
    tabcost := tabcost.set! n (c.table * p * p * (p + 1.0))
    initcost := initcost.set! n
      (if p * p > Float.ofNat samplePairs then c.init * p * p else 0.0)
  return { logr, tabcost, initcost }

/-! ### The rankings and the stages -/

/-- The ranking of the first stage, `list1`: for each of the first `nPrimes` records of `prec`
whose prime `p` is at most `MAX_TABLE_PRIME`, in their order, the candidate with the value
`-log r / (W AND (1 + p / SIZE) + passx + (tabcost + initcost) / rows)`, the reduction per cycle of
a pass over the `W` words of a row with its penalty for the size of the table and of its set-up per
row, for the terms `s` of the mode and `t` of the primes and the constants `c`; sorted by value by
`qsort` with `compare_cands`.

C: `j-points.c:931`, `j-points.c:976-984`

Deviation: an array of the candidates for the array `list1`, whose size is their count `ne`; the
sort of glibc as `JPoints.qsort`. -/
def choosePrimesModeList1 (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (prec : Array Entry)
    (nPrimes : Nat) : Id (Array Cand) := do
  let mut list1 := #[]
  for n in [0:nPrimes] do
    if prec[n]!.p ≤ maxTablePrime then
      list1 := list1.push
        { n, v := t.logr[n]! / (s.w * c.and * (1.0 + Float.ofNat prec[n]!.p / c.size) + s.passx
            + (t.tabcost[n]! + t.initcost[n]!) / s.rows) }
  return qsort compareCands list1 list1.size

/-- The range `[n1lo, n1hi]` of the number of the primes of the first stage, for `ne` candidates
and the pins `pin1` (`JPoints.ModeShape.pin1`), `pin2` and `pin3` (`sieve_primes2` and
`sieve_primes3`), each `-1` when not pinned: `[0, ne]`, its upper end at most each of `pin2` and
`pin3` that is pinned, and the one number `min(pin1, n1hi)` when `pin1` is pinned.

C: `j-points.c:986-990`

Deviation: integers for the `long`s, the ends returned as natural numbers, which they are. -/
def choosePrimesModeRange1 (ne : Nat) (pin1 pin2 pin3 : Int) : Nat × Nat :=
  let hi : Int := ne
  let hi := if pin2 ≥ 0 ∧ hi > pin2 then pin2 else hi
  let hi := if pin3 ≥ 0 ∧ hi > pin3 then pin3 else hi
  let (lo, hi) := if pin1 ≥ 0 then
      let v := if pin1 < hi then pin1 else hi
      (v, v)
    else (0, hi)
  (lo.toNat, hi.toNat)

/-- The locals of the first stage of `n1` primes in `choose_primes_mode`: its cost per row
(`cost1`), its set-up (`setup1`), the density of the triples that survive it (`rho1`), and the flags
of the primes it takes (`used`).

It models no C code of its own: `JPoints.choosePrimesModeFirst` computes the locals. -/
structure FirstStage where
  /-- `cost1`: the cost per row of the first stage. -/
  cost1 : Float
  /-- `setup1`: the set-up of the first stage. -/
  setup1 : Float
  /-- `rho1`: the density of the triples that survive the first stage. -/
  rho1 : Float
  /-- `used`: at the index in `prec`, whether the first stage takes the prime. -/
  used : Array Bool

/-- The first stage of the `n1` best candidates of `list1`, for the terms `s` of the mode and `t`
of the primes, the constants `c` and the condition at 2 `two`: what it costs per row,
`W AND (1 + p / SIZE) + passx` per prime `p`, its set-up `tabcost + initcost`, the density `rho1`
of the triples that survive it, from the density that the condition at 2 admits when it is used and
the rates of its primes, and the flags `used` of its primes, which the C code first clears for the
first `nPrimes` indices.

C: `j-points.c:992`, `j-points.c:994-1001`

Deviation: the flags taken and returned, for the local array that the loop over `n1` reuses; an
array of Booleans for the array of `int` flags; the `Float` of the bits of the rate. -/
def choosePrimesModeFirst (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (two : TwoAdic)
    (prec : Array Entry) (nPrimes : Nat) (list1 : Array Cand) (used : Array Bool) (n1 : Nat) :
    Id FirstStage := do
  let mut cost1 := 0.0
  let mut setup1 := 0.0
  let mut rho1 := if two.use2 then two.density2 else 1.0
  let mut used := used
  for n in [0:nPrimes] do used := used.set! n false
  for k in [0:n1] do
    let n := list1[k]!.n
    used := used.set! n true
    cost1 := cost1 + (s.w * c.and * (1.0 + Float.ofNat prec[n]!.p / c.size) + s.passx)
    setup1 := setup1 + (t.tabcost[n]! + t.initcost[n]!)
    rho1 := rho1 * prec[n]!.r.toFloat
  return { cost1, setup1, rho1, used }

/-- The ranking of the second stage, `list2`: for each candidate of `list1` in its order whose prime
the first stage does not take (`used`), the candidate with the value
`-log r / (W s1 TEST2 + (tabcost + initcost) / rows)`, the reduction per cycle of the tests of the
`W s1` words per row that survive the first stage and of its set-up per row, for the terms `s` of
the mode and `t` of the primes and the constants `c`; sorted by value by `qsort` with
`compare_cands`.

C: `j-points.c:993`, `j-points.c:1004-1013`

Deviation: an array of the candidates for the array `list2`, whose size is their count `ne2`; the
sort of glibc as `JPoints.qsort`. -/
def choosePrimesModeList2 (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (list1 : Array Cand)
    (used : Array Bool) (s1 : Float) : Id (Array Cand) := do
  let mut list2 := #[]
  for k in [0:list1.size] do
    let n := list1[k]!.n
    if !used[n]! then
      list2 := list2.push
        { n, v := t.logr[n]! / (s.w * s1 * c.test2 + (t.tabcost[n]! + t.initcost[n]!) / s.rows) }
  return qsort compareCands list2 list2.size

/-- The range `[n2lo, n2hi]` of the number of the primes of the first two stages, for `n1` primes
of the first stage, `ne2` candidates of the second and the pins `pin2` and `pin3` (`sieve_primes2`
and `sieve_primes3`), each `-1` when not pinned: `[n1, n1 + ne2]`, its upper end at most `pin3`
when it is pinned, and the one number `min(pin2, n2hi)` when `pin2` is pinned (at least `n1`, which
is at most a pinned `pin2` and `pin3`).

C: `j-points.c:1014-1018`

Deviation: integers for the `long`s, the ends returned as natural numbers, which they are. -/
def choosePrimesModeRange2 (n1 ne2 : Nat) (pin2 pin3 : Int) : Nat × Nat :=
  let hi : Int := n1 + ne2
  let hi := if pin3 ≥ 0 ∧ hi > pin3 then pin3 else hi
  let (lo, hi) := if pin2 ≥ 0 then
      let v := if pin2 < hi then pin2 else hi
      (v, v)
    else (n1, hi)
  (lo.toNat, hi.toNat)

/-- The locals of the second stage in `choose_primes_mode`, for the numbers `n1` and `n2`: the cost
per row of the tests of the words that survive the first stage (`cost2`), the set-up of the first
two stages (`setup2`), the density of the triples that survive them (`rho2`), and the fraction of
the rows with a bit left after them (`rowbit`).

It models no C code of its own: `JPoints.choosePrimesModeSecond` computes the locals. -/
structure SecondStage where
  /-- `cost2`: the cost per row of the second stage. -/
  cost2 : Float
  /-- `setup2`: the set-up of the first two stages. -/
  setup2 : Float
  /-- `rho2`: the density of the triples that survive the first two stages. -/
  rho2 : Float
  /-- `rowbit`: the fraction of the rows with a bit left after the first two stages. -/
  rowbit : Float

/-- The second stage of the `n2 - n1` best candidates of `list2`, after the first stage `st` with
the fraction `s1` of the words that survive it, for the terms `s` of the mode and `t` of the primes
and the constants `c`: the cost per row of finding the words that the first stage leaves (`W w
WORD`, none in the tube) and of testing them for each prime until they die (`W w TEST2` for the
fraction `w` that survives the primes before, `W TTEST` in the tube, where every word is tested),
the set-up, the density `rho2` that survives, the fraction `w = 1 - (1 - rho2) ^ 64` of the words,
and the fraction `rowbit = 1 - (1 - rho2) ^ bits` of the rows with a bit left.

C: `j-points.c:1020`, `j-points.c:1023-1031`

Deviation: `Float.pow` for `pow`; the `Float` of the bits of the rate. -/
def choosePrimesModeSecond (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (prec : Array Entry)
    (st : FirstStage) (s1 : Float) (list2 : Array Cand) (n1 n2 : Nat) : Id SecondStage := do
  let mut setup2 := st.setup1
  let mut rho2 := st.rho1
  let mut w := s1
  let mut cost2 := if s.tube then 0.0 else s.w * w * c.word
  for k in [0:n2 - n1] do
    let n := list2[k]!.n
    cost2 := cost2 + (if s.tube then s.w * c.ttest else s.w * w * c.test2)
    setup2 := setup2 + (t.tabcost[n]! + t.initcost[n]!)
    rho2 := rho2 * prec[n]!.r.toFloat
    w := 1.0 - Float.pow (1.0 - rho2) (Float.ofNat longLength)
  let rowbit := 1.0 - Float.pow (1.0 - rho2) s.bits
  return { cost2, setup2, rho2, rowbit }

/-- The ranking of the third stage, `list3`: for each of the first `nPrimes` records of `prec`, in
their order, whose prime neither the first stage (`used`) nor the second (the first `k2 = n2 - n1`
candidates of `list2`) takes, the candidate with the value
`-log r / (bits rho2 TEST3 + rowbit ROW3 + initcost / rows)`, the reduction per cycle of the tests
of the bits per row that survive the first two stages, of the data of the third stage of the rows
with a bit left, and of the set-up of its exact table per row, for the terms `s` of the mode and `t`
of the primes and the constants `c`; sorted by value by `qsort` with `compare_cands`.

C: `j-points.c:1021`, `j-points.c:1033-1044`

Deviation: an array of the candidates for the array `list3`, whose size is their count `ne3`; a
Boolean for the `int` flag `in2`; the sort of glibc as `JPoints.qsort`. -/
def choosePrimesModeList3 (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (nPrimes : Nat)
    (used : Array Bool) (list2 : Array Cand) (k2 : Nat) (rho2 rowbit : Float) :
    Id (Array Cand) := do
  let mut list3 := #[]
  for n in [0:nPrimes] do
    let mut in2 := false
    for k in [0:k2] do
      if list2[k]!.n == n then in2 := true
    if !used[n]! && !in2 then
      list3 := list3.push
        { n, v := t.logr[n]! /
            (s.bits * rho2 * c.test3 + rowbit * c.row3 + t.initcost[n]! / s.rows) }
  return qsort compareCands list3 list3.size

/-- The range `[n3lo, n3hi]` of the number of the primes of all three stages, for `n2` primes of
the first two stages, `ne3` candidates of the third and the pin `pin3` (`sieve_primes3`), `-1` when
not pinned: `[n2, n2 + ne3]`, and the one number `min(pin3, n2 + ne3)` when `pin3` is pinned (at
least `n2`, which is at most a pinned `pin3`).

C: `j-points.c:1045-1048`

Deviation: integers for the `long`s, the ends returned as natural numbers, which they are. -/
def choosePrimesModeRange3 (n2 ne3 : Nat) (pin3 : Int) : Nat × Nat :=
  let hi : Int := n2 + ne3
  let (lo, hi) := if pin3 ≥ 0 then
      let v := if pin3 < hi then pin3 else hi
      (v, v)
    else (n2, hi)
  (lo.toNat, hi.toNat)

/-! ### The loops over the numbers of primes -/

/-- The cheapest choice of `choose_primes_mode` so far: its cost (`best`, `-1` before the first),
its numbers of primes (`b1`, `b2`, `b3`), and the indices in `prec` of the primes of its first,
second and third stage (`best1`, `best2`, `best3`). The defaults are the initial values: the
arrays, which the C code leaves uninitialized, start as zeros, and only the entries that the C code
writes are read.

C: `j-points.c:933`, `j-points.c:939`, `j-points.c:941`

Deviation: a structure for the locals; a `Float` for the double `best`; natural numbers for the
`long` numbers and indices; arrays of `JPoints.numPrimes` entries for the local arrays. -/
structure ModeBest where
  /-- `best`: the cost of the cheapest choice so far, `-1` before the first. -/
  best : Float := -1.0
  /-- `b1`: the number of the primes of its first stage. -/
  b1 : Nat := 0
  /-- `b2`: the number of the primes of its first two stages. -/
  b2 : Nat := 0
  /-- `b3`: the number of the primes of its three stages. -/
  b3 : Nat := 0
  /-- `best1`: the indices in `prec` of the primes of its first stage. -/
  best1 : Array Nat := .replicate numPrimes 0
  /-- `best2`: the indices in `prec` of the primes of its second stage. -/
  best2 : Array Nat := .replicate numPrimes 0
  /-- `best3`: the indices in `prec` of the primes of its third stage. -/
  best3 : Array Nat := .replicate numPrimes 0

/-- The cheapest choice `b` replaced by the choice of the cost `total` with the numbers `n1`, `n2`
and `n3`: the first `n1` candidates of `list1`, the first `n2 - n1` of `list2` and the first
`n3 - n2` of `list3`, by their indices in `prec`, copied into the arrays of the choice.

C: `j-points.c:1057-1060`

Deviation: the cheapest choice taken and returned, for the locals of `choose_primes_mode` that the C
code writes; natural numbers for the `long` numbers and indices; a `Float` for the double
`total`. -/
def choosePrimesModeKeep (b : ModeBest) (total : Float) (list1 list2 list3 : Array Cand)
    (n1 n2 n3 : Nat) : Id ModeBest := do
  let mut best1 := b.best1
  let mut best2 := b.best2
  let mut best3 := b.best3
  for k in [0:n1] do best1 := best1.set! k list1[k]!.n
  for k in [0:n2 - n1] do best2 := best2.set! k list2[k]!.n
  for k in [0:n3 - n2] do best3 := best3.set! k list3[k]!.n
  return { best := total, b1 := n1, b2 := n2, b3 := n3, best1, best2, best3 }

/-- The loop over the number `n3` of the primes of all three stages, from `n2` to `n3hi`, for the
stages `st1` and `st2`, the terms `s` of the mode and `t` of the primes and the constants `c`: for
each `n3 ≥ n3lo` the cost of the run, `rows` times the cost per row (the fixed cost, the first
three stages, the data of the `n3 - n2` primes of the third stage for the rows with a bit left,
`bits rho EXACT` for the exact check of the bits that survive, `rho` the density after the `n3 - n2`
best candidates of `list3`) plus the set-up, kept when it is the first or is below the cheapest so
far (`JPoints.choosePrimesModeKeep`), so that on a tie the earlier choice stays; then the next
candidate of `list3` added, its tests `bits rho TEST3` and the set-up of its exact table.

C: `j-points.c:1049-1056`, `j-points.c:1061-1070`

Deviation: the `Float` of the bits of the rate. -/
def choosePrimesModeLoop3 (s : ModeShape) (t : PrimeTerms) (c : Cli.Costs) (prec : Array Entry)
    (st1 : FirstStage) (st2 : SecondStage) (list1 list2 list3 : Array Cand)
    (n1 n2 n3lo n3hi : Nat) (b : ModeBest) : Id ModeBest := do
  let mut cost3 := s.bits * st2.rho2 * c.bit
  let mut setup3 := st2.setup2
  let mut rho := st2.rho2
  let mut b := b
  for n3 in [n2:n3hi + 1] do
    if n3 ≥ n3lo then
      let total := s.rows * (s.fixed + st1.cost1 + st2.cost2 + cost3
          + st2.rowbit * Float.ofNat (n3 - n2) * c.row3 + s.bits * rho * c.exact) + setup3
      if b.best < 0.0 ∨ total < b.best then
        b ← choosePrimesModeKeep b total list1 list2 list3 n1 n2 n3
    if n3 < n3hi then
      let n := list3[n3 - n2]!.n
      cost3 := cost3 + s.bits * rho * c.test3
      setup3 := setup3 + t.initcost[n]!
      rho := rho * prec[n]!.r.toFloat
  return b

/-- The loop over the number `n2` of the primes of the first two stages, from `n2lo` to `n2hi`, for
the first stage `st1` of `n1` primes with the fraction `s1` of the words that survive it, the
rankings `list1` and `list2`, the globals `g`, the terms `s` of the mode and `t` of the primes and
the records `prec`: the second stage (`JPoints.choosePrimesModeSecond`), the ranking of the third
(`JPoints.choosePrimesModeList3`), its range (`JPoints.choosePrimesModeRange3`) and the loop over
`n3` (`JPoints.choosePrimesModeLoop3`), from the cheapest choice `b` so far.

C: `j-points.c:1019`, `j-points.c:1021`, `j-points.c:1071`

Deviation: the pin `sieve_primes3` read from `JPoints.Cli.Input`. -/
def choosePrimesModeLoop2 (g : ChoiceGlobals) (s : ModeShape) (t : PrimeTerms)
    (prec : Array Entry) (st1 : FirstStage) (s1 : Float) (list1 list2 : Array Cand)
    (n1 n2lo n2hi : Nat) (b : ModeBest) : Id ModeBest := do
  let c := g.input.costs
  let mut b := b
  for n2 in [n2lo:n2hi + 1] do
    let st2 ← choosePrimesModeSecond s t c prec st1 s1 list2 n1 n2
    let list3 ← choosePrimesModeList3 s t c g.input.numPrimes.toNat st1.used list2 (n2 - n1)
      st2.rho2 st2.rowbit
    let (n3lo, n3hi) := choosePrimesModeRange3 n2 list3.size g.input.sievePrimes3
    b ← choosePrimesModeLoop3 s t c prec st1 st2 list1 list2 list3 n1 n2 n3lo n3hi b
  return b

/-- The loop over the number `n1` of the primes of the first stage, from `n1lo` to `n1hi`, for the
ranking `list1`, the globals `g`, the terms `s` of the mode and `t` of the primes and the records
`prec`: the first stage (`JPoints.choosePrimesModeFirst`), the fraction `s1 = 1 - (1 - rho1) ^ 64`
of the words that survive it, the ranking of the second stage (`JPoints.choosePrimesModeList2`),
its range (`JPoints.choosePrimesModeRange2`) and the loop over `n2`
(`JPoints.choosePrimesModeLoop2`), from the cheapest choice `b` so far; the flags `used` of the
first stage, which the C code declares here, start as `false`.

C: `j-points.c:944`, `j-points.c:991`, `j-points.c:993`, `j-points.c:1002`, `j-points.c:1072`

Deviation: an array of `JPoints.numPrimes` Booleans for the array of `int` flags `used`, which the
C code leaves uninitialized (the first stage clears the entries it reads); `Float.pow` for `pow`;
the pins `sieve_primes2` and `sieve_primes3` read from `JPoints.Cli.Input`. -/
def choosePrimesModeLoop1 (g : ChoiceGlobals) (s : ModeShape) (t : PrimeTerms)
    (prec : Array Entry) (list1 : Array Cand) (n1lo n1hi : Nat) (b : ModeBest) : Id ModeBest := do
  let c := g.input.costs
  let mut used := Array.replicate numPrimes false
  let mut b := b
  for n1 in [n1lo:n1hi + 1] do
    let st1 ← choosePrimesModeFirst s t c g.two prec g.input.numPrimes.toNat list1 used n1
    used := st1.used
    let s1 := 1.0 - Float.pow (1.0 - st1.rho1) (Float.ofNat longLength)
    let list2 ← choosePrimesModeList2 s t c list1 used s1
    let (n2lo, n2hi) :=
      choosePrimesModeRange2 n1 list2.size g.input.sievePrimes2 g.input.sievePrimes3
    b ← choosePrimesModeLoop2 g s t prec st1 s1 list1 list2 n1 n2lo n2hi b
  return b

/-! ### The choice -/

/-- `choose_primes_mode`: the cost model of the mode `mode` (`0` the box, `1` the tube, `2` the
region) with the cut `cut` of the words of the tube, for the globals `g` and the records `prec`,
sorted by rate: the terms that the mode fixes (`JPoints.choosePrimesModeShape`) and that the primes
give (`JPoints.choosePrimesModeTerms`), the ranking of the first stage
(`JPoints.choosePrimesModeList1`) and its range (`JPoints.choosePrimesModeRange1`), and the loop
over `n1` (`JPoints.choosePrimesModeLoop1`); the cheapest choice is written into the plan `plan`:
its numbers of primes, and the indices in `prime[]` of the primes of its three stages, stage by
stage, at the start of `pnn`. The cost of the cheapest choice, and the plan.

C: `j-points.c:928-929`, `j-points.c:931`, `j-points.c:932`, `j-points.c:1073-1078`

Deviation: the plan taken and returned, for the globals that the C code writes, its mode and cut
unchanged; the pins `sieve_primes1`, `sieve_primes2` and `sieve_primes3` read from
`JPoints.Cli.Input`, which holds the values that `choose_primes` sets them to before the call; a
natural number for the `int` `mode` and a Boolean for the `int` flag `cut`. -/
def choosePrimesMode (mode : Nat) (cut : Bool) (g : ChoiceGlobals) (prec : Array Entry)
    (plan : Plan) : Id (Float × Plan) := do
  let nPrimes := g.input.numPrimes.toNat
  let s := choosePrimesModeShape mode cut g
  let t ← choosePrimesModeTerms g.input.costs prec nPrimes
  let list1 ← choosePrimesModeList1 s t g.input.costs prec nPrimes
  let (n1lo, n1hi) :=
    choosePrimesModeRange1 list1.size s.pin1 g.input.sievePrimes2 g.input.sievePrimes3
  let b ← choosePrimesModeLoop1 g s t prec list1 n1lo n1hi {}
  let mut pnn := plan.pnn
  for k in [0:b.b1] do pnn := pnn.set! k prec[b.best1[k]!]!.n
  for k in [0:b.b2 - b.b1] do pnn := pnn.set! (b.b1 + k) prec[b.best2[k]!]!.n
  for k in [0:b.b3 - b.b2] do pnn := pnn.set! (b.b2 + k) prec[b.best3[k]!]!.n
  return (b.best,
    { plan with sievePrimes1 := b.b1, sievePrimes2 := b.b2, sievePrimes3 := b.b3, pnn })

/-- `choose_primes`: the modes of the run priced by `JPoints.choosePrimesMode`, in this order: the
box (mode `0`), the region (mode `2`) and, when the fourth coordinate is bounded (`dbounded`), the
tube (mode `1`) without and with the cut of its words to the real region; the first one, and then
each one cheaper than the cheapest before, taken with its numbers of primes and its primes, so that
on a tie the earlier one stays. The plan with the mode, the cut, the numbers and the primes of the
cheapest; `pnn` beyond them as the last mode priced leaves it.

C: `j-points.c:907-926`

Deviation: the plan taken and returned, for the globals; the pins `pin1`, `pin2` and `pin3`, to
which the C code sets `sieve_primes1`, `sieve_primes2` and `sieve_primes3` back before each mode,
read by `JPoints.choosePrimesMode` from `JPoints.Cli.Input`, which holds them; natural numbers for
the `long` numbers and indices and the `int` modes, Booleans for the `int` cuts; `Float`s for the
doubles `best` and `cost`; an array of `JPoints.numPrimes` entries for the local array `pn`, which
starts as zeros (the C code leaves it uninitialized, and reads only the entries it writes). -/
def choosePrimes (g : ChoiceGlobals) (prec : Array Entry) (plan : Plan) : Id Plan := do
  let (modes, cuts) : Array Nat × Array Bool := (#[0, 2, 1, 1], #[false, false, false, true])
  let mut plan := plan
  let mut best : Float := -1.0
  let mut (b1, b2, b3) := (0, 0, 0)
  let mut pn := Array.replicate numPrimes 0
  for k in [0:if g.input.dbounded then 4 else 2] do
    let (cost, plan') ← choosePrimesMode modes[k]! cuts[k]! g prec plan
    plan := plan'
    if best < 0.0 ∨ cost < best then
      best := cost
      plan := { plan with sieveMode := modes[k]!, tubeCut := cuts[k]! }
      (b1, b2, b3) := (plan.sievePrimes1, plan.sievePrimes2, plan.sievePrimes3)
      for n in [0:b3] do pn := pn.set! n plan.pnn[n]!
  let mut pnn := plan.pnn
  for n in [0:b3] do pnn := pnn.set! n pn[n]!
  return { plan with sievePrimes1 := b1, sievePrimes2 := b2, sievePrimes3 := b3, pnn }

/-! ### The messages -/

/-- The lines of message 4 of `message` on the mode of the sieve, for the plan `plan` and the
statistics `s` of the analysis: in the tube, the cut to the real region if there is one, and the
words per row and the cells of the analysis per row; in the region, its words per row, its ranges
and the fraction of the rows that meet it; nothing in the box. The doubles are printed by `%.2f` and
`%.3f` (`JPoints.Double.printFixed`).

C: `j-points.c:2327-2337`

Deviation: the text returned, for the output on `stdout`; the doubles by `JPoints.Double.ofFloat`,
which takes a NaN to `0x7ff8000000000000` and would print `nan` for `-nan` (the statistics are
quotients of sums of counts by a positive number of rows, or `1`, never NaNs). -/
def message4Mode (plan : Plan) (s : TubeStats) : String :=
  let f2 (x : Float) := Double.printFixed 2 (.ofFloat x)
  let words := if plan.tubeCut then s.tubeWordsCut else s.tubeWords
  (if plan.sieveMode == 1 then
    "Sieving in the tube of the bound on the fourth coordinate" ++
      (if plan.tubeCut then ", cut to the real region" else "") ++ ":\n" ++
      s!"about {f2 words} words per row, {f2 s.tubeCells} cells of the analysis per row.\n"
  else "") ++
  if plan.sieveMode == 2 then
    "Sieving the real region by passes over its ranges of words:\n" ++
      s!"about {f2 s.regWords} words per row in {f2 s.regRanges} ranges, " ++
      s!"{Double.printFixed 3 (.ofFloat s.regRows)} of the rows.\n"
  else ""

/-- The line of message 4 of `message` on the constants of the cost model that `-c` set, for the
globals `input` of the command line: their names and values, in the order of `cost_names`, the
values printed by `%g` (`JPoints.Double.printGeneral`).

C: `j-points.c:2348-2356`

Deviation: the text returned, for the output on `stdout`; a natural number for the `size_t`
index; the values by `JPoints.Double.ofFloat`, which takes a NaN to `0x7ff8000000000000` and would
print `nan` for `-nan` (`-c` sets only positive normal values, never NaNs). -/
def message4Costs (input : Cli.Input) : Id String := do
  let mut out := ""
  if input.costsSet then
    out := out ++ "Constants of the cost model set by -c:"
    for k in [0:Cli.numCosts] do
      if input.costSet[k]! then
        let e := Cli.costNames[k]!
        out := out ++ s!" {e.name}={Double.printGeneral 6 (.ofFloat (e.value input.costs))}"
    out := out ++ "\n"
  return out

/-- Message 4 of `message`, the text that it prints for the plan `plan` and the globals `g`: the
mode of the sieve (`JPoints.message4Mode`); when the condition at 2 is used, the fraction of the
classes modulo `64` that it admits and of the rows that it empties, printed by `%.3f`
(`JPoints.Double.printFixed`); the numbers of the primes of the stages; and the constants of the
cost model that `-c` set (`JPoints.message4Costs`).

C: `j-points.c:2338-2347`, `j-points.c:2357`

Deviation: the text returned, for the output on `stdout`; the fractions by
`JPoints.Double.ofFloat`, which takes a NaN to `0x7ff8000000000000` and would print `nan` for
`-nan` (they are quotients by positive counts, never NaNs). -/
def message4 (g : ChoiceGlobals) (plan : Plan) : Id String := do
  let f3 (x : Float) := Double.printFixed 3 (.ofFloat x)
  let two := if g.two.use2 then
      s!"The condition at 2 admits {f3 g.two.density2} of the classes mod 64 and " ++
        s!"empties {f3 g.two.empty2} of the rows.\n"
    else ""
  return message4Mode plan g.stats ++ two ++
    s!"{plan.sievePrimes1} primes used for the first stage of sieving,\n" ++
    s!"{plan.sievePrimes2} primes used for the first two stages together,\n" ++
    s!"{plan.sievePrimes3} primes used for all three stages together.\n" ++
    (← message4Costs g.input)

/-- Message 7 of `message`, the text that it prints for the plan `plan`: the primes of the first,
second and third stage, each list after its title and separated by `, `.

C: `j-points.c:2363-2381`

Deviation: the text returned, for the output on `stdout`; the index `i` that the three loops share
as their bounds: each loop starts where the one before ended, at the larger of the numbers before,
which is the number of the stages before it for a plan of `JPoints.choosePrimes`. -/
def message7 (plan : Plan) : Id String := do
  let sp1 := plan.sievePrimes1
  let sp2 := plan.sievePrimes2
  let sp3 := plan.sievePrimes3
  let mut out := "Sieving primes:\n First stage: "
  for i in [0:sp1] do
    out := out ++ toString primeTable[plan.pnn[i]!]!
    if i < sp1 - 1 then out := out ++ ", "
  out := out ++ "\n Second stage: "
  for i in [sp1:sp2] do
    out := out ++ toString primeTable[plan.pnn[i]!]!
    if i < sp2 - 1 then out := out ++ ", "
  out := out ++ "\n Third stage: "
  for i in [max sp1 sp2:sp3] do
    out := out ++ toString primeTable[plan.pnn[i]!]!
    if i < sp3 - 1 then out := out ++ ", "
  return out ++ "\n"

/-- Message 8 of `message`, the text that it prints for the records `prec`, sorted by rate, of the
`nPrimes` primes considered (`num_primes`) and the plan `plan`: the prime and the rate of the first
record (`Min`), for each stage the prime and the rate of its last prime, which a linear search
finds in `prec` (`Cut1`, `Cut2`, `Cut3`, one label for an index where stages end together, the
first), and the prime and the rate of the last record (`Max`), the rates printed by `%f`
(`JPoints.Double.printFixed`).

C: `j-points.c:2382-2401`

Deviation: the text returned, for the output on `stdout`; natural numbers for the `long` indices;
the linear search for the record of a prime bounded by the size of `prec`, which holds it (its
records hold the indices of all primes considered), where the C code searches without a bound. -/
def message8 (prec : Array Entry) (nPrimes : Nat) (plan : Plan) : Id String := do
  let sp1 := plan.sievePrimes1
  let sp2 := plan.sievePrimes2
  let sp3 := plan.sievePrimes3
  let mut out := s!"Probabilities: Min({prec[0]!.p}) = {Double.printFixed 6 prec[0]!.r}"
  for i in [0:nPrimes] do
    if i + 1 == sp1 || i + 1 == sp2 || i + 1 == sp3 then
      let mut j := 0
      while j < prec.size && prec[j]!.n != plan.pnn[i]! do j := j + 1
      let label := if i + 1 == sp1 then 1 else if i + 1 == sp2 then 2 else 3
      out := out ++ s!", Cut{label}({prec[j]!.p}) = {Double.printFixed 6 prec[j]!.r}"
  let e := prec[nPrimes - 1]!
  return out ++ s!", Max({e.p}) = {Double.printFixed 6 e.r}\n\n"

/-! ### The end of `init_fmodpsquare` -/

/-- The tables of the primes chosen, as the end of `init_fmodpsquare` fills them, for the tables `t`
and `ct` and the degree `degree` of the curve searched: for each of the first `sieve_primes3`
primes of the plan `plan`, the rows of the prime in the table of the third stage filled by
`JPoints.initTable` unless `tabled` holds at its index in `prime[]`, which is then set.

C: `j-points.c:863-864`

Deviation: the tables of the curve and the flags taken and returned, for the globals and the local
array; a natural number for the index `n`; the count that `init_table` returns dropped, as the C
code drops it. -/
def initFmodpsquareTables (t : Tables) (ct : CurveTables) (degree : Nat) (plan : Plan)
    (tabled : Array Bool) : Id (CurveTables × Array Bool) := do
  let mut ct := ct
  let mut tabled := tabled
  for n in [0:plan.sievePrimes3] do
    if !tabled[plan.pnn[n]!]! then
      (ct, _) ← initTable t ct degree plan.pnn[n]!
      tabled := tabled.set! plan.pnn[n]! true
  return (ct, tabled)

/-- `init_fmodpsquare`, for the tables `t`, the globals `g` (of which the curve searched and the
condition at 2), the tables of the curve `ct`, the records `prec` and the plan `plan`: the
coefficients modulo the primes, the tables of the squares and the rates of the primes considered,
with `prec` sorted by rate (`JPoints.initFmodpsquareRates`); the choice of the primes
(`JPoints.choosePrimes`); when there are no sieving primes, the box and the condition at 2 not used;
the tables of the primes chosen (`JPoints.initFmodpsquareTables`); and unless `quiet`, message 4
(`JPoints.message4`) and, when there are sieving primes, messages 7 and 8 (`JPoints.message7`,
`JPoints.message8`). The tables of the curve, the records, the plan, the globals of the condition
at 2 and the text printed.

C: `j-points.c:804-807`, `j-points.c:858`, `j-points.c:861`, `j-points.c:865-871`

Deviation: the tables, the records, the plan and the globals of the condition at 2 taken and
returned, for the globals, and the text returned, for the output on `stdout`; `num_primes`, which
`read_input` leaves in `[1, 53]`, as a natural number; the messages as their texts, where the C
code calls `message`, which prints them and flushes `stdout`. -/
def initFmodpsquare (t : Tables) (g : ChoiceGlobals) (ct : CurveTables) (prec : Array Entry)
    (plan : Plan) : Id (CurveTables × Array Entry × Plan × TwoAdic × String) := do
  let nPrimes := g.input.numPrimes.toNat
  let (ct, r) ← initFmodpsquareRates t g.curve.coeffs g.curve.degree nPrimes ct prec
  let mut plan ← choosePrimes g r.prec plan
  let mut two := g.two
  if plan.sievePrimes3 == 0 then
    plan := { plan with sieveMode := 0 }
    two := { two with use2 := false }
  let (ct, _) ← initFmodpsquareTables t ct g.curve.degree plan r.tabled
  let mut out := ""
  if !g.input.quiet then
    out := out ++ (← message4 { g with two } plan)
    if plan.sievePrimes3 > 0 then
      out := out ++ (← message7 plan) ++ (← message8 r.prec nPrimes plan)
  return (ct, r.prec, plan, two, out)

/-! ### Examples

The values of the C code at the pin: of `compare_cands` and of `qsort` with it from a test program
with a copy of `compare_cands`; and of the choice from a copy of `j-points` that prints, after
`choose_primes`, the inputs of the choice that the program computes before it (the statistics of
`tube_sample`, `num_neg`, the condition at 2) with the plan and the records, after
the tables of the primes chosen their flags and a hash of the table of the third stage (as in
`JPoints.Model.Rates`), for each mode the terms it fixes, the terms of the primes, the range of the
first stage and the cost and the plan of the mode, and stops after messages 4, 7 and 8, which are
those that `j-points` prints. No example depends on the values of `log` and `pow`, which differ
between processors: the costs and the plans are compared for a curve whose rates at the primes
considered are all `1`, where the cost model meets `log` only at `1` and `pow` only at the base
`+0` with a positive exponent, whose values IEEE 754 fixes (`log 1 = +0`, `pow(+0, y) = +0`), and
otherwise the parts of the choice that need neither, the messages for the plans that the C code
made, and the tables for them. -/

-- `+∞` and the NaN of the C library's `NAN`, as `Float`s.
private def inf : Float := .ofBits 0x7ff0000000000000
private def nan : Float := .ofBits 0x7ff8000000000000

-- The candidates with the values `vs`, each at the index of its position.
private def cands (vs : List Float) : Array Cand := vs.toArray.zipIdx.map fun (v, n) ↦ { n, v }

#guard [(1.0, 0.5, -1), (0.5, 1.0, 1), (0.25, 0.25, 0), (0.0, -0.0, 0), (inf, 1.0, -1),
    (1.0, inf, 1), (inf, inf, 0), (-inf, -inf, 0), (nan, 1.0, 0), (1.0, nan, 0), (nan, nan, 0),
    (.ofBits 1, 0.0, -1), (0.0, .ofBits 1, 1), (-inf, inf, 1)].all fun (a, b, c) ↦
  compareCands { v := a } { v := b } == c

-- `qsort` with `compare_cands`, the largest value first, on values with NaNs and infinities, where
-- `∞ - ∞` is a NaN, and on both zeros and subnormals, as glibc 2.41 sorts them.
#guard [([1.0, inf, 0.0, inf, -inf, nan, 2.0, 0.5, nan, inf, 1.0],
      [1, 3, 0, 2, 4, 5, 6, 7, 8, 9, 10]),
    ([0.3, nan, 0.7, 0.1, nan, 0.9, 0.2, 0.5, -0.0, 0.0, 0.4], [5, 2, 7, 10, 0, 1, 6, 3, 4, 8, 9]),
    ([-0.0, 0.0, -0.0, 0.0, .ofBits 1, -.ofBits 1], [4, 0, 1, 2, 3, 5])].all fun (vs, ns) ↦
  (qsort compareCands (cands vs) vs.length).toList.map (·.n) == ns

-- The globals of the command line `args` (the words after the name of the program) of a curve that
-- the search takes as it is given, with the statistics `st` of `tube_sample`, `num_neg` and the
-- condition at 2 (`use2`, `density2` and `empty2`) by their bits, as the copy of the C code prints
-- them.
private def globals (args : List String) (st : List UInt64) (numNeg : Nat) (use2 : Bool)
    (d2 e2 : UInt64) : ChoiceGlobals :=
  let input := match (Cli.readInput args.toArray).run with
    | .ok i => i
    | .error _ => {}
  let f (k : Nat) : Float := .ofBits (st.getD k 0)
  let curve : SearchCurve :=
    { coeffs := input.coeffs, degree := input.degree.toNat, reversed := false, negated := false }
  { input, curve, numNeg, stats := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6⟩,
    two := { TwoAdic.initial with use2, density2 := .ofBits d2, empty2 := .ofBits e2 } }

-- The plan of the mode `mode`, the cut `cut`, the numbers `sp1`, `sp2` and `sp3` and the primes
-- `pnn`.
private def plan (mode : Nat) (cut : Bool) (sp1 sp2 sp3 : Nat) (pnn : List Nat) : Plan :=
  { pnn := pnn.toArray ++ .replicate (numPrimes + 1 - pnn.length) 0, sievePrimes1 := sp1,
    sievePrimes2 := sp2, sievePrimes3 := sp3, sieveMode := mode, tubeCut := cut }

-- The records of `prec` with the indices of their primes and their rates by their bits.
private def precOf (es : List (Nat × UInt64)) : Array Entry :=
  es.toArray.map (fun (n, r) ↦ { p := primeTable[n]!, r := ⟨r⟩, n }) ++
    .replicate (numPrimes - es.length) {}

-- The hash of the examples over the entries `vs`.
private def hash (vs : Array UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The curve `y² = (x³ - x + 1)² + 30030` at the height bound `300` with its first five primes
-- considered (`-p 5`), the primes up to `13`, modulo each of which `f` is a square, so that every
-- rate is `1`, under options that pin the numbers of primes, leave the fourth coordinate unbounded
-- or bound it apart and set constants of the cost model: the plan and the text of
-- `init_fmodpsquare`, and for each mode its cost by its bits and its plan.
#guard
  let t := (initMain Tables.initial).run
  let cases : List (List String × List UInt64 × (Nat × Bool × Nat × Nat × Nat × List Nat) ×
      String × List (Nat × Bool × UInt64 × Nat × Nat × Nat × List Nat)) := [
    ([],
      [0x40188e8145b9c3f2, 0x40188e8145b9c3f2, 0x3fd00824a4e60b32, 0x3fec6a8a1817127e,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 0, 0, 0, []),
      "0 primes used for the first stage of sieving,\n" ++
      "0 primes used for the first two stages together,\n" ++
      "0 primes used for all three stages together.\n",
      [(0, false, 0x4241f1af79a60000, 0, 0, 0, []), (2, false, 0x4241f20248fc0000, 0, 0, 0, []),
       (1, false, 0x423604ace05ed4bd, 0, 0, 0, []), (1, true, 0x4236055875a81fe5, 0, 0, 0, [])]),
    (["-n", "2", "-M", "3", "-N", "5"],
      [0x40188e8145b9c3f2, 0x40188e8145b9c3f2, 0x3fd00824a4e60b32, 0x3fec6a8a1817127e,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (1, false, 0, 3, 5, [0, 1, 2, 3, 4]),
      "Sieving in the tube of the bound on the fourth coordinate:\n" ++
      "about 6.14 words per row, 0.25 cells of the analysis per row.\n" ++
      "0 primes used for the first stage of sieving,\n" ++
      "3 primes used for the first two stages together,\n" ++
      "5 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: \n" ++
      " Second stage: 3, 5, 7\n" ++
      " Third stage: 11, 13\n" ++
      "Probabilities: Min(3) = 1.000000, Cut2(7) = 1.000000, Cut3(13) = 1.000000, " ++
      "Max(13) = 1.000000\n" ++
      "\n",
      [(0, false, 0x424259ffe3115555, 2, 3, 5, [0, 1, 2, 3, 4]),
       (2, false, 0x42425a607fa05555, 2, 3, 5, [0, 1, 2, 3, 4]),
       (1, false, 0x423685080cb3231e, 0, 3, 5, [0, 1, 2, 3, 4]),
       (1, true, 0x423685b3a1fc6e46, 0, 3, 5, [0, 1, 2, 3, 4])]),
    (["-N", "4"],
      [0x40188e8145b9c3f2, 0x40188e8145b9c3f2, 0x3fd00824a4e60b32, 0x3fec6a8a1817127e,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (1, false, 0, 4, 4, [0, 1, 2, 3]),
      "Sieving in the tube of the bound on the fourth coordinate:\n" ++
      "about 6.14 words per row, 0.25 cells of the analysis per row.\n" ++
      "0 primes used for the first stage of sieving,\n" ++
      "4 primes used for the first two stages together,\n" ++
      "4 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: \n" ++
      " Second stage: 3, 5, 7, 11\n" ++
      " Third stage: \n" ++
      "Probabilities: Min(3) = 1.000000, Cut2(11) = 1.000000, Max(13) = 1.000000\n" ++
      "\n",
      [(0, false, 0x4241f1d2c1773555, 4, 4, 4, [0, 1, 2, 3]),
       (2, false, 0x4241f2412b3f3555, 4, 4, 4, [0, 1, 2, 3]),
       (1, false, 0x42360534d91d8bf6, 0, 4, 4, [0, 1, 2, 3]),
       (1, true, 0x423605e06e66d71d, 0, 4, 4, [0, 1, 2, 3])]),
    (["-a"],
      [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 0, 0, 0, []),
      "0 primes used for the first stage of sieving,\n" ++
      "0 primes used for the first two stages together,\n" ++
      "0 primes used for all three stages together.\n",
      [(0, false, 0x4241f1af79a60000, 0, 0, 0, []), (2, false, 0x4241f20248fc0000, 0, 0, 0, [])]),
    (["-w", "50"],
      [0x401122704eb78f5a, 0x401122704eb78f5a, 0x3fc9f4cd9d43b09b, 0x3fe7127de11fb96d,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 0, 0, 0, []),
      "0 primes used for the first stage of sieving,\n" ++
      "0 primes used for the first two stages together,\n" ++
      "0 primes used for all three stages together.\n",
      [(0, false, 0x4241f1af79a60000, 0, 0, 0, []), (2, false, 0x4241f20248fc0000, 0, 0, 0, []),
       (1, false, 0x422eba5355ea8a17, 0, 0, 0, []), (1, true, 0x422ebb69f75618c4, 0, 0, 0, [])]),
    (["-n", "5"],
      [0x40188e8145b9c3f2, 0x40188e8145b9c3f2, 0x3fd00824a4e60b32, 0x3fec6a8a1817127e,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 0, 0, 0, []),
      "0 primes used for the first stage of sieving,\n" ++
      "0 primes used for the first two stages together,\n" ++
      "0 primes used for all three stages together.\n",
      [(0, false, 0x4241f1dbd5bf2999, 5, 5, 5, [0, 1, 2, 3, 4]),
       (2, false, 0x4241f2512623a999, 5, 5, 5, [0, 1, 2, 3, 4]),
       (1, false, 0x423604ace05ed4bd, 0, 0, 0, []), (1, true, 0x4236055875a81fe5, 0, 0, 0, [])]),
    (["-M", "1", "-N", "2", "-c", "ROW=1,CELL=1e6"],
      [0x40188e8145b9c3f2, 0x40188e8145b9c3f2, 0x3fd00824a4e60b32, 0x3fec6a8a1817127e,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (1, false, 0, 1, 2, [0, 1]),
      "Sieving in the tube of the bound on the fourth coordinate:\n" ++
      "about 6.14 words per row, 0.25 cells of the analysis per row.\n" ++
      "0 primes used for the first stage of sieving,\n" ++
      "1 primes used for the first two stages together,\n" ++
      "2 primes used for all three stages together.\n" ++
      "Constants of the cost model set by -c: ROW=1 CELL=1e+06\n" ++
      "Sieving primes:\n" ++
      " First stage: \n" ++
      " Second stage: 3\n" ++
      " Third stage: 5\n" ++
      "Probabilities: Min(3) = 1.000000, Cut2(3) = 1.000000, Cut3(5) = 1.000000, " ++
      "Max(13) = 1.000000\n" ++
      "\n",
      [(0, false, 0x42422414549be999, 1, 1, 2, [0, 1]),
       (2, false, 0x4242246e0a8e6999, 1, 1, 2, [0, 1]),
       (1, false, 0x4240687557a8949d, 0, 1, 2, [0, 1]),
       (1, true, 0x424068cb224d3a30, 0, 1, 2, [0, 1])]),
    (["-a", "-n", "1", "-N", "3", "-c", "RROW=0.5,RANGE=1e-3"],
      [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 1, 3, 3, [0, 1, 2]),
      "1 primes used for the first stage of sieving,\n" ++
      "3 primes used for the first two stages together,\n" ++
      "3 primes used for all three stages together.\n" ++
      "Constants of the cost model set by -c: RROW=0.5 RANGE=0.001\n" ++
      "Sieving primes:\n" ++
      " First stage: 3\n" ++
      " Second stage: 5, 7\n" ++
      " Third stage: \n" ++
      "Probabilities: Min(3) = 1.000000, Cut1(3) = 1.000000, Cut2(7) = 1.000000, " ++
      "Max(13) = 1.000000\n" ++
      "\n",
      [(0, false, 0x4241f252d72e6999, 1, 3, 3, [0, 1, 2]),
       (2, false, 0x4241f25a6ece9cee, 1, 3, 3, [0, 1, 2])]),
    (["-a", "-n", "2", "-M", "2", "-N", "2", "-c", "ROW=1e6"],
      [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
      0x4024000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      (0, false, 2, 2, 2, [0, 1]),
      "2 primes used for the first stage of sieving,\n" ++
      "2 primes used for the first two stages together,\n" ++
      "2 primes used for all three stages together.\n" ++
      "Constants of the cost model set by -c: ROW=1e+06\n" ++
      "Sieving primes:\n" ++
      " First stage: 3, 5\n" ++
      " Second stage: \n" ++
      " Third stage: \n" ++
      "Probabilities: Min(3) = 1.000000, Cut1(5) = 1.000000, Max(13) = 1.000000\n" ++
      "\n",
      [(0, false, 0x42537fb4035daaaa, 2, 2, 2, [0, 1]),
       (2, false, 0x42537fe451a52aaa, 2, 2, 2, [0, 1])])]
  cases.all fun (os, st, (m, c, s1, s2, s3, pnn), text, modes) ↦
    let g := globals (["30031 -2 1 2 -2 0 1", "300", "-p", "5"] ++ os) st 0 false
      0x3ff0000000000000 0
    let (_, prec, p, _, out) :=
      (initFmodpsquare t g CurveTables.initial (.replicate numPrimes {}) {}).run
    (p.sieveMode, p.tubeCut, p.sievePrimes1, p.sievePrimes2, p.sievePrimes3) ==
        (m, c, s1, s2, s3) && (p.pnn.extract 0 s3).toList == pnn && out == text &&
      modes.all fun (m, c, cost, s1, s2, s3, pnn) ↦
        let (k, p) := (choosePrimesMode m c g prec {}).run
        k.toBits == cost && (p.sievePrimes1, p.sievePrimes2, p.sievePrimes3) == (s1, s2, s3) &&
          (p.pnn.extract 0 s3).toList == pnn

-- Curves of `testcurves2` of `j-points` with their first 20 primes considered (`-p 20`): in the
-- box, in the tube cut to the real region with the condition at 2 (the monic quintic of example 2
-- of the README of `j-points`), in the region with constants set by `-c` (a curve of `test3.sh`),
-- in the tube, and in the box with all 20 primes pinned: for each mode the terms it fixes, the
-- range of the first stage and the number of its candidates; the set-up terms of the primes
-- (`tabcost`, `initcost`) by their hashes; and messages 4, 7 and 8 for the records and the plan
-- that the C code made.
#guard
  let cases : List (List String × List UInt64 × Nat × Bool × UInt64 × UInt64 × Plan ×
      List (Nat × UInt64) × List (Nat × Bool × Int × List UInt64) × (UInt64 × UInt64) ×
      List (Nat × Nat × Nat) × String) := [
    (["1 4 3 -8 2 8 7", "255", "-p", "20"],
      [0x401bdd99292c199e, 0x401bdd99292c199e, 0x3fd0609e19fbf96a, 0x3ff0000000000000,
      0x4020000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      0, false, 0x3ff0000000000000, 0x0000000000000000,
      plan 0 false 12 13 17 [7, 6, 1, 3, 8, 2, 4, 5, 9, 0, 11, 12, 10, 15, 14, 16, 13],
      [(12, 0x3fd7cd47f28736cc), (8, 0x3fd86585c1e1aa3e), (15, 0x3fd89df187461878),
      (14, 0x3fd8c4c8c0bd65a5), (11, 0x3fd91c39c7fabd8c), (16, 0x3fd971cc77f8aeba),
      (13, 0x3fd9bf712f44032a), (19, 0x3fda326f3e6d85f7), (7, 0x3fda463bb686c91b),
      (17, 0x3fdbf1361dce84b5), (18, 0x3fdc221276a4e3b7), (9, 0x3fdccf93cb601039),
      (6, 0x3fdd10c214ad543d), (10, 0x3fdda8799432c328), (3, 0x3fe09cf258171494),
      (1, 0x3fe0a3d70a3d70a4), (2, 0x3fe17231426cf7ca), (5, 0x3fe23e6c7c6e41f8),
      (4, 0x3fe2b7680dfb9278), (0, 0x3fe425ed097b425f)],
      [(0, false, -1, [0x4020000000000000, 0x40fff00000000000, 0x4080000000000000,
          0x4072c00000000000, 0x0000000000000000]),
       (2, false, -1, [0x4020000000000000, 0x40fff00000000000, 0x4080000000000000,
          0x4076800000000000, 0x4014000000000000]),
       (1, false, 0, [0x401bdd99292c199e, 0x40fff00000000000, 0x407bdd99292c199e,
          0x406a4f7c3fae057d, 0x0000000000000000]),
       (1, true, 0, [0x401bdd99292c199e, 0x40fff00000000000, 0x407bdd99292c199e,
          0x407187be1fd702be, 0x0000000000000000])],
      (8396603543330488320, 11788901997283901440), [(20, 0, 20), (20, 0, 20), (20, 0, 0),
       (20, 0, 0)],
      "12 primes used for the first stage of sieving,\n" ++
      "13 primes used for the first two stages together,\n" ++
      "17 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: 23, 19, 5, 11, 29, 7, 13, 17, 31, 3, 41, 43\n" ++
      " Second stage: 37\n" ++
      " Third stage: 59, 53, 61, 47\n" ++
      "Probabilities: Min(43) = 0.371904, Cut1(43) = 0.371904, Cut2(37) = 0.463408, " ++
      "Cut3(47) = 0.402310, Max(3) = 0.629630\n" ++
      "\n"),
    (["1 178 817 -274 16 1", "2000", "-p", "20"],
      [0x402ee47391ce4739, 0x40239fea7fa9fea8, 0x3fe3dd0f743dd0f7, 0x3ff0000000000000,
      0x404ae952a54a952a, 0x3ff6096825a09682, 0x3febf7efdfbf7efe],
      3, true, 0x3fd3249249249249, 0x3fd7000000000000,
      plan 1 true 0 9 13 [7, 8, 10, 13, 5, 11, 14, 15, 2, 16, 12, 9, 6],
      [(17, 0x3fd8da69141b483d), (13, 0x3fd93584ce944b53), (19, 0x3fd9cb5a58a03ad8),
      (10, 0x3fda27db15eb4f17), (7, 0x3fda9f1bc0a03e9e), (8, 0x3fdaaca042d7892e),
      (15, 0x3fdab6aa83f30fc4), (16, 0x3fdafbe9ef4e3bb0), (11, 0x3fdbeee61f2dbc42),
      (14, 0x3fdc6992a94badbe), (18, 0x3fdd326441ff3a39), (5, 0x3fddd16aa98e1848),
      (12, 0x3fdf93ea94e4569d), (2, 0x3fe17231426cf7ca), (9, 0x3fe1777d0a260893),
      (6, 0x3fe1a3cfc744c965), (3, 0x3fe24bc7d6748e54), (4, 0x3fe310e550fbb04c),
      (0, 0x3fe684bda12f684c), (1, 0x3fe9db22d0e56042)],
      [(0, false, -1, [0x4050000000000000, 0x40fc28d540000000, 0x40b0000000000000,
          0x4072c00000000000, 0x0000000000000000]),
       (2, false, -1, [0x404ae952a54a952a, 0x40fc28d540000000, 0x40aae952a54a952a,
          0x407a3c02b00ac02b, 0x401b8bc22f08bc22]),
       (1, false, 0, [0x402ee47391ce4739, 0x40fc28d540000000, 0x408ee47391ce4739,
          0x407acfd4ff53fd50, 0x0000000000000000]),
       (1, true, 0, [0x40239fea7fa9fea8, 0x40fc28d540000000, 0x40839fea7fa9fea8,
          0x40804b10cc43310c, 0x0000000000000000])],
      (15219096717216448512, 9646244552494809088), [(20, 0, 20), (20, 0, 20), (20, 0, 0),
       (20, 0, 0)],
      "Sieving in the tube of the bound on the fourth coordinate, cut to the real region:\n" ++
      "about 9.81 words per row, 0.62 cells of the analysis per row.\n" ++
      "The condition at 2 admits 0.299 of the classes mod 64 and empties 0.359 of the rows.\n" ++
      "0 primes used for the first stage of sieving,\n" ++
      "9 primes used for the first two stages together,\n" ++
      "13 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: \n" ++
      " Second stage: 23, 29, 37, 47, 17, 41, 53, 59, 7\n" ++
      " Third stage: 61, 43, 31, 19\n" ++
      "Probabilities: Min(67) = 0.388331, Cut2(7) = 0.545190, Cut3(19) = 0.551247, " ++
      "Max(5) = 0.808000\n" ++
      "\n"),
    (["-15999999989999968000000020000000000000000000 159999999899999680000000200 0 " ++
      "0 15999999989999968000000020000000000000000000 -159999999899999680000000200",
      "256", "-p", "20", "-a", "-c", "ROW=10000000,RROW=1,RANGE=1,PASS=1,REXCL=1"],
      [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
      0x40180423e1a38951, 0x3ff62542eebfd3d7, 0x3ff0000000000000],
      2, false, 0x3ff0000000000000, 0x0000000000000000,
      plan 2 false 11 11 14 [6, 9, 8, 3, 7, 10, 11, 2, 12, 13, 14, 15, 16, 19],
      [(19, 0x3fd7fe83de40bf25), (15, 0x3fd8b513fc1895e3), (16, 0x3fd8e735729444e5),
      (9, 0x3fdabf9c74d54880), (11, 0x3fdbe563daa9b22b), (13, 0x3fdbf5a75ddf7ca0),
      (14, 0x3fdc3058ba707eea), (8, 0x3fdc5d404ff10d8d), (10, 0x3fdc855d648c9a26),
      (12, 0x3fdd24c2cceacdc4), (18, 0x3fddac2234dbda73), (6, 0x3fe0b754e90bd4db),
      (7, 0x3fe1212e4f682bef), (3, 0x3fe3046c7a53795d), (2, 0x3fe70b32017e2255),
      (0, 0x3ff0000000000000), (1, 0x3ff0000000000000), (4, 0x3ff0000000000000),
      (5, 0x3ff0000000000000), (17, 0x3ff0000000000000)],
      [(0, false, -1, [0x4024000000000000, 0x4100180800000000, 0x4084000000000000,
          0x416312d000000000, 0x0000000000000000]),
       (2, false, -1, [0x40180423e1a38951, 0x4100180800000000, 0x40780423e1a38951,
          0x416312d0cc4a85dd, 0x3ff62542eebfd3d7])],
      (11755346596768776192, 18297534573384302592), [(20, 0, 20), (20, 0, 20)],
      "Sieving the real region by passes over its ranges of words:\n" ++
      "about 6.00 words per row in 1.38 ranges, 1.000 of the rows.\n" ++
      "11 primes used for the first stage of sieving,\n" ++
      "11 primes used for the first two stages together,\n" ++
      "14 primes used for all three stages together.\n" ++
      "Constants of the cost model set by -c: ROW=1e+07 RROW=1 REXCL=1 RANGE=1 PASS=1\n" ++
      "Sieving primes:\n" ++
      " First stage: 19, 31, 29, 11, 23, 37, 41, 7, 43, 47, 53\n" ++
      " Second stage: \n" ++
      " Third stage: 59, 61, 73\n" ++
      "Probabilities: Min(73) = 0.374909, Cut1(53) = 0.440451, Cut3(73) = 0.374909, " ++
      "Max(67) = 1.000000\n" ++
      "\n"),
    (["-7 0 6 6 10 -7 -3", "63", "-p", "20"],
      [0x4000000000000000, 0x3ff8b67616983174, 0x3faeb1c59868051e, 0x3ff0000000000000,
      0x3ff8b67616983174, 0x3fed712f88a1ff93, 0x3fed712f88a1ff93],
      3, false, 0x3ff0000000000000, 0x0000000000000000,
      plan 1 false 0 9 12 [4, 2, 3, 1, 0, 5, 6, 7, 8, 10, 13, 11],
      [(10, 0x3fd5d5a32da719a9), (8, 0x3fd68f4717d10f3b), (18, 0x3fd72d63d238105d),
      (13, 0x3fd77373fedda293), (11, 0x3fd78cda8a5115d6), (19, 0x3fd7976eade16d2a),
      (16, 0x3fd8724606078b99), (17, 0x3fd8808bd94a0ebf), (12, 0x3fd904dbd683fb39),
      (7, 0x3fd9593b9b983a69), (4, 0x3fda3f27bbf36a63), (15, 0x3fdaf77164a6d556),
      (6, 0x3fdd10c214ad543d), (9, 0x3fddd78f76a57416), (14, 0x3fde612a126e16a2),
      (5, 0x3fde717d00fd7260), (3, 0x3fe09cf258171494), (2, 0x3fe17231426cf7ca),
      (1, 0x3fe3b645a1cac083), (0, 0x3fe425ed097b425f)],
      [(0, false, -1, [0x4000000000000000, 0x40bfc00000000000, 0x4060000000000000,
          0x4072c00000000000, 0x0000000000000000]),
       (2, false, -1, [0x3ff8b67616983174, 0x40bfc00000000000, 0x4058b67616983174,
          0x407a86bdb5653fbc, 0x401266bdb5653fbc]),
       (1, false, 0, [0x4000000000000000, 0x40bfc00000000000, 0x4060000000000000,
          0x40560bc6dfd040cd, 0x0000000000000000]),
       (1, true, 0, [0x3ff8b67616983174, 0x40bfc00000000000, 0x4058b67616983174,
          0x406e56fe82066509, 0x0000000000000000])],
      (16284594080908836864, 4476181140268384256), [(20, 0, 20), (20, 0, 20), (20, 0, 0),
       (20, 0, 0)],
      "Sieving in the tube of the bound on the fourth coordinate:\n" ++
      "about 2.00 words per row, 0.06 cells of the analysis per row.\n" ++
      "0 primes used for the first stage of sieving,\n" ++
      "9 primes used for the first two stages together,\n" ++
      "12 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: \n" ++
      " Second stage: 13, 7, 11, 5, 3, 17, 19, 23, 29\n" ++
      " Third stage: 37, 47, 41\n" ++
      "Probabilities: Min(37) = 0.341164, Cut2(29) = 0.352495, Cut3(41) = 0.367972, " ++
      "Max(3) = 0.629630\n" ++
      "\n"),
    (["1 4 3 -8 2 8 7", "255", "-p", "20", "-N", "20"],
      [0x401bdd99292c199e, 0x401bdd99292c199e, 0x3fd0609e19fbf96a, 0x3ff0000000000000,
      0x4020000000000000, 0x3ff0000000000000, 0x3ff0000000000000],
      0, false, 0x3ff0000000000000, 0x0000000000000000,
      plan 0 false 12 13 20 [7, 6, 1, 3, 8, 2, 4, 5, 9, 0, 11, 12, 10, 15, 14, 16, 13, 17, 19, 18],
      [(12, 0x3fd7cd47f28736cc), (8, 0x3fd86585c1e1aa3e), (15, 0x3fd89df187461878),
      (14, 0x3fd8c4c8c0bd65a5), (11, 0x3fd91c39c7fabd8c), (16, 0x3fd971cc77f8aeba),
      (13, 0x3fd9bf712f44032a), (19, 0x3fda326f3e6d85f7), (7, 0x3fda463bb686c91b),
      (17, 0x3fdbf1361dce84b5), (18, 0x3fdc221276a4e3b7), (9, 0x3fdccf93cb601039),
      (6, 0x3fdd10c214ad543d), (10, 0x3fdda8799432c328), (3, 0x3fe09cf258171494),
      (1, 0x3fe0a3d70a3d70a4), (2, 0x3fe17231426cf7ca), (5, 0x3fe23e6c7c6e41f8),
      (4, 0x3fe2b7680dfb9278), (0, 0x3fe425ed097b425f)],
      [(0, false, -1, [0x4020000000000000, 0x40fff00000000000, 0x4080000000000000,
          0x4072c00000000000, 0x0000000000000000]),
       (2, false, -1, [0x4020000000000000, 0x40fff00000000000, 0x4080000000000000,
          0x4076800000000000, 0x4014000000000000]),
       (1, false, 0, [0x401bdd99292c199e, 0x40fff00000000000, 0x407bdd99292c199e,
          0x406a4f7c3fae057d, 0x0000000000000000]),
       (1, true, 0, [0x401bdd99292c199e, 0x40fff00000000000, 0x407bdd99292c199e,
          0x407187be1fd702be, 0x0000000000000000])],
      (8396603543330488320, 11788901997283901440), [(20, 0, 20), (20, 0, 20), (20, 0, 0),
       (20, 0, 0)],
      "12 primes used for the first stage of sieving,\n" ++
      "13 primes used for the first two stages together,\n" ++
      "20 primes used for all three stages together.\n" ++
      "Sieving primes:\n" ++
      " First stage: 23, 19, 5, 11, 29, 7, 13, 17, 31, 3, 41, 43\n" ++
      " Second stage: 37\n" ++
      " Third stage: 59, 53, 61, 47, 67, 73, 71\n" ++
      "Probabilities: Min(43) = 0.371904, Cut1(43) = 0.371904, Cut2(37) = 0.463408, " ++
      "Cut3(71) = 0.439580, Max(3) = 0.629630\n" ++
      "\n")]
  cases.all fun (args, st, nn, u2, d2, e2, pl, prec, shapes, (ht, hi), ranges, text) ↦
    let g := globals args st nn u2 d2 e2
    let np := g.input.numPrimes.toNat
    let pr := precOf prec
    let tm := (choosePrimesModeTerms g.input.costs pr np).run
    hash ((tm.tabcost.extract 0 np).map Float.toBits) == ht &&
      hash ((tm.initcost.extract 0 np).map Float.toBits) == hi &&
      (shapes.zip ranges).all (fun ((m, c, p1, bs), (ne, lo, hi)) ↦
        let s := choosePrimesModeShape m c g
        s.pin1 == p1 && [s.w, s.rows, s.bits, s.fixed, s.passx].map Float.toBits == bs &&
          (choosePrimesModeList1 s tm g.input.costs pr np).run.size == ne &&
          choosePrimesModeRange1 ne p1 g.input.sievePrimes2 g.input.sievePrimes3 == (lo, hi)) &&
      (message4 g pl).run ++ (message7 pl).run ++ (message8 pr np pl).run == text

-- The tables of the primes chosen, after the rates of the model, for the plans that the C code
-- made: the flags `tabled` of the primes considered and the hash of the rows of the table of the
-- third stage of the primes considered; `73`, whose rate was sampled, in the region, and every
-- prime with `-N 20`.
#guard
  let t := (initMain Tables.initial).run
  let cases : List (List String × Plan × String × UInt64) := [
    (["-15999999989999968000000020000000000000000000 159999999899999680000000200 0 " ++
      "0 15999999989999968000000020000000000000000000 -159999999899999680000000200",
      "256", "-p", "20", "-a", "-c", "ROW=10000000,RROW=1,RANGE=1,PASS=1,REXCL=1"],
      plan 2 false 11 11 14 [6, 9, 8, 3, 7, 10, 11, 2, 12, 13, 14, 15, 16, 19],
      "11111111111111111001", 3917551803131195816),
    (["1 4 3 -8 2 8 7", "255", "-p", "20", "-N", "20"],
      plan 0 false 12 13 20 [7, 6, 1, 3, 8, 2, 4, 5, 9, 0, 11, 12, 10, 15, 14, 16, 13, 17, 19, 18],
      "11111111111111111111", 10293545642693327659)]
  cases.all fun (args, pl, tb, h) ↦
    let g := globals args [] 0 false 0 0
    let np := g.input.numPrimes.toNat
    let (ct, r) := (initFmodpsquareRates t g.curve.coeffs g.curve.degree np CurveTables.initial
      (.replicate numPrimes {})).run
    let (ct, tabled) := (initFmodpsquareTables t ct g.curve.degree pl r.tabled).run
    String.ofList ((tabled.extract 0 np).toList.map (if · then '1' else '0')) == tb &&
      ct.isPointOnJ.foldl (fun h b ↦ h * 1000003 + if b then 1 else 0) 0 0
        (np * maxPrimeEven * maxPrimeEven) == h

end JPoints

end
