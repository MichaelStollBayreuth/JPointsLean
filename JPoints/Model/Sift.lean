/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Check
public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import JPoints.Model.Rows
public import JPoints.Model.TwoAdic

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Check
meta import JPoints.Model.DoubleArith
meta import JPoints.Model.Rows
meta import JPoints.Model.TwoAdic

/-!
# The second and third stages of the sieve

What the sieve of `j-points` does with a word of the bit array of a row `(a, b)` that the passes of
the first-stage primes leave: `check_point` (`JPoints.checkPoint`) takes its AND with the word of
the row of `(a, b)` of the sieve table of each second-stage prime at the residue of the index of the
word, and hands the bits that are left to `check_bits` (`JPoints.checkBits`), which takes each bit
`c` in turn to the test whether `gcd(a, b, c) = 1` (`JPoints.relprime3`, `JPoints.relprime2`,
`JPoints.oddGcd`), the third stage (`JPoints.checkBit`) and the exact check
(`JPoints.checkOnePoint`). The third stage tests the bit against each third-stage prime `p` by an
entry of a table of the curve, found from the class of `(a, b, c)` modulo `p` by a factor `1 / a`
or `1 / b` modulo `p` and a row of the table that `row3_setup` sets for the row `(a, b)`
(`JPoints.row3Setup`) and the thread keeps from bit to bit, and the reductions modulo `p` are
made by a reciprocal of `p` (`JPoints.mod3`).

Here are also the data of the sieve: what it reads from the globals of the program
(`JPoints.SiftGlobals`), the static data that `init_sift` computes once for the run
(`JPoints.SiftData`, with the chunks of a row, `JPoints.ChunkSpec` and `JPoints.WalkSpec`) and
`init_sift` itself (`JPoints.initSift`: the sieving primes with the lengths of their rows and the
reciprocals of the third stage, `JPoints.initSiftPrimes`; the chunks with the walks of the
first-stage primes over them, `JPoints.initSiftChunk` and `JPoints.initSiftWalk`; the residues of
the positions in a chunk and the reciprocals of the primes, `JPoints.initSiftResidues`), and the
state of the thread that the sieve threads through the rows (`JPoints.SiftState`): the bit array,
the rows of the sieve tables for the row in hand, the data of the third stage
(`JPoints.Row3Cache`), the statics of `row_setup` (`JPoints.RowSetupCache`), the counters of the
survivors of the three stages and the output.

## Main definitions

* `JPoints.WalkSpec`, `JPoints.ChunkSpec`: the walk of a first-stage prime over a chunk, and a
  chunk of a row.
* `JPoints.SiftData`, `JPoints.SiftData.initial`: the static data of the sieve.
* `JPoints.SiftGlobals`: what the sieve reads from the globals of the program.
* `JPoints.initSift`, `JPoints.initSiftPrimes`, `JPoints.initSiftWalk`, `JPoints.initSiftChunk`,
  `JPoints.initSiftResidues`: the static data of the sieve as `init_sift` computes them.
* `JPoints.Tab3Ptr`, `JPoints.Tab3Ptr.get`: the pointers to the rows of the third stage.
* `JPoints.Row3Cache`, `JPoints.RowSetupCache`, `JPoints.SiftState`: the state of the thread, and
  their values when the sieve starts.
* `JPoints.relprime2`, `JPoints.relprime3`, `JPoints.oddGcd`: the tests for common factors.
* `JPoints.mod3`, `JPoints.row3Setup`, `JPoints.checkBit`: the third stage.
* `JPoints.checkBits`, `JPoints.checkPoint`: the bits of a word, and the second stage of a word.

## Implementation notes

The globals of `j-points.c` and the statics of `j-sift.c` are fields of structures: what the sieve
only reads, `JPoints.SiftGlobals` and `JPoints.SiftData`, is passed; what it writes, the state of
the thread, is taken and returned. The thread-local variables are those of the one thread of a run
without `-t`, whose threads are not modelled. The arrays of the C code are arrays with its index
arithmetic; a pointer into an array is an index (`r0` into `res0`, `rowptr[n]` into
`sieve_tab[n]`), or an array of its own where it points to the part of a chunk of an array that
`init_sift` allocates for all of them (`walk` and `res` of a chunk), and the pointers of `tab3`,
which point into three different tables, are `JPoints.Tab3Ptr`. The `long`s that may be negative
(the coordinates, the indices of the words of a row) are integers; the counts, the residues and the
indices that the C code keeps nonnegative are natural numbers. The bit array of the sieve and the
words of the tables are `UInt64`s.

`JPoints.checkBits` takes the output out of the state while the exact check appends a point to it,
so that the text is not shared and the compiled code appends to it in place.
-/

@[expose] public section

namespace JPoints

/-! ### The static data of the sieve -/

/-- `walk_spec`, the walk of a first-stage prime `p` over a chunk of a row, in the scalar walk: the
word `first` of the row of its sieve table that the chunk begins with, the `head` words from there
to the end of the period of the row (or of the chunk), then `nper` full periods of `p` words and
the `tail` words after them.

C: `j-sift.c:47-53`

Deviation: natural numbers for the `long`s, which the C code keeps nonnegative. -/
structure WalkSpec where
  /-- `first`, the word of the row of the table that the chunk begins with, in `[1, p]`. -/
  first : Nat
  /-- `head`, the words from `first` to the end of the period of the row, or of the chunk. -/
  head : Nat
  /-- `nper`, the full periods of `p` words after the head. -/
  nper : Nat
  /-- `tail`, the words after the last full period. -/
  tail : Nat
  deriving Inhabited, DecidableEq, Repr

/-- `chunk_spec`, a chunk of a row: the words `w_low ≤ i < w_high` of the row that the bit array
holds at once, the walks of the first-stage primes over them, and the residues of the first word
modulo the sieving primes. The chunks are the same for every row.

C: `j-sift.c:55-56`, `j-sift.c:58-60`

Deviation: arrays of their own for the pointers `walk` and `res` into the arrays that `init_sift`
allocates for all the chunks, the parts of this chunk; integers for the `long`s `w_low` and
`w_high`, which may be negative, and natural numbers for the residues; without the field `nvec`,
which only the vector walk reads. -/
structure ChunkSpec where
  /-- `w_low`, the index in the row of the first word of the chunk. -/
  wLow : Int
  /-- `w_high`, the index in the row of the word after the chunk. -/
  wHigh : Int
  /-- `walk`, at `n`, the walk of the `n`-th first-stage prime over the chunk. -/
  walk : Array WalkSpec
  /-- `res`, at `n`, the residue of `w_low` modulo the `n`-th sieving prime `p`, in `[0, p)`. -/
  res : Array Nat
  deriving Inhabited, Repr

/-- The static data of the sieve, which `init_sift` computes once for the run: the chunks of a row,
the number of the sieving primes of all three stages and the table `res0` of the residues of the
positions in a chunk, the row `all_ones` and the reciprocals `recip3` of the third stage, the
sieving primes with the lengths of the rows and of the blocks of rows of one residue class of `a`
in their sieve tables, the words of a whole row, the bound on the fourth coordinate and its square,
and the reciprocals of the primes as doubles. `tube_sample`, which runs before `init_sift`, sets
`w_low_all`, `w_high_all`, `th` and `th2` to the same values.

C: `j-sift.c:78-79`, `j-sift.c:81-82`, `j-sift.c:96`, `j-sift.c:99`, `j-sift.c:110`,
`j-sift.c:113-115`

Deviation: arrays for the arrays of the C code and for the pointers `chunks` and `res0` to the
arrays that `init_sift` allocates, the empty array for a null pointer; natural numbers for the
nonnegative `long`s and for the `unsigned short`s of `res0`, integers for the `long`s `w_low_all`
and `w_high_all`; an array of Booleans for the `unsigned char`s of `all_ones`, which hold `0` and
`1`; a structure, for the statics. -/
structure SiftData where
  /-- `chunks`, the chunks of a row, in the order of their words. -/
  chunks : Array ChunkSpec
  /-- `num_chunks`, the number of the chunks. -/
  numChunks : Nat
  /-- `npr`, the number `sieve_primes3` of the sieving primes of all three stages. -/
  npr : Nat
  /-- `res0`, at `k * npr + n` for `k ≤ array_size` and `n < npr`, the residue of `k` modulo the
  `n`-th sieving prime. -/
  res0 : Array Nat
  /-- `all_ones`, the row of the third stage that admits every class: `JPoints.maxPrimeEven`
  entries `true`. -/
  allOnes : Array Bool
  /-- `recip3`, at `m`, the reciprocal `⌈2 ^ 32 / p⌉` of the `m`-th third-stage prime
  `p = pr[sieve_primes2 + m]`. -/
  recip3 : Array UInt64
  /-- `pr`, at `n < npr`, the `n`-th sieving prime, `prime[pnn[n]]`. -/
  pr : Array Nat
  /-- `rowlen`, at `n`, the number `JPoints.sieveRowlen p = p + 1` of the words of a row of the
  sieve table of the `n`-th sieving prime `p`. -/
  rowlen : Array Nat
  /-- `blocklen`, at `n`, the number `p * rowlen[n]` of the words of the rows of one residue class
  of `a` in the sieve table of the `n`-th sieving prime `p`. -/
  blocklen : Array Nat
  /-- `w_low_all`, the index `⌊-height / 64⌋` of the first word of a whole row. -/
  wLowAll : Int
  /-- `w_high_all`, the index `⌊height / 64⌋ + 1` of the word after a whole row. -/
  wHighAll : Int
  /-- `th`, the bound `dbound` on the fourth coordinate, as a double. -/
  th : Double
  /-- `th2`, the square `th * th`. -/
  th2 : Double
  /-- `invp`, at `n`, the reciprocal `1 / p` of the `n`-th sieving prime `p`, as a double. -/
  invp : Array Double

/-- The static data of the sieve when the program starts: the zeros and the null pointers of static
storage.

C: `j-sift.c:78-79`, `j-sift.c:81-82`, `j-sift.c:96`, `j-sift.c:99`, `j-sift.c:110`,
`j-sift.c:113-115` -/
def SiftData.initial : SiftData where
  chunks := #[]
  numChunks := 0
  npr := 0
  res0 := #[]
  allOnes := Array.replicate maxPrimeEven false
  recip3 := Array.replicate numPrimes 0
  pr := Array.replicate numPrimes 0
  rowlen := Array.replicate numPrimes 0
  blocklen := Array.replicate numPrimes 0
  wLowAll := 0
  wHighAll := 0
  th := .zero
  th2 := .zero
  invp := Array.replicate numPrimes .zero

/-- What the sieve reads from the globals of `j-points.c`: the tables of `init_main` (`inverses`),
the tables of the curve modulo the primes (`is_f_square` and `is_point_on_j`), the sieve tables of
the first two stages (`sieve_tab`), what the exact check reads (`height`, `dbound` and `one_point`
among it), the number `array_size` of the words of the bit array, the condition at 2 (`use2` and
`mask2`), the indices `pnn` in `JPoints.primeTable` of the sieving primes, the numbers
`sieve_primes1`, `sieve_primes2` and `sieve_primes3` of the sieving primes of the first stage, of
the first two stages and of all three, and the masks `begmask` and `endmask` of the bits of the
first and the last word of a row that lie in the row, which `main` sets.

C: `j-points.c:300`

Deviation: a structure, for the globals, of which only the declaration of `begmask` and `endmask`
is recorded here, the others where the model defines them (`JPoints.Tables`, `JPoints.CurveTables`,
`JPoints.SieveTables`, `JPoints.CheckGlobals`, `JPoints.TwoAdic`, `JPoints.Cli.Input`); `UInt64`s
for the masks; a natural number for the `long` `array_size`, which `main` converts from the
kilobytes of `-s` into words. -/
structure SiftGlobals where
  /-- The tables of `init_main`. -/
  tables : Tables
  /-- The tables of the curve modulo the primes. -/
  curve : CurveTables
  /-- The sieve tables of the primes of the first two stages. -/
  sieve : SieveTables
  /-- What the exact check reads from the globals. -/
  check : CheckGlobals
  /-- `array_size`, the number of the words of the bit array, the length of a chunk of a row. -/
  arraySize : Nat
  /-- The condition at 2: whether the sieve uses it (`use2`), and the fills of rows (`mask2`). -/
  twoAdic : TwoAdic
  /-- `pnn`, at `n`, the index in `JPoints.primeTable` of the `n`-th sieving prime. -/
  pnn : Array Nat
  /-- `sieve_primes1`, the number of the sieving primes of the first stage. -/
  sievePrimes1 : Nat
  /-- `sieve_primes2`, the number of the sieving primes of the first two stages. -/
  sievePrimes2 : Nat
  /-- `sieve_primes3`, the number of the sieving primes of all three stages. -/
  sievePrimes3 : Nat
  /-- `begmask`, the bits `j` of the first word `w_low_all` of a row whose third coordinate
  `c = 64 w_low_all + j` is at least `-height`: `(~0UL) << ((-height) & 63)`. -/
  begmask : UInt64
  /-- `endmask`, the bits `j` of the last word `w_high_all - 1` of a row whose third coordinate
  `c = 64 (w_high_all - 1) + j` is at most `height`: `(~0UL) >> ((~height) & 63)`. -/
  endmask : UInt64

/-! ### The set-up of the sieve -/

/-- The static data `sd` with the data of the sieving primes as `init_sift` sets them: for the
`n`-th sieving prime `p = prime[pnn[n]]`, `n < sieve_primes3`, `pr[n] = p`, the length
`rowlen[n] = sieve_rowlen(p)` of a row of its sieve table (`JPoints.sieveRowlen`) and the length
`blocklen[n] = p * rowlen[n]` of the rows of one residue class of `a`; the row `all_ones` of the
third stage; and for the `m`-th third-stage prime `p = pr[sieve_primes2 + m]` the reciprocal
`recip3[m] = ⌈2 ^ 32 / p⌉`, as `(2 ^ 32 + p - 1) / p` in `unsigned long`s.

C: `j-sift.c:142-143`, `j-sift.c:145-152`

Deviation: the static data taken and returned, for the statics; the globals that it reads passed;
natural numbers for the nonnegative `long`s, and `UInt64`s for the `unsigned long`s of the
reciprocals. -/
def initSiftPrimes (g : SiftGlobals) (sd : SiftData) : Id SiftData := do
  let mut pr := sd.pr
  let mut rowlen := sd.rowlen
  let mut blocklen := sd.blocklen
  for n in [0:g.sievePrimes3] do
    pr := pr.set! n primeTable[g.pnn[n]!]!
    rowlen := rowlen.set! n (← sieveRowlen pr[n]!)
    blocklen := blocklen.set! n (pr[n]! * rowlen[n]!)
  let mut allOnes := sd.allOnes
  for n in [0:maxPrimeEven] do allOnes := allOnes.set! n true
  let mut recip3 := sd.recip3
  for n in [0:g.sievePrimes3 - g.sievePrimes2] do
    let p := pr[g.sievePrimes2 + n]!.toUInt64
    recip3 := recip3.set! n ((((1 : UInt64) <<< 32) + p - 1) / p)
  return { sd with pr, rowlen, blocklen, allOnes, recip3 }

/-- The walk of the first-stage prime `p` over the chunk of the `range` words from the index `wLow`
on, as `init_sift` sets it for the scalar walk: for `start = wLow mod p` in `[0, p)`, the word
`first = start` of the row of the sieve table that the chunk begins with, `p` for `start = 0`, the
`head` of the `p - first` words to the end of the period of the row, at most `range`, and the
`nper` full periods of `p` words and the `tail` of the words after the head.

C: `j-sift.c:174-183`

Deviation: the walk returned, for the entry of the array of the walks that the C code writes; the
arm `VW == 1` of the test of the constant `VW`; an integer for the `long` `start`, with `Int.tmod`
for C's `%`, and natural numbers for the nonnegative `long`s. -/
def initSiftWalk (p : Nat) (wLow : Int) (range : Nat) : Id WalkSpec := do
  let mut start := wLow.tmod p
  if start < 0 then start := start + p
  let first := if start == 0 then p else start.toNat
  let mut head := p - first
  if head > range then head := range
  let nper := (range - head) / p
  return { first, head, nper, tail := range - head - nper * p }

/-- The `k`-th chunk of a row of the words from `wLow` to `wHigh`, as `init_sift` sets it: the words
from `w_low = wLow + k array_size` on, `array_size` of them or up to `wHigh`, the walk of each
first-stage prime `prime[pnn[n]]` over them (`JPoints.initSiftWalk`), and the residue of `w_low`
modulo each sieving prime, in `[0, p)`.

C: `j-sift.c:163-168`, `j-sift.c:170-173`, `j-sift.c:190-195`

Deviation: the chunk returned, for the entry of the array `chunks` that the C code writes; arrays
of its own, filled in the order in which the C code writes them, for the parts of the arrays of the
walks and of the residues of all the chunks that the pointers `walk` and `res` of the chunk point
to; integers for the `long`s that may be negative, with `Int.tmod` for C's `%`, and natural numbers
for the nonnegative ones. -/
def initSiftChunk (g : SiftGlobals) (sd : SiftData) (wLow wHigh : Int) (k : Nat) :
    Id ChunkSpec := do
  let chLow := wLow + (k * g.arraySize : Nat)
  let mut chHigh := chLow + g.arraySize
  if chHigh > wHigh then chHigh := wHigh
  let range := (chHigh - chLow).toNat
  let mut walk := #[]
  for n in [0:g.sievePrimes1] do
    walk := walk.push (← initSiftWalk primeTable[g.pnn[n]!]! chLow range)
  let mut res := #[]
  for n in [0:sd.npr] do
    let p : Int := sd.pr[n]!
    let mut start := chLow.tmod p
    if start < 0 then start := start + p
    res := res.push start.toNat
  return { wLow := chLow, wHigh := chHigh, walk, res }

/-- The static data `sd` with the table `res0` and the reciprocals `invp` as `init_sift` sets them:
for the `n`-th sieving prime `p`, `res0[k * npr + n] = k mod p` for `k ≤ array_size`, and
`invp[n] = 1.0 / (double)p`, rounded to nearest.

C: `j-sift.c:197-201`

Deviation: the static data taken and returned, for the statics; the globals that it reads passed;
`res0` a fresh array of `(array_size + 1) npr` zeros, for the array that `init_sift` allocates
(`j-sift.c:159`, memory management, not modelled), every entry of which the loop writes; natural
numbers for the nonnegative `long`s and for the `unsigned short`s of `res0`;
`JPoints.Double.ofInt` for the exact conversion of `p` to a double. -/
def initSiftResidues (g : SiftGlobals) (sd : SiftData) : Id SiftData := do
  let mut res0 := Array.replicate ((g.arraySize + 1) * sd.npr) 0
  let mut invp := sd.invp
  for n in [0:sd.npr] do
    let p := sd.pr[n]!
    for k in [0:g.arraySize + 1] do res0 := res0.set! (k * sd.npr + n) (k % p)
    invp := invp.set! n (1.0 / Double.ofInt p)
  return { sd with res0, invp }

/-- `init_sift`, the static data of the sieve as it computes them from the static data `sd` before
it, once for the run, after the choice of the primes and `init_sieve`: the words
`w_low_all = ⌊-height / 64⌋` to `w_high_all = ⌊height / 64⌋ + 1` of a whole row, the number
`npr = sieve_primes3` of the sieving primes and their data (`JPoints.initSiftPrimes`), the number
`num_chunks = ⌈(w_high_all - w_low_all) / array_size⌉` of the chunks of a row, the bound
`th = (double)dbound` on the fourth coordinate and its square `th2`, the chunks
(`JPoints.initSiftChunk`), and the residues of the positions in a chunk and the reciprocals of the
primes (`JPoints.initSiftResidues`).

C: `j-sift.c:132-141`, `j-sift.c:153-154`, `j-sift.c:162`, `j-sift.c:196`, `j-sift.c:202-203`

Deviation: the static data taken and returned, for the statics; the globals that it reads passed;
`>>>` on integers for C's `>>` on the `long`s, which gcc shifts arithmetically also for the negative
`-height`, where ISO C leaves the result to the implementation; `JPoints.ceilDiv` for the macro
`CEIL`, and a natural number for `num_chunks`, which is positive; `JPoints.Double.ofInt` for the
conversion of the `long` `dbound` to a double, rounded to nearest; a fresh array for the array of
the chunks that `init_sift` allocates (`j-sift.c:156`, memory management, not modelled), filled in
the order of the chunks. -/
def initSift (g : SiftGlobals) (sd : SiftData) : Id SiftData := do
  let wLow := (-g.check.height) >>> longShift
  let wHigh := (g.check.height >>> longShift) + 1
  let mut sd ← initSiftPrimes g
    { sd with npr := g.sievePrimes3, wLowAll := wLow, wHighAll := wHigh }
  let th := Double.ofInt g.check.dbound
  sd := { sd with numChunks := (ceilDiv (wHigh - wLow) g.arraySize).toNat, th, th2 := th * th }
  let mut chunks := #[]
  for k in [0:sd.numChunks] do chunks := chunks.push (← initSiftChunk g sd wLow wHigh k)
  initSiftResidues g { sd with chunks }

/-! ### The state of the thread -/

/-- A pointer of the array `tab3` of the third stage: the null pointer of static storage, or the
first entry of a row of a table of the curve or of the row `all_ones`, read at the class of the
third coordinate by `JPoints.Tab3Ptr.get`. -/
inductive Tab3Ptr where
  /-- The null pointer. -/
  | null
  /-- `&is_point_on_j[pn][r][0]`, the row of the exact table of the third stage for the classes
  `(1, r, c)` modulo the prime `prime[pn]`, from the index `i = (pn * 256 + r) * 256` of
  `JPoints.CurveTables.isPointOnJ` on. -/
  | pointOnJ (i : Nat)
  /-- `&is_f_square[pn][0]`, the table of the classes `x` for which `f(x)` is a square modulo the
  prime `prime[pn]`, from the index `i = pn * 256` of `JPoints.CurveTables.isFSquare` on. -/
  | fSquare (i : Nat)
  /-- `&all_ones[0]`, the row `JPoints.SiftData.allOnes`. -/
  | allOnes
  deriving Inhabited, DecidableEq, Repr

/-- `tab3[m][x]`, the entry `x` of the row that the pointer `t` points to, in the tables of the
curve `ct` and the row `allOnes`; `false` for the null pointer, through which the C code never
reads (`JPoints.checkBit` reads the entries of `tab3` that `JPoints.row3Setup` has set). -/
def Tab3Ptr.get (ct : CurveTables) (allOnes : Array Bool) (t : Tab3Ptr) (x : Nat) : Bool :=
  match t with
  | .null => false
  | .pointOnJ i => ct.isPointOnJ[i + x]!
  | .fSquare i => ct.isFSquare[i + x]!
  | .allOnes => allOnes[x]!

/-- The data of the third stage, which the thread keeps from bit to bit and from row to row: for
the `m`-th third-stage prime `p`, the row `tab3[m]` of a table of the curve and the factor
`mult3[m]`, `1 / a` or `1 / b` modulo `p`, which `check_bit` reads, the row `(row3_a, row3_b)` that
they are for, and the part that depends on `a` alone, `inva3[m]`, the inverse of `a` modulo `p` or
`0` when `p ∣ a`, which `row3_setup` recomputes only when `a` changes.

C: `j-sift.c:97-98`, `j-sift.c:105`, `j-sift.c:219`

Deviation: arrays for the arrays of the C code, `JPoints.Tab3Ptr` for the pointers of `tab3`;
integers for the `long`s; a structure, for the thread-local globals of the one thread. -/
structure Row3Cache where
  /-- `tab3`, at `m`, the row of a table of the curve for the `m`-th third-stage prime. -/
  tab3 : Array Tab3Ptr
  /-- `mult3`, at `m`, the factor of the `m`-th third-stage prime. -/
  mult3 : Array Int
  /-- `row3_a`, the first coordinate of the row that the data are for; `-1` before the first. -/
  row3A : Int
  /-- `row3_b`, the second coordinate of the row that the data are for. -/
  row3B : Int
  /-- `inva3`, at `m`, the inverse of `row3_a` modulo the `m`-th third-stage prime, or `0`. -/
  inva3 : Array Int

/-- The data of the third stage when the program starts: `row3_a = -1` and `row3_b = 0`, and the
zeros and the null pointers of static storage.

C: `j-sift.c:97-98`, `j-sift.c:105`, `j-sift.c:219` -/
def Row3Cache.initial : Row3Cache where
  tab3 := Array.replicate numPrimes .null
  mult3 := Array.replicate numPrimes 0
  row3A := -1
  row3B := 0
  inva3 := Array.replicate numPrimes 0

/-- The statics of `row_setup`, which the thread keeps from row to row: the row
`(last_a, last_b)` of the last call and the step `last_d` of at least `3` whose residues it keeps,
`0` after a computation by division, and for the `n`-th sieving prime `p` of the first two stages,
the residue `bres[n]` of `last_b` modulo `p`, the residue `dres[n]` of the step and the offset
`drow[n] = dres[n] * rowlen[n]` of the rows of the sieve table that it makes.

C: `j-sift.c:1111-1112`

Deviation: integers for the `long`s `last_a`, `last_b` and `last_d`, natural numbers for the
residues and the offsets, which the C code keeps nonnegative; a structure, for the thread-local
statics of the one thread. -/
structure RowSetupCache where
  /-- `last_a`, the first coordinate of the row of the last call; `-1` before the first. -/
  lastA : Int
  /-- `last_b`, the second coordinate of the row of the last call. -/
  lastB : Int
  /-- `last_d`, the step of the second coordinate whose residues `dres` holds; `0` for none. -/
  lastD : Int
  /-- `bres`, at `n`, the residue of `last_b` modulo the `n`-th sieving prime. -/
  bres : Array Nat
  /-- `dres`, at `n`, the residue of `last_d` modulo the `n`-th sieving prime. -/
  dres : Array Nat
  /-- `drow`, at `n`, the offset `dres[n] * rowlen[n]` in the sieve table of the `n`-th prime. -/
  drow : Array Nat

/-- The statics of `row_setup` when the program starts: `last_a = -1`, `last_b = 0`, `last_d = 0`,
and the zeros of static storage.

C: `j-sift.c:1111-1112` -/
def RowSetupCache.initial : RowSetupCache where
  lastA := -1
  lastB := 0
  lastD := 0
  bres := Array.replicate numPrimes 0
  dres := Array.replicate numPrimes 0
  drow := Array.replicate numPrimes 0

/-- The state of the thread that the sieve threads through the rows: the bit array `survivors`,
the rows `rowptr` of the sieve tables of the first two stages for the row in hand, the data of the
third stage (`JPoints.Row3Cache`), the statics of `row_setup` (`JPoints.RowSetupCache`), the chunk
`cur_chunk` of the last word of the tube, the counters of the survivors of the three stages, and
the output with its counter of the points found (`JPoints.Output`).

C: `j-points.c:278`, `j-points.c:281-283`, `j-sift.c:112`, `j-sift.c:776`

Deviation: an array for the bit array that `survivors` points to; indices into the sieve tables
for the pointers `rowptr[n]` into `sieve_tab[n]`; natural numbers for the counters, which start at
`0` and count up, and for the index `cur_chunk`; a structure, for the thread-local globals of the
one thread. -/
structure SiftState where
  /-- `survivors`, the bit array of the chunk of the row that is sieved. -/
  survivors : Array UInt64
  /-- `rowptr`, at `n < sieve_primes2`, the index in `sieve_tab[n]` of the row of `(a, b)`. -/
  rowptr : Array Nat
  /-- The data of the third stage. -/
  row3 : Row3Cache
  /-- The statics of `row_setup`. -/
  rowSetup : RowSetupCache
  /-- `cur_chunk`, the chunk of the word that the tube tested last. -/
  curChunk : Nat
  /-- `num_surv1`, the number of the words that reached the second stage. -/
  numSurv1 : Nat
  /-- `num_surv2`, the number of the bits that survived the second stage. -/
  numSurv2 : Nat
  /-- `num_surv3`, the number of the coprime bits that survived the third stage. -/
  numSurv3 : Nat
  /-- The output, with `total`, the number of the points found. -/
  out : Output

/-- The state of the thread when its sieve starts, for `array_size = arraySize`: the initial values
of the thread-local variables (`row3_a = -1`, `last_a = -1`, `0` for the counters and for
`cur_chunk`, the zeros and the null pointers of the others) and the empty output.

C: `j-points.c:278`, `j-points.c:281-283`, `j-sift.c:112`, `j-sift.c:776`

Deviation: a fresh array of `arraySize + VW` zeros, `VW = 1`, for the bit array that
`init_thread_sieve` allocates (memory management, not modelled), every word of which the sieve
writes before it reads it; index `0` for the null pointers of `rowptr`, which the sieve reads only
after `row_setup` has set them. -/
def SiftState.initial (arraySize : Nat) : SiftState where
  survivors := Array.replicate (arraySize + 1) 0
  rowptr := Array.replicate numPrimes 0
  row3 := Row3Cache.initial
  rowSetup := RowSetupCache.initial
  curChunk := 0
  numSurv1 := 0
  numSurv2 := 0
  numSurv3 := 0
  out := {}

/-! ### The tests for common factors -/

/-- The common value of `n` and `m` after the loop of `relprime2` and `relprime3`: while they
differ, the larger replaced by the odd part of the difference. For odd `n, m > 0`, the gcd of `n`
and `m`; for other arguments the loop that takes the odd part need not end, as in the C code.

C: `j-sift.c:309-314`, `j-sift.c:336-341`, `j-sift.c:345-350`

Deviation: one function for the three loops of the C code, which are the same on the variables
`(n, m)`, `(a, b)` and `(a, c)`, returning the value of the first; integers for the `long`s;
`x % 2 == 0` for `!(x & 1)` and `x >>> 1` for `x >>= 1`, which agree on the positive `x` of the
loop. -/
def oddGcd (n m : Int) : Id Int := do
  let mut n := n
  let mut m := m
  while n != m do
    if n > m then
      n := n - m
      n := n >>> 1
      while n % 2 == 0 do n := n >>> 1
    else
      m := m - n
      m := m >>> 1
      while m % 2 == 0 do m := m >>> 1
  return n

/-- Whether `relprime2` finds `n` and `m` coprime: for `n = 0`, whether `m = 1`; for `m = 0`,
whether `n = 1`; otherwise whether the odd parts of `n` and `m` have the gcd `1`
(`JPoints.oddGcd`). For `n, m ≥ 0` not both even, whether `gcd(n, m) = 1`; for two even `n`
and `m` it ignores their common factor `2`, which the callers rule out.

C: `j-sift.c:299-305`, `j-sift.c:315-316`

Deviation: integers for the `long`s; `x % 2 == 0` for `!(x & 1)` and `x >>> 1` for `x >>= 1`,
which agree on the positive `x` of the loops; the value of `n` after the loop, which
`JPoints.oddGcd` returns, for the value of `m` that the C code compares with `1`, the same; a
Boolean for the `int`. -/
def relprime2 (n m : Int) : Id Bool := do
  if n == 0 then return m == 1
  if m == 0 then return n == 1
  let mut n := n
  let mut m := m
  while m % 2 == 0 do m := m >>> 1
  while n % 2 == 0 do n := n >>> 1
  return (← oddGcd n m) == 1

/-- Whether `relprime3` finds `gcd(a, b, c) = 1`, for `a ≥ 0`: false when all three are even;
otherwise with `|b|` and `|c|` for `b` and `c`, by `JPoints.relprime2` when one of them is `0`,
and else by the odd parts of the three, `g` the gcd of those of `a` and `b`
(`JPoints.oddGcd`), true when `g = 1`, and otherwise whether the gcd of `g` and the odd part of
`c` is `1`.

C: `j-sift.c:319-332`, `j-sift.c:343`, `j-sift.c:351-352`

Deviation: integers for the `long`s, so that the negations of `b` and `c` are exact (the callers
pass `|b| ≤ height` and `|c| < height + 64`); the test `((a | b | c) & 1) == 0` as the conjunction
of `x % 2 == 0` for the three, which agree on every `long` in two's complement; `x % 2 == 0` for
`!(x & 1)` and `x >>> 1` for `x >>= 1`, which agree on the positive `x` of the loops; a Boolean for
the `int`. -/
def relprime3 (a b c : Int) : Id Bool := do
  if a % 2 == 0 && b % 2 == 0 && c % 2 == 0 then return false
  let mut a := a
  let mut b := b
  let mut c := c
  if b < 0 then b := -b
  if c < 0 then c := -c
  if a == 0 then return ← relprime2 b c
  if b == 0 then return ← relprime2 a c
  if c == 0 then return ← relprime2 a b
  while a % 2 == 0 do a := a >>> 1
  while b % 2 == 0 do b := b >>> 1
  while c % 2 == 0 do c := c >>> 1
  a ← oddGcd a b
  if a == 1 then return true
  return (← oddGcd a c) == 1

/-! ### The third stage -/

/-- `MOD3(x, m)`, the remainder of `x` modulo the `m`-th third-stage prime
`p = pr[sieve_primes2 + m]` without a division: `x - p q` for the quotient `q`, the high half of
the product of `x` with the reciprocal `recip3[m] = ⌈2 ^ 32 / p⌉`, both as `unsigned long`s,
shifted right by `32`. For `0 ≤ x < 2 ^ 16`, the remainder of `x` modulo `p`, in `[0, p)`.

C: `j-sift.c:104`

Deviation: the static data and `sieve_primes2` passed, for the globals that the macro reads;
integers for the `long`s `x` and `pr[…]`, with the conversion of `x` to an `unsigned long` modulo
`2 ^ 64` as C converts it; the quotient is below `2 ^ 32`, so that the conversion back to a `long`
keeps it; where `x` is an `unsigned long`, the subtraction is made modulo `2 ^ 64`, which gives
the integer for the operands of the calls, below `2 ^ 16`, whose remainder is nonnegative. -/
def mod3 (sd : SiftData) (sievePrimes2 m : Nat) (x : Int) : Int :=
  x - (sd.pr[sievePrimes2 + m]! : Int) * (((UInt64.ofInt x * sd.recip3[m]!) >>> 32).toNat : Int)

/-- The array `inva3` as `row3_setup` sets it for a new first coordinate `a`: at `m`, for the
`m`-th third-stage prime `p = pr[sieve_primes2 + m]`, the inverse of `a mod p` modulo `p` from
`inverses`, or `0` when `p ∣ a`.

C: `j-sift.c:224-228`

Deviation: the array taken and returned, for the thread-local global; the globals that it reads
passed; integers for the `long`s, with `Int.tmod` for C's `%`; the entry of `inverses` read at the
natural number of the index, which is the index for the `a ≥ 0` of the calls (for a negative `a`
the C code reads before the row of the prime); natural numbers for the indices `m` and `n`. -/
def row3SetupInverses (g : SiftGlobals) (sd : SiftData) (inva3 : Array Int) (a : Int) :
    Id (Array Int) := do
  let mut inva3 := inva3
  for m in [0:g.sievePrimes3 - g.sievePrimes2] do
    let n := g.sievePrimes2 + m
    let ap := a.tmod sd.pr[n]!
    inva3 := inva3.set! m
      (if ap == 0 then 0 else g.tables.inverses[g.pnn[n]! * maxPrimeEven + ap.toNat]!)
  return inva3

/-- The arrays `mult3` and `tab3` as `row3_setup` sets them for the second coordinate `b`, from
`inva3`: for the `m`-th third-stage prime `p = pr[n]`, `n = sieve_primes2 + m`, and `bp = b mod p`
in `[0, p)`, when `inva3[m] ≠ 0` (`p ∤ a`) the factor `1 / a` and the row of `(1, b / a)` of the
exact table of the third stage, when `p ∣ a` but `p ∤ b` the factor `1 / b` and the table of the
values of `f` that are squares (whether the curve has points at infinity modulo `p` or not), and
when `p` divides both, the factor `0` and the row `all_ones`.

C: `j-sift.c:229-245`

Deviation: the arrays taken and returned, for the thread-local globals; the globals that it reads
passed; integers for the `long`s, with `Int.tmod` for C's `%`; `JPoints.Tab3Ptr` for the pointers
of `tab3`, the indices of the rows of the tables of the curve for the addresses; natural numbers
for the indices `m`, `n` and `pn`. -/
def row3SetupFactors (g : SiftGlobals) (sd : SiftData) (inva3 mult3 : Array Int)
    (tab3 : Array Tab3Ptr) (b : Int) : Id (Array Int × Array Tab3Ptr) := do
  let mut mult3 := mult3
  let mut tab3 := tab3
  for m in [0:g.sievePrimes3 - g.sievePrimes2] do
    let n := g.sievePrimes2 + m
    let pn := g.pnn[n]!
    let p : Int := sd.pr[n]!
    let mut bp := b.tmod p
    if bp < 0 then bp := bp + p
    if inva3[m]! != 0 then
      mult3 := mult3.set! m inva3[m]!
      let r := mod3 sd g.sievePrimes2 m (bp * mult3[m]!)
      tab3 := tab3.set! m (.pointOnJ ((pn * maxPrimeEven + r.toNat) * maxPrimeEven))
    else if bp != 0 then
      mult3 := mult3.set! m g.tables.inverses[pn * maxPrimeEven + bp.toNat]!
      tab3 := tab3.set! m (.fSquare (pn * maxPrimeEven))
    else
      mult3 := mult3.set! m 0
      tab3 := tab3.set! m .allOnes
  return (mult3, tab3)

/-- The data of the third stage for the row `(a, b)` as `row3_setup` sets them from the data `r`
of the rows before: `inva3` recomputed when `a` is not `row3_a` (`JPoints.row3SetupInverses`) and
kept otherwise, then the factors and the rows (`JPoints.row3SetupFactors`), and the row recorded.

C: `j-sift.c:220-223`, `j-sift.c:246-248`

Deviation: the data taken and returned, for the thread-local globals; the globals that it reads
passed. -/
def row3Setup (g : SiftGlobals) (sd : SiftData) (r : Row3Cache) (a b : Int) : Id Row3Cache := do
  let ⟨tab3, mult3, row3A, _, inva3⟩ := r
  let inva3 ← if a != row3A then row3SetupInverses g sd inva3 a else pure inva3
  let (mult3, tab3) ← row3SetupFactors g sd inva3 mult3 tab3 b
  return { tab3, mult3, row3A := a, row3B := b, inva3 }

/-- The third stage for the bit `(a, b, c)` as `check_bit` makes it, from the data of the third
stage `row3`: the data set for the row `(a, b)` (`JPoints.row3Setup`) unless they are for it, then
for each third-stage prime `p` (the `m`-th, `pr[n]` with `n = sieve_primes2 + m`) the residue
`r = (r0[n] + res[n]) mod p` of the index `i` of the word of `c`, the class
`x = (64 r + (c & 63)) mod p` of `c`, `x` multiplied by the factor `mult3[m]` modulo `p`
(`JPoints.mod3`), and the bit rejected when the row `tab3[m]` has no entry at `x`. Whether the bit
survives every prime, and the data. Here `r0` is the index `k * npr` in `res0` of the row of the
position `k` of the word in its chunk and `res` the residues of the first word of the chunk, so
that `r0[n] + res[n] ≡ i (mod p)` when `c = 64 i + (c & 63)`.

C: `j-sift.c:254-267`

Deviation: the data taken and returned, for the thread-local globals; the globals that it reads
passed; an index into `res0` for the pointer `r0`, and the array of the chunk for the pointer
`res`; integers for the `long`s `a`, `b`, `c` and `x`, natural numbers for the residues `r` and
`j`, which the C code keeps nonnegative; `c % 64`, the remainder in `[0, 64)`, for
`c & LONG_MASK`, which agree in two's complement; a Boolean for the `int`. -/
def checkBit (g : SiftGlobals) (sd : SiftData) (row3 : Row3Cache) (a b c : Int) (r0 : Nat)
    (res : Array Nat) : Id (Bool × Row3Cache) := do
  let j := (c % (longLength : Int)).toNat
  let mut row3 := row3
  if a != row3.row3A || b != row3.row3B then row3 ← row3Setup g sd row3 a b
  for m in [0:g.sievePrimes3 - g.sievePrimes2] do
    let n := g.sievePrimes2 + m
    let p := sd.pr[n]!
    let mut r := sd.res0[r0 + n]! + res[n]!
    if r ≥ p then r := r - p
    let x := mod3 sd g.sievePrimes2 m (r * longLength + j : Nat)
    let x := mod3 sd g.sievePrimes2 m (x * row3.mult3[m]!)
    if !row3.tab3[m]!.get g.curve sd.allOnes x.toNat then return (false, row3)
  return (true, row3)

/-! ### The second stage -/

/-- The bits of the word `nums` of the index `i` in the row `(a, b)` as `check_bits` takes them, in
the state `s`: for each bit `j` that is set, from the lowest, with `c = 64 i + j`, the bit counted
in `num_surv2`, and when `gcd(a, b, c) = 1` (`JPoints.relprime3`) and the bit survives the third
stage (`JPoints.checkBit`), counted in `num_surv3` and checked exactly
(`JPoints.checkOnePoint`); true, and no bit after it taken, when the check found a point and one
point is enough (`-1`). Whether it stopped so, and the state. `r0` and `res` are those of the word
for `JPoints.checkBit`.

C: `j-sift.c:274-290`

Deviation: the state taken and returned, for the thread-local globals; the globals that it reads
passed; an index into `res0` for the pointer `r0`, and the array of the chunk for the pointer
`res`; integers for the `long`s `a`, `b`, `i` and `c`, and `c` from `i * 64` for
`i << LONG_SHIFT`, which gcc computes so also for a negative `i`, whose left shift ISO C leaves
undefined; `nums &&& 1 != 0` for `nums & 1`; a Boolean for the `int`. -/
def checkBits (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64) (a b i : Int)
    (r0 : Nat) (res : Array Nat) : Id (Bool × SiftState) := do
  let mut s := s
  let mut nums := nums
  let mut c := i * 2 ^ longShift
  while nums != 0 do
    if nums &&& 1 != 0 then
      s := { s with numSurv2 := s.numSurv2 + 1 }
      if ← relprime3 a b c then
        let (bit, row3) ← checkBit g sd s.row3 a b c r0 res
        s := { s with row3 }
        if bit then
          let out := s.out
          s := { s with numSurv3 := s.numSurv3 + 1, out := {} }
          let (found, out) ← checkOnePoint g.check out a b c
          s := { s with out }
          if found && g.check.onePoint then return (true, s)
    nums := nums >>> 1
    c := c + 1
  return (false, s)

/-- The second stage for the word `nums` of the index `i` in the row `(a, b)`, at the position `k`
in its chunk, whose first word has the residues `res`, as `check_point` makes it in the state `s`:
the word counted in `num_surv1`, then for each second-stage prime `p` (the `n`-th, for
`sieve_primes1 ≤ n < sieve_primes2`) while the word is not `0`, the residue
`r = (res0[k * npr + n] + res[n]) mod p` of `i`, and the word and-ed with word `r` of the row of
`(a, b)` of the sieve table of `p` (`rowptr[n]`); the bits that are left taken by
`JPoints.checkBits`. Whether it found a point when one point is enough (`-1`), and the state.

C: `j-sift.c:357-370`

Deviation: the state taken and returned, for the thread-local globals; the globals that it reads
passed; an index into `res0` for the pointer `r0`, the index `rowptr[n]` into `sieve_tab[n]` for
the pointer, and the array of the chunk for the pointer `res`; integers for the `long`s `a`, `b`
and `i`, natural numbers for `k`, `n` and the residue `r`, which the C code keeps nonnegative; the
test of `nums` at the head of the loop as a `break`; a Boolean for the `int`. -/
def checkPoint (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64) (a b i : Int)
    (k : Nat) (res : Array Nat) : Id (Bool × SiftState) := do
  let r0 := k * sd.npr
  let s := { s with numSurv1 := s.numSurv1 + 1 }
  let mut nums := nums
  for n in [g.sievePrimes1:g.sievePrimes2] do
    if nums == 0 then break
    let mut r := sd.res0[r0 + n]! + res[n]!
    if r ≥ sd.pr[n]! then r := r - sd.pr[n]!
    nums := nums &&& g.sieve.sieveTab[n]![s.rowptr[n]! + r]!
  if nums != 0 then return ← checkBits g sd s nums a b i r0 res
  return (false, s)

/-! ### Examples

From a test program that includes `j-sift.c` of the pin, with the globals of a curve and of its
tables set as `read_input`, `normalise_curve`, `kummer_init`, `init_fmodpsquare` and `init_table`
leave them, the sieving primes given, `init_sieve` and `init_sift` called, and then `row3_setup`,
`check_bit` and `check_point` called directly, on rows `(a, b)` in turn as the sieve takes them:
what they return, the data of the third stage, the counters, and the text that the exact check
prints. `relprime2` and `relprime3` on grids are compared by a hash, `h ↦ h * 1000003 + v` modulo
`2 ^ 64` over their values `0` and `1` in the order of the arguments, from `h = 0`. -/

-- The hash of the examples over the values `vs`.
private def hash (vs : List Bool) : UInt64 :=
  vs.foldl (fun h v ↦ h * 1000003 + if v then 1 else 0) 0

-- The integers `-n, …, n`.
private def range (n : Nat) : List Int := (List.range (2 * n + 1)).map fun (k : Nat) ↦ (k : Int) - n

-- The tables of the curve with the coefficients `cs` and the degree `d` modulo the primes
-- `primeTable[n]` for `n ∈ ns`, as `init_fmodpsquare` fills them (the coefficients reduced into
-- `[0, p)`, the points at infinity, the values of `f` that are squares, by Horner's rule) and as
-- `JPoints.initTable` fills the exact table of the third stage.
private def curveTables (t : Tables) (cs : Array Int) (d : Nat) (ns : List Nat) : CurveTables :=
  ns.foldl (init := CurveTables.initial) fun ct n ↦
    let p : Int := (primeTable[n]! : Nat)
    let cm := (List.range 7).foldl (fun a i ↦ a.set! (n * 8 + i) (cs[i]! % p)) ct.coeffsModP
    let square (x : Int) : Bool := t.squares[n * maxPrime + x.toNat]! != p
    let f (x : Nat) : Int :=
      (List.range d).reverse.foldl (fun s i ↦ (s * x + cm[n * 8 + i]!) % p) cm[n * 8 + d]!
    let ct := { ct with
      coeffsModP := cm
      hasInfinity := ct.hasInfinity.set! n (square cm[n * 8 + 6]!)
      isFSquare := (List.range p.toNat).foldl
        (fun a x ↦ a.set! (n * maxPrimeEven + x) (square (f x))) ct.isFSquare }
    (initTable t ct d n).run.1

-- The globals and the static data of the sieve for the curve `cs` of degree `d` given, the height
-- bound `H`, the value `W` of `-w` (`0` for none), `-a`, `-1`, the format of `-f`,
-- `array_size = arraySize` and the sieving primes `pnn`, `sp1` of them in the first stage, `sp2`
-- in the first two and `sp3` in all three, without the condition at 2, the static data as
-- `JPoints.initSift` computes them; and the state of the thread when its sieve starts.
private def setup (cs : Array Int) (d : Nat) (H W : Int) (all one : Bool) (fmt : String)
    (arraySize sp1 sp2 sp3 : Nat) (pnn : Array Nat) : SiftGlobals × SiftData × SiftState :=
  let t := (initMain Tables.initial).run
  let curve := (normalizeCurve cs d true).run.1
  let ct := curveTables t curve.coeffs curve.degree pnn.toList
  let check := { curve, kummer := kummerInit curve.coeffs, height := H
                 dbound := if W ≤ 0 then H else W, dbounded := W > 0 || !all, allPoints := all
                 onePoint := one, printFormat := fmt }
  let g := { tables := t, curve := ct, sieve := (initSieve t ct pnn sp2 SieveTables.initial).run
             check, arraySize, twoAdic := TwoAdic.initial, pnn, sievePrimes1 := sp1
             sievePrimes2 := sp2, sievePrimes3 := sp3
             begmask := ~~~0 <<< ((-H) % 64).toNat.toUInt64
             endmask := ~~~0 >>> ((-H - 1) % 64).toNat.toUInt64 }
  (g, (initSift g SiftData.initial).run, SiftState.initial arraySize)

-- The data of the third stage `r`, as the test program prints them.
private def row3Line (g : SiftGlobals) (r : Row3Cache) : String :=
  let k := g.sievePrimes3 - g.sievePrimes2
  let ints (vs : Array Int) : String := (vs.extract 0 k).foldl (fun s v ↦ s ++ s!" {v}") ""
  let ptr : Tab3Ptr → String
    | .null => " N" | .allOnes => " A" | .pointOnJ i => s!" J{i}" | .fSquare i => s!" F{i}"
  s!"row3 {r.row3A} {r.row3B} inva3{ints r.inva3} mult3{ints r.mult3} tab3" ++
    String.join ((r.tab3.extract 0 k).toList.map ptr) ++ "\n"

-- `JPoints.checkBit` on `(a, b, c)` for `c₀ ≤ c ≤ c₁` in turn from the data of the third stage
-- `row3`, with `r0` and `res` of the word of `c` in its chunk, as the test program prints what it
-- returns (`-` for a `c` beyond the row); and the data after it.
private def bitsLine (g : SiftGlobals) (sd : SiftData) (row3 : Row3Cache) (a b c₀ c₁ : Int) :
    String × Row3Cache :=
  let (s, row3) := (List.range (c₁ - c₀ + 1).toNat).foldl (init := ("", row3)) fun (s, row3) t ↦
    let c := c₀ + t
    let i := c >>> longShift
    match sd.chunks.find? fun ch ↦ ch.wLow ≤ i && i < ch.wHigh with
    | none => (s ++ "-", row3)
    | some ch =>
      let (bit, row3) := (checkBit g sd row3 a b c ((i - ch.wLow).toNat * sd.npr) ch.res).run
      (s ++ if bit then "1" else "0", row3)
  (s!"B {a} {b}: {s}\n", row3)

-- The state `s` with the rows of the sieve tables of the first two stages for the row `(a, b)`,
-- `a ≥ 0`, as `row_setup` sets them.
private def rowSetup (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) : SiftState :=
  { s with rowptr := (List.range numPrimes).toArray.map fun n ↦
      if n < g.sievePrimes2 then ((a % sd.pr[n]!).toNat * sd.pr[n]! + (b % sd.pr[n]!).toNat) *
        sd.rowlen[n]! else s.rowptr[n]! }

-- The word `i` of the row `(a, b)` as the test program hands it to `JPoints.checkPoint`: the mask
-- of `sift` (all bits, or the odd `c` when `a` and `b` are even), with the ends of the row and the
-- excluded `c₀ = b² / 4a` taken out.
private def rowWord (g : SiftGlobals) (sd : SiftData) (a b i : Int) : UInt64 := Id.run do
  let H := g.check.height
  let c₀ := if a != 0 && b * b % (4 * a) == 0 then b * b / (4 * a) else H + 64
  let mut nums : UInt64 := if a % 2 != 0 || b % 2 != 0 then ~~~0 else halfMask
  if i == sd.wLowAll then nums := nums &&& ((~~~0) <<< ((-H) % 64).toNat.toUInt64)
  if i == sd.wHighAll - 1 then nums := nums &&& ((~~~0) >>> ((-H - 1) % 64).toNat.toUInt64)
  if c₀ >>> longShift == i then nums := nums &&& ~~~((1 : UInt64) <<< (c₀ % 64).toNat.toUInt64)
  return nums

-- The row `(a, b)` as the test program sieves it in the state `s`: the rows of the sieve tables
-- set, then every word `i` of every chunk (`rowWord`) handed to `JPoints.checkPoint` unless it is
-- `0` (`.`), until it finds a point under `-1`; what it returns, as the test program prints it,
-- and the state.
private def rowLine (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) :
    String × SiftState := Id.run do
  let mut s := rowSetup g sd s a b
  let mut log := s!"W {a} {b}: "
  for ch in sd.chunks do
    for pos in [0:(ch.wHigh - ch.wLow).toNat] do
      let nums := rowWord g sd a b (ch.wLow + pos)
      if nums == 0 then
        log := log ++ "."
        continue
      let (r, s') := (checkPoint g sd s nums a b (ch.wLow + pos) pos ch.res).run
      s := s'
      log := log ++ if r then "1" else "0"
      if r && g.check.onePoint then return (log ++ "\n", s)
  return (log ++ "\n", s)

-- The operations `ops` of the test program in turn, from the log and the state `acc`: `T a b`
-- runs `JPoints.row3Setup` and prints the data of the third stage, `I m v` and `M m v` set
-- `inva3[m]` and `mult3[m]` to `v`, `S` prints the data, `B a b c₀ c₁` is `bitsLine`, `W a b`
-- `rowLine`, and `Q` prints the counters `num_surv1`, `num_surv2`, `num_surv3` and `total`.
private def runOps (g : SiftGlobals) (sd : SiftData) :
    List String → String × SiftState → String × SiftState
  | "T" :: a :: b :: ops, (log, s) =>
    let row3 := (row3Setup g sd s.row3 a.toInt! b.toInt!).run
    runOps g sd ops (log ++ row3Line g row3, { s with row3 })
  | "I" :: m :: v :: ops, (log, s) =>
    runOps g sd ops (log, { s with row3.inva3 := s.row3.inva3.set! m.toNat! v.toInt! })
  | "M" :: m :: v :: ops, (log, s) =>
    runOps g sd ops (log, { s with row3.mult3 := s.row3.mult3.set! m.toNat! v.toInt! })
  | "S" :: ops, (log, s) => runOps g sd ops (log ++ row3Line g s.row3, s)
  | "B" :: a :: b :: c₀ :: c₁ :: ops, (log, s) =>
    let (l, row3) := bitsLine g sd s.row3 a.toInt! b.toInt! c₀.toInt! c₁.toInt!
    runOps g sd ops (log ++ l, { s with row3 })
  | "W" :: a :: b :: ops, (log, s) =>
    let (l, s) := rowLine g sd s a.toInt! b.toInt!
    runOps g sd ops (log ++ l, s)
  | "Q" :: ops, (log, s) =>
    runOps g sd ops (log ++ s!"Q {s.numSurv1} {s.numSurv2} {s.numSurv3} {s.out.total}\n", s)
  | _, acc => acc

-- `relprime2` on `0 ≤ n, m ≤ 40` and `relprime3` on `0 ≤ a ≤ 12`, `-12 ≤ b, c ≤ 12`, by their
-- hashes.
#guard hash ((List.range 41).flatMap fun (n : Nat) ↦ (List.range 41).map fun (m : Nat) ↦
    (relprime2 n m).run) ==
  5401492496658222322
#guard hash ((List.range 13).flatMap fun (a : Nat) ↦ (range 12).flatMap fun b ↦
  (range 12).map fun c ↦ (relprime3 a b c).run) == 16753479931520880571

-- The same grids against the gcd, independent of the C code: `relprime2` where `n` and `m` are not
-- both even, `relprime3` everywhere.
#guard (List.range 41).all fun (n : Nat) ↦ (List.range 41).all fun (m : Nat) ↦
  n % 2 == 0 && m % 2 == 0 || (relprime2 n m).run == (Nat.gcd n m == 1)
#guard (List.range 13).all fun (a : Nat) ↦ (range 12).all fun b ↦ (range 12).all fun c ↦
  (relprime3 a b c).run == (Int.gcd (Int.gcd a b) c == 1)

-- `relprime3` and `relprime2` at the bounds of the coordinates (`MAX_HEIGHT` and above it), at
-- zeros, at powers of `2`, and `relprime2` on even arguments, where it ignores their factor `2`.
#guard [(3037000499, 3037000498, 3037000562), (3037000499, 0, 3037000499),
    (0, 3037000499, -3037000562), (0, 1, 0), (0, 0, 1), (0, 0, -1), (1, 0, 0), (0, 2, 1), (0, 2, 4),
    (0, 4, 6), (0, 0, 3), (2, -4, 6), (2, -4, 7), (6, 10, 15), (6, 10, 14), (30, -42, 70),
    (30, -42, 71), (1024, 0, -3), (1024, -2048, 4096), (1024, -2047, 4096), (2147483648, 3, 0),
    (4294967296, -4294967297, 8589934592), (9, 15, -21), (9, 15, -22),
    (3037000499, -2147483648, 1073741824), (123456789, 987654321, -555555555), (7, 7, 7), (7, 7, 0),
    (1, 1, 1), (2, 2, 2), (0, 5, -10), (0, -5, 10), (12, -18, 0)].map
      (fun (a, b, c) ↦ if (relprime3 a b c).run then '1' else '0') ==
  "101111110000110011011101100010000".toList
#guard [(0, 1), (1, 0), (0, 0), (0, 2), (2, 0), (2, 2), (4, 6), (6, 9), (12, 18), (3, 9), (9, 3),
    (1, 1), (4611686018427387904, 3), (4611686018427387904, 4611686018427387904),
    (3037000499, 3037000498), (6074000998, 3037000499), (35, 21), (35, 22), (64, 81), (81, 64)].map
      (fun (n, m) ↦ if (relprime2 n m).run then '1' else '0') ==
  "11000110000111100111".toList

-- `MOD3` is the remainder for `0 ≤ x < 2 ^ 16` at the third-stage primes `3`, `127` and `251`,
-- independent of the C code.
#guard
  let (_, sd, _) := setup #[1, 178, 817, -274, 16, 1, 0] 5 100 0 false false "" 2 0 0 3 #[0, 29, 52]
  (List.range 3).all fun m ↦ (List.range (2 ^ 16)).all fun (x : Nat) ↦
    mod3 sd 0 m x == x % sd.pr[m]!

-- The quintic of example 2 of the README of `j-points`, at `H = 100` with three words to a chunk
-- (two chunks), the sieving primes `5` (the first stage), `3, 7` (the second) and `11, 13, 251`
-- (the third): `row3_setup` on new and old rows and on `inva3` and `mult3` changed by hand, which
-- shows on which rows it keeps `inva3`, `check_bit` along two rows, `check_point` on rows of
-- every kind (`a = 0`, `a` and `b` even, the excluded `c₀`, the third-stage primes dividing `a`,
-- or `a` and `b`), and the counters.
#guard
  let (g, sd, s) := setup #[1, 178, 817, -274, 16, 1, 0] 5 100 0 false false
    "(%ld, %ld, %ld, %ld)\n" 3 1 3 6 #[1, 0, 2, 3, 4, 52]
  let (log, s) := runOps g sd ("S T 1 2 B 1 2 -100 100 T 1 3 I 0 2 T 1 4 T 2 4 M 1 3 S \
    B 2 4 -20 20 W 0 0 W 0 1 W 1 -3 W 1 -2 W 1 0 W 1 2 W 2 -3 W 2 0 W 13 0 W 13 1 W 11 -5 \
    Q".splitOn " ") ("", s)
  log == "row3 -1 0 inva3 0 0 0 mult3 0 0 0 tab3 N N N\nrow3 1 2 inva3 1 1 1 mult3 1 1 1 tab3 \
    J197120 J262656 J3408384\nB 1 2: 01100000100010000000000110001000001010010000001000000100010100\
    01100000001001001000010000010110001000010100100000001011010000010001100000000010000000001100000\
    00001000010010000000100000010000010010100000\nrow3 1 3 inva3 1 1 1 mult3 1 1 1 tab3 J197376 \
    J262912 J3408640\nrow3 1 4 inva3 2 1 1 mult3 2 1 1 tab3 J198656 J263168 J3408896\n\
    row3 2 4 inva3 6 7 126 mult3 6 7 126 tab3 J197120 J262656 J3408384\n\
    row3 2 4 inva3 6 7 126 mult3 6 3 126 tab3 J197120 J262656 J3408384\n\
    B 2 4: 00101000110010000000011000100000000000000\nW 0 0: 0000\nW 0 1: 0000\nW 1 -3: 0000\n\
    W 1 -2: 0000\nW 1 0: 0000\nW 1 2: 0000\nW 2 -3: 0000\nW 2 0: 0000\nW 13 0: 0000\nW 13 1: 0000\n\
    W 11 -5: 0000\nQ 44 813 133 6\n" &&
    s.out.text == "(0, 1, -9, 81)\n(0, 1, -6, 36)\n(0, 1, -2, 4)\n(0, 1, 0, 0)\n(0, 1, 4, 16)\n\
    (1, -2, 0, -52)\n"

-- The sextic `1 + 4 x + 3 x² - 8 x³ + 2 x⁴ + 8 x⁵ + 7 x⁶` under `-a` and `-1` at `H = 30` (one
-- chunk), with no prime in the first stage, `3, 7` in the second and `5, 11, 61` in the third, none
-- of which has points at infinity: `check_point` on rows until the first point, and `row3_setup`
-- and `check_bit` on rows `(0, b)`, where the third stage reads the values of `f` that are squares
-- whether there are points at infinity or not, and on rows where the primes divide `a`, `b` or
-- both.
#guard
  let (g, sd, s) := setup #[1, 4, 3, -8, 2, 8, 7] 6 30 0 true true "(%ld, %ld, %ld, %ld)\n" 2 0 2
    5 #[0, 2, 1, 3, 16]
  let (log, s) := runOps g sd ("W 0 1 W 1 -2 W 1 -1 W 1 0 W 7 6 W 2 -1 W 1 2 Q T 0 1 S \
    B 0 1 -64 63 T 5 2 B 5 2 -64 63 T 0 0 T 61 0 T 61 5 T 3 61".splitOn " ") ("", s)
  log == "W 0 1: 00\nW 1 -2: 00\nW 1 -1: 01\nW 1 0: 00\nW 7 6: 1\nW 2 -1: 00\nW 1 2: 00\n\
    Q 13 98 16 2\nrow3 0 1 inva3 0 0 0 mult3 1 1 1 tab3 F256 F768 F4096\n\
    row3 0 1 inva3 0 0 0 mult3 1 1 1 tab3 F256 F768 F4096\nB 0 1: \
    00010000000000000000000100001000010000010000000010000000000100011000000000000000000100000100001\
    000000001000010000100000000001000\nrow3 5 2 inva3 0 9 49 mult3 3 9 49 tab3 F256 J198400 \
    J1058048\nB 5 2: 001000000000100000000000000001000000000000000000000000000000000000000000000000\
    00001000010100100000000000000000001000000000000000\nrow3 0 0 inva3 0 0 0 mult3 0 0 0 tab3 A A \
    A\nrow3 61 0 inva3 1 2 0 mult3 1 2 0 tab3 J65536 J196608 A\n\
    row3 61 5 inva3 1 2 0 mult3 1 2 49 tab3 J65536 J199168 F4096\n\
    row3 3 61 inva3 2 4 41 mult3 2 4 41 tab3 J66048 J197120 J1048576\n" &&
    s.out.text == "(1, -1, 0, 4)\n(7, 6, -9, -74)\n"

end JPoints

end
