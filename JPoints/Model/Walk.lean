/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Sift

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Sift

/-!
# The first stage of the sieve and the sieve of a row

The sieve of `j-points` on a row `(a, b)` of the box: the rows of the sieve tables of the primes of
the first two stages for `(a, b)` (`row_setup`, `JPoints.rowSetup`), which it advances from one row
to the next of the same `a` by the step of `b` and computes by division otherwise; and for each
chunk of the row (`sift0`, `JPoints.sift0`) the bit array filled with the mask of the row and the
pattern of the first first-stage prime in one pass, the bits of the ends of the row and of the
excluded third coordinate taken out, the patterns of the other first-stage primes and-ed in, each
by a walk through the row of its sieve table (`WALK`, `JPoints.walk`), and the words that are left
handed to the second stage (`scan_words`, `JPoints.scanWords`). `sift` (`JPoints.sift`) sieves a
row of the box, every chunk whole; `sift_range` (`JPoints.siftRange`) sieves a range of words of a
chunk, a range of the real region, with walks that start inside the chunk (`walk_parts`,
`JPoints.walkParts`).

## Main definitions

* `JPoints.andOp`, `JPoints.fillOp`: the operations of the walks.
* `JPoints.walkWords`, `JPoints.walk`: the walk of a first-stage prime over words of the bit array.
* `JPoints.walkParts`: the walk of a first-stage prime over a range of words of a chunk.
* `JPoints.scanWords`: the words of the bit array handed to the second stage.
* `JPoints.sift0Fill`, `JPoints.sift0Masks`, `JPoints.sift0`: the sieve of a whole chunk.
* `JPoints.siftRangeFill`, `JPoints.siftRangeMasks`, `JPoints.siftRange`: the sieve of a range of
  words of a chunk.
* `JPoints.rowSetupAddSmall`, `JPoints.rowSetupResidues`, `JPoints.rowSetupAddResidues`,
  `JPoints.rowSetupDivide`, `JPoints.rowSetup`: the rows of the sieve tables for a row `(a, b)`.
* `JPoints.siftMask`: the excluded third coordinate and the mask of a row.
* `JPoints.sift`: the sieve of a row of the box.

## Implementation notes

The sieve reads the globals and the static data of `JPoints.Model.Sift` (`JPoints.SiftGlobals`,
`JPoints.SiftData`), which are passed, and writes the state of the thread (`JPoints.SiftState`),
which is taken and returned. The pointers of the C code into the bit array and into the sieve
tables are indices; the pointer to a chunk is the chunk, read from the array of the chunks. The
macro `WALK` and its operations `AND_OP` and `FILL_OP` are functions, with the variables of the
function in which the macro is expanded passed; the parts of a walk that `walk_parts` returns
through its arguments are a `JPoints.WalkSpec`. The model is that of the scalar walk, `VW = 1`.

`JPoints.sift0` and `JPoints.siftRange` take the bit array out of the state while the walks write
it, so that it is not shared and the compiled code writes it in place.
-/

@[expose] public section

namespace JPoints

/-! ### The walk -/

/-- `AND_OP(d, s)`, the operation of the passes of the first-stage primes after the first: the word
`d` of the bit array and-ed with the word `s` of the row of the sieve table.

C: `j-sift.c:936`

Deviation: the value returned, for the assignment `d &= s` of the macro, which `JPoints.walkWords`
stores in the word of the bit array. -/
def andOp (d s : UInt64) : UInt64 := d &&& s

/-- `FILL_OP(d, s)`, the operation of the pass of the first first-stage prime, merged with the fill
of the bit array: the word of the bit array, whatever it holds, set to the mask `mask` of the row
and-ed with the word `s` of the row of the sieve table.

C: `j-sift.c:937`

Deviation: the mask passed, for the local variable of the function in which the macro is expanded;
the value returned, for the assignment to the word `d` of the macro, which `JPoints.walkWords`
stores, and the old value of `d` an argument that it does not read, so that both operations have the
type of the operation that `JPoints.walk` takes. -/
def fillOp (mask _d s : UInt64) : UInt64 := mask &&& s

/-- The `cnt` steps of a loop of `WALK` from word `surv` of the bit array `survivors` and word
`siv1` of the table `tab` on: in each, the word of the bit array set to `op` of it and the word of
the table, and both moved on by one word. The bit array and the two indices after them.

C: `j-sift.c:923`, `j-sift.c:929`, `j-sift.c:933`

Deviation: one function for the three loops of the macro, which are the same on their counts `hd`,
`p` and `tl`: the loop `do … while(siv1 != siv0)`, which starts at `siv1 = siv0 - p` and moves
`siv1` on by one word, runs `p` times; the loops `for(j = hd; j; j--)` and `for( ; j; j--)`, whose
counter the body does not read, over `cnt` steps; indices for the pointers `surv` and `siv1`, and
the table that `siv1` points into passed; natural numbers for the counts. -/
def walkWords (tab survivors : Array UInt64) (surv siv1 cnt : Nat)
    (op : UInt64 → UInt64 → UInt64) : Id (Array UInt64 × Nat × Nat) := do
  let mut survivors := survivors
  let mut surv := surv
  let mut siv1 := siv1
  for _ in [0:cnt] do
    survivors := survivors.set! surv (op survivors[surv]! tab[siv1]!)
    surv := surv + 1
    siv1 := siv1 + 1
  return (survivors, surv, siv1)

/-- `WALK(OP)`, the pass of the `n`-th first-stage prime `p` with the walk `w` and the operation
`op` over the words of the bit array `survivors` from `surv0` on, in the row of `(a, b)` of its
sieve table, from the index `rowptr[n]` in `sieve_tab[n]` on (`JPoints.walkWords`): the `head` words
from word `first` of the row on, then `nper` times the words `0, …, p - 1` of the row, and then its
words `0, …, tail - 1`. When `first + head = p`, as `JPoints.initSiftWalk` and `JPoints.walkParts`
make it unless `nper = tail = 0`, word `t` of the pass reads word `(first + t) mod p` of the row.

C: `j-sift.c:918-922`, `j-sift.c:924-928`, `j-sift.c:930-932`, `j-sift.c:934-935`

Deviation: a function for the macro, the variables that it reads of the function in which it is
expanded passed (the bit array and the rows `rowptr` of the state, `surv0`, `n`, `p`, and `f1`,
`hd`, `np` and `tl` as the walk `w`), and the bit array returned; the operation an argument; indices
into the bit array and into `sieve_tab[n]` for the pointers `surv` and `siv1`, without the pointer
`siv0`, at which the loop over a period ends after `p` words (`JPoints.walkWords`); the loop
`for(j = np; j; j--)`, whose counter the body does not read, over `nper` steps, and the test
`if((j = tl))`, which sets the counter of the tail, as `tail ≠ 0`; natural numbers for the counts;
the arm `VW == 1` of the preprocessor. -/
def walk (g : SiftGlobals) (rowptr : Array Nat) (survivors : Array UInt64) (surv0 n p : Nat)
    (w : WalkSpec) (op : UInt64 → UInt64 → UInt64) : Id (Array UInt64) := do
  let tab := g.sieve.sieveTab[n]!
  let mut (survivors, surv, siv1) ← walkWords tab survivors surv0 (rowptr[n]! + w.first) w.head op
  for _ in [0:w.nper] do
    (survivors, surv, siv1) ← walkWords tab survivors surv (siv1 - p) p op
  if w.tail != 0 then
    (survivors, surv, siv1) ← walkWords tab survivors surv (siv1 - p) w.tail op
  return survivors

/-- `walk_parts`, the walk of the `n`-th first-stage prime `p` over the words `off ≤ i < off + len`
of a chunk, positions in it, from the walk `w` of the prime over the whole chunk, without a
division: the word `f = first + res0[off * npr + n]` of the row that the range begins with, reduced
into `[1, p]`; the head `h = min(p - f, len)`; the tail `r = res0[rem * npr + n] = rem mod p` of the
`rem = len - h` words after the head; and the number of full periods
`(long)((double)(rem - r) * invp[n] + 0.5)`, which is `(rem - r) / p` since `p ∣ rem - r`.

C: `j-sift.c:899-910`, `j-sift.c:916-917`

Deviation: the parts returned as a walk, for the arguments `f1`, `hd`, `np` and `tl` through which
the C code returns them; the walk passed, for the pointer `w`; the static data that it reads passed;
natural numbers for the nonnegative `long`s; `JPoints.Double.ofInt` for the exact conversion of
`rem - r` to a double, the operations of the doubles of `JPoints.Model.DoubleArith`, and
`JPoints.Double.toInt64` for the conversion back to a `long`, which truncates; the arm `VW == 1` of
the test of the constant `VW`. -/
def walkParts (sd : SiftData) (n p : Nat) (w : WalkSpec) (off len : Nat) : Id WalkSpec := do
  let mut f := w.first + sd.res0[off * sd.npr + n]!
  if f > p then f := f - p
  let mut h := p - f
  if h > len then h := len
  let rem := len - h
  let r := sd.res0[rem * sd.npr + n]!
  let np := (Double.ofInt (rem - r : Nat) * sd.invp[n]! + 0.5).toInt64.toInt
  return { first := f, head := h, nper := np.toNat, tail := r }

/-! ### The words that go on to the second stage -/

/-- `scan_words`, the second stage for the words of the positions `lo ≤ i < hi` of the chunk `ch` of
the row `(a, b)` in the state `s`: each word of the bit array that is not `0` handed to
`JPoints.checkPoint` with its index `w_low + i` in the row and its position `i`, until one finds a
point when one point is enough (`-1`). Whether it stopped so, and the state.

C: `j-sift.c:963-973`, `j-sift.c:993-994`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; the chunk passed, for the pointer `ch`; an index into the bit array for
the pointer `surv`; integers for the `long`s `a` and `b`, natural numbers for the positions; the arm
`VW == 1` of the preprocessor; a Boolean for the `int`. -/
def scanWords (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) (ch : ChunkSpec)
    (lo hi : Nat) : Id (Bool × SiftState) := do
  let mut s := s
  let mut surv := lo
  for i in [lo:hi] do
    let nums := s.survivors[surv]!
    surv := surv + 1
    if nums != 0 then
      let (found, s') ← checkPoint g sd s nums a b (ch.wLow + i) i ch.res
      s := s'
      if found && g.check.onePoint then return (true, s)
  return (false, s)

/-! ### The sieve of a chunk -/

/-- The fill of `sift0` with the mask `mask` for the chunk `ch` of `range` words, in the bit array
`survivors` from `surv0` on, with the rows `rowptr`: without first-stage primes, each word of the
chunk set to the mask; otherwise the pass of the first one with its walk over the chunk
(`JPoints.walk`, `JPoints.fillOp`). The bit array, and the first-stage prime to go on with, `0` or
`1`.

C: `j-sift.c:1012-1025`

Deviation: the bit array and the variable `n` of `sift0` returned, for the bit array that the C code
writes and the local variable; the globals and the static data that it reads passed, and the rows
`rowptr` of the state, for the thread-local global; the chunk passed, for the pointer `ch`; an index
for the pointer `surv`; the loop `for(i = range; i; i--)`, whose counter the body does not read,
over `range` steps; natural numbers for the counts and for `n`. -/
def sift0Fill (g : SiftGlobals) (sd : SiftData) (rowptr : Array Nat) (survivors : Array UInt64)
    (ch : ChunkSpec) (surv0 range : Nat) (mask : UInt64) : Id (Array UInt64 × Nat) := do
  let mut survivors := survivors
  let mut n := 0
  if g.sievePrimes1 == 0 then
    let mut surv := surv0
    for _ in [0:range] do
      survivors := survivors.set! surv mask
      surv := surv + 1
    n := 0
  else
    let p := sd.pr[0]!
    let w := ch.walk[0]!
    n := 0
    survivors ← walk g rowptr survivors surv0 n p w (fillOp mask)
    n := 1
  return (survivors, n)

/-- The masks of `sift0` for the `k`-th chunk `ch` of `range` words, in the bit array `survivors`:
on the first chunk its first word and-ed with `begmask`, on the last chunk its last word with
`endmask`, and the bit of the excluded third coordinate `c0` cleared when its word lies in the
chunk.

C: `j-sift.c:1026-1029`

Deviation: the bit array taken and returned; the globals and the static data that it reads passed;
the chunk passed, for the pointer `ch`; integers for the `long` `c0` and the index of its word,
`c0 % 64`, in `[0, 64)`, for `c0 & LONG_MASK`, the same in two's complement; natural numbers for `k`
and `range`. -/
def sift0Masks (g : SiftGlobals) (sd : SiftData) (survivors : Array UInt64) (ch : ChunkSpec)
    (k range : Nat) (c0 : Int) : Id (Array UInt64) := do
  let mut survivors := survivors
  if k == 0 then survivors := survivors.set! 0 (survivors[0]! &&& g.begmask)
  if k == sd.numChunks - 1 then
    survivors := survivors.set! (range - 1) (survivors[range - 1]! &&& g.endmask)
  if ch.wLow ≤ c0 >>> longShift && c0 >>> longShift < ch.wHigh then
    let i := (c0 >>> longShift - ch.wLow).toNat
    survivors := survivors.set! i
      (survivors[i]! &&& ~~~((1 : UInt64) <<< (c0 % (longLength : Int)).toNat.toUInt64))
  return survivors

/-- `sift0`, the sieve of the `k`-th chunk of the row `(a, b)`, whole, with the mask `mask` of the
row and the excluded third coordinate `c0`, in the state `s`: the fill with the pass of the first
first-stage prime (`JPoints.sift0Fill`), the masks (`JPoints.sift0Masks`), the passes of the other
first-stage primes with their walks over the chunk (`JPoints.walk`, `JPoints.andOp`), and the words
of the chunk handed to the second stage (`JPoints.scanWords`). Whether it found a point when one
point is enough (`-1`), and the state.

C: `j-sift.c:1001-1005`, `j-sift.c:1034-1039`, `j-sift.c:1045-1046`

Deviation: the state taken and returned, for the thread-local globals, its bit array taken out of it
while the passes write it; the globals and the static data that it reads passed; the chunk read from
the array of the chunks, for the pointer `ch`; index `0` for the pointer `surv0`; the walks passed
whole, for the copies of their fields in `f1`, `hd`, `np` and `tl`; integers for the `long`s `a`,
`b` and `c0`, natural numbers for `k`, `range` and `n`; a Boolean for the `int`. -/
def sift0 (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) (k : Nat) (mask : UInt64)
    (c0 : Int) : Id (Bool × SiftState) := do
  let ch := sd.chunks[k]!
  let range := (ch.wHigh - ch.wLow).toNat
  let surv0 := 0
  let survivors := s.survivors
  let s := { s with survivors := #[] }
  let (survivors, n) ← sift0Fill g sd s.rowptr survivors ch surv0 range mask
  let mut survivors ← sift0Masks g sd survivors ch k range c0
  for n in [n:g.sievePrimes1] do
    survivors ← walk g s.rowptr survivors surv0 n sd.pr[n]! ch.walk[n]! andOp
  scanWords g sd { s with survivors } a b ch 0 range

/-! ### The sieve of a range of words -/

/-- The fill of `sift_range` with the mask `mask` for the words `off ≤ i < off + len` of the chunk
`ch`, in the bit array `survivors` from `surv0 = off` on, with the rows `rowptr`: without
first-stage primes, each word of the range set to the mask; otherwise the pass of the first one
with its walk over the range (`JPoints.walkParts`, `JPoints.walk`, `JPoints.fillOp`). The bit array,
and the first-stage prime to go on with, `0` or `1`.

C: `j-sift.c:1072-1085`

Deviation: the bit array and the variable `n` of `sift_range` returned, for the bit array that the C
code writes and the local variable; the globals and the static data that it reads passed, and the
rows `rowptr` of the state, for the thread-local global; the chunk passed, for the pointer `ch`; an
index for the pointer `surv`; the parts of the walk as a walk, for the variables `f1`, `hd`, `np`
and `tl`; the loop `for(i = len; i; i--)`, whose counter the body does not read, over `len` steps;
natural numbers for the counts and for `n`. -/
def siftRangeFill (g : SiftGlobals) (sd : SiftData) (rowptr : Array Nat)
    (survivors : Array UInt64) (ch : ChunkSpec) (surv0 off len : Nat) (mask : UInt64) :
    Id (Array UInt64 × Nat) := do
  let mut survivors := survivors
  let mut n := 0
  if g.sievePrimes1 == 0 then
    let mut surv := surv0
    for _ in [0:len] do
      survivors := survivors.set! surv mask
      surv := surv + 1
    n := 0
  else
    let p := sd.pr[0]!
    let w := ch.walk[0]!
    n := 0
    survivors ← walk g rowptr survivors surv0 n p (← walkParts sd n p w off len) (fillOp mask)
    n := 1
  return (survivors, n)

/-- The masks of `sift_range` for the words `off ≤ i < off + len` of the `k`-th chunk of `range`
words, in the bit array `survivors`: when the range begins the row, its first word and-ed with
`begmask`; when it ends the row, the last word of the chunk with `endmask`; and the bit of the
excluded third coordinate `c0` cleared when its word `cw`, as a position in the chunk, lies in the
range.

C: `j-sift.c:1087-1089`

Deviation: the bit array taken and returned; the globals and the static data that it reads passed;
integers for the `long`s `c0` and `cw`, `c0 % 64`, in `[0, 64)`, for `c0 & LONG_MASK`, the same in
two's complement; natural numbers for `k`, `range`, `off` and `len`. -/
def siftRangeMasks (g : SiftGlobals) (sd : SiftData) (survivors : Array UInt64)
    (k range off len : Nat) (cw c0 : Int) : Id (Array UInt64) := do
  let mut survivors := survivors
  if k == 0 && off == 0 then survivors := survivors.set! 0 (survivors[0]! &&& g.begmask)
  if k == sd.numChunks - 1 && off + len ≥ range then
    survivors := survivors.set! (range - 1) (survivors[range - 1]! &&& g.endmask)
  if (off : Int) ≤ cw && cw < (off + len : Nat) then
    survivors := survivors.set! cw.toNat
      (survivors[cw.toNat]! &&& ~~~((1 : UInt64) <<< (c0 % (longLength : Int)).toNat.toUInt64))
  return survivors

/-- `sift_range`, the sieve of the words `lo ≤ i < hi` of the `k`-th chunk of the row `(a, b)`, a
range of the real region, with the mask `mask` of the row and the excluded third coordinate `c0`,
in the state `s`: for the position `off = lo - w_low` of the range in the chunk and its length
`len = hi - lo`, the fill with the pass of the first first-stage prime (`JPoints.siftRangeFill`),
the masks (`JPoints.siftRangeMasks`), the passes of the other first-stage primes with their walks
over the range (`JPoints.walkParts`, `JPoints.walk`, `JPoints.andOp`), and the words of the range
handed to the second stage (`JPoints.scanWords`). Whether it found a point when one point is
enough (`-1`), and the state.

C: `j-sift.c:1053-1058`, `j-sift.c:1070`, `j-sift.c:1093-1098`, `j-sift.c:1104-1105`

Deviation: the state taken and returned, for the thread-local globals, its bit array taken out of it
while the passes write it; the globals and the static data that it reads passed; the chunk read from
the array of the chunks, for the pointer `ch`; the index `off` for the pointer `surv0`; integers for
the `long`s `a`, `b`, `lo`, `hi`, `c0` and `cw`, and natural numbers for `k`, `range`, `off`, `len`,
`lo0`, `hi0` and `n`, which the C code keeps nonnegative; the parts of a walk as a walk, for the
variables `f1`, `hd`, `np` and `tl`; a Boolean for the `int`. -/
def siftRange (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) (k : Nat)
    (lo hi : Int) (mask : UInt64) (c0 : Int) : Id (Bool × SiftState) := do
  let ch := sd.chunks[k]!
  let range := (ch.wHigh - ch.wLow).toNat
  let off := (lo - ch.wLow).toNat
  let len := (hi - lo).toNat
  let lo0 := off
  let hi0 := off + len
  let cw := (c0 >>> longShift) - ch.wLow
  let surv0 := off
  let survivors := s.survivors
  let s := { s with survivors := #[] }
  let (survivors, n) ← siftRangeFill g sd s.rowptr survivors ch surv0 off len mask
  let mut survivors ← siftRangeMasks g sd survivors k range off len cw c0
  for n in [n:g.sievePrimes1] do
    let p := sd.pr[n]!
    survivors ← walk g s.rowptr survivors surv0 n p (← walkParts sd n p ch.walk[n]! off len) andOp
  scanWords g sd { s with survivors } a b ch lo0 hi0

/-! ### The rows of the sieve tables for a row -/

/-- The step of `row_setup` by `0 < d < 3` from the last row to `(a, last_b + d)`: for the `n`-th
sieving prime `p` of the first two stages, the residue `bres[n]` of the second coordinate and the
row `rowptr[n]` of the sieve table moved on by `d` and by `d` rows, and back by `p` and by the `p`
rows of a block when the residue reaches `p`.

C: `j-sift.c:1120-1124`

Deviation: the rows and the residues taken and returned, for the thread-local global `rowptr` and
the static `bres`; the globals and the static data that it reads passed; indices into
`sieve_tab[n]` for the pointers `rowptr[n]`; natural numbers for `d` and the residues. -/
def rowSetupAddSmall (g : SiftGlobals) (sd : SiftData) (rowptr bres : Array Nat) (d : Nat) :
    Id (Array Nat × Array Nat) := do
  let mut rowptr := rowptr
  let mut bres := bres
  for n in [0:g.sievePrimes2] do
    bres := bres.set! n (bres[n]! + d)
    rowptr := rowptr.set! n (rowptr[n]! + d * sd.rowlen[n]!)
    if bres[n]! ≥ sd.pr[n]! then
      bres := bres.set! n (bres[n]! - sd.pr[n]!)
      rowptr := rowptr.set! n (rowptr[n]! - sd.blocklen[n]!)
  return (rowptr, bres)

/-- The residues of the step `d > 0` that `row_setup` keeps, for a step that is not the last one:
for the `n`-th sieving prime `p` of the first two stages, `dres[n] = d mod p`, computed for `d ≥ p`
as `r = d - p * (long)((double)d * invp[n])` and one correction each way, and the offset
`drow[n] = dres[n] * rowlen[n]` of the rows of the sieve table.

C: `j-sift.c:1129-1138`

Deviation: the residues and the offsets taken and returned, for the statics; the globals and the
static data that it reads passed; integers for the `long`s `d`, `p` and `r`, and natural numbers
for the residues and the offsets that the C code stores, the residue `r` in `[0, p)` after the
corrections; `JPoints.Double.ofInt` for the exact conversion of `d` to a double, the product of
`JPoints.Model.DoubleArith`, and `JPoints.Double.toInt64` for the conversion back to a `long`,
which truncates. -/
def rowSetupResidues (g : SiftGlobals) (sd : SiftData) (dres drow : Array Nat) (d : Int) :
    Id (Array Nat × Array Nat) := do
  let mut dres := dres
  let mut drow := drow
  for n in [0:g.sievePrimes2] do
    let p : Int := sd.pr[n]!
    let mut r := d
    if r ≥ p then
      r := d - p * (Double.ofInt d * sd.invp[n]!).toInt64.toInt
      if r ≥ p then r := r - p
      if r < 0 then r := r + p
    dres := dres.set! n r.toNat
    drow := drow.set! n (r.toNat * sd.rowlen[n]!)
  return (dres, drow)

/-- The step of `row_setup` by `d = last_d ≥ 1` with its residues `dres` and offsets `drow`: for the
`n`-th sieving prime `p` of the first two stages, the residue `bres[n]` of the second coordinate and
the row `rowptr[n]` of the sieve table moved on by `dres[n]` and by `drow[n]`, and back by `p` and
by the `p` rows of a block when the residue reaches `p`.

C: `j-sift.c:1141-1145`

Deviation: the rows and the residues taken and returned, for the thread-local global `rowptr` and
the static `bres`; the globals and the static data that it reads passed; indices into
`sieve_tab[n]` for the pointers `rowptr[n]`; natural numbers for the residues and the offsets. -/
def rowSetupAddResidues (g : SiftGlobals) (sd : SiftData) (rowptr bres dres drow : Array Nat) :
    Id (Array Nat × Array Nat) := do
  let mut rowptr := rowptr
  let mut bres := bres
  for n in [0:g.sievePrimes2] do
    bres := bres.set! n (bres[n]! + dres[n]!)
    rowptr := rowptr.set! n (rowptr[n]! + drow[n]!)
    if bres[n]! ≥ sd.pr[n]! then
      bres := bres.set! n (bres[n]! - sd.pr[n]!)
      rowptr := rowptr.set! n (rowptr[n]! - sd.blocklen[n]!)
  return (rowptr, bres)

/-- The rows of the sieve tables of the row `(a, b)` by division, as `row_setup` computes them on a
new `a` or a `b` not above the last one: for the `n`-th sieving prime `p` of the first two stages,
the residue `bp = b mod p`, in `[0, p)`, in `bres[n]`, and the row of `(a mod p, bp)` of the sieve
table, from the index `(ap * p + bp) * rowlen[n]` of `sieve_tab[n]` on, in `rowptr[n]`.

C: `j-sift.c:1148-1153`

Deviation: the rows and the residues taken and returned, for the thread-local global `rowptr` and
the static `bres`; the globals and the static data that it reads passed; integers for the `long`s,
with `Int.tmod` for C's `%`; the index into `sieve_tab[n]` for the pointer `rowptr[n]`, a natural
number, which is the index for the `a ≥ 0` of the calls; a natural number for the residue `bp`. -/
def rowSetupDivide (g : SiftGlobals) (sd : SiftData) (rowptr bres : Array Nat) (a b : Int) :
    Id (Array Nat × Array Nat) := do
  let mut rowptr := rowptr
  let mut bres := bres
  for n in [0:g.sievePrimes2] do
    let p : Int := sd.pr[n]!
    let ap := a.tmod p
    let mut bp := b.tmod p
    if bp < 0 then bp := bp + p
    bres := bres.set! n bp.toNat
    rowptr := rowptr.set! n ((ap * p + bp) * sd.rowlen[n]!).toNat
  return (rowptr, bres)

/-- `row_setup`, the rows of the sieve tables of the primes of the first two stages for the row
`(a, b)` in the state `s`, from those of the last row `(last_a, last_b)`: for the same `a` and the
step `d = b - last_b`, moved on by `d` when `0 < d < 3` (`JPoints.rowSetupAddSmall`), and by the
residues of `d`, computed when `d` is not the last step `last_d` (`JPoints.rowSetupResidues`), when
`d ≥ 3` (`JPoints.rowSetupAddResidues`); otherwise computed by division (`JPoints.rowSetupDivide`),
and `last_d` cleared. Then `(a, b)` recorded as the last row.

C: `j-sift.c:1113-1114`, `j-sift.c:1117-1119`, `j-sift.c:1125-1128`, `j-sift.c:1139-1140`,
`j-sift.c:1146-1147`, `j-sift.c:1154-1158`

Deviation: the state taken and returned, for the thread-local global `rowptr` and the statics of
`row_setup` (`JPoints.RowSetupCache`); the globals and the static data that it reads passed;
integers for the `long`s `a`, `b` and `d`. -/
def rowSetup (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) : Id SiftState := do
  let c := s.rowSetup
  let d := b - c.lastB
  let mut (rowptr, bres, dres, drow, lastD) := (s.rowptr, c.bres, c.dres, c.drow, c.lastD)
  if a == c.lastA && d > 0 && d < 3 then
    (rowptr, bres) ← rowSetupAddSmall g sd rowptr bres d.toNat
  else if a == c.lastA && d > 0 then
    if d != lastD then
      (dres, drow) ← rowSetupResidues g sd dres drow d
      lastD := d
    (rowptr, bres) ← rowSetupAddResidues g sd rowptr bres dres drow
  else
    (rowptr, bres) ← rowSetupDivide g sd rowptr bres a b
    lastD := 0
  return { s with rowptr, rowSetup := { lastA := a, lastB := b, lastD, bres, dres, drow } }

/-! ### The sieve of a row -/

/-- The excluded third coordinate `c0` and the mask of the row `(a, b)`, as `sift` and `sift_bands`
make them for their rows: `c0 = b² / 4a` when `a ≠ 0` and `4a ∣ b²`, and otherwise `height + 64`,
whose word lies beyond the row; the mask the word of the condition at 2 for `(a mod 64, b mod 64)`
when the sieve uses it and `a ≠ 0`, else the odd `c` (`JPoints.halfMask`) when `a` and `b` are even,
else all `c`.

C: `j-sift.c:852-856`, `j-sift.c:1165`, `j-sift.c:1167`, `j-sift.c:1173-1175`

Deviation: one function for the two copies in `sift_bands` and `sift`, which are the same on `a`,
`b`, `c0` and `mask` (in `sift` the call of `row_setup` between them reads neither); the pair
returned, for the local variables; the globals that it reads passed; integers for the `long`s, with
`Int.tmod` and `Int.tdiv` for C's `%` and `/`, and `height + 64` for `height + LONG_LENGTH`, which
the C code computes as a `size_t` and converts back to a `long`, the same value; `a % 64` and
`b % 64`, in `[0, 64)`, for `a & 63` and `b & 63`, the same in two's complement, and the entry
`(a & 63) * 64 + (b & 63)` of the flat array `mask2`; the test that `a` and `b` are even for
`!((a|b)&1)`. -/
def siftMask (g : SiftGlobals) (a b : Int) : Int × UInt64 :=
  let c0 := if a != 0 && (b * b).tmod (4 * a) == 0 then (b * b).tdiv (4 * a)
    else g.check.height + longLength
  let mask : UInt64 := if g.twoAdic.use2 && a != 0 then
      g.twoAdic.mask2[(a % 64).toNat * 64 + (b % 64).toNat]!
    else if a % 2 == 0 && b % 2 == 0 then halfMask else ~~~0
  (c0, mask)

/-- `sift`, the sieve of the row `(a, b)` of the box, every chunk whole, in the state `s`: the
excluded third coordinate `c0` and the mask of the row (`JPoints.siftMask`), the rows of the sieve
tables (`JPoints.rowSetup`), and each chunk sieved (`JPoints.sift0`) until a point is found when one
point is enough (`-1`). Whether it stopped so, and the state.

C: `j-sift.c:1160-1164`, `j-sift.c:1166`, `j-sift.c:1171`, `j-sift.c:1176-1180`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s; `c0` and the mask computed together before
`row_setup` (`JPoints.siftMask`), which reads neither; a Boolean for the `int`. -/
def sift (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : Int) :
    Id (Bool × SiftState) := do
  let (c0, mask) := siftMask g a b
  let mut s ← rowSetup g sd s a b
  for k in [0:sd.numChunks] do
    let (found, s') ← sift0 g sd s a b k mask c0
    s := s'
    if found && g.check.onePoint then return (true, s)
  return (false, s)

/-! ### Examples

From a test program that includes `j-sift.c` of the pin (with the statics of `row_setup` moved out
of the function, so that it can print them), with the globals of a curve and of its tables set as
`read_input`, `normalise_curve`, `kummer_init`, `init_fmodpsquare`, `init_table` and `twoadic_init`
leave them, `begmask` and `endmask` as `main` sets them, the sieving primes given, `init_sieve` and
`init_sift` called, and then `walk_parts`, `row_setup`, `sift0`, `sift_range` and `sift` called
directly, on rows `(a, b)` in turn: what `init_sift` computes (the doubles by their bits), what the
functions return, the statics of `row_setup` with the rows (as indices into the tables), the words
of the bit array that `sift0` and `sift_range` write, by a hash, the counters and the points. The
hash of a list of words is `h ↦ h * 1000003 + v` modulo `2 ^ 64` over them, from `h = 0`. -/

-- The hash of the examples over the words `vs`.
private def hash (vs : List UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The word `x` in hexadecimal, as `printf` prints it with `%lx`.
private def hex (x : UInt64) : String := String.ofList (Nat.toDigits 16 x.toNat)

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

-- The condition at 2 for the curve `cs`, used, with the words of `mask2` of the classes `cells`
-- modulo `64` as `twoadic_table` computes them (`JPoints.twoadicRow`) and the others `0`: all that
-- `JPoints.sift` reads of the table of `twoadic_init` on the rows of those classes, at a fraction
-- of the cost of the whole table.
private def twoAdicCells (cs : Array Int) (cells : List (Nat × Nat)) : TwoAdic :=
  let (fm, km) := (twoadicCoeffs cs (kummerInit cs)).run
  let sq := twoadicSquares.run
  let sol := twoadicSol.run
  let row (a2 b2 : Nat) : UInt64 := (twoadicRow fm km sol sq halfMask (twoadicPowers a2).run
    (twoadicPowers b2).run a2 b2).run.1
  { TwoAdic.initial with
    use2 := true
    mask2 := cells.foldl (fun m (a2, b2) ↦ m.set! (a2 * 64 + b2) (row a2 b2))
      TwoAdic.initial.mask2 }

-- The globals of the sieve for the curve `cs` of degree `d` given, the height bound `H`, the value
-- `W` of `-w` (`0` for none), `-a`, `-1`, the condition at 2 `twoAdic`, `array_size = arraySize`
-- and the sieving primes `pnn`, `sp1` of them in the first stage, `sp2` in the first two and `sp3`
-- in all three; with the tables of the curve and the sieve tables when `tables`, empty tables
-- otherwise.
private def globals (cs : Array Int) (d : Nat) (H W : Int) (all one : Bool) (twoAdic : TwoAdic)
    (tables : Bool) (arraySize sp1 sp2 sp3 : Nat) (pnn : Array Nat) : SiftGlobals :=
  let t := (initMain Tables.initial).run
  let curve := (normalizeCurve cs d true).run.1
  let ct := if tables then curveTables t curve.coeffs curve.degree pnn.toList
    else CurveTables.initial
  let kummer := kummerInit curve.coeffs
  { tables := t, curve := ct, arraySize, pnn, sievePrimes1 := sp1, sievePrimes2 := sp2
    sieve := if tables then (initSieve t ct pnn sp2 SieveTables.initial).run else
      SieveTables.initial
    check := { curve, kummer, height := H, dbound := if W ≤ 0 then H else W
               dbounded := W > 0 || !all, allPoints := all, onePoint := one
               printFormat := "(%ld, %ld, %ld, %ld)\n" }
    twoAdic, sievePrimes3 := sp3, begmask := ~~~0 <<< ((-H) % 64).toNat.toUInt64
    endmask := ~~~0 >>> ((-H - 1) % 64).toNat.toUInt64 }

-- What `init_sift` computes for the globals `g`, as the test program prints it.
private def dump (g : SiftGlobals) (sd : SiftData) : String := Id.run do
  let mut log := s!"D {sd.numChunks} {sd.npr} {sd.wLowAll} {sd.wHighAll} {hex sd.th.bits} \
    {hex sd.th2.bits}\n"
  for n in [0:sd.npr] do
    log := log ++ s!"pr {sd.pr[n]!} {sd.rowlen[n]!} {sd.blocklen[n]!} {hex sd.invp[n]!.bits}\n"
  for m in [0:g.sievePrimes3 - g.sievePrimes2] do
    log := log ++ s!"recip3 {sd.recip3[m]!}\n"
  for ch in sd.chunks do
    log := log ++ s!"chunk {ch.wLow} {ch.wHigh} res" ++
      String.join ((ch.res.extract 0 sd.npr).toList.map (s!" {·}")) ++ " walk" ++
      String.join ((ch.walk.extract 0 g.sievePrimes1).toList.map fun w ↦
        s!" {w.first},{w.head},{w.nper},{w.tail}") ++ "\n"
  let vs := (sd.res0.extract 0 ((g.arraySize + 1) * sd.npr)).toList.map Nat.toUInt64 ++
    sd.allOnes.toList.map fun v ↦ if v then 1 else 0
  return log ++ s!"res0 {hash vs}\n"

-- The chunk of the word `i` of a row.
private def chunkOf (sd : SiftData) (i : Int) : Nat :=
  ((List.range sd.numChunks).find? fun k ↦ sd.chunks[k]!.wLow ≤ i && i < sd.chunks[k]!.wHigh).getD 0

-- `JPoints.sift` on the rows `(a, b)` for `b = b0, b0 + m, …` up to the height bound, until it
-- finds a point under `-1`: what the last call returned, the number of the rows, and the state.
private def rows (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b0 m : Int) :
    Bool × Nat × SiftState := Id.run do
  let mut s := s
  let mut b := b0
  let mut n := 0
  let mut r := false
  while b ≤ g.check.height do
    n := n + 1
    (r, s) := (sift g sd s a b).run
    if r && g.check.onePoint then break
    b := b + m
  return (r, n, s)

-- `0` or `1` for a Boolean, as the test program prints an `int`.
private def bit (r : Bool) : String := if r then "1" else "0"

-- `P k n off len`: `JPoints.walkParts` on the walk of the `n`-th prime over the chunk `k`, as the
-- test program prints it.
private def opParts (sd : SiftData) (k n o l : String) : String :=
  let w := (walkParts sd n.toNat! sd.pr[n.toNat!]! sd.chunks[k.toNat!]!.walk[n.toNat!]! o.toNat!
    l.toNat!).run
  s!"P {k} {n} {o} {l}: {w.first} {w.head} {w.nper} {w.tail}\n"

-- `U a b`: `JPoints.rowSetup` on the row `(a, b)`, and its statics and the rows, as the test
-- program prints them.
private def opSetup (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : String) :
    String × SiftState :=
  let s := (rowSetup g sd s a.toInt! b.toInt!).run
  let c := s.rowSetup
  let l := String.join ((List.range g.sievePrimes2).map fun n ↦
    s!" {c.bres[n]!},{c.dres[n]!},{c.drow[n]!},{s.rowptr[n]!}")
  (s!"U {a} {b}: {c.lastA} {c.lastB} {c.lastD}{l}\n", s)

-- `Z a b k`: `JPoints.rowSetup` on the row `(a, b)`, then `JPoints.sift0` on the chunk `k` with the
-- mask and `c0` of `JPoints.sift`; what it returns and the hash of the words of the chunk.
private def opSift0 (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b k : String) :
    String × SiftState :=
  let s := (rowSetup g sd s a.toInt! b.toInt!).run
  let (c0, mask) := siftMask g a.toInt! b.toInt!
  let (r, s) := (sift0 g sd s a.toInt! b.toInt! k.toNat! mask c0).run
  let ch := sd.chunks[k.toNat!]!
  let h := hash (s.survivors.extract 0 (ch.wHigh - ch.wLow).toNat).toList
  (s!"Z {a} {b} {k}: {bit r} {h}\n", s)

-- `G a b lo hi`: `JPoints.rowSetup` on the row `(a, b)`, then `JPoints.siftRange` on the words
-- `[lo, hi)` in their chunk with the mask and `c0` of `JPoints.sift`; what it returns and the hash
-- of the words of the range.
private def opRange (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : String) :
    String × SiftState :=
  let s := (rowSetup g sd s a.toInt! b.toInt!).run
  let (c0, mask) := siftMask g a.toInt! b.toInt!
  let k := chunkOf sd lo.toInt!
  let off := (lo.toInt! - sd.chunks[k]!.wLow).toNat
  let (r, s) := (siftRange g sd s a.toInt! b.toInt! k lo.toInt! hi.toInt! mask c0).run
  let h := hash (s.survivors.extract off (off + (hi.toInt! - lo.toInt!).toNat)).toList
  (s!"G {a} {b} {lo} {hi}: {bit r} {h}\n", s)

-- The operations `ops` of the test program in turn, from the log and the state `acc`: `D` prints
-- what `init_sift` computes, `P`, `U`, `Z` and `G` are `opParts`, `opSetup`, `opSift0` and
-- `opRange`, `X a b` runs `JPoints.sift`, `Y a b0 m` is `rows`, and `Q` prints the counters
-- `num_surv1`, `num_surv2`, `num_surv3` and `total`.
private def runOps (g : SiftGlobals) (sd : SiftData) :
    List String → String × SiftState → String × SiftState
  | "D" :: ops, (log, s) => runOps g sd ops (log ++ dump g sd, s)
  | "P" :: k :: n :: o :: l :: ops, (log, s) => runOps g sd ops (log ++ opParts sd k n o l, s)
  | "U" :: a :: b :: ops, (log, s) =>
    let (l, s) := opSetup g sd s a b
    runOps g sd ops (log ++ l, s)
  | "Z" :: a :: b :: k :: ops, (log, s) =>
    let (l, s) := opSift0 g sd s a b k
    runOps g sd ops (log ++ l, s)
  | "G" :: a :: b :: lo :: hi :: ops, (log, s) =>
    let (l, s) := opRange g sd s a b lo hi
    runOps g sd ops (log ++ l, s)
  | "X" :: a :: b :: ops, (log, s) =>
    let (r, s) := (sift g sd s a.toInt! b.toInt!).run
    runOps g sd ops (log ++ s!"X {a} {b}: {bit r}\n", s)
  | "Y" :: a :: b0 :: m :: ops, (log, s) =>
    let (r, n, s) := rows g sd s a.toInt! b0.toInt! m.toInt!
    runOps g sd ops (log ++ s!"Y {a} {b0} {m}: {bit r} {n}\n", s)
  | "Q" :: ops, (log, s) =>
    runOps g sd ops (log ++ s!"Q {s.numSurv1} {s.numSurv2} {s.numSurv3} {s.out.total}\n", s)
  | _, acc => acc

-- The log of the operations `ops` from the start of the sieve with the globals `g`, and the points
-- printed.
private def run (g : SiftGlobals) (ops : String) : String × String :=
  let (log, s) := runOps g (initSift g SiftData.initial).run (ops.splitOn " ")
    ("", SiftState.initial g.arraySize)
  (log, s.out.text)

-- `JPoints.walkParts` against the arithmetic, independent of the C code: for the chunks of nine
-- words of a row at `H = 1000` with the first-stage primes `3, 5, 7, 11`, and for the one chunk of
-- a row at `H = 100000` with the primes `3, 61, 127, 251` and long ranges, for every range
-- `[off, off + len)` of a chunk the first word is `w_low + off` modulo `p`, in `[1, p]`, the head
-- is `min(p - first, len)`, the parts add up to `len` with a tail below `p` (so that the number of
-- the periods, which the doubles compute, is exact), and over the whole chunk they are the walk
-- that `JPoints.initSiftWalk` computes.
#guard [(1000, 9, #[0, 1, 2, 3], fun (r : Nat) ↦ List.range r),
    (100000, 3126, #[0, 16, 29, 52], fun r ↦ (List.range 40).map (r - 1 - 37 * ·))].all
  fun (H, asize, pnn, offs) ↦
  let g := globals #[1, 4, 3, -8, 2, 8, 7] 6 H 0 false false TwoAdic.initial false asize 4 4 4 pnn
  let sd := (initSift g SiftData.initial).run
  sd.chunks.all fun ch ↦ (List.range 4).all fun n ↦
    let p := sd.pr[n]!
    let range := (ch.wHigh - ch.wLow).toNat
    (offs range).all fun off ↦ (List.range (min (range - off) 50)).all fun l ↦
      let len := range - off - l
      let w := (walkParts sd n p ch.walk[n]! off len).run
      (w.first : Int) % p == (ch.wLow + off) % p && 1 ≤ w.first && w.first ≤ p &&
        w.head == min (p - w.first) len && w.head + w.nper * p + w.tail == len && w.tail < p &&
        (off != 0 || len != range || w == ch.walk[n]!)

-- The sextic `1 + 4 x + 3 x² - 8 x³ + 2 x⁴ + 8 x⁵ + 7 x⁶` at `H = 1000` with `-w 2⁵³ + 1` (`th` is
-- `2⁵³`, the double nearest to it, and `th2 = 2¹⁰⁶`), chunks of seven words, the primes
-- `103, 107` in the first stage and `3, 5, 7` in the second: what `init_sift` computes,
-- `row_setup` on a sequence of rows with steps `1` and `2`, steps from `3` up to the primes and
-- beyond them, the same step again (the residues kept), the steps `103` and `107`, where
-- `(double)d * invp[n]` rounds to just below `1` and the correction of the residue from `p` to `0`
-- is taken, steps back, a new `a`, and the rows of `a = 0`; and `walk_parts` on ranges of chunks.
#guard
  let g := globals #[1, 4, 3, -8, 2, 8, 7] 6 1000 9007199254740993 false false TwoAdic.initial false
    7 2 5 5 #[25, 26, 0, 1, 2]
  run g "D U 1 -1000 U 1 -999 U 1 -997 U 1 -994 U 1 -991 U 1 -888 U 1 -781 U 1 -674 U 1 -700 U 2 \
    -700 U 2 -486 U 2 -177 U 2 -174 U 2 -173 U 2 -171 U 2 -171 U 0 1 U 0 104 U 0 211 P 0 0 0 7 P 0 \
    1 2 5 P 4 0 3 2 P 4 1 0 7 P 3 1 6 1" ==
    ("D 5 5 -16 16 4340000000000000 4690000000000000\npr 103 104 10712 3f83e22cbce4a902\n\
    pr 107 108 11556 3f8323e34a2b10bf\npr 3 4 12 3fd5555555555555\npr 5 6 30 3fc999999999999a\n\
    pr 7 8 56 3fc2492492492492\nchunk -16 -9 res 87 91 2 4 5 walk 87,7,0,0 91,7,0,0\n\
    chunk -9 -2 res 94 98 0 1 5 walk 94,7,0,0 98,7,0,0\nchunk -2 5 res 101 105 1 3 5 walk \
    101,2,0,5 105,2,0,5\nchunk 5 12 res 5 5 2 0 5 walk 5,7,0,0 5,7,0,0\n\
    chunk 12 16 res 12 12 0 2 5 walk 12,4,0,0 12,4,0,0\nres0 10340257825428252395\n\
    U 1 -1000: 1 -1000 0 30,0,0,13832 70,0,0,19116 2,0,0,20 0,0,0,30 1,0,0,64\n\
    U 1 -999: 1 -999 0 31,0,0,13936 71,0,0,19224 0,0,0,12 1,0,0,36 2,0,0,72\n\
    U 1 -997: 1 -997 0 33,0,0,14144 73,0,0,19440 2,0,0,20 3,0,0,48 4,0,0,88\n\
    U 1 -994: 1 -994 3 36,3,312,14456 76,3,324,19764 2,0,0,20 1,3,18,36 0,3,24,56\n\
    U 1 -991: 1 -991 3 39,3,312,14768 79,3,324,20088 2,0,0,20 4,3,18,54 3,3,24,80\n\
    U 1 -888: 1 -888 103 39,0,0,14768 75,103,11124,19656 0,1,4,12 2,3,18,42 1,5,40,64\n\
    U 1 -781: 1 -781 107 43,4,416,15184 75,0,0,19656 2,2,8,20 4,2,12,54 3,2,16,80\n\
    U 1 -674: 1 -674 107 47,4,416,15600 75,0,0,19656 1,2,8,16 1,2,12,36 5,2,16,96\n\
    U 1 -700: 1 -700 0 21,4,416,12896 49,0,0,16848 2,2,8,20 0,2,12,30 0,2,16,56\n\
    U 2 -700: 2 -700 0 21,4,416,23608 49,0,0,28404 2,2,8,32 0,2,12,60 0,2,16,112\n\
    U 2 -486: 2 -486 214 29,8,832,24440 49,0,0,28404 0,1,4,24 4,4,24,84 4,4,32,144\n\
    U 2 -177: 2 -177 309 29,0,0,24440 37,95,10260,27108 0,0,0,24 3,4,24,78 5,1,8,152\n\
    U 2 -174: 2 -174 3 32,3,312,24752 40,3,324,27432 0,0,0,24 1,3,18,66 1,3,24,120\n\
    U 2 -173: 2 -173 3 33,3,312,24856 41,3,324,27540 1,0,0,28 2,3,18,72 2,3,24,128\n\
    U 2 -171: 2 -171 3 35,3,312,25064 43,3,324,27756 0,0,0,24 4,3,18,84 4,3,24,144\n\
    U 2 -171: 2 -171 0 35,3,312,25064 43,3,324,27756 0,0,0,24 4,3,18,84 4,3,24,144\n\
    U 0 1: 0 1 0 1,3,312,104 1,3,324,108 1,0,0,4 1,3,18,6 1,3,24,8\n\
    U 0 104: 0 104 103 1,0,0,104 104,103,11124,11232 2,1,4,8 4,3,18,24 6,5,40,48\n\
    U 0 211: 0 211 107 5,4,416,520 104,0,0,11232 1,2,8,4 1,2,12,6 1,2,16,8\nP 0 0 0 7: 87 7 0 0\n\
    P 0 1 2 5: 93 5 0 0\nP 4 0 3 2: 15 2 0 0\nP 4 1 0 7: 12 7 0 0\nP 3 1 6 1: 11 1 0 0\n", "")

-- The statics of `row_setup` against their meaning, independent of the C code: for the same
-- globals, along rows of `a = 0, 1, 2, 5` with steps of every kind, after each call and for each
-- prime `p` of the first two stages, `bres = b mod p`, the row is that of `(a mod p, b mod p)`, and
-- when `last_d ≠ 0`, `dres = last_d mod p` and `drow = dres * rowlen`.
#guard
  let g := globals #[1, 4, 3, -8, 2, 8, 7] 6 1000 0 false false TwoAdic.initial false 7 2 5 5
    #[25, 26, 0, 1, 2]
  let sd := (initSift g SiftData.initial).run
  let steps : List Int := [1, 2, 3, 3, 103, 107, 107, 2, 5, 5, 214, 309, 321, 1, 0, -7, 13, 13, 535]
  let rowsAB := [0, 1, 2, 5].flatMap fun (a : Int) ↦
    (steps.foldl (fun bs d ↦ bs ++ [bs.getLast! + d]) [if a == 0 then 1 else -1000]).map (a, ·)
  (rowsAB.foldl (init := (true, SiftState.initial 7)) fun (ok, s) (a, b) ↦
    let s := (rowSetup g sd s a b).run
    let c := s.rowSetup
    (ok && (List.range 5).all fun n ↦
      let p := sd.pr[n]!
      c.bres[n]! == (b % p).toNat &&
        s.rowptr[n]! == ((a % p).toNat * p + (b % p).toNat) * (p + 1) &&
        (c.lastD == 0 || c.dres[n]! == (c.lastD % p).toNat && c.drow[n]! == c.dres[n]! * (p + 1)),
      s)).1

-- The quintic of example 2 of the README of `j-points` at `H = 100`, chunks of three words (two
-- chunks), the sieving primes `5` (the first stage), `3, 7` (the second) and `11, 13, 251` (the
-- third): what `init_sift` computes, `sift` on rows and on all the rows of `a = 0` and of `a = 1`,
-- the counters and the points.
#guard
  let g := globals #[1, 178, 817, -274, 16, 1, 0] 5 100 0 false false TwoAdic.initial true 3 1 3 6
    #[1, 0, 2, 3, 4, 52]
  run g "D X 0 1 X 1 -2 Y 0 1 1 Y 1 -100 1 Q" ==
    ("D 2 6 -2 2 4059000000000000 40c3880000000000\npr 5 6 30 3fc999999999999a\n\
    pr 3 4 12 3fd5555555555555\npr 7 8 56 3fc2492492492492\npr 11 12 132 3fb745d1745d1746\n\
    pr 13 14 182 3fb3b13b13b13b14\npr 251 252 63252 3f705197f7d73404\nrecip3 390451573\n\
    recip3 330382100\nrecip3 17111424\nchunk -2 1 res 3 1 5 9 11 249 walk 3,2,0,1\n\
    chunk 1 2 res 1 1 1 1 1 1 walk 1,1,0,0\nres0 18204871162949420181\nX 0 1: 0\nX 1 -2: 0\n\
    Y 0 1 1: 0 100\nY 1 -100 1: 0 201\nQ 1212 18420 3359 21\n",
    "(0, 1, -9, 81)\n(0, 1, -6, 36)\n(0, 1, -2, 4)\n(0, 1, 0, 0)\n(0, 1, 4, 16)\n(1, -2, 0, -52)\n\
    (0, 1, -9, 81)\n(0, 1, -6, 36)\n(0, 1, -2, 4)\n(0, 1, 0, 0)\n(0, 1, 4, 16)\n(1, -17, 0, -2)\n\
    (1, -9, 0, -6)\n(1, -6, 0, -12)\n(1, -2, 0, -52)\n(1, 4, -6, -40)\n(1, 4, 0, 40)\n\
    (1, 6, -2, 32)\n(1, 8, 2, -24)\n(1, 8, 10, -72)\n(1, 30, -6, 48)\n")

-- The sextic at `H = 1000` with the condition at 2 (which `twoadic_init` sets up for it; here the
-- words of `mask2` that the rows read), chunks of five words (seven chunks), the primes `7, 11, 13`
-- in the first stage, `3, 5` in the second and `17, 19` in the third: what `init_sift` computes,
-- `sift0` on chunks of rows (the first and the last chunk, with `begmask` and `endmask`, the
-- excluded `c0` in the chunk), `sift` on rows with points, `sift_range` on ranges of one or two
-- words, at the ends of the row, around `c0` and on a whole chunk, `sift` on the rows of `a = 1`
-- and on every seventh row of `a = 7`, the counters and the points.
#guard
  let cs := #[1, 4, 3, -8, 2, 8, 7]
  let cells := [1, 7].flatMap (fun a2 ↦ (List.range 64).map (a2, ·)) ++
    [(32, 16), (19, 45), (53, 3), (59, 9), (2, 4)]
  let g := globals cs 6 1000 0 false false (twoAdicCells cs cells) true 5 3 5 7
    #[2, 3, 4, 0, 1, 5, 6]
  run g "D Z 1 -2 3 Z 1 -2 0 Z 1 -2 6 Z 1 -85 3 Z 7 6 3 Z 1 0 3 X 1 -1 X 32 80 X \
    19 -19 X 53 67 X 59 73 G 1 -85 0 1 G 7 6 -1 1 G 1 -1 -16 -14 G 1 -1 14 16 G 1 -2 -1 4 G 2 4 -6 \
    -1 Q Y 1 -1000 1 Y 7 -994 7 Q" ==
    ("D 7 7 -16 16 408f400000000000 412e848000000000\npr 7 8 56 3fc2492492492492\n\
    pr 11 12 132 3fb745d1745d1746\npr 13 14 182 3fb3b13b13b13b14\npr 3 4 12 3fd5555555555555\n\
    pr 5 6 30 3fc999999999999a\npr 17 18 306 3fae1e1e1e1e1e1e\npr 19 20 380 3faaf286bca1af28\n\
    recip3 252645136\nrecip3 226050911\nchunk -16 -11 res 5 6 10 2 4 1 3 walk 5,2,0,3 6,5,0,0 \
    10,3,0,2\nchunk -11 -6 res 3 0 2 1 4 6 8 walk 3,4,0,1 11,0,0,5 2,5,0,0\n\
    chunk -6 -1 res 1 5 7 0 4 11 13 walk 1,5,0,0 5,5,0,0 7,5,0,0\n\
    chunk -1 4 res 6 10 12 2 4 16 18 walk 6,1,0,4 10,1,0,4 12,1,0,4\n\
    chunk 4 9 res 4 4 4 1 4 4 4 walk 4,3,0,2 4,5,0,0 4,5,0,0\n\
    chunk 9 14 res 2 9 9 0 4 9 9 walk 2,5,0,0 9,2,0,3 9,4,0,1\n\
    chunk 14 16 res 0 3 1 2 4 14 14 walk 7,0,0,2 3,2,0,0 1,2,0,0\nres0 10924848842612445117\n\
    Z 1 -2 3: 0 8593405314460000256\nZ 1 -2 0: 0 18038890310291753234\n\
    Z 1 -2 6: 0 536872556167168\nZ 1 -85 3: 0 15102589880070709833\n\
    Z 7 6 3: 0 12186951676254032664\nZ 1 0 3: 0 461765956283943146\nX 1 -1: 0\nX 32 80: 0\n\
    X 19 -19: 0\nX 53 67: 0\nX 59 73: 0\nG 1 -85 0 1: 0 1153202979584606480\n\
    G 7 6 -1 1: 0 12659089502881677352\nG 1 -1 -16 -14: 0 16777266331920\n\
    G 1 -1 14 16: 0 269484840456448\nG 1 -2 -1 4: 0 8593405314460000256\n\
    G 2 4 -6 -1: 0 3576074541658824578\nQ 202 302 106 11\nY 1 -1000 1: 0 2001\nY 7 -994 7: 0 285\n\
    Q 70415 104603 25057 14\n",
    "(1, -85, 48, -476)\n(7, 6, -9, -74)\n(7, 6, 3, -2)\n(1, -1, 0, 4)\n(1, -1, 0, -8)\n\
    (19, -19, -36, -32)\n(53, 67, -12, 476)\n(59, 73, 12, -448)\n(1, -85, 48, -476)\n\
    (7, 6, -9, -74)\n(7, 6, 3, -2)\n(1, -85, 48, -476)\n(1, -1, 0, 4)\n(1, -1, 0, -8)\n")

-- The quintic under `-a` and `-1` at `H = 100`, chunks of two words, no prime in the first stage
-- (the bit array filled with the mask), `3, 7` in the second and `11, 13` in the third: `sift`,
-- `sift0` and `sift_range` stopping at the first point, and on rows without one.
#guard
  let g := globals #[1, 178, 817, -274, 16, 1, 0] 5 100 0 true true TwoAdic.initial true 2 0 2 4
    #[0, 2, 3, 4]
  run g "D X 0 1 X 1 -2 Z 1 -17 1 Z 1 -17 0 G 1 -9 0 1 G 1 -9 -1 0 X 2 4 Q Y 1 -100 1 Q" ==
    ("D 2 4 -2 2 4059000000000000 40c3880000000000\npr 3 4 12 3fd5555555555555\n\
    pr 7 8 56 3fc2492492492492\npr 11 12 132 3fb745d1745d1746\npr 13 14 182 3fb3b13b13b13b14\n\
    recip3 390451573\nrecip3 330382100\nchunk -2 0 res 1 5 9 11 walk\nchunk 0 2 res 0 0 0 0 walk\n\
    res0 11145675350458543224\nX 0 1: 1\nX 1 -2: 1\nZ 1 -17 1: 1 137437953468\n\
    Z 1 -17 0: 0 18446475637448245247\nG 1 -9 0 1: 1 18446744073709551615\n\
    G 1 -9 -1 0: 0 18446744073709551615\nX 2 4: 0\nQ 13 185 77 4\nY 1 -100 1: 1 74\n\
    Q 308 5426 1773 5\n",
    "(0, 1, -17, 289)\n(25, -50, -600, -2996)\n(1, -17, 0, -2)\n(1, -9, 0, -6)\n\
    (1, -27, 10, 110)\n")

-- The sextic `-7 + 6 x² + 6 x³ + 10 x⁴ - 7 x⁵ - 3 x⁶` at `H = 2000`, chunks of 33 words (two
-- chunks), the primes `3, 5, 7` in the first stage, `11` in the second and `13` in the third, so
-- that the walks run over full periods: what `init_sift` computes, `walk_parts` on long ranges,
-- `sift0`, `sift_range` on ranges inside a chunk and on a whole chunk, `sift` on rows and on every
-- fifth row of `a = 4` from `b = -199` on, the counters and the points.
#guard
  let g := globals #[-7, 0, 6, 6, 10, -7, -3] 6 2000 0 false false TwoAdic.initial true 33 3 4 5
    #[0, 1, 2, 3, 4]
  run g "D P 0 0 0 33 P 0 1 5 28 P 1 2 0 30 P 1 0 7 23 P 0 2 1 31 Z 4 1 0 Z 4 1 1 G 4 1 -20 -1 G 4 \
    1 1 31 G 4 1 -32 1 X 1 -3 X 2 5 X 3 -7 Q Y 4 -199 5 Q" ==
    ("D 2 5 -32 32 409f400000000000 414e848000000000\npr 3 4 12 3fd5555555555555\n\
    pr 5 6 30 3fc999999999999a\npr 7 8 56 3fc2492492492492\npr 11 12 132 3fb745d1745d1746\n\
    pr 13 14 182 3fb3b13b13b13b14\nrecip3 330382100\nchunk -32 1 res 1 3 3 1 7 walk 1,2,10,1 \
    3,2,6,1 3,4,4,1\nchunk 1 32 res 1 1 1 1 1 walk 1,2,9,2 1,4,5,2 1,6,3,4\n\
    res0 12919881662621974893\nP 0 0 0 33: 1 2 10 1\nP 0 1 5 28: 3 2 5 1\nP 1 2 0 30: 1 6 3 3\n\
    P 1 0 7 23: 2 1 7 1\nP 0 2 1 31: 4 3 4 0\nZ 4 1 0: 0 8887334014868007872\n\
    Z 4 1 1: 0 7153978942720686317\nG 4 1 -20 -1: 0 5779176224485055599\n\
    G 4 1 1 31: 0 1406880763606258275\nG 4 1 -32 1: 0 8887334014868007872\nX 1 -3: 0\nX 2 5: 0\n\
    X 3 -7: 0\nQ 337 2557 1265 2\nY 4 -199 5: 0 440\nQ 28300 143631 58245 3\n",
    "(4, 1, 2, 50)\n(4, 1, 2, 50)\n(4, 1, 2, 50)\n")

-- The words of the bit array after `sift0` and `sift_range` against their meaning, independent of
-- the C code: for the globals of the sextics with chunks of five and of 33 words, without the
-- condition at 2, on rows of every kind, on every chunk and on ranges at the ends of the row,
-- around `c0` and inside a chunk, word `i` of the row is the mask of the row and-ed with word
-- `i mod p` of the row of `(a, b)` of the sieve table of each first-stage prime `p`, with
-- `begmask` on the first word of the row, `endmask` on its last word, and the bit of `c0` cleared.
#guard [(globals #[1, 4, 3, -8, 2, 8, 7] 6 1000 0 false false TwoAdic.initial true 5 3 5 7
      #[2, 3, 4, 0, 1, 5, 6], [(1, -2), (1, 0), (7, 6), (2, 4), (32, 80), (0, 5), (3, -1000),
      (12, 1000)], [(-16, -14), (14, 16), (-1, 1), (-1, 4), (5, 8), (10, 11)]),
    (globals #[-7, 0, 6, 6, 10, -7, -3] 6 2000 0 false false TwoAdic.initial true 33 3 4 5
      #[0, 1, 2, 3, 4], [(4, 1), (1, -3), (2, 4), (0, 7), (4, -2000), (6, 2000)],
      [(-32, 1), (-20, -1), (1, 31), (5, 6), (31, 32)])].all fun (g, rowsAB, ranges) ↦
  let sd := (initSift g SiftData.initial).run
  let word (s : SiftState) (a b i : Int) : UInt64 :=
    let (c0, mask) := siftMask g a b
    let w := (List.range g.sievePrimes1).foldl (init := mask) fun w n ↦
      w &&& g.sieve.sieveTab[n]![s.rowptr[n]! + (i % ((sd.pr[n]! : Nat) : Int)).toNat]!
    let w := if i == sd.wLowAll then w &&& g.begmask else w
    let w := if i == sd.wHighAll - 1 then w &&& g.endmask else w
    if c0 >>> longShift == i then w &&& ~~~(1 <<< (c0 % 64).toNat.toUInt64) else w
  rowsAB.all fun (a, b) ↦
    let s := (rowSetup g sd (SiftState.initial g.arraySize) a b).run
    let (c0, mask) := siftMask g a b
    (List.range sd.numChunks).all (fun k ↦
      let ch := sd.chunks[k]!
      let s' := (sift0 g sd s a b k mask c0).run.2
      (List.range (ch.wHigh - ch.wLow).toNat).all fun t ↦
        s'.survivors[t]! == word s a b (ch.wLow + t)) &&
    ranges.all fun (lo, hi) ↦
      let k := chunkOf sd lo
      let s' := (siftRange g sd s a b k lo hi mask c0).run.2
      (List.range (hi - lo).toNat).all fun t ↦
        s'.survivors[(lo - sd.chunks[k]!.wLow).toNat + t]! == word s a b (lo + t)

end JPoints

end
