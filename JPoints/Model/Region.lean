/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Sturm
public import JPoints.Model.Walk

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Sturm
meta import JPoints.Model.Walk

/-!
# The real region and the sieve by bands

The rows of a first coordinate `a` as `j-points` sieves them in the tube or in the real region, when
the choice of the primes has chosen one of these modes (`sift_bands`, `JPoints.siftBands`): band by
band, a band of up to `TUBE_BAND` consecutive rows (`JPoints.siftBandsBand`), in the tube with the
words that can hold a point collected first by the analysis of the tube (`JPoints.tubeCell`); then
the rows of the band that the step of `b` takes, in order (`JPoints.siftBandsRow`), each with its
ranges of words (`JPoints.siftBandsRanges`): in the tube those that the analysis collected, cut to
the real region when the choice says so (`JPoints.rowCut`), in the region the ranges of the real
region. The real region of a row (`row_region`, `JPoints.rowRegion`) is what the intervals on which
`f` is negative leave of it: for `a > 0` the third coordinates `c` for which a real root `x` or `u`
of `a t² - b t + c` lies in such an interval are excluded (`JPoints.rowRegionPositive`), for `a = 0`
those for which `c / b` does (`JPoints.rowRegionZero`), each interval of `c` shrunk by a margin for
the rounding (`JPoints.rowRegionMargins`), the intervals sorted (`JPoints.rowRegionSort`), and the
words wholly inside them (`JPoints.rowRegionEnds`) taken out of the row (`JPoints.rowRegionWords`).
A range of the region is sieved by the passes of the box sieve over the chunks that it meets
(`JPoints.siftBandsRegion`, `JPoints.siftRange`), a range of the tube word by word
(`JPoints.siftBandsTube`): each word of the tube is and-ed with the words of the sieve tables of all
the primes of the first two stages at once and its bits handed to the third stage and the exact
check (`tube_word`, `JPoints.tubeWord`, `JPoints.checkBits`). The chunk of a word is found from that
of the last one (`JPoints.seekChunk`).

## Main definitions

* `JPoints.BandGlobals`: what the sieve by bands reads from the globals of the program.
* `JPoints.rowRegionPositive`, `JPoints.rowRegionZero`, `JPoints.rowRegionMargins`,
  `JPoints.rowRegionSort`, `JPoints.rowRegionEnds`, `JPoints.rowRegionWords`,
  `JPoints.rowRegion`: the real region of a row.
* `JPoints.seekChunk`: the chunk of a word of a row.
* `JPoints.tubeWord`: the sieve of a word of the tube.
* `JPoints.siftBandsBand`, `JPoints.siftBandsRanges`, `JPoints.siftBandsTube`,
  `JPoints.siftBandsRegion`, `JPoints.siftBandsRow`, `JPoints.siftBands`: the sieve of the rows of
  a first coordinate by bands.

## Implementation notes

What the sieve by bands reads of the globals of the program and of the statics of the sieve is
passed (`JPoints.BandGlobals`, `JPoints.SiftData`), the state of the thread, with the analysis of
the tube and its bands, is taken and returned (`JPoints.SiftState`), as in `JPoints.Model.Walk`.
The doubles of the real region decide which words of a row are sieved, so each is a
`JPoints.Double` and each operation on it is that of `JPoints.Model.DoubleArith`, in the order of
the C code. The ranges of words that the C code writes into arrays of the caller (`lo` and `hi` of
`row_region`, the arrays `reglo`, `reghi`, `clo` and `chi` of `sift_bands`) are arrays of their
number, returned, as for `JPoints.rowCut`; the local arrays `xlo` and `xhi` of the excluded
intervals of `row_region` likewise. The loops of `sift_bands` over the bands and over the rows of
a band, which step by `step` and by `m`, are loops over the counts of their steps.
-/

@[expose] public section

namespace JPoints

/-! ### The globals -/

/-- What the sieve by bands reads from the globals of `j-points` besides what the sieve reads
(`sift`): the mode of the sieve (`sieve_mode`, `1` for the tube, `2` for the region) and whether
the words of the tube are cut to the real region (`tube_cut`), which the choice of the primes sets
(`JPoints.Plan`); the intervals on which the polynomial `f` of the curve searched is negative
(`neg`), which `row_region` reads; and the coefficients of the analysis of the tube (`kd`), which
`tube_a_init` reads.

It models no C code of its own: it gathers globals that other structures hold. -/
structure BandGlobals where
  /-- What the sieve reads from the globals. -/
  sift : SiftGlobals
  /-- `sieve_mode`: `0` for the box, `1` for the tube, `2` for the region. -/
  sieveMode : Nat
  /-- `tube_cut`: whether the words of the tube are cut to the real region. -/
  tubeCut : Bool
  /-- `num_neg` and the ends of the intervals on which `f` is negative. -/
  neg : NegativeIntervals
  /-- The coefficients of the Kummer surface and of the curve as doubles. -/
  kd : TubeCoeffs

/-! ### The real region of a row -/

/-- The intervals of the third coordinate `c` that the intervals `(nl, nh)` on which `f` is negative
(the shrunk ones of `neg`) exclude from the row `(a, b)`, for `a > 0`, as `row_region` computes
them, in the order of the intervals and, for each, of the two branches: for `A = (double)a`,
`B = (double)b` and the vertex `m = 0.5 * B / A`, on the branch of the root `x ≥ m`, from
`l = max(nl, m)` on, when `nh > l`, the interval from `C(nh) = B nh - A nh²` (`-∞` when `nh = ∞`)
to `C(l)`; on the branch of the root `u ≤ m`, up to `h = min(nh, m)`, when `h > nl`, the interval
from `C(nl)` (`-∞` when `nl = -∞`) to `C(h)`. The lower and the upper ends of the intervals.

C: `j-sift.c:488-505`

Deviation: the ends returned as two arrays of the number `n` of the intervals, filled in the order
in which the C code writes them, for the local arrays `xlo` and `xhi` of eight doubles and the
count; the intervals passed, for the globals; `JPoints.Double.ofInt` for the conversions of the
`long`s `a` and `b`, exact for the values of the program; `JPoints.Double.lt` for `>` and `<` and
`JPoints.Double.beq` for `==`, false when either side is a NaN. -/
def rowRegionPositive (neg : NegativeIntervals) (a b : Int) : Id (Array Double × Array Double) := do
  let A := Double.ofInt a
  let B := Double.ofInt b
  let m := 0.5 * B / A
  let mut xlo := #[]
  let mut xhi := #[]
  for i in [0:neg.numNeg] do
    let nl := neg.shrunkLo[i]!
    let nh := neg.shrunkHi[i]!
    let l := if m < nl then nl else m
    if l < nh then
      xlo := xlo.push (if nh.beq Double.huge then -Double.huge else B * nh - A * nh * nh)
      xhi := xhi.push (B * l - A * l * l)
    let h := if nh < m then nh else m
    if nl < h then
      xlo := xlo.push (if nl.beq (-Double.huge) then -Double.huge else B * nl - A * nl * nl)
      xhi := xhi.push (B * h - A * h * h)
  return (xlo, xhi)

/-- The intervals of the third coordinate `c` that the intervals `(nl, nh)` on which `f` is negative
(the shrunk ones of `neg`) exclude from the row `(0, b)`, as `row_region` computes them: for
`B = (double)b`, the interval from `B nl` to `B nh` for each, an infinite end kept. The lower and
the upper ends of the intervals.

C: `j-sift.c:508-514`

Deviation: the ends returned as two arrays of the number `n` of the intervals, filled in the order
in which the C code writes them, for the local arrays `xlo` and `xhi` of eight doubles and the
count; the intervals passed, for the globals; `JPoints.Double.ofInt` for the conversion of the
`long` `b`, exact for the values of the program; `JPoints.Double.beq` for `==`. -/
def rowRegionZero (neg : NegativeIntervals) (b : Int) : Id (Array Double × Array Double) := do
  let B := Double.ofInt b
  let mut xlo := #[]
  let mut xhi := #[]
  for i in [0:neg.numNeg] do
    let nl := neg.shrunkLo[i]!
    let nh := neg.shrunkHi[i]!
    xlo := xlo.push (if nl.beq (-Double.huge) then -Double.huge else B * nl)
    xhi := xhi.push (if nh.beq Double.huge then Double.huge else B * nh)
  return (xlo, xhi)

/-- The `n` excluded intervals `(xlo[i], xhi[i])` of the third coordinate shrunk by the margins of
`row_region` for the rounding: a finite lower end `x` raised by `1.0e-9 * (|x| + 1.0) + 1.0`, a
finite upper end lowered by as much, an infinite end kept.

C: `j-sift.c:518-521`

Deviation: the arrays taken and returned, for the local arrays that the C code writes;
`JPoints.Double.lt` for `>` and `<`, false when either side is a NaN. -/
def rowRegionMargins (xlo xhi : Array Double) (n : Nat) : Id (Array Double × Array Double) := do
  let mut xlo := xlo
  let mut xhi := xhi
  for i in [0:n] do
    if -Double.huge < xlo[i]! then
      xlo := xlo.set! i (xlo[i]! + (1.0e-9 * (xlo[i]!.fabs + 1.0) + 1.0))
    if xhi[i]! < Double.huge then
      xhi := xhi.set! i (xhi[i]! - (1.0e-9 * (xhi[i]!.fabs + 1.0) + 1.0))
  return (xlo, xhi)

/-- The `n` excluded intervals `(xlo[i], xhi[i])` of the third coordinate sorted by their lower ends
as `row_region` sorts them, by insertion: each interval in turn moved down past the intervals
before it whose lower end is above its own, in a stable order.

C: `j-sift.c:522-526`

Deviation: the arrays taken and returned, for the local arrays that the C code writes; natural
numbers for the indices `i` and `j`, which the C code keeps nonnegative; the inner loop, which ends
on the data, a `while` loop; `JPoints.Double.lt` for `>`, false when either side is a NaN. -/
def rowRegionSort (xlo xhi : Array Double) (n : Nat) : Id (Array Double × Array Double) := do
  let mut xlo := xlo
  let mut xhi := xhi
  for i in [1:n] do
    let l := xlo[i]!
    let h := xhi[i]!
    let mut j := i
    while j > 0 && l < xlo[j - 1]! do
      xlo := xlo.set! j xlo[j - 1]!
      xhi := xhi.set! j xhi[j - 1]!
      j := j - 1
    xlo := xlo.set! j l
    xhi := xhi.set! j h
  return (xlo, xhi)

/-- The words `[wl, wh)` of the row that lie wholly inside the excluded interval `(xl, xh)` of the
third coordinate, as `row_region` computes them for an interval that meets the row: a lower end at
or below `-ROW_BEYOND` stands for the first word `w_low_all` of the row, an upper end at or above
`ROW_BEYOND` for the end `w_high_all`; otherwise the first `c > xl` is at most `(long)xl + 2`, the
last `c < xh` at least `(long)xh - 2`, and the words wholly between those two are from
`⌊(c + 63) / 64⌋` and up to `⌊(c + 1) / 64⌋`, by the shifts.

C: `j-sift.c:540-544`

Deviation: the words returned as a pair, for the local variables `wl` and `wh`; the static data
passed, for the statics `w_low_all` and `w_high_all`; integers for the `long`s, which they are,
since an end that is truncated lies in `(-ROW_BEYOND, ROW_BEYOND)` (a NaN, which the ends of the
program never are, would truncate to `-2 ^ 63`, from which `(long)xh - 2` overflows);
`JPoints.Double.toInt64` for the conversion `(long)`, which truncates towards zero; `>>>` on
integers for C's `>>` on `long`s, which gcc shifts arithmetically, also for a negative `c`;
`JPoints.Double.le` for `<=` and `>=`, false when either side is a NaN. -/
def rowRegionEnds (sd : SiftData) (xl xh : Double) : Int × Int :=
  let wl := if xl ≤ -rowBeyond then sd.wLowAll else (xl.toInt64.toInt + 2 + longMask) >>> longShift
  let wh := if rowBeyond ≤ xh then sd.wHighAll else (xh.toInt64.toInt - 2 + 1) >>> longShift
  (wl, wh)

/-- The ranges of words of the real region of a row, as `row_region` places them from the `n`
excluded intervals `(xlo[i], xhi[i])` of the third coordinate, sorted by their lower ends: from the
first word `w = w_low_all` of the row on, for each interval that meets the row and is at least `64`
wide, the words `[wl, wh)` wholly inside it (`JPoints.rowRegionEnds`), cut to `[w, w_high_all)`, and
when they are not empty, the range `[w, wl)` before them kept when it is not empty, and `w` moved to
`wh`; then the range `[w, w_high_all)` after the last kept when it is not empty. The number of the
ranges, and their lower and their upper ends, in order.

C: `j-sift.c:528-533`, `j-sift.c:545-551`

Deviation: the ranges returned as arrays of their number, filled in the order in which the C code
writes them, for the arrays `lo` and `hi` of the caller, which have room for `ROW_RANGES` ranges
(`JPoints.rowRanges`), and there are at most `2 * 4 + 1` of them; the static data passed, for the
statics `w_low_all` and `w_high_all`; integers for the `long`s, a natural number for the count `nr`
and the index `i`; `JPoints.Double.le` for `<=` and `>=` and `JPoints.Double.lt` for `<`, false when
either side is a NaN; `JPoints.Double.ofInt` for the conversion of `LONG_LENGTH`. -/
def rowRegionWords (sd : SiftData) (xlo xhi : Array Double) (n : Nat) :
    Id (Nat × Array Int × Array Int) := do
  let mut w := sd.wLowAll
  let mut nr := 0
  let mut lo := #[]
  let mut hi := #[]
  for i in [0:n] do
    if rowBeyond ≤ xlo[i]! || xhi[i]! ≤ -rowBeyond then continue
    if xhi[i]! - xlo[i]! < Double.ofInt longLength then continue
    let (wl, wh) := rowRegionEnds sd xlo[i]! xhi[i]!
    let wl := if wl < w then w else wl
    let wh := if wh > sd.wHighAll then sd.wHighAll else wh
    if wh ≤ wl then continue
    if wl > w then (lo, hi, nr) := (lo.push w, hi.push wl, nr + 1)
    w := wh
  if w < sd.wHighAll then (lo, hi, nr) := (lo.push w, hi.push sd.wHighAll, nr + 1)
  return (nr, lo, hi)

/-- `row_region`, the real region of the row `(a, b)`, for `a ≥ 0` (and `b > 0` when `a = 0`): the
ranges of words `[lo[k], hi[k])` of the row that it meets, in order, and their number. Without an
interval on which `f` is negative, the whole row `[w_low_all, w_high_all)`; otherwise the intervals
of the third coordinate `c` that those intervals exclude (`JPoints.rowRegionPositive` for `a > 0`,
`JPoints.rowRegionZero` for `a = 0`), shrunk by the margins (`JPoints.rowRegionMargins`), sorted
(`JPoints.rowRegionSort`), and the words of the row that they do not wholly cover
(`JPoints.rowRegionWords`).

C: `j-sift.c:481-487`, `j-sift.c:506-507`, `j-sift.c:515`, `j-sift.c:552-553`

Deviation: the ranges returned as arrays of their number, for the arrays `lo` and `hi` of the
caller, which have room for `ROW_RANGES` (`JPoints.rowRanges`); the intervals and the static data
passed, for the globals and the statics that it reads; the arrays of the excluded intervals returned
by the functions that fill them, for the local arrays `xlo` and `xhi`, with their size for the count
`n`; integers for the `long`s `a` and `b` and for the ends of the ranges, natural numbers for the
counts. -/
def rowRegion (neg : NegativeIntervals) (sd : SiftData) (a b : Int) :
    Id (Nat × Array Int × Array Int) := do
  if neg.numNeg == 0 then return (1, #[sd.wLowAll], #[sd.wHighAll])
  let (xlo, xhi) ← if a > 0 then rowRegionPositive neg a b else rowRegionZero neg b
  let n := xlo.size
  let (xlo, xhi) ← rowRegionMargins xlo xhi n
  let (xlo, xhi) ← rowRegionSort xlo xhi n
  rowRegionWords sd xlo xhi n

/-! ### A word of the tube -/

/-- The chunk of the word `i` of a row, from the chunk `cur` of the word before, as `tube_word`
and `sift_bands` find it in the chunks of the static data `sd`: `cur` moved up while `i` lies at or
beyond its end, then down while `i` lies before it. For a word `w_low_all ≤ i < w_high_all` of the
row, the chunk that holds it.

C: `j-sift.c:783-784`, `j-sift.c:862-863`

Deviation: one function for the two pairs of loops, which are the same on `cur_chunk` and the word,
`i` in `tube_word` and `lo` in `sift_bands`, returning `cur_chunk`; the static data passed, for the
static `chunks`; a natural number for the index `cur_chunk`, which stays in `[0, num_chunks)` for a
word of the row (for a word outside the row the C code reads beyond the array of the chunks, and the
loops of the model need not end); integers for the `long`s of the words. -/
def seekChunk (sd : SiftData) (cur : Nat) (i : Int) : Id Nat := do
  let mut cur := cur
  while i ≥ sd.chunks[cur]!.wHigh do cur := cur + 1
  while i < sd.chunks[cur]!.wLow do cur := cur - 1
  return cur

/-- `tube_word`, the sieve of the word `i` of the row `(a, b)` of the tube, whose rows of the sieve
tables `row_setup` has set (`JPoints.rowSetup`), with the mask `mask` of the row and the excluded
third coordinate `c0`, in the state `s`: the chunk of the word (`JPoints.seekChunk`) recorded in
`cur_chunk`, its position `k = i - w_low` in the chunk, the mask and-ed with `begmask` on the first
word of the row, with `endmask` on the last, and the bit of `c0` cleared on its word; then the word
and-ed with the word `r = (res0[k * npr + n] + res[n]) mod p` of the row of the sieve table of each
prime `p` of the first two stages (the `n`-th, `n < sieve_primes2`), all of them, and the bits that
are left handed to `JPoints.checkBits`. Whether it found a point when one point is enough (`-1`),
and the state.

C: `j-sift.c:777-782`, `j-sift.c:785-801`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; the chunk read from the array of the chunks, for the pointer `ch`; the
index `k * npr` into `res0` for the pointer `r0`, the index `rowptr[n]` into `sieve_tab[n]` for the
pointer, and the array of the chunk for the pointer `res`; integers for the `long`s `a`, `b`, `i`
and `c0`, natural numbers for `k`, `n` and the residue `r`, which the C code keeps nonnegative;
`c0 >>> 6` for `c0 >> LONG_SHIFT` and `c0 % 64`, in `[0, 64)`, for `c0 & LONG_MASK`, the same for
the nonnegative `c0` of the calls; a Boolean for the `int`. -/
def tubeWord (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b i : Int) (mask : UInt64)
    (c0 : Int) : Id (Bool × SiftState) := do
  let mut nums := mask
  let cur ← seekChunk sd s.curChunk i
  let s := { s with curChunk := cur }
  let ch := sd.chunks[cur]!
  let k := (i - ch.wLow).toNat
  let r0 := k * sd.npr
  if i == sd.wLowAll then nums := nums &&& g.begmask
  if i == sd.wHighAll - 1 then nums := nums &&& g.endmask
  if c0 >>> longShift == i then
    nums := nums &&& ~~~((1 : UInt64) <<< (c0 % (longLength : Int)).toNat.toUInt64)
  for n in [0:g.sievePrimes2] do
    let mut r := sd.res0[r0 + n]! + ch.res[n]!
    r := r - if r ≥ sd.pr[n]! then sd.pr[n]! else 0
    nums := nums &&& g.sieve.sieveTab[n]![s.rowptr[n]! + r]!
  if nums != 0 then return ← checkBits g sd s nums a b i r0 ch.res
  return (false, s)

/-! ### The sieve by bands -/

/-- The band of the rows `b_lo ≤ b ≤ b_hi` set up by `sift_bands` in the state `t` of the analysis
of the tube: its first row `band_b0 = b_lo`, and in the tube the numbers of the ranges of its rows
set to `0` and the words of the tube collected by the analysis of the band, over the whole row
(`JPoints.tubeCell`, with the bound `th` and its square `th2` of the static data `sd`).

C: `j-sift.c:823-827`

Deviation: the state of the analysis taken and returned, for the thread-local globals of the bands
and the globals of the analysis; the static data passed, for the statics; integers for the `long`s
`b_lo` and `b_hi`; the loop `for(k = 0; k <= b_hi - b_lo; k++)` over `k < b_hi - b_lo + 1`; the
bands taken out of the state while their counts are written, so that they are not shared. -/
def siftBandsBand (sd : SiftData) (t : TubeState) (bLo bHi : Int) (tube : Bool) :
    Id TubeState := do
  let mut bands := t.bands
  let t := { t with bands := default }
  bands := { bands with bandB0 := bLo }
  if tube then
    for k in [0:(bHi - bLo + 1).toNat] do bands := { bands with bandNr := bands.bandNr.set! k 0 }
    return ← tubeCell sd.th sd.th2 { t with bands } bLo bHi sd.wLowAll sd.wHighAll
  return { t with bands }

/-- The ranges of words of the row `(a, b)` of the band from the row `b_lo` on, with the bands `bd`,
that `sift_bands` sieves: in the tube without the cut, the ranges of the row in the band; in the
tube with the cut (`tube_cut`), those cut to the real region of the row (`JPoints.rowRegion`,
`JPoints.rowCut`); in the region, the ranges of the real region. Their number, and their lower and
their upper ends.

C: `j-sift.c:834-845`

Deviation: the ranges returned as arrays of their number, for the arrays `reglo`, `reghi`, `clo` and
`chi` and the pointers `rlo` and `rhi` to the arrays sieved; the bands and the globals that it reads
passed; integers for the `long`s `a`, `b` and `b_lo` and for the ends of the ranges, a natural
number for the index `b - b_lo` of the row in the band and for the count. -/
def siftBandsRanges (g : BandGlobals) (sd : SiftData) (bd : TubeBands) (a b bLo : Int)
    (tube : Bool) : Id (Nat × Array Int × Array Int) := do
  let row := (b - bLo).toNat
  if tube && !g.tubeCut then
    let nr := bd.bandNr[row]!
    let mut clo := #[]
    let mut chi := #[]
    for k in [0:nr] do
      clo := clo.push (bd.blo row k)
      chi := chi.push (bd.bhi row k)
    return (nr, clo, chi)
  else if tube then
    let (nr, reglo, reghi) ← rowRegion g.neg sd a b
    rowCut bd row nr reglo reghi
  else rowRegion g.neg sd a b

/-- The range `[lo, hi)` of words of the row `(a, b)` of the tube sieved by `sift_bands` in the
state `s`, with the mask `mask` and the excluded third coordinate `c0` of the row: its words counted
in `num_surv1`, then each word sieved by `JPoints.tubeWord`, until one finds a point when one point
is enough (`-1`). Whether it stopped so, and the state.

C: `j-sift.c:856-859`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s, and the number `hi - lo` of the words, which is
positive for a range of the tube, added as a natural number; the loop over `i` from `lo` below `hi`
as a loop over `i = lo + k` for `k < hi - lo`; whether `sift_bands` returns `1` here, for its
return. -/
def siftBandsTube (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : Int)
    (mask : UInt64) (c0 : Int) : Id (Bool × SiftState) := do
  let mut s := { s with numSurv1 := s.numSurv1 + (hi - lo).toNat }
  for k in [0:(hi - lo).toNat] do
    let (found, s') ← tubeWord g sd s a b (lo + k) mask c0
    s := s'
    if found && g.check.onePoint then return (true, s)
  return (false, s)

/-- The range `[lo, hi)` of words of the row `(a, b)` of the real region sieved by `sift_bands` in
the state `s`, with the mask `mask` and the excluded third coordinate `c0` of the row: the chunk of
`lo` (`JPoints.seekChunk`) recorded in `cur_chunk`, then from it on each chunk that the range meets,
the part of the range in it sieved by `JPoints.siftRange`, until one finds a point when one point is
enough (`-1`). Whether it stopped so, and the state.

C: `j-sift.c:861`, `j-sift.c:864-869`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s `a`, `b`, `lo`, `hi`, `l`, `h` and `c0`, a
natural number for the index `c` of the chunk; the second condition of the loop over the chunks,
`chunks[c].w_low < hi`, tested at the head of its body, with a `break`; whether `sift_bands` returns
`1` here, for its return. -/
def siftBandsRegion (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b lo hi : Int)
    (mask : UInt64) (c0 : Int) : Id (Bool × SiftState) := do
  let cur ← seekChunk sd s.curChunk lo
  let mut s := { s with curChunk := cur }
  for c in [cur:sd.numChunks] do
    if !(sd.chunks[c]!.wLow < hi) then break
    let l := if lo > sd.chunks[c]!.wLow then lo else sd.chunks[c]!.wLow
    let h := if hi < sd.chunks[c]!.wHigh then hi else sd.chunks[c]!.wHigh
    let (found, s') ← siftRange g sd s a b c l h mask c0
    s := s'
    if found && g.check.onePoint then return (true, s)
  return (false, s)

/-- The row `(a, b)` of the band from the row `b_lo` on, sieved by `sift_bands` in the state `s`:
skipped in the tube when the analysis left it no word, and when the condition at 2 is used, `a ≠ 0`
and the class `(a mod 64, b mod 64)` admits no third coordinate; otherwise its ranges of words
(`JPoints.siftBandsRanges`), and when there are any, the rows of the sieve tables for the row
(`JPoints.rowSetup`), the excluded third coordinate and the mask (`JPoints.siftMask`), and each
range sieved in turn, in the tube (`JPoints.siftBandsTube`) or in the region
(`JPoints.siftBandsRegion`), until a point is found when one point is enough (`-1`). Whether it
stopped so, and the state.

C: `j-sift.c:829-833`, `j-sift.c:846-847`, `j-sift.c:853-855`, `j-sift.c:860`,
`j-sift.c:870-871`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s, a natural number for the index `b - b_lo` of
the row in the band; `a % 64` and `b % 64`, in `[0, 64)`, for `a & 63` and `b & 63`, the same in
two's complement, and the entry `(a & 63) * 64 + (b & 63)` of the flat array `alive2`; the
`continue`s of the C code as returns of `false`, and whether `sift_bands` returns `1` from the row,
for its return. -/
def siftBandsRow (g : BandGlobals) (sd : SiftData) (s : SiftState) (a b bLo : Int) (tube : Bool) :
    Id (Bool × SiftState) := do
  let two := g.sift.twoAdic
  if tube && s.tube.bands.bandNr[(b - bLo).toNat]! == 0 then return (false, s)
  if two.use2 && a != 0 && !two.alive2[(a % 64).toNat * 64 + (b % 64).toNat]! then
    return (false, s)
  let (nr, rlo, rhi) ← siftBandsRanges g sd s.tube.bands a b bLo tube
  if nr == 0 then return (false, s)
  let mut s ← rowSetup g.sift sd s a b
  let (c0, mask) := siftMask g.sift a b
  for k in [0:nr] do
    let lo := rlo[k]!
    let hi := rhi[k]!
    let (found, s') ← if tube then siftBandsTube g.sift sd s a b lo hi mask c0
      else siftBandsRegion g.sift sd s a b lo hi mask c0
    s := s'
    if found then return (true, s)
  return (false, s)

/-- `sift_bands`, the rows `(a, b)` of the first coordinate `a` with `b` from `b_first` on by the
step `m ≥ 1` up to the height bound, sieved in the tube (`sieve_mode = 1`) or in the real region,
in the state `s`: the polynomials of the analysis of the tube for `a` (`JPoints.tubeAInit`); then
the bands of `len` rows from `b_first` on, `len` the largest multiple of `m` up to `TUBE_BAND`, or
`1` when `m` exceeds `TUBE_BAND`, each band starting `step = len` (or `m`) rows after the last, so
that it starts on a row of the step, and the last cut at the height bound: each band set up
(`JPoints.siftBandsBand`), and its rows of the step sieved in order (`JPoints.siftBandsRow`), until
a point is found when one point is enough (`-1`). Whether it stopped so, and the state.

C: `j-sift.c:811-822`, `j-sift.c:828`, `j-sift.c:872-874`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s, with `Int.tmod` for C's `%`; the loop
`for(b_lo = b_first; b_lo <= height; b_lo += step)` over `b_lo = b_first + t step` for
`t < (height - b_first) / step + 1`, with Lean's `/`, which rounds down, none when
`b_first > height`, and the loop `for(b = b_lo; b <= b_hi; b += m)` over `b = b_lo + k m` for
`k < (b_hi - b_lo) / m + 1`; Booleans for the `int` `tube` and for the `int` returned. -/
def siftBands (g : BandGlobals) (sd : SiftData) (s : SiftState) (a bFirst m : Int) :
    Id (Bool × SiftState) := do
  let height := g.sift.check.height
  let band : Int := tubeBand
  let len := if m > band then 1 else band - band.tmod m
  let step := if m > band then m else len
  let tube := g.sieveMode == 1
  let mut s := { s with tube := ← tubeAInit g.kd height sd.th sd.th2 s.tube a }
  for t in [0:((height - bFirst) / step + 1).toNat] do
    let bLo := bFirst + t * step
    let bHi := if bLo + len - 1 > height then height else bLo + len - 1
    s := { s with tube := ← siftBandsBand sd s.tube bLo bHi tube }
    for k in [0:((bHi - bLo) / m + 1).toNat] do
      let (found, s') ← siftBandsRow g sd s a (bLo + k * m) bLo tube
      s := s'
      if found then return (true, s)
  return (false, s)

/-! ### Examples

From a test program that includes `j-points.c` and `j-sift.c` of the pin, with the globals of a
curve and of its tables set as `read_input`, `normalise_curve`, `kummer_init`, `init_fmodpsquare`,
`init_table` and `twoadic_init` leave them, `begmask` and `endmask` as `main` sets them, the doubles
of `tube_init` and the intervals of `real_roots_init`, the sieving primes given, `init_sieve` and
`init_sift` called, and `sieve_mode` and `tube_cut` set; and then `row_region`, `tube_word` (after
`row_setup`, with the mask and `c0` of `sift_bands`) and `sift_bands` called directly, in turn: the
intervals on which `f` is negative, by their bits, the ranges of the real region, what `tube_word`
and `sift_bands` return with `cur_chunk` and `tube_ncells`, the counters, and the points printed.
The condition at 2 of the model is that of the classes of the first coordinates of the examples,
computed by `JPoints.twoadicRow`, all that they read of the table of `twoadic_init`. -/

-- The coefficients of the analysis for the curve searched `sc`: those of the curve and of its
-- quartic `K₀` (`JPoints.kummerInit`), as `tube_init` computes them (`JPoints.tubeInitCoeffs`).
private def coeffsOf (sc : SearchCurve) : TubeCoeffs :=
  (tubeInitCoeffs sc (kummerInit sc.coeffs)).run

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

-- The condition at 2 for the curve `cs`, used, with the words of `mask2` and the entries of
-- `alive2` of the classes `(a2, b2)` modulo `64` for `a2 ∈ as` as `twoadic_table` computes them
-- (`JPoints.twoadicRow`), and the others `0`; not used for `as = []`.
private def twoAdicOf (cs : Array Int) (as : List Nat) : TwoAdic :=
  let (fm, km) := (twoadicCoeffs cs (kummerInit cs) 64).run
  let sq := (twoadicSquares 64).run
  let sol := (twoadicSol 64).run
  let cells := as.flatMap fun a2 ↦ (List.range 64).map fun b2 ↦ (a2 * 64 + b2,
    (twoadicRow fm km sol sq halfMask 64 (twoadicPowers a2 64).run (twoadicPowers b2 64).run a2
      b2).run.1)
  { TwoAdic.initial with
    use2 := !as.isEmpty
    mask2 := cells.foldl (fun m (i, w) ↦ m.set! i w) TwoAdic.initial.mask2
    alive2 := cells.foldl (fun m (i, w) ↦ m.set! i (w != 0)) TwoAdic.initial.alive2 }

-- The globals of the sieve by bands for the curve `cs` of degree `d` given, the height bound `H`,
-- the value `W` of `-w` (`0` for none), `-a`, `-1`, the condition at 2 for the first coordinates
-- `as` modulo `64` (`[]` for none), `array_size = arraySize`, the sieving primes `pnn`, `sp1` of
-- them in the first stage, `sp2` in the first two and `sp3` in all three, `sieve_mode = mode` and
-- `tube_cut = cut`; and the static data of the sieve as `init_sift` computes them.
private def globals (cs : Array Int) (d : Nat) (H W : Int) (all one : Bool) (as : List Nat)
    (arraySize sp1 sp2 sp3 mode : Nat) (cut : Bool) (pnn : Array Nat) : BandGlobals × SiftData :=
  let t := (initMain Tables.initial).run
  let curve := (normalizeCurve cs d true).run.1
  let ct := curveTables t curve.coeffs curve.degree pnn.toList
  let g : SiftGlobals :=
    { tables := t, curve := ct, arraySize, pnn, sievePrimes1 := sp1, sievePrimes2 := sp2
      sieve := (initSieve t ct pnn sp2 SieveTables.initial).run
      check := { curve, kummer := kummerInit curve.coeffs, height := H
                 dbound := if W ≤ 0 then H else W, dbounded := W > 0 || !all, allPoints := all
                 onePoint := one, printFormat := "(%ld, %ld, %ld, %ld)\n" }
      twoAdic := twoAdicOf curve.coeffs as, sievePrimes3 := sp3
      begmask := ~~~0 <<< ((-H) % 64).toNat.toUInt64
      endmask := ~~~0 >>> ((-H - 1) % 64).toNat.toUInt64 }
  ({ sift := g, sieveMode := mode, tubeCut := cut, kd := coeffsOf curve
     neg := (realRootsInit curve.coeffs curve.degree).run }, (initSift g SiftData.initial).run)

-- `0` or `1` for a Boolean, as the test program prints an `int`.
private def bit (r : Bool) : String := if r then "1" else "0"

-- The word `x` in hexadecimal, as `printf` prints it with `%lx`.
private def hex (x : UInt64) : String := String.ofList (Nat.toDigits 16 x.toNat)

-- The operations `ops` of the test program in turn, from the log and the state `acc`: `I` prints
-- the intervals on which `f` is negative, `N a b` the real region of the row `(a, b)`, `T a b i`
-- runs `JPoints.rowSetup` and `JPoints.tubeWord`, `S a b0 m` runs `JPoints.siftBands`, and `Q`
-- prints the counters `num_surv1`, `num_surv2`, `num_surv3` and `total`.
private def runOps (g : BandGlobals) (sd : SiftData) :
    List String → String × SiftState → String × SiftState
  | "I" :: ops, (log, s) =>
    runOps g sd ops (log ++ s!"I {g.neg.numNeg}" ++ String.join ((List.range g.neg.numNeg).map
      fun i ↦ s!" {hex g.neg.shrunkLo[i]!.bits} {hex g.neg.shrunkHi[i]!.bits}") ++ "\n", s)
  | "N" :: a :: b :: ops, (log, s) =>
    let (n, lo, hi) := (rowRegion g.neg sd a.toInt! b.toInt!).run
    runOps g sd ops (log ++ s!"N {a} {b}: {n}" ++
      String.join ((List.range n).map fun r ↦ s!" {lo[r]!} {hi[r]!}") ++ "\n", s)
  | "T" :: a :: b :: i :: ops, (log, s) =>
    let s := (rowSetup g.sift sd s a.toInt! b.toInt!).run
    let (c0, mask) := siftMask g.sift a.toInt! b.toInt!
    let (r, s) := (tubeWord g.sift sd s a.toInt! b.toInt! i.toInt! mask c0).run
    runOps g sd ops (log ++ s!"T {a} {b} {i}: {bit r} {s.curChunk}\n", s)
  | "S" :: a :: b0 :: m :: ops, (log, s) =>
    let (r, s) := (siftBands g sd s a.toInt! b0.toInt! m.toInt!).run
    runOps g sd ops (log ++ s!"S {a} {b0} {m}: {bit r} {s.tube.tubeNcells}\n", s)
  | "Q" :: ops, (log, s) =>
    runOps g sd ops (log ++ s!"Q {s.numSurv1} {s.numSurv2} {s.numSurv3} {s.out.total}\n", s)
  | _, acc => acc

-- The log of the operations `ops` from the start of the sieve with the globals `gsd`, and the
-- points printed.
private def run (gsd : BandGlobals × SiftData) (ops : String) : String × String :=
  let (log, s) := runOps gsd.1 gsd.2 (ops.splitOn " ") ("", SiftState.initial gsd.1.sift.arraySize)
  (log, s.out.text)

-- The real region of rows of `x⁶ + 1`, where `f` is negative nowhere, at `H = 1000`.
#guard run (globals #[1, 0, 0, 0, 0, 0, 1] 6 1000 0 false false [] 1000 0 0 0 2 false #[])
    "I N 5 3 N 0 7" ==
  ("I 0\nN 5 3: 1 -16 16\nN 0 7: 1 -16 16\n", "")

-- The real region of rows of `x⁶ - 10⁶`, negative on `(-10, 10)`, at `H = 1000`: of `a = 0`, the
-- interval of `c / b` meeting the row, covering a part of it or all of it; of `a > 0`, the vertex
-- `b / 2a` inside the interval and outside it, and an interval of `c` too short to exclude a word.
#guard run (globals #[-1000000, 0, 0, 0, 0, 0, 1] 6 1000 0 false false [] 1000 0 0 0 2 false #[])
    "I N 0 1 N 0 50 N 0 1000 N 1 0 N 3 -1000 N 7 100 N 500 0 N 1000 1000 N 1000 -1000" ==
  ("I 1 c023fffffffff76c 4023fffffffff76c\nN 0 1: 1 -16 16\nN 0 50: 2 -16 -7 7 16\n\
    N 0 1000: 0\nN 1 0: 1 -16 16\nN 3 -1000: 0\nN 7 100: 1 5 16\nN 500 0: 1 -1 16\n\
    N 1000 1000: 1 3 16\nN 1000 -1000: 1 3 16\n", "")

-- The real region of rows of `x⁵ - x`, negative on `(-∞, -1)` and `(0, 1)`, with an infinite end,
-- and of `-(x² - 1) (x² - 4) (x² - 9)`, negative on four intervals, two of them infinite, at
-- `H = 1000`.
#guard run (globals #[0, -1, 0, 0, 0, 1, 0] 5 1000 0 false false [] 1000 0 0 0 2 false #[])
    "I N 0 5 N 0 900 N 1 0 N 30 -999 N 500 -1000 N 999 600" ==
  ("I 2 1 3feffffffffff7ff fff0000000000000 bff0000000000801\nN 0 5: 1 -1 16\n\
    N 0 900: 2 -15 1 14 16\nN 1 0: 1 -1 16\nN 30 -999: 0\nN 500 -1000: 1 7 16\n\
    N 999 600: 2 -16 -6 1 16\n", "")
#guard run (globals #[36, 0, -49, 0, 14, 0, -1] 6 1000 0 false false [] 1000 0 0 0 2 false #[])
    "I N 0 88 N 0 287 N 2 -88 N 100 0 N 400 -900 N 1000 1000" ==
  ("I 4 4008000000000181 7ff0000000000000 3ff0000000000981 3ffffffffffff97f bffffffffffff97f \
    bff0000000000981 fff0000000000000 c008000000000181\nN 0 88: 1 -5 5\n\
    N 0 287: 3 -14 -8 -5 5 8 14\nN 2 -88: 1 15 16\nN 100 0: 2 -15 -6 -2 16\n\
    N 400 -900: 2 -15 4 7 16\nN 1000 1000: 1 -1 16\n", "")

-- The real region of rows of `(x² - 100) (x² - 400) (x² - 900)`, negative on three intervals, at
-- `H = 1000`, with up to four ranges.
#guard run (globals #[-36000000, 0, 490000, 0, -1400, 0, 1] 6 1000 0 false false [] 1000 0 0 0 2
    false #[]) "I N 0 1 N 0 20 N 1 -40 N 2 -50 N 3 10 N 1000 0" ==
  ("I 3 4034000000000691 403dfffffffff8ad c023fffffffff564 4023fffffffff564 c03dfffffffff8ad \
    c034000000000691\nN 0 1: 1 -16 16\nN 0 20: 4 -16 -9 -7 -3 3 7 9 16\n\
    N 1 -40: 3 -16 -7 4 5 6 16\nN 2 -50: 2 -16 -10 4 16\nN 3 10: 2 -16 -6 0 16\n\
    N 1000 0: 1 -1 16\n", "")

-- The sextic at `H = 300` in the tube, chunks of three words (four chunks), the primes `7, 11, 13`
-- in the first stage, `3, 5` in the second and `17, 19` in the third: `tube_word` on the first and
-- the last word of a row, with `cur_chunk` moving up and down, on a word with points and on the
-- word of the excluded `c0`; then `sift_bands` on the rows of `a = 7`.
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 300 0 false false [] 3 3 5 7 1 false
    #[2, 3, 4, 0, 1, 5, 6])
    "T 7 -300 -5 T 7 -300 4 T 7 13 -2 T 7 13 3 T 1 -1 0 T 1 2 0 Q S 7 -300 1 Q" ==
  ("T 7 -300 -5: 0 0\nT 7 -300 4: 0 3\nT 7 13 -2: 0 1\nT 7 13 3: 0 2\nT 1 -1 0: 0 1\n\
    T 1 2 0: 0 1\nQ 0 32 5 2\nS 7 -300 1: 0 299\nQ 4130 13326 3162 4\n",
    "(1, -1, 0, 4)\n(1, -1, 0, -8)\n(7, 6, -9, -74)\n(7, 6, 3, -2)\n")

-- The same with the condition at 2, which removes rows and bits.
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 300 0 false false [7] 3 3 5 7 1 false
    #[2, 3, 4, 0, 1, 5, 6]) "T 7 6 -5 T 7 -2 0 S 7 -300 1 Q" ==
  ("T 7 6 -5: 0 0\nT 7 -2 0: 0 1\nS 7 -300 1: 0 299\nQ 4130 6267 1549 2\n",
    "(7, 6, -9, -74)\n(7, 6, 3, -2)\n")

-- `x⁶ - 10⁶` at `H = 300` in the tube cut to the real region, on the rows of `a = 7` and of
-- `a = 0`.
#guard run (globals #[-1000000, 0, 0, 0, 0, 0, 1] 6 300 0 false false [] 3 3 5 7 1 true
    #[2, 3, 4, 0, 1, 5, 6]) "S 7 -300 1 Q S 0 1 1 Q" ==
  ("S 7 -300 1: 0 319\nQ 726 6468 1597 0\nS 0 1 1: 0 478\nQ 916 8257 2107 0\n", "")

-- `(x² - 100) (x² - 400) (x² - 900)` at `H = 300` in the region, the primes `7, 11` in the first
-- stage, `3, 5` in the second, `17, 19` in the third, on every third row of `a = 5` and of `a = 0`.
#guard run (globals #[-36000000, 0, 490000, 0, -1400, 0, 1] 6 300 0 false false [] 3 2 4 6 2 false
    #[2, 3, 0, 1, 5, 6]) "S 5 -300 3 Q S 0 3 3 Q" ==
  ("S 5 -300 3: 0 0\nQ 204 4882 1264 0\nS 0 3 3: 0 0\nQ 260 6417 1599 0\n", "")

-- The sextic at `H = 300` in the region with the condition at 2, on every second row of `a = 5`.
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 300 0 false false [5] 3 3 5 7 2 false
    #[2, 3, 4, 0, 1, 5, 6]) "S 5 -300 2 Q" ==
  ("S 5 -300 2: 0 0\nQ 2971 2112 387 0\n", "")

-- The sextic under `-1` in the tube, twice on the rows of `a = 1` (each stopping at the first
-- point), and in the region.
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 300 0 false true [] 3 3 5 7 1 false
    #[2, 3, 4, 0, 1, 5, 6]) "S 1 -300 1 Q S 1 -300 1 Q" ==
  ("S 1 -300 1: 1 299\nQ 2057 5527 1360 1\nS 1 -300 1: 1 598\nQ 4114 11054 2720 2\n",
    "(1, -1, 0, 4)\n(1, -1, 0, 4)\n")
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 300 0 false true [] 3 3 5 7 2 false
    #[2, 3, 4, 0, 1, 5, 6]) "S 1 -300 1 Q" ==
  ("S 1 -300 1: 1 0\nQ 2995 7853 1933 1\n", "(1, -1, 0, 4)\n")

-- The sextic `-7 + 6 x² + 6 x³ + 10 x⁴ - 7 x⁵ - 3 x⁶` at `H = 2100` in the region, chunks of 33
-- words, on every seventh row of `a = 4`: two bands, of `4095` rows and of the rest.
#guard run (globals #[-7, 0, 6, 6, 10, -7, -3] 6 2100 0 false false [] 33 3 4 5 2 false
    #[0, 1, 2, 3, 4]) "S 4 -2100 7 Q" ==
  ("S 4 -2100 7: 0 0\nQ 1172 4835 1925 0\n", "")

-- The sextic at `H = 5000` in the tube with the step `m = 5001` beyond `TUBE_BAND`: the band of the
-- one row `b = 0`.
#guard run (globals #[1, 4, 3, -8, 2, 8, 7] 6 5000 0 false false [] 1000 3 5 7 1 false
    #[2, 3, 4, 0, 1, 5, 6]) "S 3 0 5001 Q" ==
  ("S 3 0 5001: 0 47\nQ 158 897 189 0\n", "")

-- The quintic of example 2 of the README of `j-points` at `H = 200` with `-w 10` in the tube cut to
-- the real region, on the rows of `a = 16`.
#guard run (globals #[1, 178, 817, -274, 16, 1, 0] 5 200 10 false false [] 5 2 3 5 1 true
    #[0, 1, 2, 3, 4]) "I S 16 -200 1 Q" ==
  ("I 3 4014c412f8cd6d75 4018c3db4ed0c4e7 bfc963a687d245ff bf77a37be4699001 fff0000000000000 \
    c03b2dba0d19a7c9\nS 16 -200 1: 0 113\nQ 1917 22596 7280 0\n", "")

end JPoints

end
