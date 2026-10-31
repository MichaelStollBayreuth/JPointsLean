/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Check
public import JPoints.Model.Choice
public import JPoints.Model.Constants
public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import JPoints.Model.Kummer
public import JPoints.Model.Region
public import JPoints.Model.Sift
public import JPoints.Model.Sturm
public import JPoints.Model.Tube

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Choice
meta import JPoints.Model.Input
meta import JPoints.Model.Region

/-!
# The sample of the tube and of the real region

What `j-points` does for the analysis of the plane of `(b, c)` before the choice of the primes
(`tube_init`, `JPoints.tubeInit`): the coefficients of the Kummer surface and of the curve searched
as doubles (`JPoints.tubeInitCoeffs`), the intervals on which `f` is negative
(`JPoints.realRootsInit`), and the sample of the rows (`tube_sample`, `JPoints.tubeSample`) from
which the cost model learns what the analysis of the tube and the real region leave of a row. The
sample is 24 bands of up to 64 rows, of first coordinates spread over the box
(`JPoints.tubeSampleRange`); each band is analysed as `sift_bands` analyses its bands
(`JPoints.tubeSampleBand`), when the fourth coordinate is bounded, and each of its rows measured
(`JPoints.tubeSampleRow`): the words of the tube, as they are and cut to the real region
(`JPoints.rowCut`), and the words and the ranges of the real region (`JPoints.rowRegion`). The
statistics are the sums per row (`JPoints.tubeSampleStats`).

## Main definitions

* `JPoints.TubeSampleSums`: the sums of the sample.
* `JPoints.tubeSampleRange`, `JPoints.tubeSampleBand`, `JPoints.tubeSampleRow`,
  `JPoints.tubeSampleStats`, `JPoints.tubeSample`: the sample of the rows.
* `JPoints.tubeInitCoeffs`, `JPoints.tubeInit`: the coefficients of the analysis, and the start of
  the analysis.

## Implementation notes

The analysis of the bands and the real region of the rows are those of the search
(`JPoints.tubeCell`, `JPoints.rowRegion`), with their doubles of `JPoints.Model.DoubleArith`, and
so is the root of the height bound that limits the first coordinates of a monic quintic. The sums
of the sample and the statistics feed only the cost model and its message, and are Lean's `Float`s,
the doubles of the platform, in the order of the C code; the integers that the sample converts to
doubles are below `2 ^ 53` and convert exactly, and no statistic is a NaN (the sums are finite and
nonnegative, and a quotient is taken only by a positive number of rows), so that `Float.toBits`
gives the bits of the C code.

`tube_sample` writes the statics `th`, `th2`, `w_low_all` and `w_high_all` of the sieve, which
`init_sift` sets to the same values later, and the state of the analysis of the thread that runs it,
whose statics of `tube_cell` and whose count `tube_ncells` the search inherits; both are taken and
returned (`JPoints.SiftData`, `JPoints.TubeState`). The globals that `tube_init` writes, the
coefficients of the analysis (`JPoints.TubeCoeffs`), `sieve_mode` (`JPoints.Plan`), the intervals
on which `f` is negative (`JPoints.NegativeIntervals`) and the statistics (`JPoints.TubeStats`),
are returned.
-/

@[expose] public section

namespace JPoints

/-! ### The sample of the rows -/

/-- The sums of `tube_sample` over the rows of its sample: the number of the rows (`rows`), of those
that meet the real region (`left`) and of those with a word in the tube (`tleft`); the words of the
tube (`twords`), the words of the tube cut to the real region (`tcut`), the cells of the analysis
(`cells`), the words of the real region (`rwords`) and its ranges (`ranges`). The defaults are the
initial values, `0` and `0.0`.

It models no C code of its own: the locals of `JPoints.tubeSample`, which declares them. -/
structure TubeSampleSums where
  /-- `rows`, the number of the rows of the sample. -/
  rows : Int := 0
  /-- `left`, the number of the rows that meet the real region. -/
  left : Nat := 0
  /-- `tleft`, the number of the rows with a word in the tube. -/
  tleft : Nat := 0
  /-- `twords`, the number of the words of the tube. -/
  twords : Float := 0.0
  /-- `tcut`, the number of the words of the tube cut to the real region. -/
  tcut : Float := 0.0
  /-- `cells`, the number of the cells of the analysis of the tube. -/
  cells : Float := 0.0
  /-- `rwords`, the number of the words of the real region. -/
  rwords : Float := 0.0
  /-- `ranges`, the number of the ranges of words of the real region. -/
  ranges : Float := 0.0

/-- The `k`-th band of the sample of `tube_sample`, for the curve searched `curve` and the height
bound `height ≥ 1`: the first coordinate `a = 7919 k mod (height + 1)`, reduced modulo
`⌊√height + 1⌋` and squared when `f` is a monic quintic, whose first coordinates are the squares;
and the rows from `b_lo = 104729 k mod (2 height + 1) - height`, raised to `1` when `a = 0`, to
`b_hi = b_lo + 63`, cut at the height bound. The first coordinate, and the first and the last row.

C: `j-sift.c:736-742`

Deviation: the curve and the height bound passed, for the globals that it reads; the first
coordinate and the rows returned, for the locals of `tube_sample`; integers for the `long`s, with
`Int.tmod` for C's `%` on the nonnegative operands; `JPoints.Double.ofInt` for the conversion of the
`long` `height`, exact, `JPoints.Double.sqrt`, `JPoints.Double.floor` and the sum with `1.0` for
`floor(sqrt((double)height) + 1)`, and `JPoints.Double.toInt64` for the cast to a `long`, which
truncates. -/
def tubeSampleRange (curve : SearchCurve) (height : Int) (k : Nat) : Int × Int × Int :=
  let a := ((k : Int) * 7919).tmod (height + 1)
  let a := if curve.degree == 5 && curve.coeffs[5]! == 1 then
      let a := a.tmod (Double.floor (Double.sqrt (Double.ofInt height) + 1.0)).toInt64.toInt
      a * a
    else a
  let bLo := ((k : Int) * 104729).tmod (2 * height + 1) - height
  let bLo := if a == 0 && bLo < 1 then 1 else bLo
  let bHi := bLo + 63
  (a, bLo, if bHi > height then height else bHi)

/-- The band of the rows `b_lo ≤ b ≤ b_hi` of the first coordinate `a` set up and analysed by
`tube_sample` in the state `t` of the analysis of the tube: the polynomials of `a`
(`JPoints.tubeAInit`), the count `tube_ncells` of the cells set to `0`, the first row of the band
`band_b0 = b_lo`, the numbers of the ranges of its rows set to `0`, and, when the fourth coordinate
is bounded (`dbounded`), the words of the tube collected by the analysis of the band over the words
`w_low ≤ i < w_high` of a whole row (`JPoints.tubeCell`), with the bound `th` and its square `th2`
of the static data `sd`.

C: `j-sift.c:743-747`

Deviation: the state of the analysis taken and returned, for the thread-local globals of the bands
and the globals of the analysis; the globals and the statics that it reads passed; integers for the
`long`s `a`, `b_lo`, `b_hi`, `w_low` and `w_high`; the loop `for(b = b_lo; b <= b_hi; b++)` over
`b = b_lo + k` for `k < b_hi - b_lo + 1`; the bands taken out of the state while their counts are
written, so that they are not shared. -/
def tubeSampleBand (g : CheckGlobals) (kd : TubeCoeffs) (sd : SiftData) (t : TubeState)
    (a bLo bHi wLow wHigh : Int) : Id TubeState := do
  let t ← tubeAInit kd g.height sd.th sd.th2 t a
  let t := { t with tubeNcells := 0 }
  let mut bands := t.bands
  let t := { t with bands := default }
  bands := { bands with bandB0 := bLo }
  for k in [0:(bHi - bLo + 1).toNat] do bands := { bands with bandNr := bands.bandNr.set! k 0 }
  if g.dbounded then return ← tubeCell sd.th sd.th2 { t with bands } bLo bHi wLow wHigh
  return { t with bands }

/-- The row `(a, b)` of the band from the row `b_lo` on, with the bands `bd`, measured by
`tube_sample` into the sums `s`: the words of the ranges of the real region of the row
(`JPoints.rowRegion`) added to `rwords`, their number to `ranges`, and the row counted in `left`
when it meets the region; the words of the ranges of the row in the band cut to the real region
(`JPoints.rowCut`) added to `tcut`; the words of the ranges of the row in the band added to
`twords`, and the row counted in `tleft` when it has any.

C: `j-sift.c:749-757`

Deviation: the sums taken and returned, for the locals of the caller; the ranges of the real region
and of the cut returned as arrays of their number, for the local arrays `reglo`, `reghi`, `rlo` and
`rhi`; the intervals, the static data and the bands passed, for the globals and the statics that it
reads; integers for the `long`s `a`, `b` and `b_lo` and for the ends of the ranges; a natural number
for the index `b - b_lo` of the row in the band and for the counts; `Float.ofInt` and `Float.ofNat`
for the conversions of the `long`s to doubles, exact. -/
def tubeSampleRow (neg : NegativeIntervals) (sd : SiftData) (bd : TubeBands) (s : TubeSampleSums)
    (a b bLo : Int) : Id TubeSampleSums := do
  let row := (b - bLo).toNat
  let mut s := s
  let (nreg, reglo, reghi) ← rowRegion neg sd a b
  for r in [0:nreg] do s := { s with rwords := s.rwords + Float.ofInt (reghi[r]! - reglo[r]!) }
  s := { s with ranges := s.ranges + Float.ofNat nreg }
  if nreg > 0 then s := { s with left := s.left + 1 }
  let (n, rlo, rhi) ← rowCut bd row nreg reglo reghi
  for r in [0:n] do s := { s with tcut := s.tcut + Float.ofInt (rhi[r]! - rlo[r]!) }
  for r in [0:bd.bandNr[row]!] do
    s := { s with twords := s.twords + Float.ofInt (bd.bhi row r - bd.blo row r) }
  if bd.bandNr[row]! > 0 then s := { s with tleft := s.tleft + 1 }
  return s

/-- The statistics of `tube_sample` from its sums `s`: the words of the tube per row, as they are
and cut to the real region, the cells of the analysis per row, the fraction of the rows with a word
in the tube, the words and the ranges of the real region per row, and the fraction of the rows that
meet it; each `1.0` when the sample has no rows.

C: `j-sift.c:762-768`

Deviation: the statistics returned, for the globals that the C code writes through the pointers of
its arguments; `Float.ofInt` and `Float.ofNat` for the conversions of the `long`s, exact. -/
def tubeSampleStats (s : TubeSampleSums) : TubeStats :=
  let rows := Float.ofInt s.rows
  { tubeWords := if s.rows > 0 then s.twords / rows else 1.0
    tubeWordsCut := if s.rows > 0 then s.tcut / rows else 1.0
    tubeCells := if s.rows > 0 then s.cells / rows else 1.0
    tubeRows := if s.rows > 0 then Float.ofNat s.tleft / rows else 1.0
    regWords := if s.rows > 0 then s.rwords / rows else 1.0
    regRanges := if s.rows > 0 then s.ranges / rows else 1.0
    regRows := if s.rows > 0 then Float.ofNat s.left / rows else 1.0 }

/-- `tube_sample`, the statistics of the analysis of the tube and of the real region for the cost
model, on a sample of 24 bands of up to 64 rows (`JPoints.tubeSampleRange`), with the coefficients
`kd` of the analysis and the intervals `neg` on which `f` is negative: the statics `th = dbound`
and `th2 = th * th`, `w_low_all = ⌊-height / 64⌋` and `w_high_all = ⌊height / 64⌋ + 1` of the
static data `sd` set; then for each band its analysis (`JPoints.tubeSampleBand`), its rows
measured in order (`JPoints.tubeSampleRow`), and the cells that the analysis visited and the rows
added to the sums; the statistics from the sums (`JPoints.tubeSampleStats`). The static data, the
state of the analysis, and the statistics.

C: `j-sift.c:727-733`, `j-sift.c:735`, `j-sift.c:748`, `j-sift.c:758-761`, `j-sift.c:769-770`

Deviation: the static data and the state of the analysis taken and returned, for the statics and the
thread-local globals that it writes; the globals that it reads passed; the statistics returned, for
the globals that the C code writes through the pointers of its arguments; the sums in a structure,
for the locals (`JPoints.TubeSampleSums`), `Float`s for the doubles, an integer for the `long`
`rows` and natural numbers for the `long`s `left` and `tleft`, which count up from `0`; `>>>` on
integers for C's `>>` on the `long`s, which gcc shifts arithmetically also for the negative
`-height`; `JPoints.Double.ofInt` for the conversion of the `long` `dbound`, rounded to nearest; the
loop `for(b = b_lo; b <= b_hi; b++)` over `b = b_lo + j` for `j < b_hi - b_lo + 1`; `Float.ofNat`
for the conversion of the `long` `tube_ncells`, exact. -/
def tubeSample (g : CheckGlobals) (kd : TubeCoeffs) (neg : NegativeIntervals) (sd : SiftData)
    (t : TubeState) : Id (SiftData × TubeState × TubeStats) := do
  let wLow := (-g.height) >>> longShift
  let wHigh := (g.height >>> longShift) + 1
  let th := Double.ofInt g.dbound
  let sd := { sd with th, th2 := th * th, wLowAll := wLow, wHighAll := wHigh }
  let mut t := t
  let mut s : TubeSampleSums := {}
  for k in [0:24] do
    let (a, bLo, bHi) := tubeSampleRange g.curve g.height k
    t ← tubeSampleBand g kd sd t a bLo bHi wLow wHigh
    for j in [0:(bHi - bLo + 1).toNat] do s ← tubeSampleRow neg sd t.bands s a (bLo + j) bLo
    s := { s with cells := s.cells + Float.ofNat t.tubeNcells, rows := s.rows + (bHi - bLo + 1) }
  return (sd, t, tubeSampleStats s)

/-! ### The start of the analysis -/

/-- The coefficients of the analysis of the tube as `tube_init` sets them: the coefficients
`k400, …, k004` of the quartic `K₀` (`k`) and the coefficients `f₀, …, f₆` of the curve searched
(`curve`), each by `mpz_get_d` (`JPoints.Double.mpzGetD`).

C: `j-points.c:1472-1480`

Deviation: the curve and the coefficients `k` passed, for the globals that it reads; the
coefficients returned, for the globals `kd400, …, kd004` and `fd` that the C code writes; the array
`fd` filled by the loop over `n ≤ 6` from seven zeros, for the global array, every entry of which
the loop writes. -/
def tubeInitCoeffs (curve : SearchCurve) (k : KummerCoeffs) : Id TubeCoeffs := do
  let d := Double.mpzGetD
  let mut fd : Array Double := .replicate 7 .zero
  for n in [0:7] do fd := fd.set! n (d curve.coeffs[n]!)
  return {
    kd400 := d k.k400, kd310 := d k.k310, kd301 := d k.k301, kd220 := d k.k220, kd211 := d k.k211,
    kd202 := d k.k202, kd130 := d k.k130, kd121 := d k.k121, kd112 := d k.k112, kd103 := d k.k103,
    kd040 := d k.k040, kd031 := d k.k031, kd022 := d k.k022, kd013 := d k.k013, kd004 := d k.k004,
    fd }

/-- `tube_init`, the start of the analysis of the plane of `(b, c)`, after `kummer_init`: the
coefficients of the analysis (`JPoints.tubeInitCoeffs`) from the curve searched and its quartic
`K₀` in `g`, `sieve_mode = 0` in the plan, the intervals on which `f` is negative
(`JPoints.realRootsInit`), and the sample of the rows (`JPoints.tubeSample`), with the static data
`sd` of the sieve and the state `t` of the analysis of the thread. The coefficients, the plan, the
intervals, the static data, the state of the analysis, and the statistics of the sample.

C: `j-points.c:1469-1471`, `j-points.c:1481-1485`

Deviation: the globals that it writes returned, the plan, the static data and the state of the
analysis taken and returned; the globals that it reads passed. -/
def tubeInit (g : CheckGlobals) (plan : Plan) (sd : SiftData) (t : TubeState) :
    Id (TubeCoeffs × Plan × NegativeIntervals × SiftData × TubeState × TubeStats) := do
  let kd ← tubeInitCoeffs g.curve g.kummer
  let plan := { plan with sieveMode := 0 }
  let neg ← realRootsInit g.curve.coeffs g.curve.degree
  let (sd, t, stats) ← tubeSample g kd neg sd t
  return (kd, plan, neg, sd, t, stats)

/-! ### Examples

From a test program that includes `j-points.c` and `j-sift.c` of the pin (the statics of
`tube_cell` moved out of the function, so that it can print them) and runs `main` up to `tube_init`
on the command line given: `read_input`, `normalise_curve`, `kummer_init` and `tube_init`; then it
prints the seven statistics of `tube_sample` by their bits, `th` and `th2` by their bits,
`w_low_all`, `w_high_all`, `num_neg`, `sieve_mode`, `tube_ok` and `tube_ncells` of the last band,
the statics `last_rb` and `last_rc` of `tube_cell` by their bits, `band_b0`, a hash of the bits of
the polynomials `K0`, `K1`, `K2` and `KA` of the last band, and a hash of the counts and the ranges
of the rows of the last band. -/

-- The word `x` in hexadecimal, as `printf` prints it with `%lx`.
private def hex (x : UInt64) : String := String.ofList (Nat.toDigits 16 x.toNat)

-- One step of the hash of the test program.
private def mix (h x : UInt64) : UInt64 :=
  let h := (h ^^^ x) * 0x100000001b3
  h ^^^ (h >>> 32)

-- The hash of the bits of the polynomials `K0`, `K1`, `K2` and `KA` of the state.
private def polysHash (t : TubeState) : UInt64 :=
  (t.k0 ++ t.k1 ++ t.k2 ++ t.ka).foldl (fun h x ↦ mix h x.bits) 0xcbf29ce484222325

-- The hash of the counts and the ranges of the first `n` rows of the bands, the ends as the
-- `unsigned long`s of their two's complement.
private def bandsHash (bd : TubeBands) (n : Nat) : UInt64 :=
  (List.range n).foldl (init := 0xcbf29ce484222325) fun h row ↦
    (List.range bd.bandNr[row]!).foldl
      (fun h r ↦ mix (mix h (Int64.ofInt (bd.blo row r)).toUInt64)
        (Int64.ofInt (bd.bhi row r)).toUInt64)
      (mix h bd.bandNr[row]!.toUInt64)

-- The line of the test program for the command line `args` of `j-points` (after the name of the
-- program).
private def sample (args : Array String) : String :=
  match (Cli.readInput args).run with
  | .error _ => "error"
  | .ok inp =>
    let curve := (normalizeCurve inp.coeffs inp.degree.toNat true).run.1
    let g : CheckGlobals :=
      { curve, kummer := kummerInit curve.coeffs, height := inp.height, dbound := inp.dbound
        dbounded := inp.dbounded, allPoints := inp.allPoints, onePoint := inp.onePoint
        printFormat := inp.printFormat }
    let (_, plan, neg, sd, t, st) := (tubeInit g {} SiftData.initial TubeState.initial).run
    let bLo := t.bands.bandB0
    let n := ((if bLo + 63 > inp.height then inp.height else bLo + 63) - bLo + 1).toNat
    " ".intercalate <|
      ([st.tubeWords, st.tubeWordsCut, st.tubeCells, st.tubeRows, st.regWords, st.regRanges,
        st.regRows].map fun x ↦ hex x.toBits) ++
      [hex sd.th.bits, hex sd.th2.bits, toString sd.wLowAll, toString sd.wHighAll,
        toString neg.numNeg, toString plan.sieveMode, if t.tubeOk then "1" else "0",
        toString t.tubeNcells, hex t.cache.lastRb.bits, hex t.cache.lastRc.bits, toString bLo,
        hex (polysHash t), hex (bandsHash t.bands n)]

-- Sextics of `testcurves2` at their height bounds: one where `f` is negative nowhere; one at a
-- height bound below 64, where every band is cut at the height bound; one with a negative leading
-- coefficient, so that two intervals on which `f` is negative are infinite.
#guard sample #["1 4 3 -8 2 8 7", "255"] ==
  "401bdd99292c199e 401bdd99292c199e 3fd0609e19fbf96a 3ff0000000000000 4020000000000000 " ++
  "3ff0000000000000 3ff0000000000000 406fe00000000000 40efc02000000000 -4 4 0 0 1 15 " ++
  "403f800000000000 403f800000000000 169 726b56e8c2aad351 5f653b72b063cc18"
#guard sample #["-7 0 6 6 10 -7 -3", "63"] ==
  "4000000000000000 3ff8b67616983174 3faeb1c59868051e 3ff0000000000000 3ff8b67616983174 " ++
  "3fed712f88a1ff93 3fed712f88a1ff93 404f800000000000 40af020000000000 -1 1 3 0 1 3 " ++
  "4034800000000000 403f800000000000 22 4d966fa968cdd2b9 c75ee7f42000bf35"
#guard sample #["3 2 -1 4 1 -2 -1", "300"] ==
  "401c06c934150955 400cc41d2df98da8 3fd2114dde68d7cb 3fed491e5dfc448a 4015aee86b37d080 " ++
  "3feef5fd9ffa923d 3feef5fd9ffa923d 4072c00000000000 40f5f90000000000 -5 5 2 0 1 19 " ++
  "4034000000000000 403f800000000000 260 358e5d6d3bbbe9d8 c8ad0c3656c35d4c"

-- Monic quintics, whose first coordinates are squares (`a` reduced modulo `⌊√height + 1⌋` and
-- squared): one as given, one that `normalise_curve` makes by negation (`f₅ = -1`), and one by
-- the reversal of a sextic with `f₀ = 0` and `f₁ = 1`.
#guard sample #["1 178 817 -274 16 1", "2000"] ==
  "402ee47391ce4739 40239fea7fa9fea8 3fe3dd0f743dd0f7 3ff0000000000000 404ae952a54a952a " ++
  "3ff6096825a09682 3febf7efdfbf7efe 409f400000000000 414e848000000000 -32 32 3 0 1 125 " ++
  "403f800000000000 403f800000000000 -1835 2d98d5b6477231f6 88cb9de48004ce3e"
#guard sample #["5 -2 3 1 -1 -1", "300"] ==
  "402103e6e458e55d 40179575e7e8ed82 3fd1a4ba9d184281 3ff0000000000000 401d8da81f3722c7 " ++
  "3fecabaf3f476c11 3fecabaf3f476c11 4072c00000000000 40f5f90000000000 -5 5 1 0 1 13 " ++
  "4034000000000000 4057e00000000000 260 1f45406beb27de8e f2533aeca9c22703"
#guard sample #["0 1 2 -1 3 1 1", "300"] ==
  "401c4740a2dce1f9 4014318995ccc41d 3fd0cb941a7717ec 3fedc5fae918f039 401fea48f2efe224 " ++
  "3fecabaf3f476c11 3fecabaf3f476c11 4072c00000000000 40f5f90000000000 -5 5 1 0 1 11 " ++
  "4034000000000000 404fc00000000000 260 4812db28b6b41ef3 b067ab58a485cd9f"

-- The bound on the fourth coordinate: under `-a` without `-w` the fourth coordinate is not
-- bounded, no cell is analysed and the statics of `tube_cell` keep their initial `-1.0`; under
-- `-a` with `-w 50`, and `-w 10` and `-w 3` without `-a`, the tube of the bound given.
#guard sample #["-36 0 49 0 -14 0 1", "300", "-a"] ==
  "0 0 0 0 40175707a25a97aa 3ff7db5b19f4cd9d 3ff0000000000000 4072c00000000000 " ++
  "40f5f90000000000 -5 5 3 0 1 0 bff0000000000000 bff0000000000000 260 b7271c1d9b26a036 " ++
  "b067ab58a485cd9f"
#guard sample #["-36 0 49 0 -14 0 1", "300", "-a", "-w", "50"] ==
  "40064c5789eca8f8 40000eedd8fb1487 3fc9f4cd9d43b09b 3fea923cbbf88914 40175707a25a97aa " ++
  "3ff7db5b19f4cd9d 3ff0000000000000 4049000000000000 40a3880000000000 -5 5 3 0 1 19 " ++
  "4034000000000000 403f800000000000 260 5cfe2c06944e4692 f2533aeca9c22703"
#guard sample #["1 6 5 22 22 8 1", "500", "-w", "10"] ==
  "40126b94c754bbd1 400c2ec640679f93 3fd77a2737f30c0e 3ff0000000000000 4022f6d33459f368 " ++
  "3ff1aa01cc8c52c1 3ff0000000000000 4024000000000000 4059000000000000 -8 8 1 0 1 23 " ++
  "403f800000000000 404fc00000000000 -139 731250709cf52a1f 18ce038aa2bbb21a"
#guard sample #["7 0 0 0 0 0 -1", "300", "-w", "3"] ==
  "4016b99883a5bf32 401100824a4e60b3 3fd0f702349753a3 3ff0000000000000 40197aa7f3c908a7 " ++
  "3feef5fd9ffa923d 3feef5fd9ffa923d 4008000000000000 4022000000000000 -5 5 2 0 1 19 " ++
  "4034000000000000 403f800000000000 260 7bf01aa2d493bca e70f93d5072a7582"

-- Large coefficients: `f₀` and `f₆` beyond `2 ^ 64`, as in `testcurves2`; and coefficients of
-- `10 ^ 150`, where the analysis decides nothing (`tube_ok` false) and takes each band whole, in
-- one cell.
#guard sample #["123456789012345678901 2 -3 1 4 -1 3", "200"] ==
  "401920212a7e7202 401920212a7e7202 3fcd052ea3c1d053 3fef22e4b507f22e 4020000000000000 " ++
  "3ff0000000000000 3ff0000000000000 4069000000000000 40e3880000000000 -4 4 0 0 1 3 " ++
  "4033800000000000 405fe00000000000 161 f5f40e585ad7b4f3 291d8aeb9ad3349d"
#guard sample #["3 -1 2 1 -1 2 123456789012345678901", "200"] ==
  "401ca5239597aa52 401ca5239597aa52 3fcf17d68ae1f17d 3ff0000000000000 4020000000000000 " ++
  "3ff0000000000000 3ff0000000000000 4069000000000000 40e3880000000000 -4 4 0 0 1 15 " ++
  "4033800000000000 403f800000000000 161 9fac879c479b9dae 700f896e1405dc3f"
#guard
  let e := "1".pushn '0' 150
  sample #[s!"{e} 3 -{"1".pushn '0' 149} 7 1 {e} 1", "1000"] ==
  "4040000000000000 4040000000000000 3f90000000000000 3ff0000000000000 4040000000000000 " ++
  "3ff0000000000000 3ff0000000000000 408f400000000000 412e848000000000 -16 16 0 0 0 1 " ++
  "bff0000000000000 bff0000000000000 564 a26df2603614aa60 5fb0ebc51b0f769b"

end JPoints
