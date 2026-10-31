/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants
public import JPoints.Model.Double
public import JPoints.Model.DoubleArith
public import JPoints.Model.Kummer

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Constants
meta import JPoints.Model.DoubleArith
meta import JPoints.Model.Kummer

/-!
# The analysis of the tube

The analysis of the plane of `(b, c)` of `j-points` for a first coordinate `a`, when the fourth
coordinate `d` is bounded by `W = th`: a point `(a : b : c : d)` with `|d| ≤ W` needs a root in
`[-W, W]` of the Kummer equation `Q(d) = k₂ d² + k₁ d + k₀`, whose coefficients are polynomials in
`(b, c)` for the fixed `a`. `tube_a_init` (`JPoints.tubeAInit`) computes them in doubles for the
`a` in hand, `K₀` of degree 4, `K₁` of degree 3 and `K₂ = b² - 4 a c`, with the absolute
polynomial `KA` of the coefficients `|K₀| + W |K₁| + W² |K₂|`, the scale of the rounding errors,
and decides whether the analysis may decide anything at all (`tube_ok`). `tube_cell`
(`JPoints.tubeCell`) analyses a cell of rows by words of the plane: it shifts the polynomials to
the centre of the cell (`JPoints.shift2`, `JPoints.shift1`), bounds the terms that are not constant
over the cell (`JPoints.tubeSum`), and from the signs that the bounds show (`JPoints.polySign`)
drops the cell, takes it whole, or halves it, in words or in rows, down to leaves of at most
`JPoints.tubeRows` rows by one word; the words that it keeps go to the ranges of the rows of the
band of rows in hand (`tube_emit`, `JPoints.tubeEmit`), which the thread keeps
(`JPoints.TubeBands`). `row_cut` (`JPoints.rowCut`) intersects the ranges of a row of the band with
the ranges of the real region of the row.

## Main definitions

* `JPoints.TubeCoeffs`, `JPoints.tubeInitCoeffs`: the coefficients of the Kummer surface and of
  the curve as doubles, as `tube_init` sets them.
* `JPoints.numCoeffs`, `JPoints.coeffIndex`: the arrays of the coefficients of polynomials in two
  variables.
* `JPoints.TubeBands`, `JPoints.TubeBands.initial`, `JPoints.TubeBands.blo`,
  `JPoints.TubeBands.bhi`, `JPoints.TubeBands.setBlo`, `JPoints.TubeBands.setBhi`: the bands of the
  tube.
* `JPoints.TubeCellCache`, `JPoints.TubeState`, and their values `JPoints.TubeCellCache.initial`
  and `JPoints.TubeState.initial` when the program starts: the state of the analysis of the tube.
* `JPoints.tubeEval`, `JPoints.tubeAInitK0`, `JPoints.tubeAInitK1K2`, `JPoints.tubeAInit`: the
  polynomials of the analysis for a first coordinate.
* `JPoints.shift1`, `JPoints.shift2`, `JPoints.tubeSum`, `JPoints.polySign`: the Taylor shifts and
  the bounds over a cell.
* `JPoints.tubeEmit`, `JPoints.tubeEmitRows`: the words collected for the rows of the band.
* `JPoints.tubeCellProducts`, `JPoints.tubeCellCombine`, `JPoints.tubeCellAnalyze`,
  `JPoints.tubeCellDecide`, `JPoints.tubeCell`: the analysis of a cell.
* `JPoints.rowCut`: the ranges of a row of the band cut to the real region.

## Implementation notes

Every double of the analysis decides which words of a row are sieved, so each is a
`JPoints.Double` and each operation on it is that of `JPoints.Model.DoubleArith`, in the order of
the C code. The arrays of the coefficients are arrays of `JPoints.numCoeffs` doubles, the
coefficient of `b ^ j c ^ k` at `JPoints.coeffIndex j k`, and a pointer into one of them is the
array and an index. The `long`s that may be negative (the rows `b` and the indices of the words)
are integers, the counts natural numbers.

The globals and the statics that the analysis writes, `K0`, `K1`, `K2`, `KA`, `tube_ok`,
`tube_ncells`, the statics of `tube_cell` and the bands, form the state `JPoints.TubeState`, which
is taken and returned; `JPoints.SiftState` holds it for the one thread of a run. What it only reads,
the coefficients `JPoints.TubeCoeffs`, the height bound and the bound `th` on the fourth
coordinate with its square `th2`, is passed. `JPoints.tubeEmitRows` takes the bands out of the
state while it writes them, so that they are not shared and the compiled code writes them in place.

The recursion of `tube_cell` ends because each call halves its cell in words while it has more
than one, or in rows while it has more than `JPoints.tubeRows ≥ 1` (`JPoints.tubeRows_pos`): the
model's recursion is well founded on the number of rows and words of the cell.
-/

@[expose] public section

namespace JPoints

/-! ### The coefficients and the state -/

/-- The coefficients of the analysis of the tube as doubles, the globals of `j-points.c` that
`tube_init` sets: `kd400, …, kd004`, the coefficients `k400, …, k004` of the quartic `K₀` of the
Kummer surface (`JPoints.KummerCoeffs`) as `mpz_get_d` gives them, and `fd`, at `n ≤ 6`, the
coefficient `fₙ` of the curve searched as `mpz_get_d` gives it.

C: `j-points.c:225-227`

Deviation: an array of seven doubles for the array `fd`; a structure, for the globals, without the
zeros of static storage, which nothing reads: `tube_init` writes every field first. -/
structure TubeCoeffs where
  /-- `kd400`, `k400` as a double. -/
  kd400 : Double
  /-- `kd310`, `k310` as a double. -/
  kd310 : Double
  /-- `kd301`, `k301` as a double. -/
  kd301 : Double
  /-- `kd220`, `k220` as a double. -/
  kd220 : Double
  /-- `kd211`, `k211` as a double. -/
  kd211 : Double
  /-- `kd202`, `k202` as a double. -/
  kd202 : Double
  /-- `kd130`, `k130` as a double. -/
  kd130 : Double
  /-- `kd121`, `k121` as a double. -/
  kd121 : Double
  /-- `kd112`, `k112` as a double. -/
  kd112 : Double
  /-- `kd103`, `k103` as a double. -/
  kd103 : Double
  /-- `kd040`, `k040` as a double. -/
  kd040 : Double
  /-- `kd031`, `k031` as a double. -/
  kd031 : Double
  /-- `kd022`, `k022` as a double. -/
  kd022 : Double
  /-- `kd013`, `k013` as a double. -/
  kd013 : Double
  /-- `kd004`, `k004` as a double. -/
  kd004 : Double
  /-- `fd`, at `n ≤ 6`, the coefficient `fₙ` of the curve searched as a double. -/
  fd : Array Double
  deriving Repr

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

/-- `NC`, the number `L * L` of the entries of an array of the coefficients of a polynomial in two
variables, for `L = JPoints.coeffRow`.

C: `j-sift.c:426` -/
def numCoeffs : Nat := coeffRow * coeffRow

/-- `P(j, k)`, the index `L j + k` of the coefficient of `b ^ j c ^ k` (or `s ^ j t ^ k`) in an
array of the coefficients of a polynomial in two variables, for `L = JPoints.coeffRow`.

C: `j-sift.c:427` -/
def coeffIndex (j k : Nat) : Nat := coeffRow * j + k

/-- The bands of the tube of the thread: the first row `band_b0` of the band in hand, and for its
`row`-th row, `row < TUBE_BAND`, the number `band_nr[row]` of the ranges of words that the analysis
of the tube collected for it, and the ranges `[BLO(row, k), BHI(row, k))` for `k < band_nr[row]`
in `band_rg` (`JPoints.TubeBands.blo`, `JPoints.TubeBands.bhi`).

C: `j-sift.c:121-123`

Deviation: arrays for the arrays that `band_nr` and `band_rg` point to, one flat array of
`2 TUBE_RANGES TUBE_BAND` entries for the array of the rows of `band_rg`, the `k`-th range of the
`row`-th row at the indices `2 TUBE_RANGES row + 2 k` and `2 TUBE_RANGES row + 2 k + 1`; integers
for the `long`s of the first row and of the ends of the ranges, natural numbers for the counts; a
structure, for the thread-local globals of the one thread. -/
structure TubeBands where
  /-- `band_b0`, the first row of the band. -/
  bandB0 : Int
  /-- `band_nr`, at `row`, the number of the ranges of the `row`-th row of the band. -/
  bandNr : Array Nat
  /-- `band_rg`, at `2 TUBE_RANGES row + 2 k` and at the index after it, the ends of the `k`-th
  range of the `row`-th row of the band. -/
  bandRg : Array Int
  deriving Inhabited

/-- The bands of the tube when the analysis first runs: `band_b0 = 0`, and the arrays of
`TUBE_BAND` counts and of `TUBE_BAND` rows of ranges that `init_thread_sieve` allocates.

C: `j-sift.c:121-123`

Deviation: fresh arrays of zeros, for the arrays that `init_thread_sieve` allocates (memory
management, not modelled), whose pointers start as null pointers; the C code sets each count of a
band to `0` before it reads it and reads only the ranges that the count covers. -/
def TubeBands.initial : TubeBands where
  bandB0 := 0
  bandNr := .replicate tubeBand 0
  bandRg := .replicate (2 * tubeRanges * tubeBand) 0

/-- `BLO(row, k)`, the lower end of the `k`-th range of the `row`-th row of the band.

C: `j-sift.c:124`

Deviation: the index `2 TUBE_RANGES row + 2 k` of the flat array `band_rg`. -/
def TubeBands.blo (bd : TubeBands) (row k : Nat) : Int := bd.bandRg[2 * tubeRanges * row + 2 * k]!

/-- `BHI(row, k)`, the upper end of the `k`-th range of the `row`-th row of the band, the first word
after it.

C: `j-sift.c:125`

Deviation: the index `2 TUBE_RANGES row + 2 k + 1` of the flat array `band_rg`. -/
def TubeBands.bhi (bd : TubeBands) (row k : Nat) : Int :=
  bd.bandRg[2 * tubeRanges * row + 2 * k + 1]!

/-- The assignment `BLO(row, k) = v` of the macro `BLO`, the lower end of the `k`-th range of the
`row`-th row of the band set to `v`.

C: `j-sift.c:124`

Deviation: the index `2 TUBE_RANGES row + 2 k` of the flat array `band_rg`; the bands returned. -/
def TubeBands.setBlo (bd : TubeBands) (row k : Nat) (v : Int) : TubeBands :=
  { bd with bandRg := bd.bandRg.set! (2 * tubeRanges * row + 2 * k) v }

/-- The assignment `BHI(row, k) = v` of the macro `BHI`, the upper end of the `k`-th range of the
`row`-th row of the band set to `v`.

C: `j-sift.c:125`

Deviation: the index `2 TUBE_RANGES row + 2 k + 1` of the flat array `band_rg`; the bands
returned. -/
def TubeBands.setBhi (bd : TubeBands) (row k : Nat) (v : Int) : TubeBands :=
  { bd with bandRg := bd.bandRg.set! (2 * tubeRanges * row + 2 * k + 1) v }

/-- The statics of `tube_cell`, which the thread keeps from cell to cell: the products
`rp[P(j, k)] = rb ^ j rc ^ k` for `j, k < L` of the half-sizes `rb` and `rc` of the last cell whose
products it computed, and those half-sizes `last_rb` and `last_rc`, `-1.0` before the first.

C: `j-sift.c:631`

Deviation: an array for the array `rp`; a structure, for the thread-local statics of the one
thread. -/
structure TubeCellCache where
  /-- `rp`, at `P(j, k)`, the product `rb ^ j rc ^ k` of the half-sizes of the last cell. -/
  rp : Array Double
  /-- `last_rb`, the half-size in rows of the cell of the products. -/
  lastRb : Double
  /-- `last_rc`, the half-size in third coordinates of the cell of the products. -/
  lastRc : Double

/-- The statics of `tube_cell` when the program starts: `last_rb = last_rc = -1.0`, and the zeros
of static storage in `rp`.

C: `j-sift.c:631` -/
def TubeCellCache.initial : TubeCellCache where
  rp := .replicate numCoeffs .zero
  lastRb := -1.0
  lastRc := -1.0

/-- The state of the analysis of the tube: the polynomials `K0`, `K1` and `K2` in `(b, c)` of the
coefficients `k₀`, `k₁` and `k₂` of the Kummer equation for the `a` in hand and the absolute values
`KA` of the coefficients of `|k₀| + W |k₁| + W² |k₂|`, which `tube_a_init` sets
(`JPoints.tubeAInit`), whether the analysis may decide (`tube_ok`), the number `tube_ncells` of
the cells analysed, the statics of `tube_cell` (`JPoints.TubeCellCache`) and the bands of the tube
(`JPoints.TubeBands`).

C: `j-sift.c:432`, `j-sift.c:434-435`

Deviation: arrays of `JPoints.numCoeffs` doubles for the arrays of the coefficients; a Boolean for
the `int` `tube_ok`; a natural number for the `long` `tube_ncells`, which starts at `0` and counts
up; a structure, for the thread-local globals of the one thread, and for `tube_ncells`, which the
threads share. -/
structure TubeState where
  /-- `K0`, at `P(j, k)`, the coefficient of `b ^ j c ^ k` of `k₀`, of degree 4. -/
  k0 : Array Double
  /-- `K1`, at `P(j, k)`, the coefficient of `b ^ j c ^ k` of `k₁`, of degree 3. -/
  k1 : Array Double
  /-- `K2`, at `P(j, k)`, the coefficient of `b ^ j c ^ k` of `k₂ = b² - 4 a c`. -/
  k2 : Array Double
  /-- `KA`, at `P(j, k)`, `|K0[P(j, k)]| + th |K1[P(j, k)]| + th2 |K2[P(j, k)]|`. -/
  ka : Array Double
  /-- `tube_ok`, whether the analysis of a cell may decide anything. -/
  tubeOk : Bool
  /-- `tube_ncells`, the number of the cells that `tube_cell` analysed. -/
  tubeNcells : Nat
  /-- The statics of `tube_cell`. -/
  cache : TubeCellCache
  /-- The bands of the tube. -/
  bands : TubeBands

/-- The state of the analysis of the tube when the program starts: the zeros of static storage
(`tube_ok` false, no cell analysed), the statics of `tube_cell` (`JPoints.TubeCellCache.initial`)
and the bands (`JPoints.TubeBands.initial`).

C: `j-sift.c:432`, `j-sift.c:434-435` -/
def TubeState.initial : TubeState where
  k0 := .replicate numCoeffs .zero
  k1 := .replicate numCoeffs .zero
  k2 := .replicate numCoeffs .zero
  ka := .replicate numCoeffs .zero
  tubeOk := false
  tubeNcells := 0
  cache := .initial
  bands := .initial

/-! ### The polynomials of a first coordinate -/

/-- `tube_eval`, the value at `(x, y)` of the polynomial of degree `deg` with the coefficients `qa`,
the sum over `j ≤ deg` and `k ≤ deg - j` of `qa[P(j, k)] * x ^ j * y ^ k` in this order, the powers
by repeated products.

C: `j-sift.c:587-597`

Deviation: the array passed, for the pointer to it; a natural number for the `long` `deg`. -/
def tubeEval (qa : Array Double) (deg : Nat) (x y : Double) : Id Double := do
  let mut sum : Double := 0.0
  let mut xj : Double := 1.0
  for j in [0:deg + 1] do
    let mut yk : Double := 1.0
    for k in [0:deg - j + 1] do
      sum := sum + qa[coeffIndex j k]! * xj * yk
      yk := yk * y
    xj := xj * x
  return sum

/-- The coefficients of `K0` as `tube_a_init` sets them in the array `k0`, whose entries it has set
to `0.0`, for `A = (double)a` and its powers `A2 = A * A`, `A3 = A2 * A`, `A4 = A3 * A`: the
coefficient `kᵢⱼₖ` of `K₀` (`kd.kdijk`) times `A ^ i` at `P(j, k)`.

C: `j-sift.c:443-449`

Deviation: the array returned, for the global `K0` that the C code writes; the coefficients `kd`
passed, for the globals that it reads, and `A`, `A2`, `A3` and `A4`, for the locals of
`tube_a_init`. -/
def tubeAInitK0 (kd : TubeCoeffs) (k0 : Array Double) (A A2 A3 A4 : Double) : Array Double :=
  let k0 := k0.set! (coeffIndex 0 0) (kd.kd400 * A4)
  let k0 := (k0.set! (coeffIndex 1 0) (kd.kd310 * A3)).set! (coeffIndex 0 1) (kd.kd301 * A3)
  let k0 := k0.set! (coeffIndex 2 0) (kd.kd220 * A2)
  let k0 := (k0.set! (coeffIndex 1 1) (kd.kd211 * A2)).set! (coeffIndex 0 2) (kd.kd202 * A2)
  let k0 := (k0.set! (coeffIndex 3 0) (kd.kd130 * A)).set! (coeffIndex 2 1) (kd.kd121 * A)
  let k0 := k0.set! (coeffIndex 1 2) (kd.kd112 * A)
  let k0 := k0.set! (coeffIndex 0 3) (kd.kd103 * A)
  let k0 := (k0.set! (coeffIndex 4 0) kd.kd040).set! (coeffIndex 3 1) kd.kd031
  let k0 := (k0.set! (coeffIndex 2 2) kd.kd022).set! (coeffIndex 1 3) kd.kd013
  k0.set! (coeffIndex 0 4) kd.kd004

/-- The coefficients of `K1` and `K2` as `tube_a_init` sets them in the arrays `k1` and `k2`, whose
entries it has set to `0.0`, for `A = (double)a`, `A2 = A * A` and `A3 = A2 * A`: those of
`k₁ = -2 (2 f₀ a³ + f₁ a² b + 2 f₂ a² c + f₃ a b c + 2 f₄ a c² + f₅ b c² + 2 f₆ c³)` from the
coefficients `fd` of the curve, and those of `k₂ = b² - 4 a c`, in the order of the products of the
C code (`-4.0*A3*fd[0]` as `(-4.0 * A3) * fd[0]`).

C: `j-sift.c:450-453`

Deviation: the arrays returned, for the globals `K1` and `K2` that the C code writes; the
coefficients `kd` passed, for the globals that it reads, and `A`, `A2` and `A3`, for the locals of
`tube_a_init`; the literals `-4.0` and `-2.0` as the negations of `4.0` and `2.0`, which they
are. -/
def tubeAInitK1K2 (kd : TubeCoeffs) (k1 k2 : Array Double) (A A2 A3 : Double) :
    Array Double × Array Double :=
  let k1 := k1.set! (coeffIndex 0 0) ((-4.0 : Double) * A3 * kd.fd[0]!)
  let k1 := k1.set! (coeffIndex 1 0) ((-2.0 : Double) * A2 * kd.fd[1]!)
  let k1 := k1.set! (coeffIndex 0 1) ((-4.0 : Double) * A2 * kd.fd[2]!)
  let k1 := k1.set! (coeffIndex 1 1) ((-2.0 : Double) * A * kd.fd[3]!)
  let k1 := k1.set! (coeffIndex 0 2) ((-4.0 : Double) * A * kd.fd[4]!)
  let k1 := k1.set! (coeffIndex 1 2) ((-2.0 : Double) * kd.fd[5]!)
  let k1 := k1.set! (coeffIndex 0 3) ((-4.0 : Double) * kd.fd[6]!)
  (k1, (k2.set! (coeffIndex 2 0) 1.0).set! (coeffIndex 0 1) ((-4.0 : Double) * A))

/-- `tube_a_init`, the state `t` of the analysis with the polynomials of the first coordinate `a`:
`K0`, `K1` and `K2` set to `0.0` and then to the coefficients of `k₀`, `k₁` and `k₂`
(`JPoints.tubeAInitK0`, `JPoints.tubeAInitK1K2`) for `A = (double)a`, `KA` to
`|K0| + th |K1| + th2 |K2|` coefficient by coefficient, and `tube_ok` to whether the value of `KA`
at `(height, height + 64)`, beyond every cell (`JPoints.tubeEval`), is below `TUBE_BIG`, false
also for an infinity or a NaN.

C: `j-sift.c:438-442`, `j-sift.c:454-461`, `j-sift.c:463-464`

Deviation: the state taken and returned, for the globals that it writes; the globals that it reads
passed (the coefficients `kd`, the height bound, `th` and `th2`), and without the store of `a` in
`tube_a`, which nothing reads; `JPoints.Double.ofInt` for the conversions of the `long`s `a` and
`height` and of the `unsigned long` `height + LONG_LENGTH`, rounded to nearest, exact for the values
of the program; `JPoints.Double.lt` for the comparison `<`, false when either side is a NaN. -/
def tubeAInit (kd : TubeCoeffs) (height : Int) (th th2 : Double) (t : TubeState) (a : Int) :
    Id TubeState := do
  let A := Double.ofInt a
  let A2 := A * A
  let A3 := A2 * A
  let A4 := A3 * A
  let mut k0 := t.k0
  let mut k1 := t.k1
  let mut k2 := t.k2
  for i in [0:numCoeffs] do
    k0 := k0.set! i 0.0
    k1 := k1.set! i 0.0
    k2 := k2.set! i 0.0
  k0 := tubeAInitK0 kd k0 A A2 A3 A4
  (k1, k2) := tubeAInitK1K2 kd k1 k2 A A2 A3
  let mut ka := t.ka
  for i in [0:numCoeffs] do
    ka := ka.set! i (k0[i]!.fabs + th * k1[i]!.fabs + th2 * k2[i]!.fabs)
  let v ← tubeEval ka 4 (Double.ofInt height) (Double.ofInt (height + longLength))
  return { t with k0, k1, k2, ka, tubeOk := v.lt tubeBig }

/-! ### The bounds over a cell -/

/-- `shift1`, the Taylor shift to the point `x`, in place, of the polynomial of degree `deg` whose
coefficients are the entries `p[base], p[base + s], …, p[base + deg s]` of the array `p`: for each
`i < deg`, for `j` from `deg - 1` down to `i`, the coefficient `j` increased by `x` times the
coefficient `j + 1`.

C: `j-sift.c:557-563`

Deviation: the array and the index `base` in it, for the pointer `p` into the array of the caller
(`Q + k` or `Q + L j`), and the array returned, for the array that the C code writes; natural
numbers for the `long`s; the loop of `j` down from `deg - 1` to `i` as a loop up over `t < deg - i`
with `j = deg - 1 - t`. -/
def shift1 (p : Array Double) (base deg s : Nat) (x : Double) : Id (Array Double) := do
  let mut p := p
  for i in [0:deg] do
    for t in [0:deg - i] do
      let j := deg - 1 - t
      p := p.set! (base + j * s) (p[base + j * s]! + x * p[base + (j + 1) * s]!)
  return p

/-- `shift2`, the shift of the polynomial of degree `deg` with the coefficients `Q[P(j, k)]`
(`j + k ≤ deg`) to the point `(bm, cm)`: each column `k` shifted in `b` to `bm`, then each row `j`
shifted in `c` to `cm` (`JPoints.shift1`).

C: `j-sift.c:566-572`

Deviation: the array returned, for the array that the C code shifts in place; a natural number for
the `long` `deg`. -/
def shift2 (q : Array Double) (deg : Nat) (bm cm : Double) : Id (Array Double) := do
  let mut q := q
  for k in [0:deg + 1] do q ← shift1 q k (deg - k) coeffRow bm
  for j in [0:deg + 1] do q ← shift1 q (coeffRow * j) (deg - j) 1 cm
  return q

/-- `tube_sum`, the sum over `(j, k) ≠ (0, 0)` with `j + k ≤ deg` of `|Q[P(j, k)]| rp[P(j, k)]`,
in the order of `j` and then of `k`: the bound on the terms of the shifted polynomial that are not
constant over the cell, `rp` holding the products of the half-sizes of the cell.

C: `j-sift.c:576-584`

Deviation: the arrays passed, for the pointers to them; a natural number for the `long` `deg`. -/
def tubeSum (q : Array Double) (deg : Nat) (rp : Array Double) : Id Double := do
  let mut sum : Double := 0.0
  for j in [0:deg + 1] do
    for k in [(if j == 0 then 1 else 0):deg - j + 1] do
      sum := sum + q[coeffIndex j k]!.fabs * rp[coeffIndex j k]!
  return sum

/-- `poly_sign`, the sign of the shifted polynomial `Q` throughout the cell, with the bounds `lo`
and `hi` on its absolute value: for `s = tube_sum(Q) + err`, `lo = |Q[0]| - s` and
`hi = |Q[0]| + s`, and the sign `1` or `-1` of `Q[0]` when `lo > 0.0`, else `0`.

C: `j-sift.c:602-609`

Deviation: the bounds returned with the sign, for the pointers `lo` and `hi` through which the C
code returns them; an integer for the `int` sign; a natural number for the `long` `deg`;
`JPoints.Double.lt` for the comparisons `>`, false when either side is a NaN. -/
def polySign (q : Array Double) (deg : Nat) (rp : Array Double) (err : Double) :
    Id (Int × Double × Double) := do
  let s := (← tubeSum q deg rp) + err
  let lo := q[0]!.fabs - s
  let hi := q[0]!.fabs + s
  if 0.0 < lo then return (if (0.0 : Double) < q[0]! then 1 else -1, lo, hi)
  return (0, lo, hi)

/-! ### The words collected -/

/-- `tube_emit`, the words `[i_lo, i_hi)` collected for the row `b` of the band `bd`, the
`row = b - band_b0`-th: merged into its last range when that reaches `i_lo`, the end raised to
`i_hi` if it is below; otherwise, when the row has `TUBE_RANGES` ranges, the first range extended
to `i_hi` and the others dropped (the hull of the ranges, since the analysis collects the words of
a row in increasing order); and otherwise a new range.

C: `j-sift.c:614-626`

Deviation: the bands passed and returned, for the thread-local globals that the C code reads and
writes; integers for the `long`s `b`, `i_lo` and `i_hi` and for the ends of the ranges, a natural
number for the index `row` of the row in the band, which the C code keeps nonnegative; the test
`nr > 0 && …` as a conjunction, the second part read only when the first holds. -/
def tubeEmit (bd : TubeBands) (b iLo iHi : Int) : TubeBands :=
  let row := (b - bd.bandB0).toNat
  let nr := bd.bandNr[row]!
  if nr > 0 ∧ bd.bhi row (nr - 1) ≥ iLo then
    if bd.bhi row (nr - 1) < iHi then bd.setBhi row (nr - 1) iHi else bd
  else if nr = tubeRanges then { bd.setBhi row 0 iHi with bandNr := bd.bandNr.set! row 1 }
  else { (bd.setBlo row nr iLo).setBhi row nr iHi with bandNr := bd.bandNr.set! row (nr + 1) }

/-- The words `[i_lo, i_hi)` collected for each of the rows `b_lo ≤ b ≤ b_hi` of the band of the
state `t`, in order (`JPoints.tubeEmit`), as `tube_cell` collects a cell whole, when the analysis
decides nothing or when it shows that the cell holds a root throughout, and the word of a leaf.

C: `j-sift.c:644`, `j-sift.c:683`, `j-sift.c:702`

Deviation: one function for the three loops, which differ only in the words; the loop
`for(b = b_lo; b <= b_hi; b++)` over `b = b_lo + k` for `k < b_hi - b_lo + 1`, none when
`b_hi < b_lo`; integers for the `long`s `b_lo`, `b_hi`, `i_lo` and `i_hi`; the bands taken out of
the state while they are written, so that they are not shared, and the state returned. -/
def tubeEmitRows (t : TubeState) (bLo bHi iLo iHi : Int) : Id TubeState := do
  let mut bands := t.bands
  let t := { t with bands := default }
  for k in [0:(bHi - bLo + 1).toNat] do
    bands := tubeEmit bands (bLo + k) iLo iHi
  return { t with bands }

/-! ### The analysis of a cell -/

/-- The statics `c` of `tube_cell` for a cell with the half-sizes `rb` and `rc`: when either differs
from the last (`!=` of doubles, true also for a NaN), the products `rp[P(j, k)] = rb ^ j rc ^ k`
for `j, k < L`, by repeated products (`rbj` the power of `rb`, `rck` that times the power of `rc`),
and `last_rb = rb`, `last_rc = rc`; otherwise the statics as they are.

C: `j-sift.c:648-655`

Deviation: the statics taken and returned, for the thread-local statics that the C code writes;
`!rb.beq last_rb` for the comparison `rb != last_rb`. -/
def tubeCellProducts (c : TubeCellCache) (rb rc : Double) : Id TubeCellCache := do
  if !rb.beq c.lastRb || !rc.beq c.lastRc then
    let mut rp := c.rp
    let mut rbj : Double := 1.0
    for j in [0:coeffRow] do
      let mut rck := rbj
      for k in [0:coeffRow] do
        rp := rp.set! (coeffIndex j k) rck
        rck := rck * rc
      rbj := rbj * rb
    return { rp, lastRb := rb, lastRc := rc }
  return c

/-- The coefficients `q` of `Q(W) = k₀ + W k₁ + W² k₂` and `m` of `Q(-W) = k₀ - W k₁ + W² k₂` from
the shifted coefficients `p0`, `p1` and `p2` of `k₀`, `k₁` and `k₂`, for `W = th` and
`W² = th2`: `q[j] = p0[j] + th * p1[j] + th2 * p2[j]` and `m[j] = p0[j] - th * p1[j] + th2 * p2[j]`
for `j < NC`, in the order of the C code.

C: `j-sift.c:664-667`

Deviation: the bound `th` and its square `th2` passed, for the statics, and the shifted
coefficients, for the local arrays `p0`, `p1` and `p2`; fresh arrays filled by the loop, returned,
for the local arrays of `tube_cell`. -/
def tubeCellCombine (th th2 : Double) (p0 p1 p2 : Array Double) :
    Id (Array Double × Array Double) := do
  let mut q := #[]
  let mut m := #[]
  for j in [0:numCoeffs] do
    q := q.push (p0[j]! + th * p1[j]! + th2 * p2[j]!)
    m := m.push (p0[j]! - th * p1[j]! + th2 * p2[j]!)
  return (q, m)

/-- The analysis of the cell with the centre `(bm, cm)` and the half-sizes `rb` and `rc` by
`tube_cell`, from the polynomials of the state `t` and the products `rp = rb ^ j rc ^ k`: the
polynomials shifted to the centre (`JPoints.shift2`), the margin `err = TUBE_EPS ma` for the value
`ma` of `KA` at the far corner `(|bm| + rb, |cm| + rc)`, and the signs (`JPoints.polySign`) of
`k₂`, of `Q(W)` and of `Q(-W)` throughout the cell (`JPoints.tubeCellCombine`). The pair returned:
whether `Q(W)` and `Q(-W)` have different signs throughout (`inside`, a root in `[-W, W]`
everywhere), and whether the cell is out, `Q(W)` and `Q(-W)` of the same sign throughout and either
`k₂` of the other sign throughout or `|k₁| > 2 W |k₂|` throughout, where `tube_cell` returns.

C: `j-sift.c:633`, `j-sift.c:637-640`, `j-sift.c:656-663`, `j-sift.c:668-679`

Deviation: the bound `th` and its square `th2` passed, for the statics, and the polynomials of the
state and the products `rp`, for the globals and the static that it reads; the shifted copies of
`K0`, `K1` and `K2` returned by `JPoints.shift2`, for the copies into the local arrays `p0`, `p1`
and `p2` that it shifts in place; `inside` and the returns of the C code returned as a pair of
Booleans; integers for the `int` signs; the outputs of `JPoints.polySign` that the C code discards
dropped; `JPoints.Double.lt` for the comparison `>`, false when either side is a NaN, which keeps
the cell. -/
def tubeCellAnalyze (th th2 : Double) (t : TubeState) (rp : Array Double) (bm rb cm rc : Double) :
    Id (Bool × Bool) := do
  let p0 ← shift2 t.k0 4 bm cm
  let p1 ← shift2 t.k1 3 bm cm
  let p2 ← shift2 t.k2 2 bm cm
  let ma ← tubeEval t.ka 4 (bm.fabs + rb) (cm.fabs + rc)
  let err := tubeEps * ma
  let (s2, _, hi2) ← polySign p2 2 rp (err / th2)
  let (q, m) ← tubeCellCombine th th2 p0 p1 p2
  let (sp, _, _) ← polySign q 4 rp err
  let (sm, _, _) ← polySign m 4 rp err
  let inside := sp != 0 && sm != 0 && sp != sm
  if sp != 0 && sm != 0 && sp == sm then
    if s2 != 0 && s2 != sp then return (inside, true)
    let (_, lo1, _) ← polySign p1 3 rp (err / th)
    if 2.0 * th * hi2 < lo1 then return (inside, true)
  return (inside, false)

/-- The decision of `tube_cell` on the cell of the rows `b_lo ≤ b ≤ b_hi` and the words
`i_lo ≤ i < i_hi`, in the state `t` whose analysis may decide: its centre
`bm = 0.5 * (double)(b_lo + b_hi)`, `cm = 32.0 * (double)(i_lo + i_hi) - 0.5` and its half-sizes
`rb = 0.5 * (double)(b_hi - b_lo)`, `rc = 32.0 * (double)(i_hi - i_lo) - 0.5`, which bound the
coordinates `b` and `c = 64 i + j` of the cell, the products of the half-sizes in the statics
(`JPoints.tubeCellProducts`), and the analysis (`JPoints.tubeCellAnalyze`): whether the cell holds
a root throughout, whether it is out, and the state with the statics.

C: `j-sift.c:634-636`

Deviation: the bound `th` and its square `th2` passed, for the statics; the statics taken and
returned in the state, for the thread-local statics that the C code writes; the centre and the
half-sizes computed after the test of `tube_ok`, which reads none of them; `JPoints.Double.ofInt`
for the exact conversions of the `long`s to doubles. -/
def tubeCellDecide (th th2 : Double) (t : TubeState) (bLo bHi iLo iHi : Int) :
    Id (Bool × Bool × TubeState) := do
  let bm := 0.5 * Double.ofInt (bLo + bHi)
  let rb := 0.5 * Double.ofInt (bHi - bLo)
  let cm := 32.0 * Double.ofInt (iLo + iHi) - 0.5
  let rc := 32.0 * Double.ofInt (iHi - iLo) - 0.5
  let t := { t with cache := ← tubeCellProducts t.cache rb rc }
  let (inside, out) ← tubeCellAnalyze th th2 t t.cache.rp bm rb cm rc
  return (inside, out, t)

/-- `tube_cell`, the analysis of the cell of the rows `b_lo ≤ b ≤ b_hi` and the words
`i_lo ≤ i < i_hi` of the plane of `(b, c)`, with the bound `th` on the fourth coordinate and its
square `th2`, in the state `t`: the cell counted in `tube_ncells`; when the analysis may not decide
(`tube_ok`), the cell collected whole (`JPoints.tubeEmitRows`); otherwise, by the bounds over the
cell (`JPoints.tubeCellDecide`), a cell that is out is dropped, a cell with a root throughout
collected whole, and any other halved, in words while it has more than one and at most
`TUBE_ROWS` rows to a word (the lower half first), else in rows while it has more than
`TUBE_ROWS` (the lower half first), and a leaf, at most `TUBE_ROWS` rows by one word, collects its
word for each of its rows.

C: `j-sift.c:629-630`, `j-sift.c:632`, `j-sift.c:641-643`, `j-sift.c:645-647`,
`j-sift.c:680-682`, `j-sift.c:684-701`, `j-sift.c:703-705`

Deviation: the state taken and returned, for the globals and the statics that it writes; the bound
and its square passed, for the statics that it reads; integers for the `long`s, and Lean's `/` for
C's `/` on the positive `words` and `rows - 1`, where it truncates the same way; the recursion
well founded on the number of the rows and the words of the cell, which each recursive call lowers
(`JPoints.tubeRows_pos`). -/
def tubeCell (th th2 : Double) (t : TubeState) (bLo bHi iLo iHi : Int) : Id TubeState := do
  let rows := bHi - bLo + 1
  let words := iHi - iLo
  let t := { t with tubeNcells := t.tubeNcells + 1 }
  if !t.tubeOk then return (← tubeEmitRows t bLo bHi iLo iHi)
  let (inside, out, t) ← tubeCellDecide th th2 t bLo bHi iLo iHi
  if out then return t
  if inside then return (← tubeEmitRows t bLo bHi iLo iHi)
  if h : words > 1 ∧ rows ≤ tubeRows * words then
    let mid := iLo + words / 2
    let t ← tubeCell th th2 t bLo bHi iLo mid
    tubeCell th th2 t bLo bHi mid iHi
  else if h' : rows > tubeRows then
    let mid := bLo + (rows - 1) / 2
    let t ← tubeCell th th2 t bLo mid iLo iHi
    tubeCell th th2 t (mid + 1) bHi iLo iHi
  else tubeEmitRows t bLo bHi iLo (iLo + 1)
termination_by (bHi - bLo + 1).toNat + (iHi - iLo).toNat
decreasing_by all_goals lia [tubeRows_pos]

/-! ### The ranges of a row cut to the real region -/

/-- `row_cut`, the ranges of the `row`-th row of the band `bd` intersected with the `nreg` ranges
`[reglo[j], reghi[j])` of the real region of the row (`row_region`): with an index `i` into the
ranges of the row and `j` into those of the region, while both last, the intersection
`[max(lo), min(hi))` of the two ranges kept when it is not empty, and the range that ends first
left behind (the range of the region when both end together). The number of the ranges, and their
lower and their upper ends, in order.

C: `j-sift.c:710-720`

Deviation: the ranges returned as arrays of their number, filled in the order in which the C code
writes them, for the arrays `rlo` and `rhi` of the caller; the bands and the arrays of the region
passed, for the globals and the pointers; integers for the `long`s of the ends of the ranges,
natural numbers for the counts and the indices, which the C code keeps nonnegative. -/
def rowCut (bd : TubeBands) (row nreg : Nat) (reglo reghi : Array Int) :
    Id (Nat × Array Int × Array Int) := do
  let nr := bd.bandNr[row]!
  let mut i := 0
  let mut j := 0
  let mut n := 0
  let mut rlo := #[]
  let mut rhi := #[]
  while i < nr && j < nreg do
    let lo := if bd.blo row i > reglo[j]! then bd.blo row i else reglo[j]!
    let hi := if bd.bhi row i < reghi[j]! then bd.bhi row i else reghi[j]!
    if lo < hi then
      rlo := rlo.push lo
      rhi := rhi.push hi
      n := n + 1
    if bd.bhi row i < reghi[j]! then i := i + 1 else j := j + 1
  return (n, rlo, rhi)

/-! ### Examples

The values are those of an instrumented copy of `j-points` at the pin, which calls `tube_a_init`,
`tube_cell`, `tube_emit` and `row_cut` directly, prints the doubles by their bits and traces the
cells that `tube_cell` visits, with the coefficients of the analysis as `tube_init` computes them
from the curve searched. -/

-- The coefficients of the analysis for the curve with the coefficients `c` of degree `deg`: those
-- of the curve searched (`JPoints.normalizeCurve`) and of its quartic `K₀` (`JPoints.kummerInit`),
-- as `tube_init` computes them (`JPoints.tubeInitCoeffs`).
private def coeffsOf (c : Array Int) (deg : Nat) : TubeCoeffs :=
  let sc := (normalizeCurve c deg true).run.1
  (tubeInitCoeffs sc (kummerInit sc.coeffs)).run

-- The state after `tube_a_init(a)` at the height bound `H` with the bound `W` on the fourth
-- coordinate, `th = (double)W`.
private def aInit (c : Array Int) (deg : Nat) (H W a : Int) : TubeState :=
  let th := Double.ofInt W
  (tubeAInit (coeffsOf c deg) H th (th * th) .initial a).run

-- The nonzero entries of an array of doubles, with their bits.
private def nonzero (x : Array Double) : List (Nat × UInt64) :=
  (List.range x.size).filterMap fun i ↦ if x[i]!.bits == 0 then none else some (i, x[i]!.bits)

-- A hash of the bits of the four polynomials of the state.
private def polysHash (t : TubeState) : UInt64 :=
  (t.k0 ++ t.k1 ++ t.k2 ++ t.ka).foldl (init := 0xcbf29ce484222325) fun h x ↦
    let h := (h ^^^ x.bits) * 0x100000001b3
    h ^^^ (h >>> 32)

-- The ranges of the `row`-th row of the band, as a text.
private def rowText (bd : TubeBands) (row : Nat) : String :=
  " ".intercalate <| (List.range bd.bandNr[row]!).flatMap fun k ↦
    [toString (bd.blo row k), toString (bd.bhi row k)]

-- The cell of the rows `bLo..bHi` of `a` and the words `iLo..iHi` (by default the whole row), as
-- `tube_sample` and `sift_bands` analyse it after `tube_a_init(a)`, with the band starting at
-- `bLo`: the number of the cells visited, then the runs of rows with the same ranges, without the
-- rows without ranges.
private def band (c : Array Int) (deg : Nat) (H W a bLo bHi : Int)
    (iLo : Int := (-H) >>> longShift) (iHi : Int := (H >>> longShift) + 1) : String := Id.run do
  let th := Double.ofInt W
  let t := aInit c deg H W a
  let t := { t with bands := { t.bands with bandB0 := bLo } }
  let t := (tubeCell th (th * th) t bLo bHi iLo iHi).run
  let n := (bHi - bLo + 1).toNat
  let mut parts : Array String := #[]
  let mut start := 0
  for k in [0:n] do
    if k + 1 == n || rowText t.bands (k + 1) != rowText t.bands k then
      if rowText t.bands k != "" then
        parts := parts.push s!"{bLo + start}..{bLo + k}: {rowText t.bands k}"
      start := k + 1
  return s!"{t.tubeNcells}; " ++ "; ".intercalate parts.toList

-- The polynomials of `a = 3` for the sextic `1 + 4 x + 3 x² - 8 x³ + 2 x⁴ + 8 x⁵ + 7 x⁶` at
-- `H = 1000`, by their nonzero entries.
#guard
  let t := aInit #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3
  t.tubeOk && nonzero t.k0 == [(0, 0x4074400000000000), (1, 0x409b000000000000),
    (2, 0x4085600000000000), (3, 0x4078000000000000), (4, 0x4020000000000000),
    (5, 0x408b000000000000), (7, 0x4048000000000000), (8, 0x406c000000000000),
    (10, 0xc052000000000000), (11, 0xc06b000000000000), (12, 0xc055000000000000),
    (15, 0xc058000000000000), (16, 0xc05c000000000000), (20, 0xc03c000000000000)] &&
  nonzero t.k1 == [(0, 0xc05b000000000000), (1, 0xc05b000000000000), (2, 0xc038000000000000),
    (3, 0xc03c000000000000), (5, 0xc052000000000000), (6, 0x4048000000000000),
    (7, 0xc030000000000000)] &&
  nonzero t.k2 == [(1, 0xc028000000000000), (10, 0x3ff0000000000000)] &&
  nonzero t.ka == [(0, 0x40fa724000000000), (1, 0x416718f400000000), (2, 0x40d81b0000000000),
    (3, 0x40dbb80000000000), (4, 0x4020000000000000), (5, 0x40f1ca0000000000),
    (6, 0x40e7700000000000), (7, 0x40cf580000000000), (8, 0x406c000000000000),
    (10, 0x412e851000000000), (11, 0x406b000000000000), (12, 0x4055000000000000),
    (15, 0x4058000000000000), (16, 0x405c000000000000), (20, 0x403c000000000000)]

-- The polynomials by a hash of their bits, and `tube_ok`: for the sextic at `a = 3`, `a = 0`
-- (with the zeros `-0.0` of the products by `A = 0.0`) and `a = H`; for the quintic
-- `1 + 178 x + 817 x² - 274 x³ + 16 x⁴ + x⁵` at `H = 2000`; for the sextic at `H = 10 ^ 6` with
-- `-w 2 ^ 53 + 1` (`th = 2 ^ 53`); `tube_ok` false for coefficients of `10 ^ 150`, where `KA` at
-- `(h, h + 64)` is beyond `TUBE_BIG`, and for a coefficient `10 ^ 400`, whose `k400` is beyond the
-- largest double, so that `kd400` is infinite (and a NaN times `A = 0.0`).
#guard [(#[1, 4, 3, -8, 2, 8, 7], 6, 1000, 1000, 3, true, 0x1aa6fc894cfe5946),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 1000, 1000, 0, true, 0xd1d0dc9c43cf8de3),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 1000, 1000, 1000, true, 0x2259238d40b2ebc0),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 2000, 2000, 1, true, 0x2d98d5b6477231f6),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 2000, 2000, 1999, true, 0xf7a919ea09e3f9fd),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 1000000, 9007199254740993, 999999, true, 0xad73892372896496),
    (#[10 ^ 150, 3, -10 ^ 149, 7, 1, 10 ^ 150, 1], 6, 1000000, 1000000, 999999, false,
      0xa244256c66952161),
    (#[10 ^ 150, 3, -10 ^ 149, 7, 1, 10 ^ 150, 1], 6, 1000000, 1000000, 0, false,
      0x15e41c511db71dcd),
    (#[10 ^ 400, 1, 2, 3, 4, 5, 6], 6, 100, 100, 0, false, 0xae4bd57c455be3f7),
    (#[10 ^ 400, 1, 2, 3, 4, 5, 6], 6, 100, 100, 5, false, 0x1a93e88cf5823dd6)].all
  fun (c, deg, H, W, a, ok, h) ↦ let t := aInit c deg H W a; t.tubeOk == ok && polysHash t == h

-- `shift2` of `K2` of `a = 3` to `(10.5, -3.5)`, by the bits that a test program calling `shift2`
-- of the pin prints: `k₂ = b² - 12 c` shifted there is `152.25 + 21 s + s² - 12 t`, exactly.
#guard
  let t := aInit #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3
  nonzero (shift2 t.k2 2 10.5 (-3.5)).run ==
    [(0, 0x4063080000000000), (1, 0xc028000000000000), (5, 0x4035000000000000),
      (10, 0x3ff0000000000000)]

-- The cells of a band of 130 rows of the sextic at `H = 1000`, `a = 3`, with the verdict of the
-- analysis on each (whether it holds a root throughout, whether it is out), in the order in which
-- `tube_cell` visits them: cells out by the sign of `k₂` and by `|k₁| > 2 W |k₂|`, cells with a
-- root throughout, halved in words and in rows, and leaves.
#guard
  let t := aInit #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3
  let th := Double.ofInt 1000
  [(-700, -571, -16, 16, (false, false)), (-700, -571, -16, 0, (false, false)),
  (-700, -571, -16, -8, (false, false)), (-700, -571, -16, -12, (false, false)),
  (-700, -571, -16, -14, (false, true)), (-700, -571, -14, -12, (false, false)),
  (-700, -636, -14, -12, (false, false)), (-700, -636, -14, -13, (false, true)),
  (-700, -636, -13, -12, (false, false)), (-700, -668, -13, -12, (false, false)),
  (-667, -636, -13, -12, (false, false)), (-635, -571, -14, -12, (false, true)),
  (-700, -571, -12, -8, (false, false)), (-700, -571, -12, -10, (false, false)),
  (-700, -636, -12, -10, (false, false)), (-700, -636, -12, -11, (false, false)),
  (-700, -668, -12, -11, (true, false)), (-667, -636, -12, -11, (false, false)),
  (-700, -636, -11, -10, (true, false)), (-635, -571, -12, -10, (false, false)),
  (-635, -571, -12, -11, (false, false)), (-635, -603, -12, -11, (false, false)),
  (-602, -571, -12, -11, (false, false)), (-635, -571, -11, -10, (false, false)),
  (-635, -603, -11, -10, (true, false)), (-602, -571, -11, -10, (false, false)),
  (-700, -571, -10, -8, (false, false)), (-700, -636, -10, -8, (false, false)),
  (-700, -636, -10, -9, (false, false)), (-700, -668, -10, -9, (false, false)),
  (-667, -636, -10, -9, (true, false)), (-700, -636, -9, -8, (false, false)),
  (-700, -668, -9, -8, (false, false)), (-667, -636, -9, -8, (false, false)),
  (-635, -571, -10, -8, (false, false)), (-635, -571, -10, -9, (true, false)),
  (-635, -571, -9, -8, (false, false)), (-635, -603, -9, -8, (false, false)),
  (-602, -571, -9, -8, (true, false)), (-700, -571, -8, 0, (false, false)),
  (-700, -571, -8, -4, (false, false)), (-700, -571, -8, -6, (false, false)),
  (-700, -636, -8, -6, (false, true)), (-635, -571, -8, -6, (false, false)),
  (-635, -571, -8, -7, (false, false)), (-635, -603, -8, -7, (false, false)),
  (-602, -571, -8, -7, (false, false)), (-635, -571, -7, -6, (false, true)),
  (-700, -571, -6, -4, (false, true)), (-700, -571, -4, 0, (false, false)),
  (-700, -571, -4, -2, (false, true)), (-700, -571, -2, 0, (false, true)),
  (-700, -571, 0, 16, (false, false)), (-700, -571, 0, 8, (false, false)),
  (-700, -571, 0, 4, (false, false)), (-700, -571, 0, 2, (false, false)),
  (-700, -636, 0, 2, (false, false)), (-700, -636, 0, 1, (false, true)),
  (-700, -636, 1, 2, (false, true)), (-635, -571, 0, 2, (false, false)),
  (-635, -571, 0, 1, (false, true)), (-635, -571, 1, 2, (false, true)),
  (-700, -571, 2, 4, (false, false)), (-700, -636, 2, 4, (false, false)),
  (-700, -636, 2, 3, (false, true)), (-700, -636, 3, 4, (false, true)),
  (-635, -571, 2, 4, (false, false)), (-635, -571, 2, 3, (false, false)),
  (-635, -603, 2, 3, (false, true)), (-602, -571, 2, 3, (false, true)),
  (-635, -571, 3, 4, (false, true)), (-700, -571, 4, 8, (false, false)),
  (-700, -571, 4, 6, (false, false)), (-700, -636, 4, 6, (false, false)),
  (-700, -636, 4, 5, (false, true)), (-700, -636, 5, 6, (false, true)),
  (-635, -571, 4, 6, (false, false)), (-635, -571, 4, 5, (false, true)),
  (-635, -571, 5, 6, (false, true)), (-700, -571, 6, 8, (false, true)),
  (-700, -571, 8, 16, (false, false)), (-700, -571, 8, 12, (false, true)),
  (-700, -571, 12, 16, (false, true))].all fun (bLo, bHi, iLo, iHi, v) ↦
    let (inside, out, _) := (tubeCellDecide th (th * th) t bLo bHi iLo iHi).run
    (inside, out) == v

-- The bands of the sextic at `H = 1000`: the number of the cells of `tube_cell` and the ranges of
-- the rows, for the band above, a band of 64 rows of `a = 500`, the same with `-w 10`, a band of
-- `a = 0`, and cells of one word and 200 rows and of two words, which `tube_cell` halves in rows.
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3 (-700) (-571) ==
  "83; -700..-636: -13 -8; -635..-571: -12 -7"
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 500 600 663 == "37; 600..663: -6 -1 6 10"
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 10 500 600 663 == "39; 600..663: -13 -10 7 9"
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 0 1 64 == "43; 1..64: -16 16"
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3 (-700) (-501) (-13) (-12) ==
  "5; -700..-651: -13 -12"
#guard band #[1, 4, 3, -8, 2, 8, 7] 6 1000 1000 3 (-700) (-501) (-10) (-8) ==
  "13; -700..-501: -10 -8"

-- The bands of the quintic at `H = 2000`, and the rows whole where the analysis may not decide.
#guard band #[1, 178, 817, -274, 16, 1, 0] 5 2000 2000 1999 100 163 ==
  "23; 100..163: -11 -9 -1 0"
#guard band #[1, 178, 817, -274, 16, 1, 0] 5 2000 2000 30 (-500) (-437) == "39; -500..-437: -6 4"
#guard band #[1, 178, 817, -274, 16, 1, 0] 5 2000 2000 1 (-2000) (-1937) ==
  "125; -2000..-1937: -30 32"
#guard band #[10 ^ 150, 3, -10 ^ 149, 7, 1, 10 ^ 150, 1] 6 1000000 1000000 999999 1 64 ==
  "1; 1..64: -15625 15626"
#guard band #[10 ^ 400, 1, 2, 3, 4, 5, 6] 6 100 100 5 1 10 == "1; 1..10: -2 2"

-- `tube_emit` on the band of the rows `0` to `3`: ranges that touch merged, one inside the last,
-- and the hull of a row at its thirteenth range.
#guard
  let emits : List (Int × Int × Int) := [(0, 0, 1), (0, 1, 2), (0, 3, 4), (0, 2, 5)] ++
    (List.range 13).map (fun (i : Nat) ↦ ((1 : Int), (2 * i : Int), (2 * i + 1 : Int))) ++
    [(1, 27, 28), (2, 10, 20), (2, 12, 15), (2, 20, 21), (3, -5, -3)]
  let bd := emits.foldl (fun bd (b, lo, hi) ↦ tubeEmit bd b lo hi) TubeBands.initial
  (List.range 4).map (rowText bd) == ["0 2 3 5", "0 25 27 28", "10 21", "-5 -3"]

-- `row_cut` of the ranges `rs` of the row `1` of the band against the ranges `reg` of the region.
#guard [([(-16, -10), (-5, 3), (7, 16)], [(-16, -12), (-11, 0), (2, 16)],
      [(-16, -12), (-11, -10), (-5, 0), (2, 3), (7, 16)]),
    ([], [(0, 5), (6, 8)], []), ([(0, 5), (6, 8)], [], []), ([(0, 5)], [(0, 5), (6, 8)], [(0, 5)]),
    ([(-3, -1), (4, 9)], [(-2, 0), (1, 6)], [(-2, -1), (4, 6)])].all
  fun ((rs : List (Int × Int)), (reg : List (Int × Int)), cut) ↦
    let bd0 := { TubeBands.initial with bandNr := TubeBands.initial.bandNr.set! 1 rs.length }
    let bd := (List.range rs.length).foldl (fun bd k ↦
      (bd.setBlo 1 k rs[k]!.1).setBhi 1 k rs[k]!.2) bd0
    let (n, rlo, rhi) :=
      (rowCut bd 1 reg.length (reg.map (·.1)).toArray (reg.map (·.2)).toArray).run
    n == cut.length && (List.range n).map (fun i ↦ (rlo[i]!, rhi[i]!)) == cut

end JPoints

end
