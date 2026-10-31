/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.DoubleArith
public import JPoints.Model.Qsort
public import JPoints.Model.Tables

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.DoubleArith
meta import JPoints.Model.Qsort
meta import JPoints.Model.Tables

/-!
# The rates of the primes

The first part of `init_fmodpsquare` of `j-points`, up to the choice of the sieving primes: for each
prime `p` considered, the coefficients of the curve searched modulo `p`
(`JPoints.initFmodpsquareCoeffs`), whether `f₆` is a square modulo `p` (the points at infinity)
and which values of `f` are squares modulo `p` (`JPoints.initFmodpsquareValues`, with the values by
Horner's rule, `JPoints.initFmodpsquareEval`), which give the number `np0` of the classes
`(0, b, c)` that it counts, and the number of the admitted classes `(1, b, c)`, all of them by
`JPoints.initTable` for `p² ≤ SAMPLE_PAIRS`, else a sample of every `stride`-th class
(`JPoints.initFmodpsquareSample`); from these the rate of `p` (`JPoints.rateOf`), the fraction of
the residue triples modulo `p` that the sieve admits, in the record `entry` of the prime
(`JPoints.Entry`) in the global `prec` (`JPoints.initFmodpsquarePrime`); then the exact count for a
sampled rate of `0` (`JPoints.initFmodpsquareRecount`), and `prec` sorted by rate by `qsort` with
`compare_entries` (`JPoints.compareEntries`), in `JPoints.initFmodpsquareRates`.

## Main definitions

* `JPoints.Entry`, `JPoints.compareEntries`, `JPoints.rateOf`: the record of a prime, the order
  by rate and the rate.
* `JPoints.Rates`: the global `prec` with the arrays `sampled` and `tabled` of `init_fmodpsquare`.
* `JPoints.initFmodpsquareCoeffs`, `JPoints.initFmodpsquareEval`,
  `JPoints.initFmodpsquareValues`, `JPoints.initFmodpsquareSample`,
  `JPoints.initFmodpsquarePrime`: the steps for one prime.
* `JPoints.initFmodpsquareRecount`, `JPoints.initFmodpsquareRates`: the exact count of a sampled
  rate of `0`, and `init_fmodpsquare` up to the choice of the primes.

## Implementation notes

The rates are doubles of `JPoints.Double`, computed by the operations of `JPoints.Model.DoubleArith`
in the order of the C code, since they decide the order of `prec`, which the choice of the primes
reads, and the test of a rate of `0` (which never holds: the numerator of a rate is at least `p`).
The tables of the curve are those of `JPoints.CurveTables`, taken apart before the loops, so that
the compiled code writes them in place. The prime, its square, the counts and the indices, which the
C code keeps nonnegative in `long`s, are natural numbers. The local arrays `sampled` and `tabled`
of `init_fmodpsquare` are fields of `JPoints.Rates`, since the end of `init_fmodpsquare`, which
fills the tables of the primes chosen, reads `tabled`.
-/

@[expose] public section

namespace JPoints

/-! ### The record of a prime -/

/-- `entry`, the record of a prime considered for the sieve in `prec`: the prime, its rate, its
index in the table `prime[]` and the number `np0` of the classes `(0, b, c)` counted. The default
is the record of zeros of static storage.

C: `j-points.c:184`

Deviation: natural numbers for the `long`s `p`, `n` and `np0`, which the C code sets to a prime of
the table, an index of the table and a positive count. -/
structure Entry where
  /-- `p`: the prime. -/
  p : Nat := 0
  /-- `r`: the rate of the prime, `JPoints.rateOf`. -/
  r : Double := Double.zero
  /-- `n`: the index of the prime in the table `prime[]` (`JPoints.primeTable`). -/
  n : Nat := 0
  /-- `np0`: the number of the classes `(0, b, c)` modulo the prime counted for its rate,
  `(0, 0, 1)` and the classes `(0, 1, x)` with `f(x)` a square modulo the prime (`0` included). -/
  np0 : Nat := 0
  deriving Inhabited, Repr

/-- The comparison `compare_entries` by which `qsort` sorts `prec`: the sign of the difference
`a.r - b.r` of the rates, `1`, `-1` or `0`, the last also when the difference is a NaN.

C: `j-points.c:731-735`

Deviation: the records passed, for the pointers. -/
def compareEntries (a b : Entry) : Int :=
  let diff := a.r - b.r
  if diff > 0.0 then 1 else if diff < 0.0 then -1 else 0

/-- `rate_of`: the rate `((p - 1) (np0 + np1) + 1) / p³` of the prime `p`, the fraction of the
residue triples `(a, b, c)` modulo `p` that the sieve admits, for the number `np0` of the classes
`(0, b, c)` counted and the number `np1` of the classes `(1, b, c)` admitted (a sample's estimate),
computed in doubles in the order of the C code: `np0 + np1`, its product with `p - 1`, the sum
with `1`, and the quotient by `p p p`, each rounded.

C: `j-points.c:740-742` -/
def rateOf (p np0 : Int) (np1 : Double) : Double :=
  (Double.ofInt (p - 1) * (Double.ofInt np0 + np1) + 1.0) /
    (Double.ofInt p * Double.ofInt p * Double.ofInt p)

/-- The global `prec`, the records of the primes considered, with the local arrays `sampled` and
`tabled` of `init_fmodpsquare`, which are indexed by the index of the prime in the table: what the
first part of `init_fmodpsquare` leaves for the choice of the primes and for the tables of the
primes chosen.

C: `j-points.c:261`

Deviation: the global and the two local arrays (`j-points.c:798`) in a structure; arrays of
Booleans for the arrays of `int` flags. -/
structure Rates where
  /-- `prec`, `JPoints.numPrimes` records: those of the primes considered, sorted by rate when
  `JPoints.initFmodpsquareRates` returns, and the records of zeros of static storage after them. -/
  prec : Array Entry
  /-- `sampled`: at `pn`, whether the rate of `prime[pn]` comes from a sample of the classes
  `(1, b, c)`. -/
  sampled : Array Bool
  /-- `tabled`: at `pn`, whether the rows of `prime[pn]` in the table of the third stage are filled
  (by `JPoints.initTable`). -/
  tabled : Array Bool

/-! ### The steps for one prime -/

/-- The coefficients `f₀, …, f₆` of the curve searched (`coeffs`) modulo the prime `p` of the index
`pn`, written into the table `coeffsModP` at `pn * 8 + n`: the remainder of `mpz_fdiv_r_ui`, in
`[0, p)`.

C: `j-points.c:808-809`

Deviation: the table taken and returned, for the global; the remainder of `mpz_fdiv_r_ui`, which
rounds the quotient down, as `Int.emod` (`%` of integers) for `p > 0`, and the GMP temporary `tmp`,
into which the C code also writes it, left out (no reader of `tmp` reads it before writing it). -/
def initFmodpsquareCoeffs (coeffs coeffsModP : Array Int) (pn p : Nat) : Id (Array Int) := do
  let mut coeffsModP := coeffsModP
  for n in [0:7] do
    coeffsModP := coeffsModP.set! (pn * 8 + n) (coeffs[n]! % (p : Int))
  return coeffsModP

/-- The value `f(a)` modulo the prime `p` of the index `pn`, by Horner's rule from the coefficient
of degree `degree` modulo `p` in `coeffsModP`: for `n` from `degree - 1` down to `0`, `s` multiplied
by `a`, the coefficient `fₙ` modulo `p` added, and the sum reduced modulo `p`.

C: `j-points.c:818-823`

Deviation: natural numbers for the index `pn` and the `long` `degree`, and the steps of the loop
counted up, for the index `n` that counts down from `degree - 1` to `0`; `Int.tmod` for C's `%`. -/
def initFmodpsquareEval (coeffsModP : Array Int) (degree pn : Nat) (p a : Int) : Id Int := do
  let mut s := coeffsModP[pn * 8 + degree]!
  for i in [0:degree] do
    let n := degree - 1 - i
    s := s * a
    s := s + coeffsModP[pn * 8 + n]!
    s := s.tmod p
  return s

/-- For the prime `p` of the index `pn`: whether the coefficient `f₆` modulo `p`, `0` for a
quintic, is a square (`0` included), written into `hasInfinity` at `pn`; whether `f(x)` is a square
modulo `p`, for `x < p`, written into `isFSquare` at `pn * 256 + x`, `f(0)` from `f₀` and the others
by `JPoints.initFmodpsquareEval`; and the number `np0 = 1 + #{x < p : f(x) a square}` of the
classes `(0, b, c)` counted, `(0, 0, 1)` and the `(0, 1, x)` with `f(x)` a square. A square is a
residue whose entry in `squares` is not `p`.

C: `j-points.c:811-817`, `j-points.c:824-825`

Deviation: the tables taken and returned, for the globals; natural numbers for the index `pn`, the
`long` `degree`, the prime and the count `np0`, and the entries of `squares` read at the natural
number of the index, which the reductions make nonnegative; Booleans for the `unsigned char`s, each
tested as the value of its assignment is in the C code. -/
def initFmodpsquareValues (squares coeffsModP : Array Int) (hasInfinity isFSquare : Array Bool)
    (degree pn p : Nat) : Id (Array Bool × Array Bool × Nat) := do
  let hasInfinity :=
    hasInfinity.set! pn (squares[pn * maxPrime + coeffsModP[pn * 8 + 6]!.toNat]! != (p : Int))
  let mut np0 := 1
  let square := squares[pn * maxPrime + coeffsModP[pn * 8]!.toNat]! != (p : Int)
  let mut isFSquare := isFSquare.set! (pn * maxPrimeEven) square
  if square then np0 := np0 + 1
  for a in [1:p] do
    let s ← initFmodpsquareEval coeffsModP degree pn p a
    let square := squares[pn * maxPrime + s.toNat]! != (p : Int)
    isFSquare := isFSquare.set! (pn * maxPrimeEven + a) square
    if square then np0 := np0 + 1
  return (hasInfinity, isFSquare, np0)

/-- The sample of the classes `(1, b, c)` modulo the prime `p` of the index `pn`, with `pp = p²`:
the class `(1, b, c)` with `b p + c = i` for every `i < pp` that `stride` divides, admitted when
`c` is `b² / 4` modulo `p` (computed as in `JPoints.initTable`) or when `JPoints.pointOnJ` admits it
with the reciprocal `recip` of `p`; the number of the classes admitted and the number of the classes
of the sample.

C: `j-points.c:833-840`

Deviation: the tables and the degree passed, for the globals that `point_on_j` reads; natural
numbers for the index `pn`, the `long` `degree`, the prime, its square, the stride, the residues
`i`, `b` and `c` and the counts, which the C code keeps nonnegative, so that `/` is the division of
natural numbers; `Int.tdiv` and `Int.tmod` for C's `/` and `%` in `b² / 4`; a `while` loop for the
`for` loop with the step `stride`. -/
def initFmodpsquareSample (squares coeffsModP : Array Int) (degree pn p pp : Nat) (recip : UInt64)
    (stride : Nat) : Id (Nat × Nat) := do
  let mut count := 0
  let mut total := 0
  let mut i := 0
  while i < pp do
    let b := i / p
    let c := i - b * p
    let bb := ((1 + (p : Int) * (3 - (p &&& 2 : Nat))).tdiv 4 * b * b).tmod p
    total := total + 1
    let admitted ← if (c : Int) == bb then pure true
      else pointOnJ squares coeffsModP degree pn p recip b c
    if admitted then count := count + 1
    i := i + stride
  return (count, total)

/-- The body of the loop of `init_fmodpsquare` over the primes, for the prime `p = prime[pn]`, the
tables `t`, the coefficients `coeffs` and the degree `degree` of the curve searched: the reciprocal
`⌈2 ^ 32 / p⌉` in `unsigned long`s, the coefficients modulo `p`
(`JPoints.initFmodpsquareCoeffs`), the squares and `np0` (`JPoints.initFmodpsquareValues`); then,
for the stride `⌈p² / SAMPLE_PAIRS⌉`, the rows of `p` in the table of the third stage
(`JPoints.initTable`) and their count out of `p²` when the stride is `1`, else the count of a sample
(`JPoints.initFmodpsquareSample`), with `sampled` and `tabled` at `pn`; and the record of `p` at
`pn` in `prec`, with the rate `JPoints.rateOf p np0 np1` for `np1 = count p² / total`, a product
and a quotient of doubles.

C: `j-points.c:802-806`, `j-points.c:826-832`, `j-points.c:841-845`

Deviation: the tables taken and the tables of the curve and the records returned, for the globals
and the local arrays; natural numbers for the index `pn`, the `long` `degree`, the prime, its
square, the stride and the counts, which the C code keeps nonnegative; Booleans for the `int`
flags. -/
def initFmodpsquarePrime (t : Tables) (coeffs : Array Int) (degree : Nat) (ct : CurveTables)
    (r : Rates) (pn : Nat) : Id (CurveTables × Rates) := do
  let ⟨coeffsModP, hasInfinity, isFSquare, isPointOnJ⟩ := ct
  let p := primeTable[pn]!
  let pp := p * p
  let recip : UInt64 := ((1 : UInt64) <<< 32 + UInt64.ofNat p - 1) / UInt64.ofNat p
  let coeffsModP ← initFmodpsquareCoeffs coeffs coeffsModP pn p
  let (hasInfinity, isFSquare, np0) ←
    initFmodpsquareValues t.squares coeffsModP hasInfinity isFSquare degree pn p
  let stride := (pp + samplePairs - 1) / samplePairs
  let sampled := r.sampled.set! pn (stride > 1)
  let tabled := r.tabled.set! pn false
  let (ct, count, total, tabled) ← if stride == 1 then do
      let (ct, count) ← initTable t ⟨coeffsModP, hasInfinity, isFSquare, isPointOnJ⟩ degree pn
      pure (ct, count, pp, tabled.set! pn true)
    else do
      let (count, total) ← initFmodpsquareSample t.squares coeffsModP degree pn p pp recip stride
      pure (⟨coeffsModP, hasInfinity, isFSquare, isPointOnJ⟩, count, total, tabled)
  let rate := rateOf p np0 (Double.ofInt count * Double.ofInt pp / Double.ofInt total)
  return (ct, { prec := r.prec.set! pn { p, r := rate, n := pn, np0 }, sampled, tabled })

/-! ### The rates of the primes -/

/-- The exact count for a sampled rate of `0`, for the first `nPrimes` primes (`num_primes`): for
each prime `prime[pn]` whose rate was sampled and is `0`, the rows of the prime in the table of the
third stage filled by `JPoints.initTable`, the rate made from their count, and `tabled` set at
`pn`. A sampled rate is never `0` (the numerator of a rate is at least `p`), so that this changes
nothing, but the C code does it.

C: `j-points.c:850-855`

Deviation: the tables taken and the tables of the curve and the records returned, for the globals
and the local arrays; a natural number for the index `pn`; `JPoints.Double.beq` for `==` on
doubles. -/
def initFmodpsquareRecount (t : Tables) (degree nPrimes : Nat) (ct : CurveTables) (r : Rates) :
    Id (CurveTables × Rates) := do
  let mut ct := ct
  let mut prec := r.prec
  let mut tabled := r.tabled
  for pn in [0:nPrimes] do
    if r.sampled[pn]! && prec[pn]!.r.beq 0.0 then
      let (ct', count) ← initTable t ct degree pn
      ct := ct'
      prec := prec.set! pn
        { prec[pn]! with r := rateOf primeTable[pn]! prec[pn]!.np0 (Double.ofInt count) }
      tabled := tabled.set! pn true
  return (ct, { r with prec, tabled })

/-- `init_fmodpsquare` up to the choice of the primes, for the tables `t`, the coefficients
`coeffs` and the degree `degree` of the curve searched, the number `nPrimes` of the primes
considered (`num_primes`), the tables of the curve `ct` and the records `prec`: for each of the
first `nPrimes` primes of the table, `JPoints.initFmodpsquarePrime`; then the exact count of a
sampled rate of `0` (`JPoints.initFmodpsquareRecount`); and the first `nPrimes` records of `prec`
sorted by `qsort` with `compare_entries` (`JPoints.qsort`, `JPoints.compareEntries`). The tables of
the curve and the records with `sampled` and `tabled`.

C: `j-points.c:797-801`, `j-points.c:846`, `j-points.c:857`

Deviation: the tables and the records taken and returned, for the globals; a natural number for
the index `pn`; the local arrays `sampled` and `tabled`, which the C code leaves uninitialised,
start as `false`, and only the entries that the loop writes are read; the sort of glibc as
`JPoints.qsort`, its merge sort, as glibc sorts when it can allocate its buffer. -/
def initFmodpsquareRates (t : Tables) (coeffs : Array Int) (degree nPrimes : Nat)
    (ct : CurveTables) (prec : Array Entry) : Id (CurveTables × Rates) := do
  let mut ct := ct
  let mut r : Rates :=
    { prec, sampled := .replicate numPrimes false, tabled := .replicate numPrimes false }
  for pn in [0:nPrimes] do
    (ct, r) ← initFmodpsquarePrime t coeffs degree ct r pn
  (ct, r) ← initFmodpsquareRecount t degree nPrimes ct r
  return (ct, { r with prec := qsort compareEntries r.prec nPrimes })

/-! ### Examples

The values of the C code at the pin: of `rate_of` from a test program with a copy of it, and of
`init_fmodpsquare` from a copy of `j-points` that prints the state after the sort of `prec` and
stops, for the curve searched (after `normalise_curve`) and the number of the primes considered
(`-p`): the order of the records (their indices `n`), the hashes of their rates (by their bits), of
their counts `np0` and of their primes, the hashes of the tables of the curve (of the table of the
third stage the rows of the primes considered), and `sampled` and `tabled`. For the test of the
exact count of a sampled rate of `0`, which the C code never meets, the copy sets some sampled
rates to `0` before it. A hash is `h ↦ h * 1000003 + v` modulo `2 ^ 64` over the entries in the
order of their indices, from `h = 0`. -/

-- The hash of the examples over the entries `vs`.
private def hash (vs : Array UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The flags `fs` as a string of `0`s and `1`s.
private def flags (fs : Array Bool) : String :=
  String.ofList (fs.toList.map (if · then '1' else '0'))

-- The double `x` as a record with that rate.
private def withRate (x : Double) : Entry := { r := x }

-- `+∞` and the NaN of the C library's `NAN`.
private def inf : Double := ⟨0x7ff0000000000000⟩
private def nan : Double := ⟨0x7ff8000000000000⟩

#guard [(1.0, 0.5, 1), (0.5, 1.0, -1), (0.25, 0.25, 0), (0.0, -0.0, 0), (inf, 1.0, 1),
    (inf, inf, 0), (-inf, -inf, 0), (nan, 1.0, 0), (1.0, nan, 0), (⟨1⟩, 0.0, 1),
    (0.0, ⟨1⟩, -1)].all fun (x, y, c) ↦ compareEntries (withRate x) (withRate y) == c

-- `qsort` with `compare_entries` on rates with NaNs and infinities, where `∞ - ∞` is a NaN.
#guard ((qsort compareEntries (#[1.0, inf, 0.0, inf, -inf, nan, 2.0, 0.5, nan, inf, 1.0].map
    withRate |>.zipIdx |>.map fun (e, i) ↦ { e with n := i }) 11).map (·.n)).toList ==
  [4, 2, 0, 1, 3, 5, 7, 6, 8, 10, 9]

-- `rate_of`, among them the rate `1` of a prime that admits everything, and the estimate of a
-- sample, `count * pp / total`.
#guard [(3, 1, 0x0, 0x3fbc71c71c71c71c), (3, 4, 0x4022000000000000, 0x3ff0000000000000),
    (251, 252, 0x40eec32000000000, 0x3ff0000000000000),
    (67, 40, 0x40a1cb0000000000, 0x3fe0461f672bc5e6),
    (251, 140, 0x40dd4c07df3b645a, 0x3fde7efe897e6945),
    (61, 33, 0x409d380000000000, 0x3fe018ebc19a5b2a), (251, 1, 0x0, 0x3ef0a4d007ff2ff4),
    (3, 1, 0x7fe1ccf385ebc8a0, 0x7ff0000000000000),
    (7, 3, 0x7ff8000000000000, 0x7ff8000000000000)].all fun (p, np0, np1, r) ↦
    (rateOf p np0 ⟨np1⟩).bits == r
#guard (Double.ofInt 2277 * Double.ofInt 4489 / Double.ofInt 2245).bits == 0x40b1c8fc59db482f

-- The tables of `init_main` and of the curve as the program starts, and the records of zeros.
private def start : Tables × CurveTables × Array Entry :=
  ((initMain Tables.initial).run, CurveTables.initial, .replicate numPrimes {})

-- `init_fmodpsquare` up to the choice, for the coefficients `cs` and the degree `d` of the curve
-- searched and `np` primes considered.
private def rates (cs : Array Int) (d np : Nat) : CurveTables × Rates :=
  let (t, ct, prec) := start
  (initFmodpsquareRates t cs d np ct prec).run

-- The same, with the rates of the indices `zeros` set to `0` after the loop over the primes.
private def ratesZero (cs : Array Int) (d np : Nat) (zeros : List Nat) : CurveTables × Rates :=
  Id.run do
    let (t, ct, prec) := start
    let mut ct := ct
    let mut r : Rates := ⟨prec, .replicate numPrimes false, .replicate numPrimes false⟩
    for pn in [0:np] do
      (ct, r) ← initFmodpsquarePrime t cs d ct r pn
    for k in zeros do r := { r with prec := r.prec.set! k { r.prec[k]! with r := 0.0 } }
    (ct, r) ← initFmodpsquareRecount t d np ct r
    return (ct, { r with prec := qsort compareEntries r.prec np })

-- What the copy of the C code prints, for `np` primes considered.
private def summary (np : Nat) (s : CurveTables × Rates) :
    List Nat × List UInt64 × String × String :=
  let (ct, r) := s
  let prec := r.prec.extract 0 np
  let hashFlags (fs : Array Bool) (n : Nat) : UInt64 :=
    fs.foldl (fun h b ↦ h * 1000003 + if b then 1 else 0) 0 0 n
  (prec.toList.map (·.n),
    [hash (prec.map (·.r.bits)), hash (prec.map (·.np0.toUInt64)), hash (prec.map (·.p.toUInt64)),
      hash (ct.coeffsModP.map UInt64.ofInt), hashFlags ct.hasInfinity numPrimes,
      hashFlags ct.isFSquare (numPrimes * maxPrimeEven),
      hashFlags ct.isPointOnJ (np * maxPrimeEven * maxPrimeEven)],
    flags (r.sampled.extract 0 np), flags (r.tabled.extract 0 np))

-- A sextic of `testcurves2`, with all primes.
#guard summary 53 (rates #[1, 4, 3, -8, 2, 8, 7] 6 53) ==
  ([48, 34, 35, 29, 45, 21, 12, 27, 37, 41, 30, 8, 15, 47, 14, 23, 50, 40, 11, 38, 36, 25, 51, 31,
      16, 22, 42, 13, 28, 46, 26, 44, 32, 19, 33, 7, 52, 49, 39, 24, 17, 18, 43, 9, 6, 20, 10, 3, 1,
      2, 5, 4, 0],
    [14219440367052132670, 16705835480827958533, 17317019396175217391, 4627478108643463220,
      12667289985001821665, 5850927734063238848, 5093387786610826308],
    "00000000000000000111111111111111111111111111111111111",
    "11111111111111111000000000000000000000000000000000000")
-- The monic quintic of example 2 of the README of `j-points`; `f = (x³ + x + 1)² + 105`, a square
-- modulo `3`, `5` and `7`, whose rates there are `1`, in the order of the primes; the curve
-- `0 1 2 -1 3 1 1` reversed and `5 -2 3 1 -1 -1` negated (the coefficients from `f₀` on); two
-- curves with large coefficients; and one prime.
#guard summary 20 (rates #[1, 178, 817, -274, 16, 1, 0] 5 20) ==
  ([17, 13, 19, 10, 7, 8, 15, 16, 11, 14, 18, 5, 12, 2, 9, 6, 3, 4, 0, 1],
    [6173402084790149849, 1609590289091419804, 16842076063007995090, 1793336077815620033,
      7268596541933839064, 4499970625339279680, 13618552476633876935],
    "00000000000000000111", "11111111111111111000")
#guard summary 12 (rates #[106, 2, 1, 2, 2, 0, 1] 6 12) ==
  ([11, 8, 9, 6, 10, 5, 3, 7, 4, 0, 1, 2],
    [13768860024459029944, 17200698332864230160, 1294912726235036176, 3272012481838888171,
      4460777891842762088, 3001404929620977600, 10323796408861505767],
    "000000000000", "111111111111")
#guard summary 20 (rates #[1, 1, 3, -1, 2, 1, 0] 5 20) ==
  ([12, 10, 16, 17, 6, 14, 13, 11, 15, 18, 9, 4, 19, 5, 7, 8, 2, 3, 0, 1],
    [7361589562512209584, 9012254277958151430, 12431525136923256386, 14168070777035297897,
      7268596541933839064, 9072228874312319764, 10584654932309870136],
    "00000000000000000111", "11111111111111111000")
#guard summary 20 (rates #[5, 2, 3, -1, -1, 1, 0] 5 20) ==
  ([13, 19, 11, 4, 17, 18, 10, 14, 16, 15, 12, 8, 5, 7, 9, 2, 3, 6, 0, 1],
    [4071598582616380089, 9196816978048217960, 16230449776971133026, 2617483901524246563,
      7268596541933839064, 5820511909170126298, 14083673598243657267],
    "00000000000000000111", "11111111111111111000")
#guard summary 20 (rates #[3, -1, 2, 1, -1, 2, 123456789012345678901] 6 20) ==
  ([16, 9, 17, 15, 13, 11, 19, 3, 14, 12, 8, 10, 6, 7, 18, 2, 4, 5, 1, 0],
    [6775860835950440509, 3415287678109673291, 6248051280955743970, 13486317893132435034,
      9102104638016932847, 5891451427073184193, 664531455055268244],
    "00000000000000000111", "11111111111111111000")
#guard summary 20 (rates #[-98765432109876543210, 1, 2, 3, 4, 5, 0] 5 20) ==
  ([6, 3, 10, 18, 11, 14, 8, 17, 19, 16, 13, 12, 5, 15, 9, 7, 2, 1, 4, 0],
    [14387463214282444451, 7079637912154983756, 4354137094108348378, 223173419415516602,
      7268596541933839064, 1062909771931771644, 15680502384714749227],
    "00000000000000000111", "11111111111111111000")
#guard summary 1 (rates #[1, 4, 3, -8, 2, 8, 7] 6 1) ==
  ([0], [4603846419076039263, 3, 3, 6461566272736509952, 12097824945061001489,
      15881541509488288190, 2601702501518771611], "0", "1")

-- The exact count of the sampled rates of `67` and `73`, set to `0`.
#guard summary 20 (ratesZero #[1, 4, 3, -8, 2, 8, 7] 6 20 [17, 19]) ==
  ([12, 8, 15, 14, 11, 16, 13, 19, 7, 17, 18, 9, 6, 10, 3, 1, 2, 5, 4, 0],
    [14538699671217564866, 10409101709790967671, 9817213264089389266, 3683433972510414584,
      8709831556261560447, 4110434287494595835, 6591668627125202736],
    "00000000000000000111", "11111111111111111101")

end JPoints

end
