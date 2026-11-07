/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Sift

import JPoints.Model.Input
import JPoints.Model.Rates

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Check
meta import JPoints.Model.Input
meta import JPoints.Model.Rates
meta import JPoints.Model.Rows
meta import JPoints.Model.TwoAdic

/-!
# The double points, the steps of the rows and the units of work

Three pieces of the search of `j-points` around the sieve. `find_double_points`
(`JPoints.findDoublePoints`) finds the points whose image on the Kummer surface is
`(a² : 2ab : b²)`, the points `[2P - O]` for a point `P` of the curve with `x = b / a`, by a sieve
of its own: for `1 ≤ a ≤ ⌊√H⌋` (only the squares `a` when the curve searched is a monic quintic) and
`|b| ≤ min(H / (2a), ⌊√H⌋)` coprime to `a`, it tests at each sieving prime `p` whether `f(b / a)` is
a square modulo `p` (whether the curve has points at infinity modulo `p`, when `p ∣ a`), and hands
the triples that pass to the exact check. `row_step` (`JPoints.rowStep`) gives the step of the loop
over `b` of the main search for an `a`, the product of the sieving primes that divide `a` and modulo
which the curve has no point at infinity. `unit_a` (`JPoints.unitA`) gives the first coordinate of a
unit of work of the main search.

## Main definitions

* `JPoints.TablePtr`, `JPoints.TablePtr.read`: a pointer of `find_double_points` into a table of
  the curve, and the entries that it reads.
* `JPoints.Stype`: a record of the sieve of `find_double_points`.
* `JPoints.findDoublePointsSetup`: the records of the sieving primes for an `a`.
* `JPoints.findDoublePointsSieve`: the sieve of a pair `(a, b)`.
* `JPoints.findDoublePointsRows`: the loop over `b` for an `a`.
* `JPoints.findDoublePointsSquares`, `JPoints.findDoublePointsAll`: the loops over `a` of the two
  branches.
* `JPoints.findDoublePoints`: the search for the double points.
* `JPoints.rowStep`: the step of the loop over `b` of the main search.
* `JPoints.unitA`: the first coordinate of a unit of work.

## Implementation notes

The functions read the globals of the sieve (`JPoints.SiftGlobals`), of which the tables of
`init_main` (`inverses`), the tables of the curve modulo the primes (`has_infinity` and
`is_f_square`), the sieving primes (`pnn` and `sieve_primes3`) and what the exact check reads (the
curve searched, the height bound and `one_point`). The exact check writes the output, which is
taken and returned. The local array `ssp0` of the records of the sieving primes is an array of
`NUM_PRIMES` records, threaded through the loops over `a` as the C code keeps it from one `a` to the
next; the pointer `ptr` of a record into `has_infinity` or into `is_f_square` is the table and the
index (`JPoints.TablePtr`), and the pointer `ssp` into `ssp0` is the index of the record.
`find_double_points` is split at its loops: the loops over `a` of its two branches, and the
records for an `a`, the sieve of a pair and the loop over `b`, each of these written once for the
two branches of the C code, which have the same code for them except for the skip of an `a` at a
prime that divides it and modulo which the curve has no point at infinity, which only the branch
for the curves that are not monic quintics makes.
-/

@[expose] public section

namespace JPoints

/-! ### The records of the sieve of the double points -/

/-- A pointer of `find_double_points` into a table of the curve, the field `ptr` of a record
`JPoints.Stype`: `&has_infinity[i]`, or `&is_f_square[0][0] + i`, the entry `i` of the flat table
`is_f_square` (`JPoints.CurveTables`), of which `&is_f_square[pn][0]` is the index
`pn * MAX_PRIME_EVEN`.

It models no C code of its own: the pointers that `JPoints.findDoublePointsSetup` sets. -/
inductive TablePtr where
  /-- `&has_infinity[i]`. -/
  | hasInfinity (i : Nat)
  /-- `&is_f_square[0][0] + i`. -/
  | isFSquare (i : Nat)
  deriving DecidableEq, Repr

/-- The entry `ptr[k]` of the tables of the curve `ct` that the pointer `ptr` reads at the offset
`k`.

It models no C code of its own: the reads of `JPoints.findDoublePointsSieve`. -/
def TablePtr.read (ct : CurveTables) : TablePtr → Nat → Bool
  | .hasInfinity i, k => ct.hasInfinity[i + k]!
  | .isFSquare i, k => ct.isFSquare[i + k]!

/-- `struct stype`, a record of the sieve of `find_double_points` for a sieving prime: the prime
`p`, the inverse `ap` of `a` modulo `p` (`0` when `p ∣ a`), and the pointer `ptr` to the table
that decides whether `(a, b)` passes at `p`: `has_infinity` at the index of `p` when `p ∣ a`, and
otherwise the row of `p` of `is_f_square`, read at `b a⁻¹ mod p`. The defaults stand for the
uninitialized entries of the local array `ssp0`, which the C code writes before it reads them.

C: `j-points.c:1189`

Deviation: integers for the `long`s `p` and `ap`; a `JPoints.TablePtr` for the pointer `ptr`. -/
structure Stype where
  /-- `p`, the sieving prime. -/
  p : Int := 0
  /-- `ap`, the inverse of `a` modulo `p`, or `0` when `p ∣ a`. -/
  ap : Int := 0
  /-- `ptr`, the table that decides whether `(a, b)` passes at `p`. -/
  ptr : TablePtr := .hasInfinity 0
  deriving DecidableEq, Inhabited, Repr

/-! ### The double points -/

/-- The records `ssp0` of the sieving primes for the first coordinate `a ≥ 1`, as the loop over the
sieving primes of `find_double_points` sets them for each `a`: for the `n`-th sieving prime
`p = ssp0[n].p`, of index `pn = pnn[n]` in `prime[]`, when `p ∣ a`, the inverse `0` and the pointer
`&has_infinity[pn]`, and otherwise the inverse of `a mod p` (`inverses[pn][a mod p]`) and the
pointer `&is_f_square[pn][0]`. Under `skip` (the branch for the curves that are not monic
quintics), when `p ∣ a` and the curve has no points at infinity modulo `p`, the loop stops there,
and the C code goes on to the next `a` (`goto nexta2`). The records, and whether the loop went
through.

C: `j-points.c:1198-1207`, `j-points.c:1227-1237`

Deviation: one function for the loops of the two branches of `find_double_points`, which differ
only in the test that skips `a` (line 1230), made under `skip`, and returning the records written
so far with `false` for the `goto`; the records taken and returned, for the local array `ssp0`;
the index `n` for the pointer `ssp`, which the C code moves along with `n`; integers for the
`long`s, `Int.tmod` for C's `%`. -/
def findDoublePointsSetup (g : SiftGlobals) (skip : Bool) (ssp0 : Array Stype) (a : Int) :
    Id (Array Stype × Bool) := do
  let mut ssp0 := ssp0
  for n in [0:g.sievePrimes3] do
    let pn := g.pnn[n]!
    let ap0 := a.tmod ssp0[n]!.p
    if ap0 == 0 then
      if skip && !g.curve.hasInfinity[pn]! then return (ssp0, false)
      ssp0 := ssp0.set! n { ssp0[n]! with ap := 0, ptr := .hasInfinity pn }
    else
      ssp0 := ssp0.set! n { ssp0[n]! with
        ap := g.tables.inverses[pn * maxPrimeEven + ap0.toNat]!
        ptr := .isFSquare (pn * maxPrimeEven) }
  return (ssp0, true)

/-- The sieve of `find_double_points` for the second coordinate `b`, with the records `ssp0` of the
first `sieve_primes3` sieving primes for the first coordinate: whether `(a, b)` passes at every
prime `p`, the entry of the table of its record at `(ap * bp) mod p`, `bp = b mod p` in `[0, p)`
(`has_infinity` at the index of `p` when `p ∣ a`, where `ap = 0`; `f(b / a)` a square modulo `p`
otherwise), the primes in the order of `pnn`, up to the first at which it fails.

C: `j-points.c:1212-1216`, `j-points.c:1242-1246`

Deviation: one function for the loops of the two branches of `find_double_points`, which are the
same code; the index `k` of the record for the pointer `ssp`, which the C code moves on while it
counts `n` down from `sieve_primes3`; integers for the `long`s, `Int.tmod` for C's `%`; `false` for
the `goto` to the next `b` (`nextb1`, `nextb2`). -/
def findDoublePointsSieve (ct : CurveTables) (ssp0 : Array Stype) (sievePrimes3 : Nat) (b : Int) :
    Id Bool := do
  for k in [0:sievePrimes3] do
    let ssp := ssp0[k]!
    let p := ssp.p
    let mut bp := b.tmod p
    if bp < 0 then bp := bp + p
    if !ssp.ptr.read ct ((ssp.ap * bp).tmod p).toNat then return false
  return true

/-- The loop of `find_double_points` over the second coordinate `b` for the first coordinate
`a ≥ 1`, with the records `ssp0` of the sieving primes for `a` and `wheight = ⌊√H⌋`: for
`|b| ≤ bmax = min(H / (2a), wheight)` in increasing order, when `gcd(a, b) = 1`
(`JPoints.relprime`) and `(a, b)` passes the sieve (`JPoints.findDoublePointsSieve`), the triple
`(a², 2ab, b²)` checked (`JPoints.checkOnePoint`). Whether one point is enough (`-1`) and the check
of a triple found one, which ends the search, and the output with the points.

C: `j-points.c:1208-1211`, `j-points.c:1217-1221`, `j-points.c:1238-1241`, `j-points.c:1247-1251`

Deviation: one function for the loops of the two branches of `find_double_points`, which are the
same code; integers for the `long`s, `/` for C's division of the positive `height` by `2 a`;
`true` for the `return(1)` of `find_double_points`; the output taken and returned, for the
thread-local counter `total` and `stdout`. -/
def findDoublePointsRows (g : SiftGlobals) (ssp0 : Array Stype) (wheight : Int) (out : Output)
    (a : Int) : Id (Bool × Output) := do
  let mut bmax := g.check.height / (2 * a)
  if wheight < bmax then bmax := wheight
  let mut out := out
  for b in (-bmax)...=bmax do
    if ← relprime a b then
      if ← findDoublePointsSieve g.curve ssp0 g.sievePrimes3 b then
        let (r, out') ← checkOnePoint g.check out (a * a) (2 * a * b) (b * b)
        out := out'
        if r && g.check.onePoint then return (true, out)
  return (false, out)

/-- The loop of `find_double_points` over the squares `a = aa²`, `aa = 1, 2, …` while
`a ≤ wheight`, for a monic quintic, with the records `ssp0` of the sieving primes: for each `a`
the records set (`JPoints.findDoublePointsSetup`, which skips no `a` here) and the loop over `b`
(`JPoints.findDoublePointsRows`). Whether one point is enough (`-1`) and one was found, which ends
the search, and the output with the points.

C: `j-points.c:1195-1197`, `j-points.c:1222`

Deviation: integers for the `long`s; a `while` loop over `aa`, which ends on the data, for the
`for` loop whose test sets `a`; the records taken, for the local array `ssp0`, and threaded
through the loop; `true` for the `return(1)` of `find_double_points`; the output taken and
returned, for the thread-local counter `total` and `stdout`. -/
def findDoublePointsSquares (g : SiftGlobals) (ssp0 : Array Stype) (wheight : Int)
    (out : Output) : Id (Bool × Output) := do
  let mut ssp0 := ssp0
  let mut out := out
  let mut aa : Int := 1
  while aa * aa ≤ wheight do
    let a := aa * aa
    (ssp0, _) ← findDoublePointsSetup g false ssp0 a
    let (r, out') ← findDoublePointsRows g ssp0 wheight out a
    out := out'
    if r then return (true, out)
    aa := aa + 1
  return (false, out)

/-- The loop of `find_double_points` over every `1 ≤ a ≤ wheight`, for the curves that are not
monic quintics, with the records `ssp0` of the sieving primes: for each `a` the records set
(`JPoints.findDoublePointsSetup`), and unless that skips `a` (at a prime that divides `a` and
modulo which the curve has no points at infinity), the loop over `b`
(`JPoints.findDoublePointsRows`). Whether one point is enough (`-1`) and one was found, which ends
the search, and the output with the points.

C: `j-points.c:1225-1226`, `j-points.c:1252-1253`

Deviation: integers for the `long`s; the records taken, for the local array `ssp0`, and threaded
through the loop; the skip of `a` (`goto nexta2`) by the flag of `JPoints.findDoublePointsSetup`;
`true` for the `return(1)` of `find_double_points`; the output taken and returned, for the
thread-local counter `total` and `stdout`. -/
def findDoublePointsAll (g : SiftGlobals) (ssp0 : Array Stype) (wheight : Int) (out : Output) :
    Id (Bool × Output) := do
  let mut ssp0 := ssp0
  let mut out := out
  for a in (1 : Int)...=wheight do
    let (ssp, through) ← findDoublePointsSetup g true ssp0 a
    ssp0 := ssp
    if through then
      let (r, out') ← findDoublePointsRows g ssp0 wheight out a
      out := out'
      if r then return (true, out)
  return (false, out)

/-- `find_double_points`, the search for the points `[2P - O]`, whose image on the Kummer surface is
`(a² : 2ab : b²)` with `gcd(a, b) = 1`, for the globals `g`: `wheight = ⌊√H⌋` as
`floor(sqrt(height))` computes it in doubles; the prime `prime[pnn[n]]` in the record `n`, for each
of the first `sieve_primes3` sieving primes; and the loop over the squares `a` for a monic quintic
(`JPoints.findDoublePointsSquares`) or over all `a` otherwise (`JPoints.findDoublePointsAll`).
Whether one point is enough (`-1`) and one was found, and the output with the points.

C: `j-points.c:1183-1188`, `j-points.c:1189`, `j-points.c:1190-1194`, `j-points.c:1223-1224`,
`j-points.c:1254-1255`

Deviation: integers for the `long`s; `wheight` by the doubles of `JPoints.Model.DoubleArith`, the
exact conversion of `height`, `sqrt` and `floor`, and the conversion back to a `long`, which
truncates (`JPoints.Double.toInt64`); the local array `ssp0` of `NUM_PRIMES` records that start as
`JPoints.Stype`'s defaults, for the uninitialized array; the test `mpz_cmp_si` of `f₅` with `1` as
the equality of integers; a Boolean for the `int` returned; the output taken and returned, for the
thread-local counter `total` and `stdout`. -/
def findDoublePoints (g : SiftGlobals) (out : Output) : Id (Bool × Output) := do
  let wheight := (Double.ofInt g.check.height).sqrt.floor.toInt64.toInt
  let mut ssp0 : Array Stype := .replicate numPrimes {}
  for n in [0:g.sievePrimes3] do
    ssp0 := ssp0.set! n { ssp0[n]! with p := (primeTable[g.pnn[n]!]! : Int) }
  if g.check.curve.degree == 5 && g.check.curve.coeffs[5]! == 1 then
    findDoublePointsSquares g ssp0 wheight out
  else
    findDoublePointsAll g ssp0 wheight out

/-! ### The units of work of the main search -/

/-- `row_step`, the step of the loop over `b` of the main search for the first coordinate `a ≥ 0`:
the product `m` of the sieving primes `p` (of all three stages) with `p ∣ a` modulo which the curve
has no points at infinity, the rows `(a, b)` with `p ∤ b` being empty for those; or `H + 1`, as
soon as the product exceeds the height bound `H`, so that `b = 0` is the only row (and none for
`a = 0`).

C: `j-points.c:1265-1276`

Deviation: integers for the `long`s, `Int.tmod` for C's `%`; a natural number for the index `n`. -/
def rowStep (g : SiftGlobals) (a : Int) : Id Int := do
  let mut m : Int := 1
  for n in [0:g.sievePrimes3] do
    let pn := g.pnn[n]!
    let p : Int := primeTable[pn]!
    if !g.curve.hasInfinity[pn]! && a.tmod p == 0 then
      m := m * p
      if m > g.check.height then return g.check.height + 1
  return m

/-- `unit_a`, the first coordinate of the unit of work `k` of the main search, for the curve
searched `curve`: `k²` when it is a monic quintic, `k` otherwise.

C: `j-points.c:1314-1315`

Deviation: integers for the `long`s; the test `mpz_cmp_si` of `f₅` with `1` as the equality of
integers. -/
def unitA (curve : SearchCurve) (k : Int) : Int :=
  if curve.degree == 5 && curve.coeffs[5]! == 1 then k * k else k

/-! ### Examples

From a test program that includes `j-points.c` of the pin, runs the set-up of `main` on a command
line (`read_input`, and quietly `normalise_curve`, `kummer_init` and `init_fmodpsquare`, which
fills the tables of the curve), sets the sieving primes `pnn` and their number `sieve_primes3`
given, and calls `row_step`, `unit_a` and `find_double_points`: the values that they return, the
text that they print and `total`; and from a copy of it that prints, in `find_double_points`, the
records of each `a` (`A a ap:t …`, `t = 0` for `has_infinity` and `1` for `is_f_square`), the skip
of an `a` at the `n`-th prime (`S a n`), and each pair `(a, b)` that passes the sieve (`C a b`). -/

-- The globals of the search for the command line `args` (after the name of the program), with the
-- sieving primes of the indices `pnn` in `prime[]`, as the test program sets them: the tables of
-- the curve searched as `init_fmodpsquare` fills them for the primes considered, and what the
-- exact check reads.
private def globals (args : List String) (pnn : List Nat) : SiftGlobals :=
  let input := match (Cli.readInput args.toArray).run with
    | .ok input => input
    | .error _ => {}
  let t := (initMain Tables.initial).run
  let curve := (normalizeCurve input.coeffs input.degree.toNat true).run.1
  let ct := (initFmodpsquareRates t curve.coeffs curve.degree input.numPrimes.toNat
    CurveTables.initial (.replicate numPrimes {})).run.1
  { tables := t, curve := ct, sieve := SieveTables.initial, arraySize := 0
    check := { curve, kummer := kummerInit curve.coeffs, height := input.height
               dbound := input.dbound, dbounded := input.dbounded, allPoints := input.allPoints
               onePoint := input.onePoint, printFormat := input.printFormat }
    twoAdic := TwoAdic.initial, pnn := pnn.toArray ++ .replicate (numPrimes + 1 - pnn.length) 0
    sievePrimes1 := 0, sievePrimes2 := 0, sievePrimes3 := pnn.length, begmask := 0
    endmask := 0 }

-- `find_double_points` for the command line `args` and the sieving primes `pnn`, from the empty
-- output: the value that it returns, the text that it prints and `total`.
private def doublePoints (args : List String) (pnn : List Nat) : Bool × String × Nat :=
  let (r, out) := (findDoublePoints (globals args pnn) {}).run
  (r, out.text, out.total)

-- The lines of the trace of the instrumented copy of `find_double_points` for `a`, by the functions
-- of the model, with the records `ssp0` before it: the records for `a` and the pairs `(a, b)` that
-- pass the sieve, or the skip; and the records after it.
private def traceA (g : SiftGlobals) (wheight : Int) (ssp0 : Array Stype) (a : Int) :
    String × Array Stype := Id.run do
  let (ssp0, through) := (findDoublePointsSetup g true ssp0 a).run
  if !through then
    let n := (List.range g.sievePrimes3).find? fun n ↦
      a.tmod ssp0[n]!.p == 0 && !g.curve.hasInfinity[g.pnn[n]!]!
    return (s!"S {a} {n.getD 0}\n", ssp0)
  let mut log := s!"A {a}" ++ String.join ((ssp0.extract 0 g.sievePrimes3).toList.map fun s ↦
    s!" {s.ap}:{if s.ptr matches .hasInfinity _ then 0 else 1}") ++ "\n"
  let bmax := min (g.check.height / (2 * a)) wheight
  for b in (-bmax)...=bmax do
    if (relprime a b).run && (findDoublePointsSieve g.curve ssp0 g.sievePrimes3 b).run then
      log := log ++ s!"C {a} {b}\n"
  return (log, ssp0)

-- The trace of the instrumented copy of `find_double_points`, for a curve that is not a monic
-- quintic: for each `a`, the records or the skip, and the pairs `(a, b)` that pass the sieve.
private def trace (args : List String) (pnn : List Nat) : String := Id.run do
  let g := globals args pnn
  let wheight := (Double.ofInt g.check.height).sqrt.floor.toInt64.toInt
  let mut ssp0 : Array Stype := .replicate numPrimes {}
  for n in [0:g.sievePrimes3] do
    ssp0 := ssp0.set! n { ssp0[n]! with p := (primeTable[g.pnn[n]!]! : Int) }
  let mut log := ""
  for a in (1 : Int)...=wheight do
    let (l, ssp) := traceA g wheight ssp0 a
    log := log ++ l
    ssp0 := ssp
  return log

-- `row_step(a)` and `unit_a(a)` for `0 ≤ a ≤ 40`: at the primes from `3` to `31`, modulo the
-- primes `3, 5, 11, 13, 19, 29` of which the leading coefficient `2` is not a square, the product
-- beyond the height bound `1000` for `a = 0` and beyond the height bound `20` for `a = 0, 29, 33,
-- 39`; at the primes `11, 3, 5, 7`, beyond `100000` for none; for a monic quintic, `1` and the
-- squares.
#guard
  let steps (args : List String) (pnn : List Nat) : List (Int × Int) :=
    let g := globals args pnn
    (List.range 41).map fun (a : Nat) ↦ ((rowStep g a).run, unitA g.check.curve a)
  [steps ["1 0 0 0 0 0 2", "1000", "-p", "10"] (List.range 10) ==
      [(1001, 0), (1, 1), (1, 2), (3, 3), (1, 4), (5, 5), (3, 6), (1, 7), (1, 8), (3, 9), (5, 10),
        (11, 11), (3, 12), (13, 13), (1, 14), (15, 15), (1, 16), (1, 17), (3, 18), (19, 19),
        (5, 20), (3, 21), (11, 22), (1, 23), (3, 24), (5, 25), (13, 26), (3, 27), (1, 28),
        (29, 29), (15, 30), (1, 31), (1, 32), (33, 33), (1, 34), (5, 35), (3, 36), (1, 37),
        (19, 38), (39, 39), (5, 40)],
    (steps ["1 0 0 0 0 0 2", "20", "-p", "10"] (List.range 10)).map (·.1) ==
      [21, 1, 1, 3, 1, 5, 3, 1, 1, 3, 5, 11, 3, 13, 1, 15, 1, 1, 3, 19, 5, 3, 11, 1, 3, 5, 13, 3,
        1, 21, 15, 1, 1, 21, 1, 5, 3, 1, 19, 21, 5],
    (steps ["1 0 0 0 0 0 2", "100000", "-p", "10"] [3, 0, 1, 2]).take 13 ==
      [(165, 0), (1, 1), (1, 2), (3, 3), (1, 4), (5, 5), (3, 6), (1, 7), (1, 8), (3, 9), (5, 10),
        (11, 11), (3, 12)],
    (steps ["1 178 817 -274 16 1", "1000", "-p", "10"] [3, 0, 1, 2]).take 13 ==
      [(1, 0), (1, 1), (1, 4), (1, 9), (1, 16), (1, 25), (1, 36), (1, 49), (1, 64), (1, 81),
        (1, 100), (1, 121), (1, 144)],
    (steps ["1 0 0 0 0 0 2", "1000", "-p", "10"] []).take 3 == [(1, 0), (1, 1), (1, 2)]].all id

-- `find_double_points` on sextics, with the points of the machine words and beyond (`-a`), `-w`
-- under `-a`, `-1`, a format of `-f`, without sieving primes, on a curve searched reversed, on
-- monic quintics given and made by a negation, and on a monic quintic without double points: the
-- value that it returns, the text that it prints and `total`.
#guard
  let p10 := List.range 10
  ([(["1 0 0 0 0 0 2", "100"], p10, false, "(1, 0, 0, 0)\n", 1),
    (["1 1 -2 -15 13 2 1", "300"], p10, false,
      "(25, -50, 25, 11)\n(4, 0, 0, 9)\n(1, 2, 1, 59)\n", 3),
    (["1 1 -2 -15 13 2 1", "300", "-1"], p10, true, "(25, -50, 25, 11)\n", 1),
    (["1 1 -2 -15 13 2 1", "300", "-a"], [], false,
      "(19321, -193210, 483025, -6633229)\n(1681, -10086, 15129, -122157)\n\
      (25, -50, 25, 11)\n(4, 0, 0, 9)\n(1, 2, 1, 59)\n(1849, 11094, 16641, 8163)\n\
      (177241, 2481374, 8684809, -41587717)\n(198916, -994580, 1243225, -7262824)\n\
      (27556, -82668, 62001, -64656)\n(676, -676, 169, -3832)\n(4, 4, 1, 1568)\n\
      (1069156, 7484092, 13097161, -6656536)\n(7569, -5046, 841, -68637)\n\
      (4761, 3174, 529, 44403)\n(59536, -29768, 3721, -470356)\n\
      (3491628100, -22346419840, 35754271744, -317739167383)\n\
      (380094016, 1045258544, 718615249, 6511204868)\n\
      (2473669696, 9276261360, 8696495025, 35688016836)\n\
      (18788184900, 66802435200, 59379942400, 277426703049)\n\
      (102616900, -61570140, 9235521, -918781632)\n", 20),
    (["4 13 1 -19 -4 0 9", "300", "-f", "[%ld|%ld|%ld|%ld]"], p10, false,
      "[4|-8|4|25][16|0|0|153][1|2|1|-27][4|-4|1|156]", 4),
    (["4 4 -5 7 2 -4 1", "300", "-a", "-w", "1000"], p10, false,
      "(4, -16, 16, 181)\n(1, 0, 0, 6)\n(4, 8, 4, 1)\n(4, 16, 16, -27)\n(25, 200, 400, -266)\n",
      5),
    (["1 -1 0 0 0 1", "1000"], p10, false, "(1, -2, 1, 10)\n(4, 0, 0, 1)\n(1, 2, 1, -2)\n", 3),
    (["1 -1 0 0 0 1", "1000", "-a"], p10, false,
      "(1, -2, 1, 10)\n(4, 0, 0, 1)\n(1, 2, 1, -2)\n(131044, 2096704, 8386816, 16822273)\n\
      (21818241, 33939486, 13198689, -54184598)\n", 5),
    (["16 0 -8 0 0 1", "1000", "-1"], p10, true, "(1, 0, 0, 8)\n", 1),
    (["1 1 -2 -15 13 -1", "1000", "-a"], p10, false,
      "(4, 0, 0, 9)\n(6724, -40344, 60516, 16569)\n", 2),
    (["0 -1 2 -1 3 1 1", "100"], p10, false, "(0, 0, 4, -11)\n", 1),
    (["0 1 0 0 0 1", "1000"], p10, false, "", 0)] :
    List (List String × List Nat × Bool × String × Nat)).all fun (args, pnn, r, t, n) ↦
    doublePoints (args ++ ["-p", "10"]) pnn == (r, t, n)

-- The records, the skips and the pairs that pass the sieve: at the primes from `3` to `31` for a
-- leading coefficient `2`, which is not a square modulo `3, 5, 11, 13, 19, 29`; and at the primes
-- `11, 3, 5, 7` for `3 + 7 x⁶`, which is not a square modulo `7` but for `7 ∣ a`, and whose leading
-- coefficient is not a square modulo `5` and `11`.
#guard trace ["1 0 0 0 0 0 2", "100", "-p", "10"] (List.range 10) ==
  "A 1 1:1 1:1 1:1 1:1 1:1 1:1 1:1 1:1 1:1 1:1\nC 1 0\n\
  A 2 2:1 3:1 4:1 6:1 7:1 9:1 10:1 12:1 15:1 16:1\nS 3 0\n\
  A 4 1:1 4:1 2:1 3:1 10:1 13:1 5:1 6:1 22:1 8:1\nS 5 1\nS 6 0\n\
  A 7 1:1 3:1 0:0 8:1 2:1 5:1 11:1 10:1 25:1 9:1\n\
  A 8 2:1 2:1 1:1 7:1 5:1 15:1 12:1 3:1 11:1 4:1\nS 9 0\nS 10 1\n"
#guard trace ["3 0 0 0 0 0 7", "400", "-p", "10"] [3, 0, 1, 2] ==
  "A 1 1:1 1:1 1:1 1:1\nA 2 6:1 2:1 3:1 4:1\nA 3 4:1 0:0 2:1 5:1\nA 4 3:1 1:1 4:1 2:1\nS 5 2\n\
  A 6 2:1 0:0 1:1 6:1\nA 7 8:1 1:1 3:1 0:0\nC 7 -19\nC 7 -17\nC 7 -16\nC 7 -13\nC 7 -11\n\
  C 7 -9\nC 7 -8\nC 7 -6\nC 7 -3\nC 7 -2\nC 7 2\nC 7 3\nC 7 6\nC 7 8\nC 7 9\nC 7 11\nC 7 13\n\
  C 7 16\nC 7 17\nC 7 19\nA 8 7:1 2:1 2:1 1:1\nA 9 5:1 0:0 4:1 4:1\nS 10 2\nS 11 0\n\
  A 12 1:1 0:0 3:1 3:1\nA 13 6:1 1:1 2:1 6:1\nA 14 4:1 2:1 4:1 0:0\nC 14 -11\nC 14 -1\nC 14 1\n\
  C 14 11\nS 15 2\nA 16 9:1 1:1 1:1 4:1\nA 17 2:1 2:1 3:1 5:1\nA 18 8:1 0:0 2:1 2:1\n\
  A 19 7:1 1:1 4:1 3:1\nS 20 2\n"

end JPoints

end
