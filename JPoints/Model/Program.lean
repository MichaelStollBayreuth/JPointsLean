/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Check
public import JPoints.Model.Choice
public import JPoints.Model.Constants
public import JPoints.Model.DoubleArith
public import JPoints.Model.Input
public import JPoints.Model.Kummer
public import JPoints.Model.Messages
public import JPoints.Model.Printf
public import JPoints.Model.Region
public import JPoints.Model.Rows
public import JPoints.Model.Sample
public import JPoints.Model.Search
public import JPoints.Model.Sift
public import JPoints.Model.Tables
public import JPoints.Model.TwoAdic
public import JPoints.Model.Walk

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Choice
meta import JPoints.Model.Input
meta import JPoints.Model.Messages
meta import JPoints.Model.Region
meta import JPoints.Model.Sample
meta import JPoints.Model.Search

/-!
# The search and the program

The search of `j-points` and its `main`. `find_points` (`JPoints.findPoints`) makes the choice of
the sieve and the tables of the sieving primes (`init_fmodpsquare`, `init_sieve`), stops when a
prime of rate `0` leaves no point (message 1), sets up the sieve (`init_sift`), checks the points
over `(0, 0, 1)` when the leading coefficient of the curve searched is a square
(`JPoints.findPointsOrigin`) and the double points (`JPoints.findDoublePoints`), and runs the main
search over the units of work, the first coordinates `a` (`JPoints.findPointsUnits`,
`JPoints.runUnits`): for each `a`, `run_a` (`JPoints.runA`) sieves the rows `(a, b)` that the
primes without points at infinity leave (`JPoints.rowStep`) and the condition at 2 leaves, by bands
in the tube or the real region (`JPoints.siftBands`) or row by row in the box (`JPoints.sift`), and
the run stops at the first point found when one point is enough (`-1`). `main`
(`JPoints.Program.run`) reads the command line (`JPoints.Cli.readInput`, or the constants of the
cost model under `-c list`, `JPoints.Program.mainCostList`), prints the head of the report
(`JPoints.Program.mainHead`), and makes the search (`JPoints.Program.mainSearch`): the curve
searched (`JPoints.normalizeCurve`), the masks of the ends of a row (`JPoints.Program.mainMasks`),
the size of the bit array in words (`JPoints.Program.mainArraySize`), the Kummer surface
(`JPoints.kummerInit`), the analysis of the plane of `(b, c)` and its sample (`JPoints.tubeInit`),
the condition at 2 from the height bound `500` on (`JPoints.twoadicInit`), `find_points`, and the
numbers of the survivors and of the points (messages 12 and 2). `JPoints.Program.main` is the
program `j-points-model`: it writes the text of `JPoints.Program.run` and exits with its status.

## Main definitions

* `JPoints.SearchGlobals`: what `find_points` reads from the globals of the program.
* `JPoints.runA`: the rows of a first coordinate.
* `JPoints.runUnits`: the units of work of the main search.
* `JPoints.findPointsSetup`, `JPoints.findPointsOrigin`, `JPoints.findPointsUnits`,
  `JPoints.findPoints`: the search.
* `JPoints.Program.mainCostList`, `JPoints.Program.mainHead`, `JPoints.Program.mainMasks`,
  `JPoints.Program.mainArraySize`, `JPoints.Program.mainSearch`: the parts of `main`.
* `JPoints.Program.formatRefusal`: the refusal of a format of `-f` that the model does not admit.
* `JPoints.Program.run`: `main`, the text on the standard output and the exit status.
* `JPoints.Program.main`: the program `j-points-model`.

## Implementation notes

The globals of the program are the fields of the structures of the model, which `main` computes in
the order of the C code and passes on: the tables of `init_main` (`JPoints.Tables`), the globals of
the command line (`JPoints.Cli.Input`), the curve searched (`JPoints.SearchCurve`), what the exact
check reads (`JPoints.CheckGlobals`), the analysis of the plane of `(b, c)` (`JPoints.TubeCoeffs`,
`JPoints.NegativeIntervals`, `JPoints.TubeStats`, the static data `JPoints.SiftData` and the state
`JPoints.TubeState` that `tube_sample` leaves), the condition at 2 (`JPoints.TwoAdic`), the plan of
the sieve (`JPoints.Plan`); then `find_points` makes the tables of the curve, the records of the
primes, the sieve tables, the globals of the sieve (`JPoints.SiftGlobals`, `JPoints.BandGlobals`),
and the state of the one thread (`JPoints.SiftState`), which takes over the state of the analysis
that `tube_sample` leaves, as the thread of a run without `-t` does. The text that the program
prints on the standard output is collected in the order of the calls, with the points in the output
of the thread (`JPoints.Output`), and written at the end (`JPoints.Program.main`). The units of work
run in turn on one thread, whatever the number of threads of `-t`, whose output the threads of
`j-points` reproduce when the system lets them all start (otherwise `j-points` exits with error 8 or
7 after part of the points).

The model prints the points under the formats of `-f` whose conversions are all
`%[flags][width][.precision]ld`, at most four of them, and `%%` (`JPoints.Printf.parseFormat`),
the formats that `printf` and `gmp_printf` print as the model does; it refuses any other format
after the command line is read, with a message of its own and the exit status 11
(`JPoints.Program.formatRefusal`), where `j-points` passes it to `printf` as it is.
-/

@[expose] public section

namespace JPoints

/-! ### The globals of the search -/

/-- What `find_points` reads from the globals of `j-points`, besides the plan of the sieve, the
static data of the sieve and the state of the analysis of the tube, which it takes and passes on:
the tables of `init_main` (`tables`); the globals of the choice of the primes (`choice`: the
command line, the curve searched, the number of the intervals on which `f` is negative, the
statistics of the analysis and the condition at 2); what the exact check reads (`check`); the
intervals on which `f` is negative (`neg`) and the coefficients of the analysis of the tube (`kd`),
which the sieve by bands reads; the size `array_size` of the bit array in words; and the masks
`begmask` and `endmask` of the ends of a row, which `main` sets.

It models no C code of its own: it gathers globals that other structures hold. -/
structure SearchGlobals where
  /-- The tables of `init_main`. -/
  tables : Tables
  /-- The globals of the choice of the primes. -/
  choice : ChoiceGlobals
  /-- What the exact check reads from the globals. -/
  check : CheckGlobals
  /-- `num_neg` and the ends of the intervals on which `f` is negative. -/
  neg : NegativeIntervals
  /-- The coefficients of the Kummer surface and of the curve as doubles. -/
  kd : TubeCoeffs
  /-- `array_size`, the number of the words of the bit array. -/
  arraySize : Nat
  /-- `begmask`, the bits of the first word of a row that lie in the row. -/
  begmask : UInt64
  /-- `endmask`, the bits of the last word of a row that lie in the row. -/
  endmask : UInt64

/-! ### The rows of a first coordinate and the units of work -/

/-- `run_a`, the rows of the first coordinate `a ≥ 0` in the state `s`: the step `m` of `b`
(`JPoints.rowStep`), which leaves the rows `(a, b)` with `m ∣ b`, from `b₀ = m` for `a = 0` and
from `b₀ = -⌊H / m⌋ m` otherwise, up to the height bound `H`; the rows sieved by bands
(`JPoints.siftBands`) in the tube or the real region (`sieve_mode ≠ 0`), and otherwise each row
`(a, b)` sieved in the box (`JPoints.sift`), but for those of `a ≠ 0` whose class modulo `64` the
condition at 2 empties when it is used, until a point is found when one point is enough (`-1`).
Whether it stopped so, and the state.

C: `j-points.c:1330-1335`, `j-points.c:1339-1343`

Deviation: the state taken and returned, for the thread-local globals; the globals and the static
data that it reads passed; integers for the `long`s, with `Int.tdiv` for C's `/` on the positive
`height` and `m`; the loop `for(b = b0; b <= height; b += m)` over `b = b₀ + k m` for
`k < (H - b₀) / m + 1`, with Lean's `/`, which rounds down, none when `b₀ > H`; `a % 64` and
`b % 64`, in `[0, 64)`, for `a & 63` and `b & 63`, the same in two's complement, and the entry
`(a & 63) * 64 + (b & 63)` of the flat array `alive2`; a Boolean for the `int` returned. -/
def runA (g : BandGlobals) (sd : SiftData) (s : SiftState) (a : Int) : Id (Bool × SiftState) := do
  let height := g.sift.check.height
  let m ← rowStep g.sift a
  let b0 := if a == 0 then m else -(height.tdiv m) * m
  if g.sieveMode != 0 then return ← siftBands g sd s a b0 m
  let two := g.sift.twoAdic
  let mut s := s
  for k in [0:((height - b0) / m + 1).toNat] do
    let b := b0 + k * m
    if two.use2 && a != 0 && !two.alive2[(a % 64).toNat * 64 + (b % 64).toNat]! then continue
    let (found, s') ← sift g.sift sd s a b
    s := s'
    if found && g.sift.check.onePoint then return (true, s)
  return (false, s)

/-- `run_units`, the main search over the units of work `k < units` in the state `s`: the rows of
the first coordinate of each unit (`JPoints.unitA`, `JPoints.runA`), in order, until a point is
found when one point is enough (`-1`); then the totals, the counters of the survivors and of the
points of the one thread. The totals, and the state.

C: `j-points.c:1385-1386`, `j-points.c:1396-1403`, `j-points.c:1414`

Deviation: the arm of one thread for every number of threads of `-t` (the threads are not modelled,
and print the points in the order of the units, as this arm does, when the system lets them all
start: when it refuses a thread or the memory for them, `j-points` exits with error 8 or 7 after
part of the points, which depends on the limits of the machine; `j-points.c:1387-1395`, the bound of
the number of threads by the number of units and the points collected for the threads, and
`j-points.c:1404-1413` are excluded), so that the test `num_threads == 1` is left out; the state
taken and returned, for the thread-local globals, and the totals returned, for the globals; the
globals and the static data that it reads passed; the loop over `k < units` as a loop over the
natural numbers below `units.toNat`, `units` being nonnegative; natural numbers for the counters and
the totals. -/
def runUnits (g : BandGlobals) (sd : SiftData) (s : SiftState) (units : Int) :
    Id (Totals × SiftState) := do
  let mut s := s
  for k in [0:units.toNat] do
    let (found, s') ← runA g sd s (unitA g.sift.check.curve k)
    s := s'
    if found && g.sift.check.onePoint then break
  return ({ totSurv1 := s.numSurv1, totSurv2 := s.numSurv2, totSurv3 := s.numSurv3
            totPoints := s.out.total }, s)

/-! ### The search -/

/-- The set-up of the search of `find_points` for the globals `g`, from the plan `plan` and the
static data `sd` of the sieve that `tube_init` leaves, after the output `out`: the tables of the
curve, the records of the primes sorted by rate, the choice of the sieve and its messages
(`JPoints.initFmodpsquare`); the sieve tables of the first two stages (`JPoints.initSieve`); the
end of the search when there are sieving primes and the best rate is `0`, with message 1 unless
`-q` is given; the box and the condition at 2 not used when there are no sieving primes; and the
static data of the sieve (`JPoints.initSift`). The globals of the sieve by bands
(`JPoints.BandGlobals`) and the static data, or `none` when the search ends here, and the output.

C: `j-points.c:1295`, `j-points.c:1297-1300`, `j-points.c:1302`

Deviation: the globals that it writes returned, the tables of the curve and the records of the
primes from their initial values, which nothing writes before `init_fmodpsquare`; `none` for the
return of `find_points`; the comparison `prec[0].r == 0.0` by `JPoints.Double.beq`; the output
taken and returned, for `stdout`. -/
def findPointsSetup (g : SearchGlobals) (plan : Plan) (sd : SiftData) (out : Output) :
    Id (Option (BandGlobals × SiftData) × Output) := do
  let (ct, prec, plan, text) ←
    initFmodpsquare g.tables g.choice CurveTables.initial (.replicate numPrimes {}) plan
  let out := out.print text
  let sieve ← initSieve g.tables ct plan.pnn plan.sievePrimes2 SieveTables.initial
  if plan.sievePrimes3 > 0 && prec[0]!.r.beq .zero then
    if g.choice.input.quiet then return (none, out)
    return (none, out.print (← message { choice := g.choice, plan, prec } 1 0))
  let (plan, two) := if plan.sievePrimes3 == 0 then
      ({ plan with sieveMode := 0 }, { g.choice.two with use2 := false })
    else (plan, g.choice.two)
  let sg : SiftGlobals :=
    { tables := g.tables, curve := ct, sieve, check := g.check, arraySize := g.arraySize
      twoAdic := two, pnn := plan.pnn, sievePrimes1 := plan.sievePrimes1
      sievePrimes2 := plan.sievePrimes2, sievePrimes3 := plan.sievePrimes3, begmask := g.begmask
      endmask := g.endmask }
  let bg : BandGlobals :=
    { sift := sg, sieveMode := plan.sieveMode, tubeCut := plan.tubeCut, neg := g.neg, kd := g.kd }
  return (some (bg, ← initSift sg sd), out)

/-- The points over `(0, 0, 1)` that `find_points` checks for the globals `g` of the exact check,
after the output `out`: when the curve searched is a sextic whose leading coefficient `f₆` is a
square (`JPoints.mpzPerfectSquareP`), so that it has points at infinity, the root
`d = (f₅² - 4 f₆ f₄) / (4 f₆)` of the Kummer equation over `(0, 0, 1)`, checked by
`JPoints.checkOnePointFinal`. Whether a point was found and one point is enough (`-1`), when
`find_points` returns, and the output with the point.

C: `j-points.c:1304-1310`

Deviation: integers for the GMP integers `fff`, `tmp` and `tmp2`, locals for the thread-local
scratch integers; a Boolean for the return of `find_points`; the output taken and returned, for the
thread-local counter `total` and `stdout`. -/
def findPointsOrigin (g : CheckGlobals) (out : Output) : Id (Bool × Output) := do
  let cs := g.curve.coeffs
  if g.curve.degree == 6 && mpzPerfectSquareP cs[6]! then
    let fff := cs[5]! * cs[5]!
    let tmp := cs[6]! * 4
    let tmp2 := tmp * cs[4]!
    let fff := fff - tmp2
    let (found, out) ← checkOnePointFinal g out 0 0 1 fff tmp
    return (found && g.onePoint, out)
  return (false, out)

/-- The number of the units of work of the main search of `find_points`, for the curve searched
`curve` and the height bound `H`: `⌊√H⌋ + 1` for a monic quintic, whose units are the squares
`k²` (`JPoints.unitA`), as `floor(sqrt(height))` computes it in doubles, and `H + 1` otherwise,
then lowered while the first coordinate of the last unit exceeds `H`.

C: `j-points.c:1314-1316`

Deviation: an integer for the `long` `units`; `⌊√H⌋` by the doubles of
`JPoints.Model.DoubleArith`, the exact conversion of `height`, `sqrt` and `floor`, and the
conversion back to a `long`, which truncates (`JPoints.Double.toInt64`); the test `mpz_cmp_si` of
`f₅` with `1` as the equality of integers. -/
def findPointsUnits (curve : SearchCurve) (height : Int) : Id Int := do
  let mut units := if curve.degree == 5 && curve.coeffs[5]! == 1 then
      (Double.ofInt height).sqrt.floor.toInt64.toInt + 1
    else height + 1
  while units > 0 && unitA curve (units - 1) > height do units := units - 1
  return units

/-- `find_points`, the search of `j-points` for the globals `g`, from the plan `plan`, the static
data `sd` of the sieve and the state `t` of the analysis of the tube that `tube_init` leaves, after
the output `out`: the set-up (`JPoints.findPointsSetup`), the points over `(0, 0, 1)`
(`JPoints.findPointsOrigin`), the double points (`JPoints.findDoublePoints`), each ending the search
when it finds a point and one point is enough (`-1`), and the main search over the units of work
(`JPoints.findPointsUnits`, `JPoints.runUnits`) in the state of the one thread, which takes over the
state `t`. The totals of the counters, their initial values when the search ends before the main
search, and the output with the messages of the choice and the points.

C: `j-points.c:1291-1292`, `j-points.c:1312`, `j-points.c:1317-1320`

Deviation: the totals returned, for the globals that `run_units` sets; the globals, the static data
and the state passed; the output taken and returned, for the thread-local counter `total` and
`stdout`; the state of the thread from `JPoints.SiftState.initial` with the state of the analysis
`t` and the output, for the thread-local globals, whose bit array and bands `init_sift` allocates
anew, and which nothing reads before it writes them. -/
def findPoints (g : SearchGlobals) (plan : Plan) (sd : SiftData) (t : TubeState) (out : Output) :
    Id (Totals × Output) := do
  let (setup, out) ← findPointsSetup g plan sd out
  let some (bg, sd) := setup | return ({}, out)
  let (stop, out) ← findPointsOrigin g.check out
  if stop then return ({}, out)
  let (found, out) ← findDoublePoints bg.sift out
  if found && g.check.onePoint then return ({}, out)
  let units ← findPointsUnits g.check.curve g.check.height
  let (totals, s) ← runUnits bg sd { SiftState.initial g.arraySize with tube := t, out } units
  return (totals, s.out)

/-! ### `main` -/

namespace Program

/-- What `main` prints under `-c list`: for each constant of the cost model, in the order of
`cost_names`, its name and the value in force, the constants `costs`, printed by `%g`
(`JPoints.Double.printGeneral`), on a line of its own.

C: `j-points.c:345-347`

Deviation: the text returned, for the output on `stdout`; the constants in force passed, for the
statics; a natural number for the `size_t` index; the values by `JPoints.Double.ofFloat`, which
takes a NaN to `0x7ff8000000000000` and would print `nan` for `-nan` (the defaults of the build are
positive numbers). -/
def mainCostList (costs : Cli.Costs) : Id String := do
  let mut out := ""
  for k in [0:Cli.numCosts] do
    let e := Cli.costNames[k]!
    out := out ++ s!"{e.name} {Double.printGeneral 6 (.ofFloat (e.value costs))}\n"
  return out

/-- The head of the report that `main` prints for the globals `input` that `read_input` leaves,
unless `-q` is given: the banner (message 0), the curve given (message 5, with its degree), the
height bound with the bound on the fourth coordinate (message 6) and message 3, which prints
nothing (`JPoints.message`).

C: `j-points.c:353-358`

Deviation: the text returned, for the output on `stdout`; the globals of `message` gathered from
`input`, with the curve given as the curve of `JPoints.ChoiceGlobals` (the global `coeffs` before
`normalise_curve`, which message 5 prints), and the initial values of the statistics of the
analysis, of `num_neg` and of the condition at 2, which no message here reads. -/
def mainHead (input : Cli.Input) : Id String := do
  if input.quiet then return ""
  let curve : SearchCurve :=
    { coeffs := input.coeffs, degree := input.degree.toNat, reversed := false, negated := false }
  let g : MessageGlobals :=
    { choice := { input, curve, numNeg := 0, stats := {}, two := TwoAdic.initial } }
  return (← message g 0 0) ++ (← message g 5 input.degree) ++ (← message g 6 input.height) ++
    (← message g 3 0)

/-- `begmask` and `endmask` as `main` sets them for the height bound `H`: the bits `j` of the first
word of a row with `j ≥ (-H) mod 64`, `(~0UL) << ((-height) & 63)`, and the bits `j` of its last
word with `j ≤ H mod 64`, `(~0UL) >> ((~height) & 63)`.

C: `j-points.c:360-361`

Deviation: `UInt64`s for the `unsigned long`s; the integers `(-H) % 64` and `(-H - 1) % 64`, in
`[0, 64)`, for `(-height) & LONG_MASK` and `(~height) & LONG_MASK` on the `long` `height`, the same
in two's complement. -/
def mainMasks (height : Int) : UInt64 × UInt64 :=
  ((~~~0 : UInt64) <<< ((-height) % longLength).toNat.toUInt64,
    (~~~0 : UInt64) >>> ((-height - 1) % longLength).toNat.toUInt64)

/-- The size `array_size` of the bit array in words, as `main` converts it from the kilobytes `kb`
of `-s` (or the default) for the height bound `H`: `kb · 2 ^ (13 - LONG_SHIFT)`, the words of `kb`
kilobytes, unless `kb > s >> (13 - LONG_SHIFT)` for `s = 2 ⌈(H + 1) / 64⌉`, more words than a row
has, and then `s` (the comparison is made before the shift, so that the shift cannot overflow).

C: `j-points.c:338`, `j-points.c:362`, `j-points.c:365`

Deviation: integers for the `long`s; `JPoints.ceilDiv` for the macro `CEIL`; `>>>` for C's `>>` on
the positive `s`, and the product with `2 ^ (13 - LONG_SHIFT)` for the shift `<<` of the positive
`array_size`, which does not overflow when `array_size ≤ s >> (13 - LONG_SHIFT)`. -/
def mainArraySize (height kb : Int) : Int :=
  let s := 2 * ceilDiv (height + 1) longLength
  if kb > s >>> (13 - longShift) then s else kb * 2 ^ (13 - longShift)

/-- The search of `main` for the tables `t` of `init_main` and the globals `input` that `read_input`
leaves: the curve searched and the message of the transformation (`JPoints.normalizeCurve`), the
masks of the ends of a row (`JPoints.Program.mainMasks`), the size of the bit array in words
(`JPoints.Program.mainArraySize`), the Kummer surface (`JPoints.kummerInit`), the analysis of the
plane of `(b, c)` and its sample (`JPoints.tubeInit`), the condition at 2 when `H ≥ 500`
(`JPoints.twoadicInit`), the search (`JPoints.findPoints`), and unless `-q` is given the numbers of
the survivors of the stages and of the points found (messages 12 and 2, `JPoints.message`). The
text printed.

C: `j-points.c:359`, `j-points.c:367-368`, `j-points.c:370`, `j-points.c:372-373`

Deviation: the text returned, for the output on `stdout`; the globals computed in the order of the C
code and passed, for the globals that the functions read and write, the plan, the static data of the
sieve and the state of the analysis from their initial values; the words of the bit array in
`JPoints.SearchGlobals.arraySize`, a natural number, for the global `array_size` that `main`
overwrites with them, while `JPoints.Cli.Input.arraySize` keeps the kilobytes, which nothing reads
after the conversion; the globals of `message` for messages 12 and 2 with the totals, which they
print, and the initial values of the plan and of the records, which they do not read. -/
def mainSearch (t : Tables) (input : Cli.Input) : Id String := do
  let (curve, text) ← normalizeCurve input.coeffs input.degree.toNat input.quiet
  let (begmask, endmask) := mainMasks input.height
  let arraySize := (mainArraySize input.height input.arraySize).toNat
  let kummer := kummerInit curve.coeffs
  let check : CheckGlobals :=
    { curve, kummer, height := input.height, dbound := input.dbound, dbounded := input.dbounded
      allPoints := input.allPoints, onePoint := input.onePoint, printFormat := input.printFormat }
  let (kd, plan, neg, sd, tube, stats) ← tubeInit check {} SiftData.initial TubeState.initial
  let two ← if input.height ≥ 500 then twoadicInit curve.coeffs kummer TwoAdic.initial
    else pure TwoAdic.initial
  let choice : ChoiceGlobals := { input, curve, numNeg := neg.numNeg, stats, two }
  let g : SearchGlobals := { tables := t, choice, check, neg, kd, arraySize, begmask, endmask }
  let (totals, out) ← findPoints g plan sd tube { text }
  if input.quiet then return out.text
  let mg : MessageGlobals := { choice, totals }
  return out.text ++ (← message mg 12 0) ++ (← message mg 2 0)

/-- The message with which the program refuses a format of `-f` that it does not admit
(`JPoints.Printf.parseFormat`), before it prints anything else, with the exit status 11.

It models no C code: `j-points` passes any format to `printf`. -/
def formatRefusal : String :=
  "\nThe format of -f may have only %ld conversions (with flags, width and precision), " ++
    "at most four,\nand %%.\n\n"

/-- `main` of `j-points`, on the command line `args` (the words after the name of the program):
the text that it prints on the standard output and its exit status. The tables of `init_main`
(`JPoints.initMain`); under `-c list` alone, the constants of the cost model in force, their
defaults (`JPoints.Program.mainCostList`), and the status 0; with fewer than two words, error 2;
otherwise the command line read (`JPoints.Cli.readInput`), on an error its message and its status
(`JPoints.Cli.Failure.message`, `JPoints.Cli.Failure.status`); a format of `-f` that the model does
not admit refused (`JPoints.Program.formatRefusal`, the status 11); then the head of the report
(`JPoints.Program.mainHead`) and the search (`JPoints.Program.mainSearch`), and the status 0.

C: `j-points.c:336-337`, `j-points.c:341`, `j-points.c:344`, `j-points.c:348-349`,
`j-points.c:351-352`, `j-points.c:374-375`

Deviation: the text returned, which `JPoints.Program.main` writes at the end, where `j-points`
prints as it goes; the exit through `error` as the text and the status returned; the words after
the name of the program for `argv`, `args.length + 1` for `argc`, and the comparisons of
`strcmp` as the equality of strings; the refusal of the formats of `-f` that the model does not
admit, a decision of the project, after the command line is read and before any message (the
formats that it admits are those that `printf` and `gmp_printf` print as the model does); the
words of the command line as the Lean runtime makes strings of them, which replaces the bytes that
are not valid UTF-8 by the character U+FFFD, where `j-points` reads the bytes as they are. -/
def run (args : List String) : String × UInt32 := Id.run do
  let t ← initMain Tables.initial
  let init : Cli.Input := {}
  if args == ["-c", "list"] then return (← mainCostList init.costs, 0)
  if args.length < 2 then
    return (← Cli.Failure.tooFewArguments.message, Cli.Failure.tooFewArguments.status)
  match ← Cli.readInput args.toArray with
  | .error f => return (← f.message, f.status)
  | .ok input =>
    if (Printf.parseFormat 'l' input.printFormat).isNone then return (formatRefusal, 11)
    return ((← mainHead input) ++ (← mainSearch t input), 0)

/-- The program `j-points-model`: it prints the text of `JPoints.Program.run` on the standard
output, in one write once it is computed, and exits with its status. Like `j-points`, it ignores a
failed write, but for one case: when the reader of the output is gone, the write fails with
`IO.Error.resourceVanished`, since the Lean runtime ignores the signal `SIGPIPE` that ends
`j-points` then, and the program exits quietly with the status 141 that the shell reports for
`j-points` (where `SIGPIPE` has its default action). It flushes the standard output itself, since
a short output waits in the buffer of the C library until the exit, where a failed write goes
unnoticed. -/
def main (args : List String) : IO UInt32 := do
  let (out, status) := run args
  let stdout ← IO.getStdout
  try
    stdout.putStr out
    stdout.flush
  catch
    | .resourceVanished .. => return 141
    | _ => pure ()
  return status

/-! ### Examples

The text and the exit status of `j-points` at the pin on the command lines given, and the values of
the lines of its `main` that set the masks and the size of the bit array. No example prints
what depends on the values of `log` and `pow` of the C library, which differ between processors:
the messages of the choice of the sieve and the numbers of the survivors are left out by `-q`, or
the output is compared before and after them. -/

-- The constants of the cost model under `-c list`; the errors 2, 3, 4, 6 and 10, also after a
-- format that the model refuses, which it refuses only once the command line is read; a third
-- word after `-c list`, which makes the words a command line.
#guard run ["-c", "list"] ==
  ("AND 0.63\nSIZE 756\nWORD 56\nTEST2 5.6\nBIT 30\nROW3 40\nTEST3 15\nEXACT 1300\nROW 300\n\
    CELL 320\nTWORD 12\nTTEST 2\nTROW 45\nRROW 40\nREXCL 15\nRCUT 30\nRANGE 20\nPASS 5\n\
    TABLE 13\nINIT 110\n", 0)
#guard
  let height := "\nIncorrect height argument.\n  Height must be in [1, 3037000499].\n\n"
  [run [] == ("\n" ++ Cli.usage, 2), run ["-c"] == ("\n" ++ Cli.usage, 2),
    run ["-c", "list", "5"] == ("\nToo many coefficients.\n\n", 3),
    run ["1 2 3 4 5 6 7 8", "100"] == ("\nToo many coefficients.\n\n", 3),
    run ["1 2 3 4 5 6 7", "0"] == (height, 4),
    run ["1 2 3 4 5 6 7", "abc", "-f", "%s"] == (height, 4),
    run ["1 2 3 4 5 6 7", "10", "-f", "%d", "-x"] ==
      ("\nWrong syntax for optional arguments:\n\n\n" ++ Cli.usage, 6),
    run ["1 2 3 4 5 6 7", "10", "-c", "FOO=1"] ==
      ("\nThe argument of -c must be NAME=value, or several of them separated\n\
      by commas, with a positive value and one of the names\n AND SIZE WORD TEST2 BIT ROW3 TEST3 \
      EXACT ROW CELL TWORD TTEST TROW RROW REXCL RCUT RANGE PASS TABLE INIT.\n\n", 10)].all id

-- `begmask`, `endmask` and `array_size` in words for the kilobytes `1`, `2`, `10`, `100` and
-- `2 ^ 63 - 1` of `-s`, at height bounds around the multiples of `64` and at `MAX_HEIGHT`, from a
-- test program with the lines of `main`.
#guard ([(1, 0x8000000000000000, 0x3, [2, 2, 2, 2, 2]),
    (2, 0xc000000000000000, 0x7, [2, 2, 2, 2, 2]),
    (30, 0xfffffffc00000000, 0x7fffffff, [2, 2, 2, 2, 2]),
    (63, 0xfffffffffffffffe, 0xffffffffffffffff, [2, 2, 2, 2, 2]),
    (64, 0xffffffffffffffff, 0x1, [4, 4, 4, 4, 4]), (65, 0x8000000000000000, 0x3, [4, 4, 4, 4, 4]),
    (100, 0xfffffffff0000000, 0x1fffffffff, [4, 4, 4, 4, 4]),
    (127, 0xfffffffffffffffe, 0xffffffffffffffff, [4, 4, 4, 4, 4]),
    (128, 0xffffffffffffffff, 0x1, [6, 6, 6, 6, 6]),
    (1000, 0xffffffffff000000, 0x1ffffffffff, [32, 32, 32, 32, 32]),
    (3037000499, 0xffffffffffffe000, 0xfffffffffffff, [128, 256, 1280, 12800, 94906266])] :
    List (Int × UInt64 × UInt64 × List Int)).all fun (h, b, e, sizes) ↦
  mainMasks h == (b, e) &&
    [1, 2, 10, 100, 9223372036854775807].map (mainArraySize h ·) == sizes

-- The formats of `-f` that the model refuses: a conversion other than `%ld`, five conversions, a
-- `%` at the end, a field beyond `JPoints.Printf.maxField`.
#guard ["%d", "%s %ld", "%ld %ld %ld %ld %ld", "%ld %", "%lld", "%4096ld", "%l%ld"].all fun f ↦
  run ["1 2 3 4 5 6 7", "10", "-f", f] == (formatRefusal, 11) &&
    run ["1 2 3 4 5 6 7", "10", "-q", "-f", f] == (formatRefusal, 11)

-- The points of searches: a monic sextic in the tube, with a format of `-f`; the same with `-a`;
-- a monic quintic, whose first coordinates are squares; a sextic with `f₀ = 0` and `f₁ = -1`,
-- searched reversed and negated.
#guard run ["21 116 171 128 55 12 1", "30", "-q", "-f", "[%ld:%ld:%ld:%ld]"] ==
  ("[0:0:1:-19][0:1:-2:26][1:-6:-1:-24][1:-4:-3:28]", 0)
#guard run ["21 116 171 128 55 12 1", "20", "-q", "-a"] ==
  ("(0, 0, 1, -19)\n(1, -4, 4, -91)\n(0, 1, -2, 38)\n(0, 1, -2, 26)\n(1, -12, 17, -300)\n\
    (1, -6, -1, -24)\n(1, -6, 7, -136)\n(1, -4, -3, 28)\n(1, -4, 1, -44)\n(1, -4, 5, -116)\n\
    (1, -2, -5, 64)\n(1, -2, 3, -112)\n(3, -14, 3, -117)\n(3, -6, 1, -160)\n(5, -14, 3, -232)\n", 0)
#guard run ["1 178 817 -274 16 1", "100", "-q"] ==
  ("(0, 1, -9, 81)\n(0, 1, -6, 36)\n(0, 1, -2, 4)\n(0, 1, 0, 0)\n(0, 1, 4, 16)\n(1, -17, 0, -2)\n\
    (1, -9, 0, -6)\n(1, -6, 0, -12)\n(1, -2, 0, -52)\n(1, 4, -6, -40)\n(1, 4, 0, 40)\n\
    (1, 6, -2, 32)\n(1, 8, 2, -24)\n(1, 8, 10, -72)\n(1, 30, -6, 48)\n(9, 10, -56, -89)\n\
    (9, 70, 4, 76)\n", 0)
#guard run ["0 -1 2 -1 3 1 1", "60", "-q"] == ("(0, 0, 4, -11)\n(0, 1, 0, 0)\n", 0)

-- A report under `-1`, which stops at the point over `(0, 0, 1)` before the main search, so that
-- the totals keep their initial values `0`: the head before the messages of the choice, and the
-- end after them.
#guard
  let (out, status) := run ["1 1 -2 -15 13 2 1", "30", "-1"]
  status == 0 &&
  out.startsWith "\nThis is j-points-3.0.1 by Michael Stoll (2026-10-30).\n\n\
    Please acknowledge use of the program in published work.\n\n\n\
    y^2 = x^6 + 2 x^5 + 13 x^4 - 15 x^3 - 2 x^2 + x + 1\n\nmax. Height = 30\n" &&
  out.endsWith "\n(0, 0, 1, -12)\n\n0 candidates survived the first stage,\n\
    0 candidates survived the second stage,\n0 candidates survived the third stage.\n\n\
    Found 0 rational points on K lifting to J.\n"

end Program

end JPoints

end
