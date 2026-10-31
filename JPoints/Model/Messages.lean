/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Choice
public import JPoints.Model.Constants
public import JPoints.Model.Printf

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.Choice

/-!
# The messages of `j-points`

`message` of `j-points.c` (`JPoints.message`) prints, unless `-q` is given, the messages of a run
by their numbers: `0` the banner of the version, `5` the curve given and `6` the height bound with
the bound on the fourth coordinate, which `main` prints first; `4`, `7` and `8` the choice of the
sieve, which `init_fmodpsquare` prints (`JPoints.message4`, `JPoints.message7`,
`JPoints.message8`); `1` the end of a search that a prime of rate `0` makes empty, which
`find_points` prints; and `12` the numbers of the survivors of the three stages of the sieve and
`2` the number of the points found, which `main` prints last. A number without a message prints
nothing. The totals of the counters of the threads that messages `12` and `2` print are
`JPoints.Totals`.

## Main definitions

* `JPoints.Totals`: the totals of the counters of the survivors and of the points.
* `JPoints.MessageGlobals`: what `message` reads from the globals.
* `JPoints.message`: the text of a message.

## Implementation notes

`message` reads globals of the whole program, which the structures of the model hold: the command
line (`JPoints.Cli.Input`), the curve (`JPoints.SearchCurve`), the statistics of the analysis and
the condition at 2 (in `JPoints.ChoiceGlobals`), the plan of the sieve (`JPoints.Plan`), the records
of the primes (`JPoints.Entry`) and the totals; they are gathered in `JPoints.MessageGlobals`, whose
defaults for the plan, the records and the totals are the values of the globals before the choice
of the sieve and the search set them. Message `5` prints the global `coeffs`, the coefficients of
the curve that the program holds at the call, which are those that `read_input` leaves until
`normalise_curve` replaces them by those of the curve searched: the curve of the
`JPoints.ChoiceGlobals`, which the caller sets to the curve given before `normalise_curve`. The
text that a message prints is returned; the program writes the texts in the order of the calls.
-/

@[expose] public section

namespace JPoints

/-! ### The totals -/

/-- The totals `tot_surv1`, `tot_surv2` and `tot_surv3` of the counters of the survivors of the
first, the second and the third stage of the sieve, and the total `tot_points` of the counters of
the points found, over the threads, which messages `12` and `2` print. The defaults are the
initial values.

C: `j-points.c:285`

Deviation: a structure for the globals; natural numbers for the `long` sums of the counters, which
count up from `0`. -/
structure Totals where
  /-- `tot_surv1`, the survivors of the first stage. -/
  totSurv1 : Nat := 0
  /-- `tot_surv2`, the survivors of the second stage. -/
  totSurv2 : Nat := 0
  /-- `tot_surv3`, the survivors of the third stage. -/
  totSurv3 : Nat := 0
  /-- `tot_points`, the points found. -/
  totPoints : Nat := 0
  deriving DecidableEq, Repr

/-! ### The messages -/

/-- What `message` reads from the globals of `j-points`: the globals of the choice (`choice`: the
command line, the curve, the statistics of the analysis and the condition at 2), the plan of the
sieve (`plan`), the records of the primes considered, sorted by rate (`prec`), and the totals of
the counters (`totals`). The defaults are the values of the globals before `init_fmodpsquare` and
the search set them.

It models no C code of its own: it gathers globals that other structures hold. -/
structure MessageGlobals where
  /-- The globals of the choice: the command line, the curve, the statistics of the analysis and
  the condition at 2. -/
  choice : ChoiceGlobals
  /-- The plan of the sieve: `pnn`, `sieve_primes1`, `sieve_primes2`, `sieve_primes3`,
  `sieve_mode` and `tube_cut`. -/
  plan : Plan := {}
  /-- `prec`, the records of the primes. -/
  prec : Array Entry := .replicate numPrimes {}
  /-- The totals of the counters. -/
  totals : Totals := {}

/-- `message(n, total)`, the text of message `n` for the globals `g`: `0` the banner of the version
after a blank line; `1` that the rate `0` of a prime leaves no point; `2` the number of the points
found (`tot_points`); `4` the mode of the sieve, the condition at 2, the numbers of the primes of
the stages and the constants that `-c` set (`JPoints.message4`); `5` the polynomial of the global
`coeffs` of degree at most `total` (`JPoints.Printf.printPoly`) after `y^2 = `; `6` the height
bound `total` and, when the fourth coordinate is bounded by a `dbound` other than the height bound,
`dbound`; `7` the sieving primes of the stages (`JPoints.message7`); `8` the rates of the best
prime, of the last of each stage and of the worst (`JPoints.message8`, for the `num_primes`
records of `prec`); `12` the numbers of the survivors of the three stages (`tot_surv1`,
`tot_surv2`, `tot_surv3`); nothing for any other `n`.

C: `j-points.c:2295-2301`, `j-points.c:2333-2337`, `j-points.c:2377-2383`

Deviation: the text returned, for the output on `stdout` that `fflush` flushes; the `long` `n` an
integer; the `long` `total` an integer, which message `6` prints, and message `5` passes as a
natural number to `print_poly`, as the degree, at least `5`, that `main` passes; the global
`coeffs` read from the curve of `g.choice`; `num_primes`, which `read_input` leaves in `[1, 53]`,
as a natural number; the messages `4`, `7` and `8` by the functions of their cases. -/
def message (g : MessageGlobals) (n total : Int) : Id String := do
  let input := g.choice.input
  match n with
  | 0 => return s!"\n{version}\n"
  | 1 => return "\nprob = 0, hence no solutions.\n"
  | 2 => return s!"\nFound {g.totals.totPoints} rational points on K lifting to J.\n"
  | 4 => message4 g.choice g.plan
  | 5 => return "\ny^2 = " ++ (← Printf.printPoly g.choice.curve.coeffs total.toNat) ++ "\n"
  | 6 =>
    let bound := if input.dbounded && input.dbound != input.height then
        s!"Bound on the fourth coordinate = {input.dbound}\n"
      else ""
    return s!"max. Height = {total}\n" ++ bound
  | 7 => message7 g.plan
  | 8 => message8 g.prec input.numPrimes.toNat g.plan
  | 12 =>
    return s!"\n{g.totals.totSurv1} candidates survived the first stage,\n" ++
      s!"{g.totals.totSurv2} candidates survived the second stage,\n" ++
      s!"{g.totals.totSurv3} candidates survived the third stage.\n"
  | _ => return ""

/-! ### Examples

From a test program that includes `j-points.c` of the pin, runs `read_input` on a command line
and, for the messages after the choice, quietly `normalise_curve`, `kummer_init` and
`init_fmodpsquare` (which sorts the records of the primes), then sets the totals and, for the
messages after the choice, `sieve_mode`, `tube_cut`, the numbers of the sieving primes and `pnn`,
and calls `message`: the text that it prints. The statistics of the analysis are their initial
values, since the test program runs no `tube_init`, and the condition at 2 is not used, as for a
height bound below `500`. -/

-- The globals of `message` for the command line `args` (after the name of the program), the
-- totals `tot` and, after the choice (`after`), the curve searched, the records of the primes as
-- `init_fmodpsquare` sorts them and the plan `plan`; before it, the curve given.
private def globals (args : List String) (tot : Totals) (after : Bool) (plan : Plan) :
    MessageGlobals :=
  let input := match (Cli.readInput args.toArray).run with
    | .ok input => input
    | .error _ => {}
  let given : SearchCurve :=
    { coeffs := input.coeffs, degree := input.degree.toNat, reversed := false, negated := false }
  let curve := if after then (normalizeCurve input.coeffs input.degree.toNat true).run.1 else given
  let t := (initMain Tables.initial).run
  let prec := if after then
      (initFmodpsquareRates t curve.coeffs curve.degree input.numPrimes.toNat CurveTables.initial
        (.replicate numPrimes {})).run.2.prec
    else .replicate numPrimes {}
  { choice := { input, curve, numNeg := 0, stats := {}, two := TwoAdic.initial }, plan, prec
    totals := tot }

-- The plan of the mode `mode`, the cut `cut`, the numbers `sp1`, `sp2` and `sp3` of the sieving
-- primes and the indices `pnn` in `prime[]`.
private def plan (mode : Nat) (cut : Bool) (sp1 sp2 sp3 : Nat) (pnn : List Nat) : Plan :=
  { pnn := pnn.toArray ++ .replicate (numPrimes + 1 - pnn.length) 0, sievePrimes1 := sp1
    sievePrimes2 := sp2, sievePrimes3 := sp3, sieveMode := mode, tubeCut := cut }

-- The messages before the choice: the banner, the curve given (a sextic with `f₀ = 0` and
-- `f₁ = 1`, which the search reverses), the height bound with a bound of `-w` and without one
-- (none, the height bound itself, `-a`), the messages `1`, `12` and `2`, and the numbers `3` and
-- `-1`, which have no message.
#guard
  let tot : Totals := { totSurv1 := 123, totSurv2 := 45, totSurv3 := 6, totPoints := 7 }
  ([(["0 1 2 -1 3 1 1", "300"], 0, 0,
      "\nThis is j-points-3.0.1 by Michael Stoll (2026-10-30).\n\n\
      Please acknowledge use of the program in published work.\n\n"),
    (["0 1 2 -1 3 1 1", "300"], 5, 6, "\ny^2 = x^6 + x^5 + 3 x^4 - x^3 + 2 x^2 + x\n\n"),
    (["1 -2 0 4 5 6 -7", "10"], 5, 6, "\ny^2 = - 7 x^6 + 6 x^5 + 5 x^4 + 4 x^3 - 2 x + 1\n\n"),
    (["0 1 0 0 0 -1 0", "10"], 5, 5, "\ny^2 = - x^5 + x\n\n"),
    (["1 2 3 4 5 6", "10"], 6, 10, "max. Height = 10\n"),
    (["1 2 3 4 5 6", "10", "-w", "7"], 6, 10,
      "max. Height = 10\nBound on the fourth coordinate = 7\n"),
    (["1 2 3 4 5 6", "10", "-w", "10"], 6, 10, "max. Height = 10\n"),
    (["1 2 3 4 5 6", "10", "-a"], 6, 10, "max. Height = 10\n"),
    (["1 2 3 4 5 6", "10", "-a", "-w", "3"], 6, 10,
      "max. Height = 10\nBound on the fourth coordinate = 3\n"),
    (["1 2 3 4 5 6", "10"], 1, 0, "\nprob = 0, hence no solutions.\n"),
    (["1 2 3 4 5 6", "10"], 12, 0,
      "\n123 candidates survived the first stage,\n45 candidates survived the second stage,\n\
      6 candidates survived the third stage.\n"),
    (["1 2 3 4 5 6", "10"], 2, 0, "\nFound 7 rational points on K lifting to J.\n"),
    (["1 2 3 4 5 6", "10"], 3, 0, ""),
    (["1 2 3 4 5 6", "10"], -1, 0, "")] :
    List (List String × Int × Int × String)).all fun (args, n, total, t) ↦
    (message (globals args tot false {}) n total).run == t

-- The messages after the choice, for plans set by hand: message `4` in the box, in the tube without
-- and with the cut, with constants set by `-c`, and in the region; message `7` with primes in each
-- stage and with none; message `8` with the ends of the three stages apart, with the first two
-- together and with the last two together; message `5`, which prints the curve searched, and
-- message `6`.
#guard
  let tot : Totals := { totSurv1 := 1, totSurv2 := 2, totSurv3 := 3, totPoints := 4 }
  let c := "1 1 -2 -15 13 2 1"
  let counts := "2 primes used for the first stage of sieving,\n\
    4 primes used for the first two stages together,\n\
    6 primes used for all three stages together.\n"
  let tube := "Sieving in the tube of the bound on the fourth coordinate"
  let words := ":\nabout 0.00 words per row, 0.00 cells of the analysis per row.\n"
  let p6 := [0, 1, 2, 3, 4, 5]
  let q6 := [5, 4, 3, 2, 1, 0]
  ([([c, "300"], 4, 0, plan 0 false 2 4 6 p6, counts),
    ([c, "300", "-c", "AND=0.5,ROW=7.25,INIT=1e-3"], 4, 0, plan 1 false 2 4 6 p6,
      tube ++ words ++ counts ++
        "Constants of the cost model set by -c: AND=0.5 ROW=7.25 INIT=0.001\n"),
    ([c, "300", "-w", "20"], 4, 0, plan 1 true 2 4 6 p6,
      tube ++ ", cut to the real region" ++ words ++ counts),
    ([c, "300", "-a"], 4, 0, plan 2 false 3 3 3 [0, 1, 2],
      "Sieving the real region by passes over its ranges of words:\n\
      about 0.00 words per row in 0.00 ranges, 1.000 of the rows.\n\
      3 primes used for the first stage of sieving,\n\
      3 primes used for the first two stages together,\n\
      3 primes used for all three stages together.\n"),
    ([c, "300"], 7, 0, plan 0 false 2 4 6 q6,
      "Sieving primes:\n First stage: 17, 13\n Second stage: 11, 7\n Third stage: 5, 3\n"),
    ([c, "300"], 7, 0, plan 0 false 0 0 0 [],
      "Sieving primes:\n First stage: \n Second stage: \n Third stage: \n"),
    ([c, "300"], 8, 0, plan 0 false 2 4 6 q6,
      "Probabilities: Min(29) = 0.484522, Cut1(13) = 0.683204, Cut2(7) = 0.790087, \
      Cut3(3) = 0.851852, Max(3) = 0.851852\n\n"),
    ([c, "300"], 8, 0, plan 0 false 2 2 6 q6,
      "Probabilities: Min(29) = 0.484522, Cut1(13) = 0.683204, Cut3(3) = 0.851852, \
      Max(3) = 0.851852\n\n"),
    ([c, "300"], 8, 0, plan 0 false 1 3 3 [9, 8, 7],
      "Probabilities: Min(29) = 0.484522, Cut1(31) = 0.518647, Cut2(23) = 0.533492, \
      Max(3) = 0.851852\n\n"),
    (["0 1 2 -1 3 1 1", "300"], 5, 6, plan 0 false 0 0 0 [],
      "\ny^2 = x^5 + 2 x^4 - x^3 + 3 x^2 + x + 1\n\n"),
    (["0 1 2 -1 3 1 1", "300", "-w", "20"], 6, 300, plan 0 false 0 0 0 [],
      "max. Height = 300\nBound on the fourth coordinate = 20\n")] :
    List (List String × Int × Int × Plan × String)).all fun (args, n, total, pl, t) ↦
    (message (globals (args ++ ["-p", "10"]) tot true pl) n total).run == t

end JPoints

end
