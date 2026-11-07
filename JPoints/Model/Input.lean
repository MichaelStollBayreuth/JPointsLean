/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.CliNumbers
public import JPoints.Model.Constants

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.CliNumbers
meta import JPoints.Model.Constants

/-!
# The command line of `j-points`

`j-points` takes the coefficients `f₀ f₁ … f_d` of the curve `y² = f(x)` as its first argument,
constant term first, the height bound as its second, and the options after them. `read_input` of
`j-points.c` reads them into its globals in this order, and every failure is an exit through `error`
with its number: the coefficients, integers separated by blanks that `scan_mpz` reads (error 3 for a
malformed integer or more than seven); the degree, without the zero leading coefficients (error 5
below 5); whether the polynomial is squarefree, by Euclid's algorithm over `ℚ` in `squarefree`
(error 9); the height bound, which `scan_long` reads (error 4 outside `[1, MAX_SEARCH_HEIGHT]`); and
the options from left to right, each a word of two characters, a minus sign and the option's
character (error 6 for a word that is no option, an option without its value or a value that is
refused, and error 10 for an argument of `-c` that `set_costs` does not read). Then it
reconciles the numbers of sieving primes with each other and with `-p`, and the bound on the fourth
coordinate with `-a` and `-w`. The values of `-c` replace the constants of the cost model in force,
by their names in the table `cost_names`; the format of `-f` is kept with its backslash escapes
interpreted by `unescape`.

## Main definitions

* `JPoints.Cli.Costs`, `JPoints.Cli.costNames`: the constants of the cost model in force, and the
  table of their names.
* `JPoints.Cli.Input`: the globals that `read_input` sets.
* `JPoints.Cli.Failure`: the errors with which `j-points` refuses a command line, with their texts
  (`JPoints.Cli.Failure.message`) and exit statuses (`JPoints.Cli.Failure.status`).
* `JPoints.Cli.setCosts`: the argument of `-c`, as `set_costs` reads it.
* `JPoints.Cli.unescape`: the format of `-f`, as `unescape` copies it.
* `JPoints.Cli.squarefree`: whether the polynomial is squarefree, as `squarefree` decides it.
* `JPoints.Cli.scanMpz`: an integer of the coefficient list, as `scan_mpz` reads it.
* `JPoints.Cli.readInput`: the command line, as `read_input` reads it, or the error.

## Implementation notes

The globals that `read_input` writes are the fields of one structure, `JPoints.Cli.Input`, whose
defaults are the values that they have before it runs. `read_input` and its helpers take it and
return it, or the error with which they exit, since `error` does not return. The words of the
command line are Lean strings, read as lists of characters as in `JPoints.Model.CliNumbers`, and the
index arithmetic over the words is that of the C, with `argv[i]` the word `i - 1` after the name of
the program. `read_input` is split at its loops and at its switch: the coefficients
(`JPoints.Cli.readCoefficients`, each read by `JPoints.Cli.scanMpz`), the loop over the options
(`JPoints.Cli.readOptions`), one option (`JPoints.Cli.readOption`, with the values of the options in
`JPoints.Cli.setOption`), and the reconciliation after the options (`JPoints.Cli.settleOptions`).
`main` checks the number of the arguments (error 2) before it calls `read_input`, and converts
`array_size` from kilobytes into words after it.
-/

@[expose] public section

namespace JPoints

namespace Cli

/-! ### The constants of the cost model -/

/-- The constants of the cost model in force, the static doubles `cost_and` to `cost_init` of
`j-points.c`: the defaults of the build (`JPoints.costAnd` to `JPoints.costInit`), or the values
that `-c` gives them.

C: `j-points.c:164-170`

Deviation: `Float`s, as the cost model runs in `Float`, which is the hardware double. -/
structure Costs where
  /-- `cost_and`, by default `JPoints.costAnd`. -/
  and : Float := costAnd
  /-- `cost_size`, by default `JPoints.costSize`. -/
  size : Float := costSize
  /-- `cost_word`, by default `JPoints.costWord`. -/
  word : Float := costWord
  /-- `cost_test2`, by default `JPoints.costTest2`. -/
  test2 : Float := costTest2
  /-- `cost_bit`, by default `JPoints.costBit`. -/
  bit : Float := costBit
  /-- `cost_row3`, by default `JPoints.costRow3`. -/
  row3 : Float := costRow3
  /-- `cost_test3`, by default `JPoints.costTest3`. -/
  test3 : Float := costTest3
  /-- `cost_exact`, by default `JPoints.costExact`. -/
  exact : Float := costExact
  /-- `cost_row`, by default `JPoints.costRow`. -/
  row : Float := costRow
  /-- `cost_cell`, by default `JPoints.costCell`. -/
  cell : Float := costCell
  /-- `cost_tword`, by default `JPoints.costTword`. -/
  tword : Float := costTword
  /-- `cost_ttest`, by default `JPoints.costTtest`. -/
  ttest : Float := costTtest
  /-- `cost_trow`, by default `JPoints.costTrow`. -/
  trow : Float := costTrow
  /-- `cost_rrow`, by default `JPoints.costRrow`. -/
  rrow : Float := costRrow
  /-- `cost_rexcl`, by default `JPoints.costRexcl`. -/
  rexcl : Float := costRexcl
  /-- `cost_rcut`, by default `JPoints.costRcut`. -/
  rcut : Float := costRcut
  /-- `cost_range`, by default `JPoints.costRange`. -/
  range : Float := costRange
  /-- `cost_pass`, by default `JPoints.costPass`. -/
  pass : Float := costPass
  /-- `cost_table`, by default `JPoints.costTable`. -/
  table : Float := costTable
  /-- `cost_init`, by default `JPoints.costInit`. -/
  init : Float := costInit
deriving Inhabited

/-- An entry of the table `cost_names` of `j-points.c`: the name of a constant of the cost model,
and the constant in force that its pointer `value` points to, which `JPoints.Cli.CostEntry.value`
reads and `JPoints.Cli.CostEntry.setValue` writes. -/
structure CostEntry where
  /-- `name`: the name of the macro without its prefix `COST_`. -/
  name : String
  /-- `*value`: the constant in force. -/
  value : Costs → Float
  /-- `*value = v`: the constants in force with this one set to `v`. -/
  setValue : Costs → Float → Costs
deriving Inhabited

/-- The table `cost_names` of `j-points.c`: the names of the constants of the cost model with
the constants in force that they name, in the order of the statics, which is the order in which
`-c list`, message 4 and error 10 print them.

C: `j-points.c:171-178`

Deviation: the pointer of an entry to its static double as the functions that read and write the
field of `JPoints.Cli.Costs` that it points to; the flags `set` of the entries in the globals
(`JPoints.Cli.Input.costSet`), since the names and the pointers do not change. -/
def costNames : Array CostEntry := #[⟨"AND", (·.and), ({ · with and := · })⟩,
  ⟨"SIZE", (·.size), ({ · with size := · })⟩, ⟨"WORD", (·.word), ({ · with word := · })⟩,
  ⟨"TEST2", (·.test2), ({ · with test2 := · })⟩, ⟨"BIT", (·.bit), ({ · with bit := · })⟩,
  ⟨"ROW3", (·.row3), ({ · with row3 := · })⟩, ⟨"TEST3", (·.test3), ({ · with test3 := · })⟩,
  ⟨"EXACT", (·.exact), ({ · with exact := · })⟩, ⟨"ROW", (·.row), ({ · with row := · })⟩,
  ⟨"CELL", (·.cell), ({ · with cell := · })⟩, ⟨"TWORD", (·.tword), ({ · with tword := · })⟩,
  ⟨"TTEST", (·.ttest), ({ · with ttest := · })⟩, ⟨"TROW", (·.trow), ({ · with trow := · })⟩,
  ⟨"RROW", (·.rrow), ({ · with rrow := · })⟩, ⟨"REXCL", (·.rexcl), ({ · with rexcl := · })⟩,
  ⟨"RCUT", (·.rcut), ({ · with rcut := · })⟩, ⟨"RANGE", (·.range), ({ · with range := · })⟩,
  ⟨"PASS", (·.pass), ({ · with pass := · })⟩, ⟨"TABLE", (·.table), ({ · with table := · })⟩,
  ⟨"INIT", (·.init), ({ · with init := · })⟩]

/-- `NUM_COSTS`, the number of entries of `cost_names`.

C: `j-points.c:179` -/
def numCosts : Nat := costNames.size

/-! ### The globals of the command line -/

/-- The globals that `read_input` of `j-points.c` sets, with the values that they have before it
runs as their defaults: the static initializers of `num_primes`, `dbound`, `dbounded`,
`num_threads`, the constants of the cost model, the flags `set` of `cost_names` and `costs_set`, the
zeros of the coefficients, which `init_main` initializes, and zero for the others, which
`read_input` sets before it reads them.

C: `j-points.c:66`, `j-points.c:180`, `j-points.c:208`, `j-points.c:254`, `j-points.c:265-269`,
`j-points.c:270-272`, `j-points.c:273-277`, `j-points.c:292`

Deviation: a structure for the globals; an array of seven `Int`s for the seven GMP integers of
`coeffs`; `Int`s for the `long`s, whose ranges after `read_input` later lemmas give; `Bool`s for
the `int` flags; a string for `print_format`, the empty string for the null pointer that it is
before `read_input` sets it; the flags `set` of the entries of `cost_names` as an array of their
own. -/
structure Input where
  /-- `coeffs`: the coefficients `f₀` to `f₆` of the polynomial, `0` above the degree. -/
  coeffs : Array Int := .replicate 7 0
  /-- `degree`: the degree of the polynomial. -/
  degree : Int := 0
  /-- `height`: the height bound. -/
  height : Int := 0
  /-- `dbound`: the bound on the fourth coordinate, the value of `-w` or the height bound. -/
  dbound : Int := -1
  /-- `dbounded`: whether the fourth coordinate is bounded at all (not under `-a` without
  `-w`). -/
  dbounded : Bool := true
  /-- `sieve_primes1`: the number of primes of the first stage of the sieve, `-1` for the choice
  of the cost model. -/
  sievePrimes1 : Int := 0
  /-- `sieve_primes2`: the number of primes of the first two stages, `-1` for the choice of the
  cost model. -/
  sievePrimes2 : Int := 0
  /-- `sieve_primes3`: the number of primes of all three stages, `-1` for the choice of the cost
  model. -/
  sievePrimes3 : Int := 0
  /-- `quiet`: whether the messages are left out (`-q`). -/
  quiet : Bool := false
  /-- `one_point`: whether one point is enough (`-1`). -/
  onePoint : Bool := false
  /-- `all_points`: whether the bound is on the height in `ℙ²` of the first three coordinates
  (`-a`). -/
  allPoints : Bool := false
  /-- `print_format`: the format in which the points are printed. -/
  printFormat : String := ""
  /-- `array_size`: the size of the bit array of the sieve, in kilobytes. -/
  arraySize : Int := 0
  /-- `num_primes`: the number of primes of the table that the sieve may use. -/
  numPrimes : Int := JPoints.numPrimes
  /-- `num_threads`: the number of threads (`-t`). -/
  numThreads : Int := 1
  /-- `cost_and` to `cost_init`: the constants of the cost model in force. -/
  costs : Costs := {}
  /-- The flags `set` of the entries of `cost_names`: whether `-c` set the constant. -/
  costSet : Array Bool := .replicate numCosts false
  /-- `costs_set`: whether `-c` set any constant. -/
  costsSet : Bool := false

/-! ### The errors -/

/-- The errors with which `j-points` refuses its command line, those of `main` and `read_input` that
a command line can cause: each a case of `error` of `j-points.c`, whose number is its exit status
(`JPoints.Cli.Failure.status`). -/
inductive Failure where
  /-- Error 2: fewer than two arguments, which `main` refuses. -/
  | tooFewArguments
  /-- Error 3: a first argument that is not a list of at most seven integers separated by blanks:
  an integer that `scan_mpz` refuses, or more than seven, the zero leading ones included. -/
  | coefficientSyntax
  /-- Error 4: a height bound that `scan_long` does not read, or outside
  `[1, MAX_SEARCH_HEIGHT]`. -/
  | incorrectHeight
  /-- Error 5: a polynomial of degree below 5, its zero leading coefficients not counted. -/
  | degreeTooSmall
  /-- Error 6: a word among the options that is no option, an option without its value, or a
  value that the option refuses. -/
  | optionSyntax
  /-- Error 9: a polynomial that is not squarefree. -/
  | notSquarefree
  /-- Error 10: an argument of `-c` that `set_costs` does not read. -/
  | costSyntax
deriving DecidableEq, Repr

/-- The usage of `j-points`, which errors 2 and 6 print.

C: `j-points.c:2436-2439`

Deviation: the text returned, for the output of the four `printf`s. -/
def usage : String :=
  "Usage: j-points 'a_0 a_1 ... a_d' max_height\n" ++
  "                [-n num_primes1] [-M num_primes2] [-N num_primes3]\n" ++
  "                [-p num_primes] [-s size] [-t threads] [-f format]\n" ++
  "                [-w bound4] [-c constants] [-1] [-q] [-a]\n"

/-- What error 10 prints: what the argument of `-c` must be, with the names of the constants of
the cost model in the order of `cost_names`.

C: `j-points.c:2425-2432`

Deviation: the text returned, for the output on `stdout`; a natural number for the `size_t` index
`k`. -/
def costSyntaxMessage : Id String := do
  let mut s := "\nThe argument of -c must be NAME=value, or several of them separated\n" ++
    "by commas, with a positive normal value and one of the names\n"
  for k in [0:numCosts] do
    s := s ++ " " ++ costNames[k]!.name
  return s ++ ".\n\n"

/-- What `error` of `j-points.c` prints for the failure `f`: a blank line, the message and a
blank line; for error 2 the usage after the blank line, which error 6 prints after its message, as
its case falls through to that of error 2.

C: `j-points.c:2410-2412`, `j-points.c:2413`, `j-points.c:2417-2421`, `j-points.c:2424`,
`j-points.c:2433-2435`, `j-points.c:2440-2441`

Deviation: the text returned, for the output on `stdout`; the failure `f`, for the `long` `n`, with
only the errors that a command line can cause (the messages of errors 1, 7 and 8 are excluded). -/
def Failure.message (f : Failure) : Id String := do
  match f with
  | .tooFewArguments => return "\n" ++ usage
  | .coefficientSyntax =>
    return "\nThe polynomial must be given by at most seven integers, separated\nby blanks.\n\n"
  | .incorrectHeight =>
    return s!"\nIncorrect height argument.\n  Height must be in [1, {maxSearchHeight}].\n\n"
  | .degreeTooSmall => return "\nThe polynomial must have degree at least 5.\n\n"
  | .optionSyntax => return "\nWrong syntax for optional arguments:\n\n\n" ++ usage
  | .notSquarefree => return "\nThe polynomial must be squarefree.\n\n"
  | .costSyntax => costSyntaxMessage

/-- The exit status of `j-points` on the failure `f`: the number of the error, with which `error`
exits after it has flushed the standard output.

C: `j-points.c:2442-2444`

Deviation: the status returned, for `exit(n)`; the flush of `stdout` made by `JPoints.Program.main`
when it writes the text. -/
def Failure.status : Failure → UInt32
  | .tooFewArguments => 2
  | .coefficientSyntax => 3
  | .incorrectHeight => 4
  | .degreeTooSmall => 5
  | .optionSyntax => 6
  | .notSquarefree => 9
  | .costSyntax => 10

/-! ### The option `-c` -/

/-- The index in `cost_names` of the entry whose name is `name`, the characters before the `=`,
or `NUM_COSTS` when there is none: the loop of `set_costs` over the table, which stops at the
first entry whose name has the length of `name` and agrees with it.

C: `j-points.c:398-400`

Deviation: the lists of characters compared for `strlen` and `strncmp` on the bytes, which agree as
the names are ASCII; the index returned, a natural number, for the `size_t` `k` that the loop
leaves. -/
def costIndex (name : List Char) : Id Nat := do
  for k in [0:numCosts] do
    if costNames[k]!.name.toList == name then return k
  return numCosts

/-- `set_costs` of `j-points.c`: the globals `st` with the constants of the cost model that the
argument `s` of `-c` sets, or none when `s` is not of the form `NAME=value`, several of them
separated by commas: the characters before the first `=` must be the name of an entry of
`cost_names` (`JPoints.Cli.costIndex`), and the value after it a double that `strtod` reads
(`JPoints.Cli.strtod`) without setting `ERANGE`, a positive normal double (not a NaN, a zero, a
negative, a subnormal or an infinity), followed by the end of `s`, or by a comma and the next item.
Each value is set and marked set (`JPoints.Cli.Input.costSet`, `costs_set`), the last one winning
for a name that comes twice; the empty string, an empty item and a final comma are refused; the
value may have white space before it. `ERANGE` refuses a constant that `strtod` rounds to an
infinity and one that underflows (`JPoints.Cli.underflows`): an inexact tiny value, which it rounds
to a zero, to a subnormal or, just below `2 ^ (-1022)`, to the normal double `2 ^ (-1022)`; an
exact subnormal leaves `errno` alone and is refused by `isnormal` (`JPoints.Double.isNormal`).

C: `j-points.c:391-397`, `j-points.c:401-413`

Deviation: some globals for the return value 1, and none for 0, on which the caller exits, so that
the values set by the items before a refused one are never read; the rest of the string from the
pointer for the pointer `s`, the characters before the `=` for `eq`, the number of characters that
`strtod` reads for `end`, and the flag of `JPoints.Cli.strtod` for `errno`, which `set_costs`
clears before the call; the return of 1 at the end of `s` as the exit from the loop, after which
the globals are returned; the double stored as a `Float` (`JPoints.Double.toFloat`). -/
def setCosts (s : List Char) (st : Input) : Id (Option Input) := do
  let mut s := s
  let mut st := st
  repeat
    let name := s.takeWhile (· != '=')
    if name.length == s.length then return none
    let k ← costIndex name
    if k == numCosts then return none
    let t := s.drop (name.length + 1)
    let (v, n, erange) := strtod t
    let e := t.drop n
    if n == 0 || erange || !Double.zero.lt v || !v.isNormal || e.head?.any (· != ',') then
      return none
    st := { st with
      costs := costNames[k]!.setValue st.costs v.toFloat
      costSet := st.costSet.set! k true
      costsSet := true }
    if e.isEmpty then break
    s := e.tail
  return some st

/-! ### The option `-f` -/

/-- `unescape` of `j-points.c`: the format `s` of `-f` with the backslash escapes `\n`, `\t` and
`\\` replaced by a line feed, a tab and a backslash, read from left to right, so that `\\n` gives
a backslash and an `n`; every other backslash is kept, a trailing one too.

C: `j-points.c:652-653`, `j-points.c:656-663`

Deviation: the string returned, for the copy that `unescape` allocates (lines 654-655, memory); the
rest of the string from the pointer for the pointer `s`. -/
def unescape (s : List Char) : Id String := do
  let mut s := s
  let mut d := ""
  while !s.isEmpty do
    let c := s.tail.head?
    if s.head? == some '\\' && (c == some 'n' || c == some 't' || c == some '\\') then
      d := d.push (if c == some 'n' then '\n' else if c == some 't' then '\t' else '\\')
      s := s.tail
    else
      d := d.push (s.headD '\\')
    s := s.tail
  return d

/-! ### Squarefreeness -/

/-- The polynomial `pu` of degree `du` replaced by its remainder modulo the polynomial `pv` of
degree `dv ≥ 0` (with `pv[dv] ≠ 0`), as the loop of `squarefree` computes it over `ℚ`: while
`du ≥ dv`, the multiple `q x ^ (du - dv) pv` that cancels the leading term of `pu` is subtracted
from it, and the degree lowered past the leading zeros, down to `-1` for the zero polynomial; the
remainder and its degree.

C: `j-points.c:633-640`

Deviation: the coefficients that `pu` points to as an array, returned; `Rat` for the `mpq_t`s; an
`Int` for the `long`s `du` and `dv`. -/
def remainderModulo (pu pv : Array Rat) (du dv : Int) : Id (Array Rat × Int) := do
  let mut pu := pu
  let mut du := du
  while du ≥ dv do
    let q := pu[du.toNat]! / pv[dv.toNat]!
    for i in [0:dv.toNat + 1] do
      let t := q * pv[i]!
      pu := pu.set! (i + (du - dv).toNat) (pu[i + (du - dv).toNat]! - t)
    du := du - 1
    while du ≥ 0 && pu[du.toNat]! == 0 do
      du := du - 1
  return (pu, du)

/-- `squarefree` of `j-points.c`: whether the polynomial with the coefficients `coeffs` of degree
`degree ≥ 0` (with `coeffs[degree] ≠ 0`) is squarefree, that is, whether the gcd of it and its
derivative over `ℚ` is a constant, by Euclid's algorithm: the remainder of the one modulo the
other (`JPoints.Cli.remainderModulo`), then the two exchanged, until the second is `0`; the first
is then the gcd, and its degree must be `0`.

C: `j-points.c:618-622`, `j-points.c:625-629`, `j-points.c:632`, `j-points.c:641-644`,
`j-points.c:647-648`

Deviation: the globals `coeffs` and `degree` as arguments; arrays of seven `Rat`s for the arrays
`u` and `v` of `mpq_t`s, zero at the start as `mpq_init` sets them (lines 623-624, memory), and
exchanged where the C exchanges the pointers `pu` and `pv` to them; an `Int` for the `long`s `du`
and `dv`, which reach `-1`; a `Bool` for the `int` result. -/
def squarefree (coeffs : Array Int) (degree : Int) : Id Bool := do
  let mut pu : Array Rat := .replicate 7 0
  let mut pv : Array Rat := .replicate 7 0
  let mut du := degree
  let mut dv := degree - 1
  for i in [0:(degree + 1).toNat] do
    pu := pu.set! i (coeffs[i]! : Rat)
  for i in [1:(degree + 1).toNat] do
    let t : Rat := i
    pv := pv.set! (i - 1) (coeffs[i]! * t)
  while dv ≥ 0 do
    (pu, du) ← remainderModulo pu pv du dv
    (pu, pv) := (pv, pu)
    (du, dv) := (dv, du)
  return du == 0

/-! ### `read_input` -/

/-- `scan_mpz` of `j-points.c`: the integer at the pointer `s` of the coefficient list and the
pointer after it, `NULL` (none) when `s` is `NULL` (none), the empty string or blanks only, or
error 3. It skips blanks, spaces and tabs (not the other C white space), reads an optional sign `-`
or `+` and the maximal run of decimal digits after it, which must not be empty, and wants a blank
or the end of the string after them; anything else is error 3: a lone sign, `1-6`, a comma or a
letter. There is no bound on the size of the integer.

C: `j-points.c:560-578`

Deviation: the rest of the string from the pointer for the pointer, with none for `NULL`; the
integer returned with the pointer, for the `mpz_t` that `scan_mpz` writes through `x` when it does
not return `NULL`; the error returned, for the exit through `error(3)`; a local integer for `tmp2`,
a global GMP integer of the C (one per thread) that `scan_mpz` sets before it reads it and that no
function reads before setting it; a `Bool` for the `long` flag `neg`. -/
def scanMpz (s : Option (List Char)) : Id (Except Failure (Option (Int × List Char))) := do
  let some s := s | return .ok none
  if s.isEmpty then return .ok none
  let mut s := s
  while s.head? == some ' ' || s.head? == some '\t' do
    s := s.tail
  if s.isEmpty then return .ok none
  let neg := s.head? == some '-'
  if neg || s.head? == some '+' then s := s.tail
  if !s.head?.any Char.isDigit then return .error .coefficientSyntax
  let mut tmp2 : Int := 0
  while s.head?.any Char.isDigit do
    tmp2 := 10 * tmp2 + digitValue (s.headD '0')
    s := s.tail
  if s.head?.any (fun c ↦ c != ' ' && c != '\t') then return .error .coefficientSyntax
  if neg then tmp2 := -tmp2
  return .ok (some (tmp2, s))

/-- The coefficients of the first argument `s` and the degree, as `read_input` of `j-points.c`
reads them into the coefficients `coeffs`: up to seven integers that `scan_mpz` reads one after the
other (`JPoints.Cli.scanMpz`), each from the pointer that the last one returned, until it returns
`NULL`; error 3 when `scan_mpz` refuses an integer or reads an eighth; else the coefficients and
the degree, without the zero leading coefficients, and `-1` when there is none.

C: `j-points.c:417-424`

Deviation: the global `coeffs` as an argument, returned with `degree`, or the error, for the exit
through `error(3)`; the rest of the string from the pointer for the pointer `s`, with none for
`NULL`; the eighth integer, which `scan_mpz` writes into the scratch `fff`, not kept; an `Int` for
the `long` `degree`. -/
def readCoefficients (s : List Char) (coeffs : Array Int) :
    Id (Except Failure (Array Int × Int)) := do
  let mut s : Option (List Char) := some s
  let mut coeffs := coeffs
  let mut degree : Int := 0
  while degree ≤ 6 do
    match ← scanMpz s with
    | .error e => return .error e
    | .ok r =>
      s := r.map (·.2)
      let some (x, _) := r | break
      coeffs := coeffs.set! degree.toNat x
      degree := degree + 1
  degree := degree - 1
  match ← scanMpz s with
  | .error e => return .error e
  | .ok (some _) => return .error .coefficientSyntax
  | .ok none => pure ()
  while 0 < degree && coeffs[degree.toNat]! == 0 do
    degree := degree - 1
  return .ok (coeffs, degree)

/-- The globals `st` with the one that the option `-o`, one of `-n`, `-M`, `-N`, `-s`, `-f`, `-w`,
`-t`, `-c` and `-p`, sets from its value `v`, as the switch of `read_input` of `j-points.c` sets
them: the format for `-f` (`JPoints.Cli.unescape`); the constants of the cost model for `-c`
(`JPoints.Cli.setCosts`), error 10 when it refuses `v`; and for the others, error 6 when `scan_long`
does not read `v` (`JPoints.Cli.scanLong`), else the numbers of sieving primes for `-n`, `-M` and
`-N`, error 6 when they are negative; the size of the bit array for `-s`, error 6 when it is not
positive; the bound on the fourth coordinate for `-w` and the number of threads for `-t`, error 6
below `1`; and the number of primes for `-p`, the last of them, error 6 when it is not positive, and
made `JPoints.numPrimes` above it.

C: `j-points.c:449-450`, `j-points.c:456-457`, `j-points.c:463-464`, `j-points.c:470-471`,
`j-points.c:477`, `j-points.c:483-484`, `j-points.c:502-503`, `j-points.c:510`,
`j-points.c:516-518`

Deviation: the globals returned, or the error, for the exit through `error`, so that a value
refused after `scan_long` has written it is not kept; `scan_long` called once before the cases of
the options that read a `long`, where each of these cases calls it first; the long that `scan_long`
writes when it fails, on which the caller exits, not kept. -/
def setOption (o : Char) (v : List Char) (st : Input) : Id (Except Failure Input) := do
  if o == 'f' then return .ok { st with printFormat := ← unescape v }
  if o == 'c' then
    let some st ← setCosts v st | return .error .costSyntax
    return .ok st
  let some x := scanLong v | return .error .optionSyntax
  match o with
  | 'n' => return if x < 0 then .error .optionSyntax else .ok { st with sievePrimes1 := x }
  | 'M' => return if x < 0 then .error .optionSyntax else .ok { st with sievePrimes2 := x }
  | 'N' => return if x < 0 then .error .optionSyntax else .ok { st with sievePrimes3 := x }
  | 's' => return if x ≤ 0 then .error .optionSyntax else .ok { st with arraySize := x }
  | 'w' => return if x < 1 then .error .optionSyntax else .ok { st with dbound := x }
  | 't' => return if x < 1 then .error .optionSyntax else .ok { st with numThreads := x }
  | _ =>
    if x ≤ 0 then return .error .optionSyntax
    return .ok { st with numPrimes := if x > JPoints.numPrimes then JPoints.numPrimes else x }

/-- One pass of the loop of `read_input` of `j-points.c` over the options: the option at
`argv[i]`, the word `args[i - 1]`, read into the globals `st`, and the index of the next one;
error 6 unless the word has two characters, a minus sign and the option's character (so `-quiet`
and `-n5` are refused): `-q`, `-a` and `-1` set their flags, and `-n`, `-M`, `-N`, `-s`, `-f`,
`-w`, `-t`, `-c` and `-p` take the next word as their value (`JPoints.Cli.setOption`), error 6 when
there is none; every other character is error 6.

C: `j-points.c:444-448`, `j-points.c:451-455`, `j-points.c:458-462`, `j-points.c:465-469`,
`j-points.c:472-476`, `j-points.c:478-482`, `j-points.c:485-501`, `j-points.c:504-509`,
`j-points.c:511-515`, `j-points.c:519-521`

Deviation: the globals and the index returned, or the error, for the exit through `error`; the
words after the name of the program for `argv`, `args[i - 1]` for `argv[i]` and `args.size` for
`argc`; the number of characters of the word for `strlen`, its number of bytes, which differ only
for a word with a character that is not ASCII, refused either way, as neither the minus sign nor an
option is such a character; the test for the missing value, which each case of an option with a
value makes, made once before them. -/
def readOption (args : Array String) (i : Nat) (st : Input) :
    Id (Except Failure (Input × Nat)) := do
  let w := args[i - 1]!.toList
  if w.head? != some '-' || w.length != 2 then return .error .optionSyntax
  match w[1]! with
  | 'q' => return .ok ({ st with quiet := true }, i + 1)
  | 'a' => return .ok ({ st with allPoints := true }, i + 1)
  | '1' => return .ok ({ st with onePoint := true }, i + 1)
  | o =>
    if !"nMNsfwtcp".contains o || args.size == i then return .error .optionSyntax
    match ← setOption o args[i]!.toList st with
    | .ok st => return .ok (st, i + 2)
    | .error e => return .error e

/-- The globals `st` after the options, as `read_input` of `j-points.c` settles them: one thread
under `-1`; the numbers of sieving primes made at most `num_primes`, and each at most those of the
later stages that are not `-1`, in the order of the C; the fourth coordinate bounded unless `-a`
is given without `-w`, and its bound the height bound unless `-w` gives one.

C: `j-points.c:525`, `j-points.c:529-537`, `j-points.c:540-541`

Deviation: the globals taken and returned. -/
def settleOptions (st : Input) : Input :=
  let np := st.numPrimes
  let s3 := if st.sievePrimes3 > np then np else st.sievePrimes3
  let s2 := if st.sievePrimes2 > np then np else st.sievePrimes2
  let s2 := if s3 ≥ 0 && s2 > s3 then s3 else s2
  let s1 := if st.sievePrimes1 > np then np else st.sievePrimes1
  let s1 := if s3 ≥ 0 && s1 > s3 then s3 else s1
  let s1 := if s2 ≥ 0 && s1 > s2 then s2 else s1
  { st with
    numThreads := if st.onePoint then 1 else st.numThreads
    sievePrimes1 := s1, sievePrimes2 := s2, sievePrimes3 := s3
    dbounded := st.dbound > 0 || !st.allPoints
    dbound := if st.dbound ≤ 0 then st.height else st.dbound }

/-- The loop of `read_input` of `j-points.c` over the options of the command line `args`, from the
third word on: each read into the globals `st` (`JPoints.Cli.readOption`), the last of each option
winning, or the first error.

C: `j-points.c:441-443`, `j-points.c:522`

Deviation: the globals returned, or the error, for the exit through `error`; the words after the
name of the program for `argv` and `args.size` for `argc`; a natural number for the `long` `i`. -/
def readOptions (args : Array String) (st : Input) : Id (Except Failure Input) := do
  let mut st := st
  let mut i := 3
  while i ≤ args.size do
    match ← readOption args i st with
    | .ok (st', i') =>
      st := st'
      i := i'
    | .error e => return .error e
  return .ok st

/-- `read_input` of `j-points.c`: the globals that the command line `args` (the words after the
name of the program, at least two) sets, or the error with which `read_input` exits, in its order:
the coefficients of the first word (`JPoints.Cli.readCoefficients`, error 3), the degree at least
5 (error 5), then the coefficient `f₆` set to `0` for the degree 5, the polynomial squarefree
(`JPoints.Cli.squarefree`, error 9), the height bound of the second word in
`[1, MAX_SEARCH_HEIGHT]` (`JPoints.Cli.scanLong`, error 4); the defaults of the options; the options
(`JPoints.Cli.readOptions`, errors 6 and 10); and the settlement after them
(`JPoints.Cli.settleOptions`).

C: `j-points.c:415-416`, `j-points.c:425-438`, `j-points.c:542`

Deviation: the globals returned, or the error, for the exit through `error`; the words after the
name of the program for `argv`, `args[0]` for `argv[1]` and `args[1]` for `argv[2]`, which `main`
makes sure exist. -/
def readInput (args : Array String) : Id (Except Failure Input) := do
  let mut st : Input := {}
  let (coeffs, degree) ← match ← readCoefficients args[0]!.toList st.coeffs with
    | .ok r => pure r
    | .error e => return .error e
  if degree < 5 then return .error .degreeTooSmall
  st := { st with coeffs := if degree == 5 then coeffs.set! 6 0 else coeffs, degree }
  if !(← squarefree st.coeffs st.degree) then return .error .notSquarefree
  let some height := scanLong args[1]!.toList | return .error .incorrectHeight
  if height < 1 || height > maxSearchHeight then return .error .incorrectHeight
  st := { st with
    height, sievePrimes1 := -1, sievePrimes2 := -1, sievePrimes3 := -1, quiet := false
    onePoint := false, allPoints := false, printFormat := "(%ld, %ld, %ld, %ld)\n"
    arraySize := defaultSize }
  return (← readOptions args st).map settleOptions

/-! ### Examples

The expected values are those of `j-points` at the pin: the texts of its errors and its exit
statuses, and the globals that a copy of it prints after `read_input`, the constants of the cost
model by their bits, and the values and the pointers of `scan_mpz` in a test program. -/

-- The globals that `read_input` sets for a command line without options, with the coefficients
-- `cs` of the degree `d` and the height bound `h`.
private def plain (cs : Array Int) (d h : Int) : Input :=
  { coeffs := cs, degree := d, height := h, dbound := h, sievePrimes1 := -1, sievePrimes2 := -1,
    sievePrimes3 := -1, printFormat := "(%ld, %ld, %ld, %ld)\n", arraySize := 10 }

-- The command line of the curve `y² = x⁵ + 1` with the height bound 10 and the options `os`.
private def opts (os : List String) : List String := "1 0 0 0 0 1" :: "10" :: os

-- The globals for `opts []`.
private def quintic : Input := plain #[1, 0, 0, 0, 0, 1, 0] 5 10

-- The smallest normal double, `2 ^ (-1022)`.
private def dblMin : Float := .ofBits 0x0010000000000000

-- The flags `set` of `cost_names` with those of the entries `ks` set.
private def flags (ks : List Nat) : Array Bool := (Array.range numCosts).map (ks.contains ·)

-- Whether the globals `a` and `b` agree, the constants of the cost model by their bits.
private def same (a b : Input) : Bool :=
  a.coeffs == b.coeffs && a.degree == b.degree && a.height == b.height &&
    a.dbound == b.dbound && a.dbounded == b.dbounded && a.sievePrimes1 == b.sievePrimes1 &&
    a.sievePrimes2 == b.sievePrimes2 && a.sievePrimes3 == b.sievePrimes3 && a.quiet == b.quiet &&
    a.onePoint == b.onePoint && a.allPoints == b.allPoints && a.printFormat == b.printFormat &&
    a.arraySize == b.arraySize && a.numPrimes == b.numPrimes && a.numThreads == b.numThreads &&
    a.costSet == b.costSet && a.costsSet == b.costsSet &&
    costNames.all fun e ↦ (e.value a.costs).toBits == (e.value b.costs).toBits

-- Whether `readInput` gives `r` on the command line `args`, a failure by its exit status.
private def reads (args : List String) (r : Except UInt32 Input) : Bool :=
  match (readInput args.toArray).run, r with
  | .ok a, .ok b => same a b
  | .error f, .error n => f.status == n
  | _, _ => false

-- Whether `readInput` gives each of the `cases`, as `reads` checks it.
private def readsAll (cases : List (List String × Except UInt32 Input)) : Bool :=
  cases.all fun (a, r) ↦ reads a r

-- The texts of `error` and the exit statuses.
#guard ([(.tooFewArguments, 2, "\nUsage: j-points 'a_0 a_1 ... a_d' max_height\n" ++
      "                [-n num_primes1] [-M num_primes2] [-N num_primes3]\n" ++
      "                [-p num_primes] [-s size] [-t threads] [-f format]\n" ++
      "                [-w bound4] [-c constants] [-1] [-q] [-a]\n"),
    (.coefficientSyntax, 3,
      "\nThe polynomial must be given by at most seven integers, separated\nby blanks.\n\n"),
    (.incorrectHeight, 4, "\nIncorrect height argument.\n  Height must be in [1, 67108864].\n\n"),
    (.degreeTooSmall, 5, "\nThe polynomial must have degree at least 5.\n\n"),
    (.optionSyntax, 6, "\nWrong syntax for optional arguments:\n\n\n" ++
      "Usage: j-points 'a_0 a_1 ... a_d' max_height\n" ++
      "                [-n num_primes1] [-M num_primes2] [-N num_primes3]\n" ++
      "                [-p num_primes] [-s size] [-t threads] [-f format]\n" ++
      "                [-w bound4] [-c constants] [-1] [-q] [-a]\n"),
    (.notSquarefree, 9, "\nThe polynomial must be squarefree.\n\n"),
    (.costSyntax, 10,
      "\nThe argument of -c must be NAME=value, or several of them separated\n" ++
      "by commas, with a positive normal value and one of the names\n" ++
      " AND SIZE WORD TEST2 BIT ROW3 TEST3 EXACT ROW CELL TWORD TTEST TROW RROW REXCL RCUT RANGE" ++
      " PASS TABLE INIT.\n\n")] :
    List (Failure × UInt32 × String)).all fun (f, n, m) ↦ f.status == n && f.message.run == m

-- `unescape`: the escapes `\n`, `\t` and `\\`, read from left to right; other backslashes kept.
#guard ([("", ""), ("\\n", "\n"), ("\\t", "\t"), ("\\\\", "\\"), ("\\\\n", "\\n"), ("\\q", "\\q"),
    ("a\\", "a\\"), ("\\\\\\n", "\\\n"), ("\\\\\\", "\\\\"), ("%ld\\t%ld\\n", "%ld\t%ld\n"),
    ("é\\n", "é\n"), ("\\\n", "\\\n")] : List (String × String)).all fun (s, r) ↦
  (unescape s.toList).run == r

-- `scan_mpz`, one call: `NULL` (`some none`) for `NULL`, the empty string and blanks only; spaces
-- and tabs skipped; the value and the characters read; error 3 (`none`) for a sign without a
-- digit, digits followed by anything but a blank or the end, and every other character.
#guard (scanMpz none).run matches .ok none
#guard ([
    ("", some none), (" ", some none), ("   ", some none), ("\t", some none),
    (" \t ", some none), ("+", none), ("-", none), ("-5", some (some (-5, 2))),
    ("+5", some (some (5, 2))), (" 12 34", some (some (12, 3))), ("\t1 2", some (some (1, 2))),
    ("\t-7\t8", some (some (-7, 3))), ("1\t2", some (some (1, 1))),
    ("\t\t+12\t ", some (some (12, 5))), ("007 ", some (some (7, 3))), ("a", none),
    ("+-5", none), ("-0", some (some (0, 2))), ("  -  5", none), ("- 5", none), ("+\t5", none),
    ("1,2", none), ("12a", none), ("5\n", none), ("1\x0b2", none),
    ("12345678901234567890123456789", some (some (12345678901234567890123456789, 29))),
    ("5     ", some (some (5, 1))), ("    +", none), ("\u00a01", none), ("\u0661\u0662", none),
    ("-c", none), ("1 2 3 4 5 6 -", some (some (1, 1))), ("1 2 3 4 5 6 7 8", some (some (1, 1))),
    (" 0 0 1 -1  +2", some (some (0, 2))), ("1-2", none)] :
    List (String × Option (Option (Int × Nat)))).all fun (s, r) ↦
  match (scanMpz (some s.toList)).run, r with
  | .ok v, some w => v.map (fun (x, t) ↦ (x, s.length - t.length)) == w
  | .error .coefficientSyntax, none => true
  | _, _ => false

-- `scan_mpz` called as `read_input` calls it, up to eight times, each time on the pointer that the
-- last call returned, until it returns `NULL` or gives error 3: the values and the characters read
-- in all, and whether a call gave error 3.
#guard ([("1 2 3 4 5 6 -", [(1, 1), (2, 3), (3, 5), (4, 7), (5, 9), (6, 11)], true),
    ("1 2 3 4 5 6 7 8", [(1, 1), (2, 3), (3, 5), (4, 7), (5, 9), (6, 11), (7, 13), (8, 15)], false),
    (" 0 0 1 -1  +2", [(0, 2), (0, 4), (1, 6), (-1, 9), (2, 13)], false),
    ("1\t0 0 0\t0 1", [(1, 1), (0, 3), (0, 5), (0, 7), (0, 9), (1, 11)], false),
    ("1 178 817 \t-274 16\t1", [(1, 1), (178, 5), (817, 9), (-274, 15), (16, 18), (1, 20)], false),
    ("\t1 2\t", [(1, 2), (2, 4)], false),
    ("1 6 5 22 22 8 -", [(1, 1), (6, 3), (5, 5), (22, 8), (22, 11), (8, 13)], true),
    ("+-5", [], true), ("  -  5", [], true), ("1-2", [], true), ("1,2", [], true)] :
    List (String × List (Int × Nat) × Bool)).all fun (s, xs, e) ↦
  let step (acc : List (Int × Nat) × Option (List Char) × Bool) (_ : Nat) :=
    match (scanMpz acc.2.1).run with
    | .ok (some (x, t)) => (acc.1 ++ [(x, s.length - t.length)], some t, acc.2.2)
    | .ok none => (acc.1, none, acc.2.2)
    | .error _ => (acc.1, none, true)
  let (ys, _, e') := (List.range 8).foldl step ([], some s.toList, false)
  ys == xs && e' == e

-- The coefficients: blanks, spaces and tabs, between them, the zero leading ones dropped; error 3
-- for an eighth and for an integer that `scan_mpz` refuses (a lone sign, `1-6`, a comma, a letter),
-- also where the degree would be below 5 or the polynomial not squarefree; error 5 below the
-- degree 5.
#guard readsAll [
    (opts [], .ok quintic),
    (["1 2 3 4 5 6 7", "100"], .ok (plain #[1, 2, 3, 4, 5, 6, 7] 6 100)),
    ([" 1  0 0 0 0 1 ", "10"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1 0 0 0 0 1 0", "10"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1\t0 0 0 0 1", "10"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1\t\t0 0 0 0 +1", "10"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1 0 0 0 0 1\t", "10"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1 178 817 \t-274 16\t1", "10"], .ok (plain #[1, 178, 817, -274, 16, 1, 0] 5 10)),
    (["123456789012345678901234567890 0 0 0 0 1", "10"],
      .ok (plain #[123456789012345678901234567890, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1 2 3 4 5 6 -", "10"], .error 3),
    (["1-2 3 4 5 6", "10"], .error 3),
    (["+-5 1 0 0 0 1", "10"], .error 3),
    (["1-6 5 22 22 8 1", "10"], .error 3),
    (["1 6 5 22 22 8 -", "10"], .error 3),
    (["1 178 817 - 274 16 1", "10"], .error 3),
    (["1 2 3 4 5 6 7 0", "10"], .error 3),
    (["1 2 3 4 5 6 7 8", "10"], .error 3),
    (["1 2 3 4 5 6 7 +", "10"], .error 3),
    (["1 2 3 4 5 6 7 8x", "10"], .error 3),
    (["1 0 0 0 0 1 x", "10"], .error 3),
    (["1,0,0,0,0,1", "10"], .error 3),
    (["1 2 -", "10"], .error 3),
    (["0 0 0 0 0 0 0 -", "10"], .error 3),
    (["1 0 0 0 0 -1 -", "abc"], .error 3),
    (["", "10"], .error 5),
    (["   ", "10"], .error 5),
    (["\t\t", "10"], .error 5),
    (["1 2 3 4 5", "10"], .error 5),
    (["0 0 0 0 0 0 0", "10"], .error 5),
    (["1 2 3 4 5 0 0", "10"], .error 5)]

-- Squarefreeness (error 9), checked before the height bound.
#guard readsAll [
    (["0 0 0 0 0 1", "10"], .error 9),
    (["1 -2 1 0 0 1", "10"], .ok (plain #[1, -2, 1, 0, 0, 1, 0] 5 10)),
    (["0 0 1 0 0 1", "10"], .error 9),
    (["1 2 1 0 0 0 1", "10"], .ok (plain #[1, 2, 1, 0, 0, 0, 1] 6 10)),
    (["4 -12 13 -6 1 0 0", "10"], .error 5),
    (["1 0 -3 0 3 0 -1", "10"], .error 9),
    (["0 1 0 0 0 0 1", "10"], .ok (plain #[0, 1, 0, 0, 0, 0, 1] 6 10)),
    (["-1 0 3 0 -3 0 1", "10"], .error 9),
    (["2 -3 0 1 0 0 1", "10"], .ok (plain #[2, -3, 0, 1, 0, 0, 1] 6 10))]

-- The height bound (error 4): from 1 to `MAX_SEARCH_HEIGHT`, the rest of the word ignored.
#guard readsAll [
    (["1 0 0 0 0 1", "0"], .error 4),
    (["1 0 0 0 0 1", "-5"], .error 4),
    (["1 0 0 0 0 1", "67108864"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 67108864)),
    (["1 0 0 0 0 1", "67108865"], .error 4),
    (["1 0 0 0 0 1", "3037000499"], .error 4),
    (["1 0 0 0 0 1", "9223372036854775808"], .error 4),
    (["1 0 0 0 0 1", " 10x"], .ok (plain #[1, 0, 0, 0, 0, 1, 0] 5 10)),
    (["1 0 0 0 0 1", ""], .error 4),
    (["1 0 0 0 0 1", "abc"], .error 4),
    (["0 0 0 0 0 1", "abc"], .error 9)]

-- The options, each a word of two characters, their values and errors 6, the last of each
-- winning, and the settlement after them: one thread under `-1`, the numbers of sieving primes
-- at most `-p` and those of the later stages, the bound on the fourth coordinate.
#guard readsAll [
    (opts ["-q", "-a", "-1"],
      .ok { quintic with dbounded := false, quiet := true, onePoint := true, allPoints := true }),
    (opts ["-quiet"], .error 6),
    (opts ["-all"], .error 6),
    (opts ["-1x"], .error 6),
    (opts ["-qq"], .error 6),
    (opts ["-n", "5", "-M", "7", "-N", "9"],
      .ok { quintic with sievePrimes1 := 5, sievePrimes2 := 7, sievePrimes3 := 9 }),
    (opts ["-n5", "7"], .error 6),
    (opts ["-cfoo", "AND=1"], .error 6),
    (opts ["-n", "0", "-M", "0", "-N", "0"],
      .ok { quintic with sievePrimes1 := 0, sievePrimes2 := 0, sievePrimes3 := 0 }),
    (opts ["-n", "-1"], .error 6),
    (opts ["-M", "-2"], .error 6),
    (opts ["-N", "-1"], .error 6),
    (opts ["-n", "-5", "-M", "-1", "-N", "-2"], .error 6),
    (opts ["-n", "x"], .error 6),
    (opts ["-n", "7x"], .ok { quintic with sievePrimes1 := 7 }),
    (opts ["-n"], .error 6),
    (opts ["-n", "9223372036854775808"], .error 6),
    (opts ["-s", "100"], .ok { quintic with arraySize := 100 }),
    (opts ["-s", "0"], .error 6),
    (opts ["-w", "5"], .ok { quintic with dbound := 5 }),
    (opts ["-w", "0"], .error 6),
    (opts ["-t", "4"], .ok { quintic with numThreads := 4 }),
    (opts ["-t", "0"], .error 6),
    (opts ["-t", "4", "-1"], .ok { quintic with onePoint := true }),
    (opts ["-p", "20"], .ok { quintic with numPrimes := 20 }),
    (opts ["-p", "100"], .ok quintic),
    (opts ["-p", "0"], .error 6),
    (opts ["-p", "3", "-n", "5", "-M", "4", "-N", "10"],
      .ok { quintic with sievePrimes1 := 3, sievePrimes2 := 3, sievePrimes3 := 3, numPrimes := 3 }),
    (opts ["-n", "10", "-M", "5"], .ok { quintic with sievePrimes1 := 5, sievePrimes2 := 5 }),
    (opts ["-N", "3", "-n", "10", "-M", "8"],
      .ok { quintic with sievePrimes1 := 3, sievePrimes2 := 3, sievePrimes3 := 3 }),
    (opts ["-M", "0", "-n", "2"], .ok { quintic with sievePrimes1 := 0, sievePrimes2 := 0 }),
    (opts ["-a"], .ok { quintic with dbounded := false, allPoints := true }),
    (opts ["-a", "-w", "5"], .ok { quintic with dbound := 5, allPoints := true }),
    (opts ["-w", "5", "-w", "7"], .ok { quintic with dbound := 7 })]

-- The format of `-f` (any word, also one that starts with `-`), and the words that are no option.
#guard readsAll [
    (opts ["-f", "%ld %ld %ld %ld\\n"], .ok { quintic with printFormat := "%ld %ld %ld %ld\n" }),
    (opts ["-f", "a\\tb\\\\c\\q\\"], .ok { quintic with printFormat := "a\tb\\c\\q\\" }),
    (opts ["-f", "\\\\n"], .ok { quintic with printFormat := "\\n" }),
    (opts ["-f", ""], .ok { quintic with printFormat := "" }),
    (opts ["-f", "-q"], .ok { quintic with printFormat := "-q" }),
    (opts ["-x"], .error 6),
    (opts [""], .error 6),
    (opts ["-"], .error 6),
    (opts ["--"], .error 6),
    (opts ["-é"], .error 6),
    (opts ["q"], .error 6),
    (opts ["-c"], .error 6)]

-- The option `-c`: the values in force and their flags, error 10 for an argument that
-- `set_costs` refuses (the empty one, a final comma, a value that is not a positive normal double,
-- `ERANGE` also for the values just below `2 ^ (-1022)` that round to it), error 6 for a missing
-- one.
#guard readsAll [
    (opts ["-c", "AND=2"],
      .ok { quintic with costs := { and := 2 }, costSet := flags [0], costsSet := true }),
    (opts ["-c", "AND=1,SIZE=0.5,AND=3"],
      .ok { quintic with
        costs := { and := 3, size := 0.5 }, costSet := flags [0, 1], costsSet := true }),
    (opts ["-c", "AND=2", "-c", "INIT=1e2"],
      .ok { quintic with
        costs := { and := 2, init := 100 }, costSet := flags [0, 19], costsSet := true }),
    (opts ["-c", "TEST2= 5.5"],
      .ok { quintic with costs := { test2 := 5.5 }, costSet := flags [3], costsSet := true }),
    (opts ["-c", "AND=0x1p-1022"],
      .ok { quintic with costs := { and := dblMin }, costSet := flags [0], costsSet := true }),
    (opts ["-c", "AND=2.2250738585072013e-308"],
      .ok { quintic with costs := { and := dblMin }, costSet := flags [0], costsSet := true }),
    (opts ["-c", "AND=0x1.fffffffffffff8p-1023"],
      .ok { quintic with costs := { and := dblMin }, costSet := flags [0], costsSet := true }),
    (opts ["-c", "AND=1.7976931348623158e308"],
      .ok { quintic with
        costs := { and := .ofBits 0x7fefffffffffffff }, costSet := flags [0], costsSet := true }),
    (opts ["-c", ""], .error 10),
    (opts ["-c", "AND=1,"], .error 10),
    (opts ["-c", "AND=0.63,"], .error 10),
    (opts ["-c", ","], .error 10),
    (opts ["-c", "AND=1, SIZE=2"], .error 10),
    (opts ["-c", "EXACT=inf,ROW=1e999,CELL=1e-320,PASS=0x1p-1074"], .error 10),
    (opts ["-c", "AND=inf"], .error 10),
    (opts ["-c", "AND=infinity"], .error 10),
    (opts ["-c", "AND=1e999"], .error 10),
    (opts ["-c", "AND=1.7976931348623159e308"], .error 10),
    (opts ["-c", "AND=1e-320"], .error 10),
    (opts ["-c", "AND=0x1p-1074"], .error 10),
    (opts ["-c", "AND=0x1p-1030"], .error 10),
    (opts ["-c", "AND=2.2250738585072011e-308"], .error 10),
    (opts ["-c", "AND=2.2250738585072012e-308"], .error 10),
    (opts ["-c", "AND=0x1.fffffffffffffp-1023"], .error 10),
    (opts ["-c", "AND=0"], .error 10),
    (opts ["-c", "AND=-1"], .error 10),
    (opts ["-c", "AND=nan"], .error 10),
    (opts ["-c", "AND=1e-400"], .error 10),
    (opts ["-c", "AND=2 "], .error 10),
    (opts ["-c", "AND=2x"], .error 10),
    (opts ["-c", "AND="], .error 10),
    (opts ["-c", "AND"], .error 10),
    (opts ["-c", "and=1"], .error 10),
    (opts ["-c", ",AND=1"], .error 10),
    (opts ["-c", "AND=1,,SIZE=2"], .error 10),
    (opts ["-c", "AND,SIZE=1"], .error 10),
    (opts ["-c", "AND=1;SIZE=2"], .error 10),
    (opts ["-c", "list"], .error 10),
    (opts ["-c", "AND=2", "-c", "FOO=1"], .error 10)]

end Cli

end JPoints

end
