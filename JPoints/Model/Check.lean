/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants
public import JPoints.Model.Kummer

-- The `#guard` examples run code of the imported modules at compile time.
meta import JPoints.Model.BruteForce
meta import JPoints.Model.Kummer

/-!
# The exact check of a triple

What `j-points` does with a triple `(a, b, c)` that the sieve leaves: `check_one_point` solves the
Kummer equation `K₂ d² + K₁ d + K₀ = 0` over the triple for the fourth coordinate `d`, by its
discriminant `K₁² - 4 K₀ K₂` (`JPoints.checkOnePoint`), and `check_one_point_final` takes each
rational solution `d = d₁ / d₂` to the point `(g a : g b : g c : u)` with `u / g = d` in lowest
terms and `g > 0`, tests the bound of the height on `g` and the bound on the fourth coordinate on
`u`, runs the lifting test, and prints and counts the point when it lifts
(`JPoints.checkOnePointFinal`): on machine words when the coordinates are at most `MAX_HEIGHT`
(`JPoints.checkOnePointWords`), on GMP integers otherwise (`JPoints.checkOnePointMpz`). What the
check reads from the globals is `JPoints.CheckGlobals`; what it writes, the text on `stdout` and the
count of the points found, is `JPoints.Output`.

## Main definitions

* `JPoints.CheckGlobals`: what the exact check reads from the globals.
* `JPoints.Output`, `JPoints.Output.print`: the output of the search and its count of points.
* `JPoints.checkOnePointWords`, `JPoints.checkOnePointMpz`: the check of a point on machine words
  and on GMP integers.
* `JPoints.checkOnePointFinal`: the check of the point over a triple for a root of its Kummer
  equation.
* `JPoints.checkOnePoint`: the check of a triple.

## Implementation notes

The GMP integers and the `long`s of the C code are integers, passed by value. The C code passes
pointers to scratch integers that the lifting test overwrites (`tmp` for `d1`), but
`check_one_point_final` reads its `d1` and `d2` before it calls the lifting test, and
`check_one_point` computes the second root from `ddd` and `kummer[1]`, which no callee writes, so
the values are those that the C code reads; the coefficient `kummer[2]`, which `check_one_point`
doubles in place before the first call, is a local of its own.

`m = max(a, |b|, |c|)` takes `a` itself, not `|a|`: the callers pass `a ≥ 0`, and `(a, b, c) ≠ 0`,
so that `m ≥ 1`. The bound `h = H / m` (`H` the height bound, or `MAX_HEIGHT` under `-a`) and the
comparison of `dbound` with `MAX_HEIGHT` are made in `unsigned long`s in the C code, the type of
`MAX_HEIGHT`; on the positive values of the calls they are those of the integers. Under `-a` the
point goes to the GMP integers when the scale `g` exceeds `MAX_HEIGHT / m`, with no bound on `g` at
all. The output of the check is threaded through it: it takes the output so far and returns it with
the points that it prints.
-/

@[expose] public section

namespace JPoints

/-! ### The globals and the output -/

/-- What the exact check reads from the globals of `j-points`: the curve searched, with its
coefficients `coeffs` and the flags `reversed` and `negated` (`JPoints.SearchCurve`), the
coefficients `k400, …, k004` of the quartic `K₀` (`JPoints.KummerCoeffs`), and the values that
`read_input` leaves in `height`, `dbound`, `dbounded`, `all_points`, `one_point` and `print_format`
(`JPoints.Cli.Input`): `1 ≤ height ≤ MAX_HEIGHT` and `dbound ≥ 1`, the value of `-w` or the height
bound. -/
structure CheckGlobals where
  /-- The curve searched, as `normalise_curve` leaves it. -/
  curve : SearchCurve
  /-- `k400, …, k004`, the coefficients of the quartic `K₀`, as `kummer_init` sets them. -/
  kummer : KummerCoeffs
  /-- `height`, the height bound. -/
  height : Int
  /-- `dbound`, the bound on the fourth coordinate: the value of `-w`, or the height bound. -/
  dbound : Int
  /-- `dbounded`, whether the fourth coordinate is bounded at all (not under `-a` without `-w`). -/
  dbounded : Bool
  /-- `all_points`, whether the bound is on the first three coordinates only (`-a`). -/
  allPoints : Bool
  /-- `one_point`, whether one point is enough (`-1`). -/
  onePoint : Bool
  /-- `print_format`, the format of the points (`-f`). -/
  printFormat : String

/-- The output of the search: the text that `j-points` prints on `stdout`, to which the exact check
appends each point that it finds, and the counter `total` of the points found.

C: `j-points.c:284`

Deviation: the text collected, for the output on `stdout`, which the program writes; a natural
number for the thread-local `long` `total` of the one thread, which starts at `0` and counts up. -/
structure Output where
  /-- The text printed so far. -/
  text : String := ""
  /-- `total`, the number of points found so far. -/
  total : Nat := 0
  deriving DecidableEq, Repr

/-- The output `out` with the text `s` printed after its text. -/
def Output.print (out : Output) (s : String) : Output := { out with text := out.text ++ s }

/-! ### The check of a point -/

/-- The check of the point over `(a, b, c)` with the fourth coordinate `u / v`, in lowest terms, on
machine words, as `check_one_point_final` makes it when `|u|` and `|v|` are within the bounds: the
point `(g a : g b : g c : d)` with `g = |v|`, and `d = u` for `v > 0` and `d = -u` for `v < 0`, and
when it lifts (`JPoints.checkLifts`), the point printed (`JPoints.Printf.emitPoint`) and counted.
Whether it was printed, and the output with it.

C: `j-points.c:2156-2158`, `j-points.c:2162-2163`, `j-points.c:2167-2172`, `j-points.c:2176-2178`

Deviation: integers for the `long`s `g`, `d`, `a`, `b` and `c`, which hold the values: `mpz_get_si`
of `cpf2` and `cpf1`, within the bounds `h` and `dmax`, and the products `g a`, `g b` and `g c`, at
most `m h ≤ MAX_HEIGHT` in absolute value; `u` and `v` by value, for the scratch integers `cpf1` and
`cpf2`; a Boolean for the `int` returned; the output taken and returned, for the thread-local
counter `total` and `stdout`. -/
def checkOnePointWords (gl : CheckGlobals) (out : Output) (a b c u v : Int) :
    Id (Bool × Output) := do
  let mut g := v
  let mut d := u
  if g < 0 then
    g := -g
    d := -d
  let a := a * g
  let b := b * g
  let c := c * g
  if ← checkLifts gl.curve.coeffs a b c d then
    let out :=
      out.print (Printf.emitPoint gl.curve.reversed gl.curve.negated gl.printFormat a b c d)
    return (true, { out with total := out.total + 1 })
  else
    return (false, out)

/-- The check of the point over `(a, b, c)` with the fourth coordinate `u / v`, in lowest terms, on
GMP integers, as `check_one_point_final` makes it when the coordinates may exceed a machine word:
`u` and `v` negated when `v < 0`, the point `(v a : v b : v c : u)`, and when it lifts
(`JPoints.checkLiftsMpz`), the point printed (`JPoints.Printf.printfMpz`) and counted. Whether it
was printed, and the output with it.

C: `j-points.c:2181-2184`, `j-points.c:2188-2193`, `j-points.c:2197-2202`, `j-points.c:2206-2208`

Deviation: integers for the `long`s `a`, `b` and `c` and for the GMP integers; `u` and `v` by value,
and locals `cpfa`, `cpfb` and `cpfc`, for the thread-local scratch integers; a Boolean for the `int`
returned; the output taken and returned, for the thread-local counter `total` and `stdout`. -/
def checkOnePointMpz (gl : CheckGlobals) (out : Output) (a b c u v : Int) :
    Id (Bool × Output) := do
  let mut cpf1 := u
  let mut cpf2 := v
  if cpf2 < 0 then
    cpf2 := -cpf2
    cpf1 := -cpf1
  let cpfa := cpf2 * a
  let cpfb := cpf2 * b
  let cpfc := cpf2 * c
  if ← checkLiftsMpz gl.curve.coeffs cpfa cpfb cpfc cpf1 then
    let s ← Printf.printfMpz gl.curve.reversed gl.curve.negated gl.printFormat cpfa cpfb cpfc cpf1
    let out := out.print s
    return (true, { out with total := out.total + 1 })
  else
    return (false, out)

/-- The check of `check_one_point_final` of the point over the triple `(a, b, c)` for the root
`d1 / d2` of its Kummer equation: for `m = max(a, |b|, |c|)`, the bound `h = H / m` on the scale of
the point (`H` the height bound, or `MAX_HEIGHT` under `-a`) and the bound `dmax` on its fourth
coordinate (`dbound` when it is bounded below `MAX_HEIGHT`, else `MAX_HEIGHT`), and `u / v` the root
in lowest terms: when `|u| ≤ dmax` and `|v| ≤ h`, the check on machine words
(`JPoints.checkOnePointWords`); else, when `u` keeps the bound of `-w` or the height bound (if the
fourth coordinate is bounded) and `|v| ≤ h` or `-a` is on, the check on GMP integers
(`JPoints.checkOnePointMpz`); else no point. Whether a point was printed, and the output with it.
The callers pass `a ≥ 0`, `(a, b, c) ≠ 0` and `d2 ≠ 0`.

C: `j-points.c:2135-2155`, `j-points.c:2179-2180`, `j-points.c:2209-2210`, `j-points.c:2214-2216`

Deviation: integers for the `long`s `a`, `b`, `c`, `m`, `h` and `dmax`, and for the GMP integers
`d1` and `d2`, these by value, for the pointers of the C code; the division `H / m` and the
comparison of `dbound` with `MAX_HEIGHT`, which the C code makes in `unsigned long`s, made in the
integers, where they agree for the `1 ≤ m ≤ height ≤ MAX_HEIGHT` and `dbound ≥ 1` of the calls;
`/` for `mpz_divexact`, which divides exactly; locals for the thread-local scratch integers `cpf1`,
`cpf2` and `cpf3`; Booleans for the `int` `dok` and for the `int` returned; the output taken and
returned, for the thread-local counter `total` and `stdout`; the two checks functions of their own.
-/
def checkOnePointFinal (gl : CheckGlobals) (out : Output) (a b c d1 d2 : Int) :
    Id (Bool × Output) := do
  let m : Int := if a > b.natAbs then (if a > c.natAbs then a else c.natAbs)
    else if b.natAbs > c.natAbs then b.natAbs else c.natAbs
  let h := (if gl.allPoints then (maxHeight : Int) else gl.height) / m
  let dmax : Int := if gl.dbounded && gl.dbound < maxHeight then gl.dbound else maxHeight
  let cpf3 : Int := d1.gcd d2
  let cpf1 := d1 / cpf3
  let cpf2 := d2 / cpf3
  let dok := !gl.dbounded || cpf1 ≤ gl.dbound && cpf1 ≥ -gl.dbound
  if cpf1 ≤ dmax ∧ cpf1 ≥ -dmax ∧ cpf2 ≤ h ∧ cpf2 ≥ -h then
    checkOnePointWords gl out a b c cpf1 cpf2
  else if dok ∧ (gl.allPoints ∨ cpf2 ≤ h ∧ cpf2 ≥ -h) then
    checkOnePointMpz gl out a b c cpf1 cpf2
  else
    return (false, out)

/-! ### The check of a triple -/

/-- The check of `check_one_point` of the triple `(a, b, c)`: the Kummer equation
`K₂ d² + K₁ d + K₀ = 0` over it (`JPoints.kummerEqn`), and by its discriminant `Δ = K₁² - 4 K₀ K₂`
the roots `d`, each checked by `JPoints.checkOnePointFinal`: for `Δ = 0`, the root `-K₁ / (2 K₂)`
(none when `K₂ = K₁ = 0`); for `Δ` a nonzero square (`JPoints.mpzPerfectSquareP`), the root
`-K₀ / K₁` when `K₂ = 0`, and otherwise `(√Δ - K₁) / (2 K₂)` and then `-(√Δ + K₁) / (2 K₂)`, but
not the second when the first gave a point and one point is enough (`-1`); none when `Δ` is not a
square. Whether the last check made printed a point, and the output with the points. The callers
pass `a ≥ 0`, `(a, b, c) ≠ 0` and `|a|, |b|, |c| ≤ height`, within which the `long` products of
`JPoints.kummerEqn` hold.

C: `j-points.c:2218-2222`, `j-points.c:2226-2230`, `j-points.c:2236-2237`, `j-points.c:2241-2242`,
`j-points.c:2246-2253`, `j-points.c:2257-2258`, `j-points.c:2262-2269`, `j-points.c:2275-2278`,
`j-points.c:2284-2288`, `j-points.c:2292-2295`

Deviation: integers for the `long`s `a`, `b` and `c` and for the GMP integers; locals for the
thread-local scratch integers `tmp`, `tmp2` and `ddd`, and `2 K₂` a local, for `kummer[2]`, which
the C code doubles in place; a Boolean for the `int` returned; the output taken and returned, for
the thread-local counter `total` and `stdout`. -/
def checkOnePoint (gl : CheckGlobals) (out : Output) (a b c : Int) : Id (Bool × Output) := do
  let k := kummerEqn gl.kummer gl.curve.coeffs a b c
  let tmp := k.k1 * k.k1 - k.k0 * k.k2 * 4
  if tmp == 0 then
    if k.k2 == 0 && k.k1 == 0 then return (false, out)
    let ddd := k.k2 * 2
    checkOnePointFinal gl out a b c (-k.k1) ddd
  else if mpzPerfectSquareP tmp then
    if k.k2 == 0 then return (← checkOnePointFinal gl out a b c (-k.k0) k.k1)
    let ddd : Int := tmp.toNat.sqrt
    let k2 := k.k2 * 2
    let (r, out) ← checkOnePointFinal gl out a b c (ddd - k.k1) k2
    if r && gl.onePoint then return (true, out)
    checkOnePointFinal gl out a b c (-(ddd + k.k1)) k2
  else
    return (false, out)

/-! ### Examples

From a test program that includes `j-points.c` of the pin, sets the globals as `read_input`,
`normalise_curve` and `kummer_init` leave them for a curve given and its options, and calls
`check_one_point` and `check_one_point_final`: the values that they return, the text that they
print and `total`. -/

-- The globals of the check for the curve `cs` of degree `d` given, the height bound `H`, the value
-- `W` of `-w` (`0` for none), `-a`, `-1` and the format of `-f`, as `read_input`,
-- `normalise_curve` and `kummer_init` leave them.
private def globalsOf (cs : Array Int) (d : Nat) (H W : Int) (all one : Bool) (fmt : String) :
    CheckGlobals :=
  let curve := (normalizeCurve cs d true).run.1
  { curve, kummer := kummerInit curve.coeffs, height := H, dbound := if W ≤ 0 then H else W,
    dbounded := W > 0 || !all, allPoints := all, onePoint := one, printFormat := fmt }

-- The check of the triples `ts` in turn, from the empty output: the values that it returns, and the
-- output.
private def checkTriples (gl : CheckGlobals) (ts : List (Int × Int × Int)) : List Bool × Output :=
  ts.foldl (fun (rs, out) (a, b, c) ↦
    let (r, out) := (checkOnePoint gl out a b c).run
    (rs ++ [r], out)) ([], {})

-- The triples of `JPoints.BruteForce.boxTriples n` in turn (every case of the discriminant occurs),
-- on curves searched as given, reversed, negated and both, the default and under `-a`, `-w` below
-- and above the height bound and `MAX_HEIGHT`, `-1`, and formats of `-f` with the flags that
-- `printf_mpz` rewrites for `gmp_printf` (`big`: points beyond the machine words, also on the
-- curves searched after a reversal (`rev`), a reversal and a negation (`revNeg`) and a negation
-- (`neg`)): the indices of the triples for which the check returns true, the number of the
-- triples, and the output.
#guard
  let big : Array Int := #[0, 400000000000000000000, -200000000060000000000,
    -399999999969999999998, 200000000059999999999, -30000000002, 1]
  let rev : Array Int := #[0, 1, -2, -100000000000000000001, 200000000000000000002,
    100000000000000000000, -200000000000000000000]
  let revNeg : Array Int := #[0, -1, -2, 100000000000000000001, 200000000000000000002,
    -100000000000000000000, -200000000000000000000]
  let neg : Array Int := #[-200000000000000000000, -100000000000000000000, 200000000000000000002,
    100000000000000000001, -2, -1, 0]
  ([
    (#[1, 178, 817, -274, 16, 1, 0], 5, 20, 0, false, false, "(%ld, %ld, %ld, %ld)\n", 5,
      [4, 6, 10], 577, "(0, 1, -2, 4)\n(0, 1, 0, 0)\n(0, 1, 4, 16)\n", 3),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 20, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 5,
      [4, 6, 10, 60, 78, 100, 118, 144], 577,
      "[0    |1|-2|4]\n[0    |1|+0|]\n[0    |1|+4|16]\n[5329 |-21316|+21316|291216]\n\
      [1    |-2|+0|-52]\n[1    |-2|+0|-125]\n[1    |0|+0|7104]\n[1    |2|-4|-348]\n\
      [4    |16|+0|197]\n[1    |4|+0|40]\n[1    |5|+2|138]\n", 11),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 60, 100000, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 4,
      [3, 5, 9, 46, 64, 78, 100], 289,
      "[0    |1|-2|4]\n[0    |1|+0|]\n[0    |1|+4|16]\n[1    |-2|+0|-52]\n[1    |-2|+0|-125]\n\
      [1    |0|+0|7104]\n[1    |2|-4|-348]\n[4    |16|+0|197]\n[1    |4|+0|40]\n", 9),
    (#[0, 1, 2, -1, 3, 1, 1], 6, 20, 0, false, false, "(%ld, %ld, %ld, %ld)\n", 5, [6, 100], 577,
      "(0, 1, 0, 0)\n(0, 0, 4, -11)\n", 2),
    (#[0, -1, 2, -1, 3, 1, 1], 6, 20, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 5, [6, 100], 577,
      "[0    |1|+0|]\n[0    |0|+4|-11]\n", 2),
    (#[3, 1, 0, -2, 0, -1, 0], 5, 10, 0, false, false, "(%ld, %ld, %ld, %ld)\n", 5, [5, 8, 109],
      577, "(0, 1, 1, -1)\n(0, 1, -2, -4)\n(1, -1, -2, -1)\n", 3),
    (#[21, 116, 171, 128, 55, 12, 1], 6, 60, 20, false, false, "(%ld, %ld, %ld, %ld)\n", 5, [0],
      577, "(0, 0, 1, -19)\n", 1),
    (#[21, 116, 171, 128, 55, 12, 1], 6, 20, 500, false, false, "(%ld, %ld, %ld, %ld)\n", 5,
      [0, 4, 57, 60, 61, 81], 577,
      "(0, 0, 1, -19)\n(0, 1, -2, 38)\n(0, 1, -2, 26)\n(1, -4, -3, 28)\n(1, -4, 1, -44)\n\
      (1, -4, 4, -91)\n(1, -4, 5, -116)\n(1, -2, -5, 64)\n(1, -2, 3, -112)\n", 9),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 8, 0, false, true, "(%ld, %ld, %ld, %ld)\n", 5, [79, 89, 100], 577,
      "(1, -2, 1, -6)\n(1, -1, 0, 4)\n(1, 0, 0, 1)\n", 3),
    (#[0, -2, 1, 3, -1, 2, 1], 6, 20, 0, false, false, "(%ld, %ld, %ld, %ld)\n", 4,
      [0, 5, 6, 11, 73, 126, 137, 138, 190, 206, 282], 289,
      "(0, 0, 1, 2)\n(0, 1, 0, 0)\n(0, 1, 1, 8)\n(0, 1, 1, 0)\n(0, 2, -1, 4)\n(0, 2, -1, -3)\n\
      (1, -2, -2, -2)\n(1, 1, 0, -2)\n(2, -1, 0, 8)\n(2, 1, -2, -4)\n(18, 9, -9, 2)\n\
      (2, 1, -1, -6)\n(3, -1, 1, 7)\n(3, 1, 2, 4)\n(4, 3, 2, 8)\n", 15),
    (big, 6, 10, 0, true, false, "[%24ld|%-3ld|%+ld|%ld] %%;", 3,
      [0, 3, 4, 5, 6, 33, 39, 45, 47, 54, 63], 145,
      "[                       0|0  |+1|24999999970000000002] %;\
      [                       0|1  |-1|-30000000004] %;[                       0|1  |+0|0] %;\
      [                       0|1  |+1|-30000000000] %;\
      [                       0|1  |+2|-119999999992] %;\
      [                       1|-1 |+0|-400000000000000000000] %;\
      [                       1|0  |-1|200000000059999999999] %;\
      [                       1|1  |-2|400000000059999999996] %;\
      [                       1|1  |+0|400000000000000000000] %;\
      [                       1|2  |+0|200000000000000000000] %;\
      [                       1|3  |+2|-399999999940000000004] %;", 11),
    (big, 6, 10, 1000000000000, false, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 3, [3, 4, 5, 6], 145,
      "[0    |1|-1|-30000000004]\n[0    |1|+0|]\n[0    |1|+1|-30000000000]\n\
      [0    |1|+2|-119999999992]\n", 4),
    (rev, 6, 5, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 3, [3, 5, 6, 39, 45, 63], 145,
      "[1    |-1|+0|-1]\n[1    |1|+0|1]\n[2    |1|+0|4]\n[1    |0|-1|200000000000000000002]\n\
      [2    |-1|-1|100000000000000000002]\n[2    |3|+1|99999999999999999998]\n", 6),
    (revNeg, 6, 5, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 3, [3, 5, 6, 39, 45, 63], 145,
      "[1    |1|+0|-1]\n[1    |-1|+0|1]\n[2    |-1|+0|4]\n[1    |0|-1|200000000000000000002]\n\
      [2    |1|-1|100000000000000000002]\n[2    |-3|+1|99999999999999999998]\n", 6),
    (neg, 5, 5, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n", 3, [3, 5, 6, 39, 45, 63], 145,
      "[0    |1|+1|-1]\n[0    |1|-1|-1]\n[0    |1|-2|-4]\n[1    |0|-1|-200000000000000000002]\n\
      [1    |-1|-2|-100000000000000000002]\n[1    |-3|+2|99999999999999999998]\n", 6)] :
    List (Array Int × Nat × Int × Int × Bool × Bool × String × Nat × List Nat × Nat × String ×
      Nat)).all fun (cs, d, H, W, all, one, fmt, n, is, k, t, tot) ↦
    let (rs, out) := checkTriples (globalsOf cs d H W all one fmt) (BruteForce.boxTriples n)
    ((rs.zipIdx.filter (·.1)).map (·.2), rs.length, out) == (is, k, ⟨t, tot⟩)

-- Points `(g : 0 : 0 : 1)` with `g` a square up to `MAX_HEIGHT` (machine words) and beyond (GMP
-- integers, only under `-a`), and `-1`, which leaves out the second root over `(1, -1, 0)`.
#guard ([
    (#[10000000000, 1, 0, 1, 2, 3, 5], 6, 10, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      [(1, 0, 0)], [true], "[40000000000|0|+0|1]\n", 1),
    (#[10000000000, 1, 0, 1, 2, 3, 5], 6, 10, 0, false, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      [(1, 0, 0)], [false], "", 0),
    (#[3036891664, 2, 0, 1, 2, 3, 5], 6, 10, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      [(1, 0, 0)], [true], "[3036891664|0|+0|1]\n", 1),
    (#[3037001881, 2, 0, 1, 2, 3, 5], 6, 10, 0, true, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      [(1, 0, 0)], [true], "[3037001881|0|+0|1]\n", 1),
    (#[3037001881, 2, 0, 1, 2, 3, 5], 6, 10, 0, false, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      [(1, 0, 0)], [false], "", 0),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 8, 0, false, true, "(%ld, %ld, %ld, %ld)\n",
      [(1, -1, 0), (1, -2, 1), (7, 6, 3), (1, 0, 0)], [true, true, true, true],
      "(1, -1, 0, 4)\n(1, -2, 1, -6)\n(7, 6, 3, -2)\n(1, 0, 0, 1)\n", 4),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 8, 0, false, false, "(%ld, %ld, %ld, %ld)\n",
      [(1, -1, 0), (1, -2, 1), (7, 6, 3), (1, 0, 0)], [true, true, true, true],
      "(1, -1, 0, 4)\n(1, -1, 0, -8)\n(1, -2, 1, -6)\n(7, 6, 3, -2)\n(1, 0, 0, 1)\n", 5)] :
    List (Array Int × Nat × Int × Int × Bool × Bool × String × List (Int × Int × Int) ×
      List Bool × String × Nat)).all fun (cs, d, H, W, all, one, fmt, ts, rs, t, tot) ↦
  checkTriples (globalsOf cs d H W all one fmt) ts == (rs, ⟨t, tot⟩)

-- `check_one_point_final` on the bounds: the point `(36 : -72 : 36 : -191)` over `(1, -2, 1)` with
-- the scale `36` at `h = 72 / 2` and beyond, under `-a`, and the fourth coordinate at the bound of
-- `-w` and beyond, also for a root `d1 / d2` not in lowest terms and with `d2 < 0`; the conversion
-- of `b` to an `unsigned long` in the lifting test on machine words; a fourth coordinate beyond
-- `MAX_HEIGHT`, through GMP integers, at the bound of `-w` and beyond, and under `-a`. The output
-- grows from the text and the count given.
#guard
  let big : Array Int := #[0, 400000000000000000000, -200000000060000000000,
    -399999999969999999998, 200000000059999999999, -30000000002, 1]
  ([
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 0, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36),
      false, ""),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 1000, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36),
      true, "(36, -72, 36, -191)\n"),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 71, 1000, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36),
      false, ""),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 71, 0, true, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36), true,
      "(36, -72, 36, -191)\n"),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 190, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36),
      false, ""),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 191, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, -191, 36),
      true, "(36, -72, 36, -191)\n"),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 1000, false, "(%ld, %ld, %ld, %ld)\n", (1, -2, 1, 382, -72),
      true, "(36, -72, 36, -191)\n"),
    (#[9, 4, 6, 5, 1, -4, -2], 6, 72, 1000, false, "[%-05ld|%ld|%+ ld|%.ld]\n",
      (1, -2, 1, -191, -36), false, ""),
    (#[3, 0, 0, 0, 0, 0, 1], 6, 5, 0, false, "(%ld, %ld, %ld, %ld)\n", (0, 1, 1, 0, 1), true,
      "(0, 1, 1, 0)\n"),
    (#[3, 0, 0, 0, 0, 0, 1], 6, 5, 0, false, "(%ld, %ld, %ld, %ld)\n", (0, -1, 1, 0, 1), false, ""),
    (big, 6, 10, 30000000004, false, "[%-05ld|%ld|%+ ld|%.ld]\n", (0, 1, -1, -30000000004, 1), true,
      "[0    |1|-1|-30000000004]\n"),
    (big, 6, 10, 30000000003, false, "[%-05ld|%ld|%+ ld|%.ld]\n", (0, 1, -1, -30000000004, 1),
      false, ""),
    (big, 6, 10, 0, false, "[%-05ld|%ld|%+ ld|%.ld]\n", (0, 1, -1, -30000000004, 1), false, ""),
    (big, 6, 10, 0, true, "[%-05ld|%ld|%+ ld|%.ld]\n", (0, 1, -1, 60000000008, -2), true,
      "[0    |1|-1|-30000000004]\n")] :
    List (Array Int × Nat × Int × Int × Bool × String × (Int × Int × Int × Int × Int) × Bool ×
      String)).all fun (cs, d, H, W, all, fmt, (a, b, c, d1, d2), r, t) ↦
    (checkOnePointFinal (globalsOf cs d H W all false fmt) ⟨"> ", 7⟩ a b c d1 d2).run ==
      (r, ⟨"> " ++ t, if r then 8 else 7⟩)

end JPoints

end
