/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Printf

-- The `#guard` examples run code of the imported modules and compare with the brute-force
-- reference at compile time.
meta import JPoints.Model.BruteForce
meta import JPoints.Model.Printf

/-!
# The Kummer surface and the lifting test

The arithmetic of `j-points` on the Kummer surface of the Jacobian of the curve `y² = f(x)`, in the
coordinates of Cassels and Flynn: the curve that the search runs on (`JPoints.normalizeCurve`: a
sextic with `f₀ = 0` and `f₁ = ±1` reversed into a quintic, and a quintic with leading coefficient
`-1` negated into a monic one, with the message that names the curve searched), the fifteen
coefficients of the quartic `K₀` of the equation of the Kummer surface (`JPoints.kummerInit`), the
coefficients of its equation `K₂ d² + K₁ d + K₀ = 0` in the fourth coordinate `d` over a triple
`(a, b, c)` (`JPoints.kummerEqn`), the test for common factors of the search for double points
(`JPoints.relprime`), and the test whether a point `(a : b : c : d)` of the Kummer surface comes
from a rational point of the Jacobian, on machine words (`JPoints.checkLifts`) and on GMP integers
(`JPoints.checkLiftsMpz`), with GMP's test for squares (`JPoints.mpzPerfectSquareP`).

## Main definitions

* `JPoints.SearchCurve`, `JPoints.normalizeCurve`: the curve that the search runs on, and the
  message that names it.
* `JPoints.KummerCoeffs`, `JPoints.kummerInit`: the coefficients of the quartic `K₀`.
* `JPoints.KummerEqn`, `JPoints.kummerEqn`: the Kummer equation over a triple.
* `JPoints.relprime`: the test for common factors by the binary algorithm.
* `JPoints.mpzPerfectSquareP`: the squares as GMP decides them.
* `JPoints.checkLifts`, `JPoints.checkLiftsMpz`: the lifting test, on machine words and on GMP
  integers.

## Implementation notes

The coefficients `f₀, …, f₆` of the curve are the array `coeffs` of the C code: an array of seven
integers, read with `coeffs[k]!`, with `f₆ = 0` for a quintic. The GMP integers of the C code are
integers, and so are its `long`s: where the C code multiplies two coordinates in `long`s
(`JPoints.kummerEqn`, `JPoints.checkLifts`), the model takes the integer product, which the `long`
holds when the coordinates are at most `JPoints.maxHeight` in absolute value, as they are at the
calls; the Deviations name these products. The scratch integers of the C code (`tmp`, `tmp2`,
`tmp3`, `x12`, `x22`, `x32`, `fff`, the arrays `bc` and `kummer`) are locals or results. The two
lifting tests are modeled each as the C code has it, each with the parts that compute
`b⁶ f(c / b)`, `A²` and `B²` as functions of their own, in the order of the products of the C code:
they differ in that order and in the conversion of `b` to an `unsigned long` in the machine-word
test, which is the identity for the `b > 0` with which the search calls it.
-/

@[expose] public section

namespace JPoints

/-! ### The curve searched -/

/-- The curve that the search runs on, as `normalise_curve` leaves the globals `coeffs`, `degree`,
`reversed` and `negated`.

C: `j-points.c:208`, `j-points.c:254`, `j-points.c:258`

Deviation: an array of integers for the array of GMP integers, a natural number for the `long`
`degree` and Booleans for the `int` flags, in a structure, for the globals; the initializers `0` of
the flags are the values `false` from which `JPoints.normalizeCurve` starts them. -/
structure SearchCurve where
  /-- The coefficients `f₀, …, f₆` of the curve searched, `coeffs[k]` for `fₖ`. -/
  coeffs : Array Int
  /-- The degree of the curve searched, `5` or `6`. -/
  degree : Nat
  /-- Whether the curve given was reversed, by `x ↦ 1 / x`. -/
  reversed : Bool
  /-- Whether the curve was negated, by `x ↦ -x`, after the reversal if there was one. -/
  negated : Bool
  deriving DecidableEq, Repr

/-- The curve that the search runs on, for the coefficients `coeffs` and the degree `degree` of the
curve given, and the message that `normalise_curve` prints: a sextic with `f₀ = 0` and `|f₁| = 1` is
reversed, `fᵢ` and `f₆₋ᵢ` exchanged for `i < 3`, into a quintic with `f₅ = f₁`; then a quintic with
`f₅ = -1` is negated, its odd coefficients negated, into a monic one; and when the curve was
transformed and `quiet` is off, the message names the curve searched
(`JPoints.Printf.printPoly`) and the transformations.

C: `j-points.c:583-594`, `j-points.c:595-601`, `j-points.c:602-603`

Deviation: the curve and the flags returned, for the globals that the C code writes, the flags
starting from `false`, the values `0` of their initializers; a natural number for the `long`
`degree`; a Boolean for the `int` `quiet`, and an argument for this global; the text of the message
returned, which the caller writes to `stdout`. -/
def normalizeCurve (coeffs : Array Int) (degree : Nat) (quiet : Bool) :
    Id (SearchCurve × String) := do
  let mut coeffs := coeffs
  let mut degree := degree
  let mut reversed := false
  let mut negated := false
  if degree == 6 && coeffs[0]! == 0 && coeffs[1]!.natAbs == 1 then
    for i in [0:3] do coeffs := coeffs.swapIfInBounds i (6 - i)
    degree := 5
    reversed := true
  if degree == 5 && coeffs[5]! == -1 then
    for i in [1:6:2] do coeffs := coeffs.set! i (-coeffs[i]!)
    negated := true
  let mut text := ""
  if (reversed || negated) && !quiet then
    text := "The search runs on y^2 = " ++ (← Printf.printPoly coeffs degree) ++
      "(the curve under " ++ (if reversed then "x -> 1/x" else "") ++
      (if reversed && negated then " and " else "") ++ (if negated then "x -> -x" else "") ++
      "), a monic quintic, and the points are\ntransformed back.\n\n"
  return ({ coeffs, degree, reversed, negated }, text)

/-! ### The equation of the Kummer surface -/

/-- The fifteen coefficients of the quartic `K₀` of the equation of the Kummer surface, `kᵢⱼₖ` the
coefficient of `x₁ⁱ x₂ʲ x₃ᵏ`: the globals `k400, …, k004` that `kummer_init` sets.

C: `j-points.c:213-214`

Deviation: integers for the GMP integers, in a structure, for the fifteen globals. -/
structure KummerCoeffs where
  /-- `k400 = f₁² - 4 f₀ f₂`. -/
  k400 : Int
  /-- `k310 = -4 f₀ f₃`. -/
  k310 : Int
  /-- `k301 = -2 f₁ f₃`. -/
  k301 : Int
  /-- `k220 = -4 f₀ f₄`. -/
  k220 : Int
  /-- `k211 = 4 (f₀ f₅ - f₁ f₄)`. -/
  k211 : Int
  /-- `k202 = f₃² - 4 f₂ f₄ + 2 f₁ f₅ - 4 f₀ f₆`. -/
  k202 : Int
  /-- `k130 = -4 f₀ f₅`. -/
  k130 : Int
  /-- `k121 = 8 f₀ f₆ - 4 f₁ f₅`. -/
  k121 : Int
  /-- `k112 = 4 (f₁ f₆ - f₂ f₅)`. -/
  k112 : Int
  /-- `k103 = -2 f₃ f₅`. -/
  k103 : Int
  /-- `k040 = -4 f₀ f₆`. -/
  k040 : Int
  /-- `k031 = -4 f₁ f₆`. -/
  k031 : Int
  /-- `k022 = -4 f₂ f₆`. -/
  k022 : Int
  /-- `k013 = -4 f₃ f₆`. -/
  k013 : Int
  /-- `k004 = f₅² - 4 f₄ f₆`. -/
  k004 : Int
  deriving DecidableEq, Repr

/-- The coefficients of the quartic `K₀` for the coefficients `coeffs` of the curve searched, each
computed as `kummer_init` computes it.

C: `j-points.c:1411-1453`

Deviation: the coefficients returned in a structure, for the fifteen globals that the C code sets;
integers for the GMP integers, without the scratch integer `tmp`. -/
def kummerInit (coeffs : Array Int) : KummerCoeffs where
  k400 := coeffs[1]! * coeffs[1]! - coeffs[0]! * coeffs[2]! * 4
  k310 := coeffs[0]! * coeffs[3]! * -4
  k301 := coeffs[1]! * coeffs[3]! * -2
  k220 := coeffs[0]! * coeffs[4]! * -4
  k211 := (coeffs[0]! * coeffs[5]! - coeffs[1]! * coeffs[4]!) * 4
  k202 := coeffs[3]! * coeffs[3]! - coeffs[2]! * coeffs[4]! * 4 + coeffs[1]! * coeffs[5]! * 2 -
    coeffs[0]! * coeffs[6]! * 4
  k130 := coeffs[0]! * coeffs[5]! * -4
  k121 := coeffs[0]! * coeffs[6]! * 8 - coeffs[1]! * coeffs[5]! * 4
  k112 := (coeffs[1]! * coeffs[6]! - coeffs[2]! * coeffs[5]!) * 4
  k103 := coeffs[3]! * coeffs[5]! * -2
  k040 := coeffs[0]! * coeffs[6]! * -4
  k031 := coeffs[1]! * coeffs[6]! * -4
  k022 := coeffs[2]! * coeffs[6]! * -4
  k013 := coeffs[3]! * coeffs[6]! * -4
  k004 := coeffs[5]! * coeffs[5]! - coeffs[4]! * coeffs[6]! * 4

/-- The coefficients of the Kummer equation `K₂ d² + K₁ d + K₀ = 0` in the fourth coordinate `d`
over a triple `(a, b, c)`: the array `kummer` that `kummer_eqn` fills.

C: `j-points.c:217`

Deviation: a structure of three integers, for the thread-local array of three GMP integers. -/
structure KummerEqn where
  /-- `kummer[0]`, the constant term `K₀`, the value of the quartic at `(a, b, c)`. -/
  k0 : Int
  /-- `kummer[1]`, the coefficient `K₁` of `d`. -/
  k1 : Int
  /-- `kummer[2]`, the coefficient `K₂ = b² - 4ac` of `d²`. -/
  k2 : Int
  deriving DecidableEq, Repr

/-- The Kummer equation over `(a, b, c)`, for the coefficients `k` of the quartic and the
coefficients `coeffs` of the curve searched, as `kummer_eqn` computes it from the products
`aa, bb, cc, ab, ac, bc` of two coordinates: `K₀` as the sum of three linear forms in them, times
`aa`, `bb` and `cc`;
`K₁ = (f₀ aa + f₂ ac) (-4a) + (f₁ aa + f₃ ac + f₅ cc) (-2b) + (f₄ ac + f₆ cc) (-4c)`; and
`K₂ = bb - 4 ac`.

C: `j-points.c:1749-1805`

Deviation: integers for the `long`s: the products `aa, …, bc` and the factors `-4a`, `-2b`, `-4c`
are `long`s in the C code, which hold them for `|a|, |b|, |c| ≤ JPoints.maxHeight`, as the comment
of the function requires and its callers ensure; the equation returned in a structure, for the
thread-local array `kummer` that the C code fills; no scratch integer `tmp`. -/
def kummerEqn (k : KummerCoeffs) (coeffs : Array Int) (a b c : Int) : KummerEqn :=
  let aa := a * a
  let bb := b * b
  let cc := c * c
  let ab := a * b
  let ac := a * c
  let bc := b * c
  let e0 := (k.k400 * aa + k.k310 * ab + k.k301 * ac + k.k220 * bb + k.k211 * bc +
    k.k202 * cc) * aa
  let e1 := (k.k130 * ab + k.k121 * ac + k.k040 * bb + k.k031 * bc + k.k022 * cc) * bb
  let e2 := (k.k112 * ab + k.k103 * ac + k.k013 * bc + k.k004 * cc) * cc
  { k0 := e0 + e1 + e2
    k1 := (coeffs[0]! * aa + coeffs[2]! * ac) * (-4 * a) +
      (coeffs[1]! * aa + coeffs[3]! * ac + coeffs[5]! * cc) * (-2 * b) +
      (coeffs[4]! * ac + coeffs[6]! * cc) * (-4 * c)
    k2 := bb - ac * 4 }

/-! ### The test for common factors -/

/-- Whether `gcd(n, m) = 1`, for `n ≥ 0`, by the binary algorithm of `relprime`: for `m = 0`,
whether `n = 1`; otherwise `m` replaced by `|m|`, for `n = 0` whether `|m| = 1`, false when both are
even, and else both replaced by their odd parts and, while they differ, the larger replaced by the
odd part of the difference, until both are the odd part of the gcd, which is `1` when they are
coprime.

C: `j-points.c:1811-1832`

Deviation: integers for the `long`s, so that the negation of `m = -2 ^ 63`, which overflows in the C
code, is exact (the callers pass `|m| ≤ ⌊√H⌋`); `x % 2 == 0` for `!(x & 1)`, which agree on every
`long` in two's complement; `x >>> 1`, the floor of `x / 2`, for `x >>= 1`, which gcc computes so
also for a negative `long`; a Boolean for the `int`. -/
-- lint: allow long-proof: a line of the model for each line of `relprime`, as in the C code
def relprime (n m : Int) : Id Bool := do
  if m == 0 then return n == 1
  let mut n := n
  let mut m := m
  if m < 0 then m := -m
  if n == 0 then return m == 1
  if m % 2 == 0 then
    if n % 2 == 0 then return false
    m := m >>> 1
    while m % 2 == 0 do m := m >>> 1
  while n % 2 == 0 do n := n >>> 1
  while n != m do
    if n > m then
      n := n - m
      n := n >>> 1
      while n % 2 == 0 do n := n >>> 1
    else
      m := m - n
      m := m >>> 1
      while m % 2 == 0 do m := m >>> 1
  return m == 1

/-! ### The lifting test -/

/-- Whether `n` is a square, as `mpz_perfect_square_p` of GMP decides it: `0` and the squares of the
positive integers, so that no negative integer is a square. -/
def mpzPerfectSquareP (n : Int) : Bool := 0 ≤ n && n.toNat.sqrt * n.toNat.sqrt == n.toNat

/-- The value `F(c, b) = b⁶ f(c / b) = f₆ c⁶ + f₅ c⁵ b + ⋯ + f₀ b⁶` that `check_lifts` computes for
a point `(0 : b : c : d)`: the products `bc[k] = fₖ b⁶⁻ᵏ` for `k = 5, …, 0`, by repeated
multiplication with `b`, and then Horner's rule in `c` from `f₆`.

C: `j-points.c:1857-1868`

Deviation: integers for the `long`s `b` and `c`; a fresh array for the thread-local array `bc`,
whose entries `0, …, 5` the first loop writes before the second reads them; the steps of the loops
counted up, for the index `k` that counts down from `5`; the value returned, for the scratch integer
`fff`. -/
def checkLiftsForm (coeffs : Array Int) (b c : Int) : Id Int := do
  let mut tmp : Int := 1
  let mut bc : Array Int := Array.replicate 7 0
  for i in [0:6] do
    let k := 5 - i
    tmp := tmp * b
    bc := bc.set! k (coeffs[k]! * tmp)
  let mut fff := coeffs[6]!
  for i in [0:6] do
    let k := 5 - i
    fff := fff * c
    fff := fff + bc[k]!
  return fff

/-- The value `A² = a³ d + f₂ a⁴ + f₃ a³ b + f₄ a² b² + f₅ a b (b² - ac) + f₆ (b² - ac)²` that
`check_lifts` computes for a point `(a : b : c : d)` with `a ≠ 0`, from `x12 = a²` and `x22 = b²`.

C: `j-points.c:1881-1900`

Deviation: integers for the `long`s: the products `a d` and `a b` are `long`s in the C code, which
hold them for `|a|, |b|, |d| ≤ JPoints.maxHeight`, as the callers ensure (`b² - ac`, which can
exceed a `long`, is a GMP integer there); the value returned, for the scratch integer `tmp`,
without the scratch integers `tmp2` and `tmp3`. -/
def checkLiftsA2 (coeffs : Array Int) (a b c d x12 x22 : Int) : Int :=
  let tmp3 := b * b - a * c
  x12 * (a * d) + x12 * x12 * coeffs[2]! + x12 * (a * b) * coeffs[3]! + x12 * x22 * coeffs[4]! +
    coeffs[5]! * tmp3 * (a * b) + coeffs[6]! * tmp3 * tmp3

/-- The value `B² = a² c d + f₀ a⁴ + f₄ a² c² + f₅ a b c² + f₆ b² c²` that `check_lifts` computes
for a point `(a : b : c : d)` with `a ≠ 0` and `A² = 0`, from `x12 = a²`, `x22 = b²` and
`x32 = c²`.

C: `j-points.c:1908-1920`

Deviation: integers for the `long`s: the products `c d` and `a b` are `long`s in the C code, which
hold them for `|a|, |b|, |c|, |d| ≤ JPoints.maxHeight`, as the callers ensure; the value returned,
for the scratch integer `tmp`, without the scratch integer `tmp2`. -/
def checkLiftsB2 (coeffs : Array Int) (a b c d x12 x22 x32 : Int) : Int :=
  x12 * (c * d) + x12 * x12 * coeffs[0]! + x12 * x32 * coeffs[4]! + coeffs[5]! * x32 * (a * b) +
    x22 * x32 * coeffs[6]!

/-- The lifting test of `check_lifts` on the point `(a : b : c : d)` of the Kummer surface of the
curve searched, of coefficients `coeffs`, given by machine words: the origin `(0 : 0 : 0 : d)`
lifts; `(0 : 0 : c : d)` lifts when `f₆` is a square; `(0 : b : c : d)` with `b ≠ 0` when `f₆` and
`b⁶ f(c / b)` (`JPoints.checkLiftsForm`) are squares (`JPoints.mpzPerfectSquareP`, which counts `0`
as a square); and for `a ≠ 0`, when `A²` (`JPoints.checkLiftsA2`) is a square, and if it is `0`,
when `B²` (`JPoints.checkLiftsB2`) is one.

C: `j-points.c:1839-1855`, `j-points.c:1869-1879`, `j-points.c:1905-1906`, `j-points.c:1924-1926`

Deviation: integers for the `long`s: the squares `a²`, `b²` and `c²` are `long`s in the C code,
which hold them for `|a|, |b|, |c| ≤ JPoints.maxHeight`, as `check_one_point_final` ensures;
`x12`, `x22` and `x32` locals, for the thread-local scratch integers; the computations of
`b⁶ f(c / b)`, `A²` and `B²` functions of their own; a Boolean for the `int`. -/
def checkLifts (coeffs : Array Int) (a b c d : Int) : Id Bool := do
  if a == 0 then
    if b == 0 then
      if c == 0 then return true
      else return mpzPerfectSquareP coeffs[6]!
    else
      if !(coeffs[6]! == 0 || mpzPerfectSquareP coeffs[6]!) then return false
      let fff ← checkLiftsForm coeffs b c
      return fff == 0 || mpzPerfectSquareP fff
  else
    let x12 := a * a
    let x22 := b * b
    let x32 := c * c
    let tmp := checkLiftsA2 coeffs a b c d x12 x22
    if tmp != 0 then return mpzPerfectSquareP tmp
    let tmp := checkLiftsB2 coeffs a b c d x12 x22 x32
    return tmp == 0 || mpzPerfectSquareP tmp

/-- The value `F(c, b) = b⁶ f(c / b)` that `check_lifts_mpz` computes for a point `(0 : b : c : d)`
given by GMP integers: the products `bc[k] = fₖ b⁶⁻ᵏ` for `k = 5, …, 0`, by repeated
multiplication with `b`, and then Horner's rule in `c` from `f₆`.

C: `j-points.c:1946-1957`

Deviation: a fresh array for the thread-local array `bc`, whose entries `0, …, 5` the first loop
writes before the second reads them; the steps of the loops counted up, for the index `k` that
counts down from `5`; the value returned, for the scratch integer `fff`. -/
def checkLiftsMpzForm (coeffs : Array Int) (b c : Int) : Id Int := do
  let mut tmp : Int := 1
  let mut bc : Array Int := Array.replicate 7 0
  for i in [0:6] do
    let k := 5 - i
    tmp := tmp * b
    bc := bc.set! k (coeffs[k]! * tmp)
  let mut fff := coeffs[6]!
  for i in [0:6] do
    let k := 5 - i
    fff := fff * c
    fff := fff + bc[k]!
  return fff

/-- The value `A² = a³ d + f₂ a⁴ + f₃ a³ b + f₄ a² b² + f₅ a b (b² - ac) + f₆ (b² - ac)²` that
`check_lifts_mpz` computes for a point `(a : b : c : d)` with `a ≠ 0`, from `x12 = a²` and
`x22 = b²`, in the order of its products.

C: `j-points.c:1970-1986`

Deviation: the value returned, for the scratch integer `tmp`, without the scratch integers `tmp2`
and `tmp3`. -/
def checkLiftsMpzA2 (coeffs : Array Int) (a b c d x12 x22 : Int) : Int :=
  let tmp3 := x22 - a * c
  x12 * a * d + x12 * x12 * coeffs[2]! + x12 * a * b * coeffs[3]! + x12 * x22 * coeffs[4]! +
    coeffs[5]! * tmp3 * a * b + coeffs[6]! * tmp3 * tmp3

/-- The value `B² = a² c d + f₀ a⁴ + f₄ a² c² + f₅ a b c² + f₆ b² c²` that `check_lifts_mpz`
computes for a point `(a : b : c : d)` with `a ≠ 0` and `A² = 0`, from `x12 = a²`, `x22 = b²` and
`x32 = c²`, in the order of its products.

C: `j-points.c:1994-2006`

Deviation: the value returned, for the scratch integer `tmp`, without the scratch integer `tmp2`. -/
def checkLiftsMpzB2 (coeffs : Array Int) (a b c d x12 x22 x32 : Int) : Int :=
  x12 * c * d + x12 * x12 * coeffs[0]! + x12 * x32 * coeffs[4]! + coeffs[5]! * x32 * a * b +
    x22 * x32 * coeffs[6]!

/-- The lifting test of `check_lifts_mpz` on the point `(a : b : c : d)` of the Kummer surface of
the curve searched, of coefficients `coeffs`, given by GMP integers: the test of
`JPoints.checkLifts`, with `b⁶ f(c / b)` (`JPoints.checkLiftsMpzForm`), `A²`
(`JPoints.checkLiftsMpzA2`) and `B²` (`JPoints.checkLiftsMpzB2`) in GMP integers throughout.

C: `j-points.c:1928-1944`, `j-points.c:1958-1968`, `j-points.c:1991-1992`, `j-points.c:2010-2012`

Deviation: integers for the GMP integers, the arguments passed by value, for the pointers;
`x12`, `x22` and `x32` locals, for the thread-local scratch integers; the computations of
`b⁶ f(c / b)`, `A²` and `B²` functions of their own; a Boolean for the `int`. -/
def checkLiftsMpz (coeffs : Array Int) (a b c d : Int) : Id Bool := do
  if a == 0 then
    if b == 0 then
      if c == 0 then return true
      else return mpzPerfectSquareP coeffs[6]!
    else
      if !(coeffs[6]! == 0 || mpzPerfectSquareP coeffs[6]!) then return false
      let fff ← checkLiftsMpzForm coeffs b c
      return fff == 0 || mpzPerfectSquareP fff
  else
    let x12 := a * a
    let x22 := b * b
    let x32 := c * c
    let tmp := checkLiftsMpzA2 coeffs a b c d x12 x22
    if tmp != 0 then return mpzPerfectSquareP tmp
    let tmp := checkLiftsMpzB2 coeffs a b c d x12 x22 x32
    return tmp == 0 || mpzPerfectSquareP tmp

/-! ### Examples

The values of the C code at the pin, from a test program that calls `normalise_curve`,
`kummer_init`, `kummer_eqn`, `relprime`, `check_lifts` and `check_lifts_mpz` of `j-points.c`
directly; where an example compares with the brute-force reference (`JPoints.BruteForce`) or with
the gcd, the C code gives the same values on the same arguments. -/

-- A reversal; a reversal and a negation; the same for two sextics with `f₆ = -1`; a negation; both
-- on the curve of the run of `test3.sh` that names them; and the messages, which `-q` leaves out.
#guard ([(#[0, 1, 2, 3, 4, 5, 6], 6, ⟨#[6, 5, 4, 3, 2, 1, 0], 5, true, false⟩,
      "x^5 + 2 x^4 + 3 x^3 + 4 x^2 + 5 x + 6\n(the curve under x -> 1/x)"),
    (#[0, -1, 2, 3, 4, 5, 6], 6, ⟨#[6, -5, 4, -3, 2, 1, 0], 5, true, true⟩,
      "x^5 + 2 x^4 - 3 x^3 + 4 x^2 - 5 x + 6\n(the curve under x -> 1/x and x -> -x)"),
    (#[0, -1, 2, 3, 4, 1, -1], 6, ⟨#[-1, -1, 4, -3, 2, 1, 0], 5, true, true⟩,
      "x^5 + 2 x^4 - 3 x^3 + 4 x^2 - x - 1\n(the curve under x -> 1/x and x -> -x)"),
    (#[0, 1, 2, 3, 4, -1, -1], 6, ⟨#[-1, -1, 4, 3, 2, 1, 0], 5, true, false⟩,
      "x^5 + 2 x^4 + 3 x^3 + 4 x^2 - x - 1\n(the curve under x -> 1/x)"),
    (#[5, -2, 3, 1, -1, -1, 0], 5, ⟨#[5, 2, 3, -1, -1, 1, 0], 5, false, true⟩,
      "x^5 - x^4 - x^3 + 3 x^2 + 2 x + 5\n(the curve under x -> -x)"),
    (#[0, -1, 2, -1, 3, 1, 1], 6, ⟨#[1, -1, 3, 1, 2, 1, 0], 5, true, true⟩,
      "x^5 + 2 x^4 + x^3 + 3 x^2 - x + 1\n(the curve under x -> 1/x and x -> -x)")] :
    List (Array Int × Nat × SearchCurve × String)).all fun (cs, d, r, m) ↦
  (normalizeCurve cs d false).run == (r, "The search runs on y^2 = " ++ m ++
    ", a monic quintic, and the points are\ntransformed back.\n\n") &&
    (normalizeCurve cs d true).run == (r, "")

-- Curves searched as given, with no message: `f₁ = 2`; a sextic; a quintic with `f₀ = 0`; quintics
-- with `f₅ ≠ -1`.
#guard [(#[0, 2, 3, 4, 5, 6, 7], 6), (#[1, 4, 3, -8, 2, 8, 7], 6), (#[0, 1, -3, 2, 1, 1, 0], 5),
    (#[1, 178, 817, -274, 16, 1, 0], 5), (#[3, -1, 0, 2, -3, -3, 0], 5),
    (#[3, 1, 0, -2, 0, 1, 0], 5)].all
  fun (cs, d) ↦ [false, true].all fun q ↦ (normalizeCurve cs d q).run == (⟨cs, d, false, false⟩, "")

#guard kummerInit #[1, 4, 3, -8, 2, 8, 7] ==
  ⟨4, 32, 64, -8, 0, 76, -32, -72, 16, 128, -28, -112, -84, 224, 8⟩
#guard kummerInit #[1, 178, 817, -274, 16, 1, 0] ==
  ⟨28416, 1096, 97544, -64, -11388, 23144, -4, -712, -3268, 548, 0, 0, 0, 0, 1⟩
#guard kummerInit
    #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800] ==
  ⟨409912278901312000, -2374453099817526400, 4724539618195256480, -52012806008462400,
    -258915714593900640, 6467345615926614400, 465899430262464000, -1690833774606969600,
    741928713302792160, 2252925735698769120, -81600924309120000, 324728923733568000,
    -186821969399092800, -789186723534979200, 203739796934438400⟩
#guard kummerInit #[123456789012345678901, 2, -3, 1, 4, -1, 3] ==
  ⟨1481481468148148146816, -493827156049382715604, -4, -1975308624197530862416,
    -493827156049382715636, -1481481468148148146767, 493827156049382715604,
    2962962936296296293632, 12, 2, -1481481468148148146812, -24, 36, -12, -47⟩

#guard kummerEqn (kummerInit #[1, 4, 3, -8, 2, 8, 7]) #[1, 4, 3, -8, 2, 8, 7] 7 6 3 ==
  ⟨-11000, -5596, -48⟩
#guard kummerEqn (kummerInit #[1, 4, 3, -8, 2, 8, 7]) #[1, 4, 3, -8, 2, 8, 7] 0 0 1 == ⟨8, -28, 0⟩
#guard kummerEqn (kummerInit #[1, 4, 3, -8, 2, 8, 7]) #[1, 4, 3, -8, 2, 8, 7] 0 1 0 == ⟨-28, 0, 1⟩
#guard kummerEqn (kummerInit #[1, 178, 817, -274, 16, 1, 0]) #[1, 178, 817, -274, 16, 1, 0]
    4 (-12) 9 == ⟨122790897, -658024, 0⟩

-- Coordinates of absolute value `JPoints.maxHeight`, and `K₂` beyond the range of a `long`.
#guard kummerEqn (kummerInit #[1, 4, 3, -8, 2, 8, 7]) #[1, 4, 3, -8, 2, 8, 7]
    3037000499 (-3037000499) 3037000498 ==
  ⟨-3402823659232626876683262737197251324560, -1232500959371525397784243199756,
    -27670116080630745007⟩
#guard kummerEqn (kummerInit #[1, 4, 3, -8, 2, 8, 7]) #[1, 4, 3, -8, 2, 8, 7]
    1 (-3037000499) (-3037000499) ==
  ⟨680564731846525375476847802056850808216, 1232500960330756088830501067940,
    9223372043074250997⟩
#guard kummerEqn
    (kummerInit #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800])
    #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800]
    3037000499 (-3037000499) 3037000498 ==
  ⟨1185645171873092224502110290562865326791517835545129389760,
    -53757682553726716563477344730142130656, -27670116080630745007⟩

-- The Kummer equation of the brute-force reference, on the triples of the cube `[-4, 4]³`.
#guard [#[1, 4, 3, -8, 2, 8, 7], #[1, 178, 817, -274, 16, 1, 0],
    #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800]].all fun cs ↦
  (BruteForce.intRange 4).all fun a ↦ (BruteForce.intRange 4).all fun b ↦
    (BruteForce.intRange 4).all fun c ↦
      let e := kummerEqn (kummerInit cs) cs a b c
      BruteForce.kummerCoeffs cs.toList a b c == (e.k2, e.k1, e.k0)

#guard [(1, 0, true), (2, 0, false), (0, 0, false), (0, 6, false), (0, 1, true), (0, -1, true),
    (0, 5, false), (5, 9, true), (6, 9, false), (8, -12, false), (9, -12, false), (12, -18, false),
    (35, -64, true), (64, 35, true), (7, 7, false), (1, 1, true), (1, -1, true), (1, -55108, true),
    (55108, -55107, true), (55108, -27554, false), (46341, -32768, true), (32768, 46341, true),
    (3037000499, -1518500249, true), (3037000498, -1518500249, false)].all
  fun (n, m, r) ↦ (relprime n m).run == r

-- The gcd, for `0 ≤ n ≤ 60` and `|m| ≤ 60`.
#guard (List.range 61).all fun n ↦ (BruteForce.intRange 60).all fun m ↦
  (relprime n m).run == (Int.gcd n m == 1)

#guard [(0, true), (1, true), (4, true), (2, false), (-1, false), (-4, false),
    (10 ^ 40, true), (10 ^ 40 + 1, false), ((2 ^ 64 - 1) ^ 2, true)].all
  fun (n, r) ↦ mpzPerfectSquareP n == r

-- `f₆ = 1`: the origin, points with `a = 0` (`b⁶ f(c / b)` a square, and not).
#guard [((0, 0, 0, 5), true), ((0, 0, 1, 26), true), ((0, 1, 0, 4), true),
    ((0, 2, -3, 0), false)].all
  fun ((a, b, c, d), r) ↦ (checkLifts #[4, -6, 10, 8, -1, -10, 1] a b c d).run == r

-- `f₆ = 7`: the origin, `a = 0` (`f₆` not a square); `A²` a square, not a square, negative, and
-- `A² = 0` with `B²` a square and negative; coordinates of absolute value `JPoints.maxHeight`.
#guard [((0, 0, 0, 5), true), ((0, 0, 1, 8), false), ((0, 1, 0, -4), false),
    ((1, -2, 1, -6), true), ((7, 6, -9, -74), true), ((1, -2, 1, -5), false),
    ((1, 0, 0, -10), false), ((1, 0, 0, -3), true), ((1, 1, 0, -12), true),
    ((1, 0, 1, -10), false), ((3037000499, 0, 0, 3037000499), true),
    ((3037000499, -3037000499, 3037000499, -3037000499), false)].all
  fun ((a, b, c, d), r) ↦ (checkLifts #[1, 4, 3, -8, 2, 8, 7] a b c d).run == r

-- `A² = 0` and `B² = 0`; `A² = 0` and `B² = 3`.
#guard (checkLifts #[0, 1, 2, -1, 3, 1, 1] 1 0 0 (-2)).run
#guard !(checkLifts #[3, -1, 2, 5, -4, 1, 4] 1 0 0 (-2)).run

-- `y² = x⁶ + 3`, `(0 : b : c : 0)`: `F(1, b) = 1 + 3 b⁶` is the square `4` for `b = ±1` and `193`
-- for `b = ±2`, `F(0, -1) = 3` is not a square.
#guard [((0, 1, 1, 0), true), ((0, -1, 1, 0), true), ((0, 2, 1, 0), false), ((0, -2, 1, 0), false),
    ((0, -1, 0, 0), false)].all
  fun ((a, b, c, d), r) ↦ (checkLifts #[3, 0, 0, 0, 0, 0, 1] a b c d).run == r
#guard (checkLiftsMpz #[3, 0, 0, 0, 0, 0, 1] 0 (-1) 1 0).run

-- Beyond the machine words: points with `a = 0`, and multiples by `10 ^ 15` and `10 ^ 12` of points
-- with `A²` a square, not a square and negative, and with `A² = 0` and `B²` a square, negative, `0`
-- and not a square.
#guard [((0, 0, 0, 0), true), ((0, 0, 5, 1), true), ((0, 10 ^ 20, 0, 4 * 10 ^ 20), true),
    ((0, 10 ^ 20, -3 * 10 ^ 20, 0), false)].all
  fun ((a, b, c, d), r) ↦ (checkLiftsMpz #[4, -6, 10, 8, -1, -10, 1] a b c d).run == r
#guard [((0, 0, 5, 1), false), ((0, 1, 0, 1), false),
    ((7 * 10 ^ 15, 6 * 10 ^ 15, -9 * 10 ^ 15, -74 * 10 ^ 15), true),
    ((10 ^ 15, -2 * 10 ^ 15, 10 ^ 15, -5 * 10 ^ 15), false), ((10 ^ 12, 0, 0, -3 * 10 ^ 12), true),
    ((10 ^ 12, 0, 10 ^ 12, -10 ^ 13), false), ((-1, 0, 0, 10), false)].all
  fun ((a, b, c, d), r) ↦ (checkLiftsMpz #[1, 4, 3, -8, 2, 8, 7] a b c d).run == r
#guard (checkLiftsMpz #[0, 1, 2, -1, 3, 1, 1] (10 ^ 12) 0 0 (-2 * 10 ^ 12)).run
#guard !(checkLiftsMpz #[3, -1, 2, 5, -4, 1, 4] (10 ^ 12) 0 0 (-2 * 10 ^ 12)).run

-- The lifting test of the brute-force reference, on the candidates over the triples of height at
-- most 6, for four curves: the numbers of the candidates and of those that lift.
#guard [#[4, -6, 10, 8, -1, -10, 1], #[1, 4, 3, -8, 2, 8, 7], #[0, 1, 2, -1, 3, 1, 1],
    #[9, 4, 6, 5, 1, -4, -2]].map (fun cs ↦
    let ps := (BruteForce.orderedTriples 6).flatMap fun (a, b, c) ↦
      BruteForce.candidates cs.toList a b c
    (ps.all (fun (a, b, c, d) ↦
        (checkLifts cs a b c d).run == BruteForce.lifts cs.toList a b c d &&
          (checkLiftsMpz cs a b c d).run == BruteForce.lifts cs.toList a b c d),
      ps.length, (ps.filter fun (a, b, c, d) ↦ (checkLifts cs a b c d).run).length)) ==
  [(true, 16, 4), (true, 22, 4), (true, 78, 2), (true, 16, 9)]

end JPoints

end
