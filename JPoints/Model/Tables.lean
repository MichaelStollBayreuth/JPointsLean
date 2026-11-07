/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Constants

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Constants

/-!
# The tables of residues modulo the primes

The tables of `j-points` that hold residues modulo the odd primes of `JPoints.primeTable`. Those
that `init_main` builds before it reads the command line (`JPoints.Tables`, `JPoints.initMain`):
the words with one bit set, the inverses modulo every prime of the table, by Fermat's little
theorem (`JPoints.invert`, `JPoints.initInverses`), and the square roots modulo every prime of the
table (`JPoints.initSquares`). And those of the curve searched (`JPoints.CurveTables`): its
coefficients modulo the primes, the tables of the points at infinity and of the values of `f` that
are squares, which `init_fmodpsquare` fills, and the exact table of the third stage of the sieve,
whose rows `JPoints.initTable` fills for one prime by the test `JPoints.pointOnJ` of the classes
`(1, b, c)` off the diagonal `c = b² / 4`, with the reductions by the reciprocal of the prime
(`JPoints.modp`).

## Main definitions

* `JPoints.Tables`, `JPoints.Tables.initial`, `JPoints.initMain`: the tables of `init_main`.
* `JPoints.invert`, `JPoints.initInverses`, `JPoints.initSquares`: the inverses and the square
  roots modulo the primes of the table.
* `JPoints.CurveTables`, `JPoints.CurveTables.initial`: the tables of the curve modulo the primes.
* `JPoints.modp`, `JPoints.pointOnJ`, `JPoints.initTable`: the exact table of the third stage.

## Implementation notes

Each table of the C code is a flat array with the index arithmetic of the C code: the entry
`t[i][j]` of a table of width `W` at `i * W + j`, and `is_point_on_j[pn][b][c]` at
`(pn * 256 + b) * 256 + c`. The `long` and `int` entries are integers, the `unsigned char` tables
of `0` and `1` arrays of Booleans, the words arrays of `UInt64`; the indices and the counters, which
the C code keeps nonnegative, are natural numbers. The globals of the C code are fields of
structures, with the zeros of static storage as their values when the program starts
(`JPoints.Tables.initial`, `JPoints.CurveTables.initial`); a function that writes a table takes it
and returns it. `JPoints.initTable` takes the tables of the curve apart before its loop, so that
the compiled code writes the large table of the third stage in place.
-/

@[expose] public section

namespace JPoints

/-! ### The tables of `init_main` -/

/-- The tables that `init_main` builds before it reads the command line: the globals `bits`,
`inverses` and `squares`.

C: `j-points.c:182`, `j-points.c:186`, `j-points.c:188`

Deviation: flat arrays for the arrays of the C code, with its index arithmetic, in a structure, for
the globals. -/
structure Tables where
  /-- `bits`, the `JPoints.longLength` words with one bit set: `bits[n] = 2 ^ n`. -/
  bits : Array UInt64
  /-- `inverses`, of width `JPoints.maxPrimeEven`: at `pn * 256 + a`, for `0 < a < p` with
  `p = primeTable[pn]`, the inverse of `a` modulo `p` in `[1, p)`; `0` for `a = 0` and `a ≥ p`. -/
  inverses : Array Int
  /-- `squares`, of width `JPoints.maxPrime`: at `pn * 251 + x`, for `x < p = primeTable[pn]`, the
  even square root of `x` modulo `p` in `[0, p)` when `x` is a square modulo `p` (`0` included),
  and `p` when it is not. -/
  squares : Array Int

/-- The tables of `init_main` when the program starts: every entry `0`, as for a global of static
storage.

C: `j-points.c:182`, `j-points.c:186`, `j-points.c:188` -/
def Tables.initial : Tables where
  bits := Array.replicate longLength 0
  inverses := Array.replicate (numPrimes * maxPrimeEven) 0
  squares := Array.replicate (numPrimes * maxPrime) 0

/-- `a ^ (p - 2)` modulo `p`, as `invert` computes it by binary exponentiation from the right: for
the exponent `n`, from `p - 2` while `n > 1`, `r` multiplied by `b` when `n` is odd, `b` squared,
`n` halved, and at the end `r b`, each product reduced modulo `p`. For a prime `p` and `0 < a < p`,
the inverse of `a` modulo `p`, by Fermat's little theorem.

C: `j-points.c:708-716`

Deviation: integers for the `long`s; `n % 2 == 1` for `n & 1` and `n >>> 1` for `n >>= 1`, which
agree on the positive `n` of the loop; `Int.tmod` for C's `%`. -/
def invert (a p : Int) : Id Int := do
  let mut r : Int := 1
  let mut b := a
  let mut n := p - 2
  while n > 1 do
    if n % 2 == 1 then
      r := r * b
      r := r.tmod p
    b := b * b
    b := b.tmod p
    n := n >>> 1
  return (r * b).tmod p

/-- The table `inverses` as `init_inverses` fills it: for every prime `p = primeTable[pn]` of the
table and `0 < a < p`, the entry `pn * 256 + a` set to the inverse `JPoints.invert a p`; the other
entries as they were.

C: `j-points.c:718-724`

Deviation: the table taken and returned, for the global; natural numbers for the nonnegative
`long`s `pn`, `p` and `a`. -/
def initInverses (inverses : Array Int) : Id (Array Int) := do
  let mut inverses := inverses
  for pn in [0:numPrimes] do
    let p := primeTable[pn]!
    for a in [1:p] do
      inverses := inverses.set! (pn * maxPrimeEven + a) (← invert a p)
  return inverses

/-- The table `squares` as `init_squares` fills it: for every prime `p = primeTable[pn]` of the
table, the entries `pn * 251 + x` for `x < p` set to `p`, and then, for the even `a < p` in
increasing order, the entry of `a² % p` set to `a`. As exactly one of the roots `r` and `p - r` of
a nonzero square is even, each square gets its even root.

C: `j-points.c:726-738`

Deviation: the table taken and returned, for the global; natural numbers for the nonnegative
`long`s `pn`, `p` and `a`, so that `a² % p` is the remainder of natural numbers. -/
def initSquares (squares : Array Int) : Id (Array Int) := do
  let mut squares := squares
  for pn in [0:numPrimes] do
    let p := primeTable[pn]!
    for a in [0:p] do squares := squares.set! (pn * maxPrime + a) p
    for a in [0:p:2] do squares := squares.set! (pn * maxPrime + a * a % p) a
  return squares

/-- The tables as `init_main` builds them from the tables `t`: `bits[n] = 2 ^ n` for
`n < JPoints.longLength`, by a word shifted left at each step, then the inverses
(`JPoints.initInverses`) and the square roots (`JPoints.initSquares`).

C: `j-points.c:683-686`, `j-points.c:695-702`

Deviation: the tables taken and returned, for the globals; a natural number for the index `n`. The
initializations of the GMP integers (`j-points.c:687-693`) are memory management, not modeled. -/
def initMain (t : Tables) : Id Tables := do
  let mut bits := t.bits
  let mut bit : UInt64 := 1
  for n in [0:longLength] do
    bits := bits.set! n bit
    bit := bit <<< 1
  let inverses ← initInverses t.inverses
  let squares ← initSquares t.squares
  return { bits, inverses, squares }

/-! ### The tables of the curve -/

/-- The tables of the curve searched modulo the primes of the table: the globals `coeffs_mod_p`,
`has_infinity`, `is_f_square`, which `init_fmodpsquare` fills for the first `num_primes` primes,
and `is_point_on_j`, whose rows `init_table` fills for a prime.

C: `j-points.c:191`, `j-points.c:194`, `j-points.c:196`, `j-points.c:259`

Deviation: flat arrays for the arrays of the C code, with its index arithmetic, in a structure, for
the globals; arrays of Booleans for the arrays of `unsigned char` that hold `0` and `1`. -/
structure CurveTables where
  /-- `coeffs_mod_p`, of width `8`: at `pn * 8 + n`, for `n ≤ 6`, the coefficient `fₙ` of the curve
  modulo `p = primeTable[pn]`, in `[0, p)`. -/
  coeffsModP : Array Int
  /-- `has_infinity`: at `pn`, whether `f₆` is a square modulo `p = primeTable[pn]` (`0`
  included), that is, whether the curve has points at infinity modulo `p`. -/
  hasInfinity : Array Bool
  /-- `is_f_square`, of width `JPoints.maxPrimeEven`: at `pn * 256 + x`, for `x < p`, whether
  `f(x)` is a square modulo `p = primeTable[pn]` (`0` included). -/
  isFSquare : Array Bool
  /-- `is_point_on_j`, of width `JPoints.maxPrimeEven` in both inner indices: at
  `(pn * 256 + b) * 256 + c`, for `b, c < p` and a prime `p = primeTable[pn]` whose table
  `JPoints.initTable` filled, whether the sieve admits the class `(1, b, c)` modulo `p`. -/
  isPointOnJ : Array Bool

/-- The tables of the curve when the program starts: every entry `0`, as for a global of static
storage.

C: `j-points.c:191`, `j-points.c:194`, `j-points.c:196`, `j-points.c:259` -/
def CurveTables.initial : CurveTables where
  coeffsModP := Array.replicate (numPrimes * 8) 0
  hasInfinity := Array.replicate numPrimes false
  isFSquare := Array.replicate (numPrimes * maxPrimeEven) false
  isPointOnJ := Array.replicate (numPrimes * maxPrimeEven * maxPrimeEven) false

/-! ### The exact table of the third stage -/

/-- `MODP(x)` of `point_on_j`: `x - p q` for the quotient `q`, the high half of the product of `x`
with the reciprocal `recip = ⌈2 ^ 32 / p⌉` of `p` that `init_table` and `init_fmodpsquare` pass to
`point_on_j`, both as `unsigned long`s, shifted right by `32`. For `0 ≤ x < 2 ^ 24` and an odd
`p < 256`, the remainder of `x` modulo `p`.

C: `j-points.c:761`

Deviation: a function of `p` and `recip`, which the macro takes from the scope where it is used;
integers for the `long`s `x` and `p`, with the conversion of `x` to an `unsigned long` modulo
`2 ^ 64` as C converts it; the quotient is below `2 ^ 32`, so that the conversion back to a `long`
keeps it, and `x - p q` fits a `long` for the operands of the calls, below `2 ^ 24`. -/
def modp (p : Int) (recip : UInt64) (x : Int) : Int :=
  x - p * (((UInt64.ofInt x * recip) >>> 32).toNat : Int)

/-- Whether `point_on_j` admits the class `(1, b, c)` modulo the prime `p = primeTable[pn]`, for
the tables `squares` and `coeffsModP` and the degree `degree` of the curve searched: the remainder
`s₁ x + s₂` of `f` modulo `x² - b x + c` by Horner's rule, from the coefficients of `f` of degree
`degree` and `degree - 1` modulo `p`; then `f(x₁) f(x₂) = s₂² + b s₁ s₂ + c s₁²` must be a square
`t²` (`t` its even root from `squares`), and one of `2 s₂ + b s₁ ± 2 t` a square, every value
reduced modulo `p` by `JPoints.modp` with the reciprocal `recip` of `p`.

C: `j-points.c:762-777`

Deviation: natural numbers for the index `pn` and the `long` `degree`, and the steps of the loop
counted up, for the index `n` that counts down from `degree - 2` to `0`; the tables and the degree
passed, for the globals that the C code reads; the entries of `squares` read at the natural number
of the index, which the reductions make nonnegative; a Boolean for the `int`. -/
def pointOnJ (squares coeffsModP : Array Int) (degree pn : Nat) (p : Int) (recip : UInt64)
    (b c : Int) : Id Bool := do
  let mut s1 := coeffsModP[pn * 8 + degree]!
  let mut s2 := coeffsModP[pn * 8 + (degree - 1)]!
  for i in [0:degree - 1] do
    let n := degree - 2 - i
    let t := s1
    s1 := modp p recip (s1 * b + s2)
    s2 := modp p recip (coeffsModP[pn * 8 + n]! + (p - c) * t)
  let t := modp p recip (s2 * s2 + modp p recip (b * s1) * s2 + modp p recip (c * s1) * s1)
  let t := squares[pn * maxPrime + t.toNat]!
  if t == p then return false
  let u1 := modp p recip (2 * s2 + b * s1 + 2 * t)
  let u2 := modp p recip (u1 + 4 * (p - t))
  return squares[pn * maxPrime + u1.toNat]! != p || squares[pn * maxPrime + u2.toNat]! != p

/-- The rows of the prime `p = primeTable[pn]` in the table of the third stage as `init_table`
fills them, for the tables `t` and `ct` and the degree `degree` of the curve searched: the entry of
`(1, b, c)` for `b, c < p` set when `c` is `b² / 4` modulo `p`, computed as `b²` times the inverse
`(1 + p (3 - (p & 2))) / 4` of `4`, or else when `JPoints.pointOnJ` admits it, with the reciprocal
`⌈2 ^ 32 / p⌉` computed in `unsigned long`s; and the number of the entries set.

C: `j-points.c:781-795`

Deviation: the tables and the degree taken and the tables of the curve returned, for the globals
(the degree for `point_on_j`, which reads it); natural numbers for the indices `pn`, `b` and `c`,
for the count, which the C code keeps nonnegative, and for the degree; `p & 2` by the AND of natural
numbers on the positive `p`; `Int.tdiv` and `Int.tmod` for C's `/` and `%`. -/
def initTable (t : Tables) (ct : CurveTables) (degree pn : Nat) : Id (CurveTables × Nat) := do
  let ⟨coeffsModP, hasInfinity, isFSquare, isPointOnJ⟩ := ct
  let p : Int := primeTable[pn]!
  let recip : UInt64 := ((1 : UInt64) <<< 32 + UInt64.ofInt p - 1) / UInt64.ofInt p
  let mut isPointOnJ := isPointOnJ
  let mut count := 0
  for b in [0:p.toNat] do
    let bb := ((1 + p * (3 - (p.toNat &&& 2 : Nat))).tdiv 4 * b * b).tmod p
    for c in [0:p.toNat] do
      let admitted ← if c == bb then pure true
        else pointOnJ t.squares coeffsModP degree pn p recip b c
      if admitted then
        isPointOnJ := isPointOnJ.set! ((pn * maxPrimeEven + b) * maxPrimeEven + c) true
        count := count + 1
      else
        isPointOnJ := isPointOnJ.set! ((pn * maxPrimeEven + b) * maxPrimeEven + c) false
  return (⟨coeffsModP, hasInfinity, isFSquare, isPointOnJ⟩, count)

/-! ### Examples

The values of the C code at the pin, from a test program that calls `init_main`, `invert`,
`point_on_j` and `init_table` of `j-points.c` directly, with the coefficients modulo the prime as
`init_fmodpsquare` reduces them. A whole table is compared by its hash: `h ↦ h * 1000003 + v`
modulo `2 ^ 64` over its entries in the order of their indices, from `h = 0`. -/

-- The hash of the examples over the entries `vs`.
private def hash (vs : Array UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The tables of the curve with the coefficients `cs` modulo the prime `primeTable[pn]`, as
-- `init_fmodpsquare` reduces them (`mpz_fdiv_r_ui`, the remainder in `[0, p)`).
private def withCoeffsModP (cs : Array Int) (pn : Nat) : CurveTables :=
  let p : Int := primeTable[pn]!
  { CurveTables.initial with
    coeffsModP := (List.range 7).foldl (fun a n ↦ a.set! (pn * 8 + n) (cs[n]! % p))
      CurveTables.initial.coeffsModP }

-- The row of `primeTable[pn]` in the table of the third stage, as a string of `0`s and `1`s per
-- residue `b`.
private def rows (ct : CurveTables) (pn : Nat) : List String :=
  let p := primeTable[pn]!
  (List.range p).map fun b ↦ String.ofList <| (List.range p).map fun c ↦
    if ct.isPointOnJ[(pn * maxPrimeEven + b) * maxPrimeEven + c]! then '1' else '0'

#guard (invert 2 3).run == 2 && (invert 5 7).run == 3 && (invert 1 251).run == 1 &&
  (invert 250 251).run == 250 && (invert 3 251).run == 84

-- `MODP` with the reciprocal of `init_table`: the remainder for `0 ≤ x < 2 ^ 24`, among them the
-- largest operand `3 (p - 1)²` of `point_on_j`; for `x = -1`, converted to `2 ^ 64 - 1`, what gcc
-- computes.
#guard [(3, 1431655766, [0, 1, 2, 0, 0, 0, -12884901886]),
    (127, 33818641, [0, 1, 126, 0, 3, 7, -545460846466]),
    (251, 17111424, [0, 1, 250, 0, 3, 124, -1078036791046])].all fun (p, recip, r) ↦
  ((1 : UInt64) <<< 32 + UInt64.ofInt p - 1) / UInt64.ofInt p == recip &&
    [0, 1, p - 1, p, 3 * (p - 1) ^ 2, 2 ^ 24 - 1, -1].map (modp p recip) == r

-- The three tables, whole, by their hashes.
#guard
  let t := (initMain Tables.initial).run
  (hash t.bits, hash (t.inverses.map UInt64.ofInt), hash (t.squares.map UInt64.ofInt)) ==
    (11310366206046337729, 14492798127286894855, 12921090494484560319)

-- The rows of the inverses and the square roots of `3`, `5` and `7`.
#guard
  let t := (initMain Tables.initial).run
  [(0, [0, 1, 2], [0, 2, 3]), (1, [0, 1, 3, 2, 4], [0, 4, 5, 5, 2]),
    (2, [0, 1, 4, 5, 2, 3, 6], [0, 6, 4, 7, 2, 7, 7])].all fun (pn, inv, sq) ↦
    (t.inverses.extract (pn * maxPrimeEven) (pn * maxPrimeEven + primeTable[pn]!)).toList == inv &&
      (t.squares.extract (pn * maxPrime) (pn * maxPrime + primeTable[pn]!)).toList == sq

-- The table of the third stage for one prime, from the tables of the curve as the program starts:
-- the count, the hash of the rows of the prime (all `256 × 256` entries, those beyond `p` still
-- `false`), and for `p ≤ 13` the rows. Sextics and the monic quintic of example 2 of the README
-- of `j-points`, and `y² = x⁶ + 3` at `3` (where `f ≡ x⁶`) and at `5`.
#guard
  let t := (initMain Tables.initial).run
  [(#[1, 4, 3, -8, 2, 8, 7], 6, 0, 5, 2601702501518771611, ["100", "011", "110"]),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 1, 13, 322297269118832913,
      ["11010", "00001", "01010", "01011", "11101"]),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 2, 26, 11872489421549309366,
      ["1100100", "0011111", "1100010", "0001110", "1100101", "0100010", "1111101"]),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 4, 96, 18020019320416980456,
      ["1010111110111", "1111010000110", "1100100010101", "1110110001011", "1011111101001",
        "0111101000010", "0100101111011", "1001010101011", "1101100101100", "1101100010110",
        "1001010011101", "0110011110110", "1100001110100"]),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 29, 5887, 10779281395284822705, []),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 52, 25651, 14580744753003515011, []),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 0, 6, 13154001439057071700, ["110", "110", "011"]),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 2, 26, 9435719846326576770,
      ["1110000", "1011000", "0111001", "0100110", "1100111", "1110101", "0010011"]),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 10, 555, 6530828247074733391, []),
    (#[1, 178, 817, -274, 16, 1, 0], 5, 52, 25726, 3910850440962706434, []),
    (#[-7, 0, 6, 6, 10, -7, -3], 6, 3, 61, 14777898414369154845,
      ["11000011100", "11111011111", "01101001010", "00011110100", "11001101100", "10101001010",
        "10010100010", "10001010010", "10110101010", "01101100110", "01111010000"]),
    (#[-7, 0, 6, 6, 10, -7, -3], 6, 20, 2412, 8048701763659466658, []),
    (#[3, 0, 0, 0, 0, 0, 1], 6, 0, 9, 17728021791368033125, ["111", "111", "111"]),
    (#[3, 0, 0, 0, 0, 0, 1], 6, 1, 17, 15433136601813064699,
      ["11111", "01101", "01011", "01011", "01101"]),
    (#[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800], 6, 7, 289,
      2550049806142847163, []),
    (#[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800], 6, 45,
      17861, 7665813887961159649, [])].all fun (cs, d, pn, n, h, rs) ↦
    let (ct, count) := (initTable t (withCoeffsModP cs pn) d pn).run
    count == n && (rs.isEmpty || rows ct pn == rs) &&
      hash ((ct.isPointOnJ.extract (pn * maxPrimeEven * maxPrimeEven)
        ((pn + 1) * maxPrimeEven * maxPrimeEven)).map fun v ↦ if v then 1 else 0) == h

end JPoints

end
