/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Kummer

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Kummer

/-!
# The condition at 2

The condition at 2 of `j-points`: a point `(a' : b' : c' : d')` of the Kummer surface with coprime
integer coordinates that comes from a rational point of the Jacobian satisfies the Kummer equation,
and `A² = a'³ d' + A₀(a', b', c')` is a square or `0`. Since the sieve's triple `(a, b, c)` is
coprime and the point is `(v a, v b, v c, u)` for `d = u / v`, a triple whose class modulo `64`
admits neither some `d` with `K₂ d² + K₁ d + K₀ = 0` and `a³ d + A₀` a square residue (`v` odd),
nor, for `v = 2 ^ e`, some odd `t` with `K₂ t² + 2 ^ e K₁ t + 4 ^ e K₀ = 0` and, for `e = 1`,
`8 (a³ t + 2 A₀)` a square residue, is not the triple of a point with `a ≠ 0`. For each class
`(a, b)` modulo `m` (`16` or `64`) `twoadic_table` builds the word of the admitted `c` modulo `m`
(`JPoints.twoadicTable`), from the table of the solutions of the quadratic equations modulo `m`
(`JPoints.twoadicSol`), the squares modulo `m` (`JPoints.twoadicSquares`) and the coefficients of
the curve and of the quartic `K₀` modulo `m` (`JPoints.twoadicCoeffs`); `twoadic_init`
(`JPoints.twoadicInit`) tries the modulus `16` first and uses the condition only when it excludes
something there, with the table modulo `64`, the density of the admitted triples and the fraction of
the empty classes for the cost model.

## Main definitions

* `JPoints.TwoAdic`, `JPoints.TwoAdic.initial`: the globals of the condition at 2.
* `JPoints.TwoadicTable`: what `twoadic_table` leaves.
* `JPoints.twoadicSquares`, `JPoints.twoadicSol`, `JPoints.twoadicCoeffs`: the squares, the
  solutions of the quadratic equations and the coefficients modulo `m`.
* `JPoints.twoadicPowers`, `JPoints.twoadicK0`, `JPoints.twoadicAdmits`, `JPoints.twoadicCell`,
  `JPoints.twoadicRow`, `JPoints.twoadicClasses`: the test of a triple, of the row of a class
  `(a, b)` and of all classes modulo `m`.
* `JPoints.twoadicTable`, `JPoints.twoadicInit`: the table modulo `m`, and the condition at 2.

## Implementation notes

The arithmetic of `twoadic_table` is on `long`s whose values stay below `2 ^ 26` in absolute value,
so that nothing overflows; the coefficients `k₂ = b² + 4m - 4ac` and `b² + 4m - ac` can be negative
before their reduction. The C code reduces by `x & mm` with `mm = m - 1`; for `m` a power of `2`
that is the residue of `x` modulo `m` in `[0, m)` also for a negative `x`, in two's complement, and
the model writes `x % m`, the Euclidean remainder of integers. The arrays of the C code are arrays,
the `5 × 5 × 5` array `km` flat at `(i * 5 + j) * 5 + k` and the `64 × 64` arrays `masks` and
`alive` at `a * 64 + b`; the local arrays that the C code leaves uninitialized start as zeros, and
only entries that the C code writes are read. The density and the fraction of the empty classes are
`Float`s, as the cost model, which reads them, runs in `Float`, and message 4 prints them by
`JPoints.Double.ofFloat`; each is one division of two integers that a double holds exactly.
-/

@[expose] public section

namespace JPoints

/-- The globals of the condition at 2: per class `(a, b)` modulo `64`, the word of the admitted
residues `c` modulo `64` and whether the class admits any `c`; whether the sieve uses the
condition; and, for the cost model, the density of the admitted triples and the fraction of the
empty classes.

C: `j-points.c:247-250`

Deviation: flat arrays for the arrays of the C code, at `a * 64 + b`, in a structure, for the
globals; a Boolean for the `int` `use2`, and an array of Booleans for the array of `unsigned char`
that holds `0` and `1`; `Float`s for the doubles, which only the cost model and message 4 read. -/
structure TwoAdic where
  /-- `mask2`: at `a * 64 + b`, the word whose bit `c` is set when the condition at 2 admits the
  triples `(a, b, c)` modulo `64`, the fill of the bit array of a row `(a, b)` with `a ≠ 0`. -/
  mask2 : Array UInt64
  /-- `alive2`: at `a * 64 + b`, whether the class `(a, b)` modulo `64` admits any `c`. -/
  alive2 : Array Bool
  /-- `use2`: whether the sieve applies the condition at 2. -/
  use2 : Bool
  /-- `density2`: the fraction of the admitted triples among those modulo `64` not all even. -/
  density2 : Float
  /-- `empty2`: the fraction of the classes `(a, b)` modulo `64` that admit no `c`. -/
  empty2 : Float

/-- The globals of the condition at 2 when the program starts: the arrays zero, as for globals of
static storage, the condition not used, and the density `1` and the fraction `0` of the
initializers, which nothing reads: the cost model and message 4 read them only when `use2` is set,
and `twoadic_init` sets it only after it has written both.

C: `j-points.c:247-250` -/
def TwoAdic.initial : TwoAdic where
  mask2 := Array.replicate (64 * 64) 0
  alive2 := Array.replicate (64 * 64) false
  use2 := false
  density2 := 1.0
  empty2 := 0.0

/-- What `twoadic_table` leaves for the modulus `m`: the arrays `masks` and `alive` that its
arguments point to, with the entries of the classes `(a, b)` modulo `m` written, the number of the
empty classes that it stores through its argument `empty`, and the number of the admitted triples
not all even, which it returns.

C: `j-points.c:1668-1669`

Deviation: a structure, for the arrays and the integer that the arguments point to and for the
result; natural numbers for the counts, which the C code keeps nonnegative. -/
structure TwoadicTable where
  /-- The array `masks`: at `a * 64 + b`, for `a, b < m`, the word of the admitted residues `c`
  modulo `m`, the pattern of the `m` residues repeated over the `64` bits for `m < 64`. -/
  masks : Array UInt64
  /-- The array `alive`: at `a * 64 + b`, for `a, b < m`, whether the class admits any `c`. -/
  alive : Array Bool
  /-- `*empty`, the number of the classes `(a, b)` modulo `m` that admit no `c`. -/
  empty : Nat
  /-- The number of the triples modulo `m`, not all even, that the condition admits. -/
  count : Nat

/-! ### The tables modulo `m` -/

/-- The table `sq` of `twoadic_table`: at `x < m`, whether `x` is a square modulo `m`, as `i² & mm`
for `i < m`.

C: `j-points.c:1678-1679`

Deviation: Booleans for the `int`s `0` and `1`; the local array of `64` entries, which the C code
leaves uninitialized, starting as `false`, of which the first loop clears the entries below `m`, the
only ones read; a natural number for `i`, and `i * i % m` for `(i*i) & mm`, equal for `m` a power
of `2`. -/
def twoadicSquares (m : Nat) : Id (Array Bool) := do
  let mut sq := Array.replicate 64 false
  for i in [0:m] do sq := sq.set! i false
  for i in [0:m] do sq := sq.set! (i * i % m) true
  return sq

/-- The table `sol` of `twoadic_table`: at `(k₂ m + k₁) m + k₀`, for `k₀, k₁, k₂ < m`, the word
whose bit `d < m` is set when `k₂ d² + k₁ d + k₀ ≡ 0 (mod m)`, built by running over
`(k₂, k₁, d)` and setting bit `d` at `k₀ = (m - v) & mm` for `v = (k₂ d² + k₁ d) & mm`.

C: `j-points.c:1680-1686`

Deviation: a fresh array of zeros for the array that the C code allocates and the loop clears
(`malloc`, memory management, not modeled); natural numbers for the nonnegative `long`s; `x % m`
for `x & mm`, equal for the nonnegative `x` and `m` a power of `2`. -/
def twoadicSol (m : Nat) : Id (Array UInt64) := do
  let mut sol : Array UInt64 := Array.replicate (m * m * m) 0
  for k2 in [0:m] do
    for k1 in [0:m] do
      for d in [0:m] do
        let v := (k2 * d * d + k1 * d) % m
        let i := (k2 * m + k1) * m + (m - v) % m
        sol := sol.set! i (sol[i]! ||| (1 : UInt64) <<< d.toUInt64)
  return sol

/-- The coefficients `f₀, …, f₆` of the curve searched (`coeffs`) and those of the quartic `K₀`
(`k`) modulo `m`, as `twoadic_table` reduces them by `mpz_fdiv_ui` into the arrays `fm` and `km`:
`km` at `(i * 5 + j) * 5 + l` the coefficient `k_ijl` for `i + j + l = 4`, and `0` elsewhere.

C: `j-points.c:1687-1696`

Deviation: integers for the `long`s, `x % m`, the Euclidean remainder, for the remainder of the
floor division of `mpz_fdiv_ui`, equal for `m > 0`; the arrays returned, for the local arrays; a
fresh array of zeros for the array `km`, which the loop at `j-points.c:1688` clears. -/
def twoadicCoeffs (coeffs : Array Int) (k : KummerCoeffs) (m : Nat) :
    Id (Array Int × Array Int) := do
  let mut fm : Array Int := Array.replicate 7 0
  for i in [0:7] do fm := fm.set! i (coeffs[i]! % m)
  let idx (i j l : Nat) : Nat := (i * 5 + j) * 5 + l
  let km : Array Int := Array.replicate 125 0
    |>.set! (idx 4 0 0) (k.k400 % m) |>.set! (idx 3 1 0) (k.k310 % m)
    |>.set! (idx 3 0 1) (k.k301 % m) |>.set! (idx 2 2 0) (k.k220 % m)
    |>.set! (idx 2 1 1) (k.k211 % m) |>.set! (idx 2 0 2) (k.k202 % m)
    |>.set! (idx 1 3 0) (k.k130 % m) |>.set! (idx 1 2 1) (k.k121 % m)
    |>.set! (idx 1 1 2) (k.k112 % m) |>.set! (idx 1 0 3) (k.k103 % m)
    |>.set! (idx 0 4 0) (k.k040 % m) |>.set! (idx 0 3 1) (k.k031 % m)
    |>.set! (idx 0 2 2) (k.k022 % m) |>.set! (idx 0 1 3) (k.k013 % m)
    |>.set! (idx 0 0 4) (k.k004 % m)
  return (fm, km)

/-! ### The test of a triple -/

/-- The powers `x⁰, …, x⁴` modulo `m` of `twoadic_table`: the array `ap`, `bp` or `cp` of the
residues `a`, `b` or `c`, from `1` by repeated multiplication with `x`, each product reduced by
`& mm`.

C: `j-points.c:1700`, `j-points.c:1703`, `j-points.c:1709`

Deviation: one function for the three loops of the C code, which differ only in the array and the
residue; the array returned, for the local array of five `long`s, which starts as zeros; a natural
number for the residue `x`; `y % m` for `y & mm`, equal for the nonnegative `y` and `m` a power of
`2`. -/
def twoadicPowers (x m : Nat) : Id (Array Int) := do
  let mut xp : Array Int := Array.replicate 5 0
  xp := xp.set! 0 1
  for i in [1:5] do xp := xp.set! i (xp[i - 1]! * x % m)
  return xp

/-- The value `k₀` of the quartic `K₀` at the triple with the powers `ap`, `bp` and `cp` modulo `m`,
for its coefficients `km` modulo `m`: the sum of `km[i][j][k] aⁱ bʲ cᵏ` over `i + j + k = 4`, in
the order of `i` and then `j`, reduced by `& mm` at each step.

C: `j-points.c:1705`, `j-points.c:1710-1714`

Deviation: natural numbers for the indices `i`, `j` and `k`, the bound `i + j < 5` written as
`j < 5 - i`; `x % m` for `x & mm`, equal for `m` a power of `2`. -/
def twoadicK0 (km ap bp cp : Array Int) (m : Nat) : Id Int := do
  let mut k0 : Int := 0
  for i in [0:5] do
    for j in [0:5 - i] do
      let k := 4 - i - j
      k0 := (k0 + km[(i * 5 + j) * 5 + k]! * ap[i]! * bp[j]! * cp[k]!) % m
  return k0

/-- Whether the condition at 2 modulo `m` admits a triple with the coefficients `k₀`, `k₁`, `k₂` of
the Kummer equation, `a3 = a³` and `A0 = A₀` modulo `m`, given the tables `sol` and `sq` and the
word `odd` of the odd residues: for `v` odd, some `d` with `k₂ d² + k₁ d + k₀ ≡ 0` and
`a³ d + A₀` a square; else for `v = 2`, some odd `t` with `k₂ t² + 2 k₁ t + 4 k₀ ≡ 0` and
`8 (a³ t + 2 A₀)` a square; else for `v = 2 ^ e`, `e = 2, …, 6`, some odd `t` with
`k₂ t² + 2 ^ e k₁ t + 4 ^ e k₀ ≡ 0`, each search ending at the first success.

C: `j-points.c:1706-1707`, `j-points.c:1724-1737`

Deviation: a Boolean for the `int` `ok`; natural numbers for the indices `d` and `e`; the condition
`!ok` of the loops a `break` at the start of each step; the entries of `sol` and `sq` read at the
natural number of the index, which the reductions make nonnegative; `x % m` for `x & mm`, equal for
`m` a power of `2`. -/
def twoadicAdmits (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) (m : Nat)
    (k0 k1 k2 a3 A0 : Int) : Id Bool := do
  let mut ok := false
  let S := sol[((k2 * m + k1) * m + k0).toNat]!
  for d in [0:m] do
    if ok then break
    if (S >>> d.toUInt64) &&& 1 != 0 then ok := sq[((a3 * d + A0) % m).toNat]!
  if !ok then
    let S := sol[((k2 * m + 2 * k1 % m) * m + 4 * k0 % m).toNat]! &&& odd
    for d in [1:m:2] do
      if ok then break
      if (S >>> d.toUInt64) &&& 1 != 0 then ok := sq[(8 * (a3 * d + 2 * A0) % m).toNat]!
  for e in [2:7] do
    if ok then break
    let S := sol[((k2 * m + (k1 <<< e) % m) * m + (k0 <<< (2 * e)) % m).toNat]! &&& odd
    ok := S != 0
  return ok

/-- Whether the condition at 2 modulo `m` admits the triple `(a2, b2, c2)` modulo `m`, given the
coefficients `fm` and `km`, the tables `sol` and `sq`, the word `odd` and the powers `ap` and `bp`
of `a2` and `b2`: the powers of `c2` (`JPoints.twoadicPowers`), `k₀` (`JPoints.twoadicK0`),
`k₁ = -(4 f₀ a³ + 2 f₁ a² b + 4 f₂ a² c + 2 f₃ a b c + 4 f₄ a c² + 2 f₅ b c² + 4 f₆ c³)`,
`k₂ = b² - 4 a c`, `kk = b² - a c` and
`A₀ = f₂ a⁴ + f₃ a³ b + f₄ a² b² + f₅ a b kk + f₆ kk²` modulo `m`, and the test
`JPoints.twoadicAdmits`.

C: `j-points.c:1705`, `j-points.c:1715-1722`

Deviation: natural numbers for the residues `a2`, `b2` and `c2`; integers for the other `long`s;
`x % m` for `x & mm`, equal also for the negative `x` of `k₂` and `kk` (two's complement) for `m` a
power of `2`. -/
def twoadicCell (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) (m : Nat)
    (ap bp : Array Int) (a2 b2 c2 : Nat) : Id Bool := do
  let cp ← twoadicPowers c2 m
  let k0 ← twoadicK0 km ap bp cp m
  let k1 := (m - (4 * ap[3]! * fm[0]! + 2 * ap[2]! * b2 * fm[1]! + 4 * ap[2]! * c2 * fm[2]! +
    2 * a2 * b2 * c2 * fm[3]! + 4 * a2 * cp[2]! * fm[4]! + 2 * b2 * cp[2]! * fm[5]! +
    4 * cp[3]! * fm[6]!) % m) % m
  let k2 := (bp[2]! + m * 4 - 4 * a2 * c2) % m
  let kk := (bp[2]! + m * 4 - a2 * c2) % m
  let A0 := (fm[2]! * ap[4]! + fm[3]! * ap[3]! * b2 + fm[4]! * ap[2]! * bp[2]! +
    fm[5]! * a2 * b2 * kk + fm[6]! * kk * kk) % m
  let a3 := ap[3]!
  twoadicAdmits sol sq odd m k0 k1 k2 a3 A0

/-- The row of the class `(a2, b2)` modulo `m` in `twoadic_table`, given the coefficients, the
tables, the word `odd` and the powers `ap` and `bp` of `a2` and `b2`: the word of the residues
`c2 < m` that `JPoints.twoadicCell` admits, the triples with `a2`, `b2` and `c2` all even skipped,
for `m < 64` with the pattern repeated over the `64` bits; and the number of the admitted `c2`.

C: `j-points.c:1702`, `j-points.c:1704`, `j-points.c:1708`, `j-points.c:1738-1741`

Deviation: the number of the admitted `c2` returned, which the caller adds to the count that the C
code increments for each; natural numbers for the residues, the index `i` and the count; a `while`
loop for the loop over `i = m, 2m, …` below `64`, as a range `[a:b:s]` of Lean needs a step that
`decide` shows positive; like the C code, it does not end for `m = 0`. -/
def twoadicRow (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) (m : Nat)
    (ap bp : Array Int) (a2 b2 : Nat) : Id (UInt64 × Nat) := do
  let mut mask : UInt64 := 0
  let mut count := 0
  for c2 in [0:m] do
    if (a2 ||| b2 ||| c2) &&& 1 == 0 then continue
    if ← twoadicCell fm km sol sq odd m ap bp a2 b2 c2 then
      mask := mask ||| (1 : UInt64) <<< c2.toUInt64
      count := count + 1
  if m < 64 then
    let mut i := m
    while i < 64 do
      mask := mask ||| mask <<< m.toUInt64
      i := i + m
  return (mask, count)

/-- The classes `(a2, b2)` modulo `m` of `twoadic_table`, given the coefficients, the tables, the
words `odd` and `all`, and the arrays `masks` and `alive`: for each class the powers of `a2` and
`b2` (`JPoints.twoadicPowers`) and its row (`JPoints.twoadicRow`), the word stored at
`a2 * 64 + b2` in `masks` and whether it is not zero in `alive`, the empty classes and the admitted
triples counted.

C: `j-points.c:1673`, `j-points.c:1697-1699`, `j-points.c:1701`, `j-points.c:1742-1746`

Deviation: the arrays taken and returned with the counts, for the arrays and the integer that the
arguments of the C code point to and for its result; natural numbers for the residues and the
counts; the count of each row added after its loop. -/
def twoadicClasses (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd all : UInt64)
    (m : Nat) (masks : Array UInt64) (alive : Array Bool) : Id TwoadicTable := do
  let mut masks := masks
  let mut alive := alive
  let mut count := 0
  let mut empty := 0
  for a2 in [0:m] do
    let ap ← twoadicPowers a2 m
    for b2 in [0:m] do
      let bp ← twoadicPowers b2 m
      let (mask, n) ← twoadicRow fm km sol sq odd m ap bp a2 b2
      count := count + n
      masks := masks.set! (a2 * 64 + b2) (mask &&& if m < 64 then ~~~0 else all)
      alive := alive.set! (a2 * 64 + b2) (mask != 0)
      if mask == 0 then empty := empty + 1
  return { masks, alive, empty, count }

/-- The table of the condition at 2 modulo `m` (`16` or `64`) as `twoadic_table` builds it into the
arrays `masks` and `alive`, for the coefficients `coeffs` of the curve searched and `k` of the
quartic `K₀`: the word `odd` of the odd residues and the word `all` of the `m` residues, the
squares (`JPoints.twoadicSquares`), the solutions of the quadratic equations
(`JPoints.twoadicSol`), the coefficients modulo `m` (`JPoints.twoadicCoeffs`), and the classes
(`JPoints.twoadicClasses`).

C: `j-points.c:1668-1669`, `j-points.c:1670`, `j-points.c:1672`, `j-points.c:1674-1675`,
`j-points.c:1677`, `j-points.c:1748-1749`

Deviation: the arrays taken and returned, for those that the arguments point to; a natural number
for the `long` `m`; the scratch array `sol` a value, its allocation and release (`j-points.c:1671`,
`j-points.c:1676`, `j-points.c:1747`, with the exit of a failed allocation) memory management, not
modeled; no `mm`, as `x % m` stands for `x & mm`. -/
def twoadicTable (coeffs : Array Int) (k : KummerCoeffs) (m : Nat) (masks : Array UInt64)
    (alive : Array Bool) : Id TwoadicTable := do
  let mut odd : UInt64 := 0
  let all : UInt64 := if m == 64 then ~~~0 else ((1 : UInt64) <<< m.toUInt64) - 1
  for d in [1:m:2] do odd := odd ||| (1 : UInt64) <<< d.toUInt64
  let sq ← twoadicSquares m
  let sol ← twoadicSol m
  let (fm, km) ← twoadicCoeffs coeffs k m
  twoadicClasses fm km sol sq odd all m masks alive

/-! ### The condition at 2 -/

/-- The condition at 2 as `twoadic_init` decides it from the globals `t`, for the coefficients
`coeffs` of the curve searched and `k` of the quartic `K₀`: the table modulo `16` first, and if it
admits all `16³ - 8³` triples not all even, the condition is not used; otherwise the table modulo
`64` into `mask2` and `alive2`, the density of the admitted triples among the `64³ - 32³` not all
even and the fraction of the empty classes among the `64²`, and the condition used.

C: `j-points.c:1751-1765`

Deviation: the globals taken and returned; fresh arrays of zeros for the static arrays `masks16`
and `alive16`, which nothing reads; `Float`s for the doubles, the integers converted exactly. -/
def twoadicInit (coeffs : Array Int) (k : KummerCoeffs) (t : TwoAdic) : Id TwoAdic := do
  let r ← twoadicTable coeffs k 16 (Array.replicate (64 * 64) 0) (Array.replicate (64 * 64) false)
  if r.count == 16 * 16 * 16 - 8 * 8 * 8 then return { t with use2 := false }
  let r ← twoadicTable coeffs k 64 t.mask2 t.alive2
  let density2 := r.count.toFloat / (64 * 64 * 64 - 32 * 32 * 32 : Nat).toFloat
  let empty2 := r.empty.toFloat / (64 * 64 : Nat).toFloat
  return { mask2 := r.masks, alive2 := r.alive, use2 := true, density2, empty2 }

/-! ### Examples

The values of the C code at the pin, from a test program that calls `twoadic_table` and
`twoadic_init` of `j-points.c` directly, after `kummer_init`. The arrays are compared by their
hashes: `h ↦ h * 1000003 + v` modulo `2 ^ 64` over the `64 × 64` entries in the order of their
indices, from `h = 0`. -/

-- The hash of the examples over the entries `vs`.
private def hash (vs : Array UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The counts and the hashes of the arrays of the table of the curve `cs` modulo `m`.
private def tableHashes (cs : Array Int) (m : Nat) : Nat × Nat × UInt64 × UInt64 :=
  let r := (twoadicTable cs (kummerInit cs) m (Array.replicate (64 * 64) 0)
    (Array.replicate (64 * 64) false)).run
  (r.count, r.empty, hash r.masks, hash (r.alive.map fun v ↦ if v then 1 else 0))

-- The tables modulo `16`, whole: sextics, the monic quintic of example 2 of the README of
-- `j-points`, `y² = x⁶ + 3`, `y² = x⁵ + x`, example 1 of the README (`f` a square modulo `4`: all
-- `16³ - 8³ = 3584` triples admitted) and its example 3.
#guard [(#[1, 4, 3, -8, 2, 8, 7], (1792, 64, 16920094735151285024, 11859793019518517952)),
    (#[1, 178, 817, -274, 16, 1, 0], (1664, 80, 12552352688459135984, 17910729531816099248)),
    (#[-7, 0, 6, 6, 10, -7, -3], (1472, 80, 9962542470539465088, 8396720724591287728)),
    (#[3, 0, 0, 0, 0, 0, 1], (2432, 0, 8414158240781700064, 9966183081014090240)),
    (#[0, 1, 0, 0, 0, 1, 0], (1408, 80, 6532845682748342096, 17910729531816099248)),
    (#[1, 6, 5, 22, 22, 8, 1], (3584, 0, 1665001055917862208, 9966183081014090240)),
    (#[21, 116, 171, 128, 55, 12, 1], (2560, 64, 4718539223577495104, 5377004344145518848)),
    (#[1, 1, -2, -15, 13, 2, 1], (2048, 16, 10506846268504824832, 873255411885716304))].all
  fun (cs, r) ↦ tableHashes cs 16 == r

-- The hash of the words of the classes `(a2, b)` modulo `64`, `b < 64`, of the curve `cs`, by
-- `JPoints.twoadicRow` with the tables `sol` and `sq` modulo `64` and the word of the odd residues,
-- and the number of those classes that admit some `c`.
private def row64 (cs : Array Int) (sol : Array UInt64) (sq : Array Bool) (a2 : Nat) :
    UInt64 × Nat :=
  let (fm, km) := (twoadicCoeffs cs (kummerInit cs) 64).run
  let ap := (twoadicPowers a2 64).run
  let ms := (List.range 64).map fun b2 ↦
    (twoadicRow fm km sol sq 0xAAAAAAAAAAAAAAAA 64 ap (twoadicPowers b2 64).run a2 b2).run.1
  (hash ms.toArray, (ms.filter (· != 0)).length)

-- Rows of the tables modulo `64`: classes `(a, b)` for `a = 0`, odd and even `a`, with some that
-- admit no `c`; for example 1 of the README the classes `(1, b)` with odd `b` admit only the even
-- `c`, those with even `b` every `c`.
#guard
  let sq := (twoadicSquares 64).run
  let sol := (twoadicSol 64).run
  [(#[1, 4, 3, -8, 2, 8, 7], 0, 7016487823355143136, 16),
    (#[1, 4, 3, -8, 2, 8, 7], 1, 15041384481810647792, 64),
    (#[1, 4, 3, -8, 2, 8, 7], 2, 7961040906164032320, 32),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 10794700154590699872, 32),
    (#[1, 1, -2, -15, 13, 2, 1], 3, 12075669951607617960, 64),
    (#[1, 1, -2, -15, 13, 2, 1], 32, 18248219748053102752, 64),
    (#[1, 6, 5, 22, 22, 8, 1], 1, 11135518375232067904, 64)].all
  fun (cs, a2, h, n) ↦ row64 cs sol sq a2 == (h, n)

-- The condition at 2 not used: the table modulo `16` admits everything, for example 1 of the
-- README and for the curve of Müller and Stoll with ten-digit coefficients.
#guard [#[1, 6, 5, 22, 22, 8, 1],
    #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800]].all fun cs ↦
  let t := (twoadicInit cs (kummerInit cs) TwoAdic.initial).run
  !t.use2 && t.density2.toBits == 0x3ff0000000000000 && t.empty2.toBits == 0 &&
    hash t.mask2 == 0 && t.alive2.all (· == false)

-- The condition at 2 used, for the monic quintic of example 2 of the README of `j-points`: the
-- density of the admitted triples and the fraction of the empty classes by their bits, as the copy
-- of `j-points` of the examples of `JPoints.Model.Choice` prints them.
#guard
  let cs := #[1, 178, 817, -274, 16, 1, 0]
  let t := (twoadicInit cs (kummerInit cs) TwoAdic.initial).run
  t.use2 && t.density2.toBits == 0x3fd3249249249249 && t.empty2.toBits == 0x3fd7000000000000

end JPoints

end
