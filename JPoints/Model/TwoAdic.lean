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
`(a, b)` modulo `64` `twoadic_table` builds the word of the admitted `c` modulo `64`
(`JPoints.twoadicTable`), from the table of the solutions of the quadratic equations modulo `64`
(`JPoints.twoadicSol`), the squares modulo `64` (`JPoints.twoadicSquares`) and the coefficients of
the curve and of the quartic `K₀` modulo `64` (`JPoints.twoadicCoeffs`);
`twoadic_init` (`JPoints.twoadicInit`) builds the table modulo `64` and uses the condition only when
it excludes something there, with the density of the admitted triples and the fraction of the empty
classes for the cost model.

## Main definitions

* `JPoints.TwoAdic`, `JPoints.TwoAdic.initial`: the globals of the condition at 2.
* `JPoints.TwoadicTable`: what `twoadic_table` leaves.
* `JPoints.twoadicSquares`, `JPoints.twoadicSol`, `JPoints.twoadicCoeffs`: the squares, the
  solutions of the quadratic equations and the coefficients modulo `64`.
* `JPoints.twoadicPowers`, `JPoints.twoadicK0`, `JPoints.twoadicAdmits`, `JPoints.twoadicCell`,
  `JPoints.twoadicRow`, `JPoints.twoadicClasses`: the test of a triple, of the row of a class
  `(a, b)` and of all classes modulo `64`.
* `JPoints.twoadicTable`, `JPoints.twoadicInit`: the table modulo `64`, and the condition at 2.

## Implementation notes

The arithmetic of `twoadic_table` is on `long`s whose values stay below `2 ^ 26` in absolute value,
so that nothing overflows; the coefficients `k₂ = b² + 256 - 4ac` and `b² + 256 - ac` can be
negative before their reduction. The C code reduces by `x & 63`, the residue of `x` modulo `64` in
`[0, 64)` also for a negative `x`, in two's complement, and the model writes `x % 64`, the
Euclidean remainder of integers. The arrays of the C code are arrays,
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

C: `j-points.c:248-251`

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

C: `j-points.c:248-251` -/
def TwoAdic.initial : TwoAdic where
  mask2 := Array.replicate (64 * 64) 0
  alive2 := Array.replicate (64 * 64) false
  use2 := false
  density2 := 1.0
  empty2 := 0.0

/-- What `twoadic_table` leaves: the arrays `masks` and `alive` that its arguments point to, with
the entries of the classes `(a, b)` modulo `64` written, the number of the empty classes that it
stores through its argument `empty`, and the number of the admitted triples not all even, which it
returns.

C: `j-points.c:1660-1661`

Deviation: a structure, for the arrays and the integer that the arguments point to and for the
result; natural numbers for the counts, which the C code keeps nonnegative. -/
structure TwoadicTable where
  /-- The array `masks`: at `a * 64 + b`, for `a, b < 64`, the word of the admitted residues `c`
  modulo `64`. -/
  masks : Array UInt64
  /-- The array `alive`: at `a * 64 + b`, for `a, b < 64`, whether the class admits any `c`. -/
  alive : Array Bool
  /-- `*empty`, the number of the classes `(a, b)` modulo `64` that admit no `c`. -/
  empty : Nat
  /-- The number of the triples modulo `64`, not all even, that the condition admits. -/
  count : Nat

/-! ### The tables modulo `64` -/

/-- The table `sq` of `twoadic_table`: at `x < 64`, whether `x` is a square modulo `64`, as
`i² & 63` for `i < 64`.

C: `j-points.c:1670-1671`

Deviation: Booleans for the `int`s `0` and `1`; the local array of `64` entries, which the C code
leaves uninitialized and the first loop clears, starting as `false`; a natural number for `i`, and
`i * i % 64` for `(i*i) & 63`. -/
def twoadicSquares : Id (Array Bool) := do
  let mut sq := Array.replicate 64 false
  for i in [0:64] do sq := sq.set! i false
  for i in [0:64] do sq := sq.set! (i * i % 64) true
  return sq

/-- The table `sol` of `twoadic_table`: at `(64 k₂ + k₁) 64 + k₀`, for `k₀, k₁, k₂ < 64`, the word
whose bit `d < 64` is set when `k₂ d² + k₁ d + k₀ ≡ 0 (mod 64)`, built by running over
`(k₂, k₁, d)` and setting bit `d` at `k₀ = (64 - v) & 63` for `v = (k₂ d² + k₁ d) & 63`.

C: `j-points.c:1672-1678`

Deviation: a fresh array of zeros for the array that the C code allocates and the loop clears
(`malloc`, memory management, not modeled); natural numbers for the nonnegative `long`s; `x % 64`
for `x & 63`, equal for the nonnegative `x`. -/
def twoadicSol : Id (Array UInt64) := do
  let mut sol : Array UInt64 := Array.replicate (64 * 64 * 64) 0
  for k2 in [0:64] do
    for k1 in [0:64] do
      for d in [0:64] do
        let v := (k2 * d * d + k1 * d) % 64
        let i := (k2 * 64 + k1) * 64 + (64 - v) % 64
        sol := sol.set! i (sol[i]! ||| (1 : UInt64) <<< d.toUInt64)
  return sol

/-- The coefficients `f₀, …, f₆` of the curve searched (`coeffs`) and those of the quartic `K₀`
(`k`) modulo `64`, as `twoadic_table` reduces them by `mpz_fdiv_ui` into the arrays `fm` and `km`:
`km` at `(i * 5 + j) * 5 + l` the coefficient `k_ijl` for `i + j + l = 4`, and `0` elsewhere.

C: `j-points.c:1679-1688`

Deviation: integers for the `long`s, `x % 64`, the Euclidean remainder, for the remainder of the
floor division of `mpz_fdiv_ui`; the arrays returned, for the local arrays; a fresh array of zeros
for the array `km`, which the loop at `j-points.c:1680` clears. -/
def twoadicCoeffs (coeffs : Array Int) (k : KummerCoeffs) : Id (Array Int × Array Int) := do
  let mut fm : Array Int := Array.replicate 7 0
  for i in [0:7] do fm := fm.set! i (coeffs[i]! % 64)
  let idx (i j l : Nat) : Nat := (i * 5 + j) * 5 + l
  let km : Array Int := Array.replicate 125 0
    |>.set! (idx 4 0 0) (k.k400 % 64) |>.set! (idx 3 1 0) (k.k310 % 64)
    |>.set! (idx 3 0 1) (k.k301 % 64) |>.set! (idx 2 2 0) (k.k220 % 64)
    |>.set! (idx 2 1 1) (k.k211 % 64) |>.set! (idx 2 0 2) (k.k202 % 64)
    |>.set! (idx 1 3 0) (k.k130 % 64) |>.set! (idx 1 2 1) (k.k121 % 64)
    |>.set! (idx 1 1 2) (k.k112 % 64) |>.set! (idx 1 0 3) (k.k103 % 64)
    |>.set! (idx 0 4 0) (k.k040 % 64) |>.set! (idx 0 3 1) (k.k031 % 64)
    |>.set! (idx 0 2 2) (k.k022 % 64) |>.set! (idx 0 1 3) (k.k013 % 64)
    |>.set! (idx 0 0 4) (k.k004 % 64)
  return (fm, km)

/-! ### The test of a triple -/

/-- The powers `x⁰, …, x⁴` modulo `64` of `twoadic_table`: the array `ap`, `bp` or `cp` of the
residues `a`, `b` or `c`, from `1` by repeated multiplication with `x`, each product reduced by
`& 63`.

C: `j-points.c:1692`, `j-points.c:1695`, `j-points.c:1701`

Deviation: one function for the three loops of the C code, which differ only in the array and the
residue; the array returned, for the local array of five `long`s, which starts as zeros; a natural
number for the residue `x`; `y % 64` for `y & 63`, equal for the nonnegative `y`. -/
def twoadicPowers (x : Nat) : Id (Array Int) := do
  let mut xp : Array Int := Array.replicate 5 0
  xp := xp.set! 0 1
  for i in [1:5] do xp := xp.set! i (xp[i - 1]! * x % 64)
  return xp

/-- The value `k₀` of the quartic `K₀` at the triple with the powers `ap`, `bp` and `cp` modulo
`64`, for its coefficients `km` modulo `64`: the sum of `km[i][j][k] aⁱ bʲ cᵏ` over
`i + j + k = 4`, in the order of `i` and then `j`, reduced by `& 63` at each step.

C: `j-points.c:1697`, `j-points.c:1702-1706`

Deviation: natural numbers for the indices `i`, `j` and `k`, the bound `i + j < 5` written as
`j < 5 - i`; `x % 64` for `x & 63`. -/
def twoadicK0 (km ap bp cp : Array Int) : Id Int := do
  let mut k0 : Int := 0
  for i in [0:5] do
    for j in [0:5 - i] do
      let k := 4 - i - j
      k0 := (k0 + km[(i * 5 + j) * 5 + k]! * ap[i]! * bp[j]! * cp[k]!) % 64
  return k0

/-- Whether the condition at 2 modulo `64` admits a triple with the coefficients `k₀`, `k₁`, `k₂` of
the Kummer equation, `a3 = a³` and `A0 = A₀` modulo `64`, given the tables `sol` and `sq` and the
word `odd` of the odd residues: for `v` odd, some `d` with `k₂ d² + k₁ d + k₀ ≡ 0` and
`a³ d + A₀` a square; else for `v = 2`, some odd `t` with `k₂ t² + 2 k₁ t + 4 k₀ ≡ 0` and
`8 (a³ t + 2 A₀)` a square; else for `v = 2 ^ e`, `e = 2, …, 6`, some odd `t` with
`k₂ t² + 2 ^ e k₁ t + 4 ^ e k₀ ≡ 0`, each search ending at the first success.

C: `j-points.c:1698-1699`, `j-points.c:1716-1729`

Deviation: a Boolean for the `int` `ok`; natural numbers for the indices `d` and `e`; the condition
`!ok` of the loops a `break` at the start of each step; the entries of `sol` and `sq` read at the
natural number of the index, which the reductions make nonnegative; `x % 64` for `x & 63`. -/
def twoadicAdmits (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) (k0 k1 k2 a3 A0 : Int) :
    Id Bool := do
  let mut ok := false
  let S := sol[((k2 * 64 + k1) * 64 + k0).toNat]!
  for d in [0:64] do
    if ok then break
    if (S >>> d.toUInt64) &&& 1 != 0 then ok := sq[((a3 * d + A0) % 64).toNat]!
  if !ok then
    let S := sol[((k2 * 64 + 2 * k1 % 64) * 64 + 4 * k0 % 64).toNat]! &&& odd
    for d in [1:64:2] do
      if ok then break
      if (S >>> d.toUInt64) &&& 1 != 0 then ok := sq[(8 * (a3 * d + 2 * A0) % 64).toNat]!
  for e in [2:7] do
    if ok then break
    let S := sol[((k2 * 64 + (k1 <<< e) % 64) * 64 + (k0 <<< (2 * e)) % 64).toNat]! &&& odd
    ok := S != 0
  return ok

/-- Whether the condition at 2 modulo `64` admits the triple `(a2, b2, c2)` modulo `64`, given the
coefficients `fm` and `km`, the tables `sol` and `sq`, the word `odd` and the powers `ap` and `bp`
of `a2` and `b2`: the powers of `c2` (`JPoints.twoadicPowers`), `k₀` (`JPoints.twoadicK0`),
`k₁ = -(4 f₀ a³ + 2 f₁ a² b + 4 f₂ a² c + 2 f₃ a b c + 4 f₄ a c² + 2 f₅ b c² + 4 f₆ c³)`,
`k₂ = b² - 4 a c`, `kk = b² - a c` and
`A₀ = f₂ a⁴ + f₃ a³ b + f₄ a² b² + f₅ a b kk + f₆ kk²` modulo `64`, and the test
`JPoints.twoadicAdmits`.

C: `j-points.c:1697`, `j-points.c:1707-1714`

Deviation: natural numbers for the residues `a2`, `b2` and `c2`; integers for the other `long`s;
`x % 64` for `x & 63`, equal also for the negative `x` of `k₂` and `kk` (two's complement). -/
def twoadicCell (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd : UInt64)
    (ap bp : Array Int) (a2 b2 c2 : Nat) : Id Bool := do
  let cp ← twoadicPowers c2
  let k0 ← twoadicK0 km ap bp cp
  let k1 := (64 - (4 * ap[3]! * fm[0]! + 2 * ap[2]! * b2 * fm[1]! + 4 * ap[2]! * c2 * fm[2]! +
    2 * a2 * b2 * c2 * fm[3]! + 4 * a2 * cp[2]! * fm[4]! + 2 * b2 * cp[2]! * fm[5]! +
    4 * cp[3]! * fm[6]!) % 64) % 64
  let k2 := (bp[2]! + 64 * 4 - 4 * a2 * c2) % 64
  let kk := (bp[2]! + 64 * 4 - a2 * c2) % 64
  let A0 := (fm[2]! * ap[4]! + fm[3]! * ap[3]! * b2 + fm[4]! * ap[2]! * bp[2]! +
    fm[5]! * a2 * b2 * kk + fm[6]! * kk * kk) % 64
  let a3 := ap[3]!
  twoadicAdmits sol sq odd k0 k1 k2 a3 A0

/-- The row of the class `(a2, b2)` modulo `64` in `twoadic_table`, given the coefficients, the
tables, the word `odd` and the powers `ap` and `bp` of `a2` and `b2`: the word of the residues
`c2 < 64` that `JPoints.twoadicCell` admits, the triples with `a2`, `b2` and `c2` all even skipped;
and the number of the admitted `c2`.

C: `j-points.c:1694`, `j-points.c:1696`, `j-points.c:1700`, `j-points.c:1730-1731`

Deviation: the number of the admitted `c2` returned, which the caller adds to the count that the C
code increments for each; natural numbers for the residues and the count. -/
def twoadicRow (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd : UInt64)
    (ap bp : Array Int) (a2 b2 : Nat) : Id (UInt64 × Nat) := do
  let mut mask : UInt64 := 0
  let mut count := 0
  for c2 in [0:64] do
    if (a2 ||| b2 ||| c2) &&& 1 == 0 then continue
    if ← twoadicCell fm km sol sq odd ap bp a2 b2 c2 then
      mask := mask ||| (1 : UInt64) <<< c2.toUInt64
      count := count + 1
  return (mask, count)

/-- The classes `(a2, b2)` modulo `64` of `twoadic_table`, given the coefficients, the tables, the
word `odd`, and the arrays `masks` and `alive`: for each class the powers of `a2` and
`b2` (`JPoints.twoadicPowers`) and its row (`JPoints.twoadicRow`), the word stored at
`a2 * 64 + b2` in `masks` and whether it is not zero in `alive`, the empty classes and the admitted
triples counted.

C: `j-points.c:1665`, `j-points.c:1689-1691`, `j-points.c:1693`, `j-points.c:1732-1736`

Deviation: the arrays taken and returned with the counts, for the arrays and the integer that the
arguments of the C code point to and for its result; natural numbers for the residues and the
counts; the count of each row added after its loop. -/
def twoadicClasses (fm km : Array Int) (sol : Array UInt64) (sq : Array Bool) (odd : UInt64)
    (masks : Array UInt64) (alive : Array Bool) : Id TwoadicTable := do
  let mut masks := masks
  let mut alive := alive
  let mut count := 0
  let mut empty := 0
  for a2 in [0:64] do
    let ap ← twoadicPowers a2
    for b2 in [0:64] do
      let bp ← twoadicPowers b2
      let (mask, n) ← twoadicRow fm km sol sq odd ap bp a2 b2
      count := count + n
      masks := masks.set! (a2 * 64 + b2) mask
      alive := alive.set! (a2 * 64 + b2) (mask != 0)
      if mask == 0 then empty := empty + 1
  return { masks, alive, empty, count }

/-- The table of the condition at 2 modulo `64` as `twoadic_table` builds it into the arrays `masks`
and `alive`, for the coefficients `coeffs` of the curve searched and `k` of the quartic `K₀`: the
word `odd` of the odd residues, the squares (`JPoints.twoadicSquares`), the solutions of the
quadratic equations (`JPoints.twoadicSol`), the coefficients modulo `64` (`JPoints.twoadicCoeffs`),
and the classes (`JPoints.twoadicClasses`).

C: `j-points.c:1660-1661`, `j-points.c:1662`, `j-points.c:1664`, `j-points.c:1666-1667`,
`j-points.c:1669`, `j-points.c:1738-1739`

Deviation: the arrays taken and returned, for those that the arguments point to; the scratch array
`sol` a value, its allocation and release (`j-points.c:1663`, `j-points.c:1668`, `j-points.c:1737`,
with the exit of a failed allocation) memory management, not modeled. -/
def twoadicTable (coeffs : Array Int) (k : KummerCoeffs) (masks : Array UInt64)
    (alive : Array Bool) : Id TwoadicTable := do
  let mut odd : UInt64 := 0
  for d in [1:64:2] do odd := odd ||| (1 : UInt64) <<< d.toUInt64
  let sq ← twoadicSquares
  let sol ← twoadicSol
  let (fm, km) ← twoadicCoeffs coeffs k
  twoadicClasses fm km sol sq odd masks alive

/-! ### The condition at 2 -/

/-- The condition at 2 as `twoadic_init` decides it from the globals `t`, for the coefficients
`coeffs` of the curve searched and `k` of the quartic `K₀`: the table modulo `64` into `mask2` and
`alive2`; if it admits all `64³ - 32³` triples not all even, the condition is not used; otherwise
the density of the admitted triples among them and the fraction of the empty classes among the
`64²`, and the condition used. A table modulo `16` cannot decide it: it may admit every triple
where the table modulo `64` does not (for `y² = x⁶ + 8 x⁵ + 22 x⁴ + 22 x³ + 5 x² + 6 x + 1` it
admits every triple, the table modulo `64` six in seven of them).

C: `j-points.c:1741-1753`

Deviation: the globals taken and returned; `Float`s for the doubles, the integers converted
exactly. -/
def twoadicInit (coeffs : Array Int) (k : KummerCoeffs) (t : TwoAdic) : Id TwoAdic := do
  let r ← twoadicTable coeffs k t.mask2 t.alive2
  if r.count == 64 * 64 * 64 - 32 * 32 * 32 then
    return { t with mask2 := r.masks, alive2 := r.alive, use2 := false }
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

-- The hash of the words of the classes `(a2, b)` modulo `64`, `b < 64`, of the curve `cs`, by
-- `JPoints.twoadicRow` with the tables `sol` and `sq` modulo `64` and the word of the odd residues,
-- and the number of those classes that admit some `c`.
private def row64 (cs : Array Int) (sol : Array UInt64) (sq : Array Bool) (a2 : Nat) :
    UInt64 × Nat :=
  let (fm, km) := (twoadicCoeffs cs (kummerInit cs)).run
  let ap := (twoadicPowers a2).run
  let ms := (List.range 64).map fun b2 ↦
    (twoadicRow fm km sol sq 0xAAAAAAAAAAAAAAAA ap (twoadicPowers b2).run a2 b2).run.1
  (hash ms.toArray, (ms.filter (· != 0)).length)

-- Rows of the tables modulo `64`: classes `(a, b)` for `a = 0`, odd and even `a`, with some that
-- admit no `c`; for example 1 of the README the classes `(1, b)` with odd `b` admit only the even
-- `c`, those with even `b` every `c`.
#guard
  let sq := twoadicSquares.run
  let sol := twoadicSol.run
  [(#[1, 4, 3, -8, 2, 8, 7], 0, 7016487823355143136, 16),
    (#[1, 4, 3, -8, 2, 8, 7], 1, 15041384481810647792, 64),
    (#[1, 4, 3, -8, 2, 8, 7], 2, 7961040906164032320, 32),
    (#[1, 4, 3, -8, 2, 8, 7], 6, 10794700154590699872, 32),
    (#[1, 1, -2, -15, 13, 2, 1], 3, 12075669951607617960, 64),
    (#[1, 1, -2, -15, 13, 2, 1], 32, 18248219748053102752, 64),
    (#[1, 6, 5, 22, 22, 8, 1], 1, 11135518375232067904, 64)].all
  fun (cs, a2, h, n) ↦ row64 cs sol sq a2 == (h, n)

-- The condition at 2 not used: the table modulo `64` admits everything, for the curve of Müller
-- and Stoll with ten-digit coefficients; the table is written all the same, and the density and
-- the fraction of the empty classes keep their initial values.
#guard
  let cs := #[247747600, -985905640, 567207969, 2396040466, 52485681, -470135160, 82342800]
  let t := (twoadicInit cs (kummerInit cs) TwoAdic.initial).run
  !t.use2 && t.density2.toBits == 0x3ff0000000000000 && t.empty2.toBits == 0 &&
    hash t.mask2 == 9146613197977768960 &&
    hash (t.alive2.map fun v ↦ if v then 1 else 0) == 12483119227067801600

-- The condition at 2 used: for example 1 of the README of `j-points`, whose table modulo `64`
-- admits six in seven of the triples, and for the monic quintic of its
-- example 2; the density of the admitted triples and the fraction of the empty classes by their
-- bits, and the hashes of the table.
#guard [(#[1, 6, 5, 22, 22, 8, 1], 0x3feb6db6db6db6db, 0, 18262992123156843520,
      12483119227067801600),
    (#[1, 178, 817, -274, 16, 1, 0], 0x3fd3249249249249, 0x3fd7000000000000, 5989795456754180160,
      8837732247861813312)].all fun (cs, d, e, hm, ha) ↦
  let t := (twoadicInit cs (kummerInit cs) TwoAdic.initial).run
  t.use2 && t.density2.toBits == d && t.empty2.toBits == e && hash t.mask2 == hm &&
    hash (t.alive2.map fun v ↦ if v then 1 else 0) == ha

end JPoints

end
