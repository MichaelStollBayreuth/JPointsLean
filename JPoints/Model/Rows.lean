/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Tables

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Tables

/-!
# The rows of the sieve tables

The sieve tables of the primes of the first two stages of the sieve of `j-points`, as `init_sieve`
builds them (`JPoints.initSieve`). The table of a sieving prime `p ≤ JPoints.maxTablePrime` has
`p * p` rows of `sieve_rowlen(p) = p + 1` words (`JPoints.sieveRowlen`), one row for each class
`(a, b)` modulo `p` of the first two coordinates; bit `j` of word `c` of the row of `(a, b)` is set
exactly when the sieve admits the triples `(a, b, c')` with `c' ≡ 64 c + j (mod p)`. For each prime
(`JPoints.initSievePrime`) the C code first writes the pattern of each row, `k p` bits for the least
multiple `k p` of `p` that is at least `64`, into the row of `(a, b)` of the global array `help`:
the row of `(0, 0)` all ones (`JPoints.initSieveClear`), the rows of `(0, b)` for `b ≠ 0` from the
points at infinity and the values of `f` that are squares (`JPoints.initSieveInfinity`), the rows of
`(a, b)` for `a ≠ 0` from the exact table of the third stage (`JPoints.initSieveOnJ`). It then
unrolls each pattern over the `p` words of the period of the row, by a rotation of the words of the
row of `help` in place, and copies word `0` to word `p` (`JPoints.initSieveRow`,
`JPoints.initSieveRotate`, `JPoints.initSieveRows`).

## Main definitions

* `JPoints.sievePeriod`, `JPoints.sieveRowlen`: the period and the length, in words, of a row of the
  table of a prime.
* `JPoints.SieveTables`, `JPoints.SieveTables.initial`, `JPoints.helpWidth`: the sieve tables and
  the array `help`.
* `JPoints.initSieveClear`, `JPoints.initSieveInfinity`, `JPoints.initSieveOnJ`: the patterns of
  the rows in `help`.
* `JPoints.initSieveRotate`, `JPoints.initSieveRow`, `JPoints.initSieveRows`: the rows of the
  table of a prime from their patterns.
* `JPoints.initSievePrime`, `JPoints.initSieve`: the table of a prime, and the tables of the
  sieving primes of the first two stages.

## Implementation notes

The tables are arrays of words, `sieve_tab[pn]` an array of `p * p * (p + 1)` words with the row of
`(a, b)` from `(a p + b) (p + 1)` on, and `help` one flat array of
`JPoints.maxTablePrime * JPoints.maxTablePrime` rows of `JPoints.helpWidth` words, `help[a][b][c]`
at `(a * maxTablePrime + b) * helpWidth + c`, with the index arithmetic of the C code; indices into
the table and into `help` take the place of the pointers `si` and `he`. The indices, the counters
and the primes, which the C code keeps nonnegative, are natural numbers. `help` is a global of
static storage, which `init_sieve` changes in place and leaves rotated, and the model threads it
through the run with the tables. The primes of the first two stages and their number, which the
choice of the primes leaves in `pnn` and `sieve_primes2`, are arguments.
-/

@[expose] public section

namespace JPoints

/-! ### The length of a row -/

/-- `sieve_period(p)`, the period in words of the row of the prime `p` that the walk of the sieve
reads: the least multiple of `p` that is at least `VW` words, `p` itself for `p ≥ 1`.

C: `j-sift.c:66-70`

Deviation: `1` for the macro `VW`, the width of the walk in the scalar build modelled; natural
numbers for the `long`s `p` and `P`, here `period`. -/
def sievePeriod (p : Nat) : Id Nat := do
  let mut period := p
  while period < 1 do period := period + p
  return period

/-- `sieve_rowlen(p)`, the number of words of a row of the table of the prime `p`: its period
(`JPoints.sievePeriod`) and `VW` words of its continuation, `p + 1` for `p ≥ 1`.

C: `j-sift.c:71`

Deviation: `1` for the macro `VW`, the width of the walk in the scalar build modelled; natural
numbers for the `long`s. -/
def sieveRowlen (p : Nat) : Id Nat := do
  return (← sievePeriod p) + 1

/-! ### The tables -/

/-- `MAX_TABLE_PRIME / LONG_LENGTH + 2`, the number of words of a row of `help`, the third dimension
of the array: enough for the pattern of `⌈64 / p⌉ p < 64 + p` bits of a prime
`p ≤ JPoints.maxTablePrime`.

C: `j-points.c:1084` -/
def helpWidth : Nat := maxTablePrime / longLength + 2

/-- The sieve tables of the primes of the first two stages, the global `sieve_tab`, and the array
`help` from which `init_sieve` builds them.

C: `j-points.c:199`, `j-points.c:1084`

Deviation: an array of arrays for the array of pointers `sieve_tab`, the empty array for a null
pointer; a flat array for the array `help`, with the index arithmetic of the C code; a structure,
for the globals. -/
structure SieveTables where
  /-- `sieve_tab`: at `pn < sieve_primes2`, the table of the sieving prime `p = prime[pnn[pn]]`,
  `p * p` rows of `JPoints.sieveRowlen p = p + 1` words, the row of `(a, b)` for `a, b < p` from
  word `(a p + b) (p + 1)` on, whose bit `j` of word `c` is set exactly when the sieve admits the
  triples `(a, b, c')` with `c' ≡ 64 c + j (mod p)`: all of them for `a = b = 0`; for `a = 0` and
  `b ≠ 0` when the curve has points at infinity modulo `p` and `f(c' / b)` is a square modulo `p`;
  for `a ≠ 0` when the exact table of the third stage admits `(1, b / a, c' / a)`. The row is
  periodic in `c` with period `p`, and word `p` repeats word `0`. Empty beyond `sieve_primes2`. -/
  sieveTab : Array (Array UInt64)
  /-- `help`, `JPoints.maxTablePrime × JPoints.maxTablePrime` rows of `JPoints.helpWidth` words,
  `help[a][b][c]` at `(a * maxTablePrime + b) * helpWidth + c`: for the prime whose table
  `init_sieve` builds, bit `j` of word `c` of the row of `(a, b)`, for `a, b < p`, is the bit of
  `64 c + j < k p` of the pattern of the row of `(a, b)` of its table, `k p = ⌈64 / p⌉ p`, until
  the rotation of `JPoints.initSieveRotate` changes the row. -/
  help : Array UInt64

/-- The sieve tables when the program starts: the null pointers of `sieve_tab` and the zeros of
`help`, as for globals of static storage.

C: `j-points.c:199`, `j-points.c:1084` -/
def SieveTables.initial : SieveTables where
  sieveTab := Array.replicate numPrimes #[]
  help := Array.replicate (maxTablePrime * maxTablePrime * helpWidth) 0

/-! ### The patterns of the rows -/

/-- The array `help` with the words `c ≤ aa` of the rows `(a, b)` for `a, b < p` cleared, and then
the words `c ≤ aa` of the row of `(0, 0)`, the first, set to all ones: the sieve admits every
triple whose first two coordinates are divisible by `p`.

C: `j-points.c:1110-1114`

Deviation: the array passed and returned, for the global; natural numbers for the nonnegative
`long`s; `c` for the index `(0 * maxTablePrime + 0) * helpWidth + c` of `help[0][0][c]`. -/
def initSieveClear (help : Array UInt64) (p aa : Nat) : Id (Array UInt64) := do
  let mut help := help
  for a in [0:p] do
    for b in [0:p] do
      for c in [0:aa + 1] do
        help := help.set! ((a * maxTablePrime + b) * helpWidth + c) 0
  for c in [0:aa + 1] do
    help := help.set! c (~~~0)
  return help

/-- The array `help` with the patterns of the rows `(0, b)` for `0 < b < p` or-ed in, for the prime
`p = prime[n]` and `kp = ⌈64 / p⌉ p`: when the curve has points at infinity modulo `p`
(`has_infinity[n]`), for each `c < p` with `f(c)` a square modulo `p` (`is_f_square[n][c]`) and each
`0 < b < p`, the bits `i < kp` with `i ≡ b c (mod p)` set, bit `i` being bit `i & 63` of word
`i >> 6`, from the table `bits` of the words with one bit set.

C: `j-points.c:1116-1121`

Deviation: the array passed and returned, for the global; the tables of the curve and the table
`bits` passed, for the globals that the C code reads; natural numbers for the nonnegative `long`s,
so that `(b*c)%p` is the remainder of natural numbers; the loop over `i` with the step `p` a `while`
loop, as C's `for` loop is, for a range of Lean needs a proof that its step is positive;
`b * helpWidth + w` for the index `(0 * maxTablePrime + b) * helpWidth + w` of `help[0][b][w]`. -/
def initSieveInfinity (bits : Array UInt64) (ct : CurveTables) (help : Array UInt64)
    (n p kp : Nat) : Id (Array UInt64) := do
  let mut help := help
  if ct.hasInfinity[n]! then
    for c in [0:p] do
      if ct.isFSquare[n * maxPrimeEven + c]! then
        for b in [1:p] do
          let mut i := b * c % p
          while i < kp do
            let j := b * helpWidth + (i >>> longShift)
            help := help.set! j (help[j]! ||| bits[i &&& longMask]!)
            i := i + p
  return help

/-- The array `help` with the patterns of the rows `(a, b)` for `0 < a < p` or-ed in, for the prime
`p = prime[n]` and `kp = ⌈64 / p⌉ p`: for each class `(1, b, c)` that the exact table of the third
stage admits (`is_point_on_j[n][b][c]`) and each `0 < a < p`, in the row of `(a, a b mod p)` the
bits `i < kp` with `i ≡ a c (mod p)` set, bit `i` being bit `i & 63` of word `i >> 6`, from the
table `bits` of the words with one bit set.

C: `j-points.c:1123-1130`

Deviation: the array passed and returned, for the global; the tables of the curve and the table
`bits` passed, for the globals that the C code reads; natural numbers for the nonnegative `long`s,
so that `(a*b)%p` and `(a*c)%p` are remainders of natural numbers; the loop over `i` with the step
`p` a `while` loop, as C's `for` loop is, for a range of Lean needs a proof that its step is
positive. -/
def initSieveOnJ (bits : Array UInt64) (ct : CurveTables) (help : Array UInt64) (n p kp : Nat) :
    Id (Array UInt64) := do
  let mut help := help
  for b in [0:p] do
    for c in [0:p] do
      if ct.isPointOnJ[(n * maxPrimeEven + b) * maxPrimeEven + c]! then
        for a in [1:p] do
          let ab := a * b % p
          let mut i := a * c % p
          while i < kp do
            let j := (a * maxTablePrime + ab) * helpWidth + (i >>> longShift)
            help := help.set! j (help[j]! ||| bits[i &&& longMask]!)
            i := i + p
  return help

/-! ### The rows from their patterns -/

/-- The rotation of `init_sieve` for the row `si` of the table `tab` of the prime `p` and the row
`he` of `help`, from word `wp` of the row on: for `c = wp, …, p - 1`, with the cursor `c1` from `wp`
on through the ring of the words `0, …, wp` of `he`, the low `diff` bits (the mask `diffMask`) of
the word after `c1` shifted left by `diffShift` and or-ed into word `c1`, which becomes word `c` of
the row, then the cursor moved on and its word shifted right by `diff`.

C: `j-points.c:1160-1166`

Deviation: indices into the arrays for the pointers `si` and `he`, and the table and `help` passed
and returned, for the table that `si` points into and the global; the values of the variables of
`init_sieve` that the loop reads passed; natural numbers for the nonnegative `long`s, and the
counter `c` of the loop from `wp`, the value that the copy of the words `c < wp` of the row in
`init_sieve` leaves in it. -/
def initSieveRotate (tab help : Array UInt64) (p si he wp diffShift diff : Nat)
    (diffMask : UInt64) : Id (Array UInt64 × Array UInt64) := do
  let mut tab := tab
  let mut help := help
  let mut c1 := wp
  for c in [wp:p] do
    help := help.set! (he + c1)
      (help[he + c1]! ||| (help[he + if c1 == wp then 0 else c1 + 1]! &&& diffMask) <<<
        diffShift.toUInt64)
    tab := tab.set! (si + c) help[he + c1]!
    c1 := if c1 == wp then 0 else c1 + 1
    help := help.set! (he + c1) (help[he + c1]! >>> diff.toUInt64)
  return (tab, help)

/-- The table `tab` of the prime `p` with the row of `(a, b)` written from the pattern in the row
`he` of `(a, b)` of `help`, and `help` with that row rotated: for `p1 = (⌊64 / p⌋ + 1) p`, the least
multiple of `p` above `64`, `diff_shift = p1 & 63`, `diff = 64 - diff_shift` and `wp = p1 >> 6`, the
words `c < wp` of the row copied from `he`, the words `c = wp, …, p - 1` by the rotation
(`JPoints.initSieveRotate`), and the words from `p` to the end of the row (`JPoints.sieveRowlen`)
the copies of the words `p` before them. For an odd `p`, `p1 = kp = 64 wp + diff_shift`, and word
`c < p` of the row holds the bits `64 c, …, 64 c + 63` of the pattern repeated with period `p`; word
`p` repeats word `0`.

C: `j-points.c:1149-1158`, `j-points.c:1168-1169`

Deviation: indices into the arrays for the pointers `si` and `he`, and the table and `help` passed
and returned, for the table that `si` points into and the global; `sieve_rowlen(p)` computed once,
for its calls at `j-points.c:1149` and in the test of the last loop, which give the same value;
natural numbers for the nonnegative `long`s, so that `LONG_LENGTH/p` is the division of natural
numbers, as for its unsigned operand, and the counter `c` of the last loop from `p`, where the C
code goes on with `c` from the rotation, the same since `wp ≤ p`; `~(bit_array)(-1L<<diff)` as the
complement of the word of all ones shifted left by `diff`, as gcc computes the left shift of the
negative `-1L`, which ISO C leaves undefined. -/
def initSieveRow (tab help : Array UInt64) (p a b : Nat) : Id (Array UInt64 × Array UInt64) := do
  let rowlen ← sieveRowlen p
  let si := (a * p + b) * rowlen
  let he := (a * maxTablePrime + b) * helpWidth
  let p1 := (longLength / p + 1) * p
  let diffShift := p1 &&& longMask
  let diff := longLength - diffShift
  let diffMask := ~~~((~~~0 : UInt64) <<< diff.toUInt64)
  let wp := p1 >>> longShift
  let mut tab := tab
  let mut help := help
  for c in [0:wp] do tab := tab.set! (si + c) help[he + c]!
  (tab, help) ← initSieveRotate tab help p si he wp diffShift diff diffMask
  for c in [p:rowlen] do tab := tab.set! (si + c) tab[si + c - p]!
  return (tab, help)

/-- The table `tab` of the prime `p` with every row `(a, b)`, `a, b < p` in this order, written from
its pattern in `help`, and `help` with the rows rotated (`JPoints.initSieveRow`).

C: `j-points.c:1147-1148`

Deviation: the table and `help` passed and returned, for the table that `sieve_tab[pn]` points to
and the global; natural numbers for the nonnegative `long`s `a` and `b`. -/
def initSieveRows (tab help : Array UInt64) (p : Nat) : Id (Array UInt64 × Array UInt64) := do
  let mut tab := tab
  let mut help := help
  for a in [0:p] do
    for b in [0:p] do
      (tab, help) ← initSieveRow tab help p a b
  return (tab, help)

/-! ### The tables of the primes -/

/-- The table of the prime `p = prime[n]` as `init_sieve` builds it, with the tables `t` and the
tables of the curve `ct`, and `help` as it leaves it: for `k = ⌈64 / p⌉` and `kp = k p`, and
`aa = max(1, p >> 6)`, the last word of the rows of `help` that the clear reaches, the patterns of
the rows in `help` (`JPoints.initSieveClear`, `JPoints.initSieveInfinity`,
`JPoints.initSieveOnJ`), then the rows of a fresh table of `p * p * sieve_rowlen(p)` words
(`JPoints.initSieveRows`).

C: `j-points.c:1097-1099`, `j-points.c:1103-1104`

Deviation: the table returned, for the table that the C code allocates and stores in `sieve_tab`
(`j-points.c:1100-1101`, memory management, not modelled), a fresh array of zeros, every word of
which the rows write; `help` passed and returned, for the global; the tables passed, for the
globals that the C code reads; natural numbers for the nonnegative `long`s, so that `/` is the
division of natural numbers, as for the unsigned operand `LONG_LENGTH + p - 1`. -/
def initSievePrime (t : Tables) (ct : CurveTables) (n : Nat) (help : Array UInt64) :
    Id (Array UInt64 × Array UInt64) := do
  let p := primeTable[n]!
  let k := (longLength + p - 1) / p
  let kp := k * p
  let tab : Array UInt64 := Array.replicate (p * p * (← sieveRowlen p)) 0
  let mut aa := p >>> longShift
  if aa == 0 then aa := 1
  let help ← initSieveClear help p aa
  let help ← initSieveInfinity t.bits ct help n p kp
  let help ← initSieveOnJ t.bits ct help n p kp
  initSieveRows tab help p

/-- The sieve tables `st` with the table of each sieving prime of the first two stages built, as
`init_sieve` builds them: for `pn < sievePrimes2`, the table of the prime `prime[pnn[pn]]`
(`JPoints.initSievePrime`) stored at `pn` of `sieve_tab`, with the tables `t` and the tables of the
curve `ct`, and `help` threaded from one prime to the next.

C: `j-points.c:1087-1089`, `j-points.c:1094-1096`, `j-points.c:1183-1185`

Deviation: the sieve tables passed and returned, for the globals `sieve_tab` and `help`; the
indices of the sieving primes in the table and their number in the first two stages passed, for
the globals `pnn` and `sieve_primes2`, and the tables passed, for the globals that the C code
reads; each table stored once it is filled, for the pointer that the C code stores before it fills
the table through it; natural numbers for the nonnegative `long`s `pn` and `n`. -/
def initSieve (t : Tables) (ct : CurveTables) (pnn : Array Nat) (sievePrimes2 : Nat)
    (st : SieveTables) : Id SieveTables := do
  let ⟨sieveTab, help⟩ := st
  let mut sieveTab := sieveTab
  let mut help := help
  for pn in [0:sievePrimes2] do
    let n := pnn[pn]!
    let (tab, help') ← initSievePrime t ct n help
    sieveTab := sieveTab.set! pn tab
    help := help'
  return ⟨sieveTab, help⟩

/-! ### Examples

The values of the C code at the pin, from a test program that sets the tables of the curve and of
the primes as `init_fmodpsquare` and `init_table` fill them, sets `pnn` and `sieve_primes2`, clears
`help` and `sieve_tab` as at the start of the program, and calls `init_sieve` of `j-points.c`. A
table is compared by its hash, `h ↦ h * 1000003 + v` modulo `2 ^ 64` over its words in the order of
their indices, from `h = 0`, and by some of its rows; `help` after the call by its hash. -/

-- The hash of the examples over the words `vs`.
private def hash (vs : Array UInt64) : UInt64 := vs.foldl (fun h v ↦ h * 1000003 + v) 0

-- The tables of the curve with the coefficients `cs` and the degree `d` modulo the primes
-- `primeTable[n]` for `n ∈ ns`, as `init_fmodpsquare` fills them (the coefficients reduced into
-- `[0, p)`, the points at infinity, the values of `f` that are squares, by Horner's rule) and as
-- `JPoints.initTable` fills the exact table of the third stage.
private def curveTables (t : Tables) (cs : Array Int) (d : Nat) (ns : List Nat) : CurveTables :=
  ns.foldl (init := CurveTables.initial) fun ct n ↦
    let p : Int := (primeTable[n]! : Nat)
    let cm := (List.range 7).foldl (fun a i ↦ a.set! (n * 8 + i) (cs[i]! % p)) ct.coeffsModP
    let square (x : Int) : Bool := t.squares[n * maxPrime + x.toNat]! != p
    let f (x : Nat) : Int :=
      (List.range d).reverse.foldl (fun s i ↦ (s * x + cm[n * 8 + i]!) % p) cm[n * 8 + d]!
    let ct := { ct with
      coeffsModP := cm
      hasInfinity := ct.hasInfinity.set! n (square cm[n * 8 + 6]!)
      isFSquare := (List.range p.toNat).foldl
        (fun a x ↦ a.set! (n * maxPrimeEven + x) (square (f x))) ct.isFSquare }
    (initTable t ct d n).run.1

-- The words of the row of `(a, b)` of the table `k` of `st`, of the prime `p`.
private def row (st : SieveTables) (k p a b : Nat) : List UInt64 :=
  ((st.sieveTab[k]?.getD #[]).extract ((a * p + b) * (p + 1)) ((a * p + b + 1) * (p + 1))).toList

-- The words `0`, `1`, `p - 1` and `p` of the row of `(a, b)` of the table `k` of `st`, of the
-- prime `p`.
private def rowEnds (st : SieveTables) (k p a b : Nat) : List (Option UInt64) :=
  let r := row st k p a b
  [r[0]?, r[1]?, r[p - 1]?, r[p]?]

#guard primeTable.all fun p ↦ (sievePeriod p).run == p && (sieveRowlen p).run == p + 1
#guard helpWidth == 3 && SieveTables.initial.help.size == 48387

-- The sextic `1 + 4 x + 3 x² - 8 x³ + 2 x⁴ + 8 x⁵ + 7 x⁶` with the primes `61, 3, 127, 5, 67, 7`
-- in the first two stages (`7` is no square modulo `5`, `61`, `67` and `127`, so these rows of
-- `(0, b)` are empty): the hashes of the tables and of `help`, the ends of five rows of the
-- tables of `61`, `127` and `67`, and four rows of the tables of `3`, `5` and `7`.
#guard
  let t := (initMain Tables.initial).run
  let pnn := #[16, 0, 29, 1, 17, 2]
  let st := (initSieve t (curveTables t #[1, 4, 3, -8, 2, 8, 7] 6 pnn.toList) pnn 6
    SieveTables.initial).run
  st.sieveTab.map hash == #[7575099805749797294, 5511373288425562676, 13381649723565379676,
      9219609252900939298, 16055791616509475644, 13117554829618209974] ++
      Array.replicate (numPrimes - 6) 0 &&
    hash st.help == 4228235161795815893 &&
    [(0, 61, [(0, 0, [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
        0xffffffffffffffff]), (0, 1, [0x0, 0x0, 0x0, 0x0]),
      (1, 0, [0x22e8458a80004439, 0xe45d08b150000887, 0x17422c54000221c8, 0x22e8458a80004439]),
      (2, 5, [0x20e003c1fe2562c1, 0x41c00783fc4ac58, 0x7001e0ff12b1608, 0x20e003c1fe2562c1]),
      (60, 59, [0x7cc390b3bad74653, 0x4f987216775ae8ca, 0xe61c859dd6ba329f,
        0x7cc390b3bad74653])]),
    (2, 127, [(0, 0, [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
        0xffffffffffffffff]), (0, 1, [0x0, 0x0, 0x0, 0x0]),
      (1, 0, [0x8004420c64c10133, 0xd404c99c41b866a9, 0xa80993388370cd53, 0x8004420c64c10133]),
      (2, 5, [0x32ca51631cac2581, 0x83420eb00e2200fd, 0x6841d601c4401fa, 0x32ca51631cac2581]),
      (126, 125, [0x92b4304315c02874, 0x5460e6f98cba9514, 0xa8c1cdf319752a29,
        0x92b4304315c02874])]),
    (4, 67, [(0, 0, [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
        0xffffffffffffffff]), (0, 1, [0x0, 0x0, 0x0, 0x0]),
      (1, 0, [0xc254708a2bd1d553, 0x12a384515e8eaa9c, 0x984a8e11457a3aaa, 0xc254708a2bd1d553]),
      (2, 5, [0xa341b1b0507116ed, 0x1a0d8d828388b76b, 0x746836360a0e22dd, 0xa341b1b0507116ed]),
      (66, 65, [0x9e12151024875cbd, 0xf090a881243ae5ec, 0x93c242a20490eb97,
        0x9e12151024875cbd])])].all
      (fun (k, p, rs) ↦ rs.all fun (a, b, ws) ↦ rowEnds st k p a b == ws.map some) &&
    [(1, 3, [(0, 1, [0xdb6db6db6db6db6d, 0x6db6db6db6db6db6, 0xb6db6db6db6db6db,
        0xdb6db6db6db6db6d]),
      (1, 0, [0x9249249249249249, 0x4924924924924924, 0x2492492492492492, 0x9249249249249249]),
      (2, 2, [0x6db6db6db6db6db6, 0xb6db6db6db6db6db, 0xdb6db6db6db6db6d, 0x6db6db6db6db6db6]),
      (2, 1, [0xdb6db6db6db6db6d, 0x6db6db6db6db6db6, 0xb6db6db6db6db6db, 0xdb6db6db6db6db6d])]),
    (3, 5, [(0, 1, [0x0, 0x0, 0x0, 0x0, 0x0, 0x0]),
      (1, 0, [0xb5ad6b5ad6b5ad6b, 0x6b5ad6b5ad6b5ad6, 0xd6b5ad6b5ad6b5ad, 0xad6b5ad6b5ad6b5a,
        0x5ad6b5ad6b5ad6b5, 0xb5ad6b5ad6b5ad6b]),
      (4, 4, [0x2108421084210842, 0x4210842108421084, 0x8421084210842108, 0x842108421084210,
        0x1084210842108421, 0x2108421084210842]),
      (2, 1, [0xe739ce739ce739ce, 0xce739ce739ce739c, 0x9ce739ce739ce739, 0x39ce739ce739ce73,
        0x739ce739ce739ce7, 0xe739ce739ce739ce])]),
    (5, 7, [(0, 1, [0xd5ab56ad5ab56ad5, 0x6ad5ab56ad5ab56a, 0xb56ad5ab56ad5ab5,
        0x5ab56ad5ab56ad5a, 0xad5ab56ad5ab56ad, 0x56ad5ab56ad5ab56, 0xab56ad5ab56ad5ab,
        0xd5ab56ad5ab56ad5]),
      (1, 0, [0x93264c993264c993, 0xc993264c993264c9, 0x64c993264c993264, 0x3264c993264c9932,
        0x993264c993264c99, 0x4c993264c993264c, 0x264c993264c99326, 0x93264c993264c993]),
      (6, 6, [0x3e7cf9f3e7cf9f3e, 0x9f3e7cf9f3e7cf9f, 0xcf9f3e7cf9f3e7cf, 0xe7cf9f3e7cf9f3e7,
        0xf3e7cf9f3e7cf9f3, 0xf9f3e7cf9f3e7cf9, 0x7cf9f3e7cf9f3e7c, 0x3e7cf9f3e7cf9f3e]),
      (2, 1, [0xa74e9d3a74e9d3a7, 0xd3a74e9d3a74e9d3, 0xe9d3a74e9d3a74e9, 0x74e9d3a74e9d3a74,
        0x3a74e9d3a74e9d3a, 0x9d3a74e9d3a74e9d, 0x4e9d3a74e9d3a74e, 0xa74e9d3a74e9d3a7])])].all
      fun (k, p, rs) ↦ rs.all fun (a, b, ws) ↦ row st k p a b == ws

-- The monic quintic `1 + 178 x + 817 x² - 274 x³ + 16 x⁴ + x⁵` (`degree = 5`, so that the curve
-- has points at infinity modulo every prime) with `pnn = (7, 3, 67)` and two primes in the first
-- two stages, so that `67` gets no table: the hashes of the tables and of `help`, and four rows.
#guard
  let t := (initMain Tables.initial).run
  let pnn := #[2, 0, 17]
  let st := (initSieve t (curveTables t #[1, 178, 817, -274, 16, 1, 0] 5 pnn.toList) pnn 2
    SieveTables.initial).run
  st.sieveTab.map hash == #[11568216707520771254, 3768494039584431942] ++
      Array.replicate (numPrimes - 2) 0 &&
    st.sieveTab[2]?.map Array.size == some 0 && hash st.help == 1279112090122557717 &&
    row st 0 7 6 6 == [0xb162c58b162c58b1, 0x58b162c58b162c58, 0x2c58b162c58b162c,
      0x162c58b162c58b16, 0x8b162c58b162c58b, 0xc58b162c58b162c5, 0x62c58b162c58b162,
      0xb162c58b162c58b1] &&
    row st 0 7 0 1 == [0xb366cd9b366cd9b3, 0xd9b366cd9b366cd9, 0x6cd9b366cd9b366c,
      0x366cd9b366cd9b36, 0x9b366cd9b366cd9b, 0xcd9b366cd9b366cd, 0x66cd9b366cd9b366,
      0xb366cd9b366cd9b3] &&
    row st 1 3 0 1 == [0xb6db6db6db6db6db, 0xdb6db6db6db6db6d, 0x6db6db6db6db6db6,
      0xb6db6db6db6db6db] &&
    row st 1 3 2 1 == [0x6db6db6db6db6db6, 0xb6db6db6db6db6db, 0xdb6db6db6db6db6d,
      0x6db6db6db6db6db6]

-- The sextic `-7 + 6 x² + 6 x³ + 10 x⁴ - 7 x⁵ - 3 x⁶` with the primes `3, 5, 7`: the hashes of
-- the tables and of `help`, and two rows.
#guard
  let t := (initMain Tables.initial).run
  let pnn := #[0, 1, 2]
  let st := (initSieve t (curveTables t #[-7, 0, 6, 6, 10, -7, -3] 6 pnn.toList) pnn 3
    SieveTables.initial).run
  st.sieveTab.map hash == #[7026569713432772986, 5177411538680879768, 9644480799571894134] ++
      Array.replicate (numPrimes - 3) 0 &&
    hash st.help == 3448016111946525521 &&
    row st 0 3 2 2 == [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff] &&
    row st 2 7 2 1 == [0x162c58b162c58b16, 0x8b162c58b162c58b, 0xc58b162c58b162c5,
      0x62c58b162c58b162, 0xb162c58b162c58b1, 0x58b162c58b162c58, 0x2c58b162c58b162c,
      0x162c58b162c58b16]

-- The rows of the same tables against the classes that they admit: bit `j` of word `w ≤ p` of the
-- row of `(a, b)` is set exactly when the sieve admits `(a, b, c)` for `c = (64 w + j) mod p`, that
-- is, always for `a = b = 0`, for `a = 0` when the curve has points at infinity modulo `p` (at `3`
-- and `7`, not at `5`) and `f(c / b)` is a square, and for `a ≠ 0` when the exact table admits
-- `(1, b / a, c / a)`.
#guard
  let t := (initMain Tables.initial).run
  let pnn := #[0, 1, 2]
  let ct := curveTables t #[-7, 0, 6, 6, 10, -7, -3] 6 pnn.toList
  let st := (initSieve t ct pnn 3 SieveTables.initial).run
  [0, 1, 2].all fun n ↦
    let p := primeTable[n]!
    let inv (x : Nat) : Nat := (t.inverses[n * maxPrimeEven + x]?.getD 0).toNat
    let admits (a b c : Nat) : Bool :=
      if a == 0 then b == 0 ||
        ct.hasInfinity[n]! && ct.isFSquare[n * maxPrimeEven + c * inv b % p]!
      else ct.isPointOnJ[(n * maxPrimeEven + b * inv a % p) * maxPrimeEven + c * inv a % p]!
    (List.range p).all fun a ↦ (List.range p).all fun b ↦
      let r := row st n p a b
      (List.range (p + 1)).all fun w ↦ (List.range 64).all fun j ↦
        (r[w]?.getD 0 >>> j.toUInt64 &&& 1 == 1) == admits a b ((64 * w + j) % p)

-- No prime in the first two stages: no table, and `help` untouched.
#guard
  let t := (initMain Tables.initial).run
  let st := (initSieve t (curveTables t #[3, 0, 0, 0, 0, 0, 1] 6 [0, 1]) #[0, 1] 0
    SieveTables.initial).run
  st.sieveTab.all (·.isEmpty) && hash st.help == 0

end JPoints

end
