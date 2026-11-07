/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Double

-- The `#guard` examples run code of the imported module at compile time.
meta import JPoints.Model.Double

/-!
# The compile-time constants of `j-points`

The constants that the C code of `j-points` fixes when it is compiled, each a definition with the
value of the default build and a docstring that names its macro: the table of the odd primes from
which the sieve takes its primes, the sizes of the tables and of the words, the bound on the height,
the defaults of the options, the defaults of the cost model, and the constants of the analysis of
the tube and of the real region. Changing a constant changes the model as changing the macro changes
the C program.

## Main definitions

* `JPoints.primeTable`: the odd primes of `prime[]`, those that the sieve may use.
* `JPoints.ceilDiv`: the macro `CEIL` of `j-points.h`.
* `JPoints.maxHeight`: the bound on the coordinates that the exact check takes in `long`s.
* `JPoints.maxSearchHeight`: the largest height bound that the program takes.
* `JPoints.costAnd` and the other `JPoints.cost…`: the defaults of the cost model.
* `JPoints.tubeEps`, `JPoints.tubeBig`, `JPoints.rowBeyond`: the doubles of the analysis of the
  tube and of the real region.

## Implementation notes

The build modeled is the default one: `DEBUG = 0`, which selects the larger of the two tables of
primes, the scalar walk `VW = 1`, and no file `tuning.mk`, so that the cost model has the defaults
of `j-points.c`. A constant whose value the constants check varies is a definition on one line,
`def name : T := v`, or, for the table `JPoints.primeTable`, an array literal on the lines after its
head. The defaults of the cost model are `Float`s, as the cost model runs in `Float`; the doubles
that decide what is searched are `JPoints.Double`s, given by their bits, which the examples check
against the values of the literals. The termination proofs of the model use of the values only that
`JPoints.tubeRows` is positive (`JPoints.tubeRows_pos`, checked by `decide`), for the end of the
recursion of `tube_cell`.
-/

@[expose] public section

namespace JPoints

/-! ### The primes and the tables -/

/-- `NUM_PRIMES`, the number of odd primes in the table `prime[]`.

C: `j-points.h:41` -/
def numPrimes : Nat := 53

/-- `MAX_PRIME`, the largest prime of the table.

C: `j-points.h:42` -/
def maxPrime : Nat := 251

/-- `MAX_PRIME_EVEN`, the least power of 2 above `JPoints.maxPrime`: the width of the tables of
residues modulo a prime of the table.

C: `j-points.h:43` -/
def maxPrimeEven : Nat := 256

/-- `MAX_TABLE_PRIME`, the largest prime that may get a sieve table of `p * p * (p + 1)` words for
the first two stages of the sieve; the larger primes of the table serve only the third stage, bit
by bit.

C: `j-points.h:44` -/
def maxTablePrime : Nat := 127

/-- The table `prime[]` of `j-points.c`: the odd primes up to `JPoints.maxPrime`, in increasing
order, `JPoints.numPrimes` of them. The C array has room for one entry more, `prime[NUM_PRIMES]`,
which is 0.

C: `j-points.c:58-61` -/
def primeTable : Array Nat :=
  #[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

/-! ### Words and heights -/

/-- `CEIL(a, b)` of `j-points.h`, `⌈a / b⌉` for `b > 0`, by the truncating division of C.

C: `j-points.h:48` -/
def ceilDiv (a b : Int) : Int := if a ≤ 0 then -((-a).tdiv b) else 1 + (a - 1).tdiv b

/-- `LONG_LENGTH`, the number of bits of an `unsigned long`, the word of the bit arrays: 64 on the
platforms of `j-points` (LP64).

C: `j-points.h:50` -/
def longLength : Nat := 64

/-- `LONG_SHIFT`, the binary logarithm of `JPoints.longLength`.

C: `j-points.h:52-54` -/
def longShift : Nat := 6

/-- `LONG_MASK`, `JPoints.longLength - 1`, the mask of the position of a bit in its word.

C: `j-points.h:55`

Deviation: the macro is `~(-1L << LONG_SHIFT)`, a left shift of a negative value, which ISO C
leaves undefined; gcc computes `63`, which is the value here. -/
def longMask : Nat := 63

/-- `MAX_HEIGHT`, the bound on the coordinates that the exact check takes in `long`s:
`⌊√(2 ^ 63 - 1)⌋`, so that the product of two coordinates of absolute value at most it fits a
`long`.

C: `j-points.h:56-58` -/
def maxHeight : Nat := 3037000499

/-- `MAX_SEARCH_HEIGHT`, the largest height bound that the program takes: the smaller of
`JPoints.maxHeight` and `2 ^ 26`, which is `2 ^ 26`. Up to it the products of `row_region` stay
below `2 ^ 53`, where the rounding of the ends of its excluded intervals stays within their margins.

C: `j-points.h:59` -/
def maxSearchHeight : Nat := 67108864

/-- `HALF_MASK`, the word whose odd bits are set.

C: `j-points.h:64` -/
def halfMask : UInt64 := 0xAAAAAAAAAAAAAAAA

/-! ### Options and messages -/

/-- `DEFAULT_SIZE`, the default of the option `-s`: the size of the bit array of the sieve, in
kilobytes.

C: `j-points.c:44` -/
def defaultSize : Nat := 10

/-- `J_POINTS_VERSION`, the banner that message 0 prints.

C: `j-points.c:46-48` -/
def version : String :=
  "This is j-points-3.0.1 by Michael Stoll (2026-10-30).\n\n" ++
    "Please acknowledge use of the program in published work.\n"

/-! ### The cost model

The defaults of the constants of the cost model, in cycles of one core: those of the scalar build,
which `-c NAME=value` replaces for one run. -/

/-- `COST_AND`, a word of one pass of the first stage, the default `COST_AND_VW` of the scalar
build.

C: `j-points.c:85-88`, `j-points.c:91-94` -/
def costAnd : Float := 0.63

/-- `COST_SIZE`, the size penalty of a pass, which costs `1 + p / COST_SIZE` times the pass of a
small prime: the tables of the larger primes spill out of the cache; the default `COST_SIZE_VW`
of the scalar build.

C: `j-points.c:89`, `j-points.c:95-99` -/
def costSize : Float := 756.0

/-- `COST_WORD`, a word that survives the first stage: found and handed to the second.

C: `j-points.c:100-103` -/
def costWord : Float := 56.0

/-- `COST_TEST2`, a test of a word in the second stage, the default `COST_TEST2_VW` of the scalar
build.

C: `j-points.c:90`, `j-points.c:104-106` -/
def costTest2 : Float := 5.6

/-- `COST_BIT`, a bit that survives the second stage: found, and tested for coprimality.

C: `j-points.c:107-110` -/
def costBit : Float := 30.0

/-- `COST_ROW3`, per prime of the third stage, the data of a row that has a bit to test there.

C: `j-points.c:111-114` -/
def costRow3 : Float := 40.0

/-- `COST_TEST3`, a test of a bit in the third stage.

C: `j-points.c:115-117` -/
def costTest3 : Float := 15.0

/-- `COST_EXACT`, the exact check of a triple.

C: `j-points.c:118-120` -/
def costExact : Float := 1300.0

/-- `COST_ROW`, a row of the box besides its passes: the fill, the scan, the set-up.

C: `j-points.c:121-124` -/
def costRow : Float := 300.0

/-- `COST_CELL`, a cell of the analysis of the tube.

C: `j-points.c:125-127` -/
def costCell : Float := 320.0

/-- `COST_TWORD`, a word that the tube leaves, besides its tests.

C: `j-points.c:128-130` -/
def costTword : Float := 12.0

/-- `COST_TTEST`, a test of such a word.

C: `j-points.c:131-133` -/
def costTtest : Float := 2.0

/-- `COST_TROW`, the set-up of a row with words in the tube.

C: `j-points.c:134-136` -/
def costTrow : Float := 45.0

/-- `COST_RROW`, the real region of a row.

C: `j-points.c:137-139` -/
def costRrow : Float := 40.0

/-- `COST_REXCL`, per interval of the third coordinate that the real region of a row excludes.

C: `j-points.c:140-143` -/
def costRexcl : Float := 15.0

/-- `COST_RCUT`, the cut of the words of a row in the tube to the real region.

C: `j-points.c:144-146` -/
def costRcut : Float := 30.0

/-- `COST_RANGE`, a range of words of the real region, besides its passes.

C: `j-points.c:147-149` -/
def costRange : Float := 20.0

/-- `COST_PASS`, a pass over such a range, besides its words.

C: `j-points.c:150-152` -/
def costPass : Float := 5.0

/-- `COST_TABLE`, a word of a sieve table at the set-up.

C: `j-points.c:153-155` -/
def costTable : Float := 13.0

/-- `COST_INIT`, a class `(1, b, c)` of the exact table of a prime whose rate was sampled, at the
set-up.

C: `j-points.c:156-159` -/
def costInit : Float := 110.0

/-- `SAMPLE_PAIRS`, the number of classes `(1, b, c)` sampled for the rate of a large prime.

C: `j-points.c:160-161` -/
def samplePairs : Nat := 4096

/-! ### The real roots, the tube and the region -/

/-- `ROOT_BITS`: the ends of the isolating intervals of the real roots are below
`2 ^ ROOT_BITS` in absolute value, so that the products of the analysis of the real region stay
far below the largest double.

C: `j-points.c:1500-1502` -/
def rootBits : Nat := 480

/-- `TUBE_BAND`, the number of rows that the tube analyzes and then sieves together.

C: `j-sift.c:119` -/
def tubeBand : Nat := 4096

/-- `TUBE_RANGES`, the number of ranges of words of the tube kept per row; more are merged.

C: `j-sift.c:120` -/
def tubeRanges : Nat := 12

/-- `TUBE_EPS`, the double nearest to `1.5e-5`: the relative margin of each coefficient of the
analysis of the tube.

C: `j-sift.c:422` -/
def tubeEps : Double := ⟨0x3eef75104d551d69⟩

/-- `TUBE_BIG`, the double nearest to `1e300`: the scale beyond which the analysis of the tube
decides nothing.

C: `j-sift.c:423` -/
def tubeBig : Double := ⟨0x7e37e43c8800759c⟩

/-- `TUBE_ROWS`, the number of rows of a leaf cell of the analysis of the tube.

C: `j-sift.c:424` -/
def tubeRows : Nat := 64

/-- The number of the rows of a leaf cell is positive, as the C code assumes: a cell of more rows
than that has at least two, so that each half of it that `tube_cell` analyzes (`JPoints.tubeCell`)
has fewer. -/
theorem tubeRows_pos : 0 < tubeRows := by decide

/-- `L`, the length of a row of an array of coefficients of a polynomial in two variables of
degree at most 4; the coefficient of `b ^ j c ^ k` is at `L j + k` (the macro `P(j, k)`,
`JPoints.coeffIndex`), and an array has `NC = L * L` entries (`JPoints.numCoeffs`).

C: `j-sift.c:425` -/
def coeffRow : Nat := 5

/-- `ROW_RANGES`, the room for the ranges of words of the real region of a row: the size of the
local arrays `reglo` and `reghi` of `tube_sample` and `sift_bands` (and, with `JPoints.tubeRanges`
more, of `rlo`, `rhi`, `clo` and `chi`), into which `row_region` writes at most `2 * 4 + 1 = 9`
ranges. The model returns the ranges as arrays of their number and reads the constant nowhere.

C: `j-sift.c:478` -/
def rowRanges : Nat := 12

/-- `ROW_BEYOND`, `4e9`, beyond every third coordinate of a row, since `MAX_HEIGHT + LONG_LENGTH`
is below it.

C: `j-sift.c:479-480` -/
def rowBeyond : Double := ⟨0x41edcd6500000000⟩

/-! ### Examples

The literals against the bits that gcc gives them, and the table against its macros. -/

#guard primeTable.size == numPrimes
#guard primeTable.back! == maxPrime
#guard maxPrime < maxPrimeEven && maxPrimeEven ≤ 2 * maxPrime
#guard primeTable.contains maxTablePrime
#guard 2 ^ longShift == longLength && longMask == longLength - 1
#guard maxHeight * maxHeight < 2 ^ 63 && 2 ^ 63 ≤ (maxHeight + 1) * (maxHeight + 1)
#guard maxSearchHeight == min maxHeight (2 ^ 26)
#guard costAnd.toBits == 0x3fe428f5c28f5c29 && costTest2.toBits == 0x4016666666666666
#guard tubeEps.bits == (Double.ofRatio false 15 1000000).bits
#guard tubeBig.bits == (Double.ofRatio false (10 ^ 300) 1).bits
#guard rowBeyond.bits == (Double.ofRatio false 4000000000 1).bits
#guard ceilDiv 3037000500 64 == 47453133 && ceilDiv (-63) 64 == 0 && ceilDiv 0 64 == 0

end JPoints

end
