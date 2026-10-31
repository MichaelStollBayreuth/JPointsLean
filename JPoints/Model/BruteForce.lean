/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The brute-force reference

`JPoints.bruteForce cs H all W` lists the points that `j-points` finds on the curve with the
coefficient list `cs` itself, for the height bound `H`, the option `-a` (`all`) and the bound `W` of
`-w`, by testing every candidate: over each coprime triple `(a, b, c)` of the box
`|a|, |b|, |c| ≤ H` with the first nonzero coordinate positive, the triples on the conic `b² = 4ac`
first and then the others, each in lexicographic order, the rational roots `d₁ / d₂` of the Kummer
equation in the order of the exact check of the program, each giving the candidate
`(m a, m b, m c, n)` with `n / m = d₁ / d₂` in lowest terms, `m > 0`, which is listed when it lies
within the bounds and passes the lifting test of the program. `JPoints.mem_bruteForce_iff`,
`JPoints.nodup_bruteForce` and `JPoints.bruteForce_eq_filter_flatMap_kummerPoints` prove that it
lists exactly the points of the specification, each once, in the order of the specification for a
curve that the program does not transform; comparator certifies these three
(`comparator/Challenge.lean`). It models no C code, but it computes as the exact check of the C code
does (`check_one_point`, `check_one_point_final`, `check_lifts`): the roots from the discriminant
`K₁² - 4 K₀ K₂`, the lifting test on `A₂` alone when it is not zero, and on `B₂` when it is.

## Main definitions

* `JPoints.bruteForce`: the points by brute force, in the order of
  `JPoints.BruteForce.orderedTriples` and of `JPoints.BruteForce.candidates`.

## Implementation notes

The reference is plain code on lists of triples and on integers, without the `Id` components, the
loops and the state of the model of the C code, as it models none: the box is a list, the triples on
the conic first (`JPoints.BruteForce.orderedTriples`), and each triple gives its candidates in the
order of the exact check (`JPoints.BruteForce.candidates`).
-/

@[expose] public section

namespace JPoints

namespace BruteForce

/-- The coefficient `cs.getD k 0` of `xᵏ`. -/
def coeff (cs : List Int) (k : Nat) : Int := cs.getD k 0

/-- The integers `-H, …, H`, in increasing order. -/
def intRange (H : Nat) : List Int := (List.range (2 * H + 1)).map fun (i : Nat) ↦ (i : Int) - H

/-- The coprime triples `(a, b, c)` with `0 ≤ a ≤ H`, `|b|, |c| ≤ H` and the first nonzero
coordinate positive, in lexicographic order. -/
def boxTriples (H : Nat) : List (Int × Int × Int) :=
  ((List.range (H + 1)).flatMap fun (a : Nat) ↦ (intRange H).flatMap fun b ↦
      (intRange H).map fun c ↦ ((a : Int), b, c)).filter
    fun (a, b, c) ↦ Int.gcd a (Int.gcd b c) == 1 && (0 < a || a == 0 && (0 < b || b == 0 && 0 < c))

/-- The triples of `JPoints.BruteForce.boxTriples` on the conic `b² = 4ac`, then the others. -/
def orderedTriples (H : Nat) : List (Int × Int × Int) :=
  (boxTriples H).filter (fun (a, b, c) ↦ b * b == 4 * a * c) ++
    (boxTriples H).filter (fun (a, b, c) ↦ b * b != 4 * a * c)

/-- The coefficients `(K₂, K₁, K₀)` of the Kummer equation `K₂ d² + K₁ d + K₀ = 0` over
`(a, b, c)`. -/
def kummerCoeffs (cs : List Int) (a b c : Int) : Int × Int × Int :=
  let f := coeff cs
  (b * b - 4 * a * c,
    -4 * f 0 * a ^ 3 - 2 * f 1 * a ^ 2 * b - 4 * f 2 * a ^ 2 * c - 2 * f 3 * a * b * c -
      4 * f 4 * a * c ^ 2 - 2 * f 5 * b * c ^ 2 - 4 * f 6 * c ^ 3,
    (f 1 ^ 2 - 4 * f 0 * f 2) * a ^ 4 - 4 * f 0 * f 3 * a ^ 3 * b - 2 * f 1 * f 3 * a ^ 3 * c -
      4 * f 0 * f 4 * a ^ 2 * b ^ 2 + 4 * (f 0 * f 5 - f 1 * f 4) * a ^ 2 * b * c +
      (f 3 ^ 2 - 4 * f 2 * f 4 + 2 * f 1 * f 5 - 4 * f 0 * f 6) * a ^ 2 * c ^ 2 -
      4 * f 0 * f 5 * a * b ^ 3 + (8 * f 0 * f 6 - 4 * f 1 * f 5) * a * b ^ 2 * c +
      4 * (f 1 * f 6 - f 2 * f 5) * a * b * c ^ 2 - 2 * f 3 * f 5 * a * c ^ 3 -
      4 * f 0 * f 6 * b ^ 4 - 4 * f 1 * f 6 * b ^ 3 * c - 4 * f 2 * f 6 * b ^ 2 * c ^ 2 -
      4 * f 3 * f 6 * b * c ^ 3 + (f 5 ^ 2 - 4 * f 4 * f 6) * c ^ 4)

/-- Whether `n` is the square of an integer: `⌊√n⌋² = n`, with `n ≥ 0`. -/
def isSquare (n : Int) : Bool := 0 ≤ n && n.toNat.sqrt * n.toNat.sqrt == n.toNat

/-- The lifting test of the program on `(a, b, c, d)`: for `a ≠ 0`, `A₂` is a square when it is
not `0`, and `B₂` is one when it is; for `a = 0 ≠ b`, `f₆` and `F(c, b) = ∑ fₖ cᵏ b⁶⁻ᵏ` are
squares; for `a = b = 0`, `f₆` is a square. -/
def lifts (cs : List Int) (a b c d : Int) : Bool :=
  let f := coeff cs
  if a == 0 then
    if b == 0 then isSquare (f 6)
    else
      isSquare (f 6) && isSquare ((List.range 7).foldr (fun k s ↦ f k * c ^ k * b ^ (6 - k) + s) 0)
  else
    let A2 := a ^ 3 * d + f 2 * a ^ 4 + f 3 * a ^ 3 * b + f 4 * a ^ 2 * b ^ 2 +
      f 5 * a * b * (b * b - a * c) + f 6 * (b * b - a * c) ^ 2
    let B2 := a ^ 2 * c * d + f 0 * a ^ 4 + f 4 * a ^ 2 * c ^ 2 + f 5 * a * b * c ^ 2 +
      f 6 * b ^ 2 * c ^ 2
    if A2 != 0 then isSquare A2 else isSquare B2

/-- The candidate over `(a, b, c)` of the root `d₁ / d₂` (`d₂ ≠ 0`): `(m a, m b, m c, n)` with
`n / m = d₁ / d₂` in lowest terms and `m > 0`. -/
def pointOf (a b c d₁ d₂ : Int) : Int × Int × Int × Int :=
  let g : Int := Int.gcd d₁ d₂
  let m := d₂ / g
  let n := d₁ / g
  if m < 0 then (-m * a, -m * b, -m * c, -n) else (m * a, m * b, m * c, n)

/-- The candidates over `(a, b, c)`, in the order of the exact check of the program: for the
discriminant `Δ = K₁² - 4 K₀ K₂` zero, the root `-K₁ / (2 K₂)` (none when `K₂ = K₁ = 0`); for `Δ` a
nonzero square, the root `-K₀ / K₁` when `K₂ = 0`, and otherwise `(√Δ - K₁) / (2 K₂)` and then
`-(√Δ + K₁) / (2 K₂)`; none when `Δ` is not a square. -/
def candidates (cs : List Int) (a b c : Int) : List (Int × Int × Int × Int) :=
  let (k2, k1, k0) := kummerCoeffs cs a b c
  let disc := k1 * k1 - 4 * k0 * k2
  if disc == 0 then (if k2 == 0 && k1 == 0 then [] else [pointOf a b c (-k1) (2 * k2)])
  else if isSquare disc then
    if k2 == 0 then [pointOf a b c (-k0) k1]
    else
      let s : Int := disc.toNat.sqrt
      [pointOf a b c (s - k1) (2 * k2), pointOf a b c (-(s + k1)) (2 * k2)]
  else []

/-- Whether `(a, b, c, d)` lies within the bounds of the search: without `-a`, `|a|, |b|, |c| ≤ H`
and `|d| ≤ W` (`H` when `-w` is not given); with `-a`, `|a|, |b|, |c| ≤ H gcd(a, b, c)` and
`|d| ≤ W` when `-w` is given. -/
def inBounds (H : Nat) (all : Bool) (W : Option Nat) (a b c d : Int) : Bool :=
  if all then
    a.natAbs ≤ H * Int.gcd a (Int.gcd b c) && b.natAbs ≤ H * Int.gcd a (Int.gcd b c) &&
      c.natAbs ≤ H * Int.gcd a (Int.gcd b c) && W.all (d.natAbs ≤ ·)
  else a.natAbs ≤ H && b.natAbs ≤ H && c.natAbs ≤ H && d.natAbs ≤ W.getD H

end BruteForce

open BruteForce in
/-- The points that `j-points` finds on the curve with the coefficient list `cs` itself, for the
height bound `H`, the option `-a` (`all`) and the bound `W` of `-w`, by brute force: over the
triples of `JPoints.BruteForce.orderedTriples H` in turn, the candidates of
`JPoints.BruteForce.candidates` within the bounds (`JPoints.BruteForce.inBounds`) that pass the
lifting test (`JPoints.BruteForce.lifts`). -/
def bruteForce (cs : List Int) (H : Nat) (all : Bool) (W : Option Nat) :
    List (Int × Int × Int × Int) :=
  (orderedTriples H).flatMap fun (a, b, c) ↦ (candidates cs a b c).filter
    fun (a, b, c, d) ↦ inBounds H all W a b c d && lifts cs a b c d

/-! ### Examples

The points that `j-points` at the pin prints, `j-points cs H -q` with the options given. -/

#guard bruteForce [1, 4, 3, -8, 2, 8, 7] 8 false none ==
  [(1, -2, 1, -6), (1, 0, 0, 1), (1, -1, 0, 4), (1, -1, 0, -8), (7, 6, 3, -2)]

#guard bruteForce [9, 4, 6, 5, 1, -4, -2] 6 true none ==
  [(1, -4, 4, 1390), (36, -72, 36, -191), (9, 0, 0, -50), (1, -3, 2, 30), (1, -3, 2, 18),
    (1, -2, 0, 4), (1, -2, 0, 1), (1, -1, 0, 32), (1, -1, 0, -4)]

#guard bruteForce [4, -6, 10, 8, -1, -10, 1] 6 true none ==
  [(0, 0, 1, 26), (4, 0, 0, -31), (0, 1, 0, 4), (0, 1, 0, -4)]

-- `-a -w 30` leaves out `(4, 0, 0, -31)`.
#guard bruteForce [4, -6, 10, 8, -1, -10, 1] 6 true (some 30) ==
  [(0, 0, 1, 26), (0, 1, 0, 4), (0, 1, 0, -4)]

end JPoints

end
