/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Squarefree.Basic
public import JPoints.Model

/-!
# Comparator challenge statements

The main theorems of the project, stated with `sorry` for
[leanprover/comparator](https://github.com/leanprover/comparator), over a verbatim restatement of
the specification. The file may import only Mathlib and the model (`scripts/check_layout.py` checks
this): the statements speak about the model's brute-force reference `JPoints.bruteForce`, which is
trusted in the sense that it is the code the executable `j-points-brute` runs, while the
specification is reproduced here, so that a solution that changed it would be rejected.

The file restates all of `JPoints/Spec/Basic.lean`, in its order and without its examples: the
points (`JPoints.degree`, `JPoints.poly`, the Kummer equation `JPoints.kummerK2`,
`JPoints.kummerK1`, `JPoints.kummerK0`, `JPoints.kummer`, the polynomials of the lifting test
`JPoints.auxA2`, `JPoints.auxB2`, `JPoints.sexticForm`, and `JPoints.Lifts`,
`JPoints.IsNormalized`, `JPoints.InBounds`, `JPoints.IsPoint` with their decidability) and their
order (`JPoints.intRange`, `JPoints.boxTriples`, `JPoints.orderedTriples`, `JPoints.kummerRoots`,
`JPoints.kummerPoints`, `JPoints.searchedCoeffs`, `JPoints.backPoint`, `JPoints.orderedPoints`).
It has four statements, which `comparator/challenges.json` lists; `comparator/README.md` describes
them and gives the date on which Comparator last accepted them. They hold for every coefficient list
`cs`, height bound `H`, option `-a` (`all`) and bound `W` of `-w`:

* membership: for every curve that the program does not refuse (at most seven coefficients, degree
  at least 5, `JPoints.poly cs` squarefree), `JPoints.bruteForce cs H all W` holds exactly the
  points (`JPoints.IsPoint`);
* no duplicates, for every curve;
* the order of the search: for every curve, the brute-force reference is the list of the candidates
  of `JPoints.kummerPoints` over the triples of `JPoints.orderedTriples H` in turn that are points;
* the order of the program: `JPoints.orderedPoints` is the brute-force reference of the curve
  searched (`JPoints.searchedCoeffs`), its points taken back to the curve given
  (`JPoints.backPoint`).

`JPoints.bruteForce` comes from the model and is never restated, since a definition of the model
elaborates without Mathlib to other instance terms. Of Mathlib, the file imports exactly the public
imports of the file of the specification that it restates (`JPoints/Spec/Basic.lean`), so that the
restated definitions elaborate to the same terms as there; the specification is one file, restated
here in its order, since Lean shares the auxiliary definitions of pattern matches of equal shape
within a module.
-/

@[expose] public section

namespace JPoints

/-- The degree of the polynomial `∑ cᵢ Xⁱ` with the coefficient list `cs`: the largest index of a
nonzero entry of `cs`, or `0` if there is none. -/
def degree (cs : List ℤ) : ℕ := (cs.reverse.dropWhile (· == 0)).length - 1

open Polynomial in
/-- The polynomial `f = ∑ cᵢ Xⁱ` over `ℚ` with the coefficient list `cs`; the program refuses the
curves for which it is not squarefree. -/
noncomputable def poly (cs : List ℤ) : ℚ[X] :=
  ∑ i ∈ Finset.range cs.length, C (cs.getD i 0 : ℚ) * X ^ i

/-- The coefficient `K₂ = b² - 4ac` of `d²` in the Kummer equation over `(a, b, c)`; on the image
`(1 : x₁ + x₂ : x₁ x₂ : d)` of a point of the Jacobian it is `(x₁ - x₂)²`. -/
def kummerK2 (a b c : ℤ) : ℤ := b ^ 2 - 4 * a * c

/-- The coefficient `K₁` of `d` in the Kummer equation over `(a, b, c)`, for the coefficients
`f 0, …, f 6` of the sextic. -/
def kummerK1 (f : ℕ → ℤ) (a b c : ℤ) : ℤ :=
  -4 * f 0 * a ^ 3 - 2 * f 1 * a ^ 2 * b - 4 * f 2 * a ^ 2 * c - 2 * f 3 * a * b * c -
    4 * f 4 * a * c ^ 2 - 2 * f 5 * b * c ^ 2 - 4 * f 6 * c ^ 3

/-- The constant term `K₀` of the Kummer equation over `(a, b, c)`, for the coefficients
`f 0, …, f 6` of the sextic: a quartic form in `a, b, c` whose fifteen coefficients are quadratic
in those of the sextic. -/
def kummerK0 (f : ℕ → ℤ) (a b c : ℤ) : ℤ :=
  (f 1 ^ 2 - 4 * f 0 * f 2) * a ^ 4 - 4 * f 0 * f 3 * a ^ 3 * b - 2 * f 1 * f 3 * a ^ 3 * c -
    4 * f 0 * f 4 * a ^ 2 * b ^ 2 + 4 * (f 0 * f 5 - f 1 * f 4) * a ^ 2 * b * c +
    (f 3 ^ 2 - 4 * f 2 * f 4 + 2 * f 1 * f 5 - 4 * f 0 * f 6) * a ^ 2 * c ^ 2 -
    4 * f 0 * f 5 * a * b ^ 3 + (8 * f 0 * f 6 - 4 * f 1 * f 5) * a * b ^ 2 * c +
    4 * (f 1 * f 6 - f 2 * f 5) * a * b * c ^ 2 - 2 * f 3 * f 5 * a * c ^ 3 -
    4 * f 0 * f 6 * b ^ 4 - 4 * f 1 * f 6 * b ^ 3 * c - 4 * f 2 * f 6 * b ^ 2 * c ^ 2 -
    4 * f 3 * f 6 * b * c ^ 3 + (f 5 ^ 2 - 4 * f 4 * f 6) * c ^ 4

/-- The equation `K(a, b, c, d) = K₂ d² + K₁ d + K₀` of the Kummer surface of the Jacobian of
`y² = f(x)`, for the coefficients `f 0, …, f 6`, in the coordinates of Cassels and Flynn; it is the
equation of Magma's `KummerSurface`. -/
def kummer (f : ℕ → ℤ) (a b c d : ℤ) : ℤ :=
  kummerK2 a b c * d ^ 2 + kummerK1 f a b c * d + kummerK0 f a b c

/-- The first polynomial of the lifting test,
`A₂ = a³ d + f₂ a⁴ + f₃ a³ b + f₄ a² b² + f₅ a b (b² - a c) + f₆ (b² - a c)²`: on the image of a
point of the Jacobian with Mumford representation `(x² - (b / a) x + c / a, v₁ x + v₀)` it is
`a⁴ v₁²`. -/
def auxA2 (f : ℕ → ℤ) (a b c d : ℤ) : ℤ :=
  a ^ 3 * d + f 2 * a ^ 4 + f 3 * a ^ 3 * b + f 4 * a ^ 2 * b ^ 2 + f 5 * a * b * (b ^ 2 - a * c) +
    f 6 * (b ^ 2 - a * c) ^ 2

/-- The second polynomial of the lifting test,
`B₂ = a² c d + f₀ a⁴ + f₄ a² c² + f₅ a b c² + f₆ b² c²`: on the image of a point of the Jacobian
with Mumford representation `(x² - (b / a) x + c / a, v₁ x + v₀)` it is `a⁴ v₀²`. -/
def auxB2 (f : ℕ → ℤ) (a b c d : ℤ) : ℤ :=
  a ^ 2 * c * d + f 0 * a ^ 4 + f 4 * a ^ 2 * c ^ 2 + f 5 * a * b * c ^ 2 + f 6 * b ^ 2 * c ^ 2

/-- The binary sextic form `F(x, z) = ∑ f k xᵏ z⁶⁻ᵏ` of the coefficients `f 0, …, f 6`, so that
`F(x, z) = z⁶ f(x / z)`. -/
def sexticForm (f : ℕ → ℤ) (x z : ℤ) : ℤ := ∑ k ∈ Finset.range 7, f k * x ^ k * z ^ (6 - k)

/-- The point `(a : b : c : d)` of the Kummer surface comes from a rational point of the Jacobian:
for `a ≠ 0`, `JPoints.auxA2` and `JPoints.auxB2` are squares in `ℤ` (`0` included), so that the
polynomial `v` of the Mumford representation is rational; for `a = 0 ≠ b`, where the divisor is
a point at infinity plus the point with `x = c / b`, both points are rational: `f₆` and
`F(c, b) = b⁶ f(c / b)` (`JPoints.sexticForm`) are squares; for `a = b = 0`, a point at
infinity counted twice, `f₆` is a square. -/
def Lifts (f : ℕ → ℤ) (a b c d : ℤ) : Prop :=
  if a = 0 then (if b = 0 then IsSquare (f 6) else IsSquare (f 6) ∧ IsSquare (sexticForm f c b))
  else IsSquare (auxA2 f a b c d) ∧ IsSquare (auxB2 f a b c d)

instance instDecidableLifts (f : ℕ → ℤ) (a b c d : ℤ) : Decidable (Lifts f a b c d) :=
  inferInstanceAs (Decidable (if a = 0 then _ else _))

/-- The point `(a, b, c, d)` is normalized as the program prints its points: the four coordinates
are coprime and the first nonzero of `a, b, c` is positive, so that `(a, b, c) ≠ 0`, which leaves
out the origin `(0, 0, 0, 1)` of the Jacobian. -/
def IsNormalized (a b c d : ℤ) : Prop :=
  gcd a (gcd b (gcd c d)) = 1 ∧ (0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c))

instance instDecidableIsNormalized (a b c d : ℤ) : Decidable (IsNormalized a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The bounds of the search on `(a, b, c, d)`, for the height bound `H`, the option `-a` (`all`)
and the bound `W` of the option `-w`, if given: without `-a`, `|a|, |b|, |c| ≤ H` and `|d| ≤ W`,
with `W = H` when `-w` is not given; with `-a`, the image `(a : b : c)` in the projective plane has
naive height at most `H`, that is `|a|, |b|, |c| ≤ H gcd(a, b, c)`, and `|d| ≤ W` only when `-w`
is given. -/
def InBounds (H : ℕ) (all : Bool) (W : Option ℕ) (a b c d : ℤ) : Prop :=
  if all then max |a| (max |b| |c|) ≤ H * gcd a (gcd b c) ∧ ∀ w ∈ W, |d| ≤ w
  else max |a| (max |b| |c|) ≤ H ∧ |d| ≤ W.getD H

instance instDecidableInBounds (H : ℕ) (all : Bool) (W : Option ℕ) (a b c d : ℤ) :
    Decidable (InBounds H all W a b c d) :=
  inferInstanceAs (Decidable (if all then _ else _))

/-- `(a, b, c, d)` is a point that `j-points` finds for the coefficient list `cs`, the height
bound `H`, the option `-a` (`all`) and the bound `W` of the option `-w`, if given: a point of the
Kummer surface of `y² = f(x)` (`JPoints.kummer`) that comes from a rational point of the Jacobian
(`JPoints.Lifts`), normalized (`JPoints.IsNormalized`) and within the bounds of the search
(`JPoints.InBounds`). -/
def IsPoint (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) : ℤ × ℤ × ℤ × ℤ → Prop
  | (a, b, c, d) => kummer (cs.getD · 0) a b c d = 0 ∧ Lifts (cs.getD · 0) a b c d ∧
      IsNormalized a b c d ∧ InBounds H all W a b c d

instance instDecidablePredIsPoint (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    DecidablePred (IsPoint cs H all W) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ### The order of the points -/

/-- The integers `-H, …, H`, in increasing order. -/
def intRange (H : ℕ) : List ℤ := (List.range (2 * H + 1)).map fun i : ℕ ↦ (i : ℤ) - H

/-- The triples `(a, b, c)` with `0 ≤ a ≤ H`, `|b|, |c| ≤ H`, `gcd(a, b, c) = 1` and the first
nonzero coordinate positive, in lexicographic order: the first three coordinates of the normalized
points of the Kummer surface with `|a|, |b|, |c| ≤ H`, divided by their gcd. -/
def boxTriples (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  ((List.range (H + 1)).flatMap fun a : ℕ ↦ (intRange H).flatMap fun b ↦
      (intRange H).map fun c ↦ ((a : ℤ), b, c)).filter
    fun (a, b, c) ↦ gcd a (gcd b c) = 1 ∧ (0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c))

/-- The triples of `JPoints.boxTriples` in the order of the search: those on the conic
`b² = 4ac` first, that is `(0, 0, 1)` and the triples `(s², 2st, t²)` of the double points (the
images of the classes `2 (x, y) - D∞` with `x = t / s`), then the others, each in lexicographic
order. -/
def orderedTriples (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  (boxTriples H).filter (fun (a, b, c) ↦ b ^ 2 = 4 * a * c) ++
    (boxTriples H).filter (fun (a, b, c) ↦ b ^ 2 ≠ 4 * a * c)

/-- The rational roots `d` of the Kummer equation `K₂ d² + K₁ d + K₀ = 0` over `(a, b, c)`, for
the coefficients `f 0, …, f 6`, in the order in which the program takes them: for `K₂ ≠ 0` and
the discriminant `Δ = K₁² - 4 K₀ K₂` a square, `(√Δ - K₁) / (2 K₂)` and then
`(-√Δ - K₁) / (2 K₂)`, the one root `-K₁ / (2 K₂)` when `Δ = 0`; for `K₂ = 0 ≠ K₁`, `-K₀ / K₁`;
none otherwise. -/
def kummerRoots (f : ℕ → ℤ) (a b c : ℤ) : List ℚ :=
  let k2 := kummerK2 a b c
  let k1 := kummerK1 f a b c
  let k0 := kummerK0 f a b c
  let s := Int.sqrt (k1 ^ 2 - 4 * k0 * k2)
  if k2 = 0 then (if k1 = 0 then [] else [(-k0 : ℚ) / k1])
  else if s ^ 2 ≠ k1 ^ 2 - 4 * k0 * k2 then []
  else if s = 0 then [(-k1 : ℚ) / (2 * k2)]
  else [((s - k1 : ℤ) : ℚ) / (2 * k2), ((-s - k1 : ℤ) : ℚ) / (2 * k2)]

/-- The candidates of the points over the triple `(a, b, c)`, for the coefficients
`f 0, …, f 6`: for each root `d = n / m` of `JPoints.kummerRoots` in lowest terms, with `m > 0`,
in their order, the point `(m a, m b, m c, n)` of the Kummer surface. -/
def kummerPoints (f : ℕ → ℤ) : ℤ × ℤ × ℤ → List (ℤ × ℤ × ℤ × ℤ)
  | (a, b, c) => (kummerRoots f a b c).map fun x ↦ (x.den * a, x.den * b, x.den * c, x.num)

/-- The coefficients `f₀, …, f₆` of the curve that `j-points` searches for the coefficient list
`cs`, and whether it reversed and whether it negated them: a sextic with `f₀ = 0` and `f₁ = ±1`
becomes the quintic `y² = x⁶ f(1 / x)`, its coefficients reversed, and a quintic, given or so
obtained, with leading coefficient `-1` becomes the monic quintic `y² = f(-x)`, its odd
coefficients negated; otherwise the curve is the one given. -/
def searchedCoeffs (cs : List ℤ) : List ℤ × Bool × Bool :=
  let rev : Bool := degree cs = 6 ∧ cs.getD 0 0 = 0 ∧ |cs.getD 1 0| = 1
  let cs₁ := if rev then (List.range 7).reverse.map (cs.getD · 0) else cs
  let neg : Bool := degree cs₁ = 5 ∧ cs₁.getD 5 0 = -1
  (if neg then (List.range 7).map (fun i ↦ (-1) ^ i * cs₁.getD i 0) else cs₁, rev, neg)

/-- A point `(a, b, c, d)` of the curve searched, taken back to the curve given, as the program
prints it: after a reversal `(c, b, a, d)`, after a negation the second coordinate negated, and
then the four coordinates negated if the first nonzero of the first three is negative. -/
def backPoint (rev neg : Bool) : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ
  | (a, b, c, d) =>
    let (a, c) := if rev then (c, a) else (a, c)
    let b := if neg then -b else b
    if a < 0 ∨ a = 0 ∧ (b < 0 ∨ b = 0 ∧ c < 0) then (-a, -b, -c, -d) else (a, b, c, d)

/-- The points of `y² = f(x)` that `j-points` finds for the coefficient list `cs`, the height bound
`H`, the option `-a` (`all`) and the bound `W` of `-w`, in the order in which it finds them: for
the curve searched (`JPoints.searchedCoeffs`), over the triples of `JPoints.orderedTriples` in
turn, the candidates of `JPoints.kummerPoints` that are points of the curve searched
(`JPoints.IsPoint`), each taken back to the curve given (`JPoints.backPoint`). -/
def orderedPoints (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) : List (ℤ × ℤ × ℤ × ℤ) :=
  let (cs', rev, neg) := searchedCoeffs cs
  (((orderedTriples H).flatMap (kummerPoints (cs'.getD · 0))).filter
    (IsPoint cs' H all W)).map (backPoint rev neg)

end JPoints

theorem challenge_mem_bruteForce_iff (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ)
    (p : ℤ × ℤ × ℤ × ℤ) (h7 : cs.length ≤ 7) (h5 : 5 ≤ JPoints.degree cs)
    (hsq : Squarefree (JPoints.poly cs)) :
    p ∈ JPoints.bruteForce cs H all W ↔ JPoints.IsPoint cs H all W p :=
  sorry

theorem challenge_nodup_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    (JPoints.bruteForce cs H all W).Nodup :=
  sorry

theorem challenge_bruteForce_eq_filter_flatMap_kummerPoints (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    JPoints.bruteForce cs H all W =
      ((JPoints.orderedTriples H).flatMap (JPoints.kummerPoints (cs.getD · 0))).filter
        (JPoints.IsPoint cs H all W) :=
  sorry

theorem challenge_orderedPoints_eq_map_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    JPoints.orderedPoints cs H all W =
      (JPoints.bruteForce (JPoints.searchedCoeffs cs).1 H all W).map
        (JPoints.backPoint (JPoints.searchedCoeffs cs).2.1 (JPoints.searchedCoeffs cs).2.2) :=
  sorry

end
