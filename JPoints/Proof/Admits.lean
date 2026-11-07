/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Rows
public import JPoints.Spec.Basic

import JPoints.Proof.Constants
import JPoints.Proof.Containers

/-!
# The classes that the tables of a prime admit

The tables of `j-points` modulo an odd prime `p`, as the C code computes them, in exact arithmetic:
the inverse modulo `p` that `invert` computes (`JPoints.refInverse`), the square roots that
`init_squares` records (`JPoints.refSquareRoot`, `JPoints.refIsSquare`), whether the curve has
points at infinity modulo `p` and which values of `f` are squares (`JPoints.refHasInfinity`,
`JPoints.refIsFSquare`), and the exact table of the third stage (`JPoints.refIsPointOnJ`, by the
test of `point_on_j`, `JPoints.refPointOnJ`, on the remainder of `f` modulo a quadratic,
`JPoints.refRemainder`). From these, the classes `(a, b, c)` modulo `p` that the sieve admits: in
the first two stages (`JPoints.refAdmits12`), as the rows of `init_sieve` hold them, and in the
third (`JPoints.refAdmits3`), as `row3_setup` and `check_bit` read the tables, which admits the
classes that the first two admit (`JPoints.refAdmits3_of_refAdmits12`).

The tables of the program are these references: those of `init_main` (`JPoints.Tables.WF`), those
of the curve (`JPoints.CurveTables.WF`), and the sieve tables of the first two stages
(`JPoints.SieveTables.WF`), whose bits are the class test of the tables of the curve
(`JPoints.CurveTables.admits12`), which is that of the references
(`JPoints.CurveTables.WF.admits12_eq`).

## Main definitions

* `JPoints.refInverse`, `JPoints.refSquareRoot`, `JPoints.refIsSquare`: the inverses and the
  square roots modulo `p`.
* `JPoints.refHasInfinity`, `JPoints.refIsFSquare`: the points at infinity and the values of `f`
  that are squares modulo `p`.
* `JPoints.refRemainder`, `JPoints.refPointOnJ`, `JPoints.refIsPointOnJ`: the exact table of the
  third stage.
* `JPoints.refAdmits12`, `JPoints.refAdmits3`: the classes that the sieve admits.
* `JPoints.sievingPrime`: a sieving prime of the plan.
* `JPoints.Tables.WF`, `JPoints.CurveTables.WF`, `JPoints.SieveTables.WF`: the tables of the
  program are the references.
* `JPoints.CurveTables.admits12`, `JPoints.CurveTables.admits3`: the class tests read from the
  tables of the curve.

## Main statements

* `JPoints.refSquareRoot_le`: the square root recorded is at most `p`.
* `JPoints.refAdmits3_of_refAdmits12`: the third stage admits the classes that the first two
  admit.
* `JPoints.CurveTables.admits12_congr`, `JPoints.CurveTables.admits12_natCast_mod`: the class test
  of the tables depends on the classes modulo the prime only.
* `JPoints.CurveTables.WF.admits12_eq`, `JPoints.CurveTables.WF.admits3_eq`: the class tests of the
  tables are those of the references.

## Implementation notes

The references compute what the C code computes, with the reductions by reciprocals (`MODP`,
`MOD3`) replaced by remainders, the tables replaced by the functions that fill them, and the index
arithmetic of the tables left out: the contracts of the builders of the tables say that the
tables are the references, and the number theory says what the references mean. The residues are
natural numbers, as the indices of the tables are; the coefficients and the values of `f` are
integers, reduced by `%`, the remainder in `[0, p)`.
-/

@[expose] public section

namespace JPoints

/-! ### Inverses and square roots modulo a prime -/

/-- The inverse of `a` modulo `p` as `invert` computes it, `a ^ (p - 2)` reduced modulo `p`: for a
prime `p ∤ a`, the inverse of `a` modulo `p`, by Fermat's little theorem. -/
def refInverse (p a : ℕ) : ℕ := a ^ (p - 2) % p

theorem refInverse_lt {p : ℕ} (a : ℕ) (hp : 0 < p) : refInverse p a < p := Nat.mod_lt _ hp

/-- The square root of `x` modulo `p` that `init_squares` records, or `p` when there is none: the
last even `y < p` with `y² ≡ x (mod p)`. For an odd prime `p` the even root of a square is unique
(`0` that of `0`). -/
def refSquareRoot (p x : ℕ) : ℕ :=
  ((List.range p).filter fun y ↦ y % 2 == 0 && y * y % p == x).getLastD p

theorem refSquareRoot_le (p x : ℕ) : refSquareRoot p x ≤ p := by
  rw [refSquareRoot, List.getLastD_eq_getLast?]
  cases h : ((List.range p).filter fun y ↦ y % 2 == 0 && y * y % p == x).getLast? with
  | none => exact le_rfl
  | some y => exact (List.mem_range.1 (List.mem_of_mem_filter (List.mem_of_getLast? h))).le

/-- Whether `x` is a square modulo `p`, `0` included, as the program reads it from the table of
the square roots: the root of its residue (`JPoints.refSquareRoot`) is not `p`. -/
def refIsSquare (p : ℕ) (x : ℤ) : Bool := refSquareRoot p (x % p).toNat != p

/-! ### The tables of the curve -/

/-- Whether the curve with the coefficients `cs` has points at infinity modulo `p`, as
`init_fmodpsquare` records it (`has_infinity`): whether `f₆` is a square modulo `p`, `0` included,
so that a quintic has them. -/
def refHasInfinity (cs : List ℤ) (p : ℕ) : Bool := refIsSquare p (cs.getD 6 0)

/-- Whether `f(x)` is a square modulo `p`, `0` included, for the polynomial `f` with the
coefficients `cs`, as `init_fmodpsquare` records it (`is_f_square`). -/
def refIsFSquare (cs : List ℤ) (p x : ℕ) : Bool := refIsSquare p (sexticForm (cs.getD · 0) x 1)

/-- The remainder `s₁ X + s₂` of `f` modulo `X² - b X + c` and `p`, for the polynomial `f` with the
coefficients `cs` of degree `deg`, by Horner's rule as `point_on_j` computes it: from
`(s₁, s₂) = (f_deg, f_(deg - 1))`, for `n = deg - 2, …, 0` the pair `(s₁ b + s₂, fₙ + (p - c) s₁)`,
each entry reduced modulo `p`. -/
def refRemainder (cs : List ℤ) (deg p : ℕ) (b c : ℤ) : ℤ × ℤ :=
  (List.range (deg - 1)).foldl (fun s i ↦
      ((s.1 * b + s.2) % p, (cs.getD (deg - 2 - i) 0 % p + (p - c) * s.1) % p))
    (cs.getD deg 0 % p, cs.getD (deg - 1) 0 % p)

/-- Whether `point_on_j` admits the class `(1, b, c)` modulo `p`, for the curve with the
coefficients `cs` of degree `deg`: for the remainder `s₁ X + s₂` of `f` modulo `X² - b X + c`
(`JPoints.refRemainder`), the value `f(x₁) f(x₂) = s₂² + b s₁ s₂ + c s₁²` at the roots of the
quadratic is a square `t²` modulo `p` (`t` its root of `JPoints.refSquareRoot`), and one of
`2 s₂ + b s₁ ± 2 t` is a square modulo `p`, each value reduced modulo `p` as the C code reduces
it. -/
def refPointOnJ (cs : List ℤ) (deg p b c : ℕ) : Bool :=
  let s := refRemainder cs deg p b c
  let t := refSquareRoot p ((s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1) % p).toNat
  t != p && (refIsSquare p (2 * s.2 + b * s.1 + 2 * t) ||
    refIsSquare p ((2 * s.2 + b * s.1 + 2 * t) % p + 4 * (p - t)))

/-- Whether the exact table of the third stage admits the class `(1, b, c)` modulo the prime `p`,
as `init_table` fills it (`is_point_on_j`), for the curve with the coefficients `cs` of degree
`deg`: on the diagonal `c ≡ b² / 4`, with `1 / 4` computed as `(1 + p (3 - (p & 2))) / 4`, always,
and off it when `point_on_j` admits it (`JPoints.refPointOnJ`). -/
def refIsPointOnJ (cs : List ℤ) (deg p b c : ℕ) : Bool :=
  c == (1 + p * (3 - (p &&& 2))) / 4 * b * b % p || refPointOnJ cs deg p b c

/-! ### The classes that the sieve admits -/

/-- Whether the sieve tables of the first two stages admit the class of `(a, b, c)` modulo `p`, for
the curve with the coefficients `cs` of degree `deg`, as `init_sieve` builds their rows from the
tables of the curve: for the residues of `a`, `b` and `c`, every class with `p ∣ a` and `p ∣ b`;
for `p ∣ a` and `p ∤ b`, those with points at infinity modulo `p` (`JPoints.refHasInfinity`) and
`f(c / b)` a square (`JPoints.refIsFSquare`); for `p ∤ a`, those whose `(1, b / a, c / a)` the exact
table of the third stage admits (`JPoints.refIsPointOnJ`), the quotients by the inverses modulo
`p` (`JPoints.refInverse`). -/
def refAdmits12 (cs : List ℤ) (deg p : ℕ) (a b c : ℤ) : Bool :=
  let a := (a % p).toNat
  let b := (b % p).toNat
  let c := (c % p).toNat
  if a = 0 then b == 0 || refHasInfinity cs p && refIsFSquare cs p (c * refInverse p b % p)
  else refIsPointOnJ cs deg p (b * refInverse p a % p) (c * refInverse p a % p)

/-- Whether the third stage of the sieve admits the class of `(a, b, c)` modulo `p`, for the curve
with the coefficients `cs` of degree `deg`, as `row3_setup` and `check_bit` read the tables of the
curve: the test of the first two stages (`JPoints.refAdmits12`) without the points at infinity,
whose table the third stage does not read. -/
def refAdmits3 (cs : List ℤ) (deg p : ℕ) (a b c : ℤ) : Bool :=
  let a := (a % p).toNat
  let b := (b % p).toNat
  let c := (c % p).toNat
  if a = 0 then b == 0 || refIsFSquare cs p (c * refInverse p b % p)
  else refIsPointOnJ cs deg p (b * refInverse p a % p) (c * refInverse p a % p)

theorem refAdmits3_of_refAdmits12 {cs : List ℤ} {deg p : ℕ} {a b c : ℤ}
    (h : refAdmits12 cs deg p a b c = true) : refAdmits3 cs deg p a b c = true := by
  simp only [refAdmits12, refAdmits3] at h ⊢
  split_ifs at h ⊢
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.imp_right And.right
  · exact h

/-! ### The tables of the program -/

/-- The `n`-th sieving prime `prime[pnn[n]]` of the plan whose indices in the table of the primes
are `pnn`. -/
abbrev sievingPrime (pnn : Array ℕ) (n : ℕ) : ℕ := primeTable[pnn[n]!]!

/-- The tables `t` as `init_main` builds them: `bits[n] = 2 ^ n`, and for every prime `p` of the
table and `0 < a < p` the inverse of `a` modulo `p` that `invert` computes
(`JPoints.refInverse`), for `x < p` the square root of `x` modulo `p` that `init_squares` records
(`JPoints.refSquareRoot`). -/
structure Tables.WF (t : Tables) : Prop where
  /-- The words with one bit set. -/
  bits {n : ℕ} (hn : n < longLength) : t.bits[n]! = 1 <<< n.toUInt64
  /-- The inverses modulo the primes of the table. -/
  inverses {pn : ℕ} (hpn : pn < numPrimes) {a : ℕ} (ha : 0 < a) (hap : a < primeTable[pn]!) :
    t.inverses[pn * maxPrimeEven + a]! = refInverse primeTable[pn]! a
  /-- The square roots modulo the primes of the table. -/
  squares {pn : ℕ} (hpn : pn < numPrimes) {x : ℕ} (hx : x < primeTable[pn]!) :
    t.squares[pn * maxPrime + x]! = refSquareRoot primeTable[pn]! x

/-- The tables of the curve `ct` as `init_fmodpsquare` fills them for the curve searched with the
coefficients `cs` of degree `deg`: for each of the first `nPrimes` primes `p` of the table (the
primes considered), the coefficients modulo `p`, whether the curve has points at infinity modulo
`p` (`JPoints.refHasInfinity`) and which values of `f` are squares (`JPoints.refIsFSquare`); and
for the sieving primes of the plan, the `prime[pnn[k]]` with `k < sp3`, the exact table of the
third stage (`JPoints.refIsPointOnJ`). -/
structure CurveTables.WF (ct : CurveTables) (cs : List ℤ) (deg nPrimes : ℕ) (pnn : Array ℕ)
    (sp3 : ℕ) : Prop where
  /-- The coefficients modulo the primes considered. -/
  coeffsModP {pn : ℕ} (hpn : pn < nPrimes) {n : ℕ} (hn : n ≤ 6) :
    ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!
  /-- The points at infinity modulo the primes considered. -/
  hasInfinity {pn : ℕ} (hpn : pn < nPrimes) :
    ct.hasInfinity[pn]! = refHasInfinity cs primeTable[pn]!
  /-- The values of `f` that are squares modulo the primes considered. -/
  isFSquare {pn : ℕ} (hpn : pn < nPrimes) {x : ℕ} (hx : x < primeTable[pn]!) :
    ct.isFSquare[pn * maxPrimeEven + x]! = refIsFSquare cs primeTable[pn]! x
  /-- The exact table of the third stage of the sieving primes. -/
  isPointOnJ {k : ℕ} (hk : k < sp3) {b c : ℕ} (hb : b < sievingPrime pnn k)
    (hc : c < sievingPrime pnn k) :
    ct.isPointOnJ[(pnn[k]! * maxPrimeEven + b) * maxPrimeEven + c]! =
      refIsPointOnJ cs deg (sievingPrime pnn k) b c

namespace CurveTables

/-- Whether the sieve tables of the first two stages admit the class of `(a, b, c)` modulo the
prime `p = prime[pn]`, read from the tables of the curve `ct` as `init_sieve` reads them: for the
residues of `a`, `b` and `c`, every class with `p ∣ a` and `p ∣ b`; for `p ∣ a` and `p ∤ b`, by
`has_infinity` and `is_f_square` at `c / b`; for `p ∤ a`, by `is_point_on_j` at
`(1, b / a, c / a)`, the quotients by the inverses modulo `p` (`JPoints.refInverse`). -/
def admits12 (ct : CurveTables) (pn : ℕ) (a b c : ℤ) : Bool :=
  let p := primeTable[pn]!
  let a := (a % p).toNat
  let b := (b % p).toNat
  let c := (c % p).toNat
  if a = 0 then
    b == 0 || ct.hasInfinity[pn]! && ct.isFSquare[pn * maxPrimeEven + c * refInverse p b % p]!
  else ct.isPointOnJ[(pn * maxPrimeEven + b * refInverse p a % p) * maxPrimeEven +
    c * refInverse p a % p]!

/-- The class test of the first two stages depends only on the classes of the coordinates modulo the
prime. -/
theorem admits12_congr {ct : CurveTables} {pn : ℕ} {a a' b b' c c' : ℤ}
    (ha : a % (primeTable[pn]! : ℤ) = a' % primeTable[pn]!)
    (hb : b % (primeTable[pn]! : ℤ) = b' % primeTable[pn]!)
    (hc : c % (primeTable[pn]! : ℤ) = c' % primeTable[pn]!) :
    ct.admits12 pn a b c = ct.admits12 pn a' b' c' := by
  simp only [admits12, ha, hb, hc]

theorem admits12_natCast_mod (ct : CurveTables) (pn : ℕ) (a b : ℤ) (x : ℕ) :
    ct.admits12 pn a b ((x % primeTable[pn]! : ℕ) : ℤ) = ct.admits12 pn a b x := by
  simp only [admits12, Int.toNat_natCast_emod, Nat.mod_mod]

@[simp]
theorem admits12_zero_zero (ct : CurveTables) (pn : ℕ) (c : ℤ) : ct.admits12 pn 0 0 c = true := by
  simp [admits12]

/-- Whether the third stage of the sieve admits the class of `(a, b, c)` modulo the prime
`p = prime[pn]`, read from the tables of the curve `ct` as `row3_setup` and `check_bit` read them:
the test of the first two stages (`JPoints.CurveTables.admits12`) without `has_infinity`. -/
def admits3 (ct : CurveTables) (pn : ℕ) (a b c : ℤ) : Bool :=
  let p := primeTable[pn]!
  let a := (a % p).toNat
  let b := (b % p).toNat
  let c := (c % p).toNat
  if a = 0 then b == 0 || ct.isFSquare[pn * maxPrimeEven + c * refInverse p b % p]!
  else ct.isPointOnJ[(pn * maxPrimeEven + b * refInverse p a % p) * maxPrimeEven +
    c * refInverse p a % p]!

theorem WF.admits12_eq {ct : CurveTables} {cs : List ℤ} {deg nPrimes : ℕ} {pnn : Array ℕ}
    {sp3 : ℕ} (h : ct.WF cs deg nPrimes pnn sp3) (hn : nPrimes ≤ numPrimes) {k : ℕ}
    (hk : k < sp3) (hlt : pnn[k]! < nPrimes) (a b c : ℤ) :
    ct.admits12 pnn[k]! a b c = refAdmits12 cs deg (sievingPrime pnn k) a b c := by
  have hp : 0 < sievingPrime pnn k :=
    (prime_getElem!_primeTable (hlt.trans_le hn)).pos
  simp only [admits12, refAdmits12]
  split_ifs
  · rw [h.hasInfinity hlt, h.isFSquare hlt (Nat.mod_lt _ hp)]
  · exact h.isPointOnJ hk (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)

theorem WF.admits3_eq {ct : CurveTables} {cs : List ℤ} {deg nPrimes : ℕ} {pnn : Array ℕ}
    {sp3 : ℕ} (h : ct.WF cs deg nPrimes pnn sp3) (hn : nPrimes ≤ numPrimes) {k : ℕ}
    (hk : k < sp3) (hlt : pnn[k]! < nPrimes) (a b c : ℤ) :
    ct.admits3 pnn[k]! a b c = refAdmits3 cs deg (sievingPrime pnn k) a b c := by
  have hp : 0 < sievingPrime pnn k :=
    (prime_getElem!_primeTable (hlt.trans_le hn)).pos
  simp only [admits3, refAdmits3]
  split_ifs
  · rw [h.isFSquare hlt (Nat.mod_lt _ hp)]
  · exact h.isPointOnJ hk (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)

end CurveTables

/-- The sieve tables `st` of the first two stages as `init_sieve` builds them from the tables of the
curve `ct`, for the sieving primes `p` of the plan whose indices in the table are `pnn`, the `n`-th
for `n < sp2`: bit `j` of word `w ≤ p` of the row of `(a, b)`, `a, b < p`, in `sieve_tab[n]`, from
word `(a p + b) (p + 1)` on, is the class test of `(a, b, 64 w + j)` modulo `p`
(`JPoints.CurveTables.admits12`); word `p` of a row repeats word `0`. -/
structure SieveTables.WF (st : SieveTables) (ct : CurveTables) (pnn : Array ℕ) (sp2 : ℕ) :
    Prop where
  /-- The bits of the rows of the sieve tables are the class tests of the tables of the curve. -/
  getLsbD_eq_admits12 {n : ℕ} (hn : n < sp2) {a b w j : ℕ} (ha : a < sievingPrime pnn n)
    (hb : b < sievingPrime pnn n) (hw : w ≤ sievingPrime pnn n) (hj : j < 64) :
    BitVec.getLsbD
        (st.sieveTab[n]![(a * sievingPrime pnn n + b) * (sievingPrime pnn n + 1) + w]!).toBitVec j =
      ct.admits12 pnn[n]! a b (64 * w + j : ℕ)

end JPoints

end
