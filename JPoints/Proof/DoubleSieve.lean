/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.Kummer
public import Mathlib.Data.ZMod.Defs
public import Std.WP

import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Order
import JPoints.Proof.Reduction
import JPoints.Proof.Sift
import JPoints.Proof.Transform
import JPoints.Proof.VCSimp
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Std.Tactic.Do

/-!
# The sieve of the pairs of the double points

`find_double_points` hands the triple `(a², 2ab, b²)` of the double point of `x = b / a` to the
exact check only when `a` and `b` are coprime (`relprime`, `JPoints.relprime_spec`) and the pair
`(a, b)` passes its sieve: at each sieving prime `p` the record of `a` (`JPoints.doubleRecord`)
reads the table of the squares of `f` at `b / a mod p`, or for `p ∣ a` whether the curve has points
at infinity modulo `p`; for a curve that is not a monic quintic it skips every `a` that a sieving
prime divides modulo which the curve has no points at infinity. The sieve and the skip are sound: a
point over the triple makes `F(b, a) = a⁶ f(b / a)` a square
(`JPoints.isSquare_sexticForm_of_hasPointOver`), so that `f(b / a)` is a square modulo `p ∤ a` and
`f₆` one modulo `p ∣ a` (`JPoints.DoubleSetup.passes_of_points_ne_nil`,
`JPoints.DoubleSetup.hasInfinity_of_points_ne_nil`); for a monic quintic it makes `a` a square
(`JPoints.isSquare_of_isSquare_sexticForm`).

## Main definitions

* `JPoints.GcdLoopInvariant`: the invariant of the loop of the binary algorithm of `relprime`.
* `JPoints.Stype.passes`: whether a record of the sieve passes a second coordinate.
* `JPoints.DoubleSieveInvariant`: the invariant of the loop of the sieve.
* `JPoints.doubleRecord`, `JPoints.DoubleRecordsWF`: the records of a first coordinate, and the
  records that hold the primes of the plan.
* `JPoints.DoubleSetupInvariant`: the invariant of the loop that sets the records.
* `JPoints.DoubleSetup`: what `find_double_points` reads of the globals of the sieve.

## Main statements

* `JPoints.isSquare_sexticForm_of_hasPointOver`: a point over a double point makes `F(t, s)` a
  square.
* `JPoints.isSquare_of_isSquare_sexticForm`: the first coordinates of the double points of a monic
  quintic.
* `JPoints.relprime_spec`: the test for common factors.
* `JPoints.findDoublePointsSieve_spec`, `JPoints.findDoublePointsSetup_spec`: the sieve of a pair
  and the records of a first coordinate.
* `JPoints.DoubleSetup.passes_of_points_ne_nil`, `JPoints.DoubleSetup.hasInfinity_of_points_ne_nil`:
  the sieve and the skip keep every pair with a point.

## Implementation notes

`vcgen` copies the code of `relprime` after each of its two `if`s that change `m`, so that its five
`while` loops appear in four blocks. The loops that take the odd part of an integer have a contract
of their own (`JPoints.forIn_loop_shiftRight_spec`, in `JPoints.Proof.Sift`), so that only the four
copies of the loop of the binary algorithm need an invariant and a variant. The facts modulo `p`
are proved in `ZMod p`, from the casts of the integer identities.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The squares of the double points -/

/-- On the conic `b² = 4ac`, over the triple `(m s², 2 m s t, m t²)` of the double point of
`x = t / s`, the value `F(t, s) = s⁶ f(t / s)` from `A₂`, `B₂` and `C`:
`m⁴ s⁴ F(t, s) = t² A₂ + s t C + s² B₂`, which is `(t α + s β)²` when `A₂ = α²`, `B₂ = β²` and
`C = 2 α β`. -/
theorem pow_four_mul_pow_four_mul_sexticForm_eq (f : ℕ → ℤ) (m s t d : ℤ) :
    m ^ 4 * s ^ 4 * sexticForm f t s =
      t ^ 2 * auxA2 f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d +
        s * t * auxC f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d +
        s ^ 2 * auxB2 f (m * s ^ 2) (m * (2 * s * t)) (m * t ^ 2) d := by
  simp only [sexticForm, auxA2, auxB2, auxC, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- A point of the Kummer surface that lifts over the triple `(s², 2st, t²)` of a double point,
`s ≠ 0`, makes `F(t, s) = s⁶ f(t / s)` a square, by
`JPoints.pow_four_mul_pow_four_mul_sexticForm_eq`: the point `(t / s, y)` of the curve whose double
it is has `y` rational. -/
theorem isSquare_sexticForm_of_hasPointOver {cs : List ℤ} {s t : ℤ} (hs : s ≠ 0)
    (h : HasPointOver cs (s ^ 2, 2 * s * t, t ^ 2)) : IsSquare (sexticForm (cs.getD · 0) t s) := by
  obtain ⟨p, hp, hl⟩ := h
  have hK := kummer_eq_zero_of_mem_kummerPoints hp
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
  have hm : (x.den : ℤ) ≠ 0 := by positivity
  simp only [Lifts, mul_ne_zero hm (pow_ne_zero 2 hs), ↓reduceIte] at hl
  obtain ⟨α, β, hα, hβ, hC⟩ := exists_auxC_eq_two_mul_mul hK hl.1 hl.2
  refine Int.isSquare_of_sq_mul_eq_sq (a := x.den ^ 2 * s ^ 2) (b := t * α + s * β)
    (by positivity) ?_
  linear_combination pow_four_mul_pow_four_mul_sexticForm_eq _ x.den s t x.num + t ^ 2 * hα +
    s * t * hC + s ^ 2 * hβ

/-- For a quintic with a unit leading coefficient, `F(t, s) = s G` with `G ≡ f₅ t⁵` modulo `s`, so
that a square `F(t, s)` with coprime `s > 0` and `t` makes `s` a square: the double points of a
monic quintic have first coordinates `s²` of squares `s`. -/
theorem isSquare_of_isSquare_sexticForm {f : ℕ → ℤ} (h6 : f 6 = 0) (h5 : IsUnit (f 5)) {s t : ℤ}
    (hs : 0 < s) (hst : Int.gcd s t = 1) (h : IsSquare (sexticForm f t s)) : IsSquare s := by
  obtain ⟨w, hw⟩ := h
  have hF : s * (f 5 * t ^ 5 + s * (f 4 * t ^ 4 + f 3 * t ^ 3 * s + f 2 * t ^ 2 * s ^ 2 +
      f 1 * t * s ^ 3 + f 0 * s ^ 4)) = w * w := by
    rw [← hw]
    simp only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero, h6]
    ring
  have hc : IsCoprime s (f 5 * t ^ 5) := (isCoprime_mul_unit_left_right h5 s _).mpr
    (Int.isCoprime_iff_gcd_eq_one.mpr hst).pow_right
  obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime (hc.add_mul_left_right _) (hF.trans (sq w).symm)
  · exact ⟨a, by rw [ha, sq]⟩
  · lia [sq_nonneg a]

theorem cast_sexticForm {R : Type*} [CommRing R] (f : ℕ → ℤ) (x z : ℤ) :
    ((sexticForm f x z : ℤ) : R) =
      ∑ k ∈ Finset.range 7, (f k : R) * (x : R) ^ k * (z : R) ^ (6 - k) := by
  simp [sexticForm]

theorem sexticForm_mul_left (f : ℕ → ℤ) (x z : ℤ) :
    sexticForm f (z * x) z = z ^ 6 * sexticForm f x 1 := by
  simp only [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- A square `F(t, s)` with `p ∣ s` and `p ∤ t` makes the leading coefficient `f₆` a square
modulo `p`, since `F(t, s) ≡ f₆ t⁶`: the curve has points at infinity modulo `p`. -/
theorem isSquare_cast_of_isSquare_sexticForm {p : ℕ} [Fact p.Prime] {f : ℕ → ℤ} {s t : ℤ}
    (hst : Int.gcd s t = 1) (hps : (p : ℤ) ∣ s) (h : IsSquare (sexticForm f t s)) :
    IsSquare ((f 6 : ℤ) : ZMod p) := by
  obtain ⟨w, hw⟩ := h
  have hs : (s : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mpr hps
  have ht : (t : ZMod p) ≠ 0 := fun ht ↦ (Fact.out : p.Prime).one_lt.ne' (by
    have := Int.dvd_coe_gcd hps ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp ht)
    rw [hst] at this
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hw' : ((sexticForm f t s : ℤ) : ZMod p) = ((w * w : ℤ) : ZMod p) := by rw [hw]
  simp only [cast_sexticForm, hs, Finset.sum_range_succ, Finset.sum_range_zero] at hw'
  refine ⟨w / t ^ 3, ?_⟩
  push_cast at hw'
  rw [div_mul_div_comm, eq_div_iff (by simp [ht])]
  linear_combination hw'

/-- A square `F(t, s)` with `p ∤ s` makes `f(x)` a square modulo `p` for the residue `x ≡ t / s`:
`F(t, s) ≡ s⁶ f(x)`. -/
theorem isSquare_cast_sexticForm_of_isSquare_sexticForm {p : ℕ} [Fact p.Prime] {f : ℕ → ℤ}
    {s t x : ℤ} (hps : ¬(p : ℤ) ∣ s) (hx : (s : ZMod p) * x = t) (h : IsSquare (sexticForm f t s)) :
    IsSquare ((sexticForm f x 1 : ℤ) : ZMod p) := by
  obtain ⟨w, hw⟩ := h
  have hs : (s : ZMod p) ≠ 0 := fun hs ↦ hps ((ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hs)
  have hw' : ((sexticForm f (s * x) s : ℤ) : ZMod p) = w * w := by
    rw [cast_sexticForm, Int.cast_mul, hx, ← cast_sexticForm, hw, Int.cast_mul]
  rw [sexticForm_mul_left, Int.cast_mul, Int.cast_pow] at hw'
  refine ⟨w / s ^ 3, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (by simp [hs])]
  linear_combination hw'

/-! ### The tables modulo a prime -/

/-- The residue that the sieve of `find_double_points` reads for `b` and the record of a prime
`p ∤ a`, `a⁻¹ b mod p` with the inverse of `JPoints.refInverse` (`JPoints.refInverse_val`), is the
quotient `b / a` modulo `p`. -/
theorem cast_mul_refInverse_mul_emod {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : ¬(p : ℤ) ∣ a) (b : ℤ) :
    (a : ZMod p) * ((((refInverse p (a % p).toNat : ℕ) : ℤ) * (b % p) % p : ℤ) : ZMod p) = b := by
  have hA : (a : ZMod p) ≠ 0 := fun h ↦ ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  rw [toNat_emod_eq_val, refInverse_val hA, ZMod.intCast_mod, Int.cast_mul, ZMod.intCast_mod,
    Int.cast_natCast, ZMod.natCast_zmod_val, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]

/-! ### The test for common factors -/

/-- The invariant of the loop of `relprime` that replaces the larger of the odd `x, y > 0` by the
odd part of their difference: they stay odd and positive and coprime exactly when `n` and `m`
are, and they are equal after the loop. -/
def GcdLoopInvariant (n m : ℤ) : Std.WP.WhileInvariant (ℤ × ℤ) Prop :=
  .mk fun exit s ↦ 0 < s.1 ∧ 0 < s.2 ∧ s.1 % 2 = 1 ∧ s.2 % 2 = 1 ∧
    (Int.gcd s.1 s.2 = 1 ↔ Int.gcd n m = 1) ∧ (exit = true → s.1 = s.2)

-- The verification conditions of `JPoints.relprime`, each in its shape; the loops that take the
-- odd part of an integer by the contract `JPoints.forIn_loop_shiftRight_spec`.

-- The odd part `y` of `M >>> 1` for an even `M` is that of `M`.
private theorem two_pow_succ_mul_eq_of_shiftRight {M y : ℤ} (he : M % 2 = 0) {t : ℕ}
    (ht : (2 : ℤ) ^ t * y = M >>> 1) : (2 : ℤ) ^ (t + 1) * y = M := by
  rw [Int.shiftRight_one_eq_ediv_two] at ht
  rw [pow_succ, mul_comm _ (2 : ℤ), mul_assoc, ht]
  lia

private theorem pos_of_one_le {n : ℤ} (h : 1 ≤ n) : 0 < n := h

private theorem shiftRight_one_pos_of_neg {m : ℤ} (hm : m < 0) (he : (-m % 2 == 0) = true) :
    (0 : ℤ) < (-m) >>> 1 := by
  have : -m % 2 = 0 := by simpa using he
  rw [Int.shiftRight_one_eq_ediv_two]
  lia

private theorem shiftRight_one_pos {m : ℤ} (h0 : ¬(m == 0) = true) (hm : ¬m < 0)
    (he : (m % 2 == 0) = true) : (0 : ℤ) < m >>> 1 := by
  have : m ≠ 0 := by simpa using h0
  have : m % 2 = 0 := by simpa using he
  rw [Int.shiftRight_one_eq_ediv_two]
  lia

private theorem relprime_post_zero {n m : ℤ} (hn : 1 ≤ n) (hm : (m == 0) = true) :
    (n == 1) = decide (n.gcd m = 1) := by
  obtain rfl : m = 0 := by simpa using hm
  simp only [Int.gcd_zero_right, beq_eq_decide]
  congr 1
  lia

private theorem relprime_post_even {n m : ℤ} (hm : (m % 2 == 0) = true) (hn : (n % 2 == 0) = true) :
    false = decide (n.gcd m = 1) := by
  have h2 : (2 : ℤ) ∣ (n.gcd m : ℤ) := Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero (by simpa using hn))
    (Int.dvd_of_emod_eq_zero (by simpa using hm))
  have : n.gcd m ≠ 1 := fun h ↦ by rw [h] at h2; lia
  simp [this]

private theorem relprime_post_even_neg {n m : ℤ} (hm : (-m % 2 == 0) = true)
    (hn : (n % 2 == 0) = true) : false = decide (n.gcd m = 1) := by
  rw [← Int.gcd_neg]
  exact relprime_post_even hm hn

-- The start of the loop of the binary algorithm from the odd parts `x` of `n` and `y` of `M >>> 1`
-- for an even `M` with `gcd(n, M) = gcd(n, m)`, `M = |m|`.
private theorem GcdLoopInvariant.of_oddPart {n m M x y : ℤ} (hM : Int.gcd n M = Int.gcd n m)
    (he : (M % 2 == 0) = true) (hn : ¬(n % 2 == 0) = true)
    (hy : 0 < y ∧ y % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * y = M >>> 1)
    (hx : 0 < x ∧ x % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * x = n) :
    GcdLoopInvariant n m false (x, y) := by
  obtain ⟨hy0, hy1, j, hj⟩ := hy
  obtain ⟨hx0, hx1, k, hk⟩ := hx
  have hn' : n % 2 = 1 := by simp at hn; lia
  refine ⟨hx0, hy0, hx1, hy1, ?_, nofun⟩
  rw [← hM, Int.gcd_eq_gcd_of_two_pow_mul_eq hk
    (two_pow_succ_mul_eq_of_shiftRight (by simpa using he) hj) hx1 hy1 (.inl hn')]

private theorem GcdLoopInvariant.of_oddPart_neg {n m : ℤ} (hm : m < 0) (ho : ¬(-m % 2 == 0) = true)
    {x : ℤ} (hx : 0 < x ∧ x % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * x = n) :
    GcdLoopInvariant n m false (x, -m) := by
  obtain ⟨hx0, hx1, k, hk⟩ := hx
  have ho' : -m % 2 = 1 := by simp at ho; lia
  refine ⟨hx0, by lia, hx1, ho', ?_, nofun⟩
  rw [← Int.gcd_neg (b := m), ← hk, Int.gcd_two_pow_mul_of_emod_two_eq_one ho']

private theorem GcdLoopInvariant.of_oddPart_pos {n m : ℤ} (hm : ¬m < 0) (ho : ¬(m % 2 == 0) = true)
    {x : ℤ} (hx : 0 < x ∧ x % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * x = n) :
    GcdLoopInvariant n m false (x, m) := by
  obtain ⟨hx0, hx1, k, hk⟩ := hx
  have ho' : m % 2 = 1 := by simp at ho; lia
  refine ⟨hx0, by lia, hx1, ho', ?_, nofun⟩
  rw [← hk, Int.gcd_two_pow_mul_of_emod_two_eq_one ho']

private theorem GcdLoopInvariant.post {n m x y : ℤ} (h : GcdLoopInvariant n m true (x, y)) :
    (y == 1) = decide (n.gcd m = 1) := by
  obtain ⟨-, hy, -, -, hg, he⟩ := h
  obtain rfl : x = y := he rfl
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← hg, Int.gcd_self]
  lia

private theorem GcdLoopInvariant.exit {n m x y : ℤ} {mb : ℕ} (hne : ¬(x != y) = true)
    (h : (x + y).toNat = mb ∧ GcdLoopInvariant n m false (x, y)) :
    GcdLoopInvariant n m true (x, y) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun _ ↦ by simpa using hne⟩

private theorem GcdLoopInvariant.shiftRight_sub_pos {n m x y : ℤ} {mb : ℕ} (hlt : y < x)
    (h : (x + y).toNat = mb ∧ GcdLoopInvariant n m false (x, y)) : (0 : ℤ) < (x - y) >>> 1 := by
  rw [Int.shiftRight_one_eq_ediv_two]
  lia [h.2.2.2.1, h.2.2.2.2.1]

private theorem GcdLoopInvariant.shiftRight_sub_pos' {n m x y : ℤ} {mb : ℕ} (hne : (x != y) = true)
    (hlt : ¬y < x) (h : (x + y).toNat = mb ∧ GcdLoopInvariant n m false (x, y)) :
    (0 : ℤ) < (y - x) >>> 1 := by
  have := bne_iff_ne.mp hne
  rw [Int.shiftRight_one_eq_ediv_two]
  lia [h.2.2.2.1, h.2.2.2.2.1]

private theorem GcdLoopInvariant.sub {n m x y z : ℤ} {mb : ℕ}
    (hz : 0 < z ∧ z % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * z = (x - y) >>> 1)
    (h : (x + y).toNat = mb ∧ GcdLoopInvariant n m false (x, y)) :
    (z + y).toNat < mb ∧ GcdLoopInvariant n m false (z, y) := by
  obtain ⟨rfl, hx0, hy0, hx1, hy1, hg, -⟩ := h
  obtain ⟨hz0, hz1, k, hk⟩ := hz
  have hk' := two_pow_succ_mul_eq_of_shiftRight (by lia) hk
  have hle : z ≤ x - y := hk' ▸ le_mul_of_one_le_left hz0.le (one_le_pow₀ one_le_two)
  refine ⟨by lia, hz0, hy0, hz1, hy1, ?_, nofun⟩
  rw [← Int.gcd_two_pow_mul_of_emod_two_eq_one hy1 (k + 1), hk', Int.gcd_sub_self_left, hg]

private theorem GcdLoopInvariant.sub_right {n m x y z : ℤ} {mb : ℕ}
    (hz : 0 < z ∧ z % 2 = 1 ∧ ∃ t : ℕ, (2 : ℤ) ^ t * z = (y - x) >>> 1)
    (h : (x + y).toNat = mb ∧ GcdLoopInvariant n m false (x, y)) :
    (x + z).toNat < mb ∧ GcdLoopInvariant n m false (x, z) := by
  obtain ⟨rfl, hx0, hy0, hx1, hy1, hg, -⟩ := h
  obtain ⟨hz0, hz1, k, hk⟩ := hz
  have hk' := two_pow_succ_mul_eq_of_shiftRight (by lia) hk
  have hle : z ≤ y - x := hk' ▸ le_mul_of_one_le_left hz0.le (one_le_pow₀ one_le_two)
  refine ⟨by lia, hx0, hz0, hx1, hz1, ?_, nofun⟩
  rw [Int.gcd_comm, ← Int.gcd_two_pow_mul_of_emod_two_eq_one hx1 (k + 1), hk',
    Int.gcd_sub_self_left, Int.gcd_comm, hg]

attribute [local irreducible] GcdLoopInvariant in
/-- `relprime` decides whether `n ≥ 1` and `m` are coprime: it replaces `|m|` and `n` by their odd
parts (after the test of two even numbers, by `JPoints.forIn_loop_shiftRight_spec`), which keeps
their coprimality, and the larger of the two by the odd part of their difference until they are
equal (`JPoints.GcdLoopInvariant`), to the odd part of their gcd. -/
@[spec]
-- lint: allow long-proof: the four copies of the loop of the binary algorithm, and their VCs
theorem relprime_spec (n m : ℤ) :
    ⦃ 1 ≤ n ⦄ relprime n m ⦃ fun r ↦ r = decide (Int.gcd n m = 1) ⦄ := by
  vcgen [relprime, forIn_loop_shiftRight_spec] invariants
  · GcdLoopInvariant n m
  · .ofMeasure fun s : ℤ × ℤ ↦ (s.1 + s.2).toNat
  · GcdLoopInvariant n m
  · .ofMeasure fun s : ℤ × ℤ ↦ (s.1 + s.2).toNat
  · GcdLoopInvariant n m
  · .ofMeasure fun s : ℤ × ℤ ↦ (s.1 + s.2).toNat
  · GcdLoopInvariant n m
  · .ofMeasure fun s : ℤ × ℤ ↦ (s.1 + s.2).toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact relprime_post_zero ‹_› ‹_›
    | exact relprime_post_even ‹_› ‹_›
    | exact relprime_post_even_neg ‹_› ‹_›
    | exact pos_of_one_le ‹_›
    | exact shiftRight_one_pos_of_neg ‹_› ‹_›
    | exact shiftRight_one_pos ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.of_oddPart Int.gcd_neg ‹_› ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.of_oddPart rfl ‹_› ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.of_oddPart_neg ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.of_oddPart_pos ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.post ‹_›
    | exact GcdLoopInvariant.exit ‹_› ‹_›
    | exact GcdLoopInvariant.shiftRight_sub_pos ‹_› ‹_›
    | exact GcdLoopInvariant.shiftRight_sub_pos' ‹_› ‹_› ‹_›
    | exact GcdLoopInvariant.sub ‹_› ‹_›
    | exact GcdLoopInvariant.sub_right ‹_› ‹_›

/-! ### The records of the sieve of the pairs -/

/-- Whether the sieve of `find_double_points` passes the second coordinate `b` at the record `r`
of a sieving prime `p`, for the tables of the curve `ct`: the entry of the table of the record at
`(ap * bp) mod p`, `bp = b mod p`. -/
def Stype.passes (ct : CurveTables) (r : Stype) (b : ℤ) : Bool :=
  r.ptr.read ct (r.ap * (b % r.p) % r.p).toNat

/-- The invariant of the loop of `JPoints.findDoublePointsSieve` over the records `k` of `ssp0`:
while it goes on, every record of `pref` passes `b`; once it has returned, it returned whether
every record of the first `sp3` passes `b`. -/
def DoubleSieveInvariant (ct : CurveTables) (ssp0 : Array Stype) (sp3 : ℕ) (b : ℤ)
    (pref suff : List ℕ) (st : Option Bool × PUnit) : Prop :=
  st.1.elim ((pref.all fun k ↦ ssp0[k]!.passes ct b) = true) fun r ↦
    suff = [] ∧ r = (List.range sp3).all fun k ↦ ssp0[k]!.passes ct b

section DoubleSieve

variable {ct : CurveTables} {ssp0 : Array Stype} {sp3 : ℕ} {b : ℤ}

private theorem doubleSieveInvariant_nil (l : List ℕ) :
    DoubleSieveInvariant ct ssp0 sp3 b [] l (none, PUnit.unit) := by
  simp [DoubleSieveInvariant]

private theorem DoubleSieveInvariant.post_some {st : Option Bool × PUnit}
    (h : DoubleSieveInvariant ct ssp0 sp3 b (ForIn.toList [:sp3]) [] st) {r : Bool}
    (hr : st.1 = some r) : r = (List.range sp3).all fun k ↦ ssp0[k]!.passes ct b := by
  obtain ⟨x, u⟩ := st
  obtain rfl : x = some r := hr
  exact h.2

private theorem DoubleSieveInvariant.post_none {st : Option Bool × PUnit}
    (h : DoubleSieveInvariant ct ssp0 sp3 b (ForIn.toList [:sp3]) [] st) (hr : st.1 = none) :
    true = (List.range sp3).all fun k ↦ ssp0[k]!.passes ct b := by
  obtain ⟨x, u⟩ := st
  obtain rfl : x = none := hr
  simpa [DoubleSieveInvariant, Std.Legacy.Range.toList_eq_range] using h.symm

private theorem DoubleSieveInvariant.fail {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) (hr : ssp0[cur]!.passes ct b = false) :
    DoubleSieveInvariant ct ssp0 sp3 b (ForIn.toList [:sp3]) [] (some false, PUnit.unit) := by
  have hc : cur ∈ List.range sp3 := by simp [← Std.Legacy.Range.toList_eq_range, hl]
  refine ⟨rfl, (Bool.eq_false_iff.mpr fun h ↦ ?_).symm⟩
  rw [List.all_eq_true] at h
  simp [h cur hc] at hr

private theorem DoubleSieveInvariant.pass {pref suff : List ℕ} {cur : ℕ} {x : Option Bool}
    (h : DoubleSieveInvariant ct ssp0 sp3 b pref (cur :: suff) (x, PUnit.unit))
    (hr : ssp0[cur]!.passes ct b = true) :
    DoubleSieveInvariant ct ssp0 sp3 b (pref ++ [cur]) suff (none, PUnit.unit) := by
  cases x with
  | none => simpa [DoubleSieveInvariant, hr] using h
  | some r => exact absurd h.1 (List.cons_ne_nil _ _)

/-- The entry that the sieve reads for the record `r`, with C's remainder `b % p` corrected by `p`
when it is negative, is the one of `JPoints.Stype.passes`. -/
theorem Stype.passes_eq (ct : CurveTables) {r : Stype} (hp : 0 < r.p) (ha : 0 ≤ r.ap) (b : ℤ) :
    r.passes ct b = r.ptr.read ct
      ((r.ap * if b.tmod r.p < 0 then b.tmod r.p + r.p else b.tmod r.p).tmod r.p).toNat := by
  rw [Int.ite_tmod_lt_zero_eq_emod b hp, passes,
    Int.tmod_eq_emod_of_nonneg (mul_nonneg ha (Int.emod_nonneg b hp.ne'))]

-- The verification conditions of `JPoints.findDoublePointsSieve`, each in its shape.

private theorem DoubleSieveInvariant.fail_neg {pref suff : List ℕ} {cur : ℕ}
    (hpre : ∀ k < sp3, 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap)
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) (hn : b.tmod ssp0[cur]!.p < 0)
    (hr : (!ssp0[cur]!.ptr.read ct
      ((ssp0[cur]!.ap * (b.tmod ssp0[cur]!.p + ssp0[cur]!.p)).tmod ssp0[cur]!.p).toNat) = true) :
    DoubleSieveInvariant ct ssp0 sp3 b (ForIn.toList [:sp3]) [] (some false, PUnit.unit) := by
  have h := hpre cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  refine fail hl ?_
  simpa [Stype.passes_eq ct h.1 h.2, hn] using hr

private theorem DoubleSieveInvariant.fail_nonneg {pref suff : List ℕ} {cur : ℕ}
    (hpre : ∀ k < sp3, 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap)
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) (hn : ¬b.tmod ssp0[cur]!.p < 0)
    (hr : (!ssp0[cur]!.ptr.read ct
      ((ssp0[cur]!.ap * b.tmod ssp0[cur]!.p).tmod ssp0[cur]!.p).toNat) = true) :
    DoubleSieveInvariant ct ssp0 sp3 b (ForIn.toList [:sp3]) [] (some false, PUnit.unit) := by
  have h := hpre cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  refine fail hl ?_
  simpa [Stype.passes_eq ct h.1 h.2, hn] using hr

private theorem DoubleSieveInvariant.pass_neg {pref suff : List ℕ} {cur : ℕ}
    (hpre : ∀ k < sp3, 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap)
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) {x : Option Bool}
    (h : DoubleSieveInvariant ct ssp0 sp3 b pref (cur :: suff) (x, PUnit.unit))
    (hn : b.tmod ssp0[cur]!.p < 0)
    (hr : ¬(!ssp0[cur]!.ptr.read ct
      ((ssp0[cur]!.ap * (b.tmod ssp0[cur]!.p + ssp0[cur]!.p)).tmod ssp0[cur]!.p).toNat) = true) :
    DoubleSieveInvariant ct ssp0 sp3 b (pref ++ [cur]) suff (none, PUnit.unit) := by
  have hk := hpre cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  refine h.pass ?_
  simpa [Stype.passes_eq ct hk.1 hk.2, hn] using hr

private theorem DoubleSieveInvariant.pass_nonneg {pref suff : List ℕ} {cur : ℕ}
    (hpre : ∀ k < sp3, 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap)
    (hl : ForIn.toList [:sp3] = pref ++ cur :: suff) {x : Option Bool}
    (h : DoubleSieveInvariant ct ssp0 sp3 b pref (cur :: suff) (x, PUnit.unit))
    (hn : ¬b.tmod ssp0[cur]!.p < 0)
    (hr : ¬(!ssp0[cur]!.ptr.read ct
      ((ssp0[cur]!.ap * b.tmod ssp0[cur]!.p).tmod ssp0[cur]!.p).toNat) = true) :
    DoubleSieveInvariant ct ssp0 sp3 b (pref ++ [cur]) suff (none, PUnit.unit) := by
  have hk := hpre cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  refine h.pass ?_
  simpa [Stype.passes_eq ct hk.1 hk.2, hn] using hr

end DoubleSieve

attribute [local irreducible] DoubleSieveInvariant in
/-- The sieve of `find_double_points` passes the second coordinate `b` when every record of the
first `sieve_primes3` sieving primes passes it (`JPoints.Stype.passes`), for records of positive
primes and nonnegative inverses. -/
@[spec]
theorem findDoublePointsSieve_spec (ct : CurveTables) (ssp0 : Array Stype) (sp3 : ℕ) (b : ℤ) :
    ⦃ ∀ k < sp3, 0 < ssp0[k]!.p ∧ 0 ≤ ssp0[k]!.ap ⦄
    findDoublePointsSieve ct ssp0 sp3 b
    ⦃ fun r ↦ r = (List.range sp3).all fun k ↦ ssp0[k]!.passes ct b ⦄ := by
  vcgen [findDoublePointsSieve] invariants
  · DoubleSieveInvariant ct ssp0 sp3 b
  all_goals with_reducible first
    | exact doubleSieveInvariant_nil _
    | exact DoubleSieveInvariant.post_some ‹_› ‹_›
    | exact DoubleSieveInvariant.post_none ‹_› ‹_›
    | exact DoubleSieveInvariant.fail_neg ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSieveInvariant.fail_nonneg ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSieveInvariant.pass_neg ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSieveInvariant.pass_nonneg ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The record `ssp0[n]` of the sieve of `find_double_points` for the `n`-th sieving prime
`p = prime[pnn[n]]` and the first coordinate `a`, as the loop over the sieving primes sets it: for
`p ∣ a` the inverse `0` and the pointer to `has_infinity[pnn[n]]`, otherwise the inverse of
`a mod p` in the table `inverses` and the pointer to the row of `p` of `is_f_square`. -/
def doubleRecord (g : SiftGlobals) (a : ℤ) (n : ℕ) : Stype :=
  if a % sievingPrime g.pnn n = 0 then
    { p := sievingPrime g.pnn n, ap := 0, ptr := .hasInfinity g.pnn[n]! }
  else
    { p := sievingPrime g.pnn n
      ap := g.tables.inverses[g.pnn[n]! * maxPrimeEven + (a % sievingPrime g.pnn n).toNat]!
      ptr := .isFSquare (g.pnn[n]! * maxPrimeEven) }

/-- The records `ssp0` of the sieve of `find_double_points` hold the primes of the plan: there are
`NUM_PRIMES` of them, and the first `sieve_primes3` have the sieving primes. -/
def DoubleRecordsWF (g : SiftGlobals) (ssp0 : Array Stype) : Prop :=
  ssp0.size = numPrimes ∧ ∀ n < g.sievePrimes3, ssp0[n]!.p = sievingPrime g.pnn n

/-- The invariant of the loop of `JPoints.findDoublePointsSetup` over the sieving primes, for the
first coordinate `a`: the records hold the primes of the plan, and while it goes on those of the
primes of `pref` are those for `a` (`JPoints.doubleRecord`); once it has returned, `skip` holds
and a sieving prime divides `a` modulo which the curve has no points at infinity. -/
def DoubleSetupInvariant (g : SiftGlobals) (skip : Bool) (a : ℤ) (pref suff : List ℕ)
    (st : Option (Array Stype × Bool) × Array Stype) : Prop :=
  st.1.elim (DoubleRecordsWF g st.2 ∧ ∀ n < pref.length, st.2[n]! = doubleRecord g a n)
    fun r ↦ suff = [] ∧ DoubleRecordsWF g r.1 ∧ r.2 = false ∧ skip = true ∧ ∃ n < g.sievePrimes3,
      a % sievingPrime g.pnn n = 0 ∧ g.curve.hasInfinity[g.pnn[n]!]! = false

section DoubleSetup

variable {g : SiftGlobals} {skip : Bool} {a : ℤ} {ssp0 : Array Stype}

-- The postcondition of `JPoints.findDoublePointsSetup_spec`.
private abbrev DoubleSetupPost (g : SiftGlobals) (skip : Bool) (a : ℤ) (s : Array Stype)
    (through : Bool) : Prop :=
  DoubleRecordsWF g s ∧ (through = true → ∀ n < g.sievePrimes3, s[n]! = doubleRecord g a n) ∧
    (through = false → skip = true ∧ ∃ n < g.sievePrimes3,
      a % sievingPrime g.pnn n = 0 ∧ g.curve.hasInfinity[g.pnn[n]!]! = false)

private theorem DoubleSetupInvariant.none_of_cons {pref suff : List ℕ} {cur : ℕ}
    {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a pref (cur :: suff) (x, s)) :
    DoubleRecordsWF g s ∧ ∀ n < pref.length, s[n]! = doubleRecord g a n := by
  cases x with
  | none => exact h
  | some r => exact absurd h.1 (List.cons_ne_nil _ _)

private theorem DoubleSetupInvariant.init
    (h : 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0) (l : List ℕ) :
    DoubleSetupInvariant g skip a [] l (none, ssp0) :=
  ⟨h.2.2, by simp⟩

private theorem DoubleSetupInvariant.post_some {l : List ℕ} {x : Option (Array Stype × Bool)}
    {s r : Array Stype} {through : Bool} (h : DoubleSetupInvariant g skip a l [] (x, s))
    (hx : x = some (r, through)) : DoubleSetupPost g skip a r through := by
  subst hx
  obtain ⟨-, hwf, rfl, hskip, hex⟩ := h
  exact ⟨hwf, nofun, fun _ ↦ ⟨hskip, hex⟩⟩

private theorem DoubleSetupInvariant.post_none {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a (ForIn.toList [:g.sievePrimes3]) [] (x, s))
    (hx : x = none) : DoubleSetupPost g skip a s true := by
  subst hx
  obtain ⟨hwf, hs⟩ := h
  refine ⟨hwf, fun _ n hn ↦ hs n (by simpa using hn), nofun⟩

private theorem tmod_sievingPrime {s : Array Stype} (hwf : DoubleRecordsWF g s) (ha : 0 ≤ a)
    {cur : ℕ} (hc : cur < g.sievePrimes3) : a.tmod s[cur]!.p = a % sievingPrime g.pnn cur := by
  rw [hwf.2 cur hc, Int.tmod_eq_emod_of_nonneg ha]

private theorem DoubleSetupInvariant.return_false
    (hpre : 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a pref (cur :: suff) (x, s))
    (h0 : (a.tmod s[cur]!.p == 0) = true)
    (hs : (skip && !g.curve.hasInfinity[g.pnn[cur]!]!) = true) :
    DoubleSetupInvariant g skip a (ForIn.toList [:g.sievePrimes3]) [] (some (s, false), s) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hwf := h.none_of_cons.1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  exact ⟨rfl, hwf, rfl, hs.1, cur, hc, by simpa [tmod_sievingPrime hwf hpre.1 hc] using h0, hs.2⟩

private theorem DoubleSetupInvariant.set
    (hpre : 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a pref (cur :: suff) (x, s)) {r : Stype}
    (hr : r = doubleRecord g a cur) :
    DoubleSetupInvariant g skip a (pref ++ [cur]) suff (none, s.set! cur r) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  obtain ⟨⟨hsize, hp⟩, hs⟩ := h.none_of_cons
  have hcs : cur < s.size := by lia [hpre.2.1]
  refine ⟨⟨by simp [hsize], fun n hn ↦ ?_⟩, fun n hn ↦ ?_⟩
  · rcases eq_or_ne cur n with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _ hcs, hr, doubleRecord]
      split_ifs <;> rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ hne, hp n hn]
  · rcases eq_or_ne cur n with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _ hcs, hr]
    · rw [Array.getElem!_set!_ne _ _ _ _ hne, hs n (by simp at hn; lia)]

private theorem DoubleSetupInvariant.set_zero
    (hpre : 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a pref (cur :: suff) (x, s))
    (h0 : (a.tmod s[cur]!.p == 0) = true) :
    DoubleSetupInvariant g skip a (pref ++ [cur]) suff
      (none, s.set! cur { p := s[cur]!.p, ptr := .hasInfinity g.pnn[cur]! }) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hwf := h.none_of_cons.1
  refine h.set hpre hl ?_
  rw [tmod_sievingPrime hwf hpre.1 hc, beq_iff_eq] at h0
  simp [doubleRecord, h0, hwf.2 cur hc]

private theorem DoubleSetupInvariant.set_inverse
    (hpre : 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:g.sievePrimes3] = pref ++ cur :: suff)
    {x : Option (Array Stype × Bool)} {s : Array Stype}
    (h : DoubleSetupInvariant g skip a pref (cur :: suff) (x, s))
    (h0 : ¬(a.tmod s[cur]!.p == 0) = true) :
    DoubleSetupInvariant g skip a (pref ++ [cur]) suff
      (none, s.set! cur
        { p := s[cur]!.p
          ap := g.tables.inverses[g.pnn[cur]! * maxPrimeEven + (a.tmod s[cur]!.p).toNat]!
          ptr := .isFSquare (g.pnn[cur]! * maxPrimeEven) }) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hwf := h.none_of_cons.1
  refine h.set hpre hl ?_
  rw [tmod_sievingPrime hwf hpre.1 hc] at h0 ⊢
  simp only [beq_iff_eq] at h0
  simp [doubleRecord, h0, hwf.2 cur hc]

end DoubleSetup

attribute [local irreducible] DoubleSetupInvariant in
/-- The loop of `find_double_points` over the sieving primes sets the records of the first
coordinate `a ≥ 0` (`JPoints.doubleRecord`), unless under `skip` it stops at a sieving prime that
divides `a` and modulo which the curve has no points at infinity, and keeps the primes of the
records. -/
@[spec]
theorem findDoublePointsSetup_spec (g : SiftGlobals) (skip : Bool) (ssp0 : Array Stype) (a : ℤ) :
    ⦃ 0 ≤ a ∧ g.sievePrimes3 ≤ numPrimes ∧ DoubleRecordsWF g ssp0 ⦄
    findDoublePointsSetup g skip ssp0 a
    ⦃ fun r ↦ DoubleRecordsWF g r.1 ∧
        (r.2 = true → ∀ n < g.sievePrimes3, r.1[n]! = doubleRecord g a n) ∧
        (r.2 = false → skip = true ∧ ∃ n < g.sievePrimes3,
          a % sievingPrime g.pnn n = 0 ∧ g.curve.hasInfinity[g.pnn[n]!]! = false) ⦄ := by
  vcgen [findDoublePointsSetup] invariants
  · DoubleSetupInvariant g skip a
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact DoubleSetupInvariant.init ‹_› _
    | exact DoubleSetupInvariant.post_some ‹_› ‹_›
    | exact DoubleSetupInvariant.post_none ‹_› ‹_›
    | exact DoubleSetupInvariant.return_false ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSetupInvariant.set_zero ‹_› ‹_› ‹_› ‹_›
    | exact DoubleSetupInvariant.set_inverse ‹_› ‹_› ‹_› ‹_›

/-! ### The soundness of the sieve of the pairs -/

/-- What `find_double_points` reads of the globals `g` of the sieve, as `find_points` sets them up
(`JPoints.IsSieveSetup.doubleSetup`): the globals of the exact check, the inverses of `init_main`,
at most `NUM_PRIMES` sieving primes of the table, and at each of them whether the curve has points
at infinity and which values of `f` are squares, as the references of the tables say. -/
structure DoubleSetup (g : SiftGlobals) : Prop where
  /-- The globals of the exact check. -/
  check : g.check.WF
  /-- The tables of `init_main`. -/
  tables : g.tables.WF
  /-- At most `NUM_PRIMES` sieving primes. -/
  sievePrimes3_le : g.sievePrimes3 ≤ numPrimes
  /-- The sieving primes are primes of the table. -/
  pnn_lt {n : ℕ} (hn : n < g.sievePrimes3) : g.pnn[n]! < numPrimes
  /-- The points at infinity modulo the sieving primes. -/
  hasInfinity {n : ℕ} (hn : n < g.sievePrimes3) :
    g.curve.hasInfinity[g.pnn[n]!]! = refHasInfinity g.check.coeffList (sievingPrime g.pnn n)
  /-- The values of `f` that are squares modulo the sieving primes. -/
  isFSquare {n : ℕ} (hn : n < g.sievePrimes3) {x : ℕ} (hx : x < sievingPrime g.pnn n) :
    g.curve.isFSquare[g.pnn[n]! * maxPrimeEven + x]! =
      refIsFSquare g.check.coeffList (sievingPrime g.pnn n) x

theorem IsSieveSetup.doubleSetup {bg : BandGlobals} {sd : SiftData} (h : IsSieveSetup bg sd) :
    DoubleSetup bg.sift := by
  obtain ⟨g, hg, hs⟩ := h
  have hpn {n : ℕ} (hn : n < bg.sift.sievePrimes3) := hs.pnn_lt hn
  refine ⟨hs.check_eq ▸ hg.check, hs.tables_eq ▸ hg.tables,
    by lia [hs.sievePrimes3_le_numPrimes, hg.input.numPrimes_le],
    fun hn ↦ by lia [hpn hn, hg.input.numPrimes_le], fun hn ↦ ?_, fun hn _ hx ↦ ?_⟩
  · rw [hs.check_eq]
    exact hs.curveTables.hasInfinity (hpn hn)
  · rw [hs.check_eq]
    exact hs.curveTables.isFSquare (hpn hn) hx

section DoubleSetup

variable {g : SiftGlobals} (hg : DoubleSetup g) {a b : ℤ}
include hg

theorem DoubleSetup.prime_sievingPrime {n : ℕ} (hn : n < g.sievePrimes3) :
    (sievingPrime g.pnn n).Prime :=
  prime_getElem!_primeTable (hg.pnn_lt hn)

theorem DoubleSetup.sievingPrime_ne_two {n : ℕ} (hn : n < g.sievePrimes3) :
    sievingPrime g.pnn n ≠ 2 := by
  have := three_le_getElem!_primeTable (hg.pnn_lt hn)
  lia

/-- At a sieving prime that divides the first coordinate `a` of a double point with a point over
it, the curve has points at infinity, so that `find_double_points` skips no such `a`. -/
theorem DoubleSetup.hasInfinity_of_points_ne_nil (ha : 0 < a) (hab : Int.gcd a b = 1)
    (hp : g.check.points (a ^ 2, 2 * a * b, b ^ 2) ≠ []) {n : ℕ} (hn : n < g.sievePrimes3)
    (hd : a % sievingPrime g.pnn n = 0) : g.curve.hasInfinity[g.pnn[n]!]! = true := by
  have : Fact (sievingPrime g.pnn n).Prime := ⟨hg.prime_sievingPrime hn⟩
  rw [hg.hasInfinity hn, refHasInfinity, refIsSquare_eq (hg.sievingPrime_ne_two hn)]
  exact decide_eq_true (isSquare_cast_of_isSquare_sexticForm hab (Int.dvd_of_emod_eq_zero hd)
      (isSquare_sexticForm_of_hasPointOver ha.ne' (hasPointOver_of_pointsOver_ne_nil hp)))

theorem DoubleSetup.inverses_eq {n : ℕ} (hn : n < g.sievePrimes3)
    (hd : ¬a % sievingPrime g.pnn n = 0) :
    g.tables.inverses[g.pnn[n]! * maxPrimeEven + (a % sievingPrime g.pnn n).toNat]! =
      refInverse (sievingPrime g.pnn n) (a % sievingPrime g.pnn n).toNat := by
  have hp0 : (0 : ℤ) < sievingPrime g.pnn n := mod_cast (hg.prime_sievingPrime hn).pos
  exact hg.tables.inverses (hg.pnn_lt hn) (by lia [Int.emod_nonneg a hp0.ne'])
    (by lia [Int.emod_lt_of_pos a hp0])

theorem DoubleSetup.isFSquare_eq {n : ℕ} (hn : n < g.sievePrimes3) (x : ℤ) :
    g.curve.isFSquare[g.pnn[n]! * maxPrimeEven + (x % sievingPrime g.pnn n).toNat]! =
      refIsSquare (sievingPrime g.pnn n)
        (sexticForm (g.check.coeffList.getD · 0) (x % sievingPrime g.pnn n) 1) := by
  have hp0 : (0 : ℤ) < sievingPrime g.pnn n := mod_cast (hg.prime_sievingPrime hn).pos
  rw [hg.isFSquare hn (by lia [Int.emod_lt_of_pos x hp0]), refIsFSquare,
    Int.toNat_of_nonneg (Int.emod_nonneg x hp0.ne')]

/-- At every sieving prime, the record of the first coordinate `a` of a double point with a point
over it passes its second coordinate `b`: `F(b, a)` is a square, so that `f(b / a)` is a square
modulo `p ∤ a`, and for `p ∣ a` the curve has points at infinity modulo `p`. -/
theorem DoubleSetup.passes_of_points_ne_nil (ha : 0 < a) (hab : Int.gcd a b = 1)
    (hp : g.check.points (a ^ 2, 2 * a * b, b ^ 2) ≠ []) {n : ℕ} (hn : n < g.sievePrimes3) :
    (doubleRecord g a n).passes g.curve b = true := by
  have : Fact (sievingPrime g.pnn n).Prime := ⟨hg.prime_sievingPrime hn⟩
  have hsq := isSquare_sexticForm_of_hasPointOver ha.ne' (hasPointOver_of_pointsOver_ne_nil hp)
  rw [doubleRecord]
  split_ifs with hd
  · simp [Stype.passes, TablePtr.read, hg.hasInfinity_of_points_ne_nil ha hab hp hn hd]
  have hps : ¬(sievingPrime g.pnn n : ℤ) ∣ a := fun h ↦ hd (Int.emod_eq_zero_of_dvd h)
  rw [Stype.passes, TablePtr.read, hg.inverses_eq hn hd, hg.isFSquare_eq hn,
    refIsSquare_eq (hg.sievingPrime_ne_two hn)]
  exact decide_eq_true
    (isSquare_cast_sexticForm_of_isSquare_sexticForm hps (cast_mul_refInverse_mul_emod hps b) hsq)

theorem DoubleSetup.pos_and_nonneg_doubleRecord {n : ℕ} (hn : n < g.sievePrimes3) :
    0 < (doubleRecord g a n).p ∧ 0 ≤ (doubleRecord g a n).ap := by
  have hp0 : (0 : ℤ) < sievingPrime g.pnn n := mod_cast (hg.prime_sievingPrime hn).pos
  rw [doubleRecord]
  split_ifs with hd
  · exact ⟨hp0, le_rfl⟩
  · exact ⟨hp0, hg.inverses_eq hn hd ▸ Int.natCast_nonneg _⟩

end DoubleSetup

end JPoints

end
