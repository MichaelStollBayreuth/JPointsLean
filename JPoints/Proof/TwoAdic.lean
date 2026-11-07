/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import Mathlib.Data.ZMod.Basic
public import Std.WP

import JPoints.Proof.Bits
import JPoints.Proof.Containers
import JPoints.Proof.Kummer
import JPoints.Proof.Order
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.Do

/-!
# The condition at 2

The table modulo `64` of `twoadic_init` keeps the classes of the points. A point
`(m a, m b, m c, n)` of the Kummer surface over a triple `(a, b, c)` with `a ≠ 0`, the candidate of
a root `n / m` in lowest terms, has `A₂ = m³ (a³ n + m A₀)` a square: for `m = 2 ^ e u` with `u` odd
and `t = n / u` modulo `64`, the Kummer quadratic cleared of its denominator is
`K₂ t² + 2 ^ e K₁ t + 4 ^ e K₀ = 0` with `t` odd for `e ≥ 1`, and for `e ≤ 1` the square is
`u⁴ (a³ t + A₀)` or `u⁴ 8 (a³ t + 2 A₀)`; for `e ≥ 6` the equation is that of `e = 6`. This is the
condition at 2 modulo `64` (`JPoints.TwoadicCondition`) of the triple (`JPoints.TwoadicAdmissible`,
`JPoints.twoadicAdmissible_of_hasPointOver`), for every curve and every triple, coprime or not.

The contracts of the components of `twoadic_table` modulo `64` say what their tables hold where the
test of a triple reads them: the squares (`JPoints.twoadicSquares_spec`), the solutions of the
quadratic equations (`JPoints.twoadicSol_spec`), the coefficients of the curve and of the quartic
`K₀` modulo `64` (`JPoints.twoadicCoeffs_spec`), the powers of the residues
(`JPoints.twoadicPowers_spec`) and the value of the quartic (`JPoints.twoadicK0_spec`). The test of
a triple of residues admits it when the condition at 2 holds (`JPoints.twoadicAdmits_spec`,
`JPoints.twoadicCell_spec`), so that the row of a class (`JPoints.twoadicRow_spec`), the classes
(`JPoints.twoadicClasses_spec`) and the table (`JPoints.twoadicTable_spec`) keep every class not
all even at which it holds (`JPoints.IsTwoadicTable`): the condition at 2 that the sieve uses
admits every point (`JPoints.TwoAdic.sound_of_isTwoadicTable`).

## Main definitions

* `JPoints.TwoadicCondition`, `JPoints.TwoadicAdmissible`: the condition at 2 modulo `64` on the
  residues of the Kummer quadratic and of `a³` and `A₀`, and on a triple.
* `JPoints.KummerCoeffs.coeff`: the coefficients of the quartic `K₀` by their exponents.
* `JPoints.IsTwoadicLookup`, `JPoints.IsTwoadicResidues`: the tables that the test of a triple
  reads.
* `JPoints.TwoadicTestOdd`, `JPoints.TwoadicTestTwo`, `JPoints.TwoadicTestPow`: the tests of
  `twoadic_table` for an odd denominator, for one `2` modulo `4` and for one divisible by `2 ^ e`.
* `JPoints.IsTwoadicTable`: the words and the flags of the classes keep the classes of the
  condition at 2.
* `JPoints.TwoadicSquaresInvariant`, `JPoints.TwoadicSolInvariant`,
  `JPoints.TwoadicCoeffsInvariant`, `JPoints.TwoadicPowersInvariant`, `JPoints.TwoadicK0Invariant`,
  `JPoints.TwoadicAdmitsInvariant`, `JPoints.TwoadicRowInvariant`,
  `JPoints.TwoadicClassesInvariant`, `JPoints.TwoadicOddInvariant`: the invariants of the loops.

## Main statements

* `JPoints.twoadicAdmissible_of_hasPointOver`: the condition at 2 holds at a triple with `a ≠ 0`
  over which a point lies.
* `JPoints.twoadicSquares_spec`, `JPoints.twoadicSol_spec`, `JPoints.twoadicCoeffs_spec`,
  `JPoints.twoadicPowers_spec`, `JPoints.twoadicK0_spec`, `JPoints.twoadicAdmits_spec`,
  `JPoints.twoadicCell_spec`, `JPoints.twoadicRow_spec`, `JPoints.twoadicClasses_spec`,
  `JPoints.twoadicTable_spec`: the contracts of the components of `twoadic_table`.
* `JPoints.TwoAdic.sound_of_isTwoadicTable`: tables that keep the classes of the condition at 2
  admit every point.
* `JPoints.TwoAdic.sound_of_use2_eq_false`, `JPoints.TwoAdic.sound_initial`: the condition at 2
  that the sieve does not use admits every point.

## Implementation notes

The contracts are on the modulus `64`, which the sieve uses; the table modulo `16` only decides
whether the sieve uses the condition, and `JPoints.twoadicInit_spec` needs nothing of it. The loop
of `JPoints.twoadicRow` that repeats the word of a modulus below `64` is never entered. The
contracts that a caller with computed arguments uses take the facts on them as preconditions,
those of the components that their callers pass on (the tables, the powers) as hypotheses outside
the triple; a private form with these hypotheses outside the triple is the one that `vcgen` proves.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### Residues modulo `64` -/

private theorem intCast_emod_sixtyFour (x : ℤ) : ((x % 64 : ℤ) : ZMod 64) = x :=
  ZMod.intCast_mod x 64

/- The residue modulo `64` lies in `[0, 64)`. -/
private theorem emod_sixtyFour_bounds (x : ℤ) : 0 ≤ x % 64 ∧ x % 64 < 64 :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

/-! ### The condition at 2 modulo `64` -/

/-- The condition at 2 modulo `64` that `twoadic_table` tests on a triple, for the coefficients
`k2`, `k1`, `k0` of its Kummer quadratic and the values `a3 = a³` and `A0 = A₀` modulo `64`: a root
`d` of the quadratic at which `a³ d + A₀` is a square (the points `(v a, v b, v c, u)` with `v`
odd); or an odd `t` with `k₂ t² + 2 k₁ t + 4 k₀ = 0` and `8 (a³ t + 2 A₀)` a square (`v ≡ 2` modulo
`4`); or, for some `2 ≤ e ≤ 6`, an odd `t` with `k₂ t² + 2 ^ e k₁ t + 4 ^ e k₀ = 0` (`v = 2 ^ e u`
with `u` odd for `e < 6`, `v` divisible by `2 ^ 6` for `e = 6`). -/
def TwoadicCondition (k2 k1 k0 a3 A0 : ZMod 64) : Prop :=
  (∃ d, k2 * d ^ 2 + k1 * d + k0 = 0 ∧ IsSquare (a3 * d + A0)) ∨
    (∃ t : ZMod 64, t.val % 2 = 1 ∧ k2 * t ^ 2 + 2 * k1 * t + 4 * k0 = 0 ∧
      IsSquare (8 * (a3 * t + 2 * A0))) ∨
    ∃ e, 2 ≤ e ∧ e ≤ 6 ∧
      ∃ t : ZMod 64, t.val % 2 = 1 ∧ k2 * t ^ 2 + 2 ^ e * k1 * t + 4 ^ e * k0 = 0

/-- The triple `(a, b, c)` satisfies the condition at 2 modulo `64` (`JPoints.TwoadicCondition`) for
the coefficients `f 0, …, f 6`: that of the coefficients `K₂`, `K₁`, `K₀` of the Kummer quadratic
over it, of `a³` and of `A₀ = JPoints.auxA2 f a b c 0`, so that `A₂ = a³ d + A₀`. -/
def TwoadicAdmissible (f : ℕ → ℤ) (a b c : ℤ) : Prop :=
  TwoadicCondition (kummerK2 a b c) (kummerK1 f a b c) (kummerK0 f a b c) (a ^ 3) (auxA2 f a b c 0)

theorem twoadicAdmissible_congr {f : ℕ → ℤ} {a b c a' b' c' : ℤ} (ha : (a : ZMod 64) = a')
    (hb : (b : ZMod 64) = b') (hc : (c : ZMod 64) = c') :
    TwoadicAdmissible f a b c ↔ TwoadicAdmissible f a' b' c' := by
  simp only [TwoadicAdmissible]
  push_cast [kummerK2, kummerK1, kummerK0, auxA2, ha, hb, hc]
  rfl

/-- The Kummer quadratic `K₂ d² + K₁ d + K₀` at `d = n / m` for `m = 2 ^ e u` with a unit `u`,
cleared of the denominator: `K₂ t² + 2 ^ e K₁ t + 4 ^ e K₀ = 0` for `t = n / u`. -/
theorem add_two_pow_mul_add_four_pow_mul_eq_zero {R : Type*} [CommRing R] {k2 k1 k0 t u v : R}
    (e : ℕ) (huv : u * v = 1)
    (h : k2 * (t * u) ^ 2 + k1 * (2 ^ e * u * (t * u)) + k0 * (2 ^ e * u) ^ 2 = 0) :
    k2 * t ^ 2 + 2 ^ e * k1 * t + 4 ^ e * k0 = 0 := by
  rw [show (4 : R) ^ e = (2 ^ e) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  linear_combination
    v ^ 2 * h - (k2 * t ^ 2 + 2 ^ e * k1 * t + (2 ^ e) ^ 2 * k0) * (u * v + 1) * huv

theorem isSquare_of_sq_eq_pow_four_mul {R : Type*} [CommRing R] {u v s x : R} (huv : u * v = 1)
    (h : s ^ 2 = u ^ 4 * x) : IsSquare x :=
  ⟨s * v ^ 2, by linear_combination -v ^ 4 * h - x * (1 + u * v) * (1 + u ^ 2 * v ^ 2) * huv⟩

theorem val_mod_two_eq_one_of_mul {t u : ZMod 64} (h : (t * u).val % 2 = 1) : t.val % 2 = 1 := by
  rw [ZMod.val_mul, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 64)] at h
  exact Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 h)).1

private theorem two_pow_eq_two_pow_six {e : ℕ} (he : 6 ≤ e) : (2 : ZMod 64) ^ e = 2 ^ 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, show (2 : ZMod 64) ^ 6 = 0 by decide, zero_mul]

private theorem four_pow_eq_four_pow_six {e : ℕ} (he : 6 ≤ e) : (4 : ZMod 64) ^ e = 4 ^ 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, show (4 : ZMod 64) ^ 6 = 0 by decide, zero_mul]

/-- An odd integer `n = t u` modulo `64` makes `t` odd. -/
theorem val_mod_two_eq_one_of_intCast_eq_mul {n : ℤ} {t u : ZMod 64} (hn : (n : ZMod 64) = t * u)
    (h : n % 2 = 1) : t.val % 2 = 1 := by
  refine val_mod_two_eq_one_of_mul (u := u) ?_
  rw [← hn]
  lia [ZMod.val_intCast (n := 64) n]

/-- The condition at 2 of a root `n / m` of a Kummer quadratic modulo `64`, for `m = 2 ^ e u` with
a unit `u` and `n = t u`, at which `A₂ = m³ (a³ n + m A₀)` is a square: the quadratic cleared of its
denominator, and for `e ≤ 1` the square `u⁴ (a³ t + A₀)` or `u⁴ 8 (a³ t + 2 A₀)`
(`JPoints.isSquare_of_sq_eq_pow_four_mul`); `e ≥ 6` gives the case `e = 6`. -/
theorem twoadicCondition_of_sq_eq {k2 k1 k0 a3 A0 t u v s : ZMod 64} {e : ℕ} (huv : u * v = 1)
    (hodd : 1 ≤ e → t.val % 2 = 1) (hq : k2 * t ^ 2 + 2 ^ e * k1 * t + 4 ^ e * k0 = 0)
    (hs : (2 ^ e * u) ^ 3 * (a3 * (t * u) + 2 ^ e * u * A0) = s * s) :
    TwoadicCondition k2 k1 k0 a3 A0 := by
  rcases Nat.lt_or_ge e 2 with he | he
  · interval_cases e
    · refine .inl ⟨t, by simpa using hq, isSquare_of_sq_eq_pow_four_mul huv (s := s) ?_⟩
      linear_combination -hs
    · refine .inr (.inl ⟨t, hodd le_rfl, by simpa using hq,
        isSquare_of_sq_eq_pow_four_mul huv (s := s) ?_⟩)
      linear_combination -hs
  · refine .inr (.inr ⟨min e 6, by lia, by lia, t, hodd (by lia), ?_⟩)
    rcases le_or_gt e 6 with h6 | h6
    · rwa [min_eq_left h6]
    · rwa [min_eq_right h6.le, ← two_pow_eq_two_pow_six h6.le, ← four_pow_eq_four_pow_six h6.le]

/-- The condition at 2 of a point `(m a, m b, m c, n)` of the Kummer surface with `n / m` in
lowest terms, `m ≠ 0`, at which `A₂ = m³ (a³ n + m A₀)` is a square: for `m = 2 ^ e u` with `u`
odd and `t = n / u` modulo `64`, the Kummer quadratic cleared of its denominator
(`JPoints.add_two_pow_mul_add_four_pow_mul_eq_zero`), and `t` odd for `e ≥ 1`, as `n` is
(`JPoints.twoadicCondition_of_sq_eq`). -/
theorem twoadicAdmissible_of_isSquare {f : ℕ → ℤ} {a b c n : ℤ} {m : ℕ} (hm : m ≠ 0)
    (hmn : n.natAbs.Coprime m)
    (hK : kummerK2 a b c * n ^ 2 + kummerK1 f a b c * (m * n) + kummerK0 f a b c * m ^ 2 = 0)
    (hA : IsSquare ((m : ℤ) ^ 3 * (a ^ 3 * n + m * auxA2 f a b c 0))) :
    TwoadicAdmissible f a b c := by
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  obtain ⟨s, hs⟩ := hA
  have huv := ZMod.coe_mul_inv_eq_one (n := 64) m'
    (Nat.Coprime.pow_right 6 (Nat.coprime_two_right.2 hm'))
  set u : ZMod 64 := (m' : ZMod 64)
  set t : ZMod 64 := n * u⁻¹
  have hn : (n : ZMod 64) = t * u := by rw [mul_assoc, mul_comm u⁻¹, huv, mul_one]
  have hK' := congr(((↑) : ℤ → ZMod 64) $hK)
  have hs' := congr(((↑) : ℤ → ZMod 64) $hs)
  push_cast [hn] at hK' hs'
  refine twoadicCondition_of_sq_eq huv (fun he ↦ val_mod_two_eq_one_of_intCast_eq_mul hn ?_)
    (add_two_pow_mul_add_four_pow_mul_eq_zero e huv hK') hs'
  exact Int.odd_iff.1 (Int.natAbs_odd.1 (Nat.coprime_two_right.1
    (hmn.coprime_dvd_right ((dvd_pow_self 2 (by lia : e ≠ 0)).mul_right m'))))

/-- The condition at 2 keeps the classes modulo `64` of the triples `(a, b, c)` with `a ≠ 0` over
which a point lies (`JPoints.twoadicAdmissible_of_isSquare`): the candidate `(m a, m b, m c, n)` of
a root `n / m` of the Kummer quadratic, with `A₂` a square since `m a ≠ 0`. Neither the degree nor
the squarefreeness of the curve is needed. -/
theorem twoadicAdmissible_of_hasPointOver {cs : List ℤ} {a b c : ℤ} (ha : a ≠ 0)
    (h : HasPointOver cs (a, b, c)) : TwoadicAdmissible (cs.getD · 0) a b c := by
  obtain ⟨P, hP, hL⟩ := h
  have hK := kummer_eq_zero_of_mem_kummerPoints hP
  obtain ⟨x, -, rfl⟩ := mem_kummerPoints_iff.1 hP
  have hd : (x.den : ℤ) ≠ 0 := by positivity
  refine twoadicAdmissible_of_isSquare x.den_ne_zero x.reduced
    ((kummer_mul_mul_mul_eq_zero_iff hd a b c x.num).mp hK) ?_
  · rw [← auxA2_mul_mul_mul]
    simp only [Lifts, mul_eq_zero, hd, ha, or_self, ↓reduceIte] at hL
    exact hL.1

/-! ### The squares -/

/-- The invariant of the loops of `JPoints.twoadicSquares` for the modulus `m`: the `64` entries of
the table, with the squares `i * i % m` of the `i < n` set. -/
def TwoadicSquaresInvariant (m n : ℕ) (sq : Array Bool) : Prop :=
  sq.size = 64 ∧ ∀ i < n, sq[i * i % m]! = true

theorem twoadicSquaresInvariant_replicate (m : ℕ) :
    TwoadicSquaresInvariant m 0 (.replicate 64 false) :=
  ⟨Array.size_replicate .., fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem TwoadicSquaresInvariant.set!_zero {m : ℕ} {sq : Array Bool}
    (h : TwoadicSquaresInvariant m 0 sq) (i : ℕ) (x : Bool) :
    TwoadicSquaresInvariant m 0 (sq.set! i x) :=
  ⟨(Array.size_set! ..).trans h.1, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem TwoadicSquaresInvariant.nil {m : ℕ} {sq : Array Bool}
    (h : TwoadicSquaresInvariant m 0 sq) : TwoadicSquaresInvariant m ([] : List ℕ).length sq :=
  h

theorem TwoadicSquaresInvariant.set! {m : ℕ} (hm : m ≤ 64) {sq : Array Bool} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [0:m] = pref ++ cur :: suff)
    (h : TwoadicSquaresInvariant m pref.length sq) :
    TwoadicSquaresInvariant m (pref ++ [cur]).length (sq.set! (cur * cur % m) true) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcm := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  refine ⟨(Array.size_set! ..).trans h.1, fun i hi ↦ ?_⟩
  rw [Array.getElem!_set! (by rw [h.1]; lia [Nat.mod_lt (i * i) (by lia : 0 < m)])]
  split_ifs with hii
  · rfl
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa [hc] using hi)) with hi | rfl
    · exact h.2 i (by rw [hc]; lia)
    · exact absurd rfl hii

theorem TwoadicSquaresInvariant.getElem! {m : ℕ} {sq : Array Bool}
    (h : TwoadicSquaresInvariant m (ForIn.toList [0:m]).length sq) {i : ℕ} (hi : i < m) :
    sq[i * i % m]! = true :=
  h.2 i (by simpa using hi)

attribute [local irreducible] TwoadicSquaresInvariant in
/-- The table of the squares modulo `m ≤ 64` of `JPoints.twoadicSquares` has the entries of the
squares set. -/
@[spec]
theorem twoadicSquares_spec (m : ℕ) :
    ⦃ m ≤ 64 ⦄ twoadicSquares m ⦃ fun sq ↦ ∀ i < m, sq[i * i % m]! = true ⦄ := by
  vcgen [twoadicSquares] invariants
  · fun _ _ sq ↦ TwoadicSquaresInvariant m 0 sq
  · fun pref _ sq ↦ TwoadicSquaresInvariant m pref.length sq
  all_goals with_reducible first
    | exact twoadicSquaresInvariant_replicate m
    | exact TwoadicSquaresInvariant.nil ‹_›
    | exact TwoadicSquaresInvariant.set!_zero ‹_› _ _
    | exact TwoadicSquaresInvariant.set! ‹_› ‹_› ‹_›
    | exact TwoadicSquaresInvariant.getElem! ‹_› ‹_›

/-! ### The solutions of the quadratic equations -/

/-- The invariant of the loops of `JPoints.twoadicSol` for the modulus `m`: the `m³` words of the
table, and for the triples `(k₂, k₁, d) < (K₂, K₁, D)` in lexicographic order run through, bit `d`
of the word of `(k₂, k₁, k₀)` set for the `k₀` with `k₂ d² + k₁ d + k₀ ≡ 0`. -/
def TwoadicSolInvariant (m K2 K1 D : ℕ) (sol : Array UInt64) : Prop :=
  sol.size = m * m * m ∧ ∀ k2 < m, ∀ k1 < m, ∀ k0 < m, ∀ d < m,
    (k2 < K2 ∨ k2 = K2 ∧ (k1 < K1 ∨ k1 = K1 ∧ d < D)) → (k2 * d * d + k1 * d + k0) % m = 0 →
      sol[(k2 * m + k1) * m + k0]!.toBitVec.getLsbD d = true

theorem TwoadicSolInvariant.mono {m K2 K1 D K2' K1' D' : ℕ} {sol : Array UInt64}
    (h : TwoadicSolInvariant m K2 K1 D sol)
    (hl : ∀ k2 k1 d, k1 < m → d < m → (k2 < K2' ∨ k2 = K2' ∧ (k1 < K1' ∨ k1 = K1' ∧ d < D')) →
      k2 < K2 ∨ k2 = K2 ∧ (k1 < K1 ∨ k1 = K1 ∧ d < D)) :
    TwoadicSolInvariant m K2' K1' D' sol :=
  ⟨h.1, fun k2 hk2 k1 hk1 k0 hk0 d hd hlt ↦
    h.2 k2 hk2 k1 hk1 k0 hk0 d hd (hl k2 k1 d hk1 hd hlt)⟩

theorem twoadicSolInvariant_replicate (m : ℕ) :
    TwoadicSolInvariant m ([] : List ℕ).length 0 0 (.replicate (m * m * m) 0) :=
  ⟨Array.size_replicate .., fun _ _ _ _ _ _ _ _ h ↦ by simp at h⟩

theorem TwoadicSolInvariant.start_k1 {m : ℕ} {pref suff : List ℕ} {cur : ℕ} {sol : Array UInt64}
    (hl : ForIn.toList [0:m] = pref ++ cur :: suff)
    (h : TwoadicSolInvariant m pref.length 0 0 sol) :
    TwoadicSolInvariant m cur ([] : List ℕ).length 0 sol :=
  h.mono fun _ _ _ _ _ ↦ by
    simp only [List.length_nil]
    lia [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

theorem TwoadicSolInvariant.start_d {m k2 : ℕ} {pref suff : List ℕ} {cur : ℕ} {sol : Array UInt64}
    (hl : ForIn.toList [0:m] = pref ++ cur :: suff)
    (h : TwoadicSolInvariant m k2 pref.length 0 sol) :
    TwoadicSolInvariant m k2 cur ([] : List ℕ).length sol :=
  h.mono fun _ _ _ _ _ ↦ by
    simp only [List.length_nil]
    lia [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

theorem TwoadicSolInvariant.next_k1 {m k2 : ℕ} {pref suff : List ℕ} {cur : ℕ} {sol : Array UInt64}
    (hl : ForIn.toList [0:m] = pref ++ cur :: suff)
    (h : TwoadicSolInvariant m k2 cur (ForIn.toList [0:m]).length sol) :
    TwoadicSolInvariant m k2 (pref ++ [cur]).length 0 sol :=
  h.mono fun _ _ _ _ _ ↦ by
    simp only [List.length_append, List.length_singleton, Std.Legacy.Range.length_toList]
    lia [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

theorem TwoadicSolInvariant.next_k2 {m : ℕ} {pref suff : List ℕ} {cur : ℕ} {sol : Array UInt64}
    (hl : ForIn.toList [0:m] = pref ++ cur :: suff)
    (h : TwoadicSolInvariant m cur (ForIn.toList [0:m]).length 0 sol) :
    TwoadicSolInvariant m (pref ++ [cur]).length 0 0 sol :=
  h.mono fun _ _ _ _ _ ↦ by
    simp only [List.length_append, List.length_singleton, Std.Legacy.Range.length_toList]
    lia [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

theorem TwoadicSolInvariant.set! {m k2 k1 : ℕ} (hm : m ≤ 64) {pref suff : List ℕ} {d : ℕ}
    {sol : Array UInt64} (hl : ForIn.toList [0:m] = pref ++ d :: suff) (hk2 : k2 < m)
    (hk1 : k1 < m) (h : TwoadicSolInvariant m k2 k1 pref.length sol) :
    TwoadicSolInvariant m k2 k1 (pref ++ [d]).length
      (sol.set! ((k2 * m + k1) * m + (m - (k2 * d * d + k1 * d) % m) % m)
        (sol[(k2 * m + k1) * m + (m - (k2 * d * d + k1 * d) % m) % m]! |||
          1 <<< UInt64.ofNat d)) := by
  have hd := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hdm := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  refine ⟨(Array.size_set! ..).trans h.1, fun k2' hk2' k1' hk1' k0 hk0 d' hd' hlt hq ↦ ?_⟩
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases he : k2' = k2 ∧ k1' = k1 ∧ d' = d
  · obtain ⟨rfl, rfl, rfl⟩ := he
    rw [Nat.sub_mod_mod_eq_of_add_mod_eq_zero hk0 hq]
    refine Array.getLsbD_getElem!_set!_or_one_shiftLeft ?_ (by lia)
    rw [h.1]
    exact Nat.mul_add_mul_add_lt hk2' hk1' hk0
  · exact Array.getLsbD_getElem!_set!_or (h.2 k2' hk2' k1' hk1' k0 hk0 d' hd' (by lia) hq) _ _

theorem TwoadicSolInvariant.getLsbD {m : ℕ} {sol : Array UInt64}
    (h : TwoadicSolInvariant m (ForIn.toList [0:m]).length 0 0 sol) {k2 k1 k0 d : ℕ}
    (hk2 : k2 < m) (hk1 : k1 < m) (hk0 : k0 < m) (hd : d < m)
    (hq : (k2 * d * d + k1 * d + k0) % m = 0) :
    sol[(k2 * m + k1) * m + k0]!.toBitVec.getLsbD d = true :=
  h.2 k2 hk2 k1 hk1 k0 hk0 d hd (.inl (by simpa using hk2)) hq

attribute [local irreducible] TwoadicSolInvariant in
/-- The table `sol` of `JPoints.twoadicSol` for the modulus `m ≤ 64`: bit `d` of the word of
`(k₂, k₁, k₀)` is set for the solutions `d` of `k₂ d² + k₁ d + k₀ ≡ 0 (mod m)`. -/
@[spec]
theorem twoadicSol_spec (m : ℕ) :
    ⦃ m ≤ 64 ⦄ twoadicSol m
    ⦃ fun sol ↦ ∀ k2 < m, ∀ k1 < m, ∀ k0 < m, ∀ d < m, (k2 * d * d + k1 * d + k0) % m = 0 →
        sol[(k2 * m + k1) * m + k0]!.toBitVec.getLsbD d = true ⦄ := by
  vcgen [twoadicSol] invariants
  | inv1 => fun pref _ sol ↦ TwoadicSolInvariant m pref.length 0 0 sol
  | inv2 _ k2 _ _ _ _ => fun pref _ sol ↦ TwoadicSolInvariant m k2 pref.length 0 sol
  | inv3 _ k2 _ _ _ _ _ k1 _ _ _ _ => fun pref _ sol ↦ TwoadicSolInvariant m k2 k1 pref.length sol
  all_goals with_reducible first
    | exact twoadicSolInvariant_replicate m
    | exact TwoadicSolInvariant.start_k1 ‹_› ‹_›
    | exact TwoadicSolInvariant.start_d ‹_› ‹_›
    | exact TwoadicSolInvariant.set! ‹_› ‹_› (Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›)
        (Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›) ‹_›
    | exact TwoadicSolInvariant.next_k1 ‹_› ‹_›
    | exact TwoadicSolInvariant.next_k2 ‹_› ‹_›
    | exact TwoadicSolInvariant.getLsbD ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

/-! ### The coefficients modulo `m` -/

/-- The coefficient `k_{i j l}` of `aⁱ bʲ cˡ`, `l = 4 - i - j`, of the quartic `K₀` among the
coefficients `k`, and `0` for `i + j > 4`. -/
def KummerCoeffs.coeff (k : KummerCoeffs) : ℕ → ℕ → ℤ
  | 4, 0 => k.k400 | 3, 1 => k.k310 | 3, 0 => k.k301 | 2, 2 => k.k220 | 2, 1 => k.k211
  | 2, 0 => k.k202 | 1, 3 => k.k130 | 1, 2 => k.k121 | 1, 1 => k.k112 | 1, 0 => k.k103
  | 0, 4 => k.k040 | 0, 3 => k.k031 | 0, 2 => k.k022 | 0, 1 => k.k013 | 0, 0 => k.k004
  | _, _ => 0

theorem getElem!_snd_run_twoadicCoeffs (coeffs : Array ℤ) (k : KummerCoeffs) (m : ℕ) {i j : ℕ}
    (h : i + j ≤ 4) :
    (twoadicCoeffs coeffs k m).run.2[(i * 5 + j) * 5 + (4 - i - j)]! = k.coeff i j % m := by
  have hi : i ≤ 4 := by lia
  have hj : j ≤ 4 - i := by lia
  interval_cases i <;> interval_cases j <;> simp [twoadicCoeffs, KummerCoeffs.coeff]

/-- The invariant of the loop of `JPoints.twoadicCoeffs` that reduces the coefficients of the curve
modulo `m`: the seven entries of `fm`, those below `n` the residues. -/
def TwoadicCoeffsInvariant (coeffs : Array ℤ) (m n : ℕ) (fm : Array ℤ) : Prop :=
  fm.size = 7 ∧ ∀ i < n, fm[i]! = coeffs[i]! % (m : ℤ)

theorem twoadicCoeffsInvariant_replicate (coeffs : Array ℤ) (m : ℕ) :
    TwoadicCoeffsInvariant coeffs m ([] : List ℕ).length (.replicate 7 0) :=
  ⟨Array.size_replicate .., fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem TwoadicCoeffsInvariant.set! {coeffs : Array ℤ} {m : ℕ} {fm : Array ℤ}
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [0:7] = pref ++ cur :: suff)
    (h : TwoadicCoeffsInvariant coeffs m pref.length fm) :
    TwoadicCoeffsInvariant coeffs m (pref ++ [cur]).length (fm.set! cur (coeffs[cur]! % m)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hc7 := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  refine ⟨(Array.size_set! ..).trans h.1, fun i hi ↦ ?_⟩
  rw [Array.getElem!_set! (by rw [h.1]; simp at hi; lia)]
  split_ifs with hii
  · rw [hii]
  · exact h.2 i (by simp at hi; lia)

theorem TwoadicCoeffsInvariant.getElem! {coeffs : Array ℤ} {m : ℕ} {fm : Array ℤ}
    (h : TwoadicCoeffsInvariant coeffs m (ForIn.toList [0:7]).length fm) {i : ℕ} (hi : i < 7) :
    fm[i]! = coeffs[i]! % m :=
  h.2 i (by simpa using hi)

attribute [local irreducible] TwoadicCoeffsInvariant in
/-- The coefficients `fm` of the curve and `km` of the quartic `K₀` modulo `m` of
`JPoints.twoadicCoeffs`, `km` at `(i * 5 + j) * 5 + (4 - i - j)` the coefficient of
`aⁱ bʲ c⁴⁻ⁱ⁻ʲ` (`JPoints.KummerCoeffs.coeff`). -/
@[spec]
theorem twoadicCoeffs_spec (coeffs : Array ℤ) (k : KummerCoeffs) (m : ℕ) :
    ⦃ True ⦄ twoadicCoeffs coeffs k m
    ⦃ fun r ↦ (∀ i < 7, r.1[i]! = coeffs[i]! % (m : ℤ)) ∧
        ∀ i j, i + j ≤ 4 → r.2[(i * 5 + j) * 5 + (4 - i - j)]! = k.coeff i j % m ⦄ := by
  vcgen [twoadicCoeffs] invariants
  · fun pref _ fm ↦ TwoadicCoeffsInvariant coeffs m pref.length fm
  all_goals first
    | exact twoadicCoeffsInvariant_replicate coeffs m
    | exact TwoadicCoeffsInvariant.set! ‹_› ‹_›
    | exact ⟨fun _ ↦ TwoadicCoeffsInvariant.getElem! ‹_›,
        fun _ _ ↦ getElem!_snd_run_twoadicCoeffs coeffs k m⟩

/-! ### The powers -/

/-- The invariant of the loop of `JPoints.twoadicPowers` for the residue `x` modulo `m`: the five
entries of `xp`, those below `n` the powers of `x` modulo `m`. -/
def TwoadicPowersInvariant (x m n : ℕ) (xp : Array ℤ) : Prop :=
  xp.size = 5 ∧ ∀ i < n, ((xp[i]! : ℤ) : ZMod m) = (x : ZMod m) ^ i

theorem twoadicPowersInvariant_set!_zero (x m : ℕ) :
    TwoadicPowersInvariant x m (([] : List ℕ).length + 1) ((Array.replicate 5 0).set! 0 1) := by
  refine ⟨by simp, fun i hi ↦ ?_⟩
  obtain rfl : i = 0 := by simpa using hi
  simp

theorem TwoadicPowersInvariant.set! {x m : ℕ} {xp : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [1:5] = pref ++ cur :: suff)
    (h : TwoadicPowersInvariant x m (pref.length + 1) xp) :
    TwoadicPowersInvariant x m ((pref ++ [cur]).length + 1)
      (xp.set! cur (xp[cur - 1]! * x % m)) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hc5 := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  refine ⟨(Array.size_set! ..).trans h.1, fun i hi ↦ ?_⟩
  rw [Array.getElem!_set! (by rw [h.1]; simp at hi; lia)]
  split_ifs with hii
  · push_cast [ZMod.intCast_mod]
    rw [h.2 (cur - 1) (by lia), ← pow_succ, ← hii, Nat.sub_add_cancel (by lia)]
  · exact h.2 i (by simp at hi; lia)

theorem TwoadicPowersInvariant.getElem! {x m : ℕ} {xp : Array ℤ}
    (h : TwoadicPowersInvariant x m ((ForIn.toList [1:5]).length + 1) xp) {i : ℕ} (hi : i < 5) :
    ((xp[i]! : ℤ) : ZMod m) = (x : ZMod m) ^ i :=
  h.2 i (by simpa using hi)

attribute [local irreducible] TwoadicPowersInvariant in
/-- The powers `x⁰, …, x⁴` of the residue `x` of `JPoints.twoadicPowers`, modulo `m`. -/
@[spec]
theorem twoadicPowers_spec (x m : ℕ) :
    ⦃ True ⦄ twoadicPowers x m
    ⦃ fun xp ↦ ∀ i < 5, ((xp[i]! : ℤ) : ZMod m) = (x : ZMod m) ^ i ⦄ := by
  vcgen [twoadicPowers] invariants
  · fun pref _ xp ↦ TwoadicPowersInvariant x m (pref.length + 1) xp
  all_goals with_reducible first
    | exact twoadicPowersInvariant_set!_zero x m
    | exact TwoadicPowersInvariant.set! ‹_› ‹_›
    | exact TwoadicPowersInvariant.getElem! ‹_› ‹_›

/-! ### The value of the quartic -/

/-- The invariant of the loops of `JPoints.twoadicK0` for the coefficients `km` modulo `m` and the
powers `ap`, `bp`, `cp`: the value `k0` reduced into `[0, m)`, and modulo `m` the sum of the terms
`km[i][j][4 - i - j] aⁱ bʲ c⁴⁻ⁱ⁻ʲ` for `i < I` and `j < 5 - i`, and for `i = I` and `j < J`. -/
def TwoadicK0Invariant (km ap bp cp : Array ℤ) (m I J : ℕ) (k0 : ℤ) : Prop :=
  0 ≤ k0 ∧ k0 < m ∧ (k0 : ZMod m) =
    ((∑ i ∈ Finset.range I, ∑ j ∈ Finset.range (5 - i),
        km[(i * 5 + j) * 5 + (4 - i - j)]! * ap[i]! * bp[j]! * cp[4 - i - j]! +
      ∑ j ∈ Finset.range J, km[(I * 5 + j) * 5 + (4 - I - j)]! * ap[I]! * bp[j]! *
        cp[4 - I - j]! : ℤ) : ZMod m)

theorem twoadicK0Invariant_zero (km ap bp cp : Array ℤ) {m : ℕ} (hm : 0 < m) :
    TwoadicK0Invariant km ap bp cp m ([] : List ℕ).length 0 0 :=
  ⟨le_rfl, by lia, by simp⟩

theorem TwoadicK0Invariant.start {km ap bp cp : Array ℤ} {m : ℕ} {pref suff : List ℕ} {cur : ℕ}
    {k0 : ℤ} (hl : ForIn.toList [0:5] = pref ++ cur :: suff)
    (h : TwoadicK0Invariant km ap bp cp m pref.length 0 k0) :
    TwoadicK0Invariant km ap bp cp m cur ([] : List ℕ).length k0 := by
  rw [← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  exact h

theorem TwoadicK0Invariant.add {km ap bp cp : Array ℤ} {m I : ℕ} {pref suff : List ℕ} {cur : ℕ}
    {k0 : ℤ} (hl : ForIn.toList [0:5 - I] = pref ++ cur :: suff)
    (h : TwoadicK0Invariant km ap bp cp m I pref.length k0) :
    TwoadicK0Invariant km ap bp cp m I (pref ++ [cur]).length
      ((k0 + km[(I * 5 + cur) * 5 + (4 - I - cur)]! * ap[I]! * bp[cur]! * cp[4 - I - cur]!) %
        m) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨Int.emod_nonneg _ (by lia [h.1, h.2.1]), Int.emod_lt_of_pos _ (by lia [h.1, h.2.1]), ?_⟩
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ, hc]
  push_cast [ZMod.intCast_mod, h.2.2, ← hc]
  ring

theorem TwoadicK0Invariant.next {km ap bp cp : Array ℤ} {m : ℕ} {pref suff : List ℕ} {cur : ℕ}
    {k0 : ℤ} (hl : ForIn.toList [0:5] = pref ++ cur :: suff)
    (h : TwoadicK0Invariant km ap bp cp m cur (ForIn.toList [0:5 - cur]).length k0) :
    TwoadicK0Invariant km ap bp cp m (pref ++ [cur]).length 0 k0 := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2, List.length_append, List.length_singleton, Finset.sum_range_succ, hc,
    Std.Legacy.Range.length_toList_zero_start]
  simp

theorem TwoadicK0Invariant.eq {km ap bp cp : Array ℤ} {m : ℕ} {k0 : ℤ}
    (h : TwoadicK0Invariant km ap bp cp m (ForIn.toList [0:5]).length 0 k0) :
    0 ≤ k0 ∧ k0 < m ∧ (k0 : ZMod m) = ((∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (5 - i),
      km[(i * 5 + j) * 5 + (4 - i - j)]! * ap[i]! * bp[j]! * cp[4 - i - j]! : ℤ) : ZMod m) := by
  simpa [TwoadicK0Invariant] using h

attribute [local irreducible] TwoadicK0Invariant in
/-- The value `k₀` of the quartic `K₀` of `JPoints.twoadicK0` at the triple with the powers `ap`,
`bp`, `cp`, for the coefficients `km` and a modulus `m > 0`: the sum of the terms
`km[i][j][4 - i - j] aⁱ bʲ c⁴⁻ⁱ⁻ʲ` modulo `m`, in `[0, m)`. -/
@[spec]
theorem twoadicK0_spec (km ap bp cp : Array ℤ) (m : ℕ) :
    ⦃ 0 < m ⦄ twoadicK0 km ap bp cp m
    ⦃ fun k0 ↦ 0 ≤ k0 ∧ k0 < (m : ℤ) ∧ (k0 : ZMod m) = ((∑ i ∈ Finset.range 5,
        ∑ j ∈ Finset.range (5 - i), km[(i * 5 + j) * 5 + (4 - i - j)]! * ap[i]! * bp[j]! *
          cp[4 - i - j]! : ℤ) : ZMod m) ⦄ := by
  vcgen [twoadicK0] invariants
  | inv1 => fun pref _ k0 ↦ TwoadicK0Invariant km ap bp cp m pref.length 0 k0
  | inv2 _ i _ _ _ _ => fun pref _ k0 ↦ TwoadicK0Invariant km ap bp cp m i pref.length k0
  all_goals with_reducible first
    | exact twoadicK0Invariant_zero km ap bp cp ‹_›
    | exact TwoadicK0Invariant.start ‹_› ‹_›
    | exact TwoadicK0Invariant.add ‹_› ‹_›
    | exact TwoadicK0Invariant.next ‹_› ‹_›
    | exact TwoadicK0Invariant.eq ‹_›

/-! ### The test of a triple -/

/-- The tables of `twoadic_table` modulo `64` that the test of a triple reads, as
`JPoints.twoadicTable` builds them: bit `d` of the word of `sol` at `(k₂, k₁, k₀)` set for the
solutions `d` of `k₂ d² + k₁ d + k₀ ≡ 0 (mod 64)`, the entries of `sq` at the squares set, and the
odd bits of `odd` set. -/
structure IsTwoadicLookup (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) : Prop where
  /-- The solutions of the quadratic equations. -/
  getLsbD_sol {k2 k1 k0 d : ℕ} (hk2 : k2 < 64) (hk1 : k1 < 64) (hk0 : k0 < 64) (hd : d < 64)
    (h : (k2 * d * d + k1 * d + k0) % 64 = 0) :
    sol[(k2 * 64 + k1) * 64 + k0]!.toBitVec.getLsbD d = true
  /-- The squares. -/
  getElem!_sq {i : ℕ} (hi : i < 64) : sq[i * i % 64]! = true
  /-- The odd residues. -/
  getLsbD_odd {d : ℕ} (hd : d < 64) (h : d % 2 = 1) : odd.toBitVec.getLsbD d = true

theorem IsTwoadicLookup.getLsbD_sol_toNat {sol : Array UInt64} {sq : Array Bool} {odd : UInt64}
    (h : IsTwoadicLookup sol sq odd) {k2 k1 k0 : ℤ} (hk0 : 0 ≤ k0 ∧ k0 < 64)
    (hk1 : 0 ≤ k1 ∧ k1 < 64) (hk2 : 0 ≤ k2 ∧ k2 < 64) {d : ZMod 64}
    (hq : (k2 : ZMod 64) * d ^ 2 + k1 * d + k0 = 0) :
    sol[((k2 * 64 + k1) * 64 + k0).toNat]!.toBitVec.getLsbD d.val = true := by
  rw [show ((k2 * 64 + k1) * 64 + k0).toNat = (k2.toNat * 64 + k1.toNat) * 64 + k0.toNat by lia]
  refine h.getLsbD_sol (by lia) (by lia) (by lia) d.val_lt (Nat.mod_eq_zero_of_dvd ?_)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [ZMod.natCast_toNat 64 hk0.1, ZMod.natCast_toNat 64 hk1.1,
    ZMod.natCast_toNat 64 hk2.1, ZMod.natCast_zmod_val]
  linear_combination hq

theorem IsTwoadicLookup.getElem!_sq_toNat {sol : Array UInt64} {sq : Array Bool} {odd : UInt64}
    (h : IsTwoadicLookup sol sq odd) {x : ℤ} (hx : IsSquare (x : ZMod 64)) :
    sq[(x % 64).toNat]! = true := by
  obtain ⟨r, hr⟩ := hx
  have := h.getElem!_sq r.val_lt
  rwa [← ZMod.val_mul, ← hr, show (x : ZMod 64).val = (x % 64).toNat by
    lia [ZMod.val_intCast (n := 64) x]] at this

section

variable (sol : Array UInt64) (sq : Array Bool) (odd : UInt64) (k0 k1 k2 a3 A0 : ℤ)

/-- The test of `JPoints.twoadicAdmits` for an odd denominator at the residue `d`, for the tables
`sol` and `sq`, the coefficients `k0`, `k1`, `k2` and the values `a3`, `A0` modulo `64`: bit `d`
of the word of the solutions of `k₂ d² + k₁ d + k₀ ≡ 0` set and `a³ d + A₀` a square. -/
def TwoadicTestOdd (d : ℕ) : Prop :=
  (sol[((k2 * 64 + k1) * 64 + k0).toNat]! >>> UInt64.ofNat d &&& 1 != 0) = true ∧
    sq[((a3 * d + A0) % 64).toNat]! = true

/-- The test of `JPoints.twoadicAdmits` for a denominator `2` modulo `4` at the residue `t`, for the
tables `sol`, `sq` and the word `odd` of the odd residues, the coefficients `k0`, `k1`, `k2` and the
values `a3`, `A0` modulo `64`: bit `t` odd of the word of the solutions of
`k₂ t² + 2 k₁ t + 4 k₀ ≡ 0` set and `8 (a³ t + 2 A₀)` a square. -/
def TwoadicTestTwo (t : ℕ) : Prop :=
  ((sol[((k2 * 64 + 2 * k1 % 64) * 64 + 4 * k0 % 64).toNat]! &&& odd) >>> UInt64.ofNat t &&& 1 !=
    0) = true ∧ sq[(8 * (a3 * t + 2 * A0) % 64).toNat]! = true

/-- The test of `JPoints.twoadicAdmits` for a denominator divisible by `2 ^ e`, for the table `sol`,
the word `odd` of the odd residues and the coefficients `k0`, `k1`, `k2` modulo `64`: an odd bit of
the word of the solutions of `k₂ t² + 2 ^ e k₁ t + 4 ^ e k₀ ≡ 0` set. -/
def TwoadicTestPow (e : ℕ) : Prop :=
  (sol[((k2 * 64 + (k1 <<< e) % 64) * 64 + (k0 <<< (2 * e)) % 64).toNat]! &&& odd != 0) = true

/-- The invariant of the loops of `JPoints.twoadicAdmits`: the triple admitted, or none of the
residues `d` of `l1`, `t` of `l2` and exponents `e` of `l3` passes its test. -/
def TwoadicAdmitsInvariant (l1 l2 l3 : List ℕ) (ok : Bool) : Prop :=
  ok = true ∨ (∀ d ∈ l1, ¬TwoadicTestOdd sol sq k0 k1 k2 a3 A0 d) ∧
    (∀ t ∈ l2, ¬TwoadicTestTwo sol sq odd k0 k1 k2 a3 A0 t) ∧
      ∀ e ∈ l3, ¬TwoadicTestPow sol odd k0 k1 k2 e

end

section

variable {sol : Array UInt64} {sq : Array Bool} {odd : UInt64} {k0 k1 k2 a3 A0 : ℤ}

theorem twoadicAdmitsInvariant_nil :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 [] [] [] false :=
  .inr ⟨by simp, by simp, by simp⟩

theorem TwoadicAdmitsInvariant.of_eq_true {l1 l2 l3 : List ℕ} {ok : Bool} (h : ok = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l2 l3 ok :=
  .inl h

theorem TwoadicAdmitsInvariant.of_not_not {l1 l2 l3 : List ℕ} {ok : Bool} (h : ¬(!ok) = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l2 l3 ok :=
  .inl (by simpa using h)

theorem TwoadicAdmitsInvariant.append_odd {l : List ℕ} {ok : Bool} {d : ℕ}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l [] [] ok) (hok : ¬ok = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (l ++ [d]) [] []
      sq[((a3 * d + A0) % 64).toNat]! := by
  rcases h with h | ⟨h, -, -⟩
  · exact absurd h hok
  cases hs : sq[((a3 * d + A0) % 64).toNat]!
  · exact .inr ⟨List.forall_mem_append.2 ⟨h, List.forall_mem_singleton.2 fun ht ↦
      absurd ht.2 (by simp [hs])⟩, by simp, by simp⟩
  · exact .inl rfl

theorem TwoadicAdmitsInvariant.append_odd_of_not {l : List ℕ} {ok : Bool} {d : ℕ}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l [] [] ok)
    (hb : ¬(sol[((k2 * 64 + k1) * 64 + k0).toNat]! >>> UInt64.ofNat d &&& 1 != 0) = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (l ++ [d]) [] [] ok :=
  h.imp_right fun ⟨h, _, _⟩ ↦
    ⟨List.forall_mem_append.2 ⟨h, List.forall_mem_singleton.2 fun ht ↦ hb ht.1⟩, by simp, by simp⟩

theorem TwoadicAdmitsInvariant.append_two {l1 l : List ℕ} {ok : Bool} {t : ℕ}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l [] ok) (hok : ¬ok = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 (l ++ [t]) []
      sq[(8 * (a3 * t + 2 * A0) % 64).toNat]! := by
  rcases h with h | ⟨h1, h, -⟩
  · exact absurd h hok
  cases hs : sq[(8 * (a3 * t + 2 * A0) % 64).toNat]!
  · exact .inr ⟨h1, List.forall_mem_append.2 ⟨h, List.forall_mem_singleton.2 fun ht ↦
      absurd ht.2 (by simp [hs])⟩, by simp⟩
  · exact .inl rfl

theorem TwoadicAdmitsInvariant.append_two_of_not {l1 l : List ℕ} {ok : Bool} {t : ℕ}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l [] ok)
    (hb : ¬((sol[((k2 * 64 + 2 * k1 % 64) * 64 + 4 * k0 % 64).toNat]! &&& odd) >>>
      UInt64.ofNat t &&& 1 != 0) = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 (l ++ [t]) [] ok :=
  h.imp_right fun ⟨h1, h, _⟩ ↦
    ⟨h1, List.forall_mem_append.2 ⟨h, List.forall_mem_singleton.2 fun ht ↦ hb ht.1⟩, by simp⟩

theorem TwoadicAdmitsInvariant.append_pow {l1 l2 l : List ℕ} {ok : Bool} {e : ℕ}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l2 l ok) (hok : ¬ok = true) :
    TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 l1 l2 (l ++ [e])
      (sol[((k2 * 64 + (k1 <<< e) % 64) * 64 + (k0 <<< (2 * e)) % 64).toNat]! &&& odd != 0) := by
  rcases h with h | ⟨h1, h2, h⟩
  · exact absurd h hok
  cases hs : sol[((k2 * 64 + (k1 <<< e) % 64) * 64 + (k0 <<< (2 * e)) % 64).toNat]! &&& odd != 0
  · exact .inr ⟨h1, h2, List.forall_mem_append.2 ⟨h, List.forall_mem_singleton.2 fun ht ↦
      absurd ht (by simp [TwoadicTestPow, hs])⟩⟩
  · exact .inl rfl

theorem TwoadicAdmitsInvariant.eq_true {ok : Bool}
    (h : TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (ForIn.toList [0:64])
      (ForIn.toList [1:64:2]) (ForIn.toList [2:7]) ok)
    (he : (∃ d ∈ ForIn.toList [0:64], TwoadicTestOdd sol sq k0 k1 k2 a3 A0 d) ∨
      (∃ t ∈ ForIn.toList [1:64:2], TwoadicTestTwo sol sq odd k0 k1 k2 a3 A0 t) ∨
        ∃ e ∈ ForIn.toList [2:7], TwoadicTestPow sol odd k0 k1 k2 e) :
    ok = true := by
  refine h.resolve_right fun ⟨h1, h2, h3⟩ ↦ ?_
  rcases he with ⟨d, hd, ht⟩ | ⟨t, ht', ht⟩ | ⟨e, he, ht⟩
  · exact h1 d hd ht
  · exact h2 t ht' ht
  · exact h3 e he ht

theorem twoadicTestOdd_of_eq (h : IsTwoadicLookup sol sq odd) (hk0 : 0 ≤ k0 ∧ k0 < 64)
    (hk1 : 0 ≤ k1 ∧ k1 < 64) (hk2 : 0 ≤ k2 ∧ k2 < 64) {d : ZMod 64}
    (hq : (k2 : ZMod 64) * d ^ 2 + k1 * d + k0 = 0)
    (hs : IsSquare ((a3 : ZMod 64) * d + A0)) : TwoadicTestOdd sol sq k0 k1 k2 a3 A0 d.val := by
  refine ⟨?_, h.getElem!_sq_toNat ?_⟩
  · rw [UInt64.shiftRight_and_one_bne_zero _ d.val_lt]
    exact h.getLsbD_sol_toNat hk0 hk1 hk2 hq
  · push_cast
    rwa [ZMod.natCast_zmod_val]

theorem twoadicTestTwo_of_eq (h : IsTwoadicLookup sol sq odd) (hk2 : 0 ≤ k2 ∧ k2 < 64)
    {t : ZMod 64} (ht : t.val % 2 = 1) (hq : (k2 : ZMod 64) * t ^ 2 + 2 * k1 * t + 4 * k0 = 0)
    (hs : IsSquare (8 * ((a3 : ZMod 64) * t + 2 * A0))) :
    TwoadicTestTwo sol sq odd k0 k1 k2 a3 A0 t.val := by
  refine ⟨?_, h.getElem!_sq_toNat ?_⟩
  · rw [UInt64.shiftRight_and_one_bne_zero _ t.val_lt, UInt64.toBitVec_and, BitVec.getLsbD_and,
      h.getLsbD_odd t.val_lt ht, Bool.and_true]
    refine h.getLsbD_sol_toNat (emod_sixtyFour_bounds _) (emod_sixtyFour_bounds _) hk2 ?_
    push_cast [intCast_emod_sixtyFour]
    linear_combination hq
  · push_cast
    rwa [ZMod.natCast_zmod_val]

theorem twoadicTestPow_of_eq (h : IsTwoadicLookup sol sq odd) (hk2 : 0 ≤ k2 ∧ k2 < 64) {e : ℕ}
    {t : ZMod 64} (ht : t.val % 2 = 1)
    (hq : (k2 : ZMod 64) * t ^ 2 + 2 ^ e * k1 * t + 4 ^ e * k0 = 0) :
    TwoadicTestPow sol odd k0 k1 k2 e := by
  have hb : (sol[((k2 * 64 + (k1 <<< e) % 64) * 64 + (k0 <<< (2 * e)) % 64).toNat]! &&&
      odd).toBitVec.getLsbD t.val = true := by
    rw [UInt64.toBitVec_and, BitVec.getLsbD_and, h.getLsbD_odd t.val_lt ht, Bool.and_true]
    refine h.getLsbD_sol_toNat (emod_sixtyFour_bounds _) (emod_sixtyFour_bounds _) hk2 ?_
    push_cast [intCast_emod_sixtyFour, Int.shiftLeft_eq, pow_mul]
    linear_combination hq
  refine bne_iff_ne.2 fun h0 ↦ ?_
  simp [h0] at hb

/-- The condition at 2 modulo `64` on the residues `k₂`, `k₁`, `k₀` in `[0, 64)` and `a³`, `A₀`
passes one of the tests of `JPoints.twoadicAdmits`, for the tables of
`JPoints.IsTwoadicLookup`. -/
theorem exists_twoadicTest_of_twoadicCondition (h : IsTwoadicLookup sol sq odd)
    (hk : 0 ≤ k0 ∧ k0 < 64 ∧ 0 ≤ k1 ∧ k1 < 64 ∧ 0 ≤ k2 ∧ k2 < 64)
    (hc : TwoadicCondition k2 k1 k0 a3 A0) :
    (∃ d ∈ ForIn.toList [0:64], TwoadicTestOdd sol sq k0 k1 k2 a3 A0 d) ∨
      (∃ t ∈ ForIn.toList [1:64:2], TwoadicTestTwo sol sq odd k0 k1 k2 a3 A0 t) ∨
        ∃ e ∈ ForIn.toList [2:7], TwoadicTestPow sol odd k0 k1 k2 e := by
  obtain ⟨hk0, hk0', hk1, hk1', hk2⟩ := hk
  rcases hc with ⟨d, hq, hs⟩ | ⟨t, ht, hq, hs⟩ | ⟨e, he2, he6, t, ht, hq⟩
  · exact .inl ⟨d.val, Std.Legacy.Range.mem_toList_of_lt d.val_lt,
      twoadicTestOdd_of_eq h ⟨hk0, hk0'⟩ ⟨hk1, hk1'⟩ hk2 hq hs⟩
  · exact .inr (.inl ⟨t.val, Std.Legacy.Range.mem_toList_one_two t.val_lt ht,
      twoadicTestTwo_of_eq h hk2 ht hq hs⟩)
  · exact .inr (.inr ⟨e, Std.Legacy.Range.mem_toList_of_le_of_lt he2 (by lia),
      twoadicTestPow_of_eq h hk2 ht hq⟩)

end

attribute [local irreducible] TwoadicAdmitsInvariant in
/-- The test of `JPoints.twoadicAdmits` admits a triple whose residues `k₂`, `k₁`, `k₀` in
`[0, 64)` and `a³`, `A₀` modulo `64` satisfy the condition at 2 (`JPoints.TwoadicCondition`), for
the tables of `JPoints.IsTwoadicLookup`. -/
@[spec]
theorem twoadicAdmits_spec {sol : Array UInt64} {sq : Array Bool} {odd : UInt64}
    (h : IsTwoadicLookup sol sq odd) (k0 k1 k2 a3 A0 : ℤ) :
    ⦃ 0 ≤ k0 ∧ k0 < 64 ∧ 0 ≤ k1 ∧ k1 < 64 ∧ 0 ≤ k2 ∧ k2 < 64 ⦄
    twoadicAdmits sol sq odd 64 k0 k1 k2 a3 A0
    ⦃ fun r ↦ TwoadicCondition k2 k1 k0 a3 A0 → r = true ⦄ := by
  vcgen [twoadicAdmits] invariants
  · fun pref _ ok ↦ TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 pref [] [] ok
  · fun pref _ ok ↦ TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (ForIn.toList [0:64]) pref
      [] ok
  · fun pref _ ok ↦ TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (ForIn.toList [0:64])
      (ForIn.toList [1:64:2]) pref ok
  · fun pref _ ok ↦ TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 (ForIn.toList [0:64])
      (ForIn.toList [1:64:2]) pref ok
  all_goals try simp only [Nat.cast_ofNat] at *
  all_goals with_reducible first
    | exact twoadicAdmitsInvariant_nil
    | exact ‹TwoadicAdmitsInvariant sol sq odd k0 k1 k2 a3 A0 _ _ _ _›
    | exact TwoadicAdmitsInvariant.of_eq_true ‹_›
    | exact TwoadicAdmitsInvariant.of_not_not ‹_›
    | exact TwoadicAdmitsInvariant.append_odd ‹_› ‹_›
    | exact TwoadicAdmitsInvariant.append_odd_of_not ‹_› ‹_›
    | exact TwoadicAdmitsInvariant.append_two ‹_› ‹_›
    | exact TwoadicAdmitsInvariant.append_two_of_not ‹_› ‹_›
    | exact TwoadicAdmitsInvariant.append_pow ‹_› ‹_›
    | exact TwoadicAdmitsInvariant.eq_true ‹_› (exists_twoadicTest_of_twoadicCondition h ‹_› ‹_›)

/-! ### The test of a triple of residues -/

/-- The quartic `K₀` from the coefficients of `kummer_init` (`JPoints.KummerCoeffs.coeff`): the sum
of the terms `k_{i j l} aⁱ bʲ cˡ` over `i + j + l = 4`, as `twoadic_table` adds them up. -/
theorem sum_coeff_kummerInit (coeffs : Array ℤ) (a b c : ℤ) :
    ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (5 - i),
      (kummerInit coeffs).coeff i j * a ^ i * b ^ j * c ^ (4 - i - j) =
        kummerK0 (coeffs.toList.getD · 0) a b c := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, KummerCoeffs.coeff, kummerInit,
    kummerK0, Array.getD_toList_eq_getElem!]
  ring

/-- The coefficients `fm` of the curve with the coefficients `coeffs` and `km` of its quartic `K₀`
modulo `64`, as `JPoints.twoadicCoeffs` reduces them for `JPoints.twoadicTable`. -/
structure IsTwoadicResidues (coeffs fm km : Array ℤ) : Prop where
  /-- The coefficients of the curve. -/
  getElem!_fm {i : ℕ} (hi : i < 7) : fm[i]! = coeffs[i]! % 64
  /-- The coefficients of the quartic. -/
  getElem!_km {i j : ℕ} (h : i + j ≤ 4) :
    km[(i * 5 + j) * 5 + (4 - i - j)]! = (kummerInit coeffs).coeff i j % 64

theorem IsTwoadicResidues.intCast_sum {coeffs fm km ap bp cp : Array ℤ}
    (hr : IsTwoadicResidues coeffs fm km) {a b c : ℕ}
    (hap : ∀ i < 5, ((ap[i]! : ℤ) : ZMod 64) = (a : ZMod 64) ^ i)
    (hbp : ∀ i < 5, ((bp[i]! : ℤ) : ZMod 64) = (b : ZMod 64) ^ i)
    (hcp : ∀ i < 5, ((cp[i]! : ℤ) : ZMod 64) = (c : ZMod 64) ^ i) :
    ((∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range (5 - i),
      km[(i * 5 + j) * 5 + (4 - i - j)]! * ap[i]! * bp[j]! * cp[4 - i - j]! : ℤ) : ZMod 64) =
        kummerK0 (coeffs.toList.getD · 0) a b c := by
  rw [← sum_coeff_kummerInit]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  simp only [Finset.mem_range] at hi hj
  rw [hr.getElem!_km (by lia), intCast_emod_sixtyFour, hap i hi, hbp j (by lia), hcp _ (by lia)]

theorem TwoadicAdmissible.twoadicCondition {f : ℕ → ℤ} {a b c : ℤ} {k2 k1 k0 a3 A0 : ZMod 64}
    (h : TwoadicAdmissible f a b c) (h2 : (kummerK2 a b c : ZMod 64) = k2)
    (h1 : (kummerK1 f a b c : ZMod 64) = k1) (h0 : (kummerK0 f a b c : ZMod 64) = k0)
    (h3 : (a : ZMod 64) ^ 3 = a3) (hA : (auxA2 f a b c 0 : ZMod 64) = A0) :
    TwoadicCondition k2 k1 k0 a3 A0 :=
  h2 ▸ h1 ▸ h0 ▸ h3 ▸ hA ▸ h

/- The residues of the test of a triple in `JPoints.twoadicCell`, for the tables of
`JPoints.IsTwoadicResidues` and the powers of the residues `a2`, `b2`, `c2`, are those of `K₂`,
`K₁`, `K₀`, `a³` and `A₀` modulo `64`, so that the condition at 2 of the triple
(`JPoints.TwoadicAdmissible`) is that of the residues; in the shape of the verification condition
of `JPoints.twoadicCell_spec`. -/
private theorem twoadicCell_post {coeffs fm km ap bp cp : Array ℤ} {a2 b2 c2 : ℕ} {k0 : ℤ}
    {r : Bool} (hr : IsTwoadicResidues coeffs fm km)
    (hap : ∀ i < 5, ((ap[i]! : ℤ) : ZMod 64) = (a2 : ZMod 64) ^ i)
    (hbp : ∀ i < 5, ((bp[i]! : ℤ) : ZMod 64) = (b2 : ZMod 64) ^ i)
    (hcp : ∀ i < 5, ((cp[i]! : ℤ) : ZMod 64) = (c2 : ZMod 64) ^ i)
    (hk0 : 0 ≤ k0 ∧ k0 < 64 ∧ (k0 : ZMod 64) = ((∑ i ∈ Finset.range 5,
      ∑ j ∈ Finset.range (5 - i), km[(i * 5 + j) * 5 + (4 - i - j)]! * ap[i]! * bp[j]! *
        cp[4 - i - j]! : ℤ) : ZMod 64))
    (h : TwoadicCondition ((bp[2]! + (64 : ℤ) * 4 - 4 * (a2 : ℤ) * (c2 : ℤ)) % 64 : ℤ)
      (((64 : ℤ) - ((4 : ℤ) * ap[3]! * fm[0]! + (2 : ℤ) * ap[2]! * (b2 : ℤ) * fm[1]! +
        (4 : ℤ) * ap[2]! * (c2 : ℤ) * fm[2]! + (2 : ℤ) * (a2 : ℤ) * (b2 : ℤ) * (c2 : ℤ) * fm[3]! +
        (4 : ℤ) * (a2 : ℤ) * cp[2]! * fm[4]! + (2 : ℤ) * (b2 : ℤ) * cp[2]! * fm[5]! +
        (4 : ℤ) * cp[3]! * fm[6]!) % 64) % 64 : ℤ) k0 ap[3]!
      ((fm[2]! * ap[4]! + fm[3]! * ap[3]! * (b2 : ℤ) + fm[4]! * ap[2]! * bp[2]! +
        fm[5]! * (a2 : ℤ) * (b2 : ℤ) * ((bp[2]! + (64 : ℤ) * 4 - (a2 : ℤ) * (c2 : ℤ)) % 64) +
        fm[6]! * ((bp[2]! + (64 : ℤ) * 4 - (a2 : ℤ) * (c2 : ℤ)) % 64) *
          ((bp[2]! + (64 : ℤ) * 4 - (a2 : ℤ) * (c2 : ℤ)) % 64)) % 64 : ℤ) → r = true)
    (hP : TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2) : r = true := by
  have hfm (i : ℕ) (hi : i < 7) : ((fm[i]! : ℤ) : ZMod 64) = coeffs.toList.getD i 0 := by
    rw [hr.getElem!_fm hi, intCast_emod_sixtyFour, Array.getD_toList_eq_getElem!]
  refine h (hP.twoadicCondition ?_ ?_ ?_ ?_ ?_)
  · push_cast [intCast_emod_sixtyFour, hbp, kummerK2]
    ring_nf
    reduce_mod_char
  · push_cast [intCast_emod_sixtyFour, hap, hcp, hfm, kummerK1]
    ring_nf
    reduce_mod_char
  · rw [hk0.2.2, hr.intCast_sum hap hbp hcp]
  · push_cast [hap]
    rfl
  · push_cast [intCast_emod_sixtyFour, hap, hbp, hfm, auxA2]
    ring_nf
    reduce_mod_char

/- The bounds of the residues `k₀`, `k₁`, `k₂` that `JPoints.twoadicCell` passes to the test, in
the shape of the verification condition of `JPoints.twoadicCell_spec`. -/
private theorem twoadicCell_bounds {k0 : ℤ} {P : Prop} (h : 0 ≤ k0 ∧ k0 < 64 ∧ P) (x y : ℤ) :
    0 ≤ k0 ∧ k0 < 64 ∧ 0 ≤ x % 64 ∧ x % 64 < 64 ∧ 0 ≤ y % 64 ∧ y % 64 < 64 :=
  ⟨h.1, h.2.1, (emod_sixtyFour_bounds x).1, (emod_sixtyFour_bounds x).2, emod_sixtyFour_bounds y⟩

/-- The test of `JPoints.twoadicCell` admits the triple `(a2, b2, c2)` modulo `64` when the triple
satisfies the condition at 2 (`JPoints.TwoadicAdmissible`), for the tables of
`JPoints.IsTwoadicLookup` and `JPoints.IsTwoadicResidues` and the powers of `a2` and `b2`. -/
@[spec]
theorem twoadicCell_spec {coeffs fm km : Array ℤ} {sol : Array UInt64} {sq : Array Bool}
    {odd : UInt64} (h : IsTwoadicLookup sol sq odd) (hr : IsTwoadicResidues coeffs fm km)
    {ap bp : Array ℤ} {a2 b2 : ℕ} (hap : ∀ i < 5, ((ap[i]! : ℤ) : ZMod 64) = (a2 : ZMod 64) ^ i)
    (hbp : ∀ i < 5, ((bp[i]! : ℤ) : ZMod 64) = (b2 : ZMod 64) ^ i) (c2 : ℕ) :
    ⦃ True ⦄ twoadicCell fm km sol sq odd 64 ap bp a2 b2 c2
    ⦃ fun r ↦ TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 → r = true ⦄ := by
  vcgen [twoadicCell, twoadicAdmits_spec h]
  all_goals try simp only [Nat.cast_ofNat] at *
  all_goals first
    | decide
    | exact twoadicCell_bounds ‹_› _ _
    | exact twoadicCell_post hr hap hbp ‹_› ‹_› ‹_› ‹_›

/-! ### The rows of the classes -/

/-- The invariant of the loop of `JPoints.twoadicRow` over the residues `c2` of the class
`(a2, b2)` modulo `64`: the word `mask` has the bit of every `c2 < n` not all of whose coordinates
are even at which the condition at 2 holds for the curve with the coefficients `coeffs`. -/
def TwoadicRowInvariant (coeffs : Array ℤ) (a2 b2 n : ℕ) (mask : UInt64) : Prop :=
  ∀ c2 < n, ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
    TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 → mask.toBitVec.getLsbD c2 = true

theorem twoadicRowInvariant_zero (coeffs : Array ℤ) (a2 b2 : ℕ) :
    TwoadicRowInvariant coeffs a2 b2 ([] : List ℕ).length 0 :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

theorem TwoadicRowInvariant.of_and_one {coeffs : Array ℤ} {a2 b2 : ℕ} {pref suff : List ℕ}
    {cur : ℕ} {mask : UInt64} (hl : ForIn.toList [0:64] = pref ++ cur :: suff)
    (h : TwoadicRowInvariant coeffs a2 b2 pref.length mask)
    (hc : ((a2 ||| b2 ||| cur) &&& 1 == 0) = true) :
    TwoadicRowInvariant coeffs a2 b2 (pref ++ [cur]).length mask := by
  have hcur := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [beq_iff_eq, Nat.or_or_and_one_eq_zero_iff] at hc
  intro c2 hc2 hodd
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa using hc2)) with hc2 | rfl
  · exact h c2 hc2 hodd
  · exact absurd (hcur ▸ hc) hodd

theorem TwoadicRowInvariant.or_one_shiftLeft {coeffs : Array ℤ} {a2 b2 : ℕ}
    {pref suff : List ℕ} {cur : ℕ} {mask : UInt64}
    (hl : ForIn.toList [0:64] = pref ++ cur :: suff)
    (h : TwoadicRowInvariant coeffs a2 b2 pref.length mask) :
    TwoadicRowInvariant coeffs a2 b2 (pref ++ [cur]).length (mask ||| 1 <<< UInt64.ofNat cur) := by
  have hcur := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have h64 := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro c2 hc2 hodd hc
  rw [UInt64.getLsbD_or_one_shiftLeft _ h64, Bool.or_eq_true, decide_eq_true_iff]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa using hc2)) with hc2 | rfl
  · exact .inl (h c2 hc2 hodd hc)
  · exact .inr hcur

theorem TwoadicRowInvariant.of_not {coeffs : Array ℤ} {a2 b2 : ℕ} {pref suff : List ℕ}
    {cur : ℕ} {mask : UInt64} {r : Bool} (hl : ForIn.toList [0:64] = pref ++ cur :: suff)
    (h : TwoadicRowInvariant coeffs a2 b2 pref.length mask)
    (hr : TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 cur → r = true) (hn : ¬r = true) :
    TwoadicRowInvariant coeffs a2 b2 (pref ++ [cur]).length mask := by
  have hcur := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  intro c2 hc2 hodd hc
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by simpa using hc2)) with hc2 | rfl
  · exact h c2 hc2 hodd hc
  · exact absurd (hr (hcur ▸ hc)) hn

theorem TwoadicRowInvariant.getLsbD {coeffs : Array ℤ} {a2 b2 : ℕ} {mask : UInt64}
    (h : TwoadicRowInvariant coeffs a2 b2 (ForIn.toList [0:64]).length mask) {c2 : ℕ}
    (hc2 : c2 < 64) (hodd : ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0))
    (hc : TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2) :
    mask.toBitVec.getLsbD c2 = true :=
  h c2 (by simpa using hc2) hodd hc

attribute [local irreducible] TwoadicRowInvariant in
/- `JPoints.twoadicRow_spec` with the powers of the residues `a2` and `b2` as hypotheses. -/
private theorem twoadicRow_spec_of {coeffs fm km : Array ℤ} {sol : Array UInt64}
    {sq : Array Bool} {odd : UInt64} (h : IsTwoadicLookup sol sq odd)
    (hr : IsTwoadicResidues coeffs fm km) {ap bp : Array ℤ} {a2 b2 : ℕ}
    (hap : ∀ i < 5, ((ap[i]! : ℤ) : ZMod 64) = (a2 : ZMod 64) ^ i)
    (hbp : ∀ i < 5, ((bp[i]! : ℤ) : ZMod 64) = (b2 : ZMod 64) ^ i) :
    ⦃ True ⦄ twoadicRow fm km sol sq odd 64 ap bp a2 b2
    ⦃ fun r ↦ ∀ c2 < (64 : ℕ), ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
        TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 → r.1.toBitVec.getLsbD c2 = true ⦄ := by
  vcgen [twoadicRow, twoadicCell_spec h hr hap hbp] invariants
  · fun pref _ s ↦ TwoadicRowInvariant coeffs a2 b2 pref.length s.1
  · .mk fun _ _ ↦ False
  · .ofMeasure fun s : UInt64 × ℕ ↦ s.2
  all_goals with_reducible first
    | exact absurd ‹64 < 64› (by decide)
    | exact twoadicRowInvariant_zero coeffs a2 b2
    | exact TwoadicRowInvariant.of_and_one ‹_› ‹_› ‹_›
    | exact TwoadicRowInvariant.or_one_shiftLeft ‹_› ‹_›
    | exact TwoadicRowInvariant.of_not ‹_› ‹_› ‹_› ‹_›
    | exact TwoadicRowInvariant.getLsbD ‹_› ‹_› ‹_› ‹_›

/-- The row of the class `(a2, b2)` modulo `64` of `JPoints.twoadicRow` has the bit of every residue
`c2` not all of whose coordinates are even at which the condition at 2 holds
(`JPoints.TwoadicAdmissible`), for the tables of `JPoints.IsTwoadicLookup` and
`JPoints.IsTwoadicResidues` and the powers of `a2` and `b2`. -/
@[spec]
theorem twoadicRow_spec {coeffs fm km : Array ℤ} {sol : Array UInt64} {sq : Array Bool}
    {odd : UInt64} (h : IsTwoadicLookup sol sq odd) (hr : IsTwoadicResidues coeffs fm km)
    (ap bp : Array ℤ) (a2 b2 : ℕ) :
    ⦃ (∀ i < 5, ((ap[i]! : ℤ) : ZMod 64) = (a2 : ZMod 64) ^ i) ∧
        ∀ i < 5, ((bp[i]! : ℤ) : ZMod 64) = (b2 : ZMod 64) ^ i ⦄
    twoadicRow fm km sol sq odd 64 ap bp a2 b2
    ⦃ fun r ↦ ∀ c2 < (64 : ℕ), ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
        TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 → r.1.toBitVec.getLsbD c2 = true ⦄ :=
  ⟨fun ⟨hap, hbp⟩ ↦ (twoadicRow_spec_of h hr hap hbp).le_wp trivial⟩

/-! ### The classes -/

/-- The words `masks` and the flags `alive` at `a2 * 64 + b2` keep the classes modulo `64` of the
condition at 2 for the curve with the coefficients `coeffs`: for every triple `(a2, b2, c2)` of
residues not all even at which it holds (`JPoints.TwoadicAdmissible`), the word of `(a2, b2)` has
the bit `c2` and the class is alive. -/
def IsTwoadicTable (coeffs : Array ℤ) (masks : Array UInt64) (alive : Array Bool) : Prop :=
  ∀ a2 < (64 : ℕ), ∀ b2 < (64 : ℕ), ∀ c2 < (64 : ℕ), ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
    TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 →
      masks[a2 * 64 + b2]!.toBitVec.getLsbD c2 = true ∧ alive[a2 * 64 + b2]! = true

/-- The invariant of the loops of `JPoints.twoadicClasses`: the `64 × 64` entries of `masks` and
`alive`, those of the classes `(a2, b2) < (A, B)` in lexicographic order as in
`JPoints.IsTwoadicTable`. -/
def TwoadicClassesInvariant (coeffs : Array ℤ) (A B : ℕ) (masks : Array UInt64)
    (alive : Array Bool) : Prop :=
  masks.size = 64 * 64 ∧ alive.size = 64 * 64 ∧ ∀ a2 < (64 : ℕ), ∀ b2 < (64 : ℕ),
    (a2 < A ∨ a2 = A ∧ b2 < B) → ∀ c2 < (64 : ℕ), ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
      TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 →
        masks[a2 * 64 + b2]!.toBitVec.getLsbD c2 = true ∧ alive[a2 * 64 + b2]! = true

theorem twoadicClassesInvariant_init (coeffs : Array ℤ) {masks : Array UInt64}
    {alive : Array Bool} (hm : masks.size = 64 * 64) (ha : alive.size = 64 * 64) :
    TwoadicClassesInvariant coeffs ([] : List ℕ).length 0 masks alive :=
  ⟨hm, ha, fun _ _ _ _ h ↦ by simp at h⟩

theorem TwoadicClassesInvariant.start {coeffs : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    {masks : Array UInt64} {alive : Array Bool} (hl : ForIn.toList [0:64] = pref ++ cur :: suff)
    (h : TwoadicClassesInvariant coeffs pref.length 0 masks alive) :
    TwoadicClassesInvariant coeffs cur ([] : List ℕ).length masks alive := by
  rw [← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  exact h

theorem TwoadicClassesInvariant.next {coeffs : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    {masks : Array UInt64} {alive : Array Bool} (hl : ForIn.toList [0:64] = pref ++ cur :: suff)
    (h : TwoadicClassesInvariant coeffs cur (ForIn.toList [0:64]).length masks alive) :
    TwoadicClassesInvariant coeffs (pref ++ [cur]).length 0 masks alive := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨h.1, h.2.1, fun a2 ha2 b2 hb2 hlt ↦ h.2.2 a2 ha2 b2 hb2 ?_⟩
  simp only [List.length_append, List.length_singleton, Std.Legacy.Range.length_toList] at hlt ⊢
  lia

theorem TwoadicClassesInvariant.set! {coeffs : Array ℤ} {a2 : ℕ} (ha2 : a2 < 64)
    {pref suff : List ℕ} {b2 : ℕ} {masks : Array UInt64} {alive : Array Bool} {all mask : UInt64}
    {n : ℕ} (hall : all = ~~~0) (hl : ForIn.toList [0:64] = pref ++ b2 :: suff)
    (h : TwoadicClassesInvariant coeffs a2 pref.length masks alive)
    (hrow : ∀ c2 < (64 : ℕ), ¬(a2 % 2 = 0 ∧ b2 % 2 = 0 ∧ c2 % 2 = 0) →
      TwoadicAdmissible (coeffs.toList.getD · 0) a2 b2 c2 →
        (mask, n).1.toBitVec.getLsbD c2 = true) :
    TwoadicClassesInvariant coeffs a2 (pref ++ [b2]).length
      (masks.set! (a2 * 64 + b2) (mask &&& if 64 < 64 then ~~~0 else all))
      (alive.set! (a2 * 64 + b2) (mask != 0)) := by
  have hb := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hb64 := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [ite_eq_right (by decide), hall, show mask &&& ~~~0 = mask by simp]
  refine ⟨(Array.size_set! ..).trans h.1, (Array.size_set! ..).trans h.2.1,
    fun a2' ha2' b2' hb2' hlt c2 hc2 hodd hc ↦ ?_⟩
  simp only [List.length_append, List.length_singleton] at hlt
  by_cases he : a2' = a2 ∧ b2' = b2
  · obtain ⟨rfl, rfl⟩ := he
    have hbit := hrow c2 hc2 hodd hc
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.1]; lia),
      Array.getElem!_set!_self _ _ _ (by rw [h.2.1]; lia)]
    refine ⟨hbit, bne_iff_ne.2 fun h0 ↦ ?_⟩
    simp [h0] at hbit
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h.2.2 a2' ha2' b2' hb2' (by lia) c2 hc2 hodd hc

theorem TwoadicClassesInvariant.isTwoadicTable {coeffs : Array ℤ} {masks : Array UInt64}
    {alive : Array Bool}
    (h : TwoadicClassesInvariant coeffs (ForIn.toList [0:64]).length 0 masks alive) :
    IsTwoadicTable coeffs masks alive :=
  fun a2 ha2 b2 hb2 ↦ h.2.2 a2 ha2 b2 hb2 (.inl (by simpa using ha2))

attribute [local irreducible] TwoadicClassesInvariant in
/- `JPoints.twoadicClasses_spec` with the tables, the sizes and the word `all` as hypotheses. -/
private theorem twoadicClasses_spec_of {coeffs fm km : Array ℤ} {sol : Array UInt64}
    {sq : Array Bool} {odd : UInt64} (h : IsTwoadicLookup sol sq odd)
    (hr : IsTwoadicResidues coeffs fm km) {all : UInt64} (hall : all = ~~~0)
    {masks : Array UInt64} {alive : Array Bool} (hm : masks.size = 64 * 64)
    (ha : alive.size = 64 * 64) :
    ⦃ True ⦄ twoadicClasses fm km sol sq odd all 64 masks alive
    ⦃ fun r ↦ IsTwoadicTable coeffs r.masks r.alive ⦄ := by
  vcgen [twoadicClasses, twoadicRow_spec h hr] invariants
  | inv1 => fun pref _ s ↦ TwoadicClassesInvariant coeffs pref.length 0 s.1 s.2.1
  | inv2 _ a2 _ _ _ _ _ _ _ _ => fun pref _ s ↦
      TwoadicClassesInvariant coeffs a2 pref.length s.1 s.2.1
  all_goals with_reducible first
    | exact twoadicClassesInvariant_init coeffs hm ha
    | exact TwoadicClassesInvariant.isTwoadicTable ‹_›
    | exact TwoadicClassesInvariant.start ‹_› ‹_›
    | exact TwoadicClassesInvariant.next ‹_› ‹_›
    | exact ⟨‹_›, ‹_›⟩
    | exact TwoadicClassesInvariant.set! (Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›) hall
        ‹_› ‹_› ‹_›

/-- The words and flags of the classes modulo `64` of `JPoints.twoadicClasses` keep the classes of
the condition at 2 (`JPoints.IsTwoadicTable`), for the tables of `JPoints.IsTwoadicLookup` and
`JPoints.IsTwoadicResidues`, the word `all` of all bits and the arrays of the `64 × 64`
classes. -/
@[spec]
theorem twoadicClasses_spec (coeffs : Array ℤ) {fm km : Array ℤ} {sol : Array UInt64}
    {sq : Array Bool} {odd all : UInt64} {masks : Array UInt64} {alive : Array Bool} :
    ⦃ IsTwoadicLookup sol sq odd ∧ IsTwoadicResidues coeffs fm km ∧ all = ~~~0 ∧
        masks.size = 64 * 64 ∧ alive.size = 64 * 64 ⦄
    twoadicClasses fm km sol sq odd all 64 masks alive
    ⦃ fun r ↦ IsTwoadicTable coeffs r.masks r.alive ⦄ :=
  ⟨fun ⟨h, hr, hall, hm, ha⟩ ↦ (twoadicClasses_spec_of h hr hall hm ha).le_wp trivial⟩

/-! ### The table modulo `64` -/

/-- The invariant of the loop of `JPoints.twoadicTable` that builds the word of the odd residues:
the bits of the residues of `pref` set. -/
def TwoadicOddInvariant (pref : List ℕ) (odd : UInt64) : Prop :=
  ∀ d ∈ pref, odd.toBitVec.getLsbD d = true

theorem twoadicOddInvariant_nil : TwoadicOddInvariant [] 0 :=
  fun _ h ↦ absurd h List.not_mem_nil

theorem TwoadicOddInvariant.or_one_shiftLeft {m : ℕ} (hm : m ≤ 64) {pref suff : List ℕ}
    {cur : ℕ} {odd : UInt64} (hl : ForIn.toList [1:m:2] = pref ++ cur :: suff)
    (h : TwoadicOddInvariant pref odd) :
    TwoadicOddInvariant (pref ++ [cur]) (odd ||| 1 <<< UInt64.ofNat cur) := by
  have hc : cur < 64 := by
    have : cur ∈ ForIn.toList [1:m:2] := by simp [hl]
    simp only [Std.Internal.ForIn.toList_range, List.mem_range', Std.Legacy.Range.size] at this
    lia
  intro d hd
  rw [UInt64.getLsbD_or_one_shiftLeft _ hc, Bool.or_eq_true, decide_eq_true_iff]
  rcases List.mem_append.1 hd with hd | hd
  · exact .inl (h d hd)
  · exact .inr (List.mem_singleton.1 hd)

theorem isTwoadicLookup_of {sol : Array UInt64} {sq : Array Bool} {odd : UInt64}
    (hodd : TwoadicOddInvariant (ForIn.toList [1:64:2]) odd)
    (hsq : ∀ i < 64, sq[i * i % 64]! = true)
    (hsol : ∀ k2 < 64, ∀ k1 < 64, ∀ k0 < 64, ∀ d < 64, (k2 * d * d + k1 * d + k0) % 64 = 0 →
      sol[(k2 * 64 + k1) * 64 + k0]!.toBitVec.getLsbD d = true) :
    IsTwoadicLookup sol sq odd where
  getLsbD_sol hk2 hk1 hk0 hd h := hsol _ hk2 _ hk1 _ hk0 _ hd h
  getElem!_sq hi := hsq _ hi
  getLsbD_odd hd h := hodd _ (Std.Legacy.Range.mem_toList_one_two hd h)

theorem isTwoadicResidues_of {coeffs fm km : Array ℤ}
    (h : (∀ i < 7, (fm, km).1[i]! = coeffs[i]! % ((64 : ℕ) : ℤ)) ∧ ∀ i j, i + j ≤ 4 →
      (fm, km).2[(i * 5 + j) * 5 + (4 - i - j)]! = (kummerInit coeffs).coeff i j % ((64 : ℕ) : ℤ)) :
    IsTwoadicResidues coeffs fm km where
  getElem!_fm hi := h.1 _ hi
  getElem!_km hij := h.2 _ _ hij

attribute [local irreducible] TwoadicOddInvariant in
/- `JPoints.twoadicTable_spec` for the coefficients of the quartic of `kummer_init`. -/
private theorem twoadicTable_spec_kummerInit (coeffs : Array ℤ) (masks : Array UInt64)
    (alive : Array Bool) :
    ⦃ masks.size = 64 * 64 ∧ alive.size = 64 * 64 ⦄
    twoadicTable coeffs (kummerInit coeffs) 64 masks alive
    ⦃ fun r ↦ IsTwoadicTable coeffs r.masks r.alive ⦄ := by
  vcgen [twoadicTable, twoadicClasses_spec coeffs] invariants
  · fun pref _ odd ↦ TwoadicOddInvariant pref odd
  all_goals first
    | decide
    | exact twoadicOddInvariant_nil
    | exact TwoadicOddInvariant.or_one_shiftLeft (m := 64) (by decide) ‹_› ‹_›
    | exact ⟨isTwoadicLookup_of ‹_› ‹_› ‹_›, isTwoadicResidues_of ‹_›, rfl,
        ‹masks.size = 64 * 64 ∧ alive.size = 64 * 64›⟩

/-- The table modulo `64` of `JPoints.twoadicTable` keeps the classes of the condition at 2
(`JPoints.IsTwoadicTable`), for the coefficients `k = kummer_init(coeffs)` of the quartic and the
arrays of the `64 × 64` classes. -/
@[spec]
theorem twoadicTable_spec (coeffs : Array ℤ) (k : KummerCoeffs) (masks : Array UInt64)
    (alive : Array Bool) :
    ⦃ k = kummerInit coeffs ∧ masks.size = 64 * 64 ∧ alive.size = 64 * 64 ⦄
    twoadicTable coeffs k 64 masks alive
    ⦃ fun r ↦ IsTwoadicTable coeffs r.masks r.alive ⦄ :=
  ⟨fun ⟨hk, hs⟩ ↦ hk ▸ (twoadicTable_spec_kummerInit coeffs masks alive).le_wp hs⟩

/-! ### The condition at 2 admits every point -/

/-- A coprime triple `(a, b, c)` with `a ≠ 0` over which a point lies reduces to a class modulo `64`
that a table of the condition at 2 keeps (`JPoints.IsTwoadicTable`): not all three residues are
even, and the condition at 2 holds (`JPoints.twoadicAdmissible_of_hasPointOver`). -/
theorem IsTwoadicTable.getLsbD_and_getElem! {coeffs : Array ℤ} {masks : Array UInt64}
    {alive : Array Bool} (h : IsTwoadicTable coeffs masks alive) {a b c : ℤ} (ha : a ≠ 0)
    (habc : gcd a (gcd b c) = 1) (hp : HasPointOver coeffs.toList (a, b, c)) :
    masks[(a % 64).toNat * 64 + (b % 64).toNat]!.toBitVec.getLsbD (c % 64).toNat = true ∧
      alive[(a % 64).toNat * 64 + (b % 64).toNat]! = true := by
  refine h _ (by lia) _ (by lia) _ (by lia) (fun ⟨h2a, h2b, h2c⟩ ↦ ?_) ?_
  · have h2 : (2 : ℤ) ∣ gcd a (gcd b c) :=
      dvd_gcd (by lia) (dvd_gcd (by lia) (by lia))
    rw [habc] at h2
    exact absurd h2 (by decide)
  · refine (twoadicAdmissible_congr ?_ ?_ ?_).1 (twoadicAdmissible_of_hasPointOver ha hp) <;>
      rw [Int.natCast_toNat_eq_self.2 (Int.emod_nonneg _ (by decide)), intCast_emod_sixtyFour]

/-- A condition at 2 whose tables keep the classes of the condition at 2
(`JPoints.IsTwoadicTable`) admits every point. -/
theorem TwoAdic.sound_of_isTwoadicTable {tw : TwoAdic} {coeffs : Array ℤ}
    (h : IsTwoadicTable coeffs tw.mask2 tw.alive2) : tw.Sound coeffs.toList where
  alive2 := @fun _ _ _ _ ha habc hp ↦ (h.getLsbD_and_getElem! ha habc hp).2
  mask2 := @fun _ _ _ _ ha habc hp ↦ (h.getLsbD_and_getElem! ha habc hp).1

/-- A condition at 2 that the sieve does not use admits every point. -/
theorem TwoAdic.sound_of_use2_eq_false {tw : TwoAdic} (h : tw.use2 = false) (cs : List ℤ) :
    tw.Sound cs where
  alive2 h2 := by simp [h] at h2
  mask2 h2 := by simp [h] at h2

/-- The condition at 2 when the program starts, unused, admits every point. -/
theorem TwoAdic.sound_initial (cs : List ℤ) : TwoAdic.initial.Sound cs :=
  sound_of_use2_eq_false rfl cs

end JPoints

end
