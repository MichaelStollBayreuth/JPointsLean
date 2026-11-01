/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TubeApprox
public import JPoints.Proof.TwoAdic

import JPoints.Proof.CellSizes
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import Mathlib.Tactic.IntervalCases

/-!
# The polynomials of a first coordinate in doubles

What `tube_a_init` computes for the first coordinate `a` (`JPoints.tubeAInit`), as approximations
of the Kummer polynomials: the coefficients of `K0` and `K1`, from `mpz_get_d` of the
coefficients of `K₀` and of the curve and the powers of `A = (double)a`, within six roundings, those
of `K2 = b² - 4 a c` within one, the bound `th = (double)W` within one and `th2 = th * th` within
three, and the coefficients of the absolute polynomial `KA = |K0| + th |K1| + th2 |K2|` within ten
(`JPoints.TubeApprox`). The exact coefficients are arrays of the coefficients
(`JPoints.coeffArray`) of `JPoints.k0Coeff`, `JPoints.k1Coeff` and `JPoints.k2Coeff`, which give
the Kummer polynomials of the specification (`JPoints.eval2_k0Coeff`, `JPoints.eval2_k1Coeff`,
`JPoints.eval2_k2Coeff`). `tube_ok`, the value of `KA` at `(H, H + 64)` below `TUBE_BIG`, makes
all of them finite and bounds the absolute polynomial there by `2 ^ 998`
(`JPoints.TubeApprox.of_tubeOk`).

## Main definitions

* `JPoints.coeffArray`: the array of the coefficients of a polynomial in two variables.
* `JPoints.k0Coeff`, `JPoints.k1Coeff`, `JPoints.k2Coeff`, `JPoints.kaCoeff`: the coefficients of
  the Kummer polynomials of a first coordinate and of their absolute polynomial.
* `JPoints.TubeApprox`: the approximations of the polynomials of a first coordinate.

## Main statements

* `JPoints.eval2_k0Coeff`, `JPoints.eval2_k1Coeff`, `JPoints.eval2_k2Coeff`,
  `JPoints.eval2_kaCoeff`: the exact polynomials.
* `JPoints.Double.approxCoeffs_tubeK0`, `JPoints.Double.approxCoeffs_tubeK1`,
  `JPoints.Double.approxCoeffs_tubeK2`, `JPoints.Double.approxCoeffs_tubeKA`: the doubles of
  `tube_a_init`.
* `JPoints.TubeApprox.of_tubeOk`: what `tube_ok` gives.

## Implementation notes

The value of `KA` at `(H, H + 64)` is a sum of terms without a sign bit
(`JPoints.Double.signBit_add`, `JPoints.Double.signBit_mul`): absolute values times the positive
`th`, `th2` and powers of `H` and `H + 64`, so that neither a NaN nor `-∞`. Below the finite
`TUBE_BIG` it is finite (`JPoints.Double.isFinite_of_lt`), and then so is every term and every
operand of a term (`JPoints.Double.isFinite_and_of_isFinite_add`,
`JPoints.Double.isFinite_and_of_isFinite_mul`), which makes every coefficient of `K0`, `K1` and
`KA` finite; the coefficients of `K2` and the bounds are finite by their size. The entries of the
arrays of `tube_a_init` are read position by position, the comparisons of the indices `P(j, k)`
decided for every `L = JPoints.coeffRow ≥ 5`.
-/

@[expose] public section

namespace JPoints

open Finset

/-- The array of the coefficients `φ j k` of `s ^ j t ^ k` of a polynomial in two variables at the
indices `P(j, k)`, `j, k < L`, as the analysis of the tube keeps them. -/
def coeffArray (φ : ℕ → ℕ → ℚ) : Array ℚ :=
  Array.ofFn fun i : Fin numCoeffs ↦ φ (i / coeffRow) (i % coeffRow)

theorem size_coeffArray (φ : ℕ → ℕ → ℚ) : (coeffArray φ).size = numCoeffs :=
  Array.size_ofFn

theorem getElem!_coeffArray (φ : ℕ → ℕ → ℚ) {j k : ℕ} (hj : j < coeffRow) (hk : k < coeffRow) :
    (coeffArray φ)[coeffIndex j k]! = φ j k := by
  rw [coeffArray, getElem!_pos _ _ (by simpa using coeffIndex_lt_numCoeffs hj hk),
    Array.getElem_ofFn]
  simp only [coeffIndex, Nat.mul_add_div (show 0 < coeffRow by lia), Nat.div_eq_of_lt hk,
    Nat.add_zero, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hk]

theorem nonneg_getElem!_coeffArray {φ : ℕ → ℕ → ℚ} (hφ : ∀ j k, 0 ≤ φ j k) (i : ℕ) :
    0 ≤ (coeffArray φ)[i]! := by
  by_cases hi : i < numCoeffs
  · rw [coeffArray, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
    exact hφ _ _
  · rw [getElem!_neg _ _ (by simpa [coeffArray] using hi)]
    exact le_rfl

theorem eval2_coeffArray (φ : ℕ → ℕ → ℚ) {deg : ℕ} (hdeg : deg < coeffRow) (s t : ℚ) :
    eval2 (coeffArray φ) deg s t =
      ∑ j ∈ range (deg + 1), ∑ k ∈ range (deg - j + 1), φ j k * s ^ j * t ^ k :=
  sum_congr rfl fun j hj ↦ sum_congr rfl fun k hk ↦ by
    simp only [mem_range] at hj hk
    rw [getElem!_coeffArray φ (by lia) (by lia)]

/-- The coefficient of `b ^ j c ^ k` of `K₀` for the first coordinate `a`, the coefficient
`k_{i j k}` of `aⁱ bʲ cᵏ` (`JPoints.KummerCoeffs.coeff`) times `aⁱ` for `i = 4 - j - k`, and
`0` for `j + k > 4`. -/
def k0Coeff (K : KummerCoeffs) (a : ℤ) (j k : ℕ) : ℚ :=
  if j + k ≤ 4 then K.coeff (4 - j - k) j * a ^ (4 - j - k) else 0

/-- The coefficient of `b ^ j c ^ k` of
`K₁ = -2 (2 f₀ a³ + f₁ a² b + 2 f₂ a² c + f₃ a b c + 2 f₄ a c² + f₅ b c² + 2 f₆ c³)`
(`JPoints.kummerK1`) for the first coordinate `a` and the coefficients `fₙ = c[n]`. -/
def k1Coeff (c : Array ℤ) (a : ℤ) : ℕ → ℕ → ℚ
  | 0, 0 => -4 * c[0]! * a ^ 3 | 1, 0 => -2 * c[1]! * a ^ 2 | 0, 1 => -4 * c[2]! * a ^ 2
  | 1, 1 => -2 * c[3]! * a | 0, 2 => -4 * c[4]! * a | 1, 2 => -2 * c[5]! | 0, 3 => -4 * c[6]!
  | _, _ => 0

/-- The coefficient of `b ^ j c ^ k` of `K₂ = b² - 4 a c` (`JPoints.kummerK2`) for the first
coordinate `a`. -/
def k2Coeff (a : ℤ) : ℕ → ℕ → ℚ
  | 2, 0 => 1 | 0, 1 => -4 * a | _, _ => 0

/-- The coefficient of `b ^ j c ^ k` of the absolute polynomial `|K₀| + W |K₁| + W² |K₂|`, the
scale of the errors of the analysis of the tube, for the first coordinate `a` and the bound `W`
on the fourth coordinate. -/
def kaCoeff (K : KummerCoeffs) (c : Array ℤ) (W a : ℤ) (j k : ℕ) : ℚ :=
  |k0Coeff K a j k| + W * |k1Coeff c a j k| + W ^ 2 * |k2Coeff a j k|

theorem eval2_kaCoeff (K : KummerCoeffs) (c : Array ℤ) (W a : ℤ) {deg : ℕ} (hdeg : deg < coeffRow)
    (s t : ℚ) :
    eval2 (coeffArray (kaCoeff K c W a)) deg s t =
      eval2 (coeffArray fun j k ↦ |k0Coeff K a j k|) deg s t +
        W * eval2 (coeffArray fun j k ↦ |k1Coeff c a j k|) deg s t +
        W ^ 2 * eval2 (coeffArray fun j k ↦ |k2Coeff a j k|) deg s t := by
  simp only [eval2_coeffArray _ hdeg, kaCoeff, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

theorem eval2_k0Coeff (coeffs : Array ℤ) (a b c : ℤ) :
    eval2 (coeffArray (k0Coeff (kummerInit coeffs) a)) 4 b c =
      kummerK0 (coeffs.toList.getD · 0) a b c := by
  rw [eval2_coeffArray _ (by lia [five_le_coeffRow])]
  simp only [sum_range_succ, sum_range_zero, k0Coeff, KummerCoeffs.coeff, kummerInit, kummerK0,
    Array.getD_toList_eq_getElem!]
  norm_num
  ring

theorem eval2_k1Coeff (coeffs : Array ℤ) (a b c : ℤ) :
    eval2 (coeffArray (k1Coeff coeffs a)) 3 b c = kummerK1 (coeffs.toList.getD · 0) a b c := by
  rw [eval2_coeffArray _ (by lia [five_le_coeffRow])]
  simp only [kummerK1, Array.getD_toList_eq_getElem!]
  simp [sum_range_succ, k1Coeff]
  ring

theorem eval2_k2Coeff (a b c : ℤ) : eval2 (coeffArray (k2Coeff a)) 2 b c = kummerK2 a b c := by
  rw [eval2_coeffArray _ (by lia [five_le_coeffRow])]
  simp [sum_range_succ, k2Coeff, kummerK2]
  ring

end JPoints

namespace JPoints

namespace Double

/-- The powers `a ^ (m + 1)`, `m ≤ 3`, of the double `A = (double)a` of `|a| ≤ MAX_HEIGHT` by
repeated products, as `tube_a_init` computes them, approximate `a ^ (m + 1)` within `m`
roundings. -/
theorem approx_iterate_mul_ofInt {a : ℤ} (ha : |a| ≤ maxHeight) {m : ℕ} (hm : m ≤ 3) :
    ((· * ofInt a)^[m] (ofInt a)).Approx (a * a ^ m) |(a : ℚ) * a ^ m| m 0 := by
  have h32 : |(a : ℚ)| ≤ 2 ^ 32 := by
    rw [← Int.cast_abs]; exact mod_cast ha.trans (by lia [maxHeight_lt_two_pow_32])
  have hA := approx_ofInt (z := a) (by lia [maxHeight_lt_two_pow_32])
  have := hA.iterate_mul hA m (fun i hi ↦ ?_) (by lia)
  · simpa [abs_mul, abs_pow] using this
  have h1 : |(a : ℚ)| * |(a : ℚ)| ^ i ≤ (2 ^ 32) ^ 4 := by
    rw [← pow_succ']
    exact (pow_le_pow_left₀ (abs_nonneg _) h32 _).trans
      (pow_le_pow_right₀ (by norm_num) (by lia))
  calc (1 + 1 / 2 ^ 53 : ℚ) ^ (0 + i) * (|(a : ℚ)| * |(a : ℚ)| ^ i) ≤ 2 * (2 ^ 32) ^ 4 :=
        mul_le_mul (one_add_pow_le_two (by lia)) h1 (by positivity) (by norm_num)
    _ = 2 ^ 129 := by rw [← pow_mul, ← pow_succ']
    _ < 2 ^ 1022 := pow_lt_pow_right₀ (by norm_num) (by norm_num)

-- An entry `kd · A ^ (m + 1)` of `K0`: `mpz_get_d` within two roundings, the power within `m`.
private theorem approx_mpzGetD_mul {z : ℤ} {y : Double} {w : ℚ} {n : ℕ} (hy : y.Approx w |w| n 0)
    (hn : n ≤ 3) (hf : (mpzGetD z * y).isFinite = true) {v : ℚ} (hv : (z : ℚ) * w = v) :
    (mpzGetD z * y).Approx v |v| 6 53 := by
  have := (approx_mpzGetD (isFinite_and_of_isFinite_mul hf).1).mul hy (by norm_num) hf
  rw [← abs_mul, hv] at this
  exact this.mono le_rfl (by lia) le_rfl

theorem run_tubeInitCoeffs (curve : SearchCurve) (K : KummerCoeffs) :
    (tubeInitCoeffs curve K).run = ⟨mpzGetD K.k400, mpzGetD K.k310, mpzGetD K.k301,
      mpzGetD K.k220, mpzGetD K.k211, mpzGetD K.k202, mpzGetD K.k130, mpzGetD K.k121,
      mpzGetD K.k112, mpzGetD K.k103, mpzGetD K.k040, mpzGetD K.k031, mpzGetD K.k022,
      mpzGetD K.k013, mpzGetD K.k004,
      #[mpzGetD curve.coeffs[0]!, mpzGetD curve.coeffs[1]!, mpzGetD curve.coeffs[2]!,
        mpzGetD curve.coeffs[3]!, mpzGetD curve.coeffs[4]!, mpzGetD curve.coeffs[5]!,
        mpzGetD curve.coeffs[6]!]⟩ := by
  simp [tubeInitCoeffs, List.range']
  rfl

/-- Approximations of the coefficients `φ j k` of degree at most `deg < L` of a polynomial, each
with its absolute value as its majorant, approximate the arrays of the coefficients and of their
absolute values (`JPoints.coeffArray`). -/
theorem ApproxCoeffs.of_forall {p : Array Double} {φ : ℕ → ℕ → ℚ} {deg n g : ℕ}
    (hdeg : deg < coeffRow)
    (h : ∀ ⦃j k : ℕ⦄, j + k ≤ deg → (p[coeffIndex j k]!).Approx (φ j k) |φ j k| n g) :
    ApproxCoeffs p (coeffArray φ) (coeffArray fun j k ↦ |φ j k|) deg n g := fun j k hjk ↦ by
  rw [getElem!_coeffArray _ (by lia) (by lia), getElem!_coeffArray _ (by lia) (by lia)]
  exact h hjk

-- The powers `A`, `A²`, `A³`, `A⁴` of `A = (double)a` as `tube_a_init` computes them.
private theorem approx_powers {a : ℤ} (ha : |a| ≤ maxHeight) :
    (ofInt a).Approx (a * a ^ 0) |(a : ℚ) * a ^ 0| 0 0 ∧
      (ofInt a * ofInt a).Approx (a * a ^ 1) |(a : ℚ) * a ^ 1| 1 0 ∧
      (ofInt a * ofInt a * ofInt a).Approx (a * a ^ 2) |(a : ℚ) * a ^ 2| 2 0 ∧
      (ofInt a * ofInt a * ofInt a * ofInt a).Approx (a * a ^ 3) |(a : ℚ) * a ^ 3| 3 0 :=
  ⟨approx_iterate_mul_ofInt ha (m := 0) (by norm_num),
    approx_iterate_mul_ofInt ha (m := 1) (by norm_num),
    approx_iterate_mul_ofInt ha (m := 2) (by norm_num),
    approx_iterate_mul_ofInt ha (m := 3) (by norm_num)⟩

private theorem approx_mpzGetD_six {z : ℤ} (hf : (mpzGetD z).isFinite = true) {v : ℚ}
    (hv : (z : ℚ) = v) : (mpzGetD z).Approx v |v| 6 53 :=
  hv ▸ (approx_mpzGetD hf).mono le_rfl (by norm_num) le_rfl

theorem five_mul_coeffRow_le : 5 * coeffRow ≤ numCoeffs :=
  Nat.mul_le_mul_right _ five_le_coeffRow

/-- The coefficients of `K0` that `tube_a_init` sets for the first coordinate `a`, `|a| ≤
MAX_HEIGHT`, when finite, approximate those of `K₀` (`JPoints.k0Coeff`) within six roundings: two
of `mpz_get_d`, up to three of a power of `A`, and one of the product. -/
theorem approxCoeffs_tubeK0 {kd : TubeCoeffs} {curve : SearchCurve} {K : KummerCoeffs}
    (hkd : kd = (tubeInitCoeffs curve K).run) {a : ℤ} (ha : |a| ≤ maxHeight)
    (hf : ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeK0 kd a)[coeffIndex j k]!).isFinite = true) :
    ApproxCoeffs (tubeK0 kd a) (coeffArray (k0Coeff K a))
      (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 6 53 := by
  refine .of_forall (by lia [five_le_coeffRow]) fun j k hjk ↦ ?_
  have hf' := hf hjk
  obtain ⟨h1, h2, h3, h4⟩ := approx_powers ha
  obtain ⟨hj, hk, h5, hn⟩ : j ≤ 4 ∧ k ≤ 4 - j ∧ 5 ≤ coeffRow ∧ 5 * coeffRow ≤ numCoeffs :=
    ⟨by lia, by lia, five_le_coeffRow, five_mul_coeffRow_le⟩
  interval_cases j <;> interval_cases k <;>
    simp (disch := (simp only [coeffIndex, Array.size_set!, Array.size_replicate]; lia)) only
      [hkd, run_tubeInitCoeffs, tubeK0, tubeAInitK0, Array.getElem!_set!_ne,
        Array.getElem!_set!_self] at hf' ⊢ <;>
    first
      | with_reducible refine approx_mpzGetD_mul h4 (by norm_num) ?_ ?_
      | with_reducible refine approx_mpzGetD_mul h3 (by norm_num) ?_ ?_
      | with_reducible refine approx_mpzGetD_mul h2 (by norm_num) ?_ ?_
      | with_reducible refine approx_mpzGetD_mul h1 (by norm_num) ?_ ?_
      | with_reducible refine approx_mpzGetD_six ?_ ?_
  all_goals first
    | exact hf'
    | simp only [k0Coeff, KummerCoeffs.coeff]; push_cast; ring

theorem approx_neg_four : (-4.0 : Double).Approx (-4) |(-4 : ℚ)| 0 0 :=
  .of_toRat_eq (by decide +kernel) (by decide +kernel) (mod_cast OnGrid.intCast (-4))

theorem approx_neg_two : (-2.0 : Double).Approx (-2) |(-2 : ℚ)| 0 0 :=
  .of_toRat_eq (by decide +kernel) (by decide +kernel) (mod_cast OnGrid.intCast (-2))

-- An entry `c A ^ (m + 1) f` of `K1`: the exact `c`, the power within `m` roundings, the
-- products within two, `mpz_get_d` within two.
private theorem approx_mul_mul_mpzGetD {c y : Double} {C w : ℚ} {n : ℕ} {z : ℤ}
    (hc : c.Approx C |C| 0 0) (hy : y.Approx w |w| n 0) (hn : n ≤ 2)
    (hf : (c * y * mpzGetD z).isFinite = true) {v : ℚ} (hv : C * w * z = v) :
    (c * y * mpzGetD z).Approx v |v| 6 53 := by
  obtain ⟨h1, h2⟩ := isFinite_and_of_isFinite_mul hf
  have := ((hc.mul hy (by norm_num) h1).mul (approx_mpzGetD h2) (by norm_num) hf)
  rw [← abs_mul, ← abs_mul, hv] at this
  exact this.mono le_rfl (by lia) le_rfl

-- An entry `c f` of `K1`.
private theorem approx_mul_mpzGetD {c : Double} {C : ℚ} {z : ℤ} (hc : c.Approx C |C| 0 0)
    (hf : (c * mpzGetD z).isFinite = true) {v : ℚ} (hv : C * z = v) :
    (c * mpzGetD z).Approx v |v| 6 53 := by
  have := hc.mul (approx_mpzGetD (isFinite_and_of_isFinite_mul hf).2) (by norm_num) hf
  rw [← abs_mul, hv] at this
  exact this.mono le_rfl (by lia) le_rfl

theorem getElem!_replicate_zero (n i : ℕ) : (Array.replicate n (0.0 : Double))[i]! = 0.0 := by
  by_cases h : i < n
  · simp [h]
  · rw [getElem!_neg _ i (by simpa using h)]
    rfl

-- A coefficient `0.0` that `tube_a_init` leaves.
private theorem approx_zero_of_eq {n g : ℕ} {v : ℚ} (hv : 0 = v) :
    (0.0 : Double).Approx v |v| n g :=
  hv ▸ (Approx.of_toRat_eq isFinite_zero toRat_zero (.zero g)).mono (by simp) (Nat.zero_le n)
    le_rfl

/-- The coefficients of `K1` that `tube_a_init` sets for the first coordinate `a`, `|a| ≤
MAX_HEIGHT`, when finite, approximate those of `K₁` (`JPoints.k1Coeff`) within six roundings: two
of `mpz_get_d`, up to two of a power of `A`, and two of the products. -/
theorem approxCoeffs_tubeK1 {kd : TubeCoeffs} {curve : SearchCurve} {K : KummerCoeffs}
    (hkd : kd = (tubeInitCoeffs curve K).run) {a : ℤ} (ha : |a| ≤ maxHeight)
    (hf : ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeK1 kd a)[coeffIndex j k]!).isFinite = true) :
    ApproxCoeffs (tubeK1 kd a) (coeffArray (k1Coeff curve.coeffs a))
      (coeffArray fun j k ↦ |k1Coeff curve.coeffs a j k|) 4 6 53 := by
  refine .of_forall (by lia [five_le_coeffRow]) fun j k hjk ↦ ?_
  have hf' := hf hjk
  obtain ⟨⟨h1, h2, h3, -⟩, c4, c2⟩ :=
    And.intro (approx_powers ha) (And.intro approx_neg_four approx_neg_two)
  obtain ⟨hj, hk, h5, hn⟩ : j ≤ 4 ∧ k ≤ 4 - j ∧ 5 ≤ coeffRow ∧ 5 * coeffRow ≤ numCoeffs :=
    ⟨by lia, by lia, five_le_coeffRow, five_mul_coeffRow_le⟩
  interval_cases j <;> interval_cases k <;>
    simp (disch := (simp only [coeffIndex, Array.size_set!, Array.size_replicate]; lia)) only
      [hkd, run_tubeInitCoeffs, tubeK1, tubeAInitK1K2, Array.getElem!_set!_ne,
        Array.getElem!_set!_self, getElem!_replicate_zero, List.getElem!_toArray,
        List.getElem!_cons_succ, List.getElem!_cons_zero] at hf' ⊢ <;>
    first
      | with_reducible refine approx_mul_mul_mpzGetD (by assumption) h3 (by norm_num) ?_ ?_
      | with_reducible refine approx_mul_mul_mpzGetD (by assumption) h2 (by norm_num) ?_ ?_
      | with_reducible refine approx_mul_mul_mpzGetD (by assumption) h1 (by norm_num) ?_ ?_
      | with_reducible refine approx_mul_mpzGetD (by assumption) ?_ ?_
      | with_reducible exact approx_zero_of_eq (by simp only [k1Coeff])
  all_goals first
    | exact hf'
    | simp only [k1Coeff]; push_cast; ring

-- The coefficient `-4.0 * A` of `K2`.
private theorem approx_neg_four_mul_ofInt {a : ℤ} (ha : |a| ≤ maxHeight) :
    ((-4.0 : Double) * ofInt a).Approx (-4 * a) |-4 * (a : ℚ)| 1 0 := by
  have h32 : |(a : ℚ)| ≤ 2 ^ 32 := by
    rw [← Int.cast_abs]; exact mod_cast ha.trans (by lia [maxHeight_lt_two_pow_32])
  have h := approx_neg_four.mul_of_lt (approx_ofInt (z := a) (by lia [maxHeight_lt_two_pow_32]))
    (by norm_num) (by
      calc (1 + 1 / 2 ^ 53 : ℚ) ^ (0 + 0) * (|(-4 : ℚ)| * |(a : ℚ)|) ≤ 4 * 2 ^ 32 := by
            norm_num; linarith
        _ = 2 ^ 34 := by norm_num
        _ < 2 ^ 1022 := pow_lt_pow_right₀ (by norm_num) (by norm_num))
  rwa [← abs_mul] at h

/-- The coefficients of `K2` that `tube_a_init` sets for the first coordinate `a`, `|a| ≤
MAX_HEIGHT`, approximate those of `K₂ = b² - 4 a c` (`JPoints.k2Coeff`) within one rounding, of
`-4.0 * A`. -/
theorem approxCoeffs_tubeK2 (kd : TubeCoeffs) {a : ℤ} (ha : |a| ≤ maxHeight) :
    ApproxCoeffs (tubeK2 kd a) (coeffArray (k2Coeff a)) (coeffArray fun j k ↦ |k2Coeff a j k|)
      4 1 0 := by
  refine .of_forall (by lia [five_le_coeffRow]) fun j k hjk ↦ ?_
  have h1 := approx_neg_four_mul_ofInt ha
  obtain ⟨hj, hk, h5, hn⟩ : j ≤ 4 ∧ k ≤ 4 - j ∧ 5 ≤ coeffRow ∧ 5 * coeffRow ≤ numCoeffs :=
    ⟨by lia, by lia, five_le_coeffRow, five_mul_coeffRow_le⟩
  interval_cases j <;> interval_cases k <;>
    simp (disch := (simp only [coeffIndex, Array.size_set!, Array.size_replicate]; lia)) only
      [tubeK2, tubeAInitK1K2, Array.getElem!_set!_ne, Array.getElem!_set!_self,
        getElem!_replicate_zero] <;>
    first
      | exact approx_zero_of_eq (by simp [k2Coeff])
      | exact (Approx.of_toRat_eq isFinite_one toRat_one (.intCast 1)).mono (by simp [k2Coeff])
          (by norm_num) le_rfl
      | simpa [k2Coeff] using h1

/-- The bound `th = (double)W` on the fourth coordinate, `1 ≤ W < 2 ^ 63`, approximates `W` within
one rounding, and its square `th2 = th * th` approximates `W²` within three. -/
theorem approx_ofInt_and_ofInt_mul_ofInt {W : ℤ} (hW : 1 ≤ W) (hW' : W < 2 ^ 63) :
    (ofInt W).Approx W W 1 0 ∧ (ofInt W * ofInt W).Approx (W * W) (W * W) 3 0 := by
  have h1 : (1 : ℚ) ≤ W := mod_cast hW
  have h0 : |(W : ℚ)| = W := abs_of_nonneg (by linarith)
  have h63 : (W : ℚ) < 2 ^ 63 := mod_cast hW'
  have hlt : (2 : ℚ) ^ 63 < 2 ^ 1022 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h := approx_ofInt_of_lt (z := W) (by rw [h0]; exact h63.trans hlt)
  rw [h0] at h
  refine ⟨h, h.mul_of_lt h (by norm_num) ?_⟩
  have : (W : ℚ) * W < 2 ^ 63 * 2 ^ 63 := mul_lt_mul'' h63 h63 (by linarith) (by linarith)
  calc (1 + 1 / 2 ^ 53 : ℚ) ^ (1 + 1) * (W * W) ≤ 2 * (2 ^ 63 * 2 ^ 63) :=
        mul_le_mul (one_add_pow_le_two (by norm_num)) this.le (by positivity) (by norm_num)
    _ = 2 ^ 127 := by norm_num
    _ < 2 ^ 1022 := pow_lt_pow_right₀ (by norm_num) (by norm_num)

/-- The coefficients of `KA` that `tube_a_init` sets for the first coordinate `a`, when finite, from
approximations of `K0`, `K1` and `K2` and of `W ≥ 0` and `W²` by `th` and `th2`, approximate those
of the absolute polynomial `|K₀| + W |K₁| + W² |K₂|` (`JPoints.kaCoeff`), each its own majorant,
within ten roundings. -/
theorem approxCoeffs_tubeKA {kd : TubeCoeffs} {th th2 : Double} {K : KummerCoeffs} {c : Array ℤ}
    {W a : ℤ}
    (h0 : ApproxCoeffs (tubeK0 kd a) (coeffArray (k0Coeff K a))
      (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 6 53)
    (h1 : ApproxCoeffs (tubeK1 kd a) (coeffArray (k1Coeff c a))
      (coeffArray fun j k ↦ |k1Coeff c a j k|) 4 6 53)
    (h2 : ApproxCoeffs (tubeK2 kd a) (coeffArray (k2Coeff a))
      (coeffArray fun j k ↦ |k2Coeff a j k|) 4 1 0)
    (hth : th.Approx W W 1 0) (hth2 : th2.Approx (W * W) (W * W) 3 0)
    (hf : ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeKA kd th th2 a)[coeffIndex j k]!).isFinite = true) :
    ApproxCoeffs (tubeKA kd th th2 a) (coeffArray (kaCoeff K c W a))
      (coeffArray (kaCoeff K c W a)) 4 10 53 := by
  intro j k hjk
  have h5 := five_le_coeffRow
  have hl := coeffIndex_lt_numCoeffs (j := j) (k := k) (by lia) (by lia)
  have hf' := hf hjk
  rw [getElem!_tubeKA hl] at hf' ⊢
  obtain ⟨hs, hp2⟩ := isFinite_and_of_isFinite_add hf'
  obtain ⟨-, hp1⟩ := isFinite_and_of_isFinite_add hs
  have e0 := (h0 hjk).fabs
  have e1 := (hth.mul (h1 hjk).fabs (by norm_num) hp1).mono le_rfl le_rfl
    (by norm_num : 0 + 53 ≤ 53)
  have e2 := (hth2.mul (h2 hjk).fabs (by norm_num) hp2).mono le_rfl le_rfl
    (by norm_num : 0 + 0 ≤ 53)
  have := (e0.add e1 (by norm_num) hs).add e2 (by norm_num) hf'
  simp only [getElem!_coeffArray _ (show j < coeffRow by lia) (show k < coeffRow by lia),
    ] at this ⊢
  rw [kaCoeff, sq]
  exact this.mono le_rfl (by norm_num) le_rfl

/-! ### The signs of the absolute polynomial -/

private theorem le_or_iff {n : ℕ} : 2 ^ 63 ≤ n ||| 2 ^ 51 ↔ 2 ^ 63 ≤ n := by
  have h (m : ℕ) : 2 ^ 63 ≤ m ↔ 0 < m >>> 63 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_pos_iff]; simp
  rw [h, h, Nat.shiftRight_or_distrib, show (2 : ℕ) ^ 51 >>> 63 = 0 by decide, Nat.or_zero]

theorem signBit_quiet (x : Double) : x.quiet.signBit = x.signBit := by
  rw [signBit_eq_decide, signBit_eq_decide]
  simp only [quiet, UInt64.toNat_or, show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 from rfl]
  exact decide_eq_decide.mpr le_or_iff

theorem signBit_propagateNaN {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false) :
    (propagateNaN x y).signBit = false := by
  simp only [propagateNaN]
  split_ifs <;> rwa [signBit_quiet]

theorem fst_toDyadic_nonneg {x : Double} (hx : x.signBit = false) : 0 ≤ x.toDyadic.1 := by
  simp only [toDyadic, hx, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> positivity

/-- A sum of doubles without a sign bit has no sign bit: the infinities are `+∞`, a NaN keeps the
sign of its operand, and the exact sum of finite operands is not negative. -/
theorem signBit_add {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false) :
    (x + y).signBit = false := by
  change (add x y).signBit = false
  simp only [add]
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact signBit_propagateNaN hx hy
  · simp [hx, hy] at h3
  · exact hx
  · exact hy
  · simp [hx] at h6
  · rfl
  · rw [signBit_ofDyadic, decide_eq_false_iff_not, not_lt]
    exact add_nonneg (mul_nonneg (fst_toDyadic_nonneg hx) (by positivity))
      (mul_nonneg (fst_toDyadic_nonneg hy) (by positivity))

/-- A product of doubles without a sign bit, one of them finite and not zero, has no sign bit. -/
theorem signBit_mul {x y : Double} (hx : x.signBit = false) (hy : y.signBit = false)
    (h : x.isFinite = true ∧ x.isZero = false ∨ y.isFinite = true ∧ y.isZero = false) :
    (x * y).signBit = false := by
  change (mul x y).signBit = false
  simp only [mul, hx, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h1 h2 h3
  · exact signBit_propagateNaN hx hy
  · exfalso
    rcases h with ⟨hf, hz⟩ | ⟨hf, hz⟩ <;>
      simp_all [isInf_eq_false_of_isFinite, isZero_eq_false_of_isInf]
  · decide
  · exact signBit_ofDyadic ..

theorem signBit_foldl_add {β : Type*} {T : β → Double} {L : List β} {s : Double}
    (hs : s.signBit = false) (hT : ∀ t ∈ L, (T t).signBit = false) :
    (L.foldl (fun s t ↦ s + T t) s).signBit = false := by
  induction L generalizing s with
  | nil => exact hs
  | cons t L ih =>
    exact ih (signBit_add hs (hT t List.mem_cons_self)) fun t' ht' ↦
      hT t' (List.mem_cons_of_mem _ ht')

/-- A double without a sign bit below a finite double is finite: neither a NaN nor `+∞`. -/
theorem isFinite_of_lt {x y : Double} (hs : x.signBit = false) (hy : y.isFinite = true)
    (h : x.lt y = true) : x.isFinite = true := by
  have hn : x.isNaN = false := by
    simp only [lt, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  cases hi : x.isInf
  · exact isFinite_of_isInf_eq_false hn hi
  · rw [lt_eq_true_iff hn (isNaN_eq_false_of_isFinite hy), doubleValue_of_isInf hi, hs,
      doubleValue_eq_toRat hy] at h
    simp at h

/-- A finite double that approximates a positive `v` with `v` as its majorant within at most
`2 ^ 52` roundings is not zero. -/
theorem Approx.isZero_eq_false {x : Double} {v : ℚ} {n g : ℕ} (h : x.Approx v v n g) (hv : 0 < v)
    (hn : n ≤ 2 ^ 20) : x.isZero = false := by
  rw [isZero_eq_false_iff]
  have h1 := h.two_sub_pow_mul_le_toRat
  have h2 := one_add_pow_sub_one_le hn
  have h3 : (n : ℚ) ≤ 2 ^ 20 := mod_cast hn
  nlinarith

theorem signBit_iterate_mul {x y : Double} (hy : y.signBit = false) (hx : x.signBit = false)
    (hxf : x.isFinite = true) (hx0 : x.isZero = false) (j : ℕ) :
    ((· * x)^[j] y).signBit = false := by
  induction j with
  | zero => exact hy
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact signBit_mul ih hx (.inr ⟨hxf, hx0⟩)

-- The powers `x ^ j`, `j ≤ 4`, of `x = (double)X` for `1 ≤ X ≤ MAX_HEIGHT + 64` by repeated
-- products: finite, not zero, without a sign bit, approximating `X ^ j` within `j` roundings.
private theorem approx_iterate_mul_ofInt_one {X : ℤ} (h1 : 1 ≤ X) (h2 : X ≤ maxHeight + 64)
    {j : ℕ} (hj : j ≤ 4) :
    ((· * ofInt X)^[j] 1.0).Approx (X ^ j) (X ^ j) j j ∧
      ((· * ofInt X)^[j] 1.0).isZero = false ∧ ((· * ofInt X)^[j] 1.0).signBit = false := by
  have hX0 : (1 : ℚ) ≤ X := mod_cast h1
  have hX : |(X : ℚ)| = X := abs_of_nonneg (by linarith)
  have hx := (approx_ofInt (z := X) (by
    rw [abs_of_nonneg (by lia)]; lia [maxHeight_lt_two_pow_32])).mono le_rfl le_rfl (Nat.zero_le 1)
  have h := approx_iterate_mul_one (X := X) hx (by
    rw [hX]; exact (show (X : ℚ) ≤ 2 ^ 33 from mod_cast (by lia [maxHeight_lt_two_pow_32])).trans
      (pow_le_pow_right₀ (by norm_num) (by norm_num))) hj
  rw [hX] at h
  have hxz : (ofInt X).isZero = false := isZero_ofInt_eq_false (by lia)
  exact ⟨h, h.isZero_eq_false (by positivity) (by lia), signBit_iterate_mul (by decide)
    ((signBit_ofInt X).trans (by simp; lia)) hx.isFinite hxz j⟩

-- The bound `th = (double)W` and its square: approximations, finite, not zero, without a sign bit.
private theorem th_facts {th th2 : Double} {W : ℤ} (hth : th = ofInt W) (hth2 : th2 = th * th)
    (hW : 1 ≤ W) (hW' : W < 2 ^ 63) :
    th.Approx W W 1 0 ∧ th2.Approx (W * W) (W * W) 3 0 ∧ th.isZero = false ∧ th.signBit = false ∧
      th2.isZero = false ∧ th2.signBit = false := by
  subst hth hth2
  obtain ⟨h1, h2⟩ := approx_ofInt_and_ofInt_mul_ofInt hW hW'
  have hW0 : (0 : ℚ) < W := mod_cast (by lia : (0 : ℤ) < W)
  have hz := h1.isZero_eq_false hW0 (by norm_num)
  have hs : (ofInt W).signBit = false := (signBit_ofInt W).trans (by simp; lia)
  exact ⟨h1, h2, hz, hs, h2.isZero_eq_false (by positivity) (by norm_num),
    signBit_mul hs hs (.inl ⟨h1.isFinite, hz⟩)⟩

theorem signBit_getElem!_tubeKA {kd : TubeCoeffs} {th th2 : Double} {a : ℤ}
    (hth : th.isFinite = true ∧ th.isZero = false ∧ th.signBit = false)
    (hth2 : th2.isFinite = true ∧ th2.isZero = false ∧ th2.signBit = false) (i : ℕ) :
    ((tubeKA kd th th2 a)[i]!).signBit = false := by
  by_cases hi : i < numCoeffs
  · rw [getElem!_tubeKA hi]
    exact signBit_add (signBit_add (signBit_fabs _) (signBit_mul hth.2.2 (signBit_fabs _)
      (.inl ⟨hth.1, hth.2.1⟩))) (signBit_mul hth2.2.2 (signBit_fabs _) (.inl ⟨hth2.1, hth2.2.1⟩))
  · rw [getElem!_neg _ i (by simpa [size_tubeKA] using hi)]
    rfl

/-- `tube_eval` of a polynomial of degree 4 whose coefficients have no sign bit, at `(X, Y)` with
`1 ≤ X, Y ≤ MAX_HEIGHT + 64`, is finite when it is below `TUBE_BIG`: a sum of terms without a
sign bit is neither a NaN below `TUBE_BIG` nor `-∞`. -/
theorem isFinite_tubeEvalGen_of_lt {qa : Array Double} (hq : ∀ i : ℕ, (qa[i]!).signBit = false)
    {X Y : ℤ} (hX : 1 ≤ X) (hX' : X ≤ maxHeight + 64) (hY : 1 ≤ Y) (hY' : Y ≤ maxHeight + 64)
    (hok : (tubeEvalGen qa 4 (ofInt X) (ofInt Y)).lt tubeBig = true) :
    (tubeEvalGen qa 4 (ofInt X) (ofInt Y)).isFinite = true := by
  refine isFinite_of_lt (signBit_foldl_add (by decide) fun jk hjk ↦ ?_) isFinite_tubeBig hok
  have hjk' := mem_evalIndices.mp hjk
  obtain ⟨hx, hxz, hxs⟩ := approx_iterate_mul_ofInt_one hX hX' (j := jk.1) (by lia)
  obtain ⟨hy, hyz, hys⟩ := approx_iterate_mul_ofInt_one hY hY' (j := jk.2) (by lia)
  exact signBit_mul (signBit_mul (hq _) hxs (.inr ⟨hx.isFinite, hxz⟩)) hys (.inr ⟨hy.isFinite, hyz⟩)

theorem isFinite_getElem!_of_isFinite_tubeEvalGen {qa : Array Double} {deg : ℕ} {x y : Double}
    (hv : (tubeEvalGen qa deg x y).isFinite = true) {j k : ℕ} (hjk : j + k ≤ deg) :
    (qa[coeffIndex j k]!).isFinite = true :=
  (isFinite_and_of_isFinite_mul (isFinite_and_of_isFinite_mul
    ((isFinite_of_isFinite_foldl_add hv).2 (j, k) (mem_evalIndices.mpr hjk))).1).1

theorem isFinite_tubeK_of_isFinite_tubeKA {kd : TubeCoeffs} {th th2 : Double} {a : ℤ} {i : ℕ}
    (hi : i < numCoeffs) (h : ((tubeKA kd th th2 a)[i]!).isFinite = true) :
    ((tubeK0 kd a)[i]!).isFinite = true ∧ ((tubeK1 kd a)[i]!).isFinite = true := by
  rw [getElem!_tubeKA hi] at h
  obtain ⟨h1, -⟩ := isFinite_and_of_isFinite_add h
  obtain ⟨h2, h3⟩ := isFinite_and_of_isFinite_add h1
  exact ⟨(isFinite_fabs _).symm.trans h2,
    (isFinite_fabs _).symm.trans (isFinite_and_of_isFinite_mul h3).2⟩

/-- A double below `TUBE_BIG` that approximates `V` with `V` as its majorant within at most
`2 ^ 20` roundings bounds `V` by `2 ^ 998`, twice the bound of `TUBE_BIG`. -/
theorem Approx.lt_two_pow_of_lt_tubeBig {x : Double} {V : ℚ} {n g : ℕ} (h : x.Approx V V n g)
    (hn : n ≤ 2 ^ 20) (hlt : x.lt tubeBig = true) : V < 2 ^ 998 := by
  rw [lt_eq_true_iff (isNaN_eq_false_of_isFinite h.isFinite)
    (isNaN_eq_false_of_isFinite isFinite_tubeBig), doubleValue_eq_toRat h.isFinite,
    doubleValue_eq_toRat isFinite_tubeBig, WithBotTop.coe_lt_coe] at hlt
  have h1 := h.two_sub_pow_mul_le_toRat
  have h2 := one_add_pow_sub_one_le hn
  have h3 : (n : ℚ) ≤ 2 ^ 20 := mod_cast hn
  have h4 := toRat_tubeBig_le
  have h5 := h.nonneg
  have h6 : (1 : ℚ) / 2 * V ≤ (2 - (1 + 1 / 2 ^ 53) ^ n) * V :=
    mul_le_mul_of_nonneg_right (by nlinarith) h5
  calc V ≤ 2 * x.toRat := by linarith
    _ < 2 * 2 ^ 997 := mul_lt_mul_of_pos_left (hlt.trans_le h4) two_pos
    _ = 2 ^ 998 := (pow_succ' 2 997).symm

end Double

open Double

/-- The polynomials of the analysis of the tube for the first coordinate `a` with the coefficients
`kd` and the bound `th` on the fourth coordinate with its square `th2` approximate the Kummer
polynomials of the curve with the coefficients `c` and `K₀`'s coefficients `K`, and the bound `W`:
`K0` and `K1` within six roundings, `K2` within one, `KA` within ten (its exact coefficients
`JPoints.kaCoeff` their own majorants), `th` within one and `th2` within three. -/
structure TubeApprox (kd : TubeCoeffs) (th th2 : Double) (K : KummerCoeffs) (c : Array ℤ)
    (W a : ℤ) : Prop where
  /-- The coefficients of `K0`. -/
  k0 : ApproxCoeffs (tubeK0 kd a) (coeffArray (k0Coeff K a))
    (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 6 53
  /-- The coefficients of `K1`. -/
  k1 : ApproxCoeffs (tubeK1 kd a) (coeffArray (k1Coeff c a))
    (coeffArray fun j k ↦ |k1Coeff c a j k|) 4 6 53
  /-- The coefficients of `K2`. -/
  k2 : ApproxCoeffs (tubeK2 kd a) (coeffArray (k2Coeff a))
    (coeffArray fun j k ↦ |k2Coeff a j k|) 4 1 0
  /-- The coefficients of `KA`. -/
  ka : ApproxCoeffs (tubeKA kd th th2 a) (coeffArray (kaCoeff K c W a))
    (coeffArray (kaCoeff K c W a)) 4 10 53
  /-- The bound on the fourth coordinate. -/
  th : th.Approx W W 1 0
  /-- Its square. -/
  th2 : th2.Approx (W * W) (W * W) 3 0

-- What `tube_ok` gives: a finite value of `KA` at `(H, H + 64)` and finite coefficients of `KA`.
private theorem isFinite_of_tubeOk {kd : TubeCoeffs} {th th2 : Double} {a H : ℤ}
    (hth : th.isFinite = true ∧ th.isZero = false ∧ th.signBit = false)
    (hth2 : th2.isFinite = true ∧ th2.isZero = false ∧ th2.signBit = false) (hH : 1 ≤ H)
    (hHm : H ≤ maxHeight)
    (hok : (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).lt
      tubeBig = true) :
    (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).isFinite = true ∧
      ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeKA kd th th2 a)[coeffIndex j k]!).isFinite = true := by
  have hL : (longLength : ℤ) = 64 := rfl
  have hv := isFinite_tubeEvalGen_of_lt (signBit_getElem!_tubeKA hth hth2) hH (by lia) (by lia)
    (by lia) hok
  exact ⟨hv, fun _ _ hjk ↦ isFinite_getElem!_of_isFinite_tubeEvalGen hv hjk⟩

-- What `tube_ok` gives: the absolute polynomial at `(H, H + 64)` below `2 ^ 998`.
private theorem eval2_kaCoeff_lt_of_tubeOk {kd : TubeCoeffs} {th th2 : Double} {K : KummerCoeffs}
    {c : Array ℤ} {W a H : ℤ}
    (hka : ApproxCoeffs (tubeKA kd th th2 a) (coeffArray (kaCoeff K c W a))
      (coeffArray (kaCoeff K c W a)) 4 10 53)
    (hH : 1 ≤ H) (hHm : H ≤ maxHeight)
    (hv : (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).isFinite = true)
    (hok : (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).lt
      tubeBig = true) :
    eval2 (coeffArray (kaCoeff K c W a)) 4 H (H + longLength) < 2 ^ 998 := by
  have hL : (longLength : ℤ) = 64 := rfl
  have hb (z : ℤ) (h0 : 0 ≤ z) (h1 : z ≤ maxHeight + 64) :
      |(z : ℚ)| < 2 ^ 53 ∧ |(z : ℚ)| ≤ 2 ^ 200 := by
    rw [← Int.cast_abs, abs_of_nonneg h0]
    have : (z : ℚ) ≤ 2 ^ 33 := mod_cast (by lia [maxHeight_lt_two_pow_32])
    exact ⟨this.trans_lt (by norm_num), this.trans (pow_le_pow_right₀ (by norm_num) (by norm_num))⟩
  have hx := (approx_ofInt (z := H) (mod_cast (hb H (by lia) (by lia)).1)).mono le_rfl le_rfl
    (Nat.zero_le 1)
  have hy := (approx_ofInt (z := H + longLength) (mod_cast (hb _ (by lia) (by lia)).1)).mono
    le_rfl le_rfl (Nat.zero_le 1)
  have he := approx_tubeEvalGen hka hx hy (hb H (by lia) (by lia)).2 (hb _ (by lia) (by lia)).2
    le_rfl (by norm_num) hv
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at he
  push_cast at he
  exact he.lt_two_pow_of_lt_tubeBig (by decide) hok

/-- What `tube_ok` gives: when the value of `KA` at `(H, H + 64)`, `1 ≤ H ≤ MAX_HEIGHT`, is below
`TUBE_BIG`, the polynomials of the first coordinate `a`, `|a| ≤ MAX_HEIGHT`, for the bound
`th = (double)W`, `1 ≤ W < 2 ^ 63`, are finite and approximate the Kummer polynomials
(`JPoints.TubeApprox`), and the absolute polynomial at `(H, H + 64)` is below `2 ^ 998`: a sum of
terms without a sign bit below `TUBE_BIG` is finite, and so are its terms and their operands. -/
theorem TubeApprox.of_tubeOk {kd : TubeCoeffs} {curve : SearchCurve} {K : KummerCoeffs}
    (hkd : kd = (tubeInitCoeffs curve K).run) {th th2 : Double} {W H a : ℤ}
    (hth : th = ofInt W) (hth2 : th2 = th * th) (hW : 1 ≤ W) (hW' : W < 2 ^ 63) (hH : 1 ≤ H)
    (hHm : H ≤ maxHeight) (ha : |a| ≤ maxHeight)
    (hok : (tubeEval (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).run.lt
      tubeBig = true) :
    TubeApprox kd th th2 K curve.coeffs W a ∧
      eval2 (coeffArray (kaCoeff K curve.coeffs W a)) 4 H (H + longLength) < 2 ^ 998 := by
  obtain ⟨t1, t2, tz, ts, t2z, t2s⟩ := th_facts hth hth2 hW hW'
  rw [run_tubeEval] at hok
  obtain ⟨hv, hKA⟩ := isFinite_of_tubeOk ⟨t1.isFinite, tz, ts⟩ ⟨t2.isFinite, t2z, t2s⟩ hH hHm hok
  have hK {j k : ℕ} (hjk : j + k ≤ 4) := isFinite_tubeK_of_isFinite_tubeKA
    (coeffIndex_lt_numCoeffs (by lia [five_le_coeffRow]) (by lia [five_le_coeffRow])) (hKA hjk)
  have h0 := approxCoeffs_tubeK0 hkd ha fun _ _ hjk ↦ (hK hjk).1
  have h1 := approxCoeffs_tubeK1 hkd ha fun _ _ hjk ↦ (hK hjk).2
  have hka := approxCoeffs_tubeKA h0 h1 (approxCoeffs_tubeK2 kd ha) t1 t2 hKA
  exact ⟨⟨h0, h1, approxCoeffs_tubeK2 kd ha, hka, t1, t2⟩,
    eval2_kaCoeff_lt_of_tubeOk hka hH hHm hv hok⟩

end JPoints

end
