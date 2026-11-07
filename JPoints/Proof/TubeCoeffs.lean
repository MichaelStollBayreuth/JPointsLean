/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.TubeApprox
public import JPoints.Proof.TwoAdic

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

theorem nonneg_getElem!_coeffArray {φ : ℕ → ℕ → ℚ} (hφ : ∀ j k, 0 ≤ φ j k) (i : ℕ) :
    0 ≤ (coeffArray φ)[i]! := by
  by_cases hi : i < numCoeffs
  · rw [getElem!_coeffArray_of_lt φ hi]
    exact hφ _ _
  · rw [getElem!_neg _ _ (by simpa [size_coeffArray] using hi)]
    exact le_rfl

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

theorem k1Coeff_eq_zero (c : Array ℤ) (a : ℤ) {j k : ℕ} (h : 3 < j + k) : k1Coeff c a j k = 0 := by
  rcases j with _ | _ | j <;> rcases k with _ | _ | _ | _ | k <;> first | lia | rfl

/-- The coefficient of `b ^ j c ^ k` of `K₂ = b² - 4 a c` (`JPoints.kummerK2`) for the first
coordinate `a`. -/
def k2Coeff (a : ℤ) : ℕ → ℕ → ℚ
  | 2, 0 => 1 | 0, 1 => -4 * a | _, _ => 0

theorem k2Coeff_eq_zero (a : ℤ) {j k : ℕ} (h : 2 < j + k) : k2Coeff a j k = 0 := by
  rcases j with _ | _ | _ | j <;> rcases k with _ | _ | _ | k <;> first | lia | rfl

/-- The coefficient of `b ^ j c ^ k` of the absolute polynomial `|K₀| + W |K₁| + W² |K₂|`, the
scale of the errors of the analysis of the tube, for the first coordinate `a` and the bound `W`
on the fourth coordinate. -/
def kaCoeff (K : KummerCoeffs) (c : Array ℤ) (W a : ℤ) (j k : ℕ) : ℚ :=
  |k0Coeff K a j k| + W * |k1Coeff c a j k| + W ^ 2 * |k2Coeff a j k|

theorem nonneg_kaCoeff (K : KummerCoeffs) (c : Array ℤ) {W : ℤ} (hW : 0 ≤ W) (a : ℤ) (j k : ℕ) :
    0 ≤ kaCoeff K c W a j k := by
  have : (0 : ℚ) ≤ W := mod_cast hW
  rw [kaCoeff]
  positivity

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
  rw [eval2_coeffArray _ four_lt_coeffRow]
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

-- `Array.getElem!_replicate_default` in the form of the arrays of `tube_a_init`.
private theorem getElem!_replicate_zero (n i : ℕ) : (Array.replicate n (0.0 : Double))[i]! = 0.0 :=
  Array.getElem!_replicate_default n i

open Double in
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
  exact one_add_pow_mul_lt_two_pow_1022 (by lia) (by positivity)
    (h1.trans (by rw [← pow_mul]; exact pow_le_pow_right₀ one_le_two (by norm_num)))

-- An entry `kd · A ^ (m + 1)` of `K0`: `mpz_get_d` within two roundings, the power within `m`.
private theorem approx_mpzGetD_mul {z : ℤ} {y : Double} {w : ℚ} {n : ℕ} (hy : y.Approx w |w| n 0)
    (hn : n ≤ 3) (hf : (mpzGetD z * y).isFinite = true) {v : ℚ} (hv : (z : ℚ) * w = v) :
    (mpzGetD z * y).Approx v |v| 6 53 := by
  have := (approx_mpzGetD (isFinite_and_of_isFinite_mul hf).1).mul hy (by norm_num) hf
  rw [← abs_mul, hv] at this
  exact this.mono le_rfl (by lia) le_rfl

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

/-- The coefficients of `K0` that `tube_a_init` sets for the first coordinate `a`, `|a| ≤
MAX_HEIGHT`, when finite, approximate those of `K₀` (`JPoints.k0Coeff`) within six roundings: two
of `mpz_get_d`, up to three of a power of `A`, and one of the product. -/
theorem approxCoeffs_tubeK0 {kd : TubeCoeffs} {curve : SearchCurve} {K : KummerCoeffs}
    (hkd : kd = (tubeInitCoeffs curve K).run) {a : ℤ} (ha : |a| ≤ maxHeight)
    (hf : ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeK0 kd a)[coeffIndex j k]!).isFinite = true) :
    ApproxCoeffs (tubeK0 kd a) (coeffArray (k0Coeff K a))
      (coeffArray fun j k ↦ |k0Coeff K a j k|) 4 6 53 := by
  refine .of_forall four_lt_coeffRow fun j k hjk ↦ ?_
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

private theorem approx_neg_four : (-4.0 : Double).Approx (-4) |(-4 : ℚ)| 0 0 :=
  .of_toRat_eq (by decide +kernel) (by decide +kernel) (mod_cast OnGrid.intCast (-4))

private theorem approx_neg_two : (-2.0 : Double).Approx (-2) |(-2 : ℚ)| 0 0 :=
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
  refine .of_forall four_lt_coeffRow fun j k hjk ↦ ?_
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
    (by norm_num) (one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
      ((by norm_num; linarith : |(-4 : ℚ)| * |(a : ℚ)| ≤ 2 ^ 34).trans
        (pow_le_pow_right₀ one_le_two (by norm_num))))
  rwa [← abs_mul] at h

/-- The coefficients of `K2` that `tube_a_init` sets for the first coordinate `a`, `|a| ≤
MAX_HEIGHT`, approximate those of `K₂ = b² - 4 a c` (`JPoints.k2Coeff`) within one rounding, of
`-4.0 * A`. -/
theorem approxCoeffs_tubeK2 (kd : TubeCoeffs) {a : ℤ} (ha : |a| ≤ maxHeight) :
    ApproxCoeffs (tubeK2 kd a) (coeffArray (k2Coeff a)) (coeffArray fun j k ↦ |k2Coeff a j k|)
      4 1 0 := by
  refine .of_forall four_lt_coeffRow fun j k hjk ↦ ?_
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
one rounding. -/
theorem approx_ofInt_of_one_le {W : ℤ} (hW : 1 ≤ W) (hW' : W < 2 ^ 63) :
    (ofInt W).Approx W W 1 0 := by
  have h0 : |(W : ℚ)| = W := abs_of_nonneg (mod_cast (by lia : (0 : ℤ) ≤ W))
  have h63 : (W : ℚ) < 2 ^ 63 := mod_cast hW'
  have h := approx_ofInt_of_lt (z := W)
    (by rw [h0]; exact h63.trans (pow_lt_pow_right₀ (by norm_num) (by norm_num)))
  rwa [h0] at h

/-- The square `th2 = th * th` of the bound `th = (double)W` on the fourth coordinate,
`1 ≤ W < 2 ^ 63`, approximates `W²` within three roundings. -/
theorem approx_ofInt_mul_ofInt {W : ℤ} (hW : 1 ≤ W) (hW' : W < 2 ^ 63) :
    (ofInt W * ofInt W).Approx (W * W) (W * W) 3 0 := by
  have h1 : (1 : ℚ) ≤ W := mod_cast hW
  have h63 : (W : ℚ) < 2 ^ 63 := mod_cast hW'
  have h := approx_ofInt_of_one_le hW hW'
  refine h.mul_of_lt h (by norm_num) ?_
  have : (W : ℚ) * W < 2 ^ 63 * 2 ^ 63 := mul_lt_mul'' h63 h63 (by linarith) (by linarith)
  exact one_add_pow_mul_lt_two_pow_1022 (by norm_num) (by positivity)
    (this.le.trans (by rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by norm_num)))

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
  exact ⟨h, h.isZero_eq_false (by positivity) (by lia),
    signBit_iterate_mul_of_isFinite (signBit_ofInt_of_nonneg (by lia)) (by decide) h.isFinite⟩

-- The bound `th = (double)W` and its square: approximations, finite, not zero, without a sign bit.
private theorem th_facts {th th2 : Double} {W : ℤ} (hth : th = ofInt W) (hth2 : th2 = th * th)
    (hW : 1 ≤ W) (hW' : W < 2 ^ 63) :
    th.Approx W W 1 0 ∧ th2.Approx (W * W) (W * W) 3 0 ∧ th.isZero = false ∧ th.signBit = false ∧
      th2.isZero = false ∧ th2.signBit = false := by
  subst hth hth2
  have h1 := approx_ofInt_of_one_le hW hW'
  have h2 := approx_ofInt_mul_ofInt hW hW'
  have hW0 : (0 : ℚ) < W := mod_cast (by lia : (0 : ℤ) < W)
  exact ⟨h1, h2, h1.isZero_eq_false hW0 (by norm_num),
    signBit_eq_false_of_pos (h1.toRat_pos hW0 (by norm_num)),
    h2.isZero_eq_false (by positivity) (by norm_num),
    signBit_eq_false_of_pos (h2.toRat_pos (by positivity) (by norm_num))⟩

theorem signBit_getElem!_tubeKA {kd : TubeCoeffs} {th th2 : Double} {a : ℤ}
    (hthf : th.isFinite = true) (hthz : th.isZero = false) (hths : th.signBit = false)
    (hth2f : th2.isFinite = true) (hth2z : th2.isZero = false) (hth2s : th2.signBit = false)
    (i : ℕ) : ((tubeKA kd th th2 a)[i]!).signBit = false := by
  by_cases hi : i < numCoeffs
  · rw [getElem!_tubeKA hi]
    exact signBit_add (signBit_add (signBit_fabs _) (signBit_mul hths (signBit_fabs _)
      (.inl ⟨hthf, hthz⟩))) (signBit_mul hth2s (signBit_fabs _) (.inl ⟨hth2f, hth2z⟩))
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
  have h1 := h.div_two_le_toRat hn
  have h2 := ((lt_iff_toRat_lt h.isFinite isFinite_tubeBig).mp hlt).trans_le toRat_tubeBig_le
  calc V ≤ 2 * x.toRat := by linarith
    _ < 2 * 2 ^ 997 := mul_lt_mul_of_pos_left h2 two_pos
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
    (hthf : th.isFinite = true) (hthz : th.isZero = false) (hths : th.signBit = false)
    (hth2f : th2.isFinite = true) (hth2z : th2.isZero = false) (hth2s : th2.signBit = false)
    (hH : 1 ≤ H) (hHm : H ≤ maxHeight)
    (hok : (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).lt
      tubeBig = true) :
    (tubeEvalGen (tubeKA kd th th2 a) 4 (ofInt H) (ofInt (H + longLength))).isFinite = true ∧
      ∀ ⦃j k : ℕ⦄, j + k ≤ 4 → ((tubeKA kd th th2 a)[coeffIndex j k]!).isFinite = true := by
  have hL : (longLength : ℤ) = 64 := rfl
  have hv := isFinite_tubeEvalGen_of_lt
    (signBit_getElem!_tubeKA hthf hthz hths hth2f hth2z hth2s) hH (by lia) (by lia) (by lia) hok
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
  obtain ⟨hv, hKA⟩ := isFinite_of_tubeOk t1.isFinite tz ts t2.isFinite t2z t2s hH hHm hok
  have hK {j k : ℕ} (hjk : j + k ≤ 4) := isFinite_tubeK_of_isFinite_tubeKA
    (coeffIndex_lt_numCoeffs (by lia [five_le_coeffRow]) (by lia [five_le_coeffRow])) (hKA hjk)
  have h0 := approxCoeffs_tubeK0 hkd ha fun _ _ hjk ↦ (hK hjk).1
  have h1 := approxCoeffs_tubeK1 hkd ha fun _ _ hjk ↦ (hK hjk).2
  have hka := approxCoeffs_tubeKA h0 h1 (approxCoeffs_tubeK2 kd ha) t1 t2 hKA
  exact ⟨⟨h0, h1, approxCoeffs_tubeK2 kd ha, hka, t1, t2⟩,
    eval2_kaCoeff_lt_of_tubeOk hka hH hHm hv hok⟩

end JPoints

end
