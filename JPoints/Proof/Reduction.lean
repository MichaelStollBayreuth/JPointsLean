/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Admits
public import JPoints.Proof.Kummer
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Parity

import JPoints.Proof.Order
import Mathlib.Data.Nat.Bitwise
import Mathlib.FieldTheory.Finite.Basic

/-!
# The classes of the points modulo an odd prime

A point of the Kummer surface that comes from a rational point of the Jacobian reduces modulo every
odd prime `p` to a class that the references of the tables admit (`JPoints.refAdmits12_of_lifts`),
for every curve of degree 5 or 6, squarefree or not. For `p ∤ a`, the remainder `s₁ X + s₂` of `f`
modulo `X² - (b / a) X + c / a` is that of `v²` for the polynomial `v = v₁ X + v₀` of the Mumford
representation, whose norm and trace make the test of `point_on_j` pass
(`JPoints.refPointOnJ_of_lifts`). For `p ∣ a` and `p ∤ b`, `A₂ ≡ f₆ b⁴` makes `f₆` a square, and
the polynomial `A₂` of the point `(c, b, a, d)` of the reversed curve `y² = x⁶ f(1 / x)`, a square
(`JPoints.isSquare_auxA2_reverse`), makes `F(c, b)` one
(`JPoints.isSquare_and_isSquare_sexticForm_of_lifts`). A candidate `(m a, m b, m c, n)` of
`JPoints.kummerPoints` over a triple reduces to the class of the triple when `p ∤ m`
(`JPoints.refAdmits12_mul`); when `p ∣ m`, in the kernel of the reduction, the triple lies on the
conic `b² ≡ 4ac` (`JPoints.cast_kummerK2_eq_zero_of_kummer_eq_zero`), whose classes the tables
admit (`JPoints.refAdmits12_of_cast_kummerK2_eq_zero`).

## Main statements

* `JPoints.refAdmits12_eq`, `JPoints.refIsSquare_eq`, `JPoints.refSquareRoot_val_ne_iff`,
  `JPoints.sq_refSquareRoot`, `JPoints.cast_refRemainder`: the references of the tables in
  `ZMod p`.
* `JPoints.exists_sq_auxA2_auxB2`, `JPoints.isSquare_auxA2_reverse`: the squares of the lifting
  test with the signs of the Mumford representation, and the reversed point.
* `JPoints.refAdmits12_of_lifts`: a point that lifts reduces to an admitted class.
* `JPoints.refAdmits12_of_mem_kummerPoints`: a candidate over a triple that lifts makes the class
  of the triple admitted.

## Implementation notes

The references compute with natural numbers and integers reduced modulo `p`; the proofs read them
in `ZMod p`, a field, where the identities of the Kummer surface over `ℤ` hold after the cast. The
square root of `A₂` of the reversed point is taken in `ℤ`, where `a⁴` times it is a square: the
division by `a²` there is the step that makes the argument work at a prime `p ∣ a`, where the
Mumford representation has `a` in its denominators.
-/

@[expose] public section

namespace JPoints

variable {p : ℕ}

/-! ### The references of the tables in `ZMod p` -/

theorem toNat_emod_eq_val [NeZero p] (x : ℤ) : (x % p).toNat = (x : ZMod p).val := by
  rw [← Int.natCast_inj, ZMod.val_intCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by simp [NeZero.ne p]))]

/-- `invert` computes the inverse modulo `p`, by Fermat's little theorem. -/
theorem refInverse_val [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) : refInverse p x.val = x⁻¹.val := by
  rw [refInverse, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
  congr 1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, ← ZMod.pow_card_sub_one_eq_one hx]
  congr 1
  lia [(Fact.out : p.Prime).two_le]

/-- The class test of the first two stages in `ZMod p`: the residues are the values of the casts,
and the quotients by the inverses modulo `p` those of the divisions. -/
theorem refAdmits12_eq [Fact p.Prime] (cs : List ℤ) (deg : ℕ) (a b c : ℤ) :
    refAdmits12 cs deg p a b c = if (a : ZMod p) = 0 then
      decide ((b : ZMod p) = 0) || refHasInfinity cs p && refIsFSquare cs p ((c : ZMod p) / b).val
    else refIsPointOnJ cs deg p ((b : ZMod p) / a).val ((c : ZMod p) / a).val := by
  simp only [refAdmits12, toNat_emod_eq_val, ZMod.val_eq_zero]
  split_ifs with ha
  · by_cases hb : (b : ZMod p) = 0
    · simp [hb]
    · simp [hb, refInverse_val hb, ← ZMod.val_mul, div_eq_mul_inv]
  · simp [refInverse_val ha, ← ZMod.val_mul, div_eq_mul_inv]

/- The square root that `init_squares` records, when there is one, lies in the list of the even
roots. -/
private theorem refSquareRoot_mem {x : ℕ} (h : refSquareRoot p x ≠ p) :
    refSquareRoot p x ∈ (List.range p).filter fun y ↦ y % 2 == 0 && y * y % p == x := by
  rw [refSquareRoot, List.getLastD_eq_getLast?] at *
  cases hl : ((List.range p).filter fun y ↦ y % 2 == 0 && y * y % p == x).getLast? with
  | none => simp [hl] at h
  | some y => exact List.mem_of_getLast? hl

theorem sq_refSquareRoot {x : ℕ} (h : refSquareRoot p x ≠ p) :
    (refSquareRoot p x : ZMod p) ^ 2 = x := by
  have := (List.mem_filter.1 (refSquareRoot_mem h)).2
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  rw [sq, ← Nat.cast_mul, ← ZMod.natCast_mod, this.2]

/- An even root `y < p` of a square of `ZMod p`, for an odd prime `p`: the root or its negative. -/
private theorem exists_even_sq_eq [Fact p.Prime] (hp2 : p ≠ 2) (r : ZMod p) :
    ∃ y < p, y % 2 = 0 ∧ (y : ZMod p) ^ 2 = r ^ 2 := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp2
  rcases Nat.even_or_odd r.val with h | h
  · exact ⟨r.val, r.val_lt, Nat.even_iff.1 h, by rw [ZMod.natCast_zmod_val]⟩
  · refine ⟨p - r.val, by lia [Nat.odd_iff.1 h, r.val_lt], ?_, ?_⟩
    · lia [Nat.odd_iff.1 h, Nat.odd_iff.1 hodd, r.val_lt]
    · rw [Nat.cast_sub r.val_lt.le, ZMod.natCast_self, ZMod.natCast_zmod_val]
      ring

/-- `init_squares` records a square root of `x` modulo an odd prime `p` exactly when `x` is a
square, since one of the two roots `±r` is even. -/
theorem refSquareRoot_val_ne_iff [Fact p.Prime] (hp2 : p ≠ 2) (x : ZMod p) :
    refSquareRoot p x.val ≠ p ↔ IsSquare x := by
  refine ⟨fun h ↦ ⟨refSquareRoot p x.val, ?_⟩, fun ⟨r, hr⟩ ↦ ?_⟩
  · rw [← sq, sq_refSquareRoot h, ZMod.natCast_zmod_val]
  obtain ⟨y, hy, hy2, hyr⟩ := exists_even_sq_eq hp2 r
  have hmem : y ∈ (List.range p).filter fun y ↦ y % 2 == 0 && y * y % p == x.val := by
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hy, hy2, ?_⟩
    rw [← ZMod.val_natCast, Nat.cast_mul, ← sq, hyr, hr, sq]
  rw [refSquareRoot, List.getLastD_eq_getLast?]
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 (List.ne_nil_of_mem hmem))
  rw [hz, Option.getD_some]
  exact (List.mem_range.1 (List.mem_filter.1 (List.mem_of_getLast? hz)).1).ne

theorem refIsSquare_eq [Fact p.Prime] (hp2 : p ≠ 2) (x : ℤ) :
    refIsSquare p x = decide (IsSquare (x : ZMod p)) := by
  rw [refIsSquare, toNat_emod_eq_val, Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff,
    ← ne_eq, refSquareRoot_val_ne_iff hp2]

/-- The remainder `s₁ X + s₂` of `f` modulo `X² - b X + c` that `point_on_j` computes by Horner's
rule, for a curve of degree 5 or 6, in `ZMod p`. -/
theorem cast_refRemainder {cs : List ℤ} (h7 : cs.length ≤ 7) {deg : ℕ} (hdeg : degree cs = deg)
    (h5 : 5 ≤ deg) (b c : ℤ) :
    ((refRemainder cs deg p b c).1 : ZMod p) = cs.getD 1 0 + cs.getD 2 0 * b +
        cs.getD 3 0 * (b ^ 2 - c) + cs.getD 4 0 * (b ^ 3 - 2 * b * c) +
        cs.getD 5 0 * (b ^ 4 - 3 * b ^ 2 * c + c ^ 2) +
        cs.getD 6 0 * (b ^ 5 - 4 * b ^ 3 * c + 3 * b * c ^ 2) ∧
      ((refRemainder cs deg p b c).2 : ZMod p) = cs.getD 0 0 - cs.getD 2 0 * c -
        cs.getD 3 0 * b * c - cs.getD 4 0 * (b ^ 2 * c - c ^ 2) -
        cs.getD 5 0 * (b ^ 3 * c - 2 * b * c ^ 2) -
        cs.getD 6 0 * (b ^ 4 * c - 3 * b ^ 2 * c ^ 2 + c ^ 3) := by
  obtain rfl | rfl : deg = 6 ∨ deg = 5 := by lia [degree_le_length_sub_one cs]
  all_goals simp only [refRemainder, Nat.reduceSub, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · push_cast [ZMod.intCast_mod, ZMod.natCast_self]
    constructor <;> ring
  · rw [getD_eq_zero_of_degree_lt (by lia : degree cs < 6)]
    push_cast [ZMod.intCast_mod, ZMod.natCast_self]
    constructor <;> ring

/-! ### Squares -/

theorem exists_sq_eq_and_two_mul_mul_eq {R : Type*} [CommRing R] [NoZeroDivisors R] {x y w : R}
    (h : w ^ 2 = 4 * x ^ 2 * y ^ 2) : ∃ x', x' ^ 2 = x ^ 2 ∧ 2 * x' * y = w := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h.trans (by ring) : w ^ 2 = (2 * x * y) ^ 2) with h | h
  · exact ⟨x, rfl, h.symm⟩
  · exact ⟨-x, neg_sq x, by linear_combination -h⟩

/-- When `s₁ X + s₂` is the remainder of `(v₁ X + v₀)²` modulo `X² - b X + c`, its norm
`s₂² + b s₁ s₂ + c s₁²` is the square of the norm `N = c v₁² + b v₁ v₀ + v₀²` of `v₁ X + v₀`, and
`2 s₂ + b s₁ + 2 N` is the square of `b v₁ + 2 v₀`; so for every square root `t = ±N` of the norm
one of `2 s₂ + b s₁ ± 2 t` is a square. -/
theorem isSquare_or_isSquare_of_sq_eq {R : Type*} [CommRing R] [NoZeroDivisors R]
    {b c s₁ s₂ v₁ v₀ t : R} (h₁ : s₁ = b * v₁ ^ 2 + 2 * v₁ * v₀) (h₂ : s₂ = v₀ ^ 2 - c * v₁ ^ 2)
    (ht : t ^ 2 = s₂ ^ 2 + b * s₁ * s₂ + c * s₁ ^ 2) :
    IsSquare (2 * s₂ + b * s₁ + 2 * t) ∨ IsSquare (2 * s₂ + b * s₁ - 2 * t) := by
  have hN : t ^ 2 = (c * v₁ ^ 2 + b * v₁ * v₀ + v₀ ^ 2) ^ 2 := by rw [ht, h₁, h₂]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hN with h | h
  · exact .inl ⟨b * v₁ + 2 * v₀, by rw [h, h₁, h₂]; ring⟩
  · exact .inr ⟨b * v₁ + 2 * v₀, by rw [h, h₁, h₂]; ring⟩

/-- `F = B² γ² + B C³ W + e C⁶` is a square when `α² = e B⁴` and `W² = 4 e γ²`: up to the sign of
`γ`, `2 γ α = B² W`, and `B⁴ F = (B³ γ + α C³)²`. -/
theorem isSquare_of_sq_eq_mul_pow_four {K : Type*} [Field K] {B C W α γ e F : K} (hB : B ≠ 0)
    (hα : α ^ 2 = e * B ^ 4) (hW : W ^ 2 = 4 * e * γ ^ 2)
    (hF : F = B ^ 2 * γ ^ 2 + B * C ^ 3 * W + e * C ^ 6) : IsSquare F := by
  obtain ⟨γ', hγ', hγα⟩ := exists_sq_eq_and_two_mul_mul_eq (x := γ) (y := α) (w := B ^ 2 * W)
    (by linear_combination B ^ 4 * hW - 4 * γ ^ 2 * hα)
  refine ⟨(B ^ 3 * γ' + α * C ^ 3) / B ^ 2, ?_⟩
  linear_combination (norm := field) hF - B ^ 2 * hγ' - C ^ 3 / B * hγα - C ^ 6 / B ^ 4 * hα

/-! ### The Kummer surface -/

/-- The squares `A₂ = α²` and `B₂ = β²` of the lifting test on the Kummer surface, with the signs
of the Mumford representation `(x² - (b / a) x + c / a, v₁ x + v₀)`, `α = a² v₁` and `β = a² v₀`:
`2 α β = C` (`JPoints.auxC`), since `4 A₂ B₂ = C²` there (`JPoints.four_mul_auxA2_mul_auxB2`). -/
theorem exists_sq_auxA2_auxB2 {f : ℕ → ℤ} {a b c d : ℤ} (hK : kummer f a b c d = 0)
    (hA : IsSquare (auxA2 f a b c d)) (hB : IsSquare (auxB2 f a b c d)) :
    ∃ α β, α ^ 2 = auxA2 f a b c d ∧ β ^ 2 = auxB2 f a b c d ∧ 2 * α * β = auxC f a b c d := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨α', h1, h2⟩ := exists_sq_eq_and_two_mul_mul_eq (x := α) (y := β) (w := auxC f a b c d)
    (by linear_combination a ^ 4 * hK - four_mul_auxA2_mul_auxB2 f a b c d +
      4 * auxB2 f a b c d * hα + 4 * α ^ 2 * hβ)
  exact ⟨α', β, by rw [h1, hα, sq], by rw [hβ, sq], h2⟩

/-- The polynomial `A₂` of the point `(c, b, a, d)` of the reversed curve `y² = x⁶ f(1 / x)`, with
the coefficients `f (6 - k)`, is a square for a point `(a, b, c, d)`, `a ≠ 0`, with the squares
`α² = A₂`, `β² = B₂` and `2 α β = C`: `a⁴` times it is `(b c α + (b² - a c) β)²`. -/
theorem isSquare_auxA2_reverse {f : ℕ → ℤ} {a b c d α β : ℤ} (ha : a ≠ 0)
    (hα : α ^ 2 = auxA2 f a b c d) (hβ : β ^ 2 = auxB2 f a b c d)
    (hαβ : 2 * α * β = auxC f a b c d) : IsSquare (auxA2 (fun k ↦ f (6 - k)) c b a d) := by
  have hX : (a ^ 2) ^ 2 * auxA2 (fun k ↦ f (6 - k)) c b a d =
      (b * c * α + (b ^ 2 - a * c) * β) ^ 2 := by
    simp only [auxA2, auxB2, auxC] at hα hβ hαβ ⊢
    linear_combination (-b ^ 2 * c ^ 2) * hα - (b ^ 2 - a * c) ^ 2 * hβ -
      b * c * (b ^ 2 - a * c) * hαβ
  obtain ⟨γ, hγ⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 (Dvd.intro _ hX)
  refine ⟨γ, mul_left_cancel₀ (by positivity : (a ^ 2) ^ 2 ≠ 0) ?_⟩
  rw [hX, hγ]
  ring

/-! ### The classes of the points -/

/-- `point_on_j` admits the class `(1, b, c)` when the remainder of `f` modulo `X² - b X + c` is
that of a square `(v₁ X + v₀)²` modulo `p`. -/
theorem refPointOnJ_of_cast_refRemainder [Fact p.Prime] (hp2 : p ≠ 2) {cs : List ℤ}
    {deg b c : ℕ} {v₁ v₀ : ZMod p}
    (h₁ : ((refRemainder cs deg p b c).1 : ZMod p) = b * v₁ ^ 2 + 2 * v₁ * v₀)
    (h₂ : ((refRemainder cs deg p b c).2 : ZMod p) = v₀ ^ 2 - c * v₁ ^ 2) :
    refPointOnJ cs deg p b c = true := by
  simp only [refPointOnJ, toNat_emod_eq_val]
  generalize refRemainder cs deg p b c = s at h₁ h₂
  set x : ℤ := s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1
  have hx : (x : ZMod p) = (s.2 : ZMod p) ^ 2 + b * s.1 * s.2 + c * s.1 ^ 2 := by
    push_cast [x, ZMod.intCast_mod]
    ring
  have ht : refSquareRoot p (x : ZMod p).val ≠ p := (refSquareRoot_val_ne_iff hp2 _).2
    ⟨c * v₁ ^ 2 + b * v₁ * v₀ + v₀ ^ 2, by rw [hx, h₁, h₂]; ring⟩
  have hsq := sq_refSquareRoot ht
  generalize refSquareRoot p (x : ZMod p).val = t at ht hsq ⊢
  rw [ZMod.natCast_zmod_val, hx] at hsq
  simp only [refIsSquare_eq hp2, Bool.and_eq_true, bne_iff_ne, ne_eq, ht, not_false_eq_true,
    true_and, Bool.or_eq_true, decide_eq_true_eq]
  push_cast [ZMod.intCast_mod, ZMod.natCast_self]
  refine (isSquare_or_isSquare_of_sq_eq h₁ h₂ hsq).imp id fun h ↦ ?_
  convert h using 2
  ring

/- `(1 + p (3 - (p & 2))) / 4`, the `1 / 4` of `init_table`, is exact for odd `p`. -/
private theorem four_dvd_one_add_mul {p : ℕ} (hp : p % 2 = 1) : 4 ∣ 1 + p * (3 - (p &&& 2)) := by
  have h := Nat.and_two_pow p 1
  rw [pow_one, Nat.testBit_eq_decide_div_mod_eq, pow_one] at h
  rw [h]
  by_cases h2 : p / 2 % 2 = 1 <;> simp [h2] <;> lia

/-- The exact table of the third stage admits the classes `(1, b, c)` on the conic `4 c = b²`, the
diagonal of `init_table`. -/
theorem refIsPointOnJ_of_four_mul_eq_sq [Fact p.Prime] (hp2 : p ≠ 2) (cs : List ℤ) (deg : ℕ)
    {b c : ZMod p} (h : 4 * c = b ^ 2) : refIsPointOnJ cs deg p b.val c.val = true := by
  have hq := Nat.div_mul_cancel (four_dvd_one_add_mul (Nat.odd_iff.1
    ((Fact.out : p.Prime).odd_of_ne_two hp2)))
  have hq' := congr(((↑) : ℕ → ZMod p) $hq)
  push_cast [ZMod.natCast_self, zero_mul, add_zero] at hq'
  simp only [refIsPointOnJ, Bool.or_eq_true, beq_iff_eq]
  refine .inl ?_
  rw [← ZMod.val_natCast, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  congr 1
  linear_combination (-1 : ZMod p) * c * hq' + ((1 + p * (3 - (p &&& 2))) / 4 : ℕ) * h

/-- For `p ∤ a`, a point of the Kummer surface that lifts reduces to a class `(1, b / a, c / a)`
that `point_on_j` admits: with `v₁ = α / a²` and `v₀ = β / a²` from
`JPoints.exists_sq_auxA2_auxB2`, the remainder of `f` modulo `X² - (b / a) X + c / a` is that of
`(v₁ X + v₀)²`. -/
theorem refPointOnJ_of_lifts [Fact p.Prime] (hp2 : p ≠ 2) {cs : List ℤ} (h7 : cs.length ≤ 7)
    {deg : ℕ} (hdeg : degree cs = deg) (h5 : 5 ≤ deg) {a b c d : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hK : kummer (cs.getD · 0) a b c d = 0) (hL : Lifts (cs.getD · 0) a b c d) :
    refPointOnJ cs deg p ((b : ZMod p) / a).val ((c : ZMod p) / a).val = true := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  simp only [Lifts, ha0, ↓reduceIte] at hL
  obtain ⟨α, β, hα, hβ, hαβ⟩ := exists_sq_auxA2_auxB2 hK hL.1 hL.2
  have hα' := congr(((↑) : ℤ → ZMod p) $hα)
  have hβ' := congr(((↑) : ℤ → ZMod p) $hβ)
  have hαβ' := congr(((↑) : ℤ → ZMod p) $hαβ)
  push_cast [auxA2, auxB2, auxC] at hα' hβ' hαβ'
  refine refPointOnJ_of_cast_refRemainder hp2 (v₁ := α / a ^ 2) (v₀ := β / a ^ 2) ?_ ?_ <;>
    simp only [cast_refRemainder h7 hdeg h5, Int.cast_natCast, ZMod.natCast_zmod_val]
  · linear_combination (norm := field) (-b / a ^ 5) * hα' + (-1 / a ^ 4) * hαβ'
  · linear_combination (norm := field) (c / a ^ 5) * hα' + (-1 / a ^ 4) * hβ'

/-- For `p ∣ a` and `p ∤ b`, a point of the Kummer surface that lifts has a point at infinity
modulo `p`, `f₆` a square, and its other point `x = c / b` with `F(c, b)` a square: for `a ≠ 0`,
`A₂ ≡ f₆ b⁴`, and the square `γ²` of `A₂` of the reversed point (`JPoints.isSquare_auxA2_reverse`)
with the Kummer equation `(f₅ c² - b d)² ≡ 4 f₆ γ²` give
`F(c, b) ≡ b² γ² + b c³ (f₅ c² - b d) + f₆ c⁶` a square
(`JPoints.isSquare_of_sq_eq_mul_pow_four`). -/
theorem isSquare_and_isSquare_sexticForm_of_lifts [Fact p.Prime] {f : ℕ → ℤ} {a b c d : ℤ}
    (ha : (a : ZMod p) = 0) (hb : (b : ZMod p) ≠ 0) (hK : kummer f a b c d = 0)
    (hL : Lifts f a b c d) : IsSquare (f 6 : ZMod p) ∧ IsSquare (sexticForm f c b : ZMod p) := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  by_cases ha0 : a = 0
  · simp only [Lifts, ha0, hb0, ↓reduceIte] at hL
    exact ⟨hL.1.map (Int.castRingHom _), hL.2.map (Int.castRingHom _)⟩
  simp only [Lifts, ha0, ↓reduceIte] at hL
  obtain ⟨α, β, hα, hβ, hαβ⟩ := exists_sq_auxA2_auxB2 hK hL.1 hL.2
  obtain ⟨γ, hγ⟩ := isSquare_auxA2_reverse ha0 hα hβ hαβ
  have hα' := congr(((↑) : ℤ → ZMod p) $hα)
  have hγ' := congr(((↑) : ℤ → ZMod p) $hγ)
  have hK' := congr(((↑) : ℤ → ZMod p) $hK)
  push_cast [auxA2, kummer, kummerK2, kummerK1, kummerK0, ha] at hα' hγ' hK'
  refine ⟨⟨α / (b : ZMod p) ^ 2, by linear_combination (norm := field) -hα' / (b : ZMod p) ^ 4⟩,
    isSquare_of_sq_eq_mul_pow_four (K := ZMod p) (C := c) (W := f 5 * c ^ 2 - b * d) (α := α)
      (γ := γ) (e := f 6) hb (by linear_combination hα')
      (by linear_combination hK' + 4 * (f 6 : ZMod p) * hγ') ?_⟩
  push_cast [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination (b : ZMod p) ^ 2 * hγ'

/-- `f(c / b)` is a square modulo `p` when `F(c, b) = b⁶ f(c / b)` is one, for `p ∤ b`. -/
theorem refIsFSquare_of_isSquare [Fact p.Prime] (hp2 : p ≠ 2) {cs : List ℤ} {b c : ℤ}
    (hb : (b : ZMod p) ≠ 0) (h : IsSquare (sexticForm (cs.getD · 0) c b : ZMod p)) :
    refIsFSquare cs p ((c : ZMod p) / b).val = true := by
  rw [refIsFSquare, refIsSquare_eq hp2, decide_eq_true_iff]
  convert h.div (IsSquare.sq ((b : ZMod p) ^ 3)) using 1
  push_cast [sexticForm, Finset.sum_range_succ, Finset.sum_range_zero, ZMod.natCast_zmod_val]
  field

/-- A point of the Kummer surface that comes from a rational point of the Jacobian reduces to a
class that the tables of the first two stages admit, at every odd prime `p` and for every curve of
degree 5 or 6: for `p ∤ a` by `JPoints.refPointOnJ_of_lifts`, for `p ∣ a`, `p ∤ b` by
`JPoints.isSquare_and_isSquare_sexticForm_of_lifts`. -/
theorem refAdmits12_of_lifts [Fact p.Prime] (hp2 : p ≠ 2) {cs : List ℤ} (h7 : cs.length ≤ 7)
    {deg : ℕ} (hdeg : degree cs = deg) (h5 : 5 ≤ deg) {a b c d : ℤ}
    (hK : kummer (cs.getD · 0) a b c d = 0) (hL : Lifts (cs.getD · 0) a b c d) :
    refAdmits12 cs deg p a b c = true := by
  rw [refAdmits12_eq]
  split_ifs with ha
  · by_cases hb : (b : ZMod p) = 0
    · simp [hb]
    obtain ⟨h6, hF⟩ := isSquare_and_isSquare_sexticForm_of_lifts ha hb hK hL
    rw [decide_eq_false hb, Bool.false_or, refHasInfinity, refIsSquare_eq hp2, decide_eq_true h6,
      refIsFSquare_of_isSquare hp2 hb hF, Bool.and_self]
  · simp [refIsPointOnJ, refPointOnJ_of_lifts hp2 h7 hdeg h5 ha hK hL]

/-- The class test of the first two stages depends on the class of `(a, b, c)` in the projective
plane over `ZMod p` only. -/
theorem refAdmits12_mul [Fact p.Prime] (cs : List ℤ) (deg : ℕ) {m : ℤ} (hm : (m : ZMod p) ≠ 0)
    (a b c : ℤ) :
    refAdmits12 cs deg p (m * a) (m * b) (m * c) = refAdmits12 cs deg p a b c := by
  simp only [refAdmits12_eq, Int.cast_mul, mul_eq_zero, hm, false_or, mul_div_mul_left _ _ hm]

/-- The tables of the first two stages admit the classes on the conic `b² ≡ 4ac`: for `p ∣ a` those
with `p ∣ b`, for `p ∤ a` the diagonal of the third stage
(`JPoints.refIsPointOnJ_of_four_mul_eq_sq`). -/
theorem refAdmits12_of_cast_kummerK2_eq_zero [Fact p.Prime] (hp2 : p ≠ 2) (cs : List ℤ)
    (deg : ℕ) {a b c : ℤ} (h : (kummerK2 a b c : ZMod p) = 0) :
    refAdmits12 cs deg p a b c = true := by
  push_cast [kummerK2] at h
  rw [refAdmits12_eq]
  split_ifs with ha
  · simp [pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination h + 4 * (c : ZMod p) * ha :
      (b : ZMod p) ^ 2 = 0)]
  · exact refIsPointOnJ_of_four_mul_eq_sq hp2 cs deg
      (by linear_combination (norm := field) -h / (a : ZMod p) ^ 2)

/-- Over a point `(m a, m b, m c, n)` of the Kummer surface with `p ∣ m` and `p ∤ n`, in the kernel
of the reduction modulo `p`, the triple `(a, b, c)` lies on the conic `b² ≡ 4ac`. -/
theorem cast_kummerK2_eq_zero_of_kummer_eq_zero [Fact p.Prime] {f : ℕ → ℤ} {m a b c n : ℤ}
    (hm0 : m ≠ 0) (hK : kummer f (m * a) (m * b) (m * c) n = 0) (hm : (m : ZMod p) = 0)
    (hn : (n : ZMod p) ≠ 0) : (kummerK2 a b c : ZMod p) = 0 := by
  have h := (mul_eq_zero.1 ((kummer_mul_mul_mul f m a b c n).symm.trans hK)).resolve_left
    (pow_ne_zero 2 hm0)
  have h' := congr(((↑) : ℤ → ZMod p) $h)
  push_cast [hm] at h'
  exact (mul_eq_zero.1 (by linear_combination h' : (kummerK2 a b c : ZMod p) * n ^ 2 = 0))
    |>.resolve_right (pow_ne_zero 2 hn)

/- A prime that divides the denominator of a rational number does not divide its numerator. -/
private theorem cast_num_ne_zero_of_cast_den_eq_zero [Fact p.Prime] {x : ℚ}
    (h : ((x.den : ℤ) : ZMod p) = 0) : (x.num : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
  exact fun hn ↦ (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes x.reduced hn h)

/-- A candidate `(m a, m b, m c, n)` of the Kummer equation over a triple that lifts makes the class
of the triple one that the tables of the first two stages admit, at every odd prime `p`: for
`p ∤ m` the class of the candidate (`JPoints.refAdmits12_of_lifts`, `JPoints.refAdmits12_mul`), for
`p ∣ m` the conic (`JPoints.cast_kummerK2_eq_zero_of_kummer_eq_zero`). -/
theorem refAdmits12_of_mem_kummerPoints [Fact p.Prime] (hp2 : p ≠ 2) {cs : List ℤ}
    (h7 : cs.length ≤ 7) {deg : ℕ} (hdeg : degree cs = deg) (h5 : 5 ≤ deg) {a b c : ℤ}
    {P : ℤ × ℤ × ℤ × ℤ} (hP : P ∈ kummerPoints (cs.getD · 0) (a, b, c))
    (hL : Lifts (cs.getD · 0) P.1 P.2.1 P.2.2.1 P.2.2.2) : refAdmits12 cs deg p a b c = true := by
  have hK := kummer_eq_zero_of_mem_kummerPoints hP
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hP
  by_cases hm : ((x.den : ℤ) : ZMod p) = 0
  · exact refAdmits12_of_cast_kummerK2_eq_zero hp2 cs deg
      (cast_kummerK2_eq_zero_of_kummer_eq_zero (by positivity) hK hm
        (cast_num_ne_zero_of_cast_den_eq_zero hm))
  rw [← refAdmits12_mul cs deg hm]
  exact refAdmits12_of_lifts hp2 h7 hdeg h5 hK hL

end JPoints

end
