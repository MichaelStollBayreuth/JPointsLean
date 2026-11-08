/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import JPoints.Proof.Containers

/-!
# Lemmas on 64-bit words for the contracts

Lemmas on the unsigned 64-bit words that the contracts of the model need and Lean core lacks, under
their names in the namespaces of Lean core: their bits, masks and shifts, the words with one bit
set, the lowest bit of a word shifted, the bits of the words of an array with a bit set, and the
reciprocal of a number below `2 ^ 32` in words. The lemmas on arrays, lists, ranges, natural numbers
and integers are in `JPoints.Proof.Containers`.

## Main statements

* `UInt64.getLsbD_allOnes_shiftLeft`, `UInt64.getLsbD_allOnes_shiftRight`: the bits of the masks.
* `UInt64.getLsbD_one_shiftLeft`, `UInt64.getLsbD_or_one_shiftLeft`,
  `UInt64.getLsbD_not_one_shiftLeft`: the bits of the word `1 <<< t`, of a word with one more bit
  set, and of the mask that clears one bit.
* `UInt64.getLsbD_shiftLeft_ofNat`, `UInt64.getLsbD_shiftRight_ofNat`: the bits of a word shifted
  by an amount below 64.
* `UInt64.shiftRight_and_one_beq_zero`, `UInt64.shiftRight_and_one_bne_zero`,
  `UInt64.getLsbD_eq_and_one_bne_zero`: the bits of a word by its lowest bit after a shift.
* `Array.getLsbD_getElem!_set!_or`, `Array.getLsbD_getElem!_set!_or_one_shiftLeft`: the bits of the
  words of an array after one more bit is set in one of them.
* `Array.getLsbD_getElem!_set!_and`, `Array.getLsbD_getElem!_set!_and_not`: the bits of the words
  of an array after one of them is masked, or has one bit cleared.
* `Nat.or_or_and_one_eq_zero_iff`: three numbers all even.
* `UInt64.toNat_one_shiftLeft_sub_one`, `UInt64.and_one_shiftLeft_sub_one_shiftLeft`: a mask of
  the low bits, and the bits of it that a shift left keeps.
* `UInt64.toNat_one_shiftLeft_toUInt64`, `UInt64.ofInt_natCast`,
  `UInt64.toNat_one_shiftLeft_add_ofNat_sub_one_div`: the value `2 ^ n` of the word `1 <<< n`, the
  word of a natural number given as an integer, and the reciprocal `⌈2 ^ 32 / p⌉` of `p < 2 ^ 32`.

## Implementation notes

The file uses Lean core only, so that the `grind` calls of the proofs see only the lemmas of core,
untouched by the updates of Mathlib.

## References

Adapted from `Ratpoints/Proof/Bits.lean` of
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean).
-/

@[expose] public section

/-! ### Words -/

namespace Nat

/-- A shift amount `n < 64` is its own reduction modulo `64`, which the shifts of words take. -/
theorem toNat_toUInt64_mod_sixty_four {n : Nat} (hn : n < 64) : n.toUInt64.toNat % 64 = n := by
  rw [toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show n < 2 ^ 64 by lia),
    Nat.mod_eq_of_lt hn]

end Nat

namespace UInt64

theorem getLsbD_allOnes (t : Nat) : (~~~0 : UInt64).toBitVec.getLsbD t = decide (t < 64) := by
  simp only [UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero, BitVec.getLsbD_allOnes]

theorem getLsbD_allOnes_shiftLeft (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) <<< n).toBitVec.getLsbD t =
      (decide (t < 64) && decide (n.toNat % 64 ≤ t)) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  grind

theorem getLsbD_allOnes_shiftRight (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) >>> n).toBitVec.getLsbD t = decide (n.toNat % 64 + t < 64) := by
  simp only [UInt64.toBitVec_shiftRight, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]

theorem and_one_eq_zero_iff (x : UInt64) : x &&& 1 = 0 ↔ x.toBitVec.getLsbD 0 = false := by
  simp only [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_one, UInt64.toBitVec_zero,
    BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases x.toBitVec.getLsbD 0 <;> decide

theorem getLsbD_one_shiftLeft {t : Nat} (ht : t < 64) (s : Nat) :
    ((1 : UInt64) <<< UInt64.ofNat t).toBitVec.getLsbD s = decide (s = t) := by
  grind [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_one]

theorem getLsbD_or_one_shiftLeft (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x ||| 1 <<< UInt64.ofNat n).toBitVec.getLsbD t = (x.toBitVec.getLsbD t || decide (t = n)) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_one_shiftLeft hn]

theorem getLsbD_not_one_shiftLeft {n j : Nat} (hn : n < 64) (hj : j < 64) :
    (~~~((1 : UInt64) <<< UInt64.ofNat n)).toBitVec.getLsbD j = !(j == n) := by
  rw [UInt64.toBitVec_not, BitVec.getLsbD_not, getLsbD_one_shiftLeft hn]
  by_cases h : j = n <;> simp [hj, h]

theorem getLsbD_not_one_shiftLeft_emod (c : Int) {j : Nat} (hj : j < 64) :
    (~~~((1 : UInt64) <<< UInt64.ofNat (c % 64).toNat)).toBitVec.getLsbD j =
      !(j == (c % 64).toNat) :=
  getLsbD_not_one_shiftLeft (by lia) hj

-- `Nat.toNat_toUInt64_mod_sixty_four` in the form that the shifts of bit vectors take.
private theorem toNat_toBitVec_ofNat_mod {n : Nat} (hn : n < 64) :
    (UInt64.ofNat n).toBitVec.toNat % (64 : BitVec 64).toNat = n :=
  Nat.toNat_toUInt64_mod_sixty_four hn

theorem getLsbD_shiftLeft_ofNat (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x <<< UInt64.ofNat n).toBitVec.getLsbD t =
      (decide (t < 64) && decide (n ≤ t) && x.toBitVec.getLsbD (t - n)) := by
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft,
    BitVec.toNat_umod, toNat_toBitVec_ofNat_mod hn]
  grind

theorem getLsbD_shiftRight_ofNat (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x >>> UInt64.ofNat n).toBitVec.getLsbD t = x.toBitVec.getLsbD (n + t) := by
  rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight,
    BitVec.toNat_umod, toNat_toBitVec_ofNat_mod hn]

/-- The word `(1 <<< d) - 1` of the low `d < 64` bits has the value `2 ^ d - 1`. -/
theorem toNat_one_shiftLeft_sub_one {d : Nat} (hd : d < 64) :
    ((1 <<< UInt64.ofNat d) - 1 : UInt64).toNat = 2 ^ d - 1 := by
  have hp : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by lia) hd
  have h : (1 <<< UInt64.ofNat d : UInt64).toNat = 2 ^ d := by
    simp [UInt64.toNat_shiftLeft, Nat.one_shiftLeft, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp]
  rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le, h, Nat.one_le_two_pow]), h,
    UInt64.toNat_one]

/-- The mask `(1 <<< d) - 1` of the low `d` bits of `init_sieve`, before a shift left by
`ds = 64 - d` with `0 < ds < 64`: it keeps the bits that the shift keeps. -/
theorem and_one_shiftLeft_sub_one_shiftLeft (x : UInt64) {ds d : Nat} (hd : ds + d = 64)
    (hds0 : 0 < ds) (hds : ds < 64) :
    (x &&& ((1 <<< UInt64.ofNat d) - 1)) <<< UInt64.ofNat ds = x <<< UInt64.ofNat ds := by
  refine UInt64.toNat_inj.mp ?_
  have h64 : 2 ^ 64 = 2 ^ ds * 2 ^ d := by rw [← Nat.pow_add, hd]
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_and, Nat.and_two_pow_sub_one_eq_mod,
    toNat_one_shiftLeft_sub_one (by lia : d < 64), UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show ds < 2 ^ 64 by lia), Nat.mod_eq_of_lt hds, Nat.shiftLeft_eq]
  rw [h64, Nat.mul_comm (2 ^ ds), Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, Nat.mod_mod]

theorem toNat_shiftRight_32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem shiftRight_and_one_beq_zero (x : UInt64) {j : Nat} (hj : j < 64) :
    (x >>> UInt64.ofNat j &&& 1 == 0) = !x.toBitVec.getLsbD j := by
  rw [Bool.eq_iff_iff, beq_iff_eq, and_one_eq_zero_iff, getLsbD_shiftRight_ofNat _ hj, Nat.add_zero]
  simp

theorem shiftRight_and_one_bne_zero (x : UInt64) {j : Nat} (hj : j < 64) :
    (x >>> UInt64.ofNat j &&& 1 != 0) = x.toBitVec.getLsbD j := by
  rw [bne, UInt64.shiftRight_and_one_beq_zero x hj, Bool.not_not]

/-- The bit `t` of `nums` is the lowest bit of the word `w` with `w.toNat = nums.toNat / 2 ^ t`, the
word `nums >>> t` after `t` shifts. -/
theorem getLsbD_eq_and_one_bne_zero {nums w : UInt64} {t : Nat}
    (h : w.toNat = nums.toNat / 2 ^ t) : nums.toBitVec.getLsbD t = (w &&& 1 != 0) := by
  have e : (w &&& 1).toNat = w.toNat % 2 := by simp
  rw [BitVec.getLsbD, UInt64.toNat_toBitVec, Nat.testBit_eq_decide_div_mod_eq, ← h]
  by_cases h1 : w.toNat % 2 = 1
  · simp only [h1, decide_true]
    exact (bne_iff_ne.mpr fun h0 ↦ by simp [h0] at e; lia).symm
  · have : w &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [e]; simp; lia)
    simp [h1, this]

/-- The word `1 <<< n` with one bit set, `2 ^ n` for `n < 64`. -/
theorem toNat_one_shiftLeft_toUInt64 {n : Nat} (hn : n < 64) :
    ((1 : UInt64) <<< n.toUInt64).toNat = 2 ^ n := by
  rw [UInt64.toNat_shiftLeft, Nat.toNat_toUInt64_mod_sixty_four hn, UInt64.toNat_one,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two hn)]

theorem ofInt_natCast (n : Nat) : UInt64.ofInt n = UInt64.ofNat n := by
  rw [UInt64.ofInt, ← UInt64.toNat_inj, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have h : ((n : Int) % 2 ^ 64).toNat = n % 2 ^ 64 := by lia
  rw [h, Nat.mod_mod]

/-- The reciprocal `⌈2 ^ 32 / p⌉` of a number `p < 2 ^ 32` in words, where nothing overflows. -/
theorem toNat_one_shiftLeft_add_ofNat_sub_one_div {p : Nat} (hp : p < 2 ^ 32) :
    (((1 : UInt64) <<< 32 + UInt64.ofNat p - 1) / UInt64.ofNat p).toNat =
      (2 ^ 32 + p - 1) / p := by
  have h1 : ((1 : UInt64) <<< 32).toNat = 2 ^ 32 := rfl
  have h2 : (UInt64.ofNat p).toNat = p := UInt64.toNat_ofNat_of_lt' (by lia)
  rw [UInt64.toNat_div, UInt64.toNat_sub_of_le, UInt64.toNat_add, h1, h2,
    Nat.mod_eq_of_lt (by lia), UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, h1, h2, Nat.mod_eq_of_lt (by lia),
    UInt64.toNat_one]
  lia

end UInt64

theorem Nat.or_or_and_one_eq_zero_iff (a b c : Nat) :
    (a ||| b ||| c) &&& 1 = 0 ↔ a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 := by
  simp only [Nat.and_one_is_mod, Nat.mod_two_eq_zero_iff_testBit_zero, Nat.testBit_or,
    Bool.or_eq_false_iff, and_assoc]

namespace Array

/-- A bit set in a word of an array stays set when a word of the array is or-ed with another. -/
theorem getLsbD_getElem!_set!_or {xs : Array UInt64} {j t : Nat}
    (h : xs[j]!.toBitVec.getLsbD t = true) (i : Nat) (y : UInt64) :
    (xs.set! i (xs[i]! ||| y))[j]!.toBitVec.getLsbD t = true := by
  by_cases hj : j < xs.size
  · rw [Array.getElem!_set! hj]
    by_cases hij : i = j
    · simp [hij, h]
    · simpa [hij] using h
  · rw [getElem!_neg xs j hj, show (default : UInt64) = 0 from rfl] at h
    simp at h

theorem getLsbD_getElem!_set!_or_one_shiftLeft {xs : Array UInt64} {i d : Nat}
    (hi : i < xs.size) (hd : d < 64) :
    (xs.set! i (xs[i]! ||| 1 <<< UInt64.ofNat d))[i]!.toBitVec.getLsbD d = true := by
  rw [Array.getElem!_set!_self _ _ _ hi, UInt64.getLsbD_or_one_shiftLeft _ hd]
  simp

/-- The bits of the words of an array after one word is and-ed with a mask `m`. -/
theorem getLsbD_getElem!_set!_and {A : Array UInt64} {t : Nat} (ht : t < A.size) (i : Nat)
    (m : UInt64) (j : Nat) :
    ((A.set! i (A[i]! &&& m))[t]!).toBitVec.getLsbD j =
      (A[t]!.toBitVec.getLsbD j && (t != i || m.toBitVec.getLsbD j)) := by
  rw [Array.getElem!_set! ht]
  by_cases h : i = t
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The bits of the words of an array after one bit of one word is cleared. -/
theorem getLsbD_getElem!_set!_and_not {A : Array UInt64} {t : Nat} (ht : t < A.size) (i : Nat)
    {n : Nat} (hn : n < 64) (j : Nat) :
    ((A.set! i (A[i]! &&& ~~~(1 <<< UInt64.ofNat n)))[t]!).toBitVec.getLsbD j =
      (A[t]!.toBitVec.getLsbD j && !(t == i && j == n)) := by
  rw [getLsbD_getElem!_set!_and ht]
  rcases Nat.lt_or_ge j 64 with hj | hj
  · rw [UInt64.getLsbD_not_one_shiftLeft hn hj]
    by_cases htj : t = i <;> by_cases hjn : j = n <;> simp [htj, hjn, bne]
  · simp [BitVec.getLsbD_of_ge _ _ hj]

end Array

end
