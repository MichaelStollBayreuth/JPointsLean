/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Admits
public import Mathlib.Data.Int.ModEq
public import Std.WP

import JPoints.Mathlib.Algebra.Group.Defs
import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The contracts of the tables of residues

The tables of `j-points` modulo the primes of the table are those of the references of
`JPoints.Proof.Admits`. Those of `init_main`: the words with one bit set
(`JPoints.BitsInvariant`), the inverses of `invert`, `a ^ (p - 2)` modulo `p` by binary
exponentiation (`JPoints.invert_spec`, `JPoints.initInverses_spec`), and the square roots of
`init_squares`, the last even root of each residue (`JPoints.initSquares_spec`); from them
`JPoints.Tables.WF` in `JPoints.initMain_spec`. And the exact table of the third stage: the
reduction `MODP` by the reciprocal `⌈2 ^ 32 / p⌉` is the remainder of the operands below `2 ^ 24`
of `point_on_j` for `p ≤ 256` (`JPoints.modp_eq_emod`), so that `point_on_j` computes
`JPoints.refPointOnJ` (`JPoints.pointOnJ_spec`) and `init_table` fills the rows of a prime with
`JPoints.refIsPointOnJ` and leaves the rest of the tables of the curve as they were
(`JPoints.initTable_spec`), in the terms in which `JPoints.CurveTables.WF` reads them
(`JPoints.CurveTables.PrimeWF`, `JPoints.CurveTables.RowsWF`, `JPoints.CurveTables.EqOff`).

## Main definitions

* `JPoints.BitsInvariant`, `JPoints.InvertInvariant`, `JPoints.InversesUpTo`,
  `JPoints.SquaresUpTo`, `JPoints.SquaresRowFill`, `JPoints.SquaresRowRoots`: the invariants of
  the loops of `init_main`, `invert`, `init_inverses` and `init_squares`.
* `JPoints.PrimeRowArgs`, `JPoints.PointOnJArgs`: the rows of a prime in the tables that
  `point_on_j` reads.
* `JPoints.refRemainderNext`, `JPoints.PointOnJInvariant`: a step of `JPoints.refRemainder`, and
  the invariant of the loop of `point_on_j`.
* `JPoints.CurveTables.PrimeWF`, `JPoints.CurveTables.RowsWF`, `JPoints.CurveTables.EqOff`: the
  tables of the curve at a prime, the rows of a prime in the table of the third stage, and tables
  of the curve that agree off a prime.
* `JPoints.TableRowsUpTo`: the invariant of the loops of `init_table`.

## Main statements

* `JPoints.invert_spec`, `JPoints.initInverses_spec`, `JPoints.initSquares_spec`,
  `JPoints.Tables.wf_of_bitsInvariant`: the tables of `init_main`.
* `JPoints.modp_eq_emod`: `MODP` is the remainder.
* `JPoints.pointOnJ_spec`: `point_on_j` decides the classes as `JPoints.refPointOnJ`.
* `JPoints.initTable_spec`: `init_table` fills the rows of a prime as `JPoints.refIsPointOnJ`.
* `JPoints.CurveTables.WF.of_primeWF`: the tables of the curve from the tables at each prime.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. The tables are flat arrays with the index
arithmetic of the C code; the entries of one prime are told from those of another by the uniqueness
of the positions `a M + b` with `b < M` (`Nat.eq_and_eq_of_mul_add_eq_mul_add`). The contracts of
`point_on_j` and `init_table` read the coefficients of the curve through their residues in the table
`coeffs_mod_p`, which the program writes; the coefficients themselves, which the program does not
mention, are quantified in their postconditions, and the triples with them as parameters are proved
first (`JPoints.pointOnJ_spec_of_pointOnJArgs`, `JPoints.initTable_spec_of_coeffsModP`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The words with one bit set -/

/-- The invariant of the loop of `JPoints.initMain` over the words with one bit set: after `n`
steps, the array has `JPoints.longLength` entries, its first `n` are `2⁰, …, 2ⁿ⁻¹`, and the word
`bit` is `2ⁿ` modulo `2 ^ 64`. -/
def BitsInvariant : Std.WP.Invariant ℕ (Array UInt64 × UInt64) Prop :=
  fun pref _ s ↦ s.1.size = longLength ∧ s.2.toNat = 2 ^ pref.length % 2 ^ 64 ∧
    ∀ n < pref.length, s.1[n]! = 1 <<< n.toUInt64

theorem bitsInvariant_nil (suff : List ℕ) : BitsInvariant [] suff (Tables.initial.bits, 1) :=
  ⟨by simp [Tables.initial], by simp, by simp⟩

theorem BitsInvariant.append_singleton {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:longLength] = pref ++ cur :: suff) {s : Array UInt64 × UInt64}
    (hinv : BitsInvariant pref (cur :: suff) s) :
    BitsInvariant (pref ++ [cur]) suff (s.1.set! cur s.2, s.2 <<< 1) := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  have h64 : cur < 64 := hlt
  refine ⟨by simp [h1], ?_, fun n hn ↦ ?_⟩
  · rw [UInt64.toNat_shiftLeft, h2]
    simp [Nat.shiftLeft_eq, pow_succ, Nat.mul_mod]
  · rw [List.length_append, List.length_singleton] at hn
    rcases (show n = cur ∨ n < cur by lia) with rfl | hn'
    · rw [Array.getElem!_set!_self _ _ _ (h1 ▸ hlt), ← UInt64.toNat_inj,
        UInt64.toNat_one_shiftLeft_toUInt64 h64, h2, hc,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right Nat.one_lt_two h64)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h3 n (by lia)]

/-! ### The inverses -/

/-- The invariant of the loop of `JPoints.invert`, binary exponentiation of `a` modulo `p` from the
right: the state `(r, b, n)` keeps `r bⁿ ≡ a ^ (p - 2) (mod p)` with `r, b ≥ 0` and `n ≥ 1`, and
`n = 1` at the exit. -/
def InvertInvariant (a p : ℕ) : Std.WP.WhileInvariant (ℤ × ℤ × ℤ) Prop :=
  .mk fun exit s ↦ 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 1 ≤ s.2.2 ∧ (exit = true → s.2.2 = 1) ∧
    s.1 * s.2.1 ^ s.2.2.toNat ≡ a ^ (p - 2) [ZMOD p]

private theorem invertInvariant_init {a p : ℕ} (hp : 3 ≤ p) : InvertInvariant a p false
    (1, a, p - 2) :=
  have h : ((p : ℤ) - 2).toNat = p - 2 := by lia
  ⟨zero_le_one, Int.natCast_nonneg a, by lia, nofun, by rw [one_mul, h]⟩

private theorem InvertInvariant.tmod_eq {a p : ℕ} {r b n : ℤ}
    (h : InvertInvariant a p true (r, b, n)) :
    (r * b).tmod p = refInverse p a := by
  obtain ⟨hr, hb, -, hn, hc⟩ := h
  rw [hn rfl, Int.toNat_one, pow_one] at hc
  rw [Int.tmod_eq_emod_of_nonneg (mul_nonneg hr hb), hc, refInverse]
  push_cast
  rfl

/-- A step of the binary exponentiation of `JPoints.invert` from the state `(r, b, n)`, `n > 1`, to
`(r', b², ⌊n / 2⌋)`, the square reduced modulo `p`, for `r' ≡ r b^(n mod 2)`. -/
private theorem InvertInvariant.shiftRight {a p : ℕ} {r b n r' : ℤ} (h1 : 1 < n) (hr' : 0 ≤ r')
    (hc : r' ≡ r * b ^ (n.toNat % 2) [ZMOD p]) (h : InvertInvariant a p false (r, b, n)) :
    InvertInvariant a p false (r', (b * b).tmod p, n >>> 1) := by
  obtain ⟨-, hb, -, -, h⟩ := h
  have hn : (n >>> 1).toNat = n.toNat / 2 := by rw [Int.shiftRight_eq_div_pow]; lia
  refine ⟨hr', Int.tmod_nonneg _ (mul_nonneg hb hb), by rw [Int.shiftRight_eq_div_pow]; lia,
    nofun, ?_⟩
  rw [hn, Int.tmod_eq_emod_of_nonneg (mul_nonneg hb hb)]
  refine ((hc.mul ((Int.mod_modEq _ _).pow _)).trans ?_).trans h
  rw [mul_assoc, ← sq, pow_mod_mul_pow_pow_div]

private theorem InvertInvariant.shiftRight_of_odd {a p : ℕ} {r b n : ℤ} {m : ℕ} (h1 : 1 < n)
    (hodd : (n % 2 == 1) = true) (h : n.toNat = m ∧ InvertInvariant a p false (r, b, n)) :
    (n >>> 1).toNat < m ∧ InvertInvariant a p false ((r * b).tmod p, (b * b).tmod p, n >>> 1) := by
  obtain ⟨rfl, h⟩ := h
  have hr : 0 ≤ r * b := mul_nonneg h.1 h.2.1
  have h2 : n.toNat % 2 = 1 := by simp at hodd; lia
  refine ⟨by rw [Int.shiftRight_eq_div_pow]; lia, h.shiftRight h1 (Int.tmod_nonneg _ hr) ?_⟩
  rw [Int.tmod_eq_emod_of_nonneg hr, h2, pow_one]
  exact Int.mod_modEq _ _

private theorem InvertInvariant.shiftRight_of_even {a p : ℕ} {r b n : ℤ} {m : ℕ} (h1 : 1 < n)
    (heven : ¬(n % 2 == 1) = true) (h : n.toNat = m ∧ InvertInvariant a p false (r, b, n)) :
    (n >>> 1).toNat < m ∧ InvertInvariant a p false (r, (b * b).tmod p, n >>> 1) := by
  obtain ⟨rfl, h⟩ := h
  have h2 : n.toNat % 2 = 0 := by simp at heven; lia
  refine ⟨by rw [Int.shiftRight_eq_div_pow]; lia, h.shiftRight h1 h.1 ?_⟩
  rw [h2, pow_zero, mul_one]

private theorem InvertInvariant.exit {a p : ℕ} {r b n : ℤ} {m : ℕ} (h1 : ¬1 < n)
    (h : n.toNat = m ∧ InvertInvariant a p false (r, b, n)) : InvertInvariant a p true (r, b, n) :=
  have h := h.2
  ⟨h.1, h.2.1, h.2.2.1, fun _ ↦ by lia [h.2.2.1], h.2.2.2.2⟩

attribute [local irreducible] InvertInvariant in
/-- `invert` computes the inverse of `JPoints.refInverse`, `a ^ (p - 2)` reduced modulo `p`, for
`p ≥ 3`. -/
@[spec]
theorem invert_spec (a p : ℕ) : ⦃ 3 ≤ p ⦄ invert a p ⦃ fun r ↦ r = (refInverse p a : ℤ) ⦄ := by
  vcgen [invert] invariants
  · InvertInvariant a p
  · .ofMeasure fun s : ℤ × ℤ × ℤ ↦ s.2.2.toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact invertInvariant_init ‹_›
    | exact InvertInvariant.tmod_eq ‹_›
    | exact InvertInvariant.shiftRight_of_odd ‹_› ‹_› ‹_›
    | exact InvertInvariant.shiftRight_of_even ‹_› ‹_› ‹_›
    | exact InvertInvariant.exit ‹_› ‹_›

/-- The table `inverses` of `JPoints.initInverses` filled up to the residue `a` of the prime
`prime[pn]`: it has its size, and its entries for the residues `0 < a' < p` of the primes `p` before
`prime[pn]` and for the residues `0 < a' < a` of `prime[pn]` are the inverses of
`JPoints.refInverse`. -/
def InversesUpTo (inv : Array ℤ) (pn a : ℕ) : Prop :=
  inv.size = numPrimes * maxPrimeEven ∧
    (∀ pn' < pn, ∀ a' < primeTable[pn']!, 0 < a' →
      inv[pn' * maxPrimeEven + a']! = refInverse primeTable[pn']! a') ∧
    ∀ a' < a, 0 < a' → inv[pn * maxPrimeEven + a']! = refInverse primeTable[pn]! a'

private theorem inversesUpTo_nil {inv : Array ℤ} (h : inv.size = numPrimes * maxPrimeEven) :
    InversesUpTo inv ([] : List ℕ).length 0 :=
  ⟨h, nofun, nofun⟩

private theorem InversesUpTo.post {inv : Array ℤ}
    (h : InversesUpTo inv (ForIn.toList [:numPrimes]).length 0) :
    inv.size = numPrimes * maxPrimeEven ∧ ∀ pn < numPrimes, ∀ a < primeTable[pn]!, 0 < a →
      inv[pn * maxPrimeEven + a]! = refInverse primeTable[pn]! a := by
  rw [Std.Legacy.Range.length_toList_zero_start] at h
  exact ⟨h.1, h.2.1⟩

theorem InversesUpTo.one {inv : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:numPrimes] = pref ++ cur :: suff) (hinv : InversesUpTo inv pref.length 0) :
    InversesUpTo inv cur (([] : List ℕ).length + 1) := by
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons h] at hinv
  exact ⟨hinv.1, hinv.2.1, fun a ha ha' ↦ by simp at ha; lia⟩

theorem InversesUpTo.next {inv : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:numPrimes] = pref ++ cur :: suff)
    (hinv : InversesUpTo inv cur ((ForIn.toList [1:primeTable[cur]!]).length + 1)) :
    InversesUpTo inv (pref ++ [cur]).length 0 := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hp := three_le_getElem!_primeTable (Std.Legacy.Range.lt_of_toList_eq_append_cons h)
  obtain ⟨h1, h2, h3⟩ := hinv
  rw [Std.Legacy.Range.length_toList, Nat.sub_add_cancel (by lia)] at h3
  refine ⟨h1, fun pn hpn a ha ha0 ↦ ?_, nofun⟩
  rw [List.length_append, List.length_singleton, hc] at hpn
  rcases (show pn < cur ∨ pn = cur by lia) with hpn | rfl
  · exact h2 pn hpn a ha ha0
  · exact h3 a ha ha0

private theorem three_le_getElem!_primeTable_of_toList_eq_append_cons {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:numPrimes] = pref ++ cur :: suff) : 3 ≤ primeTable[cur]! :=
  three_le_getElem!_primeTable (Std.Legacy.Range.lt_of_toList_eq_append_cons h)

theorem InversesUpTo.set {inv : Array ℤ} {pref suff : List ℕ} {pn : ℕ}
    (hpn : ForIn.toList [:numPrimes] = pref ++ pn :: suff) {pref' suff' : List ℕ} {a : ℕ}
    (ha : ForIn.toList [1:primeTable[pn]!] = pref' ++ a :: suff')
    (hinv : InversesUpTo inv pn (pref'.length + 1)) {v : ℤ}
    (hv : v = refInverse primeTable[pn]! a) :
    InversesUpTo (inv.set! (pn * maxPrimeEven + a) v) pn ((pref' ++ [a]).length + 1) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons ha
  have hap := Std.Legacy.Range.lt_of_toList_eq_append_cons ha
  have hpn' := Std.Legacy.Range.lt_of_toList_eq_append_cons hpn
  have hM := lt_maxPrimeEven_of_lt_getElem!_primeTable hap
  obtain ⟨h1, h2, h3⟩ := hinv
  refine ⟨by rw [Array.size_set!, h1], fun pn' hpn'' a' ha' ha0 ↦ ?_, fun a' ha' ha0 ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_gt (Nat.mul_add_lt_mul_add_of_lt
      (lt_maxPrimeEven_of_lt_getElem!_primeTable ha') hpn'')), h2 pn' hpn'' a' ha' ha0]
  · rw [List.length_append, List.length_singleton] at ha'
    rcases (show a' = a ∨ a' < pref'.length + 1 by lia) with rfl | ha''
    · rw [Array.getElem!_set!_self _ _ _
        (lt_of_lt_of_eq (Nat.mul_add_lt_mul_of_lt hpn' le_rfl hM) h1.symm), hv]
    · rw [Array.getElem!_set!_ne _ _ _ _ fun h ↦ by
        lia [(Nat.eq_and_eq_of_mul_add_eq_mul_add hM (lt_of_lt_of_le ha'' (by lia)) h).2],
        h3 a' ha'' ha0]

attribute [local irreducible] InversesUpTo in
/-- `init_inverses` fills the table `inverses` with the inverses of `JPoints.refInverse` modulo
the primes of the table. -/
@[spec]
theorem initInverses_spec (inv : Array ℤ) :
    ⦃ inv.size = numPrimes * maxPrimeEven ⦄ initInverses inv
    ⦃ fun r ↦ r.size = numPrimes * maxPrimeEven ∧ ∀ pn < numPrimes, ∀ a < primeTable[pn]!,
        0 < a → r[pn * maxPrimeEven + a]! = (refInverse primeTable[pn]! a : ℤ) ⦄ := by
  vcgen [initInverses] invariants
  | inv1 => fun pref _ inv ↦ InversesUpTo inv pref.length 0
  | inv2 _ cur _ _ _ _ => fun pref _ inv ↦ InversesUpTo inv cur (pref.length + 1)
  all_goals with_reducible first
    | exact inversesUpTo_nil ‹_›
    | exact InversesUpTo.post ‹_›
    | exact InversesUpTo.one ‹_› ‹_›
    | exact InversesUpTo.next ‹_› ‹_›
    | exact three_le_getElem!_primeTable_of_toList_eq_append_cons ‹_›
    | exact InversesUpTo.set ‹_› ‹_› ‹_› ‹_›

/-! ### The square roots -/

/-- The table `squares` of `JPoints.initSquares` filled for the primes before `prime[pn]`: it has
its size, and its entries for the residues of those primes are the square roots of
`JPoints.refSquareRoot`. -/
def SquaresUpTo (sq : Array ℤ) (pn : ℕ) : Prop :=
  sq.size = numPrimes * maxPrime ∧
    ∀ pn' < pn, ∀ x < primeTable[pn']!, sq[pn' * maxPrime + x]! = refSquareRoot primeTable[pn']! x

/-- The table `squares` of `JPoints.initSquares` during the loop of the prime `p = prime[pn]` that
sets the entries of its residues `x < k` to `p`: filled for the primes before `p`, and these entries
`p`. -/
def SquaresRowFill (sq : Array ℤ) (pn k : ℕ) : Prop :=
  SquaresUpTo sq pn ∧ ∀ x < k, sq[pn * maxPrime + x]! = primeTable[pn]!

/-- The table `squares` of `JPoints.initSquares` during the loop of the prime `p = prime[pn]` over
the even `a < p`, after the `a` in `l`: filled for the primes before `p`, and the entry of each
residue `x` of `p` the last `a` of `l` with `a² ≡ x (mod p)`, or `p`. -/
def SquaresRowRoots (sq : Array ℤ) (pn : ℕ) (l : List ℕ) : Prop :=
  SquaresUpTo sq pn ∧ ∀ x < primeTable[pn]!,
    sq[pn * maxPrime + x]! =
      ((l.filter fun y ↦ y * y % primeTable[pn]! == x).getLastD primeTable[pn]! : ℕ)

private theorem squaresUpTo_nil {sq : Array ℤ} (h : sq.size = numPrimes * maxPrime) :
    SquaresUpTo sq ([] : List ℕ).length :=
  ⟨h, nofun⟩

private theorem SquaresUpTo.post {sq : Array ℤ}
    (h : SquaresUpTo sq (ForIn.toList [:numPrimes]).length) :
    sq.size = numPrimes * maxPrime ∧ ∀ pn < numPrimes, ∀ x < primeTable[pn]!,
      sq[pn * maxPrime + x]! = refSquareRoot primeTable[pn]! x := by
  rwa [Std.Legacy.Range.length_toList_zero_start] at h

private theorem SquaresUpTo.rowFill {sq : Array ℤ} {pref suff : List ℕ} {cur : ℕ}
    (h : ForIn.toList [:numPrimes] = pref ++ cur :: suff) (hinv : SquaresUpTo sq pref.length) :
    SquaresRowFill sq cur ([] : List ℕ).length :=
  ⟨Std.Legacy.Range.length_eq_of_toList_eq_append_cons h ▸ hinv, nofun⟩

theorem SquaresRowFill.set {sq : Array ℤ} {pref suff : List ℕ} {pn : ℕ}
    (hpn : ForIn.toList [:numPrimes] = pref ++ pn :: suff) {pref' suff' : List ℕ} {a : ℕ}
    (ha : ForIn.toList [:primeTable[pn]!] = pref' ++ a :: suff')
    (hinv : SquaresRowFill sq pn pref'.length) :
    SquaresRowFill (sq.set! (pn * maxPrime + a) primeTable[pn]!) pn (pref' ++ [a]).length := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons ha
  have hap := Std.Legacy.Range.lt_of_toList_eq_append_cons ha
  have hpn' := Std.Legacy.Range.lt_of_toList_eq_append_cons hpn
  have hM : a < maxPrime := lt_of_lt_of_le hap (getElem!_primeTable_le_maxPrime hpn')
  obtain ⟨⟨h1, h2⟩, h3⟩ := hinv
  refine ⟨⟨by rw [Array.size_set!, h1], fun pn' hpn'' x hx ↦ ?_⟩, fun x hx ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_gt (Nat.mul_add_lt_mul_add_of_lt
      (lt_of_lt_of_le hx (getElem!_primeTable_le_maxPrime (hpn''.trans hpn'))) hpn'')),
      h2 pn' hpn'' x hx]
  · rw [List.length_append, List.length_singleton] at hx
    rcases (show x = a ∨ x < pref'.length by lia) with rfl | hx'
    · rw [Array.getElem!_set!_self _ _ _ (lt_of_lt_of_eq (Nat.mul_add_lt_mul_of_lt hpn' le_rfl hM)
        h1.symm)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h3 x hx']

private theorem SquaresRowFill.rowRoots {sq : Array ℤ} {pn : ℕ}
    (h : SquaresRowFill sq pn (ForIn.toList [:primeTable[pn]!]).length) :
    SquaresRowRoots sq pn [] := by
  rw [Std.Legacy.Range.length_toList_zero_start] at h
  exact ⟨h.1, fun x hx ↦ by rw [h.2 x hx]; rfl⟩

theorem SquaresRowRoots.set {sq : Array ℤ} {pref suff : List ℕ} {pn : ℕ}
    (hpn : ForIn.toList [:numPrimes] = pref ++ pn :: suff) {l : List ℕ} {a : ℕ}
    (hinv : SquaresRowRoots sq pn l) :
    SquaresRowRoots (sq.set! (pn * maxPrime + a * a % primeTable[pn]!) a) pn (l ++ [a]) := by
  have hpn' := Std.Legacy.Range.lt_of_toList_eq_append_cons hpn
  have hp := three_le_getElem!_primeTable hpn'
  have hM : a * a % primeTable[pn]! < maxPrime :=
    lt_of_lt_of_le (Nat.mod_lt _ (by lia)) (getElem!_primeTable_le_maxPrime hpn')
  obtain ⟨⟨h1, h2⟩, h3⟩ := hinv
  refine ⟨⟨by rw [Array.size_set!, h1], fun pn' hpn'' x hx ↦ ?_⟩, fun x hx ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_gt (Nat.mul_add_lt_mul_add_of_lt
      (lt_of_lt_of_le hx (getElem!_primeTable_le_maxPrime (hpn''.trans hpn'))) hpn'')),
      h2 pn' hpn'' x hx]
  · rw [List.filter_append]
    by_cases hx' : a * a % primeTable[pn]! = x
    · rw [← hx', Array.getElem!_set!_self _ _ _ (lt_of_lt_of_eq
        (Nat.mul_add_lt_mul_of_lt hpn' le_rfl hM) h1.symm)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h3 x hx]
      simp [hx']

theorem SquaresRowRoots.next {sq : Array ℤ} {pref suff : List ℕ} {pn : ℕ}
    (hpn : ForIn.toList [:numPrimes] = pref ++ pn :: suff)
    (hinv : SquaresRowRoots sq pn (ForIn.toList [:primeTable[pn]!:2])) :
    SquaresUpTo sq (pref ++ [pn]).length := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hpn
  obtain ⟨⟨h1, h2⟩, h3⟩ := hinv
  refine ⟨h1, fun pn' hpn' x hx ↦ ?_⟩
  rw [List.length_append, List.length_singleton, hc] at hpn'
  rcases (show pn' < pn ∨ pn' = pn by lia) with hpn' | rfl
  · exact h2 pn' hpn' x hx
  · rw [h3 x hx, refSquareRoot, Std.Legacy.Range.toList_range_two, List.filter_filter]
    simp only [Bool.and_comm]

attribute [local irreducible] SquaresUpTo SquaresRowFill SquaresRowRoots in
/-- `init_squares` fills the table `squares` with the square roots of `JPoints.refSquareRoot`
modulo the primes of the table: for each prime `p`, the entries of its residues are first `p`, then
the entry of `a² mod p` is `a` for the even `a < p` in increasing order, so that each square gets
its last even root. -/
@[spec]
theorem initSquares_spec (sq : Array ℤ) :
    ⦃ sq.size = numPrimes * maxPrime ⦄ initSquares sq
    ⦃ fun r ↦ r.size = numPrimes * maxPrime ∧ ∀ pn < numPrimes, ∀ x < primeTable[pn]!,
        r[pn * maxPrime + x]! = (refSquareRoot primeTable[pn]! x : ℤ) ⦄ := by
  vcgen [initSquares] invariants
  | inv1 => fun pref _ sq ↦ SquaresUpTo sq pref.length
  | inv2 _ cur _ _ _ _ => fun pref _ sq ↦ SquaresRowFill sq cur pref.length
  | inv3 _ cur _ _ _ _ _ _ => fun pref _ sq ↦ SquaresRowRoots sq cur pref
  all_goals with_reducible first
    | exact squaresUpTo_nil ‹_›
    | exact SquaresUpTo.post ‹_›
    | exact SquaresUpTo.rowFill ‹_› ‹_›
    | exact SquaresRowFill.set ‹_› ‹_› ‹_›
    | exact SquaresRowFill.rowRoots ‹_›
    | exact SquaresRowRoots.set ‹_› ‹_›
    | exact SquaresRowRoots.next ‹_› ‹_›

/-! ### The tables of `init_main` -/

theorem Tables.size_inverses_initial : Tables.initial.inverses.size = numPrimes * maxPrimeEven :=
  Array.size_replicate ..

theorem Tables.size_squares_initial : Tables.initial.squares.size = numPrimes * maxPrime :=
  Array.size_replicate ..

/-- The tables of `init_main` from the words with one bit set, the inverses of
`JPoints.initInverses_spec` and the square roots of `JPoints.initSquares_spec`. -/
theorem Tables.wf_of_bitsInvariant {s : Array UInt64 × UInt64}
    (hb : BitsInvariant (ForIn.toList [:longLength]) [] s) {inverses squares : Array ℤ}
    (hi : inverses.size = numPrimes * maxPrimeEven ∧ ∀ pn < numPrimes, ∀ a < primeTable[pn]!,
      0 < a → inverses[pn * maxPrimeEven + a]! = refInverse primeTable[pn]! a)
    (hs : squares.size = numPrimes * maxPrime ∧ ∀ pn < numPrimes, ∀ x < primeTable[pn]!,
      squares[pn * maxPrime + x]! = refSquareRoot primeTable[pn]! x) :
    Tables.WF { bits := s.1, inverses, squares } where
  bits hn := hb.2.2 _ (by rwa [Std.Legacy.Range.length_toList_zero_start])
  inverses hpn _ ha hap := hi.2 _ hpn _ hap ha
  squares hpn _ hx := hs.2 _ hpn _ hx

/-! ### The reduction by the reciprocal -/

/-- `MODP` is the remainder modulo `0 < p ≤ 256` of the operands `0 ≤ x < 2 ^ 24` of
`point_on_j`, for the reciprocal `⌈2 ^ 32 / p⌉`: the quotient `⌊x ⌈2 ^ 32 / p⌉ / 2 ^ 32⌋` is
`⌊x / p⌋`, as `x (⌈2 ^ 32 / p⌉ p - 2 ^ 32) < 2 ^ 24 p ≤ 2 ^ 32`
(`Nat.mul_div_eq_div_of_mul_eq_add`). -/
theorem modp_eq_emod {p : ℕ} (hp : 0 < p) (hp256 : p ≤ 256) {recip : UInt64}
    (hrecip : recip.toNat = (2 ^ 32 + p - 1) / p) {x : ℤ} (hx : 0 ≤ x) (hx' : x < 2 ^ 24) :
    modp p recip x = x % p := by
  obtain ⟨u, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  have hm := Nat.le_mul_add_sub_one_div (2 ^ 32) hp
  have hm' := Nat.mul_add_sub_one_div_lt (2 ^ 32) hp
  rw [← hrecip] at hm hm'
  have hu : u < 2 ^ 24 := by lia
  have hδ : u * (recip.toNat * p - 2 ^ 32) < 2 ^ 32 :=
    calc u * (recip.toNat * p - 2 ^ 32) ≤ u * 256 := Nat.mul_le_mul_left _ (by lia)
      _ < 2 ^ 32 := by lia
  have hq : recip.toNat * u / 2 ^ 32 = u / p :=
    Nat.mul_div_eq_div_of_mul_eq_add hp (Nat.add_sub_of_le (Nat.mul_comm p _ ▸ hm)).symm hδ
  have hr : recip.toNat < 2 ^ 33 := by
    rw [hrecip]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by lia)
  have hlt : u * recip.toNat < 2 ^ 64 :=
    calc u * recip.toNat < 2 ^ 24 * 2 ^ 33 := Nat.mul_lt_mul'' hu hr
      _ ≤ 2 ^ 64 := by norm_num
  rw [modp, UInt64.toNat_shiftRight_32, UInt64.toNat_mul, UInt64.ofInt_natCast,
    UInt64.toNat_ofNat_of_lt' (by lia), Nat.mod_eq_of_lt hlt, Nat.mul_comm, hq, Int.natCast_div,
    Int.emod_def]

/-! ### The test of `point_on_j` -/

/-- The rows of the prime `p` of the index `pn` in the tables of the square roots and of the
coefficients modulo `p`: `p > 0`, the square roots of `JPoints.refSquareRoot` in the row of `pn` of
`squares`, and the coefficients `cs` of the curve reduced modulo `p` in the row of `pn` of
`coeffsModP`. -/
structure PrimeRowArgs (squares coeffsModP : Array ℤ) (pn p : ℕ) (cs : List ℤ) : Prop where
  /-- The prime is positive. -/
  pos : 0 < p
  /-- The square roots modulo the prime. -/
  squares {x : ℕ} (hx : x < p) : squares[pn * maxPrime + x]! = refSquareRoot p x
  /-- The coefficients modulo the prime. -/
  coeffs {n : ℕ} (hn : n ≤ 6) : coeffsModP[pn * 8 + n]! = cs.getD n 0 % p

/-- The arguments of `point_on_j` for the prime `p` of the index `pn`, as `init_table` and
`init_fmodpsquare` pass them for the curve with the coefficients `cs`: the rows of `p` in the tables
(`JPoints.PrimeRowArgs`), `p ≤ 256`, and the reciprocal `⌈2 ^ 32 / p⌉` of `p`. -/
structure PointOnJArgs (squares coeffsModP : Array ℤ) (pn p : ℕ) (recip : UInt64) (cs : List ℤ) :
    Prop extends PrimeRowArgs squares coeffsModP pn p cs where
  /-- The prime is at most `256`, so that the operands of `MODP` stay below `2 ^ 24`. -/
  le_256 : p ≤ 256
  /-- The reciprocal of the prime. -/
  toNat_recip : recip.toNat = (2 ^ 32 + p - 1) / p

/-- A step of the remainder of `f` modulo `X² - b X + c` and `p` by Horner's rule, as
`JPoints.refRemainder` computes it, for the coefficient of degree `deg - 2 - i`. -/
def refRemainderNext (cs : List ℤ) (deg p : ℕ) (b c : ℤ) (s : ℤ × ℤ) (i : ℕ) : ℤ × ℤ :=
  ((s.1 * b + s.2) % p, (cs.getD (deg - 2 - i) 0 % p + (p - c) * s.1) % p)

private theorem refRemainder_eq_foldl (cs : List ℤ) (deg p : ℕ) (b c : ℤ) :
    refRemainder cs deg p b c = (List.range (deg - 1)).foldl (refRemainderNext cs deg p b c)
      (cs.getD deg 0 % p, cs.getD (deg - 1) 0 % p) :=
  rfl

/-- The invariant of the loop of `JPoints.pointOnJ`, Horner's rule for the remainder of `f` modulo
`X² - b X + c` and `p`: after the steps `l`, the pair `(s₁, s₂)` is that of `JPoints.refRemainder`
after these steps, its entries in `[0, p)`. -/
def PointOnJInvariant (cs : List ℤ) (deg p b c : ℕ) : Std.WP.Invariant ℕ (ℤ × ℤ) Prop :=
  fun pref _ s ↦ (0 ≤ s.1 ∧ s.1 < p) ∧ (0 ≤ s.2 ∧ s.2 < p) ∧
    s = pref.foldl (refRemainderNext cs deg p b c) (cs.getD deg 0 % p, cs.getD (deg - 1) 0 % p)

private theorem pointOnJInvariant_nil {squares coeffsModP : Array ℤ} {pn p : ℕ} {recip : UInt64}
    {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {deg : ℕ} (hd : deg ≤ 6)
    (b c : ℕ) (suff : List ℕ) :
    PointOnJInvariant cs deg p b c [] suff
      (coeffsModP[pn * 8 + deg]!, coeffsModP[pn * 8 + (deg - 1)]!) := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  rw [h.coeffs hd, h.coeffs (by lia)]
  exact ⟨⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩,
    ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩, rfl⟩

-- The products of residues below `p ≤ 256` in `point_on_j`, below `2 ^ 16`.
private theorem mul_lt_two_pow_sixteen {p : ℕ} (hp : p ≤ 256) {x y : ℤ} (hx : 0 ≤ x)
    (hx' : x < p) (hy : 0 ≤ y) (hy' : y < p) : x * y < 2 ^ 16 :=
  lt_of_lt_of_le (mul_lt_mul'' hx' hy' hx hy) (by lia [Nat.mul_le_mul hp hp])

/-- The step of the loop of `point_on_j` from residues `s₁, s₂` below `p`, its reductions by `MODP`,
is that of `JPoints.refRemainder` (`JPoints.refRemainderNext`). -/
private theorem PointOnJArgs.modp_eq_refRemainderNext {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {deg b c : ℕ}
    (hd : deg ≤ 6) (hb : b < p) (hc : c < p) {s : ℤ × ℤ} (h1 : 0 ≤ s.1 ∧ s.1 < p)
    (h2 : 0 ≤ s.2 ∧ s.2 < p) (i : ℕ) :
    (modp p recip (s.1 * b + s.2), modp p recip (coeffsModP[pn * 8 + (deg - 2 - i)]! +
      (p - c) * s.1)) = refRemainderNext cs deg p b c s i := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  have hc' : (c : ℤ) ≤ p := mod_cast hc.le
  have hk := Int.emod_nonneg (cs.getD (deg - 2 - i) 0) hp.ne'
  have hk' := Int.emod_lt_of_pos (cs.getD (deg - 2 - i) 0) hp
  have hb' := mul_lt_two_pow_sixteen h.le_256 h1.1 h1.2 (Int.natCast_nonneg b) (mod_cast hb)
  have hcs := mul_le_mul_of_nonneg_right (sub_le_self (p : ℤ) (Int.natCast_nonneg c)) h1.1
  have hps := mul_lt_mul_of_pos_left h1.2 hp
  have hpp : (p : ℤ) * p ≤ 2 ^ 16 := by lia [Nat.mul_le_mul h.le_256 h.le_256]
  rw [h.coeffs (by lia), modp_eq_emod h.pos h.le_256 h.toNat_recip
      (by lia [mul_nonneg h1.1 (Int.natCast_nonneg b)]) (by lia [h.le_256]),
    modp_eq_emod h.pos h.le_256 h.toNat_recip (by lia [mul_nonneg (sub_nonneg.2 hc') h1.1])
      (by lia [h.le_256])]
  rfl

private theorem PointOnJInvariant.append_singleton {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {deg b c : ℕ}
    (hd : deg ≤ 6) (hb : b < p) (hc : c < p) {pref suff : List ℕ} {cur : ℕ} {s : ℤ × ℤ}
    (hinv : PointOnJInvariant cs deg p b c pref (cur :: suff) s) :
    PointOnJInvariant cs deg p b c (pref ++ [cur]) suff
      (modp p recip (s.1 * b + s.2), modp p recip (coeffsModP[pn * 8 + (deg - 2 - cur)]! +
        (p - c) * s.1)) := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  obtain ⟨h1, h2, hs⟩ := hinv
  rw [h.modp_eq_refRemainderNext hd hb hc h1 h2]
  refine ⟨⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩,
    ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩, ?_⟩
  rw [List.foldl_append, ← hs]
  rfl

private theorem PointOnJInvariant.eq_refRemainder {cs : List ℤ} {deg p b c : ℕ} {s : ℤ × ℤ}
    (h : PointOnJInvariant cs deg p b c (ForIn.toList [:deg - 1]) [] s) :
    s = refRemainder cs deg p b c := by
  rw [h.2.2, refRemainder_eq_foldl, Std.Internal.ForIn.toList_range, ← List.range_eq_range']
  simp [Std.Legacy.Range.size]

/-- An entry of the row of `p` in `squares` at a residue that `MODP` computes is the square root of
`JPoints.refSquareRoot` of the remainder. -/
private theorem PointOnJArgs.getElem!_squares_modp {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {x : ℤ}
    (hx : 0 ≤ x) (hx' : x < 2 ^ 24) :
    squares[pn * maxPrime + (modp p recip x).toNat]! = refSquareRoot p (x % p).toNat := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  rw [modp_eq_emod h.pos h.le_256 h.toNat_recip hx hx']
  exact h.squares (by lia [Int.emod_lt_of_pos x hp, Int.emod_nonneg x hp.ne'])

/-- The square root of `f(x₁) f(x₂) = s₂² + b s₁ s₂ + c s₁²` that `point_on_j` reads from `squares`
for residues `b, c, s₁, s₂` below `p`, with the reductions by `MODP`. -/
private theorem PointOnJArgs.getElem!_squares_modp_norm {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {b c : ℕ}
    (hb : b < p) (hc : c < p) {s : ℤ × ℤ} (h1 : 0 ≤ s.1 ∧ s.1 < p) (h2 : 0 ≤ s.2 ∧ s.2 < p) :
    squares[pn * maxPrime + (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
      modp p recip (c * s.1) * s.1)).toNat]! =
      refSquareRoot p ((s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1) % p).toNat := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  have hb' := mul_lt_two_pow_sixteen h.le_256 (Int.natCast_nonneg b) (mod_cast hb) h1.1 h1.2
  have hc' := mul_lt_two_pow_sixteen h.le_256 (Int.natCast_nonneg c) (mod_cast hc) h1.1 h1.2
  have e1 : modp p recip (b * s.1) = b * s.1 % p :=
    modp_eq_emod h.pos h.le_256 h.toNat_recip (mul_nonneg (Int.natCast_nonneg _) h1.1) (by lia)
  have e2 : modp p recip (c * s.1) = c * s.1 % p :=
    modp_eq_emod h.pos h.le_256 h.toNat_recip (mul_nonneg (Int.natCast_nonneg _) h1.1) (by lia)
  have hb'' := Int.emod_nonneg (b * s.1) hp.ne'
  have hc'' := Int.emod_nonneg (c * s.1) hp.ne'
  rw [e1, e2, h.getElem!_squares_modp (x := s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1)
    (by lia [mul_nonneg hb'' h2.1, mul_nonneg hc'' h1.1, mul_self_nonneg s.2])
    (by lia [mul_lt_two_pow_sixteen h.le_256 h2.1 h2.2 h2.1 h2.2,
      mul_lt_two_pow_sixteen h.le_256 hb'' (Int.emod_lt_of_pos _ hp) h2.1 h2.2,
      mul_lt_two_pow_sixteen h.le_256 hc'' (Int.emod_lt_of_pos _ hp) h1.1 h1.2])]

private theorem PointOnJInvariant.false_eq {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {deg b c : ℕ}
    (hb : b < p) (hc : c < p) {s : ℤ × ℤ}
    (hinv : PointOnJInvariant cs deg p b c (ForIn.toList [:deg - 1]) [] s)
    (ht : (squares[pn * maxPrime + (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
      modp p recip (c * s.1) * s.1)).toNat]! == p) = true) :
    false = refPointOnJ cs deg p b c := by
  rw [h.getElem!_squares_modp_norm hb hc hinv.1 hinv.2.1] at ht
  simp only [refPointOnJ, ← hinv.eq_refRemainder]
  simp_all

private theorem PointOnJInvariant.bne_or_bne_eq {squares coeffsModP : Array ℤ} {pn p : ℕ}
    {recip : UInt64} {cs : List ℤ} (h : PointOnJArgs squares coeffsModP pn p recip cs) {deg b c : ℕ}
    (hb : b < p) (hc : c < p) {s : ℤ × ℤ}
    (hinv : PointOnJInvariant cs deg p b c (ForIn.toList [:deg - 1]) [] s)
    (ht : ¬(squares[pn * maxPrime + (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
      modp p recip (c * s.1) * s.1)).toNat]! == p) = true) :
    (squares[pn * maxPrime + (modp p recip (2 * s.2 + b * s.1 + 2 *
        squares[pn * maxPrime + (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
          modp p recip (c * s.1) * s.1)).toNat]!)).toNat]! != p ||
      squares[pn * maxPrime + (modp p recip (modp p recip (2 * s.2 + b * s.1 + 2 *
        squares[pn * maxPrime + (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
          modp p recip (c * s.1) * s.1)).toNat]!) + 4 * (p - squares[pn * maxPrime +
            (modp p recip (s.2 * s.2 + modp p recip (b * s.1) * s.2 +
              modp p recip (c * s.1) * s.1)).toNat]!))).toNat]! != p) =
      refPointOnJ cs deg p b c := by
  have hp : (0 : ℤ) < p := mod_cast h.pos
  have hs := hinv.eq_refRemainder
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, -⟩ := hinv
  rw [h.getElem!_squares_modp_norm hb hc ⟨h1, h1'⟩ ⟨h2, h2'⟩] at ht ⊢
  simp only [refPointOnJ, refIsSquare, ← hs]
  have htp := refSquareRoot_le p ((s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1) % p).toNat
  generalize refSquareRoot p ((s.2 * s.2 + b * s.1 % p * s.2 + c * s.1 % p * s.1) % p).toNat = t
    at *
  have ht' : t < p := lt_of_le_of_ne htp (by simpa using ht)
  have hbs := mul_lt_two_pow_sixteen h.le_256 (Int.natCast_nonneg b) (mod_cast hb) h1 h1'
  have hbs' := mul_nonneg (Int.natCast_nonneg b) h1
  have e : modp p recip (2 * s.2 + b * s.1 + 2 * t) = (2 * s.2 + b * s.1 + 2 * t) % p :=
    modp_eq_emod h.pos h.le_256 h.toNat_recip (by lia) (by lia [h.le_256])
  have hX := Int.emod_nonneg (2 * s.2 + b * s.1 + 2 * t) hp.ne'
  have hX' := Int.emod_lt_of_pos (2 * s.2 + b * s.1 + 2 * t) hp
  rw [e, h.getElem!_squares_modp (x := (2 * s.2 + b * s.1 + 2 * t) % p + 4 * (p - t)) (by lia)
    (by lia [h.le_256]), h.squares (by lia), Int.natCast_bne_natCast, Int.natCast_bne_natCast,
    bne_iff_ne.2 ht'.ne, Bool.true_and]

attribute [local irreducible] PointOnJInvariant in
/-- `point_on_j` decides the class `(1, b, c)` modulo `p` as `JPoints.refPointOnJ` for the
coefficients `cs` of its arguments (`JPoints.PointOnJArgs`). -/
theorem pointOnJ_spec_of_pointOnJArgs (squares coeffsModP : Array ℤ) (deg pn p : ℕ)
    (recip : UInt64) (b c : ℕ) (cs : List ℤ) :
    ⦃ PointOnJArgs squares coeffsModP pn p recip cs ∧ deg ≤ 6 ∧ b < p ∧ c < p ⦄
    pointOnJ squares coeffsModP deg pn p recip b c
    ⦃ fun r ↦ r = refPointOnJ cs deg p b c ⦄ := by
  vcgen [pointOnJ] invariants
  · PointOnJInvariant cs deg p b c
  all_goals obtain ⟨h, hd, hb, hc⟩ := ‹PointOnJArgs squares coeffsModP pn p recip cs ∧ _›
  all_goals with_reducible first
    | exact pointOnJInvariant_nil h hd _ _ _
    | exact PointOnJInvariant.append_singleton h hd hb hc ‹_›
    | exact PointOnJInvariant.false_eq h hb hc ‹_› ‹_›
    | exact PointOnJInvariant.bne_or_bne_eq h hb hc ‹_› ‹_›

/-- `point_on_j` decides the class `(1, b, c)` modulo `p` as `JPoints.refPointOnJ`, for the
coefficients `cs` of every curve whose rows of `p` it is given (`JPoints.PointOnJArgs`). -/
@[spec]
theorem pointOnJ_spec (squares coeffsModP : Array ℤ) (deg pn p : ℕ) (recip : UInt64) (b c : ℕ) :
    ⦃ deg ≤ 6 ∧ b < p ∧ c < p ⦄ pointOnJ squares coeffsModP deg pn p recip b c
    ⦃ fun r ↦ ∀ cs, PointOnJArgs squares coeffsModP pn p recip cs →
        r = refPointOnJ cs deg p b c ⦄ :=
  ⟨fun h cs hcs ↦ (pointOnJ_spec_of_pointOnJArgs squares coeffsModP deg pn p recip b c cs).le_wp
    ⟨hcs, h⟩⟩

/-! ### The tables of the curve -/

namespace CurveTables

/-- The tables of the curve `ct` at the prime `p = prime[pn]` as `init_fmodpsquare` fills them for
the curve searched with the coefficients `cs`: the coefficients modulo `p`, whether the curve has
points at infinity modulo `p` (`JPoints.refHasInfinity`) and which values of `f` are squares
modulo `p` (`JPoints.refIsFSquare`). -/
structure PrimeWF (ct : CurveTables) (cs : List ℤ) (pn : ℕ) : Prop where
  /-- The coefficients modulo the prime. -/
  coeffsModP {n : ℕ} (hn : n ≤ 6) : ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!
  /-- The points at infinity modulo the prime. -/
  hasInfinity : ct.hasInfinity[pn]! = refHasInfinity cs primeTable[pn]!
  /-- The values of `f` that are squares modulo the prime. -/
  isFSquare {x : ℕ} (hx : x < primeTable[pn]!) :
    ct.isFSquare[pn * maxPrimeEven + x]! = refIsFSquare cs primeTable[pn]! x

/-- The tables of the curve at a prime carry over to tables of the curve with the same coefficients
modulo the primes, points at infinity and values of `f` that are squares. -/
theorem PrimeWF.of_eq {ct ct' : CurveTables} {cs : List ℤ} {pn : ℕ} (h : ct.PrimeWF cs pn)
    (h1 : ct'.coeffsModP = ct.coeffsModP) (h2 : ct'.hasInfinity = ct.hasInfinity)
    (h3 : ct'.isFSquare = ct.isFSquare) : ct'.PrimeWF cs pn :=
  ⟨fun hn ↦ h1 ▸ h.coeffsModP hn, h2 ▸ h.hasInfinity, fun hx ↦ h3 ▸ h.isFSquare hx⟩

/-- The rows of the prime `p = prime[pn]` in the exact table of the third stage of the tables of the
curve `ct` are those of `JPoints.refIsPointOnJ`, as `init_table` fills them for the curve with the
coefficients `cs` of degree `deg`. -/
def RowsWF (ct : CurveTables) (cs : List ℤ) (deg pn : ℕ) : Prop :=
  ∀ b < primeTable[pn]!, ∀ c < primeTable[pn]!,
    ct.isPointOnJ[(pn * maxPrimeEven + b) * maxPrimeEven + c]! =
      refIsPointOnJ cs deg primeTable[pn]! b c

/-- The tables of the curve `ct'` agree with `ct` off the prime of the index `pn`: they have the
sizes of those of `ct`, and the tables of every prime of another index are in `ct'` what they are in
`ct` (`JPoints.CurveTables.PrimeWF`, `JPoints.CurveTables.RowsWF`). -/
structure EqOff (ct ct' : CurveTables) (pn : ℕ) : Prop where
  /-- The size of the coefficients modulo the primes. -/
  size_coeffsModP : ct'.coeffsModP.size = ct.coeffsModP.size
  /-- The size of the table of the points at infinity. -/
  size_hasInfinity : ct'.hasInfinity.size = ct.hasInfinity.size
  /-- The size of the table of the values of `f` that are squares. -/
  size_isFSquare : ct'.isFSquare.size = ct.isFSquare.size
  /-- The size of the table of the third stage. -/
  size_isPointOnJ : ct'.isPointOnJ.size = ct.isPointOnJ.size
  /-- The tables of the curve at the other primes. -/
  primeWF {cs : List ℤ} {pn' : ℕ} (hpn : pn' ≠ pn) (h : ct.PrimeWF cs pn') : ct'.PrimeWF cs pn'
  /-- The rows of the other primes in the table of the third stage. -/
  rowsWF {cs : List ℤ} {deg pn' : ℕ} (hpn : pn' ≠ pn) (h : ct.RowsWF cs deg pn') :
    ct'.RowsWF cs deg pn'

theorem EqOff.trans {ct ct' ct'' : CurveTables} {pn : ℕ} (h : ct.EqOff ct' pn)
    (h' : ct'.EqOff ct'' pn) : ct.EqOff ct'' pn where
  size_coeffsModP := h'.size_coeffsModP.trans h.size_coeffsModP
  size_hasInfinity := h'.size_hasInfinity.trans h.size_hasInfinity
  size_isFSquare := h'.size_isFSquare.trans h.size_isFSquare
  size_isPointOnJ := h'.size_isPointOnJ.trans h.size_isPointOnJ
  primeWF hpn hp := h'.primeWF hpn (h.primeWF hpn hp)
  rowsWF hpn hr := h'.rowsWF hpn (h.rowsWF hpn hr)

/-- Tables of the curve whose coefficients, points at infinity and values of `f` that are squares
are those of `ct`, and whose table of the third stage has the size of that of `ct` and the rows of
`ct` for the primes of other indices than `pn`, agree with `ct` off `pn`. -/
private theorem eqOff_of_isPointOnJ {ct ct' : CurveTables} {pn : ℕ}
    (h1 : ct'.coeffsModP = ct.coeffsModP) (h2 : ct'.hasInfinity = ct.hasInfinity)
    (h3 : ct'.isFSquare = ct.isFSquare) (h4 : ct'.isPointOnJ.size = ct.isPointOnJ.size)
    (h : ∀ pn' ≠ pn, ∀ b < maxPrimeEven, ∀ c < maxPrimeEven,
      ct'.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]! =
        ct.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]!) : ct.EqOff ct' pn where
  size_coeffsModP := congr(Array.size $h1)
  size_hasInfinity := congr(Array.size $h2)
  size_isFSquare := congr(Array.size $h3)
  size_isPointOnJ := h4
  primeWF _ hp := hp.of_eq h1 h2 h3
  rowsWF hpn hr b hb c hc := by
    rw [h _ hpn b (lt_maxPrimeEven_of_lt_getElem!_primeTable hb) c
      (lt_maxPrimeEven_of_lt_getElem!_primeTable hc), hr b hb c hc]

/-- The tables of the curve from those at each prime: at the first `nPrimes` primes of the table
(`JPoints.CurveTables.PrimeWF`), and the rows of the sieving primes of the plan, `prime[pnn[k]]`
for `k < sp3`, in the table of the third stage (`JPoints.CurveTables.RowsWF`). -/
theorem WF.of_primeWF {ct : CurveTables} {cs : List ℤ} {deg nPrimes : ℕ} {pnn : Array ℕ}
    {sp3 : ℕ} (hp : ∀ pn < nPrimes, ct.PrimeWF cs pn) (hr : ∀ k < sp3, ct.RowsWF cs deg pnn[k]!) :
    ct.WF cs deg nPrimes pnn sp3 where
  coeffsModP hpn _ hn := (hp _ hpn).coeffsModP hn
  hasInfinity hpn := (hp _ hpn).hasInfinity
  isFSquare hpn _ hx := (hp _ hpn).isFSquare hx
  isPointOnJ hk _ _ hb hc := hr _ hk _ hb _ hc

end CurveTables

/-! ### The exact table of the third stage -/

/-- `b² / 4` modulo `p` as `init_table` computes it in `long`s is that of `JPoints.refIsPointOnJ`
in natural numbers. -/
private theorem tmod_tdiv_mul_mul_eq (p b : ℕ) :
    ((1 + (p : ℤ) * (3 - ((p : ℤ).toNat &&& 2 : ℕ))).tdiv 4 * b * b).tmod p =
      ((1 + p * (3 - (p &&& 2))) / 4 * b * b % p : ℕ) := by
  have h2 : p &&& 2 ≤ 2 := Nat.and_le_right
  have h3 : (1 : ℤ) + p * (3 - ((p &&& 2 : ℕ) : ℤ)) = ((1 + p * (3 - (p &&& 2)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (h2.trans (by decide : 2 ≤ 3))]
    ring
  rw [Int.toNat_natCast, h3, Int.tdiv_eq_ediv_of_nonneg (by positivity),
    Int.tmod_eq_emod_of_nonneg (by positivity)]
  push_cast
  rfl

private theorem true_eq_refIsPointOnJ_of_beq {cs : List ℤ} {deg p b c : ℕ}
    (h : ((c : ℤ) == ((1 + (p : ℤ) * (3 - ((p : ℤ).toNat &&& 2 : ℕ))).tdiv 4 * b * b).tmod p) =
      true) : true = refIsPointOnJ cs deg p b c := by
  rw [tmod_tdiv_mul_mul_eq, beq_iff_eq, Int.natCast_inj] at h
  simp [refIsPointOnJ, h]

private theorem eq_refIsPointOnJ_of_not_beq {cs : List ℤ} {deg p b c : ℕ}
    (h : ¬((c : ℤ) == ((1 + (p : ℤ) * (3 - ((p : ℤ).toNat &&& 2 : ℕ))).tdiv 4 * b * b).tmod p) =
      true) {r : Bool} (hr : r = refPointOnJ cs deg p b c) : r = refIsPointOnJ cs deg p b c := by
  rw [tmod_tdiv_mul_mul_eq, beq_iff_eq, Int.natCast_inj] at h
  simp [refIsPointOnJ, h, hr]

/-- The arguments of `point_on_j` that `init_table` passes for the prime `prime[pn]`, from the
tables `t` of `init_main` and tables of the curve `ct` with the coefficients `cs` modulo the
prime: `JPoints.PointOnJArgs`. -/
private theorem pointOnJArgs_initTable {t : Tables} (ht : t.WF) {pn : ℕ} (hpn : pn < numPrimes)
    {ct : CurveTables} {cs : List ℤ}
    (hcs : ∀ n ≤ 6, ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!) :
    PointOnJArgs t.squares ct.coeffsModP pn primeTable[pn]!
      (((1 : UInt64) <<< 32 + UInt64.ofInt primeTable[pn]! - 1) / UInt64.ofInt primeTable[pn]!)
      cs where
  pos := lt_of_lt_of_le (by decide) (three_le_getElem!_primeTable hpn)
  squares hx := ht.squares hpn hx
  coeffs hn := hcs _ hn
  le_256 := (getElem!_primeTable_lt_maxPrimeEven hpn).le.trans maxPrimeEven_le_256
  toNat_recip := by
    rw [UInt64.ofInt_natCast, UInt64.toNat_one_shiftLeft_add_ofNat_sub_one_div]
    exact lt_of_le_of_lt ((getElem!_primeTable_lt_maxPrimeEven hpn).le.trans maxPrimeEven_le_256)
      (by decide)

/-- The table of the third stage of `JPoints.initTable` for the prime `p = prime[pn]`, filled up
to the class `(1, b, c)`: it has the size of the table of the third stage of `ct`, that it
started from, the rows of the other primes as there, and the entries of the classes `(1, b', c')`
before `(1, b, c)` those of `JPoints.refIsPointOnJ` for the curve with the coefficients `cs` of
degree `deg`. -/
def TableRowsUpTo (ct : CurveTables) (cs : List ℤ) (deg pn : ℕ) (arr : Array Bool) (b c : ℕ) :
    Prop :=
  arr.size = ct.isPointOnJ.size ∧
    (∀ pn' ≠ pn, ∀ b' < maxPrimeEven, ∀ c' < maxPrimeEven,
      arr[(pn' * maxPrimeEven + b') * maxPrimeEven + c']! =
        ct.isPointOnJ[(pn' * maxPrimeEven + b') * maxPrimeEven + c']!) ∧
    (∀ b' < b, ∀ c' < primeTable[pn]!, arr[(pn * maxPrimeEven + b') * maxPrimeEven + c']! =
      refIsPointOnJ cs deg primeTable[pn]! b' c') ∧
    ∀ c' < c, arr[(pn * maxPrimeEven + b) * maxPrimeEven + c']! =
      refIsPointOnJ cs deg primeTable[pn]! b c'

private theorem lt_getElem!_primeTable_of_toList_eq_append_cons {pn : ℕ} {pref suff : List ℕ}
    {b : ℕ}
    (h : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff) : b < primeTable[pn]! :=
  Int.toNat_natCast primeTable[pn]! ▸ Std.Legacy.Range.lt_of_toList_eq_append_cons h

private theorem tableRowsUpTo_nil {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ} :
    TableRowsUpTo ct cs deg pn ct.isPointOnJ ([] : List ℕ).length 0 :=
  ⟨rfl, fun _ _ _ _ _ _ ↦ rfl, nofun, nofun⟩

private theorem TableRowsUpTo.rowStart {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ}
    {arr : Array Bool}
    {pref suff : List ℕ} {b : ℕ}
    (h : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hinv : TableRowsUpTo ct cs deg pn arr pref.length 0) :
    TableRowsUpTo ct cs deg pn arr b ([] : List ℕ).length := by
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons h] at hinv
  exact ⟨hinv.1, hinv.2.1, hinv.2.2.1, nofun⟩

private theorem TableRowsUpTo.rowEnd {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ}
    {arr : Array Bool}
    {pref suff : List ℕ} {b : ℕ}
    (h : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hinv : TableRowsUpTo ct cs deg pn arr b
      (ForIn.toList [:(primeTable[pn]! : ℤ).toNat]).length) :
    TableRowsUpTo ct cs deg pn arr (pref ++ [b]).length 0 := by
  have hb := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  rw [Std.Legacy.Range.length_toList, Int.toNat_natCast, Nat.sub_zero] at h4
  refine ⟨h1, h2, fun b' hb' c hc ↦ ?_, nofun⟩
  rw [List.length_append, List.length_singleton] at hb'
  rcases (show b' < b ∨ b' = b by lia) with hb' | rfl
  · exact h3 b' hb' c hc
  · exact h4 c hc

theorem TableRowsUpTo.set {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ} (hpn : pn < numPrimes)
    (hsize : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven) {arr : Array Bool}
    {pref suff pref' suff' : List ℕ} {b c : ℕ}
    (hb : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hc : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref' ++ c :: suff')
    (hinv : TableRowsUpTo ct cs deg pn arr b pref'.length) {v : Bool}
    (hv : v = refIsPointOnJ cs deg primeTable[pn]! b c) :
    TableRowsUpTo ct cs deg pn (arr.set! ((pn * maxPrimeEven + b) * maxPrimeEven + c) v) b
      (pref' ++ [c]).length := by
  have hbp := lt_getElem!_primeTable_of_toList_eq_append_cons hb
  have hcp := lt_getElem!_primeTable_of_toList_eq_append_cons hc
  have hcl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hbM := lt_maxPrimeEven_of_lt_getElem!_primeTable hbp
  have hcM := lt_maxPrimeEven_of_lt_getElem!_primeTable hcp
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have hidx : (pn * maxPrimeEven + b) * maxPrimeEven + c < arr.size := by
    rw [h1, hsize]
    exact Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt hpn le_rfl hbM) le_rfl hcM
  refine ⟨by rw [Array.size_set!, h1], fun pn' hpn' b' hb' c' hc' ↦ ?_, fun b' hb' c' hc' ↦ ?_,
    fun c' hc' ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _
      fun h ↦ hpn' (Nat.mul_add_mul_add_inj hbM hb' hcM hc' h).1.symm, h2 pn' hpn' b' hb' c' hc']
  · rw [Array.getElem!_set!_ne _ _ _ _ fun h ↦ (Nat.mul_add_mul_add_inj hbM
      (lt_maxPrimeEven_of_lt_getElem!_primeTable (hb'.trans hbp)) hcM
      (lt_maxPrimeEven_of_lt_getElem!_primeTable hc') h).2.1.not_gt hb', h3 b' hb' c' hc']
  · rw [List.length_append, List.length_singleton] at hc'
    rcases (show c' = c ∨ c' < pref'.length by lia) with rfl | hc''
    · rw [Array.getElem!_set!_self _ _ _ hidx, hv]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h4 c' hc'']

private theorem TableRowsUpTo.set_of_beq {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ}
    (hpn : pn < numPrimes) (hsize : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven)
    {arr : Array Bool} {pref suff pref' suff' : List ℕ} {b c : ℕ}
    (hb : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hc : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref' ++ c :: suff')
    (hinv : TableRowsUpTo ct cs deg pn arr b pref'.length)
    (h : ((c : ℤ) == ((1 + (primeTable[pn]! : ℤ) *
      (3 - ((primeTable[pn]! : ℤ).toNat &&& 2 : ℕ))).tdiv 4 * b * b).tmod primeTable[pn]!) = true) :
    TableRowsUpTo ct cs deg pn (arr.set! ((pn * maxPrimeEven + b) * maxPrimeEven + c) true) b
      (pref' ++ [c]).length :=
  hinv.set hpn hsize hb hc (true_eq_refIsPointOnJ_of_beq h)

private theorem TableRowsUpTo.set_of_pointOnJ {t : Tables} (ht : t.WF) {ct : CurveTables}
    {cs : List ℤ}
    {deg pn : ℕ} (hpn : pn < numPrimes)
    (hsize : ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven)
    (hcs : ∀ n ≤ 6, ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!)
    {arr : Array Bool} {pref suff pref' suff' : List ℕ} {b c : ℕ}
    (hb : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hc : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref' ++ c :: suff')
    (hinv : TableRowsUpTo ct cs deg pn arr b pref'.length)
    (h : ¬((c : ℤ) == ((1 + (primeTable[pn]! : ℤ) *
      (3 - ((primeTable[pn]! : ℤ).toNat &&& 2 : ℕ))).tdiv 4 * b * b).tmod primeTable[pn]!) = true)
    {r : Bool} (hr : ∀ cs, PointOnJArgs t.squares ct.coeffsModP pn primeTable[pn]!
      (((1 : UInt64) <<< 32 + UInt64.ofInt primeTable[pn]! - 1) / UInt64.ofInt primeTable[pn]!) cs →
        r = refPointOnJ cs deg primeTable[pn]! b c) {v : Bool} (hv : r = v) :
    TableRowsUpTo ct cs deg pn (arr.set! ((pn * maxPrimeEven + b) * maxPrimeEven + c) v) b
      (pref' ++ [c]).length :=
  hinv.set hpn hsize hb hc
    (hv ▸ eq_refIsPointOnJ_of_not_beq h (hr cs (pointOnJArgs_initTable ht hpn hcs)))

private theorem pointOnJ_pre_initTable {deg pn : ℕ} (hd : deg ≤ 6) {pref suff pref' suff' : List ℕ}
    {b c : ℕ} (hb : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref ++ b :: suff)
    (hc : ForIn.toList [:(primeTable[pn]! : ℤ).toNat] = pref' ++ c :: suff') :
    deg ≤ 6 ∧ b < primeTable[pn]! ∧ c < primeTable[pn]! :=
  ⟨hd, lt_getElem!_primeTable_of_toList_eq_append_cons hb,
    lt_getElem!_primeTable_of_toList_eq_append_cons hc⟩

private theorem TableRowsUpTo.post {ct : CurveTables} {cs : List ℤ} {deg pn : ℕ} {arr : Array Bool}
    (h : TableRowsUpTo ct cs deg pn arr (ForIn.toList [:(primeTable[pn]! : ℤ).toNat]).length 0)
    (n : ℕ) :
    ((⟨ct.coeffsModP, ct.hasInfinity, ct.isFSquare, arr⟩ : CurveTables), n).1.isPointOnJ.size =
        ct.isPointOnJ.size ∧
      ((⟨ct.coeffsModP, ct.hasInfinity, ct.isFSquare, arr⟩ : CurveTables), n).1.RowsWF cs deg pn ∧
      ∀ pn' ≠ pn, ∀ b < maxPrimeEven, ∀ c < maxPrimeEven,
        ((⟨ct.coeffsModP, ct.hasInfinity, ct.isFSquare, arr⟩ : CurveTables),
          n).1.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]! =
            ct.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]! := by
  rw [Std.Legacy.Range.length_toList, Int.toNat_natCast, Nat.sub_zero] at h
  exact ⟨h.1, h.2.2.1, h.2.1⟩

attribute [local irreducible] TableRowsUpTo in
/-- `init_table` fills the rows of the prime `prime[pn]` in the table of the third stage as
`JPoints.refIsPointOnJ` for the curve with the coefficients `cs` whose residues are those of the
tables of the curve `ct`, and leaves the rest of the tables of the curve as they were. -/
theorem initTable_spec_of_coeffsModP (t : Tables) (ct : CurveTables) (deg pn : ℕ) (cs : List ℤ) :
    ⦃ t.WF ∧ pn < numPrimes ∧ deg ≤ 6 ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven ∧
      ∀ n ≤ 6, ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]! ⦄
    initTable t ct deg pn
    ⦃ fun r ↦ r.1.coeffsModP = ct.coeffsModP ∧ r.1.hasInfinity = ct.hasInfinity ∧
        r.1.isFSquare = ct.isFSquare ∧ r.1.isPointOnJ.size = ct.isPointOnJ.size ∧
        r.1.RowsWF cs deg pn ∧ ∀ pn' ≠ pn, ∀ b < maxPrimeEven, ∀ c < maxPrimeEven,
          r.1.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]! =
            ct.isPointOnJ[(pn' * maxPrimeEven + b) * maxPrimeEven + c]! ⦄ := by
  vcgen [initTable] invariants
  | inv1 => fun pref _ s ↦ TableRowsUpTo ct cs deg pn s.1 pref.length 0
  | inv2 _ cur _ _ _ _ _ => fun pref _ s ↦ TableRowsUpTo ct cs deg pn s.1 cur pref.length
  all_goals obtain ⟨ht, hpn, hd, hsize, hcs⟩ := ‹t.WF ∧ _›
  all_goals with_reducible first
    | exact tableRowsUpTo_nil
    | exact TableRowsUpTo.post ‹_› _
    | exact TableRowsUpTo.rowStart ‹_› ‹_›
    | exact TableRowsUpTo.rowEnd ‹_› ‹_›
    | exact TableRowsUpTo.set_of_beq hpn hsize ‹_› ‹_› ‹_› ‹_›
    | exact absurd rfl ‹¬true = true›
    | exact pointOnJ_pre_initTable hd ‹_› ‹_›
    | exact TableRowsUpTo.set_of_pointOnJ ht hpn hsize hcs ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact TableRowsUpTo.set_of_pointOnJ ht hpn hsize hcs ‹_› ‹_› ‹_› ‹_› ‹_›
        (Bool.eq_false_iff.2 ‹_›)

/-- `init_table` fills the rows of the prime `prime[pn]` in the table of the third stage as
`JPoints.refIsPointOnJ` (`JPoints.CurveTables.RowsWF`), for the coefficients `cs` of every curve
whose residues modulo the prime are those of the tables of the curve `ct`, and leaves the rest of
the tables of the curve as they were (`JPoints.CurveTables.EqOff`). -/
@[spec]
theorem initTable_spec (t : Tables) (ct : CurveTables) (deg pn : ℕ) :
    ⦃ t.WF ∧ pn < numPrimes ∧ deg ≤ 6 ∧
      ct.isPointOnJ.size = numPrimes * maxPrimeEven * maxPrimeEven ⦄
    initTable t ct deg pn
    ⦃ fun r ↦ ∀ cs, (∀ n ≤ 6, ct.coeffsModP[pn * 8 + n]! = cs.getD n 0 % primeTable[pn]!) →
        r.1.coeffsModP = ct.coeffsModP ∧ r.1.hasInfinity = ct.hasInfinity ∧
        r.1.isFSquare = ct.isFSquare ∧ ct.EqOff r.1 pn ∧ r.1.RowsWF cs deg pn ⦄ :=
  ⟨fun ⟨ht, hpn, hd, hs⟩ cs hcs ↦
    have ⟨h1, h2, h3, h4, h5, h6⟩ :=
      (initTable_spec_of_coeffsModP t ct deg pn cs).le_wp ⟨ht, hpn, hd, hs, hcs⟩
    ⟨h1, h2, h3, CurveTables.eqOff_of_isPointOnJ h1 h2 h3 h4 h6, h5⟩⟩

end JPoints

end
