/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import Mathlib.Algebra.Polynomial.Derivative
public import Std.WP

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Transform
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import Mathlib.FieldTheory.Separable
import Std.Tactic.Do

/-!
# The contract of `read_input`

What `read_input` leaves when it accepts the command line (`JPoints.Cli.readInput_spec`): the
globals of the command line with the facts that the search needs (`JPoints.Cli.Input.WF`), from at
least two words that are not `-c list`, so that `main` takes no other path before it. The second
word gives the height bound, which neither the empty word, read for a missing second word, nor
`list` does (`JPoints.Cli.two_le_size_of_scanLong_eq_some`,
`JPoints.Cli.toList_ne_of_scanLong_eq_some`).

The coefficients that `read_input` reads lie in an array of seven entries, zero above the degree
(`JPoints.Cli.readCoefficients_spec`, `JPoints.Cli.HasDegree`). `squarefree` runs Euclid's
algorithm on the polynomial and its derivative over `ℚ` (`JPoints.Cli.squarefree_spec`): its arrays
hold polynomials (`JPoints.Cli.arrayPoly`) of the degrees that it keeps, and each remainder differs
from the dividend by a multiple of the divisor (`JPoints.Cli.remainderModulo_spec`), so that the
two polynomials are coprime only if the polynomial and its derivative are; a gcd of degree `0`
makes the polynomial separable, hence squarefree. The options keep the facts that
`settle_options` needs (`JPoints.Cli.Input.OptionsWF`: those of the coefficients and of the height
bound, `num_primes` in `[1, NUM_PRIMES]`, the numbers of sieving primes at least `-1` and the size
of the bit array at least `1`), option by option (`JPoints.Cli.setCosts_spec`,
`JPoints.Cli.setOption_spec`, `JPoints.Cli.readOption_spec`, `JPoints.Cli.readOptions_spec`), and
the reconciliation after them gives the facts of `JPoints.Cli.Input.WF`
(`JPoints.Cli.Input.OptionsWF.wf_settleOptions`).

## Main definitions

* `JPoints.Cli.arrayPoly`: the polynomial over `ℚ` with the entries of an array as coefficients.
* `JPoints.Cli.HasDegree`: an array holds the coefficients of a polynomial of a given degree.
* `JPoints.Cli.Input.OptionsWF`: the globals as the loop over the options keeps them.
* `JPoints.Cli.RemainderInvariant`, `JPoints.Cli.SubtractInvariant`,
  `JPoints.Cli.DescentInvariant`: the invariants of the loops of `JPoints.Cli.remainderModulo`.
* `JPoints.Cli.CopyInvariant`, `JPoints.Cli.DerivativeInvariant`, `JPoints.Cli.EuclidInvariant`:
  the invariants of the loops of `JPoints.Cli.squarefree`.
* `JPoints.Cli.ReadCoefficientsInvariant`, `JPoints.Cli.TrimInvariant`: the invariants of the
  loops of `JPoints.Cli.readCoefficients`.
* `JPoints.Cli.SetCostsInvariant`, `JPoints.Cli.ReadOptionsInvariant`: the invariants of the
  loops of `JPoints.Cli.setCosts` and `JPoints.Cli.readOptions`.

## Main statements

* `JPoints.Cli.readInput_spec`: the command lines that `read_input` accepts.
* `JPoints.Cli.squarefree_spec`: a polynomial that `squarefree` accepts is squarefree.
* `JPoints.Cli.remainderModulo_spec`: the remainder of one polynomial modulo another.
* `JPoints.Cli.readCoefficients_spec`: the coefficients and the degree that `read_input` reads.
* `JPoints.Cli.setCosts_spec`, `JPoints.Cli.setOption_spec`, `JPoints.Cli.readOption_spec`,
  `JPoints.Cli.readOptions_spec`: the options keep `JPoints.Cli.Input.OptionsWF`.
* `JPoints.Cli.Input.OptionsWF.wf_settleOptions`: `settle_options` gives `JPoints.Cli.Input.WF`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. Each loop has a named
invariant, irreducible in the proof of its contract, and each verification condition is discharged
by a lemma in its own shape. The contracts use no property of `scan_mpz` and `scan_long` beyond the
tests that `read_input` makes on what they return; the refusals of `read_input` in the terms of the
specification need lemmas on the reading of decimal numbers, which are not part of them.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints.Cli

/-! ### The polynomials of `squarefree` -/

section Polynomial

open Polynomial

/-- The polynomial over `ℚ` whose coefficients, constant term first, are the entries of the array
`p`: the polynomial that an array of `mpq_t`s of `squarefree` holds. -/
noncomputable def arrayPoly (p : Array ℚ) : ℚ[X] := ∑ i ∈ Finset.range p.size, C p[i]! * X ^ i

theorem coeff_arrayPoly (p : Array ℚ) (n : ℕ) : (arrayPoly p).coeff n = p[n]! := by
  simp only [arrayPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · exact (getElem!_neg p n h).symm

theorem arrayPoly_eq_of_getElem! {p : Array ℚ} {g : ℚ[X]} (h : ∀ n, p[n]! = g.coeff n) :
    arrayPoly p = g :=
  Polynomial.ext fun n ↦ (coeff_arrayPoly p n).trans (h n)

/-- The array `p` holds the coefficients, constant term first, of a polynomial of degree `d`, as the
arrays of `squarefree` and the coefficients of `read_input` do: the entries above the index `d` are
zero, the entries past the end read as `0` (the default of `ℤ` and of `ℚ`), and the entry at `d` is
not zero; `d = -1` for the zero polynomial. -/
structure HasDegree {α : Type*} [Zero α] [Inhabited α] (p : Array α) (d : ℤ) : Prop where
  /-- The degree is `-1` or more. -/
  neg_one_le : -1 ≤ d
  /-- The entries above the degree are zero. -/
  getElem!_eq_zero {n : ℕ} (h : d < n) : p[n]! = 0
  /-- The leading coefficient is not zero. -/
  getElem!_ne_zero (h : 0 ≤ d) : p[d.toNat]! ≠ 0

theorem HasDegree.lt_size {p : Array ℚ} {d : ℤ} (h : HasDegree p d) : d < p.size := by
  by_contra! hd
  exact h.getElem!_ne_zero (by lia) (getElem!_neg p d.toNat (by lia))

theorem HasDegree.arrayPoly_eq_zero {p : Array ℚ} {d : ℤ} (h : HasDegree p d) (hd : d < 0) :
    arrayPoly p = 0 :=
  arrayPoly_eq_of_getElem! fun n ↦ (h.getElem!_eq_zero (by lia)).trans (coeff_zero n).symm

theorem HasDegree.arrayPoly_eq_C {p : Array ℚ} (h : HasDegree p 0) : arrayPoly p = C p[0]! :=
  arrayPoly_eq_of_getElem! fun n ↦ by
    rcases n with _ | n
    · simp
    · rw [h.getElem!_eq_zero (by lia), coeff_C_succ]

/-! ### The remainder of a polynomial modulo another -/

/-- The invariant of the outer loop of `JPoints.Cli.remainderModulo` for the dividend `pu₀` and the
divisor `pv` of degree `dv`, at the array `pu` and the degree `du`: `pu` holds a polynomial of
degree `du` that differs from the dividend by a multiple of the divisor, in an array of the size of
`pu₀`; after the loop, `du < dv`. -/
def RemainderInvariant (pu₀ pv : Array ℚ) (dv : ℤ) : Std.WP.WhileInvariant (Array ℚ × ℤ) Prop :=
  .mk fun exit (pu, du) ↦ HasDegree pu du ∧ pu.size = pu₀.size ∧
    (∃ Q, arrayPoly pu = arrayPoly pu₀ - Q * arrayPoly pv) ∧ (exit = true → du < dv)

/-- The invariant of the loop of `JPoints.Cli.remainderModulo` that subtracts `q xˢ pv` from the
polynomial `pu` of degree `du`, for the divisor `pv` of degree `dv`, the quotient
`q = pu[du] / pv[dv]` of the leading coefficients and `s = du - dv`: after `i` steps, the array `p`
is `pu` with `q pv[j]` subtracted from the entry `s + j` for each `j < i`. -/
def SubtractInvariant (pu pv : Array ℚ) (du dv : ℤ) : Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ p ↦ p.size = pu.size ∧ ∀ n : ℕ, p[n]! = pu[n]! -
    if (du - dv).toNat ≤ n ∧ n - (du - dv).toNat < pref.length then
      pu[du.toNat]! / pv[dv.toNat]! * pv[n - (du - dv).toNat]! else 0

/-- The invariant of the loop of `JPoints.Cli.remainderModulo` that lowers the degree `d` from
`d₀` past the leading zeros of the array `p`: the entries above `d` are zero, and after the loop
the entry at `d` is not, unless `d = -1`. -/
def DescentInvariant (p : Array ℚ) (d₀ : ℤ) : Std.WP.WhileInvariant ℤ Prop :=
  .mk fun exit d ↦ d ≤ d₀ ∧ -1 ≤ d ∧ (∀ n : ℕ, d < n → p[n]! = 0) ∧
    (exit = true → 0 ≤ d → p[d.toNat]! ≠ 0)

theorem remainderInvariant_self {pu pv : Array ℚ} {du dv : ℤ}
    (h : HasDegree pu du ∧ HasDegree pv dv ∧ 0 ≤ dv) :
    RemainderInvariant pu pv dv false (pu, du) :=
  ⟨h.1, rfl, ⟨0, by simp⟩, nofun⟩

theorem RemainderInvariant.post {pu₀ pv pu : Array ℚ} {dv du : ℤ}
    (h : RemainderInvariant pu₀ pv dv true (pu, du)) :
    HasDegree pu du ∧ du < dv ∧ pu.size = pu₀.size ∧
      ∃ Q, arrayPoly pu = arrayPoly pu₀ - Q * arrayPoly pv :=
  ⟨h.1, h.2.2.2 rfl, h.2.1, h.2.2.1⟩

theorem RemainderInvariant.exit {pu₀ pv pu : Array ℚ} {dv du : ℤ} {m : ℕ} (hd : ¬dv ≤ du)
    (h : (du + 1).toNat = m ∧ RemainderInvariant pu₀ pv dv false (pu, du)) :
    RemainderInvariant pu₀ pv dv true (pu, du) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ by lia⟩

theorem subtractInvariant_nil (pu pv : Array ℚ) (du dv : ℤ) (suff : List ℕ) :
    SubtractInvariant pu pv du dv [] suff pu :=
  ⟨rfl, fun n ↦ by simp⟩

theorem SubtractInvariant.append_singleton {pu₀ pv pu p : Array ℚ} {du₀ dv du : ℤ} {m : ℕ}
    {pref suff : List ℕ} {cur : ℕ} (hpre : HasDegree pu₀ du₀ ∧ HasDegree pv dv ∧ 0 ≤ dv)
    (h : ForIn.toList [:dv.toNat + 1] = pref ++ cur :: suff)
    (hinv : SubtractInvariant pu pv du dv pref (cur :: suff) p)
    (hr : (du + 1).toNat = m ∧ RemainderInvariant pu₀ pv dv false (pu, du)) (hdu : dv ≤ du) :
    SubtractInvariant pu pv du dv (pref ++ [cur]) suff
      (p.set! (cur + (du - dv).toNat)
        (p[cur + (du - dv).toNat]! - pu[du.toNat]! / pv[dv.toNat]! * pv[cur]!)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  have hs := hr.2.1.lt_size
  obtain ⟨hsize, hp⟩ := hinv
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  have hpn := hp n
  have hpc := hp (cur + (du - dv).toNat)
  simp only [List.length_append, List.length_singleton]
  rcases lt_or_ge n p.size with hn | hn
  · rw [Array.getElem!_set! hn]
    split_ifs at hpn hpc ⊢ <;> grind
  · rw [getElem!_neg _ n (by simp; lia), getElem!_neg pu n (by lia)]
    split_ifs <;> grind

theorem SubtractInvariant.getElem!_eq {pu pv p : Array ℚ} {du dv : ℤ}
    (h : SubtractInvariant pu pv du dv (ForIn.toList [:dv.toNat + 1]) [] p) (hv : HasDegree pv dv)
    (n : ℕ) : p[n]! = pu[n]! - pu[du.toNat]! / pv[dv.toNat]! *
      if (du - dv).toNat ≤ n then pv[n - (du - dv).toNat]! else 0 := by
  rw [h.2 n, Std.Legacy.Range.length_toList, Nat.sub_zero]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.1 h2
  · rw [hv.getElem!_eq_zero (n := n - (du - dv).toNat) (by lia), mul_zero]
  · rw [mul_zero]

/-- After the loop that subtracts `q xˢ pv`, the array holds the polynomial of `pu` minus
`q xˢ pv`, `q` the quotient of the leading coefficients and `s = du - dv`. -/
theorem SubtractInvariant.arrayPoly_eq {pu pv p : Array ℚ} {du dv : ℤ}
    (h : SubtractInvariant pu pv du dv (ForIn.toList [:dv.toNat + 1]) [] p) (hv : HasDegree pv dv) :
    arrayPoly p = arrayPoly pu -
      C (pu[du.toNat]! / pv[dv.toNat]!) * (X ^ (du - dv).toNat * arrayPoly pv) :=
  arrayPoly_eq_of_getElem! fun n ↦ by
    rw [h.getElem!_eq hv, coeff_sub, coeff_C_mul, coeff_X_pow_mul', coeff_arrayPoly,
      coeff_arrayPoly]

/-- The subtraction of `q xˢ pv` cancels the leading coefficient of `pu`: the descent past the
leading zeros starts at `du - 1`. -/
theorem descentInvariant_sub_one {pu₀ pv pu p : Array ℚ} {du₀ dv du : ℤ} {m : ℕ}
    (hpre : HasDegree pu₀ du₀ ∧ HasDegree pv dv ∧ 0 ≤ dv) (hdu : dv ≤ du)
    (h : SubtractInvariant pu pv du dv (ForIn.toList [:dv.toNat + 1]) [] p)
    (hr : (du + 1).toNat = m ∧ RemainderInvariant pu₀ pv dv false (pu, du)) :
    DescentInvariant p (du - 1) false (du - 1) := by
  obtain ⟨-, hv, hdv⟩ := hpre
  have hu := hr.2.1
  refine ⟨le_rfl, by lia, fun n hn ↦ ?_, nofun⟩
  rw [h.getElem!_eq hv]
  rcases (show n = du.toNat ∨ du < n by lia) with rfl | hn'
  · rw [ite_eq_left (show (du - dv).toNat ≤ du.toNat by lia),
      show du.toNat - (du - dv).toNat = dv.toNat by lia,
      div_mul_cancel₀ _ (hv.getElem!_ne_zero hdv), sub_self]
  · rw [hu.getElem!_eq_zero hn']
    split_ifs
    · rw [hv.getElem!_eq_zero (n := n - (du - dv).toNat) (by lia), mul_zero, sub_zero]
    · rw [mul_zero, sub_zero]

theorem DescentInvariant.sub_one {p : Array ℚ} {d₀ d : ℤ} {m : ℕ}
    (hc : (decide (0 ≤ d) && p[d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ DescentInvariant p d₀ false d) :
    (d - 1 + 1).toNat < m ∧ DescentInvariant p d₀ false (d - 1) := by
  obtain ⟨rfl, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  refine ⟨by lia, by lia, by lia, fun n hn ↦ ?_, nofun⟩
  rcases (show n = d.toNat ∨ d < n by lia) with rfl | hn'
  · exact hc.2
  · exact hz n hn'

theorem DescentInvariant.exit {p : Array ℚ} {d₀ d : ℤ} {m : ℕ}
    (hc : ¬(decide (0 ≤ d) && p[d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ DescentInvariant p d₀ false d) : DescentInvariant p d₀ true d := by
  obtain ⟨-, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
  exact ⟨hd, hd', hz, fun _ ↦ hc⟩

/-- One pass of the outer loop of `JPoints.Cli.remainderModulo`: the polynomial after the
subtraction of `q xˢ pv` and the descent past its leading zeros has a lower degree, and still
differs from the dividend by a multiple of the divisor. -/
theorem RemainderInvariant.of_descentInvariant {pu₀ pv pu p : Array ℚ} {du₀ dv du d : ℤ} {m : ℕ}
    (hpre : HasDegree pu₀ du₀ ∧ HasDegree pv dv ∧ 0 ≤ dv) (hdu : dv ≤ du)
    (h : SubtractInvariant pu pv du dv (ForIn.toList [:dv.toNat + 1]) [] p)
    (hd : DescentInvariant p (du - 1) true d)
    (hr : (du + 1).toNat = m ∧ RemainderInvariant pu₀ pv dv false (pu, du)) :
    (d + 1).toNat < m ∧ RemainderInvariant pu₀ pv dv false (p, d) := by
  obtain ⟨-, hv, hdv⟩ := hpre
  obtain ⟨rfl, -, hsize, ⟨Q, hQ⟩, -⟩ := hr
  obtain ⟨hd1, hd2, hz, hnz⟩ := hd
  refine ⟨by lia, ⟨hd2, fun hn ↦ hz _ hn, hnz rfl⟩, h.1.trans hsize, ⟨Q + C (pu[du.toNat]! /
    pv[dv.toNat]!) * X ^ (du - dv).toNat, ?_⟩, nofun⟩
  rw [h.arrayPoly_eq hv, hQ]
  ring

attribute [local irreducible] RemainderInvariant SubtractInvariant DescentInvariant in
/-- The loop of `squarefree` that replaces the polynomial `pu` of degree `du` by its remainder
modulo the polynomial `pv` of degree `dv ≥ 0`: the remainder is of lower degree than `pv`, in an
array of the size of `pu`, and differs from `pu` by a multiple of `pv`. -/
@[spec]
theorem remainderModulo_spec (pu pv : Array ℚ) (du dv : ℤ) :
    ⦃ HasDegree pu du ∧ HasDegree pv dv ∧ 0 ≤ dv ⦄ remainderModulo pu pv du dv
    ⦃ fun r ↦ HasDegree r.1 r.2 ∧ r.2 < dv ∧ r.1.size = pu.size ∧
        ∃ Q, arrayPoly r.1 = arrayPoly pu - Q * arrayPoly pv ⦄ := by
  vcgen [remainderModulo] invariants
  | inv1 => RemainderInvariant pu pv dv
  | inv2 => .ofMeasure fun s : Array ℚ × ℤ ↦ (s.2 + 1).toNat
  | inv3 pu' du' _ _ _ => SubtractInvariant pu' pv du' dv
  | inv4 du' _ _ _ p _ => DescentInvariant p (du' - 1)
  | inv5 => .ofMeasure fun d : ℤ ↦ (d + 1).toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact remainderInvariant_self ‹_›
    | exact RemainderInvariant.post ‹_›
    | exact RemainderInvariant.exit ‹_› ‹_›
    | exact subtractInvariant_nil _ _ _ _ _
    | exact SubtractInvariant.append_singleton ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact descentInvariant_sub_one ‹_› ‹_› ‹_› ‹_›
    | exact RemainderInvariant.of_descentInvariant ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact DescentInvariant.sub_one ‹_› ‹_›
    | exact DescentInvariant.exit ‹_› ‹_›

/-! ### Squarefreeness -/

/-- The invariant of the loop of `JPoints.Cli.squarefree` that copies the coefficients `coeffs`
into the array `pu` of seven rationals: after `i` steps, the entries below `i` are the
coefficients, the others zero. -/
def CopyInvariant (coeffs : Array ℤ) : Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ pu ↦ pu.size = 7 ∧ ∀ n : ℕ, pu[n]! = if n < pref.length then (coeffs[n]! : ℚ) else 0

/-- The invariant of the loop of `JPoints.Cli.squarefree` that writes the coefficients of the
derivative of the polynomial with the coefficients `coeffs` into the array `pv` of seven rationals:
after `i` steps, the entries below `i` are those of the derivative, the others zero. -/
def DerivativeInvariant (coeffs : Array ℤ) : Std.WP.Invariant ℕ (Array ℚ) Prop :=
  fun pref _ pv ↦ pv.size = 7 ∧
    ∀ n : ℕ, pv[n]! = if n < pref.length then (coeffs[n + 1]! : ℚ) * (n + 1) else 0

/-- The invariant of Euclid's algorithm in `JPoints.Cli.squarefree` on the polynomial `f` and its
derivative, at the arrays `pu`, `pv` and the degrees `du`, `dv`: the arrays hold polynomials of
these degrees, which are coprime only if `f` and its derivative are; after the loop, `dv < 0`. -/
def EuclidInvariant (f : ℚ[X]) : Std.WP.WhileInvariant (Array ℚ × Array ℚ × ℤ × ℤ) Prop :=
  .mk fun exit (pu, pv, du, dv) ↦ HasDegree pu du ∧ HasDegree pv dv ∧
    (IsCoprime (arrayPoly pu) (arrayPoly pv) → IsCoprime f (derivative f)) ∧
    (exit = true → dv < 0)

theorem copyInvariant_nil (coeffs : Array ℤ) (suff : List ℕ) :
    CopyInvariant coeffs [] suff (Array.replicate 7 0) :=
  ⟨by simp, fun n ↦ Array.getElem!_replicate_default 7 n⟩

theorem derivativeInvariant_nil (coeffs : Array ℤ) (suff : List ℕ) :
    DerivativeInvariant coeffs [] suff (Array.replicate 7 0) :=
  ⟨by simp, fun n ↦ Array.getElem!_replicate_default 7 n⟩

theorem CopyInvariant.append_singleton {coeffs : Array ℤ} {degree : ℤ} {pref suff : List ℕ}
    {cur : ℕ} (hpre : HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7)
    (h : ForIn.toList [:(degree + 1).toNat] = pref ++ cur :: suff) {pu : Array ℚ}
    (hinv : CopyInvariant coeffs pref (cur :: suff) pu) :
    CopyInvariant coeffs (pref ++ [cur]) suff (pu.set! cur (coeffs[cur]! : ℚ)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  obtain ⟨hsize, hp⟩ := hinv
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  have := hp n
  grind

theorem DerivativeInvariant.append_singleton {coeffs : Array ℤ} {degree : ℤ} {pref suff : List ℕ}
    {cur : ℕ} (hpre : HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7)
    (h : ForIn.toList [1:(degree + 1).toNat] = pref ++ cur :: suff) {pv : Array ℚ}
    (hinv : DerivativeInvariant coeffs pref (cur :: suff) pv) :
    DerivativeInvariant coeffs (pref ++ [cur]) suff
      (pv.set! (cur - 1) ((coeffs[cur]! : ℚ) * (cur : ℚ))) := by
  obtain rfl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons h
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons h
  obtain ⟨hsize, hp⟩ := hinv
  refine ⟨by simp [hsize], fun n ↦ ?_⟩
  have := hp n
  rw [Nat.add_sub_cancel_left]
  grind

theorem CopyInvariant.getElem!_eq {coeffs : Array ℤ} {degree : ℤ} {pu : Array ℚ}
    (hpre : HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7)
    (h : CopyInvariant coeffs (ForIn.toList [:(degree + 1).toNat]) [] pu) (n : ℕ) :
    pu[n]! = coeffs[n]! := by
  rw [h.2 n, Std.Legacy.Range.length_toList]
  split_ifs with hn
  · rfl
  · rw [hpre.1.getElem!_eq_zero (by lia), Int.cast_zero]

theorem DerivativeInvariant.getElem!_eq {coeffs : Array ℤ} {degree : ℤ} {pv : Array ℚ}
    (hpre : HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7)
    (h : DerivativeInvariant coeffs (ForIn.toList [1:(degree + 1).toNat]) [] pv) (n : ℕ) :
    pv[n]! = coeffs[n + 1]! * (n + 1) := by
  rw [h.2 n, Std.Legacy.Range.length_toList]
  split_ifs with hn
  · rfl
  · rw [hpre.1.getElem!_eq_zero (n := n + 1) (by lia), Int.cast_zero, zero_mul]

/-- After the two loops that copy the coefficients and those of the derivative, the arrays hold the
polynomial and its derivative, of the degrees `degree` and `degree - 1`. -/
theorem euclidInvariant_derivative {coeffs : Array ℤ} {degree : ℤ} {pu pv : Array ℚ}
    (hpre : HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7)
    (hu : CopyInvariant coeffs (ForIn.toList [:(degree + 1).toNat]) [] pu)
    (hv : DerivativeInvariant coeffs (ForIn.toList [1:(degree + 1).toNat]) [] pv) :
    EuclidInvariant (poly coeffs.toList) false (pu, pv, degree, degree - 1) := by
  have hc := hpre.1
  have hu' := hu.getElem!_eq hpre
  have hv' := hv.getElem!_eq hpre
  have hpu : arrayPoly pu = poly coeffs.toList :=
    arrayPoly_eq_of_getElem! fun n ↦ by rw [hu', coeff_poly, Array.getD_toList_eq_getElem!]
  have hpv : arrayPoly pv = derivative (poly coeffs.toList) :=
    arrayPoly_eq_of_getElem! fun n ↦ by
      rw [hv', coeff_derivative, coeff_poly, Array.getD_toList_eq_getElem!]
  refine ⟨⟨by lia, fun hn ↦ ?_, fun _ ↦ ?_⟩, ⟨by lia, fun hn ↦ ?_, fun _ ↦ ?_⟩, ?_, nofun⟩
  · rw [hu', hc.getElem!_eq_zero hn, Int.cast_zero]
  · rw [hu']
    exact_mod_cast hc.getElem!_ne_zero (by lia)
  · rw [hv', hc.getElem!_eq_zero (by lia), Int.cast_zero, zero_mul]
  · rw [hv', show (degree - 1).toNat + 1 = degree.toNat by lia]
    exact mul_ne_zero (mod_cast hc.getElem!_ne_zero (by lia)) (by positivity)
  · rw [hpu, hpv]
    exact id

theorem EuclidInvariant.hasDegree {f : ℚ[X]} {pu pv : Array ℚ} {du dv : ℤ} {m : ℕ} (hd : 0 ≤ dv)
    (h : (dv + 1).toNat = m ∧ EuclidInvariant f false (pu, pv, du, dv)) :
    HasDegree pu du ∧ HasDegree pv dv ∧ 0 ≤ dv :=
  ⟨h.2.1, h.2.2.1, hd⟩

/-- One step of Euclid's algorithm: the divisor and the remainder are coprime only if the dividend
and the divisor are. -/
theorem EuclidInvariant.remainder {f : ℚ[X]} {pu pv p : Array ℚ} {du dv d : ℤ} {m : ℕ}
    (hr : HasDegree p d ∧ d < dv ∧ p.size = pu.size ∧
      ∃ Q, arrayPoly p = arrayPoly pu - Q * arrayPoly pv)
    (h : (dv + 1).toNat = m ∧ EuclidInvariant f false (pu, pv, du, dv)) :
    (d + 1).toNat < m ∧ EuclidInvariant f false (pv, p, dv, d) := by
  obtain ⟨hp, hd, -, Q, hQ⟩ := hr
  obtain ⟨rfl, -, hv, hcop, -⟩ := h
  refine ⟨by lia [hp.neg_one_le], hv, hp, fun hc ↦ hcop ?_, nofun⟩
  rw [show arrayPoly pu = arrayPoly p + Q * arrayPoly pv by rw [hQ]; ring]
  exact hc.symm.add_mul_right_left Q

theorem EuclidInvariant.exit {f : ℚ[X]} {pu pv : Array ℚ} {du dv : ℤ} {m : ℕ} (hd : ¬0 ≤ dv)
    (h : (dv + 1).toNat = m ∧ EuclidInvariant f false (pu, pv, du, dv)) :
    EuclidInvariant f true (pu, pv, du, dv) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ by lia⟩

/-- At the end of Euclid's algorithm, a gcd of degree `0` makes `f` separable, hence
squarefree. -/
theorem EuclidInvariant.squarefree {f : ℚ[X]} {pu pv : Array ℚ} {du dv : ℤ}
    (h : EuclidInvariant f true (pu, pv, du, dv)) (hd : (du == 0) = true) : Squarefree f := by
  obtain ⟨hu, hv, hcop, hdv⟩ := h
  obtain rfl := beq_iff_eq.mp hd
  refine Polynomial.Separable.squarefree (hcop ?_)
  rw [hu.arrayPoly_eq_C, hv.arrayPoly_eq_zero (hdv rfl), isCoprime_zero_right, isUnit_C]
  exact isUnit_iff_ne_zero.mpr (hu.getElem!_ne_zero le_rfl)

attribute [local irreducible] CopyInvariant DerivativeInvariant EuclidInvariant in
/-- Of the polynomials of a degree from `1` to `6`, `squarefree` accepts only squarefree ones: the
gcd that Euclid's algorithm leaves is a nonzero constant only if the polynomial and its derivative
are coprime. -/
@[spec]
theorem squarefree_spec (coeffs : Array ℤ) (degree : ℤ) :
    ⦃ HasDegree coeffs degree ∧ 0 < degree ∧ degree < 7 ⦄ squarefree coeffs degree
    ⦃ fun r ↦ r = true → Squarefree (poly coeffs.toList) ⦄ := by
  vcgen [squarefree] invariants
  | inv1 => CopyInvariant coeffs
  | inv2 => DerivativeInvariant coeffs
  | inv3 => EuclidInvariant (poly coeffs.toList)
  | inv4 => .ofMeasure fun s : Array ℚ × Array ℚ × ℤ × ℤ ↦ (s.2.2.2 + 1).toNat
  all_goals try vc_simp
  all_goals with_reducible first
    | exact copyInvariant_nil _ _
    | exact derivativeInvariant_nil _ _
    | exact CopyInvariant.append_singleton ‹_› ‹_› ‹_›
    | exact DerivativeInvariant.append_singleton ‹_› ‹_› ‹_›
    | exact euclidInvariant_derivative ‹_› ‹_› ‹_›
    | exact EuclidInvariant.hasDegree ‹_› ‹_›
    | exact EuclidInvariant.remainder ‹_› ‹_›
    | exact EuclidInvariant.exit ‹_› ‹_›
    | exact EuclidInvariant.squarefree ‹_› ‹_›

end Polynomial

/-! ### The coefficients -/

theorem HasDegree.set!_zero {c : Array ℤ} {d : ℤ} (h : HasDegree c d) {i : ℕ} (hi : d < i) :
    HasDegree (c.set! i 0) d := by
  refine ⟨h.neg_one_le, fun {n} hn ↦ ?_, fun hd ↦ ?_⟩
  · rcases eq_or_ne i n with rfl | hin
    · rcases lt_or_ge i c.size with hs | hs
      · rw [Array.getElem!_set!_self _ _ _ hs]
      · rw [getElem!_neg _ i (by simp; lia)]
        rfl
    · rw [Array.getElem!_set!_ne _ _ _ _ hin, h.getElem!_eq_zero hn]
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h.getElem!_ne_zero hd

/-- The degree of the coefficients is that of the specification. -/
theorem HasDegree.degree_toList {c : Array ℤ} {d : ℤ} (h : HasDegree c d) (hd : 0 ≤ d) :
    (JPoints.degree c.toList : ℤ) = d := by
  have hne : c.toList.getD d.toNat 0 ≠ 0 := by
    rw [Array.getD_toList_eq_getElem!]
    exact h.getElem!_ne_zero hd
  rw [degree_eq_of_getD_ne_zero hne fun i hi ↦ by
    rw [Array.getD_toList_eq_getElem!, h.getElem!_eq_zero (by lia)]]
  lia

/-- The invariant of the loop of `JPoints.Cli.readCoefficients` over the integers of the first
word, at the array `c` and the number `d` of integers read: seven entries, of which those from
the index `d` on are still the zeros of the start. -/
def ReadCoefficientsInvariant : Std.WP.WhileInvariant (Option (List Char) × Array ℤ × ℤ) Prop :=
  .mk fun _ (_, c, d) ↦ c.size = 7 ∧ 0 ≤ d ∧ d ≤ 7 ∧ ∀ n : ℕ, d ≤ n → c[n]! = 0

/-- The invariant of the loop of `JPoints.Cli.readCoefficients` that lowers the degree `d` past the
zero leading coefficients of `c`, down to `0`: the entries above `d` are zero, and after the loop
the entry at `d` is not, unless `d ≤ 0`. -/
def TrimInvariant (c : Array ℤ) : Std.WP.WhileInvariant ℤ Prop :=
  .mk fun exit d ↦ -1 ≤ d ∧ d ≤ 6 ∧ (∀ n : ℕ, d < n → c[n]! = 0) ∧
    (exit = true → 0 < d → c[d.toNat]! ≠ 0)

theorem readCoefficientsInvariant_zero {coeffs : Array ℤ}
    (h : coeffs.size = 7 ∧ ∀ n : ℕ, coeffs[n]! = 0) (s : List Char) :
    ReadCoefficientsInvariant false (some s, coeffs, 0) :=
  ⟨h.1, le_rfl, by lia, fun n _ ↦ h.2 n⟩

theorem ReadCoefficientsInvariant.add_one {s : Option (List Char)} {c : Array ℤ} {d : ℤ} {m : ℕ}
    (hd : d ≤ 6) (h : (7 - d).toNat = m ∧ ReadCoefficientsInvariant false (s, c, d))
    (s' : Option (List Char)) (x : ℤ) :
    (7 - (d + 1)).toNat < m ∧ ReadCoefficientsInvariant false (s', c.set! d.toNat x, d + 1) := by
  obtain ⟨rfl, hs, hd0, hd7, hz⟩ := h
  refine ⟨by lia, by simp [hs], by lia, by lia, fun n hn ↦ ?_⟩
  rw [Array.getElem!_set!_ne _ _ _ _ (by lia), hz n (by lia)]

theorem ReadCoefficientsInvariant.exit {s : Option (List Char)} {c : Array ℤ} {d : ℤ} {m : ℕ}
    (h : (7 - d).toNat = m ∧ ReadCoefficientsInvariant false (s, c, d))
    (s' : Option (List Char)) : ReadCoefficientsInvariant true (s', c, d) :=
  h.2

theorem trimInvariant_sub_one {s : Option (List Char)} {c : Array ℤ} {d : ℤ}
    (h : ReadCoefficientsInvariant true (s, c, d)) : TrimInvariant c false (d - 1) := by
  obtain ⟨-, hd0, hd7, hz⟩ := h
  exact ⟨by lia, by lia, fun n hn ↦ hz n (by lia), nofun⟩

theorem TrimInvariant.sub_one {c : Array ℤ} {d : ℤ} {m : ℕ}
    (hc : (decide (0 < d) && c[d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ TrimInvariant c false d) :
    (d - 1 + 1).toNat < m ∧ TrimInvariant c false (d - 1) := by
  obtain ⟨rfl, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  refine ⟨by lia, by lia, by lia, fun n hn ↦ ?_, nofun⟩
  rcases (show n = d.toNat ∨ d < n by lia) with rfl | hn'
  · exact hc.2
  · exact hz n hn'

theorem TrimInvariant.exit {c : Array ℤ} {d : ℤ} {m : ℕ}
    (hc : ¬(decide (0 < d) && c[d.toNat]! == 0) = true)
    (h : (d + 1).toNat = m ∧ TrimInvariant c false d) : TrimInvariant c true d := by
  obtain ⟨-, hd, hd', hz, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
  exact ⟨hd, hd', hz, fun _ ↦ hc⟩

theorem TrimInvariant.post {s : Option (List Char)} {c c' : Array ℤ} {d₁ d d' : ℤ}
    (hc : ReadCoefficientsInvariant true (s, c, d₁)) (h : TrimInvariant c true d)
    (he : some (c, d) = some (c', d')) :
    c'.size = 7 ∧ d' < 7 ∧ (0 < d' → HasDegree c' d') := by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  obtain ⟨hd, hd', hz, hnz⟩ := h
  exact ⟨hc.1, by lia, fun hd0 ↦ ⟨hd, fun hn ↦ hz _ hn, fun _ ↦ hnz rfl hd0⟩⟩

attribute [local irreducible] ReadCoefficientsInvariant TrimInvariant in
/-- The coefficients that `read_input` reads into an array of seven zeros and their degree: seven
entries, a degree below `7`, and for a positive degree a polynomial of that degree. -/
@[spec]
theorem readCoefficients_spec (s : List Char) (coeffs : Array ℤ) :
    ⦃ coeffs.size = 7 ∧ ∀ n : ℕ, coeffs[n]! = 0 ⦄ readCoefficients s coeffs
    ⦃ fun r ↦ ∀ c d, r = some (c, d) → c.size = 7 ∧ d < 7 ∧ (0 < d → HasDegree c d) ⦄ := by
  vcgen [readCoefficients] invariants
  | inv1 => ReadCoefficientsInvariant
  | inv2 => .ofMeasure fun s : Option (List Char) × Array ℤ × ℤ ↦ (7 - s.2.2).toNat
  | inv3 c _ _ _ _ _ => TrimInvariant c
  | inv4 => .ofMeasure fun d : ℤ ↦ (d + 1).toNat
  all_goals try vc_simp [reduceCtorEq]
  all_goals with_reducible first
    | exact readCoefficientsInvariant_zero ‹_› _
    | exact ReadCoefficientsInvariant.add_one ‹_› ‹_› _ _
    | exact ReadCoefficientsInvariant.exit ‹_› _
    | exact trimInvariant_sub_one ‹_›
    | exact TrimInvariant.sub_one ‹_› ‹_›
    | exact TrimInvariant.exit ‹_› ‹_›
    | exact TrimInvariant.post ‹_› ‹_› ‹_›

/-! ### The options -/

/-- The globals `st` of the command line as the loop of `read_input` over the options keeps them,
before `settle_options`: seven coefficients of a squarefree polynomial whose degree, at least `5`,
is that of their list; `1 ≤ height ≤ MAX_HEIGHT`; `num_primes` in `[1, NUM_PRIMES]`; the numbers of
sieving primes `-1` (the choice of the cost model) or nonnegative; the size of the bit array at
least `1`; and the bound on the fourth coordinate a `long`. -/
structure Input.OptionsWF (st : Input) : Prop where
  /-- Seven coefficients. -/
  size_coeffs : st.coeffs.size = 7
  /-- The degree is that of the coefficients. -/
  degree_coeffs : (JPoints.degree st.coeffs.toList : ℤ) = st.degree
  /-- The degree is at least `5`. -/
  five_le_degree : 5 ≤ st.degree
  /-- The polynomial is squarefree. -/
  squarefree : Squarefree (poly st.coeffs.toList)
  /-- The height bound is positive. -/
  one_le_height : 1 ≤ st.height
  /-- The height bound is at most `MAX_HEIGHT`. -/
  height_le_maxHeight : st.height ≤ maxHeight
  /-- `num_primes` is positive. -/
  one_le_numPrimes : 1 ≤ st.numPrimes
  /-- `num_primes` is at most `NUM_PRIMES`. -/
  numPrimes_le : st.numPrimes ≤ JPoints.numPrimes
  /-- `sieve_primes1` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes1 : -1 ≤ st.sievePrimes1
  /-- `sieve_primes2` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes2 : -1 ≤ st.sievePrimes2
  /-- `sieve_primes3` is `-1` or nonnegative. -/
  neg_one_le_sievePrimes3 : -1 ≤ st.sievePrimes3
  /-- The size of the bit array is positive. -/
  one_le_arraySize : 1 ≤ st.arraySize
  /-- The bound on the fourth coordinate is a `long`. -/
  dbound_lt : st.dbound < 2 ^ 63

/-- `scan_long` reads a `long`. -/
theorem lt_of_scanLong_eq_some {s : List Char} {x : ℤ} (h : scanLong s = some x) :
    x < 2 ^ 63 := by
  simp only [scanLong, strtol] at h
  split_ifs at h <;> simp_all
  lia

namespace Input.OptionsWF

variable {st : Input}

/-- `JPoints.Cli.Input.OptionsWF` reads only the coefficients, the degree, the height bound,
`num_primes`, the numbers of sieving primes, the size of the bit array and the bound on the fourth
coordinate. -/
theorem of_eq {st' : Input} (h : st.OptionsWF) (hc : st'.coeffs = st.coeffs)
    (hd : st'.degree = st.degree) (hh : st'.height = st.height) (hp : st'.numPrimes = st.numPrimes)
    (h1 : st'.sievePrimes1 = st.sievePrimes1) (h2 : st'.sievePrimes2 = st.sievePrimes2)
    (h3 : st'.sievePrimes3 = st.sievePrimes3) (ha : st'.arraySize = st.arraySize)
    (hw : st'.dbound = st.dbound) : st'.OptionsWF :=
  ⟨hc ▸ h.1, hc ▸ hd ▸ h.2, hd ▸ h.3, hc ▸ h.4, hh ▸ h.5, hh ▸ h.6, hp ▸ h.7, hp ▸ h.8,
    h1 ▸ h.9, h2 ▸ h.10, h3 ▸ h.11, ha ▸ h.12, hw ▸ h.13⟩

theorem setSievePrimes1 (h : st.OptionsWF) (x : ℤ) :
    { st with sievePrimes1 := if x < 0 then 0 else x }.OptionsWF :=
  { h with neg_one_le_sievePrimes1 := by split_ifs <;> lia }

theorem setSievePrimes2 (h : st.OptionsWF) (x : ℤ) :
    { st with sievePrimes2 := if x < 0 then 0 else x }.OptionsWF :=
  { h with neg_one_le_sievePrimes2 := by split_ifs <;> lia }

theorem setSievePrimes3 (h : st.OptionsWF) (x : ℤ) :
    { st with sievePrimes3 := if x < 0 then 0 else x }.OptionsWF :=
  { h with neg_one_le_sievePrimes3 := by split_ifs <;> lia }

theorem setArraySize (h : st.OptionsWF) {x : ℤ} (hx : ¬x ≤ 0) :
    { st with arraySize := x }.OptionsWF :=
  { h with one_le_arraySize := by lia }

theorem setDbound (h : st.OptionsWF) {v : List Char} {x : ℤ} (hx : scanLong v = some x) :
    { st with dbound := x }.OptionsWF :=
  { h with dbound_lt := lt_of_scanLong_eq_some hx }

theorem setNumPrimes (h : st.OptionsWF) {x : ℤ} (hx : ¬x ≤ 0) :
    { st with
      numPrimes := if (JPoints.numPrimes : ℤ) < x then JPoints.numPrimes else x }.OptionsWF :=
  { h with
    one_le_numPrimes := by split_ifs <;> lia [numPrimes_pos]
    numPrimes_le := by split_ifs <;> lia }

/-- `settle_options` reconciles the numbers of sieving primes with each other and with
`num_primes`, and the bound on the fourth coordinate with the height bound and `-a`, so that the
globals have the facts of `JPoints.Cli.Input.WF`. -/
theorem wf_settleOptions (h : st.OptionsWF) : (settleOptions st).WF := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hm : (maxHeight : ℤ) < 2 ^ 63 :=
    mod_cast (Nat.le_self_pow two_ne_zero maxHeight).trans_lt maxHeight_sq_lt
  constructor <;> simp only [settleOptions] <;> grind

end Input.OptionsWF

/-- The invariant of the loop of `JPoints.Cli.setCosts` over the items of the argument of `-c`, at
the value returned early `ret`, the rest of the argument and the globals `st`: no globals are
returned early, and `st` has the facts of `JPoints.Cli.Input.OptionsWF`. -/
def SetCostsInvariant : Std.WP.WhileInvariant (Option (Option Input) × List Char × Input) Prop :=
  .mk fun _ (ret, _, st) ↦ ret.join = none ∧ st.OptionsWF

theorem setCostsInvariant_none {st : Input} (h : st.OptionsWF) (s : List Char) :
    SetCostsInvariant false (none, s, st) :=
  ⟨rfl, h⟩

theorem SetCostsInvariant.exit {ret r : Option (Option Input)} {s : List Char} {st : Input} {m : ℕ}
    (h : s.length = m ∧ SetCostsInvariant false (ret, s, st)) (hr : r.join = none) :
    SetCostsInvariant true (r, s, st) :=
  ⟨hr, h.2.2⟩

/-- One item of the argument of `-c`: the rest after it is shorter, and the constants of the cost
model that it sets keep `JPoints.Cli.Input.OptionsWF`. -/
theorem SetCostsInvariant.setCost {ret : Option (Option Input)} {s : List Char} {st : Input}
    {m : ℕ} (hs : (!s.isEmpty) = true) (h : s.length = m ∧ SetCostsInvariant false (ret, s, st))
    {c : Prop} {_ : Decidable c} {n j : ℕ} {cs : Costs} {cset : Array Bool} {b : Bool} :
    (if c then ((s.drop (j + 1)).drop n).tail else (s.drop (j + 1)).drop n).length < m ∧
      SetCostsInvariant false (none, if c then ((s.drop (j + 1)).drop n).tail else
        (s.drop (j + 1)).drop n, { st with costs := cs, costSet := cset, costsSet := b }) := by
  obtain ⟨rfl, -, hst⟩ := h
  refine ⟨?_, rfl, { hst with }⟩
  have : s.length ≠ 0 := by simpa using hs
  split_ifs <;> simp <;> lia

theorem SetCostsInvariant.post_some {ret : Option (Option Input)} {s : List Char} {st st' : Input}
    {r : Option Input} (h : SetCostsInvariant true (ret, s, st)) (h1 : ret = some r)
    (h2 : r = some st') : st'.OptionsWF := by
  obtain ⟨hj, -⟩ := h
  simp [h1, h2] at hj

theorem SetCostsInvariant.post_none {ret : Option (Option Input)} {s : List Char} {st st' : Input}
    (h : SetCostsInvariant true (ret, s, st)) (h2 : some st = some st') : st'.OptionsWF :=
  Option.some.inj h2 ▸ h.2

attribute [local irreducible] SetCostsInvariant in
/-- The constants of the cost model that `-c` sets keep `JPoints.Cli.Input.OptionsWF`. -/
@[spec]
theorem setCosts_spec (s : List Char) (st : Input) :
    ⦃ st.OptionsWF ⦄ setCosts s st ⦃ fun r ↦ ∀ st', r = some st' → st'.OptionsWF ⦄ := by
  vcgen [setCosts] invariants
  | inv1 => SetCostsInvariant
  | inv2 => .ofMeasure fun s : Option (Option Input) × List Char × Input ↦ s.2.1.length
  all_goals try vc_simp
  all_goals with_reducible first
    | exact setCostsInvariant_none ‹_› _
    | exact SetCostsInvariant.exit ‹_› rfl
    | exact SetCostsInvariant.setCost ‹_› ‹_›
    | exact SetCostsInvariant.post_some ‹_› ‹_› ‹_›
    | exact SetCostsInvariant.post_none ‹_› ‹_›

/-- The value of an option keeps `JPoints.Cli.Input.OptionsWF`: the values of `-n`, `-M` and `-N`
are made nonnegative, those of `-s` and `-p` are positive, and that of `-p` is made at most
`NUM_PRIMES`. -/
@[spec]
theorem setOption_spec (o : Char) (v : List Char) (st : Input) :
    ⦃ st.OptionsWF ⦄ setOption o v st ⦃ fun r ↦ ∀ st', r = .ok st' → st'.OptionsWF ⦄ := by
  vcgen [setOption]
  all_goals try vc_simp [Except.ok.injEq, reduceCtorEq]
  all_goals try obtain ⟨_, rfl⟩ := Except.ite_error_eq_ok_iff.mp ‹_›
  all_goals subst_vars
  all_goals have hst := ‹Input.OptionsWF _›
  all_goals first
    | exact ‹∀ st' : Input, some _ = some st' → st'.OptionsWF› _ rfl
    | exact hst.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl
    | exact hst.setDbound ‹_›
    | exact hst.setSievePrimes1 _
    | exact hst.setSievePrimes2 _
    | exact hst.setSievePrimes3 _
    | exact hst.setArraySize ‹_›
    | exact hst.setNumPrimes ‹_›

/-- An option keeps `JPoints.Cli.Input.OptionsWF`, and the next one is after it. -/
@[spec]
theorem readOption_spec (args : Array String) (i : ℕ) (st : Input) :
    ⦃ st.OptionsWF ⦄ readOption args i st
    ⦃ fun r ↦ ∀ st' i', r = .ok (st', i') → i < i' ∧ st'.OptionsWF ⦄ := by
  vcgen [readOption]
  all_goals try vc_simp [Except.ok.injEq, reduceCtorEq, Prod.mk.injEq]
  all_goals obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
  all_goals subst_vars
  all_goals have hst := ‹Input.OptionsWF _›
  all_goals first
    | exact ⟨by lia, hst.of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
    | exact ⟨by lia, ‹∀ st' : Input, Except.ok _ = Except.ok st' → st'.OptionsWF› _ rfl⟩

/-- The invariant of the loop of `JPoints.Cli.readOptions` over the options, at the value returned
early `ret`, the globals `st` and the index of the next option: `st` has the facts of
`JPoints.Cli.Input.OptionsWF`, and globals returned early have them too. -/
def ReadOptionsInvariant :
    Std.WP.WhileInvariant (Option (Except Failure Input) × Input × ℕ) Prop :=
  .mk fun _ (ret, st, _) ↦ st.OptionsWF ∧ ∀ st', ret = some (.ok st') → st'.OptionsWF

theorem readOptionsInvariant_none {st : Input} (h : st.OptionsWF) :
    ReadOptionsInvariant false (none, st, 3) :=
  ⟨h, fun _ h ↦ by cases h⟩

theorem ReadOptionsInvariant.post_some {ret : Option (Except Failure Input)} {st st' : Input}
    {i : ℕ} {r : Except Failure Input} (h : ReadOptionsInvariant true (ret, st, i))
    (h1 : ret = some r) (h2 : r = .ok st') : st'.OptionsWF :=
  h.2 st' (h2 ▸ h1)

theorem ReadOptionsInvariant.post_none {ret : Option (Except Failure Input)} {st st' : Input}
    {i : ℕ} (h : ReadOptionsInvariant true (ret, st, i))
    (h2 : (.ok st : Except Failure Input) = .ok st') : st'.OptionsWF :=
  Except.ok.inj h2 ▸ h.1

theorem ReadOptionsInvariant.optionsWF {ret : Option (Except Failure Input)} {st : Input}
    {n i m : ℕ} (h : n + 1 - i = m ∧ ReadOptionsInvariant false (ret, st, i)) : st.OptionsWF :=
  h.2.1

theorem ReadOptionsInvariant.of_readOption {ret : Option (Except Failure Input)} {st st' : Input}
    {n i i' m : ℕ} {r : Except Failure (Input × ℕ)} (hi : i ≤ n)
    (hr : ∀ st' i', r = .ok (st', i') → i < i' ∧ st'.OptionsWF) (he : r = .ok (st', i'))
    (h : n + 1 - i = m ∧ ReadOptionsInvariant false (ret, st, i)) :
    n + 1 - i' < m ∧ ReadOptionsInvariant false (none, st', i') := by
  obtain ⟨hi', hst⟩ := hr st' i' he
  exact ⟨by lia, hst, fun _ h ↦ by cases h⟩

theorem ReadOptionsInvariant.exit {ret ret' : Option (Except Failure Input)} {st : Input}
    {n i m : ℕ} (h : n + 1 - i = m ∧ ReadOptionsInvariant false (ret, st, i))
    (hr : ∀ st', ret' = some (.ok st') → st'.OptionsWF) :
    ReadOptionsInvariant true (ret', st, i) :=
  ⟨h.2.1, hr⟩

attribute [local irreducible] ReadOptionsInvariant in
/-- The options keep `JPoints.Cli.Input.OptionsWF`. -/
@[spec]
theorem readOptions_spec (args : Array String) (st : Input) :
    ⦃ st.OptionsWF ⦄ readOptions args st ⦃ fun r ↦ ∀ st', r = .ok st' → st'.OptionsWF ⦄ := by
  vcgen [readOptions] invariants
  | inv1 => ReadOptionsInvariant
  | inv2 => .ofMeasure fun s : Option (Except Failure Input) × Input × ℕ ↦ args.size + 1 - s.2.2
  all_goals try vc_simp
  all_goals with_reducible first
    | exact readOptionsInvariant_none ‹_›
    | exact ReadOptionsInvariant.post_some ‹_› ‹_› ‹_›
    | exact ReadOptionsInvariant.post_none ‹_› ‹_›
    | exact ReadOptionsInvariant.optionsWF ‹_›
    | exact ReadOptionsInvariant.of_readOption ‹_› ‹_› ‹_› ‹_›
    | exact ReadOptionsInvariant.exit ‹_› fun _ h ↦ by cases h

/-! ### `read_input` -/

/-- The height bound is read from the second word, and a missing second word reads as the empty
word, which gives no number. -/
theorem two_le_size_of_scanLong_eq_some {args : Array String} {x : ℤ}
    (h : scanLong args[1]!.toList = some x) : 2 ≤ args.size := by
  by_contra! hs
  rw [getElem!_neg args 1 (by lia), show scanLong (default : String).toList = none by decide] at h
  cases h

/-- A height bound read from the second word excludes `-c list`, whose second word gives no
number. -/
theorem toList_ne_of_scanLong_eq_some {args : Array String} {x : ℤ}
    (h : scanLong args[1]!.toList = some x) : args.toList ≠ ["-c", "list"] := by
  intro ha
  obtain rfl : args = #["-c", "list"] := Array.toList_inj.mp ha
  rw [show scanLong (#["-c", "list"] : Array String)[1]!.toList = none by decide] at h
  cases h

/-- The coefficients of a degree at least `5`, with `f₆` set to `0` for the degree `5`, are those
of a polynomial of that degree, which `squarefree` takes. -/
theorem hasDegree_ite_set! {r : Option (Array ℤ × ℤ)} {c : Array ℤ} {d : ℤ}
    (hr : ∀ c d, r = some (c, d) → c.size = 7 ∧ d < 7 ∧ (0 < d → HasDegree c d))
    (he : r = some (c, d)) (hd : ¬d < 5) :
    HasDegree (if (d == 5) = true then c.set! 6 0 else c) d ∧ 0 < d ∧ d < 7 := by
  obtain ⟨-, h7, h⟩ := hr c d he
  refine ⟨?_, by lia, h7⟩
  split_ifs
  · exact (h (by lia)).set!_zero (by lia)
  · exact h (by lia)

/-- The globals with the coefficients, the height bound and the defaults of the options, before
the options, have the facts of `JPoints.Cli.Input.OptionsWF`. -/
theorem optionsWF_defaults {r : Option (Array ℤ × ℤ)} {c : Array ℤ} {d x : ℤ} {b : Bool}
    (hr : ∀ c d, r = some (c, d) → c.size = 7 ∧ d < 7 ∧ (0 < d → HasDegree c d))
    (he : r = some (c, d)) (hd : ¬d < 5)
    (hsq : b = true → Squarefree (poly (if (d == 5) = true then c.set! 6 0 else c).toList))
    (hb : ¬(!b) = true) (hx : ¬(decide (x < 1) || decide (↑maxHeight < x)) = true) :
    Input.OptionsWF
      { coeffs := (if (d == 5) = true then c.set! 6 0 else c), degree := d, height := x,
        sievePrimes1 := -1, sievePrimes2 := -1, sievePrimes3 := -1,
        printFormat := "(%ld, %ld, %ld, %ld)\n", arraySize := ↑defaultSize } := by
  obtain ⟨h1, h2, h3⟩ := hasDegree_ite_set! hr he hd
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, Bool.or_eq_true,
    decide_eq_true_eq, not_or, not_lt] at hb hx
  refine ⟨?_, h1.degree_toList (by lia), by lia, hsq hb, hx.1, hx.2, by lia [numPrimes_pos], le_rfl,
    le_rfl, le_rfl, le_rfl, by lia [defaultSize_pos], (by norm_num : (-1 : ℤ) < 2 ^ 63)⟩
  split_ifs <;> simp [(hr c d he).1]

theorem Input.wf_of_map_settleOptions_eq_ok {r : Except Failure Input} {input : Input}
    (h : r.map settleOptions = .ok input) (hr : ∀ st', r = .ok st' → st'.OptionsWF) :
    input.WF := by
  cases r with
  | error e => cases h
  | ok st =>
    obtain rfl := Except.ok.inj h
    exact (hr st rfl).wf_settleOptions

/-- `read_input` accepts only a command line of at least two words that is not `-c list`, and the
globals that it leaves then have the facts of `JPoints.Cli.Input.WF`: the coefficients read, of
degree at least `5` and of a squarefree polynomial, the height bound in `[1, MAX_HEIGHT]`, the
options read and settled by `settle_options`. -/
@[spec]
theorem readInput_spec (args : Array String) :
    ⦃ True ⦄ readInput args
    ⦃ fun r ↦ ∀ input, r = .ok input →
        2 ≤ args.size ∧ args.toList ≠ ["-c", "list"] ∧ input.WF ⦄ := by
  vcgen [readInput]
  all_goals try vc_simp [reduceCtorEq]
  all_goals with_reducible first
    | exact ⟨Array.size_replicate .., fun n ↦ Array.getElem!_replicate_default 7 n⟩
    | exact hasDegree_ite_set! ‹_› ‹_› ‹_›
    | exact optionsWF_defaults ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ⟨two_le_size_of_scanLong_eq_some ‹_›, toList_ne_of_scanLong_eq_some ‹_›,
        Input.wf_of_map_settleOptions_eq_ok ‹_› ‹_›⟩

end JPoints.Cli

end
