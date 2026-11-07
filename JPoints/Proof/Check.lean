/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.BruteForce
public import JPoints.Proof.Order
public import JPoints.Proof.Reference
public import Std.WP

import JPoints.Mathlib.Algebra.BigOperators.Ring.Finset
import JPoints.Mathlib.Algebra.GCDMonoid.Nat
import JPoints.Mathlib.Data.Rat.Lemmas
import JPoints.Proof.BruteForce
import JPoints.Proof.Containers
import JPoints.Proof.Kummer
import JPoints.Proof.Poly
import JPoints.Proof.Values
import Mathlib.Tactic.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Std.Tactic.Do

/-!
# The contracts of the exact check

What the exact check of `j-points` prints, in the terms of the reference layer: the points that it
finds are appended to the output, their text after its text and their number to its counter
(`JPoints.Output.appendPoints`); a part of the search that goes on has appended its points, none
under `-1` (`JPoints.Output.Searched`), and one that stops at a point under `-1` has printed the
first point of the whole search (`JPoints.Output.Searched.stop`). `check_one_point_final` prints the
candidate of a root of the Kummer equation over a triple of the search (`JPoints.pointOfRoot`)
exactly when it is a point (`JPoints.checkOnePointFinal_spec`); `check_one_point` prints the points
over a triple of the search (`JPoints.CheckGlobals.points`), only the first under `-1`
(`JPoints.checkOnePoint_spec`). The equation of the Kummer surface that the check computes from the
coefficients of `kummer_init` is that of the specification (`JPoints.kummerEqn_kummerInit`).

The lifting tests on machine words and on GMP integers are that of the brute-force reference
(`JPoints.checkLifts_spec`, `JPoints.checkLiftsMpz_spec`), which decides `JPoints.Lifts` on the
Kummer surface (`JPoints.BruteForce.lifts_eq_decide`): their loops compute `b⁶ f(c / b)` by
Horner's rule (`JPoints.SexticFormPowersInvariant`, `JPoints.SexticFormHornerInvariant`), and on
machine words the conversion of `b` to an `unsigned long` is the identity for the `b ≥ 0` of the
search. A candidate over a triple of the search lies on the Kummer surface and is normalised, so
that it is a point exactly when it lies within the bounds of the search and lifts
(`JPoints.isPoint_pointOfRoot_iff`). `check_one_point_final` checks a candidate on machine words
when its coordinates are within `MAX_HEIGHT` (`JPoints.CheckGlobals.wordsPath`), where the bounds
of the search hold (`JPoints.CheckGlobals.inBounds_of_wordsPath`), and otherwise on GMP integers
exactly when they hold (`JPoints.CheckGlobals.inBounds_pointOfRoot_iff`). The case tree of the
discriminant in `check_one_point` gives the roots of `JPoints.kummerRoots`, by the linear root when
`K₂ = 0`, so that no squarefreeness of the curve is needed. Over `(0, 0, 1)` a point lies only for
a sextic whose leading coefficient is a square (`JPoints.CheckGlobals.points_zero_zero_one_eq_nil`,
`JPoints.CheckGlobals.kummerRoots_zero_zero_one_of_mpzPerfectSquareP`).

## Main definitions

* `JPoints.Output.appendPoints`: the output with points of the curve searched printed after it.
* `JPoints.Output.Searched`: the output of a part of the search that goes on.
* `JPoints.SexticFormPowersInvariant`, `JPoints.SexticFormHornerInvariant`: the invariants of the
  loops of `JPoints.checkLiftsForm` and `JPoints.checkLiftsMpzForm`.

## Main statements

* `JPoints.Output.Searched.append`, `JPoints.Output.Searched.stop`, `JPoints.Output.Searched.post`,
  `JPoints.Output.appendPoints_firstIf_of_found`,
  `JPoints.Output.appendPoints_firstIf_of_not_found`: the output of the parts of the search.
* `JPoints.kummerEqn_kummerInit`: the Kummer equation of the check is that of the specification.
* `JPoints.CheckGlobals.abs_le_maxHeight_of_wordsPath`: the coordinates of a candidate on the path
  of machine words are within `MAX_HEIGHT`.
* `JPoints.checkLiftsForm_spec`, `JPoints.checkLiftsMpzForm_spec`, `JPoints.checkLifts_spec`,
  `JPoints.checkLiftsMpz_spec`: the lifting tests.
* `JPoints.isPoint_pointOfRoot_iff`: a candidate within the bounds is a point when it lifts.
* `JPoints.checkOnePointWords_spec`, `JPoints.checkOnePointMpz_spec`: the check of a point on
  machine words and on GMP integers.
* `JPoints.checkOnePointFinal_spec`: the check of a root.
* `JPoints.checkOnePoint_spec`: the check of a triple.
* `JPoints.CheckGlobals.points_zero_zero_one_eq_nil`,
  `JPoints.CheckGlobals.kummerRoots_zero_zero_one_of_mpzPerfectSquareP`: the points over
  `(0, 0, 1)`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`. Each verification
condition is discharged by a lemma stated in its own shape, which `exact` applies to the hypotheses
found by `‹_›`, after the conditions of the program are rewritten into the terms of the
specification, so that the dispatch depends neither on the order of the conditions nor on the names
of their hypotheses; those of the lifting tests close by one simplification with the lifting test
of the brute-force reference unfolded (`JPoints.BruteForce.lifts_eq_ite`). The triples of the
search are those of `JPoints.boxTriples`: coprime, the first nonzero coordinate positive, in the box
of the height bound, as the callers pass them. The `long`s of the C code are integers in the model,
which their range lemmas bound below `2 ^ 63` from the bounds of the inputs; of these the proofs
read only the bound of `b` below `2 ^ 64`, which makes its conversion to an `unsigned long` in the
lifting test the identity.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The output with the points found -/

/-- The output `out` with the points `L` of the curve searched printed after its text, as the exact
check with the globals `gl` prints them (`JPoints.CheckGlobals.textOf`), and counted in `total`. -/
def Output.appendPoints (out : Output) (gl : CheckGlobals) (L : List (ℤ × ℤ × ℤ × ℤ)) : Output :=
  { text := out.text ++ gl.textOf L, total := out.total + L.length }

namespace Output

@[simp]
theorem text_appendPoints (out : Output) (gl : CheckGlobals) (L : List (ℤ × ℤ × ℤ × ℤ)) :
    (out.appendPoints gl L).text = out.text ++ gl.textOf L :=
  rfl

@[simp]
theorem appendPoints_nil (out : Output) (gl : CheckGlobals) : out.appendPoints gl [] = out := by
  simp [appendPoints]

@[simp]
theorem appendPoints_appendPoints (out : Output) (gl : CheckGlobals)
    (L₁ L₂ : List (ℤ × ℤ × ℤ × ℤ)) :
    (out.appendPoints gl L₁).appendPoints gl L₂ = out.appendPoints gl (L₁ ++ L₂) := by
  simp [appendPoints, String.append_assoc, Nat.add_assoc]

/-- One point appended is its text printed (`JPoints.Output.print`) and the counter raised, as
`check_one_point_final` does. -/
private theorem appendPoints_singleton (out : Output) (gl : CheckGlobals) (p : ℤ × ℤ × ℤ × ℤ) :
    out.appendPoints gl [p] =
      { out.print (gl.text p) with total := (out.print (gl.text p)).total + 1 } := by
  simp [appendPoints, print]

end Output

/-! ### The output of the parts of the search -/

/-- The output `out` of a part of the search that started from the output `out₀`, has found the
points `L` and goes on: `out₀` with the points `L` printed, and under `-1` none, since the search
stops at the first. -/
def Output.Searched (out₀ : Output) (gl : CheckGlobals) (L : List (ℤ × ℤ × ℤ × ℤ))
    (out : Output) : Prop :=
  out = out₀.appendPoints gl L ∧ (gl.onePoint = true → L = [])

namespace Output

variable {out₀ out out' : Output} {gl : CheckGlobals} {L P : List (ℤ × ℤ × ℤ × ℤ)}

theorem searched_nil (out₀ : Output) (gl : CheckGlobals) : out₀.Searched gl [] out₀ :=
  ⟨(appendPoints_nil out₀ gl).symm, fun _ ↦ rfl⟩

/-- A part of the search that goes on after the points `P`, printed as the search prints them. -/
theorem Searched.append (h : out₀.Searched gl L out)
    (hout : out' = out.appendPoints gl (firstIf gl.onePoint P)) (hP : gl.onePoint = true → P = []) :
    out₀.Searched gl (L ++ P) out' :=
  ⟨by rw [hout, h.1, appendPoints_appendPoints, firstIf_eq_self_of_imp hP],
    fun hop ↦ by rw [h.2 hop, hP hop, List.append_nil]⟩

/-- A part of the search that stops at the points `P` under `-1` prints the first point of the
whole search, whatever comes after `P`. -/
theorem Searched.stop (h : out₀.Searched gl L out)
    (hout : out' = out.appendPoints gl (firstIf gl.onePoint P)) (hop : gl.onePoint = true)
    (hP : P ≠ []) (R : List (ℤ × ℤ × ℤ × ℤ)) :
    out' = out₀.appendPoints gl (firstIf gl.onePoint (L ++ P ++ R)) ∧
      true = (gl.onePoint && !(L ++ P ++ R).isEmpty) :=
  ⟨by rw [hout, h.1, appendPoints_appendPoints, ← firstIf_append_of_ne_nil hop h.2 hP,
    firstIf_eq_self_of_imp h.2], by simp [hop, hP]⟩

/-- A part of the search that has gone on to its end prints its points as the search prints them,
and has not stopped at a point. -/
theorem Searched.post (h : out₀.Searched gl L out) :
    out = out₀.appendPoints gl (firstIf gl.onePoint L) ∧ false = (gl.onePoint && !L.isEmpty) :=
  ⟨by rw [firstIf_eq_self_of_imp h.2]; exact h.1, by
    cases hop : gl.onePoint
    · rfl
    · simp [h.2 hop]⟩

/-- The output of a loop that stops at the points `W` of a step under `-1`, the form of
`JPoints.Output.Searched.stop` for the loops of the sieve. -/
theorem appendPoints_firstIf_of_found {L₁ W R : List (ℤ × ℤ × ℤ × ℤ)}
    (h₁ : gl.onePoint = true → L₁ = []) {found : Bool}
    (hfound : found = (gl.onePoint && !W.isEmpty)) (hf : (found && gl.onePoint) = true) :
    (out.appendPoints gl L₁).appendPoints gl (firstIf gl.onePoint W) =
        out.appendPoints gl (firstIf gl.onePoint (L₁ ++ W ++ R)) ∧
      true = (gl.onePoint && !(L₁ ++ W ++ R).isEmpty) := by
  have hop : gl.onePoint = true := by simp_all
  exact Searched.stop ⟨rfl, h₁⟩ rfl hop (by simp_all) R

/-- The output of a loop that goes on after the points `W` of a step, the form of
`JPoints.Output.Searched.append` for the loops of the sieve. -/
theorem appendPoints_firstIf_of_not_found {L₁ W : List (ℤ × ℤ × ℤ × ℤ)}
    (h₁ : gl.onePoint = true → L₁ = []) {found : Bool}
    (hfound : found = (gl.onePoint && !W.isEmpty)) (hf : ¬(found && gl.onePoint) = true) :
    (out.appendPoints gl L₁).appendPoints gl (firstIf gl.onePoint W) =
        out.appendPoints gl (L₁ ++ W) ∧ (gl.onePoint = true → L₁ ++ W = []) :=
  Searched.append ⟨rfl, h₁⟩ rfl fun hop ↦ by simpa [hop, hfound] using hf

end Output

/-! ### The Kummer equation -/

/-- The coefficients of the Kummer equation over `(a, b, c)` that `check_one_point` computes from
the coefficients `k400, …, k004` of `kummer_init` and the coefficients of the curve are those of the
specification, `K₀`, `K₁` and `K₂`, for the polynomial with the coefficients `coeffs`. -/
theorem kummerEqn_kummerInit (coeffs : Array ℤ) (a b c : ℤ) :
    kummerEqn (kummerInit coeffs) coeffs a b c =
      ⟨kummerK0 (coeffs.toList.getD · 0) a b c, kummerK1 (coeffs.toList.getD · 0) a b c,
        kummerK2 a b c⟩ := by
  simp only [kummerEqn, kummerInit, kummerK0, kummerK1, kummerK2, Array.getD_toList_eq_getElem!,
    KummerEqn.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ### The lifting test -/

private theorem mpzPerfectSquareP_eq_decide (n : ℤ) : mpzPerfectSquareP n = decide (IsSquare n) :=
  BruteForce.isSquare_eq_decide n

private theorem beq_zero_or_decide_isSquare (n : ℤ) :
    (n == 0 || decide (IsSquare n)) = decide (IsSquare n) := by
  rcases eq_or_ne n 0 with rfl | h <;> simp [*]

/-- The invariant of the first loop of `JPoints.checkLiftsForm` and `JPoints.checkLiftsMpzForm`,
for the factor `B` of the products (`b` modulo `2 ^ 64`, or `b`): after `i` steps, the product
`tmp` is `Bⁱ`, the array `bc` has seven entries, and `bc[k] = fₖ B⁶⁻ᵏ` for `6 - i ≤ k < 6`. -/
def SexticFormPowersInvariant (coeffs : Array ℤ) (B : ℤ) :
    Std.WP.Invariant ℕ (ℤ × Array ℤ) Prop :=
  fun pref _ s ↦ s.1 = B ^ pref.length ∧ s.2.size = 7 ∧
    ∀ k < 6, 6 - pref.length ≤ k → s.2[k]! = coeffs[k]! * B ^ (6 - k)

/-- The invariant of the second loop of `JPoints.checkLiftsForm` and `JPoints.checkLiftsMpzForm`,
Horner's rule in `c` from `f₆`, for the factor `B` of the products (`b` modulo `2 ^ 64`, or `b`):
after `j` steps, `fff = ∑ i ≤ j, f₆₋ᵢ Bⁱ cʲ⁻ⁱ`. -/
def SexticFormHornerInvariant (coeffs : Array ℤ) (B c : ℤ) : Std.WP.Invariant ℕ ℤ Prop :=
  fun pref _ fff ↦
    fff = ∑ i ∈ Finset.range (pref.length + 1), coeffs[6 - i]! * B ^ i * c ^ (pref.length - i)

private theorem sexticFormPowersInvariant_nil (coeffs : Array ℤ) (B : ℤ) (suff : List ℕ) :
    SexticFormPowersInvariant coeffs B [] suff (1, Array.replicate 7 0) :=
  ⟨by simp, by simp, fun k hk h ↦ by simp at h; lia⟩

private theorem SexticFormPowersInvariant.append_singleton {coeffs : Array ℤ} {B : ℤ}
    {pref suff : List ℕ} {cur : ℕ} (h : ForIn.toList [:6] = pref ++ cur :: suff)
    {s : ℤ × Array ℤ} (hinv : SexticFormPowersInvariant coeffs B pref (cur :: suff) s) :
    SexticFormPowersInvariant coeffs B (pref ++ [cur]) suff
      (s.1 * B, s.2.set! (5 - cur) (coeffs[5 - cur]! * (s.1 * B))) := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  refine ⟨by simp [h1, pow_succ], by simp [h2], fun k hk hk' ↦ ?_⟩
  simp only [List.length_append, List.length_singleton] at hk'
  by_cases hkc : 5 - cur = k
  · rw [← hkc, Array.getElem!_set!_self _ _ _ (by lia), h1, hc, ← pow_succ]
    congr 2
    lia [Std.Legacy.Range.lt_of_toList_eq_append_cons h]
  · rw [Array.getElem!_set!_ne _ _ _ _ hkc, h3 k hk (by lia)]

private theorem sexticFormHornerInvariant_nil (coeffs : Array ℤ) (B c : ℤ) (suff : List ℕ) :
    SexticFormHornerInvariant coeffs B c [] suff coeffs[6]! := by
  simp [SexticFormHornerInvariant]

private theorem SexticFormHornerInvariant.append_singleton {coeffs : Array ℤ} {B c : ℤ}
    {s : ℤ × Array ℤ} (hs : SexticFormPowersInvariant coeffs B (ForIn.toList [:6]) [] s)
    {pref suff : List ℕ} {cur : ℕ} (h : ForIn.toList [:6] = pref ++ cur :: suff) {fff : ℤ}
    (hinv : SexticFormHornerInvariant coeffs B c pref (cur :: suff) fff) :
    SexticFormHornerInvariant coeffs B c (pref ++ [cur]) suff (fff * c + s.2[5 - cur]!) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons h
  rw [SexticFormHornerInvariant] at hinv ⊢
  rw [hinv, hs.2.2 _ (by lia) (by simp), List.length_append, List.length_singleton, hc,
    ← Finset.sum_range_mul_pow_sub_mul_add]
  congr 3 <;> lia [Std.Legacy.Range.lt_of_toList_eq_append_cons h]

private theorem SexticFormHornerInvariant.eq_sexticForm {coeffs : Array ℤ} {B c fff : ℤ}
    (hinv : SexticFormHornerInvariant coeffs B c (ForIn.toList [:6]) [] fff) :
    fff = sexticForm (coeffs.toList.getD · 0) c B := by
  rw [SexticFormHornerInvariant, Std.Legacy.Range.length_toList] at hinv
  simp only [hinv, sexticForm, Finset.sum_range_succ, Finset.sum_range_zero,
    Array.getD_toList_eq_getElem!]
  ring

attribute [local irreducible] SexticFormPowersInvariant SexticFormHornerInvariant in
/-- The products of `check_lifts`, by `b` converted to an `unsigned long`, and Horner's rule give
`F(c, b mod 2 ^ 64)`, which is `b⁶ f(c / b)` for `0 ≤ b < 2 ^ 64`. -/
@[spec]
theorem checkLiftsForm_spec (coeffs : Array ℤ) (b c : ℤ) :
    ⦃ True ⦄ checkLiftsForm coeffs b c
    ⦃ fun r ↦ r = sexticForm (coeffs.toList.getD · 0) c (b % 2 ^ 64) ⦄ := by
  vcgen [checkLiftsForm] invariants
  · SexticFormPowersInvariant coeffs (b % 2 ^ 64)
  · SexticFormHornerInvariant coeffs (b % 2 ^ 64) c
  all_goals with_reducible first
    | exact sexticFormPowersInvariant_nil _ _ _
    | exact sexticFormHornerInvariant_nil _ _ _ _
    | exact SexticFormPowersInvariant.append_singleton ‹_› ‹_›
    | exact SexticFormHornerInvariant.append_singleton ‹_› ‹_› ‹_›
    | exact SexticFormHornerInvariant.eq_sexticForm ‹_›

attribute [local irreducible] SexticFormPowersInvariant SexticFormHornerInvariant in
@[spec]
theorem checkLiftsMpzForm_spec (coeffs : Array ℤ) (b c : ℤ) :
    ⦃ True ⦄ checkLiftsMpzForm coeffs b c
    ⦃ fun r ↦ r = sexticForm (coeffs.toList.getD · 0) c b ⦄ := by
  vcgen [checkLiftsMpzForm] invariants
  · SexticFormPowersInvariant coeffs b
  · SexticFormHornerInvariant coeffs b c
  all_goals with_reducible first
    | exact sexticFormPowersInvariant_nil _ _ _
    | exact sexticFormHornerInvariant_nil _ _ _ _
    | exact SexticFormPowersInvariant.append_singleton ‹_› ‹_›
    | exact SexticFormHornerInvariant.append_singleton ‹_› ‹_› ‹_›
    | exact SexticFormHornerInvariant.eq_sexticForm ‹_›

private theorem checkLiftsA2_eq_auxA2 (coeffs : Array ℤ) (a b c d : ℤ) :
    checkLiftsA2 coeffs a b c d (a * a) (b * b) = auxA2 (coeffs.toList.getD · 0) a b c d := by
  simp only [checkLiftsA2, auxA2, Array.getD_toList_eq_getElem!]
  ring

private theorem checkLiftsB2_eq_auxB2 (coeffs : Array ℤ) (a b c d : ℤ) :
    checkLiftsB2 coeffs a b c d (a * a) (b * b) (c * c) =
      auxB2 (coeffs.toList.getD · 0) a b c d := by
  simp only [checkLiftsB2, auxB2, Array.getD_toList_eq_getElem!]
  ring

private theorem checkLiftsMpzA2_eq_auxA2 (coeffs : Array ℤ) (a b c d : ℤ) :
    checkLiftsMpzA2 coeffs a b c d (a * a) (b * b) = auxA2 (coeffs.toList.getD · 0) a b c d := by
  simp only [checkLiftsMpzA2, auxA2, Array.getD_toList_eq_getElem!]
  ring

private theorem checkLiftsMpzB2_eq_auxB2 (coeffs : Array ℤ) (a b c d : ℤ) :
    checkLiftsMpzB2 coeffs a b c d (a * a) (b * b) (c * c) =
      auxB2 (coeffs.toList.getD · 0) a b c d := by
  simp only [checkLiftsMpzB2, auxB2, Array.getD_toList_eq_getElem!]
  ring

/-- The lifting test on machine words is that of the brute-force reference, on a point
`(a : b : c : d)` other than `(0 : 0 : 0 : d)` (which it lets pass) with `0 ≤ b < 2 ^ 64` when
`a = 0`, where the conversion of `b` to an `unsigned long` is the identity. -/
@[spec]
theorem checkLifts_spec (coeffs : Array ℤ) (a b c d : ℤ) :
    ⦃ (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ (a = 0 → 0 ≤ b ∧ b < 2 ^ 64) ⦄
    checkLifts coeffs a b c d
    ⦃ fun r ↦ r = BruteForce.lifts coeffs.toList a b c d ⦄ := by
  vcgen [checkLifts]
  all_goals simp_all [BruteForce.lifts_eq_ite, mpzPerfectSquareP_eq_decide, checkLiftsA2_eq_auxA2,
    checkLiftsB2_eq_auxB2, Int.emod_eq_of_lt, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, beq_zero_or_decide_isSquare]

/-- The lifting test on GMP integers is that of the brute-force reference, on a point
`(a : b : c : d)` other than `(0 : 0 : 0 : d)`, which it lets pass. -/
@[spec]
theorem checkLiftsMpz_spec (coeffs : Array ℤ) (a b c d : ℤ) :
    ⦃ a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ⦄
    checkLiftsMpz coeffs a b c d
    ⦃ fun r ↦ r = BruteForce.lifts coeffs.toList a b c d ⦄ := by
  vcgen [checkLiftsMpz]
  all_goals simp_all [BruteForce.lifts_eq_ite, mpzPerfectSquareP_eq_decide,
    checkLiftsMpzA2_eq_auxA2, checkLiftsMpzB2_eq_auxB2, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, beq_zero_or_decide_isSquare]

/-! ### The candidate of a root -/

/-- The candidate of a root of the Kummer quadratic over a coprime triple with its first nonzero
coordinate positive, within the bounds of the search, is a point exactly when it passes the lifting
test of the brute-force reference: it lies on the Kummer surface, it is normalised, and there the
test decides `JPoints.Lifts` (`JPoints.BruteForce.lifts_eq_decide`). -/
theorem isPoint_pointOfRoot_iff {cs : List ℤ} {H : ℕ} {all : Bool} {W : Option ℕ} {a b c : ℤ}
    (h : gcd a (gcd b c) = 1) (hn : 0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c)) {x : ℚ}
    (hx : (kummerK2 a b c : ℚ) * x ^ 2 + kummerK1 (cs.getD · 0) a b c * x +
      kummerK0 (cs.getD · 0) a b c = 0)
    (hB : InBounds H all W (x.den * a) (x.den * b) (x.den * c) x.num) :
    IsPoint cs H all W (pointOfRoot a b c x) ↔
      BruteForce.lifts cs (x.den * a) (x.den * b) (x.den * c) x.num = true := by
  have hK := kummer_eq_zero_of_quadratic_eq_zero hx
  rw [pointOfRoot, IsPoint, BruteForce.lifts_eq_decide hK, decide_eq_true_iff]
  exact ⟨fun h ↦ h.2.1, fun hL ↦ ⟨hK, hL, isNormalized_mul h hn (by positivity)
    (gcd_den_num x), hB⟩⟩

/-! ### The bounds of the search and the path of machine words -/

namespace CheckGlobals

theorem points_eq_filter_map (gl : CheckGlobals) (a b c : ℤ) :
    gl.points (a, b, c) = ((kummerRoots (gl.coeffList.getD · 0) a b c).map
      (pointOfRoot a b c)).filter (IsPoint gl.coeffList gl.H gl.allPoints gl.W) :=
  rfl

private theorem cast_hmax {gl : CheckGlobals} (hgl : gl.WF) :
    (gl.hmax : ℤ) = if gl.allPoints = true then (maxHeight : ℤ) else gl.height := by
  rw [hmax]
  split_ifs
  · rfl
  · exact Int.toNat_of_nonneg (by lia [hgl.one_le_height])

private theorem cast_dmax {gl : CheckGlobals} (hgl : gl.WF) :
    (gl.dmax : ℤ) =
      if (gl.dbounded && decide (gl.dbound < maxHeight)) = true then gl.dbound else maxHeight := by
  rw [dmax]
  by_cases h : gl.dbounded = true ∧ gl.dbound < maxHeight
  · rw [ite_eq_left h, ite_eq_left (by simpa using h)]
    exact Int.toNat_of_nonneg (by lia [hgl.one_le_dbound h.1])
  · rw [ite_eq_right h, ite_eq_right (by simpa using h)]

private theorem hmax_le_maxHeight {gl : CheckGlobals} (hgl : gl.WF) : gl.hmax ≤ maxHeight := by
  rw [hmax]
  split_ifs
  · rfl
  · lia [hgl.height_le_maxHeight]

private theorem dmax_le_maxHeight (gl : CheckGlobals) : gl.dmax ≤ maxHeight := by
  rw [dmax]
  split_ifs with h
  · lia
  · rfl

private theorem dmax_le_dbound {gl : CheckGlobals} (hgl : gl.WF) (h : gl.dbounded = true) :
    (gl.dmax : ℤ) ≤ gl.dbound := by
  rw [cast_dmax hgl]
  split_ifs <;> simp_all

/-- The `long`s of the path of machine words of `check_one_point_final` hold their values: the
coordinates `g a`, `g b`, `g c` and `d` of the point are at most `MAX_HEIGHT` in absolute value, by
the bounds `h` and `dmax` of the check (`JPoints.CheckGlobals.hmax_le_maxHeight`,
`JPoints.CheckGlobals.dmax_le_maxHeight`). -/
theorem abs_le_maxHeight_of_wordsPath {gl : CheckGlobals} (hgl : gl.WF) {p : ℤ × ℤ × ℤ × ℤ}
    (hw : gl.wordsPath p = true) :
    |p.1| ≤ maxHeight ∧ |p.2.1| ≤ maxHeight ∧ |p.2.2.1| ≤ maxHeight ∧ |p.2.2.2| ≤ maxHeight := by
  obtain ⟨a, b, c, d⟩ := p
  simp only [wordsPath, decide_eq_true_iff, max_le_iff] at hw
  lia [hmax_le_maxHeight hgl, gl.dmax_le_maxHeight]

private theorem wordsPath_pointOfRoot_iff (gl : CheckGlobals) (a b c : ℤ) (x : ℚ) :
    gl.wordsPath (pointOfRoot a b c x) = true ↔
      x.den * max |a| (max |b| |c|) ≤ gl.hmax ∧ |x.num| ≤ gl.dmax := by
  rw [pointOfRoot, wordsPath, decide_eq_true_iff, max_abs_mul (by positivity)]

/-- The bounds of the search on the candidate of a root over a triple of the search: the scale
times the largest coordinate of the triple within the height bound, unless `-a` is given, and the
fourth coordinate within the bound of `-w` or the height bound when it is bounded. -/
theorem inBounds_pointOfRoot_iff {gl : CheckGlobals} (hgl : gl.WF) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples gl.H) (x : ℚ) :
    InBounds gl.H gl.allPoints gl.W (x.den * a) (x.den * b) (x.den * c) x.num ↔
      (gl.allPoints = true ∨ x.den * max |a| (max |b| |c|) ≤ gl.height) ∧
        (gl.dbounded = true → |x.num| ≤ gl.dbound) := by
  have hg := Int.gcd_mul_gcd_mul_mul_of_gcd_eq_one (Nat.cast_nonneg x.den)
    (mem_boxTriples_iff.1 ht).1
  have hH : (gl.H : ℤ) = gl.height := Int.toNat_of_nonneg (by lia [hgl.one_le_height])
  have hM := Int.mul_le_mul_of_nonneg_left (max_abs_le_of_mem_boxTriples ht)
    (Nat.cast_nonneg x.den)
  rw [hH] at hM
  rw [InBounds, hg, max_abs_mul (Nat.cast_nonneg _), hH, mul_comm _ (x.den : ℤ)]
  rcases Bool.eq_false_or_eq_true gl.dbounded with hdb | hdb
  · have hd : (gl.dbound.toNat : ℤ) = gl.dbound :=
      Int.toNat_of_nonneg (by lia [hgl.one_le_dbound hdb])
    cases gl.allPoints <;> simp [W, hdb, hd, hM]
  · simp [hgl.allPoints_of_dbounded_eq_false hdb, hdb, hM]

theorem inBounds_of_wordsPath {gl : CheckGlobals} (hgl : gl.WF) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples gl.H) {x : ℚ} (hw : gl.wordsPath (pointOfRoot a b c x) = true) :
    InBounds gl.H gl.allPoints gl.W (x.den * a) (x.den * b) (x.den * c) x.num := by
  obtain ⟨h1, h2⟩ := (wordsPath_pointOfRoot_iff gl a b c x).1 hw
  rw [cast_hmax hgl] at h1
  rw [inBounds_pointOfRoot_iff hgl ht]
  refine ⟨?_, fun hdb ↦ h2.trans (dmax_le_dbound hgl hdb)⟩
  by_cases hall : gl.allPoints = true <;> simp_all

end CheckGlobals

/-! ### The check of a point -/

private theorem checkLifts_pre {H : ℕ} {a b c : ℤ} (ht : (a, b, c) ∈ boxTriples H) {g : ℤ}
    (hg : 0 < g) : (¬g * a = 0 ∨ ¬g * b = 0 ∨ ¬g * c = 0) ∧ (g * a = 0 → 0 ≤ g * b) := by
  obtain ⟨-, hn, -⟩ := mem_boxTriples_iff.1 ht
  simp only [mul_eq_zero, hg.ne', false_or]
  exact ⟨by lia, fun ha ↦ Int.mul_nonneg hg.le (by lia)⟩

private theorem checkLifts_pre_of_wordsPath {gl : CheckGlobals} (hgl : gl.WF) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples gl.H) {g d : ℤ} (hg : 0 < g)
    (hw : gl.wordsPath (g * a, g * b, g * c, d) = true) :
    (¬g * a = 0 ∨ ¬g * b = 0 ∨ ¬g * c = 0) ∧ (g * a = 0 → 0 ≤ g * b ∧ g * b < 2 ^ 64) := by
  obtain ⟨h1, h2⟩ := checkLifts_pre ht hg
  have : (maxHeight : ℤ) < 2 ^ 64 := by norm_num [maxHeight]
  exact ⟨h1, fun ha ↦ ⟨h2 ha, by
    lia [le_abs_self (g * b), (CheckGlobals.abs_le_maxHeight_of_wordsPath hgl hw).2.1]⟩⟩

private theorem checkOnePointWords_post_true {gl : CheckGlobals} {out : Output} {a b c d : ℤ}
    (hw : gl.wordsPath (a, b, c, d) = true) {l : Bool}
    (hl : l = BruteForce.lifts gl.coeffList a b c d) (h : l = true) :
    (true, { text := (out.print (Printf.emitPoint gl.curve.reversed gl.curve.negated
        gl.printFormat a b c d)).text, total := (out.print (Printf.emitPoint gl.curve.reversed
        gl.curve.negated gl.printFormat a b c d)).total + 1 }) =
      if BruteForce.lifts gl.coeffList a b c d then (true, out.appendPoints gl [(a, b, c, d)])
      else (false, out) := by
  rw [← hl, h, ite_eq_left rfl, Output.appendPoints_singleton, CheckGlobals.text, hw,
    ite_eq_left rfl]

private theorem checkOnePointMpz_post_true {gl : CheckGlobals} {out : Output} {a b c d : ℤ}
    (hw : gl.wordsPath (a, b, c, d) = false) {l : Bool}
    (hl : l = BruteForce.lifts gl.coeffList a b c d) (h : l = true) {s : String}
    (hs : s = (Printf.printfMpz gl.curve.reversed gl.curve.negated gl.printFormat a b c d).run) :
    (true, { text := (out.print s).text, total := (out.print s).total + 1 }) =
      if BruteForce.lifts gl.coeffList a b c d then (true, out.appendPoints gl [(a, b, c, d)])
      else (false, out) := by
  rw [← hl, h, ite_eq_left rfl, Output.appendPoints_singleton, CheckGlobals.text, hw, hs]
  rfl

private theorem checkOnePoint_post_false {gl : CheckGlobals} {out : Output} {a b c d : ℤ}
    {l : Bool} (hl : l = BruteForce.lifts gl.coeffList a b c d) (h : ¬l = true) :
    (false, out) =
      if BruteForce.lifts gl.coeffList a b c d then (true, out.appendPoints gl [(a, b, c, d)])
      else (false, out) := by
  rw [← hl, ite_eq_right h]

/-- `check_one_point_final` checks the candidate of the root `u / v`, in lowest terms, on machine
words when it lies on that path: it prints and counts it by `printf` when it passes the lifting test
of the brute-force reference, and says whether it did. -/
@[spec]
theorem checkOnePointWords_spec (gl : CheckGlobals) (out : Output) (a b c u v : ℤ) :
    ⦃ gl.WF ∧ (a, b, c) ∈ boxTriples gl.H ∧ v ≠ 0 ∧ Int.gcd u v = 1 ∧
      gl.wordsPath (pointOfRoot a b c ((u : ℚ) / v)) = true ⦄
    checkOnePointWords gl out a b c u v
    ⦃ fun r ↦ r = if BruteForce.lifts gl.coeffList (pointOfRoot a b c ((u : ℚ) / v)).1
          (pointOfRoot a b c ((u : ℚ) / v)).2.1 (pointOfRoot a b c ((u : ℚ) / v)).2.2.1
          (pointOfRoot a b c ((u : ℚ) / v)).2.2.2 then
        (true, out.appendPoints gl [pointOfRoot a b c ((u : ℚ) / v)]) else (false, out) ⦄ := by
  vcgen [checkOnePointWords]
  all_goals obtain ⟨hgl, ht, hv, hg, hw⟩ := ‹gl.WF ∧ _›
  all_goals first
    | simp only [pointOfRoot_div_of_neg hg ‹v < 0›, mul_comm a, mul_comm b, mul_comm c] at *
    | simp only [pointOfRoot_div_of_pos hg (by lia), mul_comm a, mul_comm b, mul_comm c] at *
  all_goals with_reducible first
    | exact checkLifts_pre_of_wordsPath hgl ht (by lia) hw
    | exact checkOnePointWords_post_true hw ‹_› ‹_›
    | exact checkOnePoint_post_false ‹_› ‹_›

/-- `check_one_point_final` checks the candidate of the root `u / v`, in lowest terms, on GMP
integers when it lies off the path of machine words: it prints and counts it by `gmp_printf` when
it passes the lifting test of the brute-force reference, and says whether it did. -/
@[spec]
theorem checkOnePointMpz_spec (gl : CheckGlobals) (out : Output) (a b c u v : ℤ) :
    ⦃ (a, b, c) ∈ boxTriples gl.H ∧ v ≠ 0 ∧ Int.gcd u v = 1 ∧
      gl.wordsPath (pointOfRoot a b c ((u : ℚ) / v)) = false ⦄
    checkOnePointMpz gl out a b c u v
    ⦃ fun r ↦ r = if BruteForce.lifts gl.coeffList (pointOfRoot a b c ((u : ℚ) / v)).1
          (pointOfRoot a b c ((u : ℚ) / v)).2.1 (pointOfRoot a b c ((u : ℚ) / v)).2.2.1
          (pointOfRoot a b c ((u : ℚ) / v)).2.2.2 then
        (true, out.appendPoints gl [pointOfRoot a b c ((u : ℚ) / v)]) else (false, out) ⦄ := by
  vcgen [checkOnePointMpz]
  all_goals obtain ⟨ht, hv, hg, hw⟩ := ‹(a, b, c) ∈ boxTriples gl.H ∧ _›
  all_goals first
    | simp only [pointOfRoot_div_of_neg hg ‹v < 0›] at *
    | simp only [pointOfRoot_div_of_pos hg (by lia)] at *
  all_goals with_reducible first
    | exact (checkLifts_pre ht (by lia)).1
    | exact checkOnePointMpz_post_true hw ‹_› ‹_› ‹_›
    | exact checkOnePoint_post_false ‹_› ‹_›

/-! ### The check of a root -/

/- The denominator and the absolute value of the numerator of `d1 / d2` in lowest terms, from the
quotients by the gcd. -/
private theorem den_and_abs_num_div (d1 : ℤ) {d2 : ℤ} (hd : d2 ≠ 0) :
    (((d1 : ℚ) / d2).den : ℤ) = |d2 / (d1.gcd d2 : ℤ)| ∧
      |((d1 : ℚ) / d2).num| = |d1 / (d1.gcd d2 : ℤ)| := by
  have h := Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right (n := d1) hd
  rw [← Rat.intCast_ediv_gcd_div_intCast_ediv_gcd d1 hd]
  rcases (Int.ediv_gcd_ne_zero_of_ne_zero_right d1 hd).lt_or_gt with hv | hv
  · rw [Rat.num_div_eq_neg_of_coprime hv h, Rat.den_div_eq_neg_of_coprime hv h, abs_of_neg hv,
      abs_neg]
    exact ⟨rfl, rfl⟩
  · rw [Rat.num_div_eq_of_coprime hv h, Rat.den_div_eq_of_coprime hv h, abs_of_pos hv]
    exact ⟨rfl, rfl⟩

private theorem ite_natAbs_eq_max {a : ℤ} (ha : 0 ≤ a) (b c : ℤ) :
    (if (b.natAbs : ℤ) < a then (if (c.natAbs : ℤ) < a then a else (c.natAbs : ℤ))
      else if c.natAbs < b.natAbs then (b.natAbs : ℤ) else (c.natAbs : ℤ)) =
      max |a| (max |b| |c|) := by
  simp only [← Int.ofNat_lt, Int.natCast_natAbs, abs_of_nonneg ha]
  split_ifs <;> simp only [max_def] <;> split_ifs <;> lia

private theorem wordsPath_pointOfRoot_div_iff (gl : CheckGlobals) {a b c : ℤ}
    (hM : 0 < max |a| (max |b| |c|)) (d1 : ℤ) {d2 : ℤ} (hd : d2 ≠ 0) :
    (d1 / (d1.gcd d2 : ℤ) ≤ gl.dmax ∧ -(gl.dmax : ℤ) ≤ d1 / (d1.gcd d2 : ℤ) ∧
      d2 / (d1.gcd d2 : ℤ) ≤ (gl.hmax : ℤ) / max |a| (max |b| |c|) ∧
      -((gl.hmax : ℤ) / max |a| (max |b| |c|)) ≤ d2 / (d1.gcd d2 : ℤ)) ↔
    gl.wordsPath (pointOfRoot a b c ((d1 : ℚ) / d2)) = true := by
  obtain ⟨hden, hnum⟩ := den_and_abs_num_div d1 hd
  rw [CheckGlobals.wordsPath_pointOfRoot_iff, hden, hnum, ← Int.le_ediv_iff_mul_le hM, abs_le,
    abs_le]
  tauto

private theorem inBounds_pointOfRoot_div_iff {gl : CheckGlobals} (hgl : gl.WF) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples gl.H) (d1 : ℤ) {d2 : ℤ} (hd : d2 ≠ 0) :
    ((!gl.dbounded || decide (d1 / (d1.gcd d2 : ℤ) ≤ gl.dbound) &&
        decide (-gl.dbound ≤ d1 / (d1.gcd d2 : ℤ))) = true ∧
      (gl.allPoints = true ∨ d2 / (d1.gcd d2 : ℤ) ≤ (gl.hmax : ℤ) / max |a| (max |b| |c|) ∧
        -((gl.hmax : ℤ) / max |a| (max |b| |c|)) ≤ d2 / (d1.gcd d2 : ℤ))) ↔
    InBounds gl.H gl.allPoints gl.W (((d1 : ℚ) / d2).den * a) (((d1 : ℚ) / d2).den * b)
      (((d1 : ℚ) / d2).den * c) ((d1 : ℚ) / d2).num := by
  obtain ⟨hden, hnum⟩ := den_and_abs_num_div d1 hd
  rw [CheckGlobals.inBounds_pointOfRoot_iff hgl ht, hden, hnum,
    ← Int.le_ediv_iff_mul_le (max_abs_pos_of_mem_boxTriples ht), abs_le, abs_le,
    CheckGlobals.cast_hmax hgl]
  by_cases hall : gl.allPoints = true <;> by_cases hdb : gl.dbounded = true <;>
    simp [hall, hdb, and_comm]

private theorem checkOnePointFinal_post {gl : CheckGlobals} {out : Output}
    {p : ℤ × ℤ × ℤ × ℤ} (hP : IsPoint gl.coeffList gl.H gl.allPoints gl.W p ↔
      BruteForce.lifts gl.coeffList p.1 p.2.1 p.2.2.1 p.2.2.2 = true) {r₁ : Bool} {r₂ : Output}
    (h : (r₁, r₂) = if BruteForce.lifts gl.coeffList p.1 p.2.1 p.2.2.1 p.2.2.2 then
      (true, out.appendPoints gl [p]) else (false, out)) :
    r₂ = out.appendPoints gl ([p].filter (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      r₁ = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W p) := by
  by_cases hl : BruteForce.lifts gl.coeffList p.1 p.2.1 p.2.2.1 p.2.2.2 = true <;> simp_all

private theorem checkOnePointFinal_post_none {gl : CheckGlobals} {out : Output} {a b c : ℤ}
    {x : ℚ} (h : ¬InBounds gl.H gl.allPoints gl.W (x.den * a) (x.den * b) (x.den * c) x.num) :
    out = out.appendPoints gl ([pointOfRoot a b c x].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      false = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x)) := by
  have : ¬IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x) :=
    fun hP ↦ h hP.2.2.2
  simp [this]

/-- `check_one_point_final` prints the candidate of the root `d1 / d2` of the Kummer equation over a
triple of the search exactly when it is a point (`JPoints.IsPoint`): the bounds `h` on its scale and
`dmax` on its fourth coordinate, and the bound of `-w`, decide the bounds of the search on the
candidate (`JPoints.InBounds`), the test of the lifting decides `JPoints.Lifts`, and the triple,
coprime with its first nonzero coordinate positive, makes the candidate normalised. It prints the
text of the point (`JPoints.CheckGlobals.text`) on the path, of machine words or of GMP integers,
that the bounds choose. The flag returned says whether it printed. -/
@[spec]
theorem checkOnePointFinal_spec (gl : CheckGlobals) (out : Output) (a b c d1 d2 : ℤ) :
    ⦃ gl.WF ∧ (a, b, c) ∈ boxTriples gl.H ∧ d2 ≠ 0 ∧
      (kummerK2 a b c : ℚ) * ((d1 : ℚ) / d2) ^ 2 +
          kummerK1 (gl.coeffList.getD · 0) a b c * ((d1 : ℚ) / d2) +
        kummerK0 (gl.coeffList.getD · 0) a b c = 0 ⦄
    checkOnePointFinal gl out a b c d1 d2
    ⦃ fun r ↦ r.2 = out.appendPoints gl ([pointOfRoot a b c ((d1 : ℚ) / d2)].filter
          (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
        r.1 = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W
          (pointOfRoot a b c ((d1 : ℚ) / d2))) ⦄ := by
  vcgen [checkOnePointFinal]
  all_goals obtain ⟨hgl, ht, hd, hx⟩ := ‹gl.WF ∧ _›
  all_goals obtain ⟨hcop, hn, -⟩ := mem_boxTriples_iff.1 ht
  all_goals simp only [ite_natAbs_eq_max (nonneg_of_mem_boxTriples ht) b c,
    ← CheckGlobals.cast_hmax hgl, ← CheckGlobals.cast_dmax hgl,
    Rat.intCast_ediv_gcd_div_intCast_ediv_gcd d1 hd] at *
  all_goals with_reducible first
    | exact ⟨hgl, ht, Int.ediv_gcd_ne_zero_of_ne_zero_right d1 hd,
        Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right hd,
        (wordsPath_pointOfRoot_div_iff gl (max_abs_pos_of_mem_boxTriples ht) d1 hd).1 ‹_›⟩
    | exact ⟨ht, Int.ediv_gcd_ne_zero_of_ne_zero_right d1 hd,
        Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right hd, Bool.eq_false_iff.2
          (mt (wordsPath_pointOfRoot_div_iff gl (max_abs_pos_of_mem_boxTriples ht) d1 hd).2 ‹_›)⟩
    | exact checkOnePointFinal_post (isPoint_pointOfRoot_iff hcop hn hx
        (CheckGlobals.inBounds_of_wordsPath hgl ht ((wordsPath_pointOfRoot_div_iff gl
          (max_abs_pos_of_mem_boxTriples ht) d1 hd).1 ‹_›))) ‹_›
    | exact checkOnePointFinal_post (isPoint_pointOfRoot_iff hcop hn hx
        ((inBounds_pointOfRoot_div_iff hgl ht d1 hd).1 ‹_›)) ‹_›
    | exact checkOnePointFinal_post_none (mt (inBounds_pointOfRoot_div_iff hgl ht d1 hd).2 ‹_›)

/-! ### The check of a triple -/

section KummerRoots

variable {f : ℕ → ℤ} {a b c : ℤ}

/- The roots of the Kummer equation in the cases of `check_one_point`, with its discriminant
`K₁ K₁ - K₀ K₂ 4` and its roots as it computes them. -/

private theorem kummerK1_sq_sub_four_mul_eq (f : ℕ → ℤ) (a b c : ℤ) :
    kummerK1 f a b c ^ 2 - 4 * kummerK0 f a b c * kummerK2 a b c =
      kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4 := by
  ring

private theorem kummerRoots_of_kummerK2_eq_zero_of_kummerK1_eq_zero
    (h : kummerK2 a b c = 0 ∧ kummerK1 f a b c = 0) : kummerRoots f a b c = [] := by
  simp [kummerRoots, h.1, h.2]

private theorem mul_two_ne_zero_and_kummerRoots_of_discrim_eq_zero
    (hd : kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4 = 0)
    (h : ¬(kummerK2 a b c = 0 ∧ kummerK1 f a b c = 0)) :
    kummerK2 a b c * 2 ≠ 0 ∧
      kummerRoots f a b c = [((-kummerK1 f a b c : ℤ) : ℚ) / ((kummerK2 a b c * 2 : ℤ) : ℚ)] := by
  have h2 : kummerK2 a b c ≠ 0 := fun h2 ↦ h ⟨h2, by simpa [h2] using hd⟩
  have hD := (kummerK1_sq_sub_four_mul_eq f a b c).trans hd
  have hs : Int.sqrt 0 = 0 := rfl
  refine ⟨mul_ne_zero h2 two_ne_zero, ?_⟩
  simp only [kummerRoots, hD, h2, hs, ↓reduceIte, ne_eq, zero_pow two_ne_zero, not_true_eq_false,
    List.cons.injEq, and_true]
  push_cast
  ring

private theorem kummerK1_ne_zero_and_kummerRoots_of_kummerK2_eq_zero
    (hd : ¬kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4 = 0)
    (h : kummerK2 a b c = 0) :
    kummerK1 f a b c ≠ 0 ∧
      kummerRoots f a b c = [((-kummerK0 f a b c : ℤ) : ℚ) / (kummerK1 f a b c : ℚ)] := by
  have h1 : kummerK1 f a b c ≠ 0 := fun h1 ↦ hd (by simp [h1, h])
  refine ⟨h1, ?_⟩
  simp [kummerRoots, h, h1]

private theorem kummerRoots_of_isSquare_of_kummerK2_ne_zero
    (hd : ¬kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4 = 0)
    (hs : IsSquare (kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4))
    (h : ¬kummerK2 a b c = 0) :
    kummerRoots f a b c =
      [(((kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4).toNat.sqrt -
          kummerK1 f a b c : ℤ) : ℚ) / ((kummerK2 a b c * 2 : ℤ) : ℚ),
        ((-((kummerK1 f a b c * kummerK1 f a b c -
          kummerK0 f a b c * kummerK2 a b c * 4).toNat.sqrt + kummerK1 f a b c) : ℤ) : ℚ) /
          ((kummerK2 a b c * 2 : ℤ) : ℚ)] := by
  have hD := kummerK1_sq_sub_four_mul_eq f a b c
  obtain ⟨r, hr⟩ := hs
  have hsq := (Int.exists_mul_self _).1 ⟨r, hr.symm⟩
  rw [← hD] at hsq hd ⊢
  have h0 : Int.sqrt (kummerK1 f a b c ^ 2 - 4 * kummerK0 f a b c * kummerK2 a b c) ≠ 0 :=
    fun h0 ↦ hd (by rw [← hsq, h0, mul_zero])
  have hsq2 : Int.sqrt (kummerK1 f a b c ^ 2 - 4 * kummerK0 f a b c * kummerK2 a b c) ^ 2 =
      kummerK1 f a b c ^ 2 - 4 * kummerK0 f a b c * kummerK2 a b c := by rw [sq, hsq]
  simp only [kummerRoots, h, ↓reduceIte, hsq2, ne_eq, not_true_eq_false, h0]
  simp only [List.cons.injEq, and_true, Int.sqrt]
  refine ⟨?_, ?_⟩ <;> push_cast <;> ring

private theorem kummerRoots_of_not_isSquare
    (hs : ¬IsSquare (kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4)) :
    kummerRoots f a b c = [] := by
  by_cases h2 : kummerK2 a b c = 0
  · exact absurd ⟨kummerK1 f a b c, by rw [h2]; ring⟩ hs
  · have hD := kummerK1_sq_sub_four_mul_eq f a b c
    have : Int.sqrt (kummerK1 f a b c * kummerK1 f a b c -
        kummerK0 f a b c * kummerK2 a b c * 4) ^ 2 ≠
        kummerK1 f a b c * kummerK1 f a b c - kummerK0 f a b c * kummerK2 a b c * 4 :=
      fun h ↦ hs ⟨_, (sq _).symm.trans h |>.symm⟩
    simp [kummerRoots, hD, h2, this]

end KummerRoots

/-- The precondition of `JPoints.checkOnePointFinal_spec` for a root of `JPoints.kummerRoots` over a
triple of the search, given as a quotient with a nonzero denominator. -/
theorem checkOnePointFinal_pre_of_mem_kummerRoots {gl : CheckGlobals} (hgl : gl.WF) {a b c : ℤ}
    (ht : (a, b, c) ∈ boxTriples gl.H) {d1 d2 : ℤ} (hd : d2 ≠ 0)
    (hx : (d1 : ℚ) / d2 ∈ kummerRoots (gl.coeffList.getD · 0) a b c) :
    gl.WF ∧ (a, b, c) ∈ boxTriples gl.H ∧ d2 ≠ 0 ∧
      (kummerK2 a b c : ℚ) * ((d1 : ℚ) / d2) ^ 2 +
          kummerK1 (gl.coeffList.getD · 0) a b c * ((d1 : ℚ) / d2) +
        kummerK0 (gl.coeffList.getD · 0) a b c = 0 :=
  ⟨hgl, ht, hd, quadratic_eq_zero_of_mem_kummerRoots hx⟩

private theorem checkOnePoint_pre {gl : CheckGlobals} {a b c : ℤ}
    (h : gl.WF ∧ (a, b, c) ∈ boxTriples gl.H) {d1 d2 : ℤ} {L : List ℚ}
    (hr : d2 ≠ 0 ∧ kummerRoots (gl.coeffList.getD · 0) a b c = L) (hx : (d1 : ℚ) / d2 ∈ L) :
    gl.WF ∧ (a, b, c) ∈ boxTriples gl.H ∧ d2 ≠ 0 ∧
      (kummerK2 a b c : ℚ) * ((d1 : ℚ) / d2) ^ 2 +
          kummerK1 (gl.coeffList.getD · 0) a b c * ((d1 : ℚ) / d2) +
        kummerK0 (gl.coeffList.getD · 0) a b c = 0 :=
  checkOnePointFinal_pre_of_mem_kummerRoots h.1 h.2 hr.1 (hr.2 ▸ hx)

private theorem checkOnePoint_post_nil {gl : CheckGlobals} {out : Output} {a b c : ℤ}
    (h : kummerRoots (gl.coeffList.getD · 0) a b c = []) :
    out = out.appendPoints gl (firstIf gl.onePoint (gl.points (a, b, c))) ∧
      (gl.onePoint = true → (false = true ↔ gl.points (a, b, c) ≠ [])) := by
  rw [CheckGlobals.points_eq_filter_map, h]
  simp

private theorem checkOnePoint_post_single {gl : CheckGlobals} {out : Output} {a b c : ℤ}
    {x : ℚ} (hr : kummerRoots (gl.coeffList.getD · 0) a b c = [x]) {r₁ : Bool} {r₂ : Output}
    (h : r₂ = out.appendPoints gl ([pointOfRoot a b c x].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      r₁ = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x))) :
    r₂ = out.appendPoints gl (firstIf gl.onePoint (gl.points (a, b, c))) ∧
      (gl.onePoint = true → (r₁ = true ↔ gl.points (a, b, c) ≠ [])) := by
  obtain ⟨rfl, rfl⟩ := h
  rw [CheckGlobals.points_eq_filter_map, hr]
  by_cases hP : IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x) <;>
    cases gl.onePoint <;> simp [hP]

private theorem checkOnePoint_post_stop {gl : CheckGlobals} {out : Output} {a b c : ℤ}
    {x y : ℚ} (hr : kummerRoots (gl.coeffList.getD · 0) a b c = [x, y]) {r : Bool}
    {out₁ : Output} (h : out₁ = out.appendPoints gl ([pointOfRoot a b c x].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      r = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x)))
    (hs : r = true ∧ gl.onePoint = true) :
    out₁ = out.appendPoints gl (firstIf gl.onePoint (gl.points (a, b, c))) ∧
      (gl.onePoint = true → gl.points (a, b, c) ≠ []) := by
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hP, hb⟩ := hs
  rw [CheckGlobals.points_eq_filter_map, hr]
  simp only [decide_eq_true_eq] at hP
  simp [hP, hb]

private theorem checkOnePoint_post_two {gl : CheckGlobals} {out : Output} {a b c : ℤ}
    {x y : ℚ} (hr : kummerRoots (gl.coeffList.getD · 0) a b c = [x, y]) {r : Bool}
    {out₁ : Output} (h₁ : out₁ = out.appendPoints gl ([pointOfRoot a b c x].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      r = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x)))
    (hs : ¬(r = true ∧ gl.onePoint = true)) {r₂ : Bool} {out₂ : Output}
    (h₂ : out₂ = out₁.appendPoints gl ([pointOfRoot a b c y].filter
        (IsPoint gl.coeffList gl.H gl.allPoints gl.W)) ∧
      r₂ = decide (IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c y))) :
    out₂ = out.appendPoints gl (firstIf gl.onePoint (gl.points (a, b, c))) ∧
      (gl.onePoint = true → (r₂ = true ↔ gl.points (a, b, c) ≠ [])) := by
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨rfl, rfl⟩ := h₂
  rw [Output.appendPoints_appendPoints, CheckGlobals.points_eq_filter_map, hr]
  by_cases hP : IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c x) <;>
    by_cases hQ : IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot a b c y) <;>
    cases hb : gl.onePoint <;> simp_all

/-- `check_one_point` prints the points over a triple of the search (`JPoints.CheckGlobals.points`),
in the order of the roots of the Kummer equation (`JPoints.kummerRoots`), and under `-1` only the
first: the case tree of the discriminant computes the roots of the specification, and each is
checked by `JPoints.checkOnePointFinal`. Under `-1` the flag returned says whether a point lies over
the triple; otherwise it is that of the last check and means nothing. -/
@[spec]
theorem checkOnePoint_spec (gl : CheckGlobals) (out : Output) (a b c : ℤ) :
    ⦃ gl.WF ∧ (a, b, c) ∈ boxTriples gl.H ⦄
    checkOnePoint gl out a b c
    ⦃ fun r ↦ r.2 = out.appendPoints gl (firstIf gl.onePoint (gl.points (a, b, c))) ∧
        (gl.onePoint = true → (r.1 = true ↔ gl.points (a, b, c) ≠ [])) ⦄ := by
  vcgen [checkOnePoint]
  all_goals simp only [‹gl.WF ∧ _›.1.kummer_eq, kummerEqn_kummerInit, beq_iff_eq,
    Bool.and_eq_true, mpzPerfectSquareP_eq_decide, decide_eq_true_eq, true_iff] at *
  all_goals with_reducible first
    | exact checkOnePoint_post_nil (kummerRoots_of_kummerK2_eq_zero_of_kummerK1_eq_zero ‹_›)
    | exact checkOnePoint_post_nil (kummerRoots_of_not_isSquare ‹_›)
    | exact checkOnePoint_pre ‹_› (mul_two_ne_zero_and_kummerRoots_of_discrim_eq_zero ‹_› ‹_›)
        (by simp)
    | exact checkOnePoint_pre ‹_› (kummerK1_ne_zero_and_kummerRoots_of_kummerK2_eq_zero ‹_› ‹_›)
        (by simp)
    | exact checkOnePoint_pre ‹_› ⟨mul_ne_zero ‹_› two_ne_zero,
        kummerRoots_of_isSquare_of_kummerK2_ne_zero ‹_› ‹_› ‹_›⟩ (by simp)
    | exact checkOnePoint_post_single
        (mul_two_ne_zero_and_kummerRoots_of_discrim_eq_zero ‹_› ‹_›).2 ‹_›
    | exact checkOnePoint_post_single
        (kummerK1_ne_zero_and_kummerRoots_of_kummerK2_eq_zero ‹_› ‹_›).2 ‹_›
    | exact checkOnePoint_post_stop (kummerRoots_of_isSquare_of_kummerK2_ne_zero ‹_› ‹_› ‹_›)
        ‹_› ‹_›
    | exact checkOnePoint_post_two (kummerRoots_of_isSquare_of_kummerK2_ne_zero ‹_› ‹_› ‹_›)
        ‹_› ‹_› ‹_›

/-! ### The points over `(0, 0, 1)` -/

/-- The root of the Kummer equation over `(0, 0, 1)`, which is linear there, `K₂ = 0`, with
`K₁ = -4 f₆`: none when `f₆ = 0`, and `(f₅² - 4 f₆ f₄) / (4 f₆)` otherwise. -/
private theorem kummerRoots_zero_zero_one (f : ℕ → ℤ) :
    kummerRoots f 0 0 1 = if f 6 = 0 then [] else
      [((f 5 * f 5 - f 6 * 4 * f 4 : ℤ) : ℚ) / ((f 6 * 4 : ℤ) : ℚ)] := by
  have h1 : kummerK1 f 0 0 1 = -4 * f 6 := by simp [kummerK1]
  by_cases h6 : f 6 = 0
  · simp [kummerRoots, kummerK2, h1, h6]
  · have : (f 6 : ℚ) ≠ 0 := mod_cast h6
    simp [kummerRoots, kummerK2, h1, h6, kummerK0]
    field

namespace CheckGlobals

/-- Over `(0, 0, 1)` no point lies unless the curve searched is a sextic whose leading coefficient
`f₆` is a square, as `find_points` tests: a quintic has no root over it, `f₆ = 0`, and the points
over it with `a = b = 0` lift only for a square `f₆`. -/
theorem points_zero_zero_one_eq_nil {gl : CheckGlobals} (hgl : gl.WF)
    (h : ¬(gl.curve.degree == 6 && mpzPerfectSquareP gl.curve.coeffs[6]!) = true) :
    gl.points (0, 0, 1) = [] := by
  rw [points_eq_filter_map, kummerRoots_zero_zero_one]
  split_ifs with h6
  · rfl
  have hdeg : gl.curve.degree = 6 := by
    by_contra hd
    exact h6 (getD_eq_zero_of_degree_lt (by
      rw [hgl.degree_coeffList]; lia [hgl.five_le_degree, degree_le_six hgl]))
  have hs : ¬IsSquare (gl.coeffList.getD 6 0) := by
    simpa only [hdeg, beq_self_eq_true, Bool.true_and, mpzPerfectSquareP_eq_decide,
      decide_eq_true_eq, Array.getD_toList_eq_getElem!] using h
  have hP (x : ℚ) : ¬IsPoint gl.coeffList gl.H gl.allPoints gl.W (pointOfRoot 0 0 1 x) :=
    fun hP ↦ hs (by simpa only [Lifts, mul_zero, ↓reduceIte] using hP.2.1)
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, hP, decide_false]
  rfl

/-- For a sextic whose leading coefficient `f₆` is a square, the root of the Kummer equation over
`(0, 0, 1)` as `find_points` computes it: `(f₅ f₅ - f₆ 4 f₄) / (f₆ 4)`, with `f₆ ≠ 0`. -/
theorem kummerRoots_zero_zero_one_of_mpzPerfectSquareP {gl : CheckGlobals} (hgl : gl.WF)
    (h : (gl.curve.degree == 6 && mpzPerfectSquareP gl.curve.coeffs[6]!) = true) :
    gl.curve.coeffs[6]! ≠ 0 ∧ kummerRoots (gl.coeffList.getD · 0) 0 0 1 =
      [((gl.curve.coeffs[5]! * gl.curve.coeffs[5]! - gl.curve.coeffs[6]! * (4 : ℤ) *
        gl.curve.coeffs[4]! : ℤ) : ℚ) / ((gl.curve.coeffs[6]! * (4 : ℤ) : ℤ) : ℚ)] := by
  have hdeg : gl.curve.degree = 6 := by
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have h6 : gl.curve.coeffs[6]! ≠ 0 := by
    have := getD_degree_ne_zero (cs := gl.coeffList) (by rw [hgl.degree_coeffList, hdeg]; lia)
    rwa [hgl.degree_coeffList, hdeg, Array.getD_toList_eq_getElem!] at this
  refine ⟨h6, ?_⟩
  rw [kummerRoots_zero_zero_one]
  simp only [Array.getD_toList_eq_getElem!, h6, ↓reduceIte]

end CheckGlobals

end JPoints

end
