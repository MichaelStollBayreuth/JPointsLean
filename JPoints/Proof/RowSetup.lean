/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Sift

import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.DoubleArith
import JPoints.Proof.Loops
import Std.Tactic.Do

/-!
# The contract of `row_setup`

The rows of the sieve tables of the primes of the first two stages for a row `(a, b)`, as
`row_setup` sets them (`JPoints.rowSetup_spec`): its statics stay consistent
(`JPoints.RowSetupCache.WF`), and for the row the residues of `b` and the indices of the rows of
`(a, b)` in the sieve tables are those that the second stage reads. The pieces: the small step
(`JPoints.rowSetupAddSmall_spec`), the residues of a step (`JPoints.rowSetupResidues_spec`, by the
quotient by a reciprocal in doubles), the step by them (`JPoints.rowSetupAddResidues_spec`), and the
computation by division (`JPoints.rowSetupDivide_spec`).

## Main definitions

* `JPoints.IsRowStep`: the rows and the residues after a step.
* `JPoints.RowSetupPre`, `JPoints.RowSetupPost`: the precondition and the postcondition of
  `row_setup`.

## Main statements

* `JPoints.rowSetupAddSmall_spec`, `JPoints.rowSetupResidues_spec`,
  `JPoints.rowSetupAddResidues_spec`, `JPoints.rowSetupDivide_spec`: the pieces of `row_setup`.
* `JPoints.rowSetup_spec`: `row_setup`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with the generic
invariant `JPoints.Set2Invariant` of `JPoints.Proof.Loops` for the loops over the primes, each
verification condition closed by a lemma stated in its own shape. A row of a sieve table is stated
relative to the residue of the first coordinate (`JPoints.IsRowStep`), so that the contracts of the
steps need no ghost argument. The step between two rows of the box stays below `2 ^ 48`, as
`|b| ≤ H ≤ MAX_HEIGHT < 2 ^ 32` and the statics keep `|last_b| ≤ H`
(`JPoints.RowSetupCache.WF.abs_lastB_le`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The steps -/

/-- The entries `n` of the rows `v₁` and of the residues `v₂` of the second coordinate after a step
by `e n` from the rows `rowptr` and the residues `bres`, modulo the `n`-th sieving prime `p`: the
residue moved on by `e n`, and the row of the same residue of the first coordinate at it. -/
def IsRowStep (sd : SiftData) (rowptr bres : Array ℕ) (e : ℕ → ℕ) (n v₁ v₂ : ℕ) : Prop :=
  v₂ = (bres[n]! + e n) % sd.pr[n]! ∧ ∀ x, rowptr[n]! = (x * sd.pr[n]! + bres[n]!) *
    (sd.pr[n]! + 1) → v₁ = (x * sd.pr[n]! + v₂) * (sd.pr[n]! + 1)

private theorem isRowStep_of_le {sd : SiftData} {rowptr bres : Array ℕ} {e : ℕ → ℕ} {n : ℕ}
    (hbr : bres[n]! < sd.pr[n]!) (he : e n ≤ sd.pr[n]!) (hle : sd.pr[n]! ≤ bres[n]! + e n) :
    IsRowStep sd rowptr bres e n (rowptr[n]! + e n * (sd.pr[n]! + 1) - sd.pr[n]! * (sd.pr[n]! + 1))
      (bres[n]! + e n - sd.pr[n]!) := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [hq, Nat.add_sub_cancel_left, Nat.add_mod_left, Nat.mod_eq_of_lt (by lia)]
  · rw [hx, show bres[n]! + e n - sd.pr[n]! = q by lia]
    refine Nat.sub_eq_of_eq_add ?_
    calc (x * sd.pr[n]! + bres[n]!) * (sd.pr[n]! + 1) + e n * (sd.pr[n]! + 1) =
        (x * sd.pr[n]! + (bres[n]! + e n)) * (sd.pr[n]! + 1) := by ring
      _ = (x * sd.pr[n]! + q) * (sd.pr[n]! + 1) + sd.pr[n]! * (sd.pr[n]! + 1) := by rw [hq]; ring

private theorem isRowStep_of_lt {sd : SiftData} {rowptr bres : Array ℕ} {e : ℕ → ℕ} {n : ℕ}
    (hlt : ¬sd.pr[n]! ≤ bres[n]! + e n) :
    IsRowStep sd rowptr bres e n (rowptr[n]! + e n * (sd.pr[n]! + 1)) (bres[n]! + e n) := by
  refine ⟨(Nat.mod_eq_of_lt (by lia)).symm, fun x hx ↦ ?_⟩
  rw [hx]
  ring

section RowSetupAdd

variable {g : SiftGlobals} {sd : SiftData} {rowptr bres b1 b2 : Array ℕ} {e : ℕ → ℕ} {cur : ℕ}
  {pref suff : List ℕ}

/-- The step of the loops of `JPoints.rowSetupAddSmall` and `JPoints.rowSetupAddResidues` past the
`p` rows of a block, in the shape of the verification condition. -/
private theorem set2Invariant_rowStep_of_le (h0 : IsStageSetup g sd)
    (hN : g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size)
    (hbr : ∀ n < g.sievePrimes2, bres[n]! < sd.pr[n]!) (he : ∀ n < g.sievePrimes2, e n ≤ sd.pr[n]!)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres e) pref (cur :: suff) (b1, b2))
    {v₁ v₂ : ℕ} (hv₁ : v₁ = b1[cur]! + e cur * sd.rowlen[cur]!) (hv₂ : v₂ = b2[cur]! + e cur)
    (hle : sd.pr[cur]! ≤ (b2.set! cur v₂)[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres e) (pref ++ [cur]) suff
      ((b1.set! cur v₁).set! cur ((b1.set! cur v₁)[cur]! - sd.blocklen[cur]!),
        (b2.set! cur v₂).set! cur ((b2.set! cur v₂)[cur]! - sd.pr[cur]!)) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := h0.lt_sievePrimes3 hcur
  obtain ⟨h1, h2⟩ := h.cur_eq hc
  have hs1 : b1.size = rowptr.size := h.1
  have hs2 : b2.size = bres.size := h.2.1
  rw [Array.getElem!_set!_self _ _ _ (by lia), hv₂, h2] at hle
  rw [Array.getElem!_set!_self _ _ _ (by lia), Array.getElem!_set!_self _ _ _ (by lia),
    Array.set!_set!, Array.set!_set!, hv₁, hv₂, h1, h2, h0.siftData.rowlen_eq hn3,
    h0.siftData.blocklen_eq hn3]
  exact h.step hc hN (isRowStep_of_le (hbr cur hcur) (he cur hcur) hle)

private theorem set2Invariant_rowStep_of_lt
    (hN : g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size) (h0 : IsStageSetup g sd)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres e) pref (cur :: suff) (b1, b2))
    {v₁ v₂ : ℕ} (hv₁ : v₁ = b1[cur]! + e cur * sd.rowlen[cur]!) (hv₂ : v₂ = b2[cur]! + e cur)
    (hlt : ¬sd.pr[cur]! ≤ (b2.set! cur v₂)[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres e) (pref ++ [cur]) suff
      (b1.set! cur v₁, b2.set! cur v₂) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := h0.lt_sievePrimes3 hcur
  obtain ⟨h1, h2⟩ := h.cur_eq hc
  rw [Array.getElem!_set!_self _ _ _ (by lia [(h.2.1 : b2.size = bres.size)]), hv₂, h2] at hlt
  rw [hv₁, hv₂, h1, h2, h0.siftData.rowlen_eq hn3]
  exact h.step hc hN (isRowStep_of_lt hlt)

private theorem addSmall_step_of_le {d : ℕ}
    (hpre : IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ d < 3 ∧
       ∀ n < g.sievePrimes2, bres[n]! < sd.pr[n]!)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun _ ↦ d) pref (cur :: suff) (b1, b2))
    (hle : sd.pr[cur]! ≤ (b2.set! cur (b2[cur]! + d))[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun _ ↦ d) (pref ++ [cur]) suff
      ((b1.set! cur (b1[cur]! + d * sd.rowlen[cur]!)).set! cur
          ((b1.set! cur (b1[cur]! + d * sd.rowlen[cur]!))[cur]! - sd.blocklen[cur]!),
        (b2.set! cur (b2[cur]! + d)).set! cur ((b2.set! cur (b2[cur]! + d))[cur]! - sd.pr[cur]!)) :=
  set2Invariant_rowStep_of_le hpre.1 ⟨hpre.2.1, hpre.2.2.1⟩ hpre.2.2.2.2
    (fun n hn ↦ by lia [hpre.1.three_le_pr_of_lt_sievePrimes2 hn])
    hc h rfl rfl hle

private theorem addSmall_step_of_lt {d : ℕ}
    (hpre : IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ d < 3 ∧
       ∀ n < g.sievePrimes2, bres[n]! < sd.pr[n]!)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun _ ↦ d) pref (cur :: suff) (b1, b2))
    (hlt : ¬sd.pr[cur]! ≤ (b2.set! cur (b2[cur]! + d))[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun _ ↦ d) (pref ++ [cur]) suff
      (b1.set! cur (b1[cur]! + d * sd.rowlen[cur]!), b2.set! cur (b2[cur]! + d)) :=
  set2Invariant_rowStep_of_lt ⟨hpre.2.1, hpre.2.2.1⟩ hpre.1 hc h rfl rfl hlt

private theorem addResidues_step_of_le {dres drow : Array ℕ} (hpre : IsStageSetup g sd ∧
      g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ ∀ n < g.sievePrimes2,
        bres[n]! < sd.pr[n]! ∧ dres[n]! < sd.pr[n]! ∧ drow[n]! = dres[n]! * (sd.pr[n]! + 1))
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun n ↦ dres[n]!) pref (cur :: suff)
      (b1, b2))
    (hle : sd.pr[cur]! ≤ (b2.set! cur (b2[cur]! + dres[cur]!))[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun n ↦ dres[n]!) (pref ++ [cur]) suff
      ((b1.set! cur (b1[cur]! + drow[cur]!)).set! cur
          ((b1.set! cur (b1[cur]! + drow[cur]!))[cur]! - sd.blocklen[cur]!),
        (b2.set! cur (b2[cur]! + dres[cur]!)).set! cur
          ((b2.set! cur (b2[cur]! + dres[cur]!))[cur]! - sd.pr[cur]!)) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := hpre.1.lt_sievePrimes3 hcur
  refine set2Invariant_rowStep_of_le hpre.1 ⟨hpre.2.1, hpre.2.2.1⟩ (fun n hn ↦ (hpre.2.2.2 n hn).1)
    (fun n hn ↦ (hpre.2.2.2 n hn).2.1.le) hc h ?_ rfl hle
  rw [(hpre.2.2.2 cur hcur).2.2, hpre.1.siftData.rowlen_eq hn3]

private theorem addResidues_step_of_lt {dres drow : Array ℕ} (hpre : IsStageSetup g sd ∧
      g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ ∀ n < g.sievePrimes2,
        bres[n]! < sd.pr[n]! ∧ dres[n]! < sd.pr[n]! ∧ drow[n]! = dres[n]! * (sd.pr[n]! + 1))
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h : Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun n ↦ dres[n]!) pref (cur :: suff)
      (b1, b2))
    (hlt : ¬sd.pr[cur]! ≤ (b2.set! cur (b2[cur]! + dres[cur]!))[cur]!) :
    Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun n ↦ dres[n]!) (pref ++ [cur]) suff
      (b1.set! cur (b1[cur]! + drow[cur]!), b2.set! cur (b2[cur]! + dres[cur]!)) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := hpre.1.lt_sievePrimes3 hcur
  refine set2Invariant_rowStep_of_lt ⟨hpre.2.1, hpre.2.2.1⟩ hpre.1 hc h ?_ rfl hlt
  rw [(hpre.2.2.2 cur hcur).2.2, hpre.1.siftData.rowlen_eq hn3]

end RowSetupAdd

/-- The small step of `row_setup` by `d < 3` moves the residue of the second coordinate on by `d`,
and the row of the sieve table of each prime of the first two stages with it, back by a block of `p`
rows past `p`, for residues below the primes. -/
@[spec]
theorem rowSetupAddSmall_spec (g : SiftGlobals) (sd : SiftData) (rowptr bres : Array ℕ) (d : ℕ) :
    ⦃ IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ d < 3 ∧
      ∀ n < g.sievePrimes2, bres[n]! < sd.pr[n]! ⦄
    rowSetupAddSmall g sd rowptr bres d
    ⦃ fun r ↦ r.1.size = rowptr.size ∧ r.2.size = bres.size ∧
        ∀ n < g.sievePrimes2, IsRowStep sd rowptr bres (fun _ ↦ d) n r.1[n]! r.2[n]! ⦄ := by
  vcgen [rowSetupAddSmall] invariants
  · Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun _ ↦ d)
  all_goals first
    | exact set2Invariant_nil
    | exact Set2Invariant.post ‹_›
    | exact addSmall_step_of_le ‹_› ‹_› ‹_› ‹_›
    | exact addSmall_step_of_lt ‹_› ‹_› ‹_› ‹_›

/-- The step of `row_setup` by the residues `dres` of the step and their offsets
`drow = dres (p + 1)` moves the residue of the second coordinate on by `dres[n]`, and the row of the
sieve table of each prime of the first two stages with it, back by a block of `p` rows past `p`, for
residues below the primes. -/
@[spec]
theorem rowSetupAddResidues_spec (g : SiftGlobals) (sd : SiftData)
    (rowptr bres dres drow : Array ℕ) :
    ⦃ IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧
      ∀ n < g.sievePrimes2,
        bres[n]! < sd.pr[n]! ∧ dres[n]! < sd.pr[n]! ∧ drow[n]! = dres[n]! * (sd.pr[n]! + 1) ⦄
    rowSetupAddResidues g sd rowptr bres dres drow
    ⦃ fun r ↦ r.1.size = rowptr.size ∧ r.2.size = bres.size ∧
        ∀ n < g.sievePrimes2, IsRowStep sd rowptr bres (fun n ↦ dres[n]!) n r.1[n]! r.2[n]! ⦄ := by
  vcgen [rowSetupAddResidues] invariants
  · Set2Invariant rowptr bres (IsRowStep sd rowptr bres fun n ↦ dres[n]!)
  all_goals first
    | exact set2Invariant_nil
    | exact Set2Invariant.post ‹_›
    | exact addResidues_step_of_le ‹_› ‹_› ‹_› ‹_›
    | exact addResidues_step_of_lt ‹_› ‹_› ‹_› ‹_›

/-! ### The residues of a step -/

section RowSetupResidues

variable {g : SiftGlobals} {sd : SiftData} {dres drow b1 b2 : Array ℕ} {d : ℤ} {cur : ℕ}
  {pref suff : List ℕ}

/-- The quotient of `row_setup` by the reciprocal of the `n`-th prime `p` leaves `d - p q` in
`[d mod p, d mod p + p]`. -/
private theorem sub_mul_toInt_toInt64_mem (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧
      g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧ d < 2 ^ 48)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff) :
    d % sd.pr[cur]! ≤ d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt ∧
      d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt ≤
        d % sd.pr[cur]! + sd.pr[cur]! := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := h.1.lt_sievePrimes3 hcur
  have hp := h.1.three_le_pr hn3
  rw [h.1.siftData.invp_eq hn3]
  obtain ⟨hq1, hq2⟩ := Double.toInt_toInt64_ofInt_mul_one_div_mem_Icc (p := sd.pr[cur]!)
    (by lia) h.2.2.2.1.le h.2.2.2.2
  have e := Int.emod_def d sd.pr[cur]!
  have m1 := Int.mul_le_mul_of_nonneg_left hq1 (show (0 : ℤ) ≤ sd.pr[cur]! by lia)
  constructor <;> lia [Int.mul_le_mul_of_nonneg_left hq2 (show (0 : ℤ) ≤ sd.pr[cur]! by lia)]

private theorem residues_step (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧
      g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧ d < 2 ^ 48)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (hi : Set2Invariant dres drow (fun n v₁ v₂ ↦ v₁ = (d % sd.pr[n]!).toNat ∧
      v₂ = v₁ * (sd.pr[n]! + 1)) pref (cur :: suff) (b1, b2)) {r : ℤ} (hr : r = d % sd.pr[cur]!) :
    Set2Invariant dres drow (fun n v₁ v₂ ↦ v₁ = (d % sd.pr[n]!).toNat ∧ v₂ = v₁ * (sd.pr[n]! + 1))
      (pref ++ [cur]) suff (b1.set! cur r.toNat, b2.set! cur (r.toNat * sd.rowlen[cur]!)) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := h.1.lt_sievePrimes3 hcur
  exact hi.step hc ⟨h.2.1, h.2.2.1⟩ ⟨by rw [hr], by rw [h.1.siftData.rowlen_eq hn3]⟩

private theorem residue_eq_sub_sub (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧
      g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧ d < 2 ^ 48)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h1 : sd.pr[cur]! ≤ d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt) :
    d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt - sd.pr[cur]! =
      d % sd.pr[cur]! := by
  have := sub_mul_toInt_toInt64_mem h hc
  have hp := h.1.three_le_pr_of_lt_sievePrimes2 (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)
  have := Int.emod_nonneg d (b := sd.pr[cur]!) (by lia)
  exact Int.eq_emod_of_eq_sub_mul (q := (Double.ofInt d * sd.invp[cur]!).toInt64.toInt + 1)
    (by ring) (by lia) (by lia [Int.emod_lt_of_pos d (b := sd.pr[cur]!) (by lia)])

private theorem residue_eq_sub
    (h1 : ¬sd.pr[cur]! ≤ d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt)
    (h2 : ¬d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt < 0) :
    d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt = d % sd.pr[cur]! :=
  Int.eq_emod_of_eq_sub_mul rfl (by lia) (by lia)

private theorem residue_eq_self (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧
      g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧ d < 2 ^ 48) (h1 : ¬(sd.pr[cur]! : ℤ) ≤ d) :
    d = d % sd.pr[cur]! :=
  (Int.emod_eq_of_lt (by lia) (by lia)).symm

private theorem residues_absurd (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧
      g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧ d < 2 ^ 48)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (h2 : d - sd.pr[cur]! * (Double.ofInt d * sd.invp[cur]!).toInt64.toInt < 0) : False := by
  have := Int.emod_nonneg d (b := sd.pr[cur]!)
    (by lia [h.1.three_le_pr_of_lt_sievePrimes2 (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)])
  lia [sub_mul_toInt_toInt64_mem h hc]

end RowSetupResidues

/-- `row_setup` computes the residues `d mod p` of a step `0 < d < 2 ^ 48` and their offsets
`(d mod p) (p + 1)` for each prime `p` of the first two stages, by the quotient by the reciprocal of
`p` in doubles, which leaves `d - p q` in `[d mod p, d mod p + p]`
(`JPoints.Double.toInt_toInt64_ofInt_mul_one_div_mem_Icc`), and one correction. -/
@[spec]
theorem rowSetupResidues_spec (g : SiftGlobals) (sd : SiftData) (dres drow : Array ℕ) (d : ℤ) :
    ⦃ IsStageSetup g sd ∧ g.sievePrimes2 ≤ dres.size ∧ g.sievePrimes2 ≤ drow.size ∧ 0 < d ∧
      d < 2 ^ 48 ⦄
    rowSetupResidues g sd dres drow d
    ⦃ fun r ↦ r.1.size = dres.size ∧ r.2.size = drow.size ∧ ∀ n < g.sievePrimes2,
        r.1[n]! = (d % sd.pr[n]!).toNat ∧ r.2[n]! = r.1[n]! * (sd.pr[n]! + 1) ⦄ := by
  vcgen [rowSetupResidues] invariants
  · Set2Invariant dres drow fun n v₁ v₂ ↦ v₁ = (d % sd.pr[n]!).toNat ∧ v₂ = v₁ * (sd.pr[n]! + 1)
  all_goals first
    | exact set2Invariant_nil
    | exact Set2Invariant.post ‹_›
    | exact residues_step ‹_› ‹_› ‹_› (residue_eq_sub_sub ‹_› ‹_› ‹_›)
    | exact residues_step ‹_› ‹_› ‹_› (residue_eq_sub ‹_› ‹_›)
    | exact residues_step ‹_› ‹_› ‹_› (residue_eq_self ‹_› ‹_›)
    | exact (residues_absurd ‹_› ‹_› ‹_›).elim
    | (exfalso; lia)

/-! ### The rows by division -/

private theorem divide_step {g : SiftGlobals} {sd : SiftData} {rowptr bres b1 b2 : Array ℕ}
    {a b : ℤ} {cur : ℕ} {pref suff : List ℕ}
    (h : IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ 0 ≤ a)
    (hc : ForIn.toList [:g.sievePrimes2] = pref ++ cur :: suff)
    (hi : Set2Invariant rowptr bres (fun n v₁ v₂ ↦ v₂ = (b % sd.pr[n]!).toNat ∧
      v₁ = ((a % sd.pr[n]!).toNat * sd.pr[n]! + v₂) * (sd.pr[n]! + 1)) pref (cur :: suff) (b1, b2))
    {bp : ℤ} (hbp : bp = b % sd.pr[cur]!) :
    Set2Invariant rowptr bres (fun n v₁ v₂ ↦ v₂ = (b % sd.pr[n]!).toNat ∧
      v₁ = ((a % sd.pr[n]!).toNat * sd.pr[n]! + v₂) * (sd.pr[n]! + 1)) (pref ++ [cur]) suff
      (b1.set! cur ((a.tmod sd.pr[cur]! * sd.pr[cur]! + bp) * sd.rowlen[cur]!).toNat,
        b2.set! cur bp.toNat) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hn3 := h.1.lt_sievePrimes3 hcur
  have hp := h.1.three_le_pr hn3
  refine hi.step hc ⟨h.2.1, h.2.2.1⟩ ⟨by rw [hbp], ?_⟩
  rw [Int.tmod_eq_emod_of_nonneg h.2.2.2, hbp, h.1.siftData.rowlen_eq hn3,
    ← Int.toNat_natCast (((a % sd.pr[cur]!).toNat * sd.pr[cur]! + (b % sd.pr[cur]!).toNat) *
      (sd.pr[cur]! + 1))]
  push_cast
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia))]

/-- `row_setup` computes the residue `b mod p` of the second coordinate and the row
`((a mod p) p + b mod p) (p + 1)` of the sieve table of each prime of the first two stages by
division, for `a ≥ 0`, where the remainder of C is the Euclidean one, and the residue of `b`
corrected into `[0, p)`. -/
@[spec]
theorem rowSetupDivide_spec (g : SiftGlobals) (sd : SiftData) (rowptr bres : Array ℕ) (a b : ℤ) :
    ⦃ IsStageSetup g sd ∧ g.sievePrimes2 ≤ rowptr.size ∧ g.sievePrimes2 ≤ bres.size ∧ 0 ≤ a ⦄
    rowSetupDivide g sd rowptr bres a b
    ⦃ fun r ↦ r.1.size = rowptr.size ∧ r.2.size = bres.size ∧ ∀ n < g.sievePrimes2,
        r.2[n]! = (b % sd.pr[n]!).toNat ∧
          r.1[n]! = ((a % sd.pr[n]!).toNat * sd.pr[n]! + r.2[n]!) * (sd.pr[n]! + 1) ⦄ := by
  vcgen [rowSetupDivide] invariants
  · Set2Invariant rowptr bres fun n v₁ v₂ ↦ v₂ = (b % sd.pr[n]!).toNat ∧
      v₁ = ((a % sd.pr[n]!).toNat * sd.pr[n]! + v₂) * (sd.pr[n]! + 1)
  all_goals first
    | exact set2Invariant_nil
    | exact Set2Invariant.post ‹_›
    | exact divide_step ‹_› ‹_› ‹_› (Int.tmod_add_natCast_eq_emod ‹_›)
    | exact divide_step ‹_› ‹_› ‹_› (Int.tmod_natCast_eq_emod ‹_›)

/-! ### `row_setup` -/

/-- The precondition of `JPoints.rowSetup`. -/
abbrev RowSetupPre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) : Prop :=
  IsStageSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ 0 ≤ a ∧ |b| ≤ g.check.height

section RowSetupProof

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {a b : ℤ}
  {rowptr bres dres drow : Array ℕ}

private theorem RowSetupPre.sievePrimes2_le (h : RowSetupPre g sd s a b) :
    g.sievePrimes2 ≤ numPrimes := by
  lia [h.1.sievePrimes2_le_sievePrimes3, h.1.sievePrimes3_le_numPrimes]

-- The statics of `row_setup` for the row `(a, b)`, `a ≥ 0`, `|b| ≤ H`, with the residues and rows
-- of `b`, and the residues and offsets of the step `D` for `D ≠ 0`, sized as consistent statics
-- before, are consistent.
private theorem RowSetupCache.wf_mk (h : RowSetupPre g sd s a b) {D : ℤ}
    (hs : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size)
    (hds : dres.size = s.rowSetup.dres.size ∧ drow.size = s.rowSetup.drow.size)
    (hbr : ∀ n < g.sievePrimes2, bres[n]! = (b % sd.pr[n]!).toNat ∧
      rowptr[n]! = ((a % sd.pr[n]!).toNat * sd.pr[n]! + bres[n]!) * (sd.pr[n]! + 1))
    (hd : D ≠ 0 → ∀ n < g.sievePrimes2, dres[n]! = (D % sd.pr[n]!).toNat ∧
      drow[n]! = dres[n]! * (sd.pr[n]! + 1)) :
    RowSetupCache.WF g sd rowptr
      { lastA := a, lastB := b, lastD := D, bres := bres, dres := dres, drow := drow } where
  size_rowptr := hs.1.trans h.2.1.size_rowptr
  size_bres := hs.2.trans h.2.1.size_bres
  size_dres := hds.1.trans h.2.1.size_dres
  size_drow := hds.2.trans h.2.1.size_drow
  abs_lastB_le _ := h.2.2.2
  bres_eq _ _ hn := (hbr _ hn).1
  rowptr_eq _ _ hn := (hbr _ hn).2
  dres_eq hD _ hn := (hd hD _ hn).1
  drow_eq hD _ hn := (hd hD _ hn).2

/-- The rows and the residues of `b` after a step from the last row of the same `a` by residues
`e n ≡ b - last_b` (mod the `n`-th prime). -/
private theorem getElem!_eq_of_isRowStep (h : RowSetupPre g sd s a b) (hA : s.rowSetup.lastA = a)
    {e : ℕ → ℕ}
    (he : ∀ n < g.sievePrimes2, (e n : ℤ) % sd.pr[n]! = (b - s.rowSetup.lastB) % sd.pr[n]!)
    (hr : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size ∧ ∀ n < g.sievePrimes2,
      IsRowStep sd s.rowptr s.rowSetup.bres e n rowptr[n]! bres[n]!) (n : ℕ)
    (hn : n < g.sievePrimes2) : bres[n]! = (b % sd.pr[n]!).toNat ∧
      rowptr[n]! = ((a % sd.pr[n]!).toNat * sd.pr[n]! + bres[n]!) * (sd.pr[n]! + 1) := by
  have hp := h.1.three_le_pr_of_lt_sievePrimes2 hn
  have ha : 0 ≤ s.rowSetup.lastA := hA ▸ h.2.2.1
  obtain ⟨h1, h2⟩ := (hr.2.2 n hn)
  refine ⟨?_, hA ▸ h2 _ (h.2.1.rowptr_eq ha hn)⟩
  rw [h1, h.2.1.bres_eq ha hn, Int.toNat_emod_add_mod _ _ (by lia), Int.add_emod, he n hn,
    ← Int.add_emod, show s.rowSetup.lastB + (b - s.rowSetup.lastB) = b by ring]

private theorem RowSetupPre.bres_lt (h : RowSetupPre g sd s a b) (hA : s.rowSetup.lastA = a) {n : ℕ}
    (hn : n < g.sievePrimes2) : s.rowSetup.bres[n]! < sd.pr[n]! := by
  rw [h.2.1.bres_eq (hA ▸ h.2.2.1) hn]
  exact Int.toNat_emod_lt _ (by lia [h.1.three_le_pr_of_lt_sievePrimes2 hn])

private theorem RowSetupPre.step_lt (h : RowSetupPre g sd s a b) (hA : s.rowSetup.lastA = a) :
    b - s.rowSetup.lastB < 2 ^ 48 := by
  have h1 := h.2.1.abs_lastB_le (hA ▸ h.2.2.1)
  rw [abs_le] at h1
  lia [abs_le.mp h.2.2.2, h.1.check.height_le_maxHeight, maxHeight_lt_two_pow_32]

private theorem rowSetup_pre_small (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB) &&
      decide (b - s.rowSetup.lastB < 3)) = true) :
    IsStageSetup g sd ∧ g.sievePrimes2 ≤ s.rowptr.size ∧ g.sievePrimes2 ≤ s.rowSetup.bres.size ∧
      (b - s.rowSetup.lastB).toNat < 3 ∧ ∀ n < g.sievePrimes2, s.rowSetup.bres[n]! < sd.pr[n]! := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  exact ⟨h.1, by lia [h.2.1.size_rowptr, h.sievePrimes2_le],
    by lia [h.2.1.size_bres, h.sievePrimes2_le], by lia, fun n hn ↦ h.bres_lt hc.1.1.symm hn⟩

private theorem rowSetup_pre_residues (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB)) = true) :
    IsStageSetup g sd ∧ g.sievePrimes2 ≤ s.rowSetup.dres.size ∧
      g.sievePrimes2 ≤ s.rowSetup.drow.size ∧ 0 < b - s.rowSetup.lastB ∧
        b - s.rowSetup.lastB < 2 ^ 48 := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  exact ⟨h.1, by lia [h.2.1.size_dres, h.sievePrimes2_le],
    by lia [h.2.1.size_drow, h.sievePrimes2_le], hc.2, h.step_lt hc.1.symm⟩

private theorem rowSetup_pre_addResidues (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB)) = true)
    (hd : dres.size = s.rowSetup.dres.size ∧ drow.size = s.rowSetup.drow.size ∧
      ∀ n < g.sievePrimes2, dres[n]! = ((b - s.rowSetup.lastB) % sd.pr[n]!).toNat ∧
        drow[n]! = dres[n]! * (sd.pr[n]! + 1)) :
    IsStageSetup g sd ∧ g.sievePrimes2 ≤ s.rowptr.size ∧ g.sievePrimes2 ≤ s.rowSetup.bres.size ∧
      ∀ n < g.sievePrimes2, s.rowSetup.bres[n]! < sd.pr[n]! ∧ dres[n]! < sd.pr[n]! ∧
        drow[n]! = dres[n]! * (sd.pr[n]! + 1) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  refine ⟨h.1, by lia [h.2.1.size_rowptr, h.sievePrimes2_le],
    by lia [h.2.1.size_bres, h.sievePrimes2_le],
    fun n hn ↦ ⟨h.bres_lt hc.1.symm hn, ?_, (hd.2.2 n hn).2⟩⟩
  rw [(hd.2.2 n hn).1]
  exact Int.toNat_emod_lt _ (by lia [h.1.three_le_pr_of_lt_sievePrimes2 hn])

private theorem rowSetup_pre_addResidues_reuse (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB)) = true)
    (hne : ¬(b - s.rowSetup.lastB != s.rowSetup.lastD) = true) :
    IsStageSetup g sd ∧ g.sievePrimes2 ≤ s.rowptr.size ∧ g.sievePrimes2 ≤ s.rowSetup.bres.size ∧
      ∀ n < g.sievePrimes2, s.rowSetup.bres[n]! < sd.pr[n]! ∧ s.rowSetup.dres[n]! < sd.pr[n]! ∧
        s.rowSetup.drow[n]! = s.rowSetup.dres[n]! * (sd.pr[n]! + 1) := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  have hD' : b - s.rowSetup.lastB = s.rowSetup.lastD := by simpa using hne
  have hD : s.rowSetup.lastD ≠ 0 := by lia
  refine ⟨h.1, by lia [h.2.1.size_rowptr, h.sievePrimes2_le],
    by lia [h.2.1.size_bres, h.sievePrimes2_le],
    fun n hn ↦ ⟨h.bres_lt hc.1.symm hn, ?_, h.2.1.drow_eq hD hn⟩⟩
  rw [h.2.1.dres_eq hD hn]
  exact Int.toNat_emod_lt _ (by lia [h.1.three_le_pr_of_lt_sievePrimes2 hn])

private theorem rowSetup_pre_divide (h : RowSetupPre g sd s a b) :
    IsStageSetup g sd ∧ g.sievePrimes2 ≤ s.rowptr.size ∧ g.sievePrimes2 ≤ s.rowSetup.bres.size ∧
      0 ≤ a :=
  ⟨h.1, by lia [h.2.1.size_rowptr, h.sievePrimes2_le], by lia [h.2.1.size_bres, h.sievePrimes2_le],
    h.2.2.1⟩

private theorem rowSetup_wf_small (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB) &&
      decide (b - s.rowSetup.lastB < 3)) = true)
    (hr : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size ∧ ∀ n < g.sievePrimes2,
      IsRowStep sd s.rowptr s.rowSetup.bres (fun _ ↦ (b - s.rowSetup.lastB).toNat) n rowptr[n]!
        bres[n]!) :
    RowSetupCache.WF g sd rowptr
      { lastA := a, lastB := b, lastD := s.rowSetup.lastD, bres := bres, dres := s.rowSetup.dres,
        drow := s.rowSetup.drow } := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  refine RowSetupCache.wf_mk h ⟨hr.1, hr.2.1⟩ ⟨rfl, rfl⟩
    (getElem!_eq_of_isRowStep h hc.1.1.symm (fun n _ ↦ ?_) hr)
    fun hD _ hn ↦ ⟨h.2.1.dres_eq hD hn, h.2.1.drow_eq hD hn⟩
  rw [Int.toNat_of_nonneg (by lia)]

private theorem rowSetup_wf_residues (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB)) = true)
    (hd : dres.size = s.rowSetup.dres.size ∧ drow.size = s.rowSetup.drow.size ∧
      ∀ n < g.sievePrimes2, dres[n]! = ((b - s.rowSetup.lastB) % sd.pr[n]!).toNat ∧
        drow[n]! = dres[n]! * (sd.pr[n]! + 1))
    (hr : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size ∧ ∀ n < g.sievePrimes2,
      IsRowStep sd s.rowptr s.rowSetup.bres (getElem! dres) n rowptr[n]! bres[n]!) :
    RowSetupCache.WF g sd rowptr
      { lastA := a, lastB := b, lastD := b - s.rowSetup.lastB, bres := bres, dres := dres,
        drow := drow } := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  refine RowSetupCache.wf_mk h ⟨hr.1, hr.2.1⟩ ⟨hd.1, hd.2.1⟩
    (getElem!_eq_of_isRowStep h hc.1.symm (fun n hn ↦ ?_) hr) fun _ ↦ hd.2.2
  rw [(hd.2.2 n hn).1,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia [h.1.three_le_pr_of_lt_sievePrimes2 hn])),
    Int.emod_emod]

private theorem rowSetup_wf_reuse (h : RowSetupPre g sd s a b)
    (hc : (a == s.rowSetup.lastA && decide (0 < b - s.rowSetup.lastB)) = true)
    (hne : ¬(b - s.rowSetup.lastB != s.rowSetup.lastD) = true)
    (hr : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size ∧ ∀ n < g.sievePrimes2,
      IsRowStep sd s.rowptr s.rowSetup.bres (getElem! s.rowSetup.dres) n rowptr[n]! bres[n]!) :
    RowSetupCache.WF g sd rowptr
      { lastA := a, lastB := b, lastD := s.rowSetup.lastD, bres := bres, dres := s.rowSetup.dres,
        drow := s.rowSetup.drow } := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  have hD' : b - s.rowSetup.lastB = s.rowSetup.lastD := by simpa using hne
  have hD : s.rowSetup.lastD ≠ 0 := by lia
  refine RowSetupCache.wf_mk h ⟨hr.1, hr.2.1⟩ ⟨rfl, rfl⟩
    (getElem!_eq_of_isRowStep h hc.1.symm (fun n hn ↦ ?_) hr)
    fun hD _ hn ↦ ⟨h.2.1.dres_eq hD hn, h.2.1.drow_eq hD hn⟩
  rw [h.2.1.dres_eq hD hn,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia [h.1.three_le_pr_of_lt_sievePrimes2 hn])),
    Int.emod_emod, hD']

private theorem rowSetup_wf_divide (h : RowSetupPre g sd s a b)
    (hr : rowptr.size = s.rowptr.size ∧ bres.size = s.rowSetup.bres.size ∧ ∀ n < g.sievePrimes2,
      bres[n]! = (b % sd.pr[n]!).toNat ∧
        rowptr[n]! = ((a % sd.pr[n]!).toNat * sd.pr[n]! + bres[n]!) * (sd.pr[n]! + 1)) :
    RowSetupCache.WF g sd rowptr
      { lastA := a, lastB := b, lastD := 0, bres := bres, dres := s.rowSetup.dres,
        drow := s.rowSetup.drow } :=
  RowSetupCache.wf_mk h ⟨hr.1, hr.2.1⟩ ⟨rfl, rfl⟩ hr.2.2 fun hD ↦ absurd rfl hD

end RowSetupProof

/-- The postcondition of `JPoints.rowSetup` for the state `s` and the row `(a, b)`: the result `r`
is `s` with its own rows and statics of `row_setup`, consistent statics for the row `(a, b)`. -/
abbrev RowSetupPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ)
    (r : SiftState) : Prop :=
  r = { s with rowptr := r.rowptr, rowSetup := r.rowSetup } ∧
    RowSetupCache.WF g sd r.rowptr r.rowSetup ∧ r.rowSetup.lastA = a ∧ r.rowSetup.lastB = b

/-- `row_setup` sets the rows of the sieve tables of the first two stages for the row `(a, b)`,
`a ≥ 0`, `|b| ≤ H`, and leaves its statics consistent for it (`JPoints.RowSetupCache.WF`): by the
small step for `0 < b - last_b < 3`, by the residues of the step (computed for a new step, kept for
the last) for a larger step of the same `a`, and by division otherwise. It changes no other field of
the state. -/
@[spec]
theorem rowSetup_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) :
    ⦃ RowSetupPre g sd s a b ⦄
    rowSetup g sd s a b
    ⦃ fun r ↦ RowSetupPost g sd s a b r ⦄ := by
  vcgen [rowSetup]
  all_goals try dsimp only at *
  all_goals first
    | exact rowSetup_pre_small ‹_› ‹_›
    | exact rowSetup_pre_residues ‹_› ‹_›
    | exact rowSetup_pre_addResidues ‹_› ‹_› ‹_›
    | exact rowSetup_pre_addResidues_reuse ‹_› ‹_› ‹_›
    | exact rowSetup_pre_divide ‹_›
    | exact ⟨rfl, rowSetup_wf_small ‹_› ‹_› ‹_›⟩
    | exact ⟨rfl, rowSetup_wf_residues ‹_› ‹_› ‹_› ‹_›⟩
    | exact ⟨rfl, rowSetup_wf_reuse ‹_› ‹_› ‹_› ‹_›⟩
    | exact ⟨rfl, rowSetup_wf_divide ‹_› ‹_›⟩

end JPoints

end
