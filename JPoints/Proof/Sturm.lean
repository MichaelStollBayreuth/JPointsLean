/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Globals
public import JPoints.Proof.SturmChain
public import JPoints.Spec.Sturm
public import Mathlib.Algebra.Algebra.Rat
public import Std.WP

import JPoints.Mathlib.Algebra.Order.Floor.Semifield
import JPoints.Mathlib.Algebra.Polynomial.Eval.Coeff
import JPoints.Mathlib.Algebra.Polynomial.Roots
import JPoints.Mathlib.Algebra.Polynomial.Sturm.Sequence
import JPoints.Mathlib.Analysis.Polynomial.CauchyBound
import JPoints.Mathlib.Analysis.Polynomial.Order
import JPoints.Mathlib.Basic.Sign.Basic
import JPoints.Mathlib.FieldTheory.Perfect
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Poly
import JPoints.Proof.Truncation
import JPoints.Proof.Values
import JPoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The intervals of `real_roots_init` on which `f` is negative

Under Sturm's theorem (`JPoints.SturmTheorem`), the intervals that `real_roots_init` records lie
where the squarefree polynomial `f` of the curve searched is negative. The counts of the finished
Sturm chain (`JPoints.Proof.SturmChain`) at a rational number are those of Mathlib's Sturm sequence
of the real polynomial of `f` (`JPoints.SturmChain.IsFinished.run_sturmChanges`, `JPoints.sturmV`),
so that they decrease and differ by the number of the roots between two points
(`JPoints.sturmV_le_of_le`, `JPoints.ncard_add_sturmV`); `JPoints.realRootsBound` gives a Cauchy
bound `B` of the roots (`JPoints.realRootsBound_spec`, `Polynomial.abs_lt_add_one_of_isRoot`), so
that they all lie in `(-B, B)`; the bisection of `JPoints.sturmIsolate` and the refinement of
`JPoints.sturmRefine` record, by the counts alone, one interval for each root in `(-B, B]` in
increasing order (`JPoints.RootIntervals.Isolated`, `JPoints.sturmIsolate_spec`,
`JPoints.sturmRefine_spec`); and between the intervals of the roots `i - 1` and `i` of the `n`
roots, `f` has the sign of its leading coefficient times `(-1) ^ (n - i)`
(`JPoints.not_isRoot_and_ncard_eq`, `Polynomial.sign_eval_eq_sign_leadingCoeff_mul_of_squarefree`),
which is the sign that `JPoints.realRootsRecord` computes for the gap, so that the gaps that it
records, shrunk by the doubles of the ends of the isolating intervals, are intervals on which `f` is
negative (`JPoints.RootIntervals.Isolated.recordPre`, `JPoints.realRootsRecord_spec`,
`JPoints.NegativeIntervals.Sound`). The contract of `real_roots_init` itself, which composes these,
is `JPoints.realRootsInit_spec`.

## Main definitions

* `JPoints.sturmV`: the count of Sturm's theorem.
* `JPoints.SturmChain.Counts`: the counts of the chain on an interval, as the isolation needs them.
* `JPoints.RootIntervals.Isolated`: the isolating intervals recorded up to a point.
* `JPoints.RefinePre`, `JPoints.IsolatePre`, `JPoints.RecordPre`: what `JPoints.sturmRefine`,
  `JPoints.sturmIsolate` and `JPoints.realRootsRecord` need.
* `JPoints.negCount`: the number of the gaps of negative sign.
* `JPoints.RefineInvariant`, `JPoints.BoundInvariant`, `JPoints.RecordInvariant`: the invariants
  of the loops.

## Main statements

* `JPoints.SturmChain.IsFinished.run_sturmChanges`: the counts of the chain are those of Sturm's
  theorem.
* `JPoints.not_isRoot_and_ncard_eq`: the roots above a point of a gap between isolating intervals.
* `JPoints.sturmRefine_spec`, `JPoints.sturmIsolate_spec`, `JPoints.realRootsBound_spec`,
  `JPoints.realRootsRecord_spec`: the contracts of the components of `real_roots_init`.
* `JPoints.SturmChain.IsFinished.counts`, `JPoints.RootIntervals.Isolated.recordPre`: the
  isolation and the record for the finished chain of a squarefree `f`.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`; each loop has a named
invariant, irreducible in the proof of its contract, and each verification condition is discharged
by a lemma in its own shape. The isolation reasons about the counts of `JPoints.sturmChanges` only
(`JPoints.SturmChain.Counts`), which Sturm's theorem supplies for the real polynomial; the recursion
of `JPoints.sturmIsolate` is proved by induction on its fuel, and a run out of fuel records nothing.
The loop of `JPoints.sturmRefine` ends because its test in doubles holds once the interval is narrow
enough (`JPoints.Double.mpqGetD_sub_mpqGetD_le`); the ends of the shrunk intervals lie strictly
inside the gaps by the truncation of `mpq_get_d`
(`JPoints.Double.lt_nextUp_and_nextDown_lt_mpqGetD`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

open Polynomial

namespace JPoints

/-! ### The isolation of the roots -/

/-- What the isolation of the roots by `JPoints.sturmIsolate` and `JPoints.sturmRefine` needs of
the counts of the chain `ch` (`JPoints.sturmChanges`) on `[lo₀, hi₀]`: they decrease, by at most
six from `lo₀` to `hi₀`, and the ends lie within `±2 ^ 480`. -/
structure SturmChain.Counts (ch : SturmChain) (lo₀ hi₀ : ℚ) : Prop where
  /-- The counts decrease. -/
  antitone {x y : ℚ} (hx : lo₀ ≤ x) (hxy : x ≤ y) (hy : y ≤ hi₀) :
    (sturmChanges ch y).run ≤ (sturmChanges ch x).run
  /-- The counts decrease by at most six. -/
  le_add_six : (sturmChanges ch lo₀).run ≤ (sturmChanges ch hi₀).run + 6
  /-- The lower end is at least `-2 ^ 480`. -/
  neg_two_pow_le : -2 ^ 480 ≤ lo₀
  /-- The upper end is at most `2 ^ 480`. -/
  le_two_pow : hi₀ ≤ 2 ^ 480

/-- The invariant of the loop of `JPoints.sturmRefine` for the chain `ch` on `[lo₀, hi₀]` and the
count `n` at the lower end of the interval it starts from: the interval `(lo, hi]` lies in
`[lo₀, hi₀]`, with the count `n` at `lo` and `n - 1` at `hi`, so that it holds one root. -/
def RefineInvariant (ch : SturmChain) (lo₀ hi₀ : ℚ) (n : ℕ) :
    Std.WP.WhileInvariant (ℚ × ℚ × ℕ × ℕ) Prop :=
  .mk fun _ s ↦ lo₀ ≤ s.1 ∧ s.1 < s.2.1 ∧ s.2.1 ≤ hi₀ ∧ s.2.2.1 = n ∧
    (sturmChanges ch s.1).run = n ∧ (sturmChanges ch s.2.1).run + 1 = n

/-- An interval on which the test of the refinement fails is wider than `2 ^ (-43)`, so that its
halves have a smaller measure. -/
private theorem SturmChain.Counts.one_lt_sub_mul_of_not_le {ch : SturmChain} {lo₀ hi₀ : ℚ}
    (hc : ch.Counts lo₀ hi₀) {lo hi : ℚ} (hlo : lo₀ ≤ lo) (hlt : lo < hi) (hhi : hi ≤ hi₀)
    (h : ¬Double.mpqGetD hi - Double.mpqGetD lo ≤
      0.5 * Double.ldexp 1.0 (-40) *
        ((Double.mpqGetD lo).fabs + (Double.mpqGetD hi).fabs + 1.0)) :
    1 < (hi - lo) * 2 ^ 43 :=
  not_le.mp fun h' ↦
    h (Double.mpqGetD_sub_mpqGetD_le (hc.neg_two_pow_le.trans hlo) (hhi.trans hc.le_two_pow) hlt h')

/-- What `JPoints.sturmRefine` needs of the interval `(lo, hi]` of `[lo₀, hi₀]` for the chain `ch`:
the counts of the chain on `[lo₀, hi₀]`, and the counts `n` and `n - 1` at the ends, so that the
interval holds one root. -/
structure RefinePre (ch : SturmChain) (lo₀ hi₀ lo hi : ℚ) (n : ℕ) : Prop where
  /-- The counts of the chain on `[lo₀, hi₀]`. -/
  counts : ch.Counts lo₀ hi₀
  /-- The lower end lies in `[lo₀, hi₀]`. -/
  le_lo : lo₀ ≤ lo
  /-- The interval is not empty. -/
  lo_lt_hi : lo < hi
  /-- The upper end lies in `[lo₀, hi₀]`. -/
  hi_le : hi ≤ hi₀
  /-- The count at the lower end. -/
  lo_eq : (sturmChanges ch lo).run = n
  /-- The count at the upper end, one less. -/
  hi_add_one_eq : (sturmChanges ch hi).run + 1 = n

private theorem refineInvariant_init {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    (h : RefinePre ch lo₀ hi₀ lo hi nlo) :
    RefineInvariant ch lo₀ hi₀ nlo false (lo, hi, nlo, nhi) :=
  ⟨h.le_lo, h.lo_lt_hi, h.hi_le, rfl, h.lo_eq, h.hi_add_one_eq⟩

private theorem RefineInvariant.post {ch : SturmChain} {lo₀ hi₀ : ℚ} {n : ℕ} {lo hi : ℚ}
    {nlo nhi : ℕ}
    (h : RefineInvariant ch lo₀ hi₀ n true (lo, hi, nlo, nhi)) :
    (sturmChanges ch lo).run = n ∧ (sturmChanges ch hi).run + 1 = n :=
  h.2.2.2.2

private theorem RefineInvariant.exit {ch : SturmChain} {lo₀ hi₀ : ℚ} {n m : ℕ}
    {s : ℚ × ℚ × ℕ × ℕ}
    (h : ⌈(s.2.1 - s.1) * 2 ^ 43⌉₊ = m ∧ RefineInvariant ch lo₀ hi₀ n false s) :
    RefineInvariant ch lo₀ hi₀ n true s :=
  h.2

/-- The root lies in the lower half: the interval becomes `(lo, mid]`. -/
private theorem RefineInvariant.lower {ch : SturmChain} {lo₀ hi₀ : ℚ} {n m : ℕ} {lo hi : ℚ}
    {nlo : ℕ}
    (hpre : RefinePre ch lo₀ hi₀ lo hi nlo)
    {l h : ℚ} {nl nh : ℕ}
    (ht : ¬Double.mpqGetD h - Double.mpqGetD l ≤
      0.5 * Double.ldexp 1.0 (-40) * ((Double.mpqGetD l).fabs + (Double.mpqGetD h).fabs + 1.0))
    {nmid : ℕ} (hmid : nmid = (sturmChanges ch ((l + h) / 2)).run) (hc : (nl == nmid + 1) = true)
    (hinv : ⌈(h - l) * 2 ^ 43⌉₊ = m ∧ RefineInvariant ch lo₀ hi₀ n false (l, h, nl, nh)) :
    ⌈((l + h) / 2 - l) * 2 ^ 43⌉₊ < m ∧
      RefineInvariant ch lo₀ hi₀ n false (l, (l + h) / 2, nl, nmid) := by
  simp only [RefineInvariant, Std.WP.WhileInvariant.mk_apply] at hinv ⊢
  obtain ⟨rfl, h1, h2, h3, rfl, h5, h6⟩ := hinv
  have hw := hpre.counts.one_lt_sub_mul_of_not_le h1 h2 h3 ht
  simp only [beq_iff_eq] at hc
  refine ⟨?_, h1, by linarith, by linarith, rfl, h5, by lia⟩
  rw [show ((l + h) / 2 - l) * 2 ^ 43 = (h - l) * 2 ^ 43 / 2 by ring]
  exact Nat.ceil_div_two_lt_ceil hw

/-- The root lies in the upper half: the interval becomes `(mid, hi]`, its count at `mid` that at
`lo`, since the counts decrease and differ by one between `lo` and `hi`. -/
private theorem RefineInvariant.upper {ch : SturmChain} {lo₀ hi₀ : ℚ} {n m : ℕ} {lo hi : ℚ}
    {nlo : ℕ}
    (hpre : RefinePre ch lo₀ hi₀ lo hi nlo)
    {l h : ℚ} {nl nh : ℕ}
    (ht : ¬Double.mpqGetD h - Double.mpqGetD l ≤
      0.5 * Double.ldexp 1.0 (-40) * ((Double.mpqGetD l).fabs + (Double.mpqGetD h).fabs + 1.0))
    {nmid : ℕ} (hmid : nmid = (sturmChanges ch ((l + h) / 2)).run) (hc : ¬(nl == nmid + 1) = true)
    (hinv : ⌈(h - l) * 2 ^ 43⌉₊ = m ∧ RefineInvariant ch lo₀ hi₀ n false (l, h, nl, nh)) :
    ⌈(h - (l + h) / 2) * 2 ^ 43⌉₊ < m ∧
      RefineInvariant ch lo₀ hi₀ n false ((l + h) / 2, h, nmid, nh) := by
  simp only [RefineInvariant, Std.WP.WhileInvariant.mk_apply] at hinv ⊢
  obtain ⟨rfl, h1, h2, h3, rfl, h5, h6⟩ := hinv
  have hw := hpre.counts.one_lt_sub_mul_of_not_le h1 h2 h3 ht
  simp only [beq_iff_eq] at hc
  have a1 := hpre.counts.antitone h1 (show l ≤ (l + h) / 2 by linarith) (by linarith)
  have a2 := hpre.counts.antitone (show lo₀ ≤ (l + h) / 2 by linarith)
    (show (l + h) / 2 ≤ h by linarith) h3
  refine ⟨?_, by linarith, by linarith, h3, by lia, by lia, h6⟩
  rw [show (h - (l + h) / 2) * 2 ^ 43 = (h - l) * 2 ^ 43 / 2 by ring]
  exact Nat.ceil_div_two_lt_ceil hw

attribute [local irreducible] RefineInvariant in
/-- `JPoints.sturmRefine` refines an interval `(lo, hi]` of `[lo₀, hi₀]` that holds one root, by
the counts of the chain at its ends, to one with the same counts. Its loop ends since the width
halves at each step and the test in doubles holds for a width of at most `2 ^ (-43)`
(`JPoints.Double.mpqGetD_sub_mpqGetD_le`). -/
@[spec]
theorem sturmRefine_spec (ch : SturmChain) (lo₀ hi₀ lo hi : ℚ) (nlo nhi : ℕ) :
    ⦃ RefinePre ch lo₀ hi₀ lo hi nlo ⦄ sturmRefine ch lo hi nlo nhi
    ⦃ fun r ↦ (sturmChanges ch r.1).run = nlo ∧ (sturmChanges ch r.2).run + 1 = nlo ⦄ := by
  vcgen [sturmRefine, Std.WP.Id.triple_eq_run (sturmChanges ch _)] invariants
  | inv1 => RefineInvariant ch lo₀ hi₀ nlo
  | inv2 => .ofMeasure fun s : ℚ × ℚ × ℕ × ℕ ↦ ⌈(s.2.1 - s.1) * 2 ^ 43⌉₊
  all_goals try vc_simp
  all_goals with_reducible first
    | exact refineInvariant_init ‹_›
    | exact RefineInvariant.post ‹_›
    | exact RefineInvariant.exit ‹_›
    | exact RefineInvariant.lower ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact RefineInvariant.upper ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The isolating intervals `roots` that `JPoints.sturmIsolate` has recorded up to `x`, for the
chain `ch` with the count `v₀` at the lower end of the whole interval: arrays of six ends, the
number of intervals the number of roots up to `x` (`v₀` less the count at `x`), and the interval
`j` holding the root `j`, the count `v₀ - j` at its lower end and `v₀ - j - 1` at its upper end. -/
structure RootIntervals.Isolated (ch : SturmChain) (v₀ : ℕ) (roots : RootIntervals) (x : ℚ) :
    Prop where
  /-- Six lower ends. -/
  size_rootLo : roots.rootLo.size = 6
  /-- Six upper ends. -/
  size_rootHi : roots.rootHi.size = 6
  /-- The number of intervals is that of the roots up to `x`. -/
  numRoots_add : roots.numRoots + (sturmChanges ch x).run = v₀
  /-- The count at the lower end of the interval `j`. -/
  rootLo_add {j : ℕ} (hj : j < roots.numRoots) : (sturmChanges ch roots.rootLo[j]!).run + j = v₀
  /-- The count at the upper end of the interval `j`. -/
  rootHi_add {j : ℕ} (hj : j < roots.numRoots) :
    (sturmChanges ch roots.rootHi[j]!).run + j + 1 = v₀

/-- What `JPoints.sturmIsolate` needs at the interval `(lo, hi]` of `[lo₀, hi₀]` with the counts
`nlo` and `nhi` at its ends: the counts of the chain `ch` as `JPoints.SturmChain.Counts` has them,
and the intervals `roots` recorded up to `lo`. -/
structure IsolatePre (ch : SturmChain) (lo₀ hi₀ lo hi : ℚ) (nlo nhi : ℕ) (roots : RootIntervals) :
    Prop where
  /-- The counts of the chain. -/
  counts : ch.Counts lo₀ hi₀
  /-- The interval starts in `[lo₀, hi₀]`. -/
  le_lo : lo₀ ≤ lo
  /-- The interval is not empty. -/
  lo_lt_hi : lo < hi
  /-- The interval ends in `[lo₀, hi₀]`. -/
  hi_le : hi ≤ hi₀
  /-- The count at the lower end. -/
  nlo_eq : (sturmChanges ch lo).run = nlo
  /-- The count at the upper end. -/
  nhi_eq : (sturmChanges ch hi).run = nhi
  /-- The intervals recorded up to the lower end. -/
  isolated : roots.Isolated ch (sturmChanges ch lo₀).run lo

private theorem RootIntervals.isolated_of_none_eq_some {ch : SturmChain} {v₀ : ℕ} {x : ℚ}
    {r : RootIntervals} (h : none = some r) : r.Isolated ch v₀ x :=
  nomatch h

/-- No root in the interval: the intervals recorded up to its lower end are those up to its upper
end. -/
private theorem IsolatePre.isolated_of_beq {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots)
    (hb : (nlo == nhi) = true) {r : RootIntervals} (hr : some roots = some r) :
    r.Isolated ch (sturmChanges ch lo₀).run hi := by
  obtain rfl := Option.some.inj hr
  have hi := h.isolated
  simp only [beq_iff_eq] at hb
  exact ⟨hi.size_rootLo, hi.size_rootHi, by rw [h.nhi_eq, ← hb, ← h.nlo_eq]; exact hi.numRoots_add,
    hi.rootLo_add, hi.rootHi_add⟩

private theorem IsolatePre.refinePre {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots)
    (hb : (nlo == nhi + 1) = true) : RefinePre ch lo₀ hi₀ lo hi nlo := by
  simp only [beq_iff_eq] at hb
  exact ⟨h.counts, h.le_lo, h.lo_lt_hi, h.hi_le, h.nlo_eq, by rw [h.nhi_eq, hb]⟩

-- The lower ends of the intervals with the interval of the root `numRoots` appended.
private theorem RootIntervals.Isolated.rootLo_add_set! {ch : SturmChain} {v₀ : ℕ}
    {roots : RootIntervals} {x : ℚ} (hi : roots.Isolated ch v₀ x) (h6 : roots.numRoots < 6)
    {l : ℚ} (hl : (sturmChanges ch l).run + roots.numRoots = v₀) {j : ℕ}
    (hj : j < roots.numRoots + 1) :
    (sturmChanges ch (roots.rootLo.set! roots.numRoots l)[j]!).run + j = v₀ := by
  rcases (show j < roots.numRoots ∨ j = roots.numRoots by lia) with hj | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]; exact hi.rootLo_add hj
  · rwa [Array.getElem!_set!_self _ _ _ (by lia [hi.size_rootLo])]

-- The upper ends of the intervals with the interval of the root `numRoots` appended.
private theorem RootIntervals.Isolated.rootHi_add_set! {ch : SturmChain} {v₀ : ℕ}
    {roots : RootIntervals} {x : ℚ} (hi : roots.Isolated ch v₀ x) (h6 : roots.numRoots < 6)
    {h : ℚ} (hh : (sturmChanges ch h).run + roots.numRoots + 1 = v₀) {j : ℕ}
    (hj : j < roots.numRoots + 1) :
    (sturmChanges ch (roots.rootHi.set! roots.numRoots h)[j]!).run + j + 1 = v₀ := by
  rcases (show j < roots.numRoots ∨ j = roots.numRoots by lia) with hj | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]; exact hi.rootHi_add hj
  · rwa [Array.getElem!_set!_self _ _ _ (by lia [hi.size_rootHi])]

/-- One root in the interval, refined to `(l, h']`: recorded as the interval of the next root. -/
private theorem IsolatePre.isolated_record {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots)
    (hb : (nlo == nhi + 1) = true) {l h' : ℚ}
    (hr : (sturmChanges ch l).run = nlo ∧ (sturmChanges ch h').run + 1 = nlo)
    (h6 : roots.numRoots < 6) {r : RootIntervals}
    (hs : some ⟨roots.rootLo.set! roots.numRoots l, roots.rootHi.set! roots.numRoots h',
      roots.numRoots + 1⟩ = some r) :
    r.Isolated ch (sturmChanges ch lo₀).run hi := by
  obtain rfl := Option.some.inj hs
  have hi := h.isolated
  have hn := hi.numRoots_add
  rw [h.nlo_eq] at hn
  simp only [beq_iff_eq] at hb
  exact ⟨by simp [hi.size_rootLo], by simp [hi.size_rootHi],
    by change roots.numRoots + 1 + _ = _; lia [h.nhi_eq],
    fun hj ↦ hi.rootLo_add_set! h6 (by lia [hr.1]) hj,
    fun hj ↦ hi.rootHi_add_set! h6 (by lia [hr.2]) hj⟩

/-- Six intervals recorded, a root left: impossible, since the counts decrease by at most six. -/
private theorem IsolatePre.isolated_of_not_lt {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots)
    (hb : (nlo == nhi + 1) = true) (h6 : ¬roots.numRoots < 6) (r : RootIntervals) :
    r.Isolated ch (sturmChanges ch lo₀).run hi := by
  simp only [beq_iff_eq] at hb
  have := h.counts.antitone (h.le_lo.trans h.lo_lt_hi.le) h.hi_le le_rfl
  have := h.counts.le_add_six
  have := h.isolated.numRoots_add
  lia [h.nlo_eq, h.nhi_eq]

private theorem IsolatePre.lower {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots) {nmid : ℕ}
    (hmid : nmid = (sturmChanges ch ((lo + hi) / 2)).run) :
    IsolatePre ch lo₀ hi₀ lo ((lo + hi) / 2) nlo nmid roots :=
  ⟨h.counts, h.le_lo, by linarith [h.lo_lt_hi], by linarith [h.lo_lt_hi, h.hi_le], h.nlo_eq,
    hmid.symm, h.isolated⟩

private theorem IsolatePre.upper {ch : SturmChain} {lo₀ hi₀ lo hi : ℚ} {nlo nhi : ℕ}
    {roots : RootIntervals} (h : IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots) {nmid : ℕ}
    (hmid : nmid = (sturmChanges ch ((lo + hi) / 2)).run) {o : Option RootIntervals}
    (ho : ∀ r, o = some r → r.Isolated ch (sturmChanges ch lo₀).run ((lo + hi) / 2))
    {r : RootIntervals} (hr : o = some r) :
    IsolatePre ch lo₀ hi₀ ((lo + hi) / 2) hi nmid nhi r :=
  ⟨h.counts, by linarith [h.lo_lt_hi, h.le_lo], by linarith [h.lo_lt_hi], h.hi_le, hmid.symm,
    h.nhi_eq, ho r hr⟩

/-- `JPoints.sturmIsolate` isolates the roots in `(lo, hi]`, an interval of `[lo₀, hi₀]`, by the
counts of the chain (`JPoints.SturmChain.Counts`): when the fuel lasts, the intervals it returns
are those recorded up to `hi` (`JPoints.RootIntervals.Isolated`). -/
theorem sturmIsolate_spec (ch : SturmChain) (lo₀ hi₀ : ℚ) (fuel : ℕ) (lo hi : ℚ) (nlo nhi : ℕ)
    (roots : RootIntervals) :
    ⦃ IsolatePre ch lo₀ hi₀ lo hi nlo nhi roots ⦄ sturmIsolate ch fuel lo hi nlo nhi roots
    ⦃ fun r ↦ ∀ roots', r = some roots' → roots'.Isolated ch (sturmChanges ch lo₀).run hi ⦄ := by
  induction fuel generalizing lo hi nlo nhi roots with
  | zero =>
    vcgen [sturmIsolate, sturmRefine_spec ch lo₀ hi₀]
    all_goals with_reducible first
      | exact IsolatePre.isolated_of_beq ‹_› ‹_› ‹_›
      | exact IsolatePre.refinePre ‹_› ‹_›
      | exact IsolatePre.isolated_record ‹_› ‹_› ‹_› ‹_› ‹_›
      | exact IsolatePre.isolated_of_not_lt ‹_› ‹_› ‹_› _
      | exact RootIntervals.isolated_of_none_eq_some ‹_›
  | succ fuel ih =>
    vcgen [sturmIsolate, sturmRefine_spec ch lo₀ hi₀, Std.WP.Id.triple_eq_run (sturmChanges ch _),
      ih]
    all_goals with_reducible first
      | exact IsolatePre.isolated_of_beq ‹_› ‹_› ‹_›
      | exact IsolatePre.refinePre ‹_› ‹_›
      | exact IsolatePre.isolated_record ‹_› ‹_› ‹_› ‹_› ‹_›
      | exact IsolatePre.isolated_of_not_lt ‹_› ‹_› ‹_› _
      | exact RootIntervals.isolated_of_none_eq_some ‹_›
      | exact IsolatePre.lower ‹_› ‹_›
      | exact IsolatePre.upper ‹_› ‹_› ‹_› ‹_›


/-- The number of the sign variations of the Sturm sequence of `F` and `F'` at `x`, the count of
`JPoints.SturmTheorem`. -/
noncomputable abbrev sturmV (F : ℝ[X]) (x : ℝ) : ℕ :=
  ((sturmSeq F (derivative F)).map (eval x)).signVariations

/-- The counts of a finished chain for `f` (`JPoints.realRootsChain_spec`) at a rational number are
those of the Sturm sequence of the real polynomial of `f`. -/
theorem SturmChain.IsFinished.run_sturmChanges {f : ℚ[X]} {ch : SturmChain}
    (h : ch.IsFinished f) (x : ℚ) :
    (sturmChanges ch x).run = sturmV (f.map (algebraMap ℚ ℝ)) x := by
  have hc : (sturmChanges ch x).run =
      ((List.range ch.len).map fun i ↦ (rowPoly ch.sturm i).eval x).signVariations :=
    (sturmChanges_spec f ch x).le_wp h.toWF
  rw [hc, sturmV, derivative_map, sturmSeq_map, ← h.map_rowPoly_eq_sturmSeq,
    List.map_map, List.map_map,
    ← List.signVariations_map (f := fun q : ℚ ↦ (q : ℝ)) sign_ratCast, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦
    ((eval_ratCast_map (algebraMap ℚ ℝ) _ x).trans (eq_ratCast _ _)).symm

/-! ### Sturm's theorem on the real line -/

section SturmTheorem

variable {F : ℝ[X]}

theorem sturmV_le_of_le (hS : SturmTheorem) (hF : Squarefree F) {x y : ℝ} (hxy : x ≤ y) :
    sturmV F y ≤ sturmV F x :=
  (Nat.le_add_left _ _).trans_eq (hS F hF x y hxy)

/-- With every real root of `F` below `B`, the number of the roots above `x` and the count at `B`
add up to the count at `x`, for every `x`. -/
theorem ncard_add_sturmV (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → y < B) (x : ℝ) :
    {y | x < y ∧ F.IsRoot y}.ncard + sturmV F B = sturmV F x := by
  rcases le_or_gt x B with hx | hx
  · have := hS F hF x B hx
    rwa [show {y | x < y ∧ y ≤ B ∧ F.IsRoot y} = {y | x < y ∧ F.IsRoot y} from
      Set.ext fun y ↦ ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, (hB y h.2).le, h.2⟩⟩] at this
  · have := hS F hF B x hx.le
    rw [show {y | B < y ∧ y ≤ x ∧ F.IsRoot y} = ∅ from
      Set.eq_empty_of_forall_notMem fun y h ↦ (hB y h.2.2).not_gt h.1, Set.ncard_empty,
      zero_add] at this
    rw [show {y | x < y ∧ F.IsRoot y} = ∅ from
      Set.eq_empty_of_forall_notMem fun y h ↦ (hB y h.2).not_gt (hx.trans h.1), Set.ncard_empty,
      zero_add]
    exact this.symm

/-- `JPoints.ncard_add_sturmV` with every real root of `F` in `(-B, B)`. -/
private theorem ncard_add_sturmV_of_abs_lt (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → |y| < B) (x : ℝ) :
    {y | x < y ∧ F.IsRoot y}.ncard + sturmV F B = sturmV F x :=
  ncard_add_sturmV hS hF (fun y hy ↦ (le_abs_self y).trans_lt (hB y hy)) x

/-- With every real root of `F` below `B`, the count at any point exceeds that at `B` by at most
the degree of `F`, the most roots there are. -/
private theorem sturmV_le_sturmV_add_natDegree (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → y < B) (x : ℝ) : sturmV F x ≤ sturmV F B + F.natDegree := by
  rw [← ncard_add_sturmV hS hF hB x]
  lia [ncard_setOf_isRoot_le_natDegree hF.ne_zero (x < ·)]

/-- By Sturm's theorem, a point `x` above `a` with the count of `a` is not a root. -/
private theorem not_isRoot_of_sturmV_eq (hS : SturmTheorem) (hF : Squarefree F) {a x : ℝ}
    (hax : a < x)
    (h : sturmV F a = sturmV F x) : ¬F.IsRoot x := fun hx ↦ by
  have h1 := hS F hF a x hax.le
  have hfin : {y | a < y ∧ y ≤ x ∧ F.IsRoot y}.Finite :=
    (finite_setOfPred_isRoot hF.ne_zero).subset fun y hy ↦ hy.2.2
  have := (Set.ncard_pos hfin).mpr ⟨x, hax, le_rfl, hx⟩
  lia

/-- With every real root of `F` in `(-B, B)`, the count at every point is at most that at `-B`. -/
private theorem sturmV_le_sturmV_neg (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → |y| < B) (t : ℝ) : sturmV F t ≤ sturmV F (-B) := by
  have K1 := ncard_add_sturmV_of_abs_lt hS hF hB
  rw [← K1 t, ← K1 (-B)]
  refine Nat.add_le_add_right (Set.ncard_le_ncard (s := {y | t < y ∧ F.IsRoot y})
    (t := {y | -B < y ∧ F.IsRoot y}) (fun y hy ↦ ⟨?_, hy.2⟩)
    ((finite_setOfPred_isRoot hF.ne_zero).subset fun y hy ↦ hy.2)) _
  exact (abs_lt.mp (hB y hy.2)).1

/-- The count at a point `x` in a gap between the isolating intervals that the counts at their
ends `lo j` and `hi j` describe, with every real root in `(-B, B)`: above the interval `i - 1` and
below the interval `i` of `n`, it is the count at `-B` less `i`. -/
private theorem sturmV_add_eq_of_gap (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → |y| < B) {n i : ℕ} {lo hi : ℕ → ℝ}
    (hn : n + sturmV F B = sturmV F (-B)) (hlo : ∀ j < n, sturmV F (lo j) + j = sturmV F (-B))
    (hhi : ∀ j < n, sturmV F (hi j) + j + 1 = sturmV F (-B)) (hin : i ≤ n) {x : ℝ}
    (hx1 : 0 < i → hi (i - 1) < x) (hx2 : i < n → x < lo i) :
    sturmV F x + i = sturmV F (-B) := by
  have K1 := ncard_add_sturmV_of_abs_lt hS hF hB
  have hup : sturmV F x + i ≤ sturmV F (-B) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using sturmV_le_sturmV_neg hS hF hB x
    · lia [sturmV_le_of_le hS hF (hx1 hi0).le, hhi (i - 1) (by lia)]
  rcases (show i < n ∨ i = n by lia) with hi' | rfl
  · lia [sturmV_le_of_le hS hF (hx2 hi').le, hlo i hi']
  · lia [K1 x]

/-- For the isolating intervals `(lo j, hi j]` of the `n` real roots of `F` in `(-B, B)`, described
by the counts of the Sturm sequence at their ends: a point `x` above the interval `i - 1` and below
the interval `i` is not a root, and `n - i` roots lie above it. -/
theorem not_isRoot_and_ncard_eq (hS : SturmTheorem) (hF : Squarefree F) {B : ℝ}
    (hB : ∀ y, F.IsRoot y → |y| < B) {n i : ℕ} {lo hi : ℕ → ℝ}
    (hn : n + sturmV F B = sturmV F (-B)) (hlo : ∀ j < n, sturmV F (lo j) + j = sturmV F (-B))
    (hhi : ∀ j < n, sturmV F (hi j) + j + 1 = sturmV F (-B)) (hin : i ≤ n) {x : ℝ}
    (hx1 : 0 < i → hi (i - 1) < x) (hx2 : i < n → x < lo i) :
    ¬F.IsRoot x ∧ {y | x < y ∧ F.IsRoot y}.ncard = n - i := by
  have hV := sturmV_add_eq_of_gap hS hF hB hn hlo hhi hin hx1 hx2
  have K1 := ncard_add_sturmV_of_abs_lt hS hF hB
  refine ⟨fun hx ↦ ?_, by lia [K1 x]⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases lt_or_ge (-B) x with h | h
    · exact not_isRoot_of_sturmV_eq hS hF h (by lia) hx
    · linarith [(abs_lt.mp (hB x hx)).1]
  · exact not_isRoot_of_sturmV_eq hS hF (hx1 hi0) (by lia [hhi (i - 1) (by lia)]) hx

end SturmTheorem


/-! ### The Cauchy bound -/

/-- The invariant of the loop of `JPoints.realRootsBound` for the coefficients `coeffs` of degree
`deg`: after `k` steps, `B ≥ 0` and `|fⱼ| ≤ |f_deg| B` for `j < k`. -/
def BoundInvariant (coeffs : Array ℤ) (deg : ℕ) : Std.WP.Invariant ℕ ℤ Prop :=
  fun pref _ B ↦ 0 ≤ B ∧ ∀ k < pref.length, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * B

private theorem boundInvariant_nil (coeffs : Array ℤ) (deg : ℕ) (suff : List ℕ) :
    BoundInvariant coeffs deg [] suff 0 :=
  ⟨le_rfl, nofun⟩

/-- The step of the loop of `JPoints.realRootsBound` to a bound `B' ≥ B` that covers the coefficient
at the cursor. -/
private theorem BoundInvariant.append_singleton {coeffs : Array ℤ} {deg : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:deg] = pref ++ cur :: suff) {B B' : ℤ}
    (hinv : BoundInvariant coeffs deg pref (cur :: suff) B) (hB : B ≤ B')
    (hcur : (coeffs[cur]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * B') :
    BoundInvariant coeffs deg (pref ++ [cur]) suff B' := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  obtain ⟨hB0, hk⟩ := hinv
  refine ⟨by lia, fun k hk' ↦ ?_⟩
  rw [List.length_append, List.length_singleton] at hk'
  rcases (show k < pref.length ∨ k = cur by lia) with h | rfl
  · exact (hk k h).trans (mul_le_mul_of_nonneg_left hB (Int.natCast_nonneg _))
  · exact hcur

private theorem BoundInvariant.of_lt {coeffs : Array ℤ} {deg : ℕ} (h0 : ¬coeffs[deg]! = 0)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:deg] = pref ++ cur :: suff) {B : ℤ}
    (hinv : BoundInvariant coeffs deg pref (cur :: suff) B)
    (hB : B < -(-(coeffs[cur]!.natAbs : ℤ) / coeffs[deg]!.natAbs)) :
    BoundInvariant coeffs deg (pref ++ [cur]) suff
      (-(-(coeffs[cur]!.natAbs : ℤ) / coeffs[deg]!.natAbs)) :=
  hinv.append_singleton hl hB.le (Int.le_mul_neg_ediv_neg _ (by simpa using h0))

private theorem BoundInvariant.of_not_lt {coeffs : Array ℤ} {deg : ℕ} (h0 : ¬coeffs[deg]! = 0)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:deg] = pref ++ cur :: suff) {B : ℤ}
    (hinv : BoundInvariant coeffs deg pref (cur :: suff) B)
    (hB : ¬B < -(-(coeffs[cur]!.natAbs : ℤ) / coeffs[deg]!.natAbs)) :
    BoundInvariant coeffs deg (pref ++ [cur]) suff B := by
  have hd : (0 : ℤ) < coeffs[deg]!.natAbs := by simpa using h0
  exact hinv.append_singleton hl le_rfl ((Int.le_mul_neg_ediv_neg _ hd).trans
    (mul_le_mul_of_nonneg_left (not_lt.mp hB) hd.le))

private theorem BoundInvariant.post {coeffs : Array ℤ} {deg : ℕ} {B : ℤ}
    (h : BoundInvariant coeffs deg (ForIn.toList [:deg]) [] B) :
    2 ≤ B + 2 ∧ ∀ k < deg, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * (B + 2 - 2) := by
  obtain ⟨hB0, hk⟩ := h
  rw [Std.Legacy.Range.length_toList_zero_start] at hk
  exact ⟨by lia, fun k hk' ↦ by rw [add_sub_cancel_right]; exact hk k hk'⟩

attribute [local irreducible] BoundInvariant in
/-- `JPoints.realRootsBound` returns the Cauchy bound `B ≥ 2` with `|fₖ| ≤ |f_deg| (B - 2)` for
the coefficients `fₖ`, `k < deg`, of a polynomial with `f_deg ≠ 0`. -/
@[spec]
theorem realRootsBound_spec (coeffs : Array ℤ) (deg : ℕ) :
    ⦃ coeffs[deg]! ≠ 0 ⦄ realRootsBound coeffs deg
    ⦃ fun r ↦ 2 ≤ r ∧ ∀ k < deg, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * (r - 2) ⦄ := by
  vcgen [realRootsBound] invariants
  | inv1 => BoundInvariant coeffs deg
  all_goals with_reducible first
    | exact boundInvariant_nil coeffs deg _
    | exact BoundInvariant.post ‹_›
    | exact BoundInvariant.of_lt ‹_› ‹_› ‹_› ‹_›
    | exact BoundInvariant.of_not_lt ‹_› ‹_› ‹_› ‹_›

/-! ### The intervals on which `f` is negative -/

/-- The number of the negative intervals among the first `m` of `JPoints.realRootsRecord`, whose
signs alternate from `sgnInf` on: the even ones for `sgnInf < 0`, the odd ones otherwise. -/
def negCount (sgnInf : ℤ) (m : ℕ) : ℕ := if sgnInf < 0 then (m + 1) / 2 else m / 2

private theorem negCount_succ {sgnInf : ℤ} (hs : sgnInf ≠ 0) (m : ℕ) :
    negCount sgnInf (m + 1) =
      negCount sgnInf m +
        if (if (m % 2 == 0) = true then sgnInf else -sgnInf) < 0 then 1 else 0 := by
  simp only [negCount, beq_iff_eq]
  split_ifs <;> lia

/-- The doubles `lo` and `hi` are the ends of an interval on which the polynomial `f` is negative:
no NaN, and `f` negative at every rational number strictly between their values. -/
def NegativeEnds (f : ℚ[X]) (lo hi : Double) : Prop :=
  ¬IsNaN lo.bits ∧ ¬IsNaN hi.bits ∧
    ∀ x : ℚ, doubleValue lo.bits < x → (x : WithBotTop ℚ) < doubleValue hi.bits → f.eval x < 0

/-- The invariant of the loop of `JPoints.realRootsRecord` for the polynomial `f` with the sign
`sgnInf` at `+∞`: the arrays of the shrunk intervals have eight entries, the first `m` intervals
from the right gave `JPoints.negCount sgnInf m` negative ones, and each of those has ends between
which `f` is negative (`JPoints.NegativeEnds`). -/
def RecordInvariant (f : ℚ[X]) (sgnInf : ℤ) : Std.WP.Invariant ℕ NegativeIntervals Prop :=
  fun pref _ neg ↦ neg.shrunkLo.size = 8 ∧ neg.shrunkHi.size = 8 ∧
    neg.numNeg = negCount sgnInf pref.length ∧
    ∀ k < neg.numNeg, NegativeEnds f neg.shrunkLo[k]! neg.shrunkHi[k]!

-- The ends of the negative intervals with an interval appended.
private theorem negativeEnds_set! {f : ℚ[X]} {neg : NegativeIntervals}
    (h1 : neg.shrunkLo.size = 8) (h2 : neg.shrunkHi.size = 8) (hk : neg.numNeg < 8)
    (h : ∀ k < neg.numNeg, NegativeEnds f neg.shrunkLo[k]! neg.shrunkHi[k]!) {slo shi : Double}
    (hn : NegativeEnds f slo shi) {k : ℕ} (hk' : k < neg.numNeg + 1) :
    NegativeEnds f (neg.shrunkLo.set! neg.numNeg slo)[k]!
      (neg.shrunkHi.set! neg.numNeg shi)[k]! := by
  rcases (show k < neg.numNeg ∨ k = neg.numNeg by lia) with hk'' | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h k hk''
  · rwa [Array.getElem!_set!_self _ _ _ (by lia), Array.getElem!_set!_self _ _ _ (by lia)]

/-- The lower end of the shrunk interval above the root `i - 1`: no NaN, and below a point only
if the upper end of the isolating interval of the root `i - 1` is. -/
private theorem not_isNaN_shrunkLo_and_rootHi_lt (roots : RootIntervals) (i : ℕ) :
    ¬IsNaN (if (i == 0) = true then (-Double.huge, -Double.huge) else
      ((Double.mpqGetD roots.rootLo[i - 1]!).nextDown,
        (Double.mpqGetD roots.rootHi[i - 1]!).nextUp)).2.bits ∧
    ∀ x : ℚ, doubleValue (if (i == 0) = true then (-Double.huge, -Double.huge) else
      ((Double.mpqGetD roots.rootLo[i - 1]!).nextDown,
        (Double.mpqGetD roots.rootHi[i - 1]!).nextUp)).2.bits < x →
      0 < i → roots.rootHi[i - 1]! < x := by
  split_ifs with h
  · simp only [beq_iff_eq] at h
    exact ⟨(Double.isNaN_eq_false_iff _).mp Double.isNaN_huge_neg, fun _ _ hi ↦ by lia⟩
  · exact ⟨(Double.isNaN_eq_false_iff _).mp (Double.isNaN_nextUp (Double.isNaN_mpqGetD _)),
      fun x hx _ ↦ WithBotTop.coe_lt_coe.mp
        ((Double.lt_nextUp_and_nextDown_lt_mpqGetD _).1.trans hx)⟩

/-- The upper end of the shrunk interval below the root `i` of `n`: no NaN, and above a point only
if the lower end of the isolating interval of the root `i` is. -/
private theorem not_isNaN_shrunkHi_and_lt_rootLo (roots : RootIntervals) (i n : ℕ) :
    ¬IsNaN (if (i == n) = true then (Double.huge, Double.huge) else
      ((Double.mpqGetD roots.rootHi[i]!).nextUp,
        (Double.mpqGetD roots.rootLo[i]!).nextDown)).2.bits ∧
    ∀ x : ℚ, (x : WithBotTop ℚ) < doubleValue (if (i == n) = true then
      (Double.huge, Double.huge) else ((Double.mpqGetD roots.rootHi[i]!).nextUp,
        (Double.mpqGetD roots.rootLo[i]!).nextDown)).2.bits →
      i < n → x < roots.rootLo[i]! := by
  split_ifs with h
  · simp only [beq_iff_eq] at h
    exact ⟨(Double.isNaN_eq_false_iff _).mp Double.isNaN_huge, fun _ _ hi ↦ by lia⟩
  · exact ⟨(Double.isNaN_eq_false_iff _).mp (Double.isNaN_nextDown (Double.isNaN_mpqGetD _)),
      fun x hx _ ↦ WithBotTop.coe_lt_coe.mp
        (hx.trans (Double.lt_nextUp_and_nextDown_lt_mpqGetD _).2)⟩

/-- What `JPoints.realRootsRecord` needs of the coefficients `coeffs` of degree `deg` and the
isolating intervals `roots` of the roots of `f`: a nonzero leading coefficient, at most six roots,
and `f` negative between the isolating intervals of the roots `i - 1` and `i` when the sign that the
record computes for that gap is. -/
structure RecordPre (coeffs : Array ℤ) (deg : ℕ) (roots : RootIntervals) : Prop where
  /-- The leading coefficient is not zero. -/
  sign_ne_zero : coeffs[deg]!.sign ≠ 0
  /-- At most six roots. -/
  numRoots_le : roots.numRoots ≤ 6
  /-- `f` is negative in a gap of a negative sign. -/
  eval_neg {i : ℕ} (hi : i ≤ roots.numRoots) {x : ℚ} (hlo : 0 < i → roots.rootHi[i - 1]! < x)
    (hhi : i < roots.numRoots → x < roots.rootLo[i]!)
    (hs : (if ((roots.numRoots - i) % 2 == 0) = true then coeffs[deg]!.sign
      else -coeffs[deg]!.sign) < 0) : (poly coeffs.toList).eval x < 0

private theorem recordInvariant_nil (f : ℚ[X]) (sgnInf : ℤ) (suff : List ℕ) :
    RecordInvariant f sgnInf [] suff {} :=
  ⟨rfl, rfl, by simp [negCount], nofun⟩

private theorem RecordInvariant.post {coeffs : Array ℤ} {deg : ℕ} {roots : RootIntervals}
    (hpre : RecordPre coeffs deg roots) {neg : NegativeIntervals}
    (h : RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign
      (ForIn.toList [:roots.numRoots + 1]) [] neg) : neg.Sound coeffs.toList := by
  obtain ⟨-, -, hn, hk⟩ := h
  rw [Std.Legacy.Range.length_toList_zero_start] at hn
  have h6 := hpre.numRoots_le
  exact ⟨by rw [hn, negCount]; split_ifs <;> lia, fun hi ↦ (hk _ hi).1, fun hi ↦ (hk _ hi).2.1,
    fun hi ↦ (hk _ hi).2.2 _⟩

private theorem RecordInvariant.skip {coeffs : Array ℤ} {deg : ℕ} {roots : RootIntervals}
    (hpre : RecordPre coeffs deg roots) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:roots.numRoots + 1] = pref ++ cur :: suff) {neg : NegativeIntervals}
    (hinv : RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign pref (cur :: suff) neg)
    (hs : ¬(if ((roots.numRoots - (roots.numRoots - cur)) % 2 == 0) = true then
      coeffs[deg]!.sign else -coeffs[deg]!.sign) < 0) :
    RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign (pref ++ [cur]) suff neg := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  rw [show roots.numRoots - (roots.numRoots - cur) = cur by lia] at hs
  refine ⟨h1, h2, ?_, h4⟩
  rw [List.length_append, List.length_singleton, negCount_succ hpre.sign_ne_zero, hc,
    ite_eq_right hs, add_zero, h3, hc]

/-- A gap of a negative sign: its shrunk interval, with ends that are no NaN and between whose
values `f` is negative, recorded as the next negative interval. -/
private theorem RecordInvariant.push {coeffs : Array ℤ} {deg : ℕ} {roots : RootIntervals}
    (hpre : RecordPre coeffs deg roots) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:roots.numRoots + 1] = pref ++ cur :: suff) {neg : NegativeIntervals}
    (hinv : RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign pref (cur :: suff) neg)
    (hs : (if ((roots.numRoots - (roots.numRoots - cur)) % 2 == 0) = true then
      coeffs[deg]!.sign else -coeffs[deg]!.sign) < 0) {glo ghi slo shi : Double}
    (hlo : ¬IsNaN slo.bits ∧ ∀ x : ℚ, doubleValue slo.bits < x →
      0 < roots.numRoots - cur → roots.rootHi[roots.numRoots - cur - 1]! < x)
    (hhi : ¬IsNaN shi.bits ∧ ∀ x : ℚ, (x : WithBotTop ℚ) < doubleValue shi.bits →
      roots.numRoots - cur < roots.numRoots → x < roots.rootLo[roots.numRoots - cur]!) :
    RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign (pref ++ [cur]) suff
      ⟨neg.numNeg + 1, neg.grownLo.set! neg.numNeg glo, neg.grownHi.set! neg.numNeg ghi,
        neg.shrunkLo.set! neg.numNeg slo, neg.shrunkHi.set! neg.numNeg shi⟩ := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have h6 := hpre.numRoots_le
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have hgap (x : ℚ) := hpre.eval_neg (i := roots.numRoots - cur) (x := x) (by lia)
  have hs' := hs
  rw [show roots.numRoots - (roots.numRoots - cur) = cur by lia] at hs'
  have hk : neg.numNeg < 8 := by rw [h3, negCount]; split_ifs <;> lia
  refine ⟨by simp [h1], by simp [h2], ?_, fun k hk' ↦ negativeEnds_set! h1 h2 hk h4
    ⟨hlo.1, hhi.1, fun x h5 h6 ↦ hgap x (hlo.2 x h5) (hhi.2 x h6) hs⟩ hk'⟩
  change neg.numNeg + 1 = _
  rw [List.length_append, List.length_singleton, negCount_succ hpre.sign_ne_zero, hc,
    ite_eq_left hs', h3, hc]

attribute [local irreducible] RecordInvariant in
/-- `JPoints.realRootsRecord` records the gaps between the isolating intervals of negative sign
(`JPoints.RecordPre`) as intervals on which `f` is negative (`JPoints.NegativeIntervals.Sound`):
at most four, as the signs of the seven gaps of six roots alternate, with ends that are no NaN
and that lie within the gaps (`JPoints.Double.lt_nextUp_and_nextDown_lt_mpqGetD`). -/
@[spec]
theorem realRootsRecord_spec (coeffs : Array ℤ) (deg : ℕ) (roots : RootIntervals) :
    ⦃ RecordPre coeffs deg roots ⦄ realRootsRecord coeffs deg roots {}
    ⦃ fun r ↦ r.Sound coeffs.toList ⦄ := by
  vcgen [realRootsRecord] invariants
  | inv1 => RecordInvariant (poly coeffs.toList) coeffs[deg]!.sign
  all_goals with_reducible first
    | exact recordInvariant_nil _ _ _
    | exact RecordInvariant.post ‹_› ‹_›
    | exact RecordInvariant.skip ‹_› ‹_› ‹_› ‹_›
    | exact RecordInvariant.push ‹_› ‹_› ‹_› ‹_› (not_isNaN_shrunkLo_and_rootHi_lt roots _)
        (not_isNaN_shrunkHi_and_lt_rootLo roots _ _)


/-! ### The real roots of the curve -/

private theorem leadingCoeff_poly_toList {coeffs : Array ℤ} {deg : ℕ}
    (hd : degree coeffs.toList = deg) :
    (poly coeffs.toList).leadingCoeff = coeffs[deg]! := by
  rw [leadingCoeff_poly, hd, Array.getD_toList_eq_getElem!]

/-- A sign of the gap that `real_roots_init` computes, `sgn_inf` or its negation by the parity of
the number `m` of the roots above the gap, that is negative makes `f` negative at a point `x` of the
gap where the sign of `f` is that of its leading coefficient `c` times `(-1) ^ m`. -/
private theorem eval_lt_zero_of_sign_eq {f : ℚ[X]} {c : ℤ} (hc : f.leadingCoeff = c) {m : ℕ} {x : ℚ}
    (hx : SignType.sign (f.eval x) = SignType.sign f.leadingCoeff * (-1) ^ m)
    (hs : (if (m % 2 == 0) = true then c.sign else -c.sign) < 0) : f.eval x < 0 := by
  rw [hc] at hx
  refine sign_eq_neg_one_iff.mp (hx.trans ?_)
  rcases Nat.even_or_odd m with hm | hm
  · rw [ite_eq_left (by simpa using Nat.even_iff.mp hm)] at hs
    rw [hm.neg_one_pow, mul_one, sign_neg (mod_cast Int.sign_neg_iff.mp hs)]
  · rw [ite_eq_right (by simpa using Nat.odd_iff.mp hm), neg_lt_zero] at hs
    rw [hm.neg_one_pow, mul_neg_one, sign_pos (mod_cast Int.sign_pos_iff.mp hs)]

/-- The real roots of the nonzero polynomial `f` of the coefficients `coeffs` of degree `deg` lie in
`(-B, B)` for the bound `B` of `JPoints.realRootsBound`. -/
theorem abs_lt_of_isRoot_map_poly {coeffs : Array ℤ} {deg : ℕ} (hd : degree coeffs.toList = deg)
    (hf : poly coeffs.toList ≠ 0) {B : ℤ}
    (hB : 2 ≤ B ∧ ∀ k < deg, (coeffs[k]!.natAbs : ℤ) ≤ coeffs[deg]!.natAbs * (B - 2)) {y : ℝ}
    (hy : ((poly coeffs.toList).map (algebraMap ℚ ℝ)).IsRoot y) : |y| < B := by
  have hF : (poly coeffs.toList).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hf
  have hcoeff (k : ℕ) : ((poly coeffs.toList).map (algebraMap ℚ ℝ)).coeff k = coeffs[k]! := by
    rw [coeff_map, coeff_poly, Array.getD_toList_eq_getElem!]
    simp
  have := abs_lt_add_one_of_isRoot hF (C := B - 2) (sub_nonneg.mpr (mod_cast hB.1))
    (fun k hk ↦ by
      rw [leadingCoeff, natDegree_map_poly, hd, hcoeff, hcoeff, ← Int.cast_abs, ← Int.cast_abs,
        Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast hB.2 k (by rwa [natDegree_map_poly, hd] at hk)) hy
  linarith

/-- The counts of the finished chain for the squarefree `f` of seven coefficients, whose real roots
lie in `(-B, B)`, on `[-B, B]`: by Sturm's theorem they decrease, by the number of the roots, at
most six. -/
theorem SturmChain.IsFinished.counts (hS : SturmTheorem) {coeffs : Array ℤ} {deg : ℕ}
    (h7 : coeffs.size = 7) (hd : degree coeffs.toList = deg)
    (hsq : Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hw : ch.IsFinished (poly coeffs.toList)) {B : ℤ}
    (hroot : ∀ y : ℝ, ((poly coeffs.toList).map (algebraMap ℚ ℝ)).IsRoot y → |y| < B)
    (hB : B < 2 ^ 480) : ch.Counts (-(B : ℚ)) B := by
  have hF := squarefree_map_of_squarefree (algebraMap ℚ ℝ) hsq
  have hrun := hw.run_sturmChanges
  have hB' : (B : ℚ) < 2 ^ 480 := by
    have := (Int.cast_lt (R := ℚ)).mpr hB
    rwa [Int.cast_pow, Int.cast_ofNat] at this
  refine ⟨fun {x y} _ hxy _ ↦ ?_, ?_, neg_le_neg hB'.le, hB'.le⟩
  · rw [hrun, hrun]
    exact sturmV_le_of_le hS hF (mod_cast hxy)
  · rw [hrun, hrun]
    have := sturmV_le_sturmV_add_natDegree hS hF (B := ((B : ℚ) : ℝ))
      (fun y hy ↦ by rw [Rat.cast_intCast]; exact (le_abs_self y).trans_lt (hroot y hy))
      ((-(B : ℚ) : ℚ) : ℝ)
    rw [natDegree_map_poly, hd] at this
    lia [hd ▸ degree_toList_le_six h7]

/-- The intervals that `JPoints.sturmIsolate` records up to `B` for the finished chain of `f`, by
the counts of the Sturm sequence of the real polynomial of `f`
(`JPoints.SturmChain.IsFinished.run_sturmChanges`). -/
private theorem RootIntervals.Isolated.sturmV_eq {f : ℚ[X]} {ch : SturmChain}
    (hw : ch.IsFinished f) {B : ℚ}
    {roots : RootIntervals} (hiso : roots.Isolated ch (sturmChanges ch (-B)).run B) :
    roots.numRoots + sturmV (f.map (algebraMap ℚ ℝ)) B =
        sturmV (f.map (algebraMap ℚ ℝ)) (-(B : ℝ)) ∧
      (∀ j < roots.numRoots, sturmV (f.map (algebraMap ℚ ℝ)) roots.rootLo[j]! + j =
        sturmV (f.map (algebraMap ℚ ℝ)) (-(B : ℝ))) ∧
      ∀ j < roots.numRoots, sturmV (f.map (algebraMap ℚ ℝ)) roots.rootHi[j]! + j + 1 =
        sturmV (f.map (algebraMap ℚ ℝ)) (-(B : ℝ)) := by
  have hrun := hw.run_sturmChanges
  have hv : sturmV (f.map (algebraMap ℚ ℝ)) (-(B : ℝ)) = (sturmChanges ch (-B)).run := by
    rw [hrun, Rat.cast_neg]
  refine ⟨?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩ <;> rw [hv, ← hrun]
  · exact hiso.numRoots_add
  · exact hiso.rootLo_add hj
  · exact hiso.rootHi_add hj

/-- At most six intervals are recorded in `(-B, B]` for the finished chain of the squarefree `f` of
seven coefficients, whose real roots lie in `(-B, B)`: one for each root. -/
private theorem RootIntervals.Isolated.numRoots_le (hS : SturmTheorem) {coeffs : Array ℤ} {deg : ℕ}
    (h7 : coeffs.size = 7) (hd : degree coeffs.toList = deg)
    (hsq : Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hw : ch.IsFinished (poly coeffs.toList)) {B : ℚ}
    (hroot : ∀ y : ℝ, ((poly coeffs.toList).map (algebraMap ℚ ℝ)).IsRoot y → |y| < B)
    {roots : RootIntervals} (hiso : roots.Isolated ch (sturmChanges ch (-B)).run B) :
    roots.numRoots ≤ 6 := by
  have hF := squarefree_map_of_squarefree (algebraMap ℚ ℝ) hsq
  have h1 := sturmV_le_sturmV_add_natDegree hS hF (B := (B : ℝ))
    (fun y hy ↦ (le_abs_self y).trans_lt (hroot y hy)) (-(B : ℝ))
  rw [natDegree_map_poly, hd] at h1
  lia [(hiso.sturmV_eq hw).1, hd ▸ degree_toList_le_six h7]

/-- Between the intervals of the roots `i - 1` and `i` recorded in `(-B, B]` for the finished chain
of the squarefree `f`, whose real roots lie in `(-B, B)`, the sign of `f` is that of its leading
coefficient times `(-1) ^ (n - i)` (`JPoints.not_isRoot_and_ncard_eq`,
`Polynomial.sign_eval_eq_sign_leadingCoeff_mul_of_squarefree`), so that `f` is negative there when
the sign that `real_roots_init` computes for the gap is. -/
theorem RootIntervals.Isolated.eval_neg (hS : SturmTheorem) {coeffs : Array ℤ} {deg : ℕ}
    (hd : degree coeffs.toList = deg) (hsq : Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hw : ch.IsFinished (poly coeffs.toList)) {B : ℚ}
    (hroot : ∀ y : ℝ, ((poly coeffs.toList).map (algebraMap ℚ ℝ)).IsRoot y → |y| < B)
    {roots : RootIntervals} (hiso : roots.Isolated ch (sturmChanges ch (-B)).run B) {i : ℕ}
    (hi : i ≤ roots.numRoots) {x : ℚ} (hlo : 0 < i → roots.rootHi[i - 1]! < x)
    (hhi : i < roots.numRoots → x < roots.rootLo[i]!)
    (hs : (if ((roots.numRoots - i) % 2 == 0) = true then coeffs[deg]!.sign
      else -coeffs[deg]!.sign) < 0) : (poly coeffs.toList).eval x < 0 := by
  have hF := squarefree_map_of_squarefree (algebraMap ℚ ℝ) hsq
  obtain ⟨hn, hlo', hhi'⟩ := hiso.sturmV_eq hw
  obtain ⟨hx, hR⟩ := not_isRoot_and_ncard_eq hS hF hroot hn (lo := fun j ↦ (roots.rootLo[j]! : ℝ))
    (hi := fun j ↦ (roots.rootHi[j]! : ℝ)) hlo' hhi' hi (x := (x : ℝ)) (fun h ↦ mod_cast hlo h)
    (fun h ↦ mod_cast hhi h)
  have := sign_eval_eq_sign_leadingCoeff_mul_of_squarefree hF hx
  rw [hR, eval_ratCast_map, eq_ratCast (algebraMap ℚ ℝ), sign_ratCast, leadingCoeff_map,
    eq_ratCast (algebraMap ℚ ℝ), sign_ratCast] at this
  exact eval_lt_zero_of_sign_eq (leadingCoeff_poly_toList hd) this hs

/-- The intervals that `JPoints.sturmIsolate` records in `(-B, B]` for the finished chain of the
squarefree `f`, whose real roots lie in `(-B, B)`, are what `JPoints.realRootsRecord` needs
(`JPoints.RecordPre`). -/
theorem RootIntervals.Isolated.recordPre (hS : SturmTheorem) {coeffs : Array ℤ} {deg : ℕ}
    (h7 : coeffs.size = 7) (hd : degree coeffs.toList = deg) (h0 : 0 < deg)
    (hsq : Squarefree (poly coeffs.toList)) {ch : SturmChain}
    (hw : ch.IsFinished (poly coeffs.toList)) {B : ℚ}
    (hroot : ∀ y : ℝ, ((poly coeffs.toList).map (algebraMap ℚ ℝ)).IsRoot y → |y| < B)
    {roots : RootIntervals} (hiso : roots.Isolated ch (sturmChanges ch (-B)).run B) :
    RecordPre coeffs deg roots :=
  ⟨by rw [Ne, Int.sign_eq_zero_iff_zero]; exact getElem!_degree_ne_zero hd h0,
    hiso.numRoots_le hS h7 hd hsq hw hroot,
    hiso.eval_neg hS hd hsq hw hroot⟩

end JPoints

end
