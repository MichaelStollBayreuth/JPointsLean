/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Check
public import JPoints.Proof.Sift

import JPoints.Proof.Bits
import JPoints.Proof.Containers
import JPoints.Proof.Order
import JPoints.Proof.VCSimp
import Mathlib.Data.Int.ModEq
import Std.Tactic.Do

/-!
# The contracts of the second stage of a word

What the sieve of `j-points` does with a word of the bit array of a row past the first stage:
`check_bits` takes its bits in turn to the test for common factors, the third stage and the exact
check (`JPoints.checkBits_spec`), and `check_point` and-s the word with the rows of the sieve tables
of the second-stage primes before (`JPoints.checkPoint_spec`). Both print the points over the
triples of the bits of the word that their tests keep (`JPoints.CheckGlobals.wordPoints`, over the
third coordinates of the word, `JPoints.wordCols`), keep the data of the third stage consistent and
change no other field of the state of the thread but the counters and the output: the state that
they leave is the state given with these fields replaced (`JPoints.SiftState.eq_with_of_fields`).

## Main definitions

* `JPoints.wordCols`, `JPoints.CheckGlobals.wordPoints`: the third coordinates of a word and the
  points over the triples of those that a test keeps.
* `JPoints.bitsKeep`, `JPoints.bitsPoints`: the test of `check_bits` and the points of the first
  bits of a word.
* `JPoints.CheckBitsCont`, `JPoints.CheckBitsPost`, `JPoints.CheckBitsInvariant`,
  `JPoints.CheckBitsPre`, `JPoints.CheckPointInvariant`, `JPoints.CheckPointPre`: the invariants and
  the conditions of the loops.

## Main statements

* `JPoints.checkBits_spec`: the bits of a word.
* `JPoints.checkPoint_spec`: the second stage of a word.
* `JPoints.IsStageSetup.getLsbD_sieveTab_eq_admits12`, `JPoints.getLsbD_sieveTab_eq_admits12`: the
  bits of the rows of the sieve tables that the first two stages read.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, each verification condition closed by a lemma stated in its own shape; the structure
literals of the states in the conditions of `JPoints.checkPoint` are reduced by `dsimp only` first.
The word of `check_bits` after `t` shifts is read by its natural number, `nums.toNat / 2 ^ t`, which
is `0` after the last set bit, so that the loop ends after at most 64 steps.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The points of a word -/

/-- The third coordinates `64 i + j`, `j < 64`, of the word of index `i` of a row, in increasing
order. -/
def wordCols (i : ℤ) : List ℤ := (List.range 64).map fun j : ℕ ↦ 64 * i + j

/-- The points over the triples `(a, b, c)` for the third coordinates `c` of the word of index `i`
that `keep` keeps, `c` increasing, as the exact check with the globals `gl` finds them
(`JPoints.CheckGlobals.points`). -/
def CheckGlobals.wordPoints (gl : CheckGlobals) (keep : ℤ → Bool) (a b i : ℤ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  ((wordCols i).filter keep).flatMap fun c ↦ gl.points (a, b, c)

/-- Whether `check_bits` hands the third coordinate `c` of the word `nums` of the row `(a, b)` to
the exact check, for the globals `g` of the sieve: its bit set in `nums`, the triple coprime
(`JPoints.coprimeKeeps`), and the third stage admitting it (`JPoints.stage3Keeps`). -/
def bitsKeep (g : SiftGlobals) (nums : UInt64) (a b : ℤ) (c : ℤ) : Bool :=
  nums.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c && stage3Keeps g a b c

/-- The points that `check_bits` finds in the first `t` bits of the word `nums` of index `i` of the
row `(a, b)`, for the globals `g` of the sieve. -/
def bitsPoints (g : SiftGlobals) (nums : UInt64) (a b i : ℤ) (t : ℕ) : List (ℤ × ℤ × ℤ × ℤ) :=
  (((List.range t).map fun j : ℕ ↦ 64 * i + j).filter (bitsKeep g nums a b)).flatMap
    fun c ↦ g.check.points (a, b, c)

section BitsPoints

variable {g : SiftGlobals} {nums : UInt64} {a b i : ℤ}

@[simp]
theorem bitsPoints_zero : bitsPoints g nums a b i 0 = [] := rfl

theorem bitsPoints_succ (t : ℕ) : bitsPoints g nums a b i (t + 1) = bitsPoints g nums a b i t ++
    if bitsKeep g nums a b (64 * i + t) then g.check.points (a, b, 64 * i + t) else [] := by
  simp only [bitsPoints, List.range_succ, List.map_append, List.map_singleton, List.filter_append,
    List.flatMap_append, List.filter_singleton]
  by_cases hk : bitsKeep g nums a b (64 * i + t) <;> simp [hk]

theorem bitsPoints_succ_of_getLsbD {t : ℕ} (ht : t < 64) (h : nums.toBitVec.getLsbD t = false) :
    bitsPoints g nums a b i (t + 1) = bitsPoints g nums a b i t := by
  rw [bitsPoints_succ, bitsKeep, Int.toNat_mul_add_emod_of_lt (by lia), h]
  simp

/-- Past the last set bit of `nums`, the points of the first `t` bits are those of the whole word.
-/
theorem bitsPoints_eq_wordPoints {t : ℕ} (ht : t ≤ 64) (h0 : nums.toNat / 2 ^ t = 0) :
    bitsPoints g nums a b i t = g.check.wordPoints (bitsKeep g nums a b) a b i := by
  have hlt : nums.toNat < 2 ^ t := by
    rcases Nat.eq_zero_or_pos (2 ^ t) with h | h
    · simp at h
    · exact (Nat.div_eq_zero_iff_lt h).mp h0
  have key (k : ℕ) (hk : t + k ≤ 64) :
      bitsPoints g nums a b i (t + k) = bitsPoints g nums a b i t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← Nat.add_assoc, bitsPoints_succ_of_getLsbD (by lia), ih (by lia)]
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by lia)))
  rw [← key (64 - t) (by lia), Nat.add_sub_cancel' ht]
  rfl

end BitsPoints

theorem bitsPoints_add {g : SiftGlobals} {nums : UInt64} {a b i : ℤ} (t k : ℕ) :
    ∃ R, bitsPoints g nums a b i (t + k) = bitsPoints g nums a b i t ++ R := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ _, by rw [← Nat.add_assoc, bitsPoints_succ, hR, List.append_assoc]⟩

/-! ### The bits of a word -/

/-- The state `s'` of `check_bits` after its first `t` bits, from the state `s`: the fields other
than the data of the third stage, the counters and the output those of `s`, consistent data of the
third stage, and the output with the points of the first `t` bits, none under `-1`. -/
def CheckBitsCont (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64) (a b i : ℤ)
    (s' : SiftState) (t : ℕ) : Prop :=
  (s'.survivors = s.survivors ∧ s'.rowptr = s.rowptr ∧ s'.rowSetup = s.rowSetup ∧
    s'.tube = s.tube ∧ s'.curChunk = s.curChunk) ∧ Row3Cache.WF g sd s'.row3 ∧
    s'.out = s.out.appendPoints g.check (bitsPoints g nums a b i t) ∧
    (g.check.onePoint = true → bitsPoints g nums a b i t = [])

/-- The postcondition of `JPoints.checkBits` for the state `s`, the word `nums` of index `i` of the
row `(a, b)` and the result `r`: the fields of the state other than the data of the third stage, the
counters and the output those of `s`, consistent data of the third stage, the points of the bits of
the word printed (only the first under `-1`), and the flag of a point under `-1`. -/
def CheckBitsPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64) (a b i : ℤ)
    (r : Bool × SiftState) : Prop :=
  r.2 = { s with
      row3 := r.2.row3, numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2,
      numSurv3 := r.2.numSurv3, out := r.2.out } ∧
    Row3Cache.WF g sd r.2.row3 ∧
    r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint (g.check.wordPoints
      (bitsKeep g nums a b) a b i)) ∧
    r.1 = (g.check.onePoint && !(g.check.wordPoints (bitsKeep g nums a b) a b i).isEmpty)

/-- The invariant of the loop of `JPoints.checkBits`, whose state is the result of an early return
and the state of the thread, the word left and the third coordinate: before a return, the word after
`t ≤ 64` shifts, the third coordinate `64 i + t` and the state after the first `t` bits
(`JPoints.CheckBitsCont`), the word `0` at the exit; after it, the postcondition. -/
def CheckBitsInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64)
    (a b i : ℤ) : Std.WP.WhileInvariant (Option (Bool × SiftState) × SiftState × UInt64 × ℤ) Prop :=
  .mk fun exit st ↦ st.1.elim
    ((∃ t : ℕ, t ≤ 64 ∧ st.2.2.2 = 64 * i + t ∧ st.2.2.1.toNat = nums.toNat / 2 ^ t ∧
      CheckBitsCont g sd s nums a b i st.2.1 t) ∧ (exit = true → st.2.2.1 = 0))
    fun r ↦ exit = true ∧ CheckBitsPost g sd s nums a b i r

/-- The precondition of `JPoints.checkBits`. -/
abbrev CheckBitsPre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64) (a b i : ℤ)
    (r0 : ℕ) (res : Array ℕ) : Prop :=
  IsStageSetup g sd ∧ Row3Cache.WF g sd s.row3 ∧ WordResidues g sd r0 res i ∧ 0 ≤ a ∧
    a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
    ∀ c ∈ wordCols i, nums.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height

section CheckBitsLoop

variable {g : SiftGlobals} {sd : SiftData} {s s' : SiftState} {nums w : UInt64} {a b i c : ℤ}
  {r0 : ℕ} {res : Array ℕ} {o : Option (Bool × SiftState)} {mb : ℕ}

private theorem CheckBitsInvariant.cont
    (h : CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) :
    o = none ∧ ∃ t : ℕ, t < 64 ∧ c = 64 * i + t ∧ w.toNat = nums.toNat / 2 ^ t ∧
      CheckBitsCont g sd s nums a b i s' t := by
  obtain _ | r := o
  · obtain ⟨⟨t, ht, hc, hw, hs⟩, -⟩ := h
    refine ⟨rfl, t, ?_, hc, hw, hs⟩
    by_contra! h64
    have : w.toNat = 0 := by
      rw [hw, Nat.div_eq_zero_iff_lt (by positivity)]
      exact lt_of_lt_of_le nums.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by lia))
    exact absurd (UInt64.toNat_inj.mp (this.trans rfl)) (bne_iff_ne.mp hne)
  · exact absurd h.1 Bool.false_ne_true

private theorem checkBitsInvariant_init (hpre : CheckBitsPre g sd s nums a b i r0 res) :
    CheckBitsInvariant g sd s nums a b i false (none, s, nums, i * 2 ^ longShift) :=
  ⟨⟨0, by lia, by simp [longShift]; ring, by simp, ⟨rfl, rfl, rfl, rfl, rfl⟩, hpre.2.1, by simp,
    fun _ ↦ rfl⟩, nofun⟩

private theorem checkBitsInvariant_done
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hz : ¬(w != 0) = true) : CheckBitsInvariant g sd s nums a b i true (none, s', w, c) := by
  obtain ⟨-, h⟩ := h
  obtain _ | r := o
  · exact ⟨h.1, fun _ ↦ by simpa using hz⟩
  · exact absurd h.1 Bool.false_ne_true

private theorem checkBitsInvariant_post_some {x : Bool} {y : SiftState}
    {st : Option (Bool × SiftState)}
    (hi : CheckBitsInvariant g sd s nums a b i true (st, s', w, c)) (hst : st = some (x, y)) :
    CheckBitsPost g sd s nums a b i (x, y) := by
  subst hst
  exact hi.2

private theorem checkBitsInvariant_post_none {st : Option (Bool × SiftState)}
    (hi : CheckBitsInvariant g sd s nums a b i true (st, s', w, c)) (hst : st = none) :
    CheckBitsPost g sd s nums a b i (false, s') := by
  subst hst
  obtain ⟨⟨t, ht, -, hw, hf, hr, hout, h1⟩, hz⟩ := hi
  have hz := hz rfl
  have hb := bitsPoints_eq_wordPoints (g := g) (a := a) (b := b) (i := i) ht
    (by rw [← hw, hz]; rfl)
  refine ⟨SiftState.eq_with_of_fields hf, hr, ?_, ?_⟩ <;> rw [← hb]
  · cases hop : g.check.onePoint
    · simpa [firstIf_false] using hout
    · simpa [h1 hop, firstIf_nil] using hout
  · cases hop : g.check.onePoint
    · simp
    · simp [h1 hop]

private theorem CheckBitsInvariant.yield
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    {s'' : SiftState} (hne : (w != 0) = true)
    (hs : ∀ t : ℕ, t < 64 → c = 64 * i + t → nums.toBitVec.getLsbD t = (w &&& 1 != 0) →
      CheckBitsCont g sd s nums a b i s' t → CheckBitsCont g sd s nums a b i s'' (t + 1)) :
    (w >>> 1).toNat < mb ∧
      CheckBitsInvariant g sd s nums a b i false (none, s'', w >>> 1, c + 1) := by
  obtain ⟨rfl, hi⟩ := h
  obtain ⟨-, t, ht, hc, hw, hs'⟩ := hi.cont hne
  have hw0 : w.toNat ≠ 0 := fun h0 ↦ bne_iff_ne.mp hne (UInt64.toNat_inj.mp h0)
  have e : (w >>> 1).toNat = w.toNat / 2 := by simp [Nat.shiftRight_eq_div_pow]
  refine ⟨by rw [e]; lia, ⟨⟨t + 1, by lia, by rw [hc]; push_cast; ring, ?_,
    hs t ht hc (UInt64.getLsbD_eq_and_one_bne_zero hw) hs'⟩, nofun⟩⟩
  rw [e, hw, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

private theorem checkBitsInvariant_skip
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) (hb : ¬(w &&& 1 != 0) = true) :
    (w >>> 1).toNat < mb ∧
      CheckBitsInvariant g sd s nums a b i false (none, s', w >>> 1, c + 1) :=
  CheckBitsInvariant.yield h hne fun t ht _ hbit ⟨hf, hw, hout, h1⟩ ↦ by
    have hk := bitsPoints_succ_of_getLsbD (g := g) (a := a) (b := b) (i := i) ht
      (by simpa [hb] using hbit)
    exact ⟨hf, hw, hk ▸ hout, hk ▸ h1⟩

private theorem checkBitsInvariant_coprime_false
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) {r : Bool} (hr : r = coprimeKeeps a b c) (hr' : ¬r = true) :
    (w >>> 1).toNat < mb ∧ CheckBitsInvariant g sd s nums a b i false
      (none, { s' with numSurv2 := s'.numSurv2 + 1 }, w >>> 1, c + 1) :=
  CheckBitsInvariant.yield h hne fun t ht hc _ ⟨hf, hw, hout, h1⟩ ↦ by
    have hk : bitsPoints g nums a b i (t + 1) = bitsPoints g nums a b i t := by
      rw [bitsPoints_succ, bitsKeep, ← hc, ← hr]
      simp [hr']
    exact ⟨hf, hw, hk ▸ hout, hk ▸ h1⟩

private theorem checkBitsInvariant_stage3_false
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) {bit : Bool} {row3 : Row3Cache}
    (hbit : bit = stage3Keeps g a b c ∧ Row3Cache.WF g sd row3 ∧ row3.row3A = a ∧ row3.row3B = b)
    (hbit' : ¬bit = true) :
    (w >>> 1).toNat < mb ∧ CheckBitsInvariant g sd s nums a b i false
      (none, { s' with numSurv2 := s'.numSurv2 + 1, row3 := row3 }, w >>> 1, c + 1) :=
  CheckBitsInvariant.yield h hne fun t ht hc _ ⟨hf, _, hout, h1⟩ ↦ by
    have hk : bitsPoints g nums a b i (t + 1) = bitsPoints g nums a b i t := by
      rw [bitsPoints_succ, bitsKeep, ← hc, ← hbit.1]
      simp [hbit']
    exact ⟨hf, hbit.2.1, hk ▸ hout, hk ▸ h1⟩

private theorem bitsPoints_succ_of_keep {t : ℕ} (ht : t < 64) (hc : c = 64 * i + t)
    (hbit : nums.toBitVec.getLsbD t = true) (hr : coprimeKeeps a b c = true)
    (h3 : stage3Keeps g a b c = true) :
    bitsPoints g nums a b i (t + 1) = bitsPoints g nums a b i t ++ g.check.points (a, b, c) := by
  rw [bitsPoints_succ, bitsKeep, Int.toNat_mul_add_emod_of_lt (by lia), hbit, ← hc, hr, h3]
  rfl

private theorem checkBitsInvariant_point
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) (hb : (w &&& 1 != 0) = true)
    {r : Bool} (hr : r = coprimeKeeps a b c) (hr' : r = true) {bit : Bool} {row3 : Row3Cache}
    (hbit : bit = stage3Keeps g a b c ∧ Row3Cache.WF g sd row3 ∧ row3.row3A = a ∧ row3.row3B = b)
    (hbit' : bit = true) {found : Bool} {out : Output}
    (hout : out = s'.out.appendPoints g.check
      (firstIf g.check.onePoint (g.check.points (a, b, c))) ∧
      (g.check.onePoint = true → (found = true ↔ g.check.points (a, b, c) ≠ [])))
    (hf : ¬(found && g.check.onePoint) = true) :
    (w >>> 1).toNat < mb ∧ CheckBitsInvariant g sd s nums a b i false
      (none, { s' with
          numSurv2 := s'.numSurv2 + 1, row3 := row3, numSurv3 := s'.numSurv3 + 1, out := out },
        w >>> 1, c + 1) :=
  CheckBitsInvariant.yield h hne fun t ht hc hbt ⟨hf', _, hout', h1⟩ ↦ by
    rw [hb] at hbt
    have hk := bitsPoints_succ_of_keep ht hc hbt (hr ▸ hr') (hbit.1 ▸ hbit')
    have hP : g.check.onePoint = true → g.check.points (a, b, c) = [] := fun hop ↦ by
      have := hout.2 hop
      simp_all
    refine ⟨hf', hbit.2.1, ?_, fun hop ↦ by rw [hk, h1 hop, hP hop, List.append_nil]⟩
    simp only [hout.1, hout', Output.appendPoints_appendPoints, hk]
    cases hop : g.check.onePoint
    · rfl
    · rw [hP hop, firstIf_nil]

private theorem checkBitsInvariant_return
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) (hb : (w &&& 1 != 0) = true)
    {r : Bool} (hr : r = coprimeKeeps a b c) (hr' : r = true) {bit : Bool} {row3 : Row3Cache}
    (hbit : bit = stage3Keeps g a b c ∧ Row3Cache.WF g sd row3 ∧ row3.row3A = a ∧ row3.row3B = b)
    (hbit' : bit = true) {found : Bool} {out : Output}
    (hout : out = s'.out.appendPoints g.check
      (firstIf g.check.onePoint (g.check.points (a, b, c))) ∧
      (g.check.onePoint = true → (found = true ↔ g.check.points (a, b, c) ≠ [])))
    (hf : (found && g.check.onePoint) = true) :
    CheckBitsInvariant g sd s nums a b i true
      (some (true, { s' with
          numSurv2 := s'.numSurv2 + 1, row3 := row3, numSurv3 := s'.numSurv3 + 1, out := out }),
        { s' with
          numSurv2 := s'.numSurv2 + 1, row3 := row3, numSurv3 := s'.numSurv3 + 1, out := out },
        w, c) := by
  obtain ⟨-, hi⟩ := h
  obtain ⟨-, t, ht, hc, hw, hf', -, hout', h1⟩ := hi.cont hne
  have hbt := UInt64.getLsbD_eq_and_one_bne_zero hw
  rw [hb] at hbt
  have hop : g.check.onePoint = true := by simp_all
  have hP : g.check.points (a, b, c) ≠ [] := (hout.2 hop).mp (by simp_all)
  have hk := bitsPoints_succ_of_keep (g := g) ht hc hbt (hr ▸ hr') (hbit.1 ▸ hbit')
  obtain ⟨R, hR⟩ := bitsPoints_add (g := g) (nums := nums) (a := a) (b := b) (i := i) (t + 1)
    (64 - (t + 1))
  rw [Nat.add_sub_cancel' (by lia)] at hR
  have hW : g.check.wordPoints (bitsKeep g nums a b) a b i = g.check.points (a, b, c) ++ R := by
    rw [show g.check.wordPoints (bitsKeep g nums a b) a b i = bitsPoints g nums a b i 64 from rfl,
      hR, hk, h1 hop, List.nil_append]
  refine ⟨rfl, SiftState.eq_with_of_fields hf', hbit.2.1, ?_, ?_⟩
  · rw [hout.1, hout', h1 hop, hW, hop, firstIf_true, firstIf_true, List.take_append_of_le_length
      (List.length_pos_iff.mpr hP), Output.appendPoints_appendPoints, List.nil_append]
  · simp [hop, hW, hP]

private theorem checkBitsPre_nonneg (hpre : CheckBitsPre g sd s nums a b i r0 res) : 0 ≤ a := by
  obtain ⟨-, -, -, ha, -⟩ := hpre
  exact ha

private theorem checkBitsPre_checkBit (hpre : CheckBitsPre g sd s nums a b i r0 res)
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) :
    IsStageSetup g sd ∧ Row3Cache.WF g sd s'.row3 ∧ WordResidues g sd r0 res (c / 64) ∧ 0 ≤ a := by
  obtain ⟨-, t, ht, hc, -, -, hw, -⟩ := h.2.cont hne
  obtain ⟨hs, -, hres, ha, -⟩ := hpre
  refine ⟨hs, hw, ?_, ha⟩
  rwa [hc, show (64 * i + t) / 64 = i by lia]

private theorem checkBitsPre_checkOnePoint (hpre : CheckBitsPre g sd s nums a b i r0 res)
    (h : w.toNat = mb ∧ CheckBitsInvariant g sd s nums a b i false (o, s', w, c))
    (hne : (w != 0) = true) (hb : (w &&& 1 != 0) = true) {r : Bool} (hr : r = coprimeKeeps a b c)
    (hr' : r = true) :
    g.check.WF ∧ (a, b, c) ∈ boxTriples g.check.height.toNat := by
  obtain ⟨-, t, ht, hc, hw, -⟩ := h.2.cont hne
  obtain ⟨hs, -, -, ha, haH, hbH, ha0, hbits⟩ := hpre
  have hbt := UInt64.getLsbD_eq_and_one_bne_zero hw
  rw [hb] at hbt
  have hcH := hbits c (by rw [hc]; exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    (by rw [hc, Int.toNat_mul_add_emod_of_lt (by lia), hbt])
  have hH := hs.check.one_le_height
  have hHn := Int.toNat_of_nonneg (show 0 ≤ g.check.height by lia)
  have hcop : coprimeKeeps a b c = true := hr ▸ hr'
  refine ⟨hs.check, mem_boxTriples_iff.mpr ⟨of_decide_eq_true hcop, ?_, ?_, by lia, by lia⟩⟩
  · rcases eq_or_lt_of_le ha with h0 | h0
    · exact .inr ⟨h0.symm, .inl (by lia [ha0 h0.symm])⟩
    · exact .inl h0
  · rw [abs_of_nonneg ha]
    lia

end CheckBitsLoop

/-- `check_bits` prints the points over the triples `(a, b, c)` of the bits `c` of the word `nums`
of index `i` of the row `(a, b)` that are coprime and that the third stage admits
(`JPoints.coprimeKeeps`, `JPoints.stage3Keeps`), `c` increasing, only the first under `-1`, for
`0 ≤ a ≤ H`, `|b| ≤ H`, `b ≥ 1` for `a = 0`, the bits of `nums` within the height bound and the
residues of the word: the bits taken from the lowest, each coprime one tested by the third stage
(`JPoints.checkBit_spec`) and checked exactly (`JPoints.checkOnePoint_spec`). It keeps the data of
the third stage consistent and changes no other field of the state but the counters and the output.
The flag returned says whether it stopped at a point under `-1`. -/
@[spec]
theorem checkBits_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64)
    (a b i : ℤ) (r0 : ℕ) (res : Array ℕ) :
    ⦃ IsStageSetup g sd ∧ Row3Cache.WF g sd s.row3 ∧ WordResidues g sd r0 res i ∧ 0 ≤ a ∧
      a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
      ∀ c ∈ wordCols i, nums.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height ⦄
    checkBits g sd s nums a b i r0 res
    ⦃ fun r ↦ r.2 = { s with
          row3 := r.2.row3, numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2,
          numSurv3 := r.2.numSurv3, out := r.2.out } ∧
        Row3Cache.WF g sd r.2.row3 ∧
        r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint (g.check.wordPoints
          (fun c ↦ nums.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c &&
            stage3Keeps g a b c) a b i)) ∧
        r.1 = (g.check.onePoint && !(g.check.wordPoints (fun c ↦
          nums.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c && stage3Keeps g a b c)
            a b i).isEmpty) ⦄ := by
  vcgen [checkBits] invariants
  · CheckBitsInvariant g sd s nums a b i
  · Std.WP.Variant.ofMeasure fun st : Option (Bool × SiftState) × SiftState × UInt64 × ℤ ↦
      st.2.2.1.toNat
  all_goals try vc_simp
  all_goals first
    | exact checkBitsInvariant_init ‹_›
    | exact checkBitsInvariant_post_some ‹_› ‹_›
    | exact checkBitsInvariant_post_none ‹_› ‹_›
    | exact checkBitsPre_nonneg ‹_›
    | exact checkBitsPre_checkBit ‹_› ‹_› ‹_›
    | exact checkBitsPre_checkOnePoint ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_return ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_point ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_stage3_false ‹_› ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_coprime_false ‹_› ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_skip ‹_› ‹_› ‹_›
    | exact checkBitsInvariant_done ‹_› ‹_›

/-! ### The second stage of a word -/

/-- The invariant of the loop of `JPoints.checkPoint` over the second-stage primes, with its `break`
at the word `0`: the bits of the word left are those of `nums` that the sieve tables of the primes
below the cursor admit (`JPoints.CurveTables.admits12`). -/
def CheckPointInvariant (g : SiftGlobals) (nums : UInt64) (a b i : ℤ) :
    Std.WP.Invariant ℕ UInt64 Prop :=
  fun pref _ w ↦ ∀ j, w.toBitVec.getLsbD j = (nums.toBitVec.getLsbD j &&
    pref.all fun n ↦ g.curve.admits12 g.pnn[n]! a b (64 * i + j))

/-- The precondition of `JPoints.checkPoint`. -/
abbrev CheckPointPre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64)
    (a b i : ℤ) (k : ℕ) (res : Array ℕ) : Prop :=
  IsStageSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧
    s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧ WordResidues g sd (k * sd.npr) res i ∧
    0 ≤ a ∧ a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
    ∀ c ∈ wordCols i, nums.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height

section CheckPointLoop

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {nums w : UInt64} {a b i : ℤ} {k : ℕ}
  {res : Array ℕ} {pref suff : List ℕ} {cur : ℕ}

private theorem checkPointInvariant_nil {l : List ℕ} : CheckPointInvariant g nums a b i [] l nums :=
  fun _ ↦ by simp

private theorem checkPointInvariant_break
    (hc : ForIn.toList [g.sievePrimes1:g.sievePrimes2] = pref ++ cur :: suff)
    (hi : CheckPointInvariant g nums a b i pref (cur :: suff) w) (hw : (w == 0) = true) :
    CheckPointInvariant g nums a b i (ForIn.toList [g.sievePrimes1:g.sievePrimes2]) [] w := by
  intro j
  have h := hi j
  rw [beq_iff_eq.mp hw] at h ⊢
  rw [hc, List.all_append]
  simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero] at h ⊢
  cases hn : nums.toBitVec.getLsbD j <;> simp_all

/-- The bit `j` of the word of the row of `(a, b)` of the sieve table of the `n`-th prime `p` of the
first two stages at the residue of the word `i` of a row is the class test at `(a, b, 64 i + j)`. -/
theorem IsStageSetup.getLsbD_sieveTab_eq_admits12 {g : SiftGlobals} {sd : SiftData}
    (h : IsStageSetup g sd) {rowptr : Array ℕ} {c : RowSetupCache}
    (hw : RowSetupCache.WF g sd rowptr c) {a b : ℤ} (hA : c.lastA = a) (hB : c.lastB = b)
    (ha : 0 ≤ a) {n : ℕ} (hn : n < g.sievePrimes2) (i : ℤ) {j : ℕ} (hj : j < 64) :
    ((g.sieve.sieveTab[n]!)[rowptr[n]! + (i % sd.pr[n]!).toNat]!).toBitVec.getLsbD j =
      g.curve.admits12 g.pnn[n]! a b (64 * i + j) := by
  have hn3 := h.lt_sievePrimes3 hn
  have hp := h.three_le_pr hn3
  have hP := h.pr_eq hn3
  rw [hw.rowptr_eq (hA ▸ ha) hn, hw.bres_eq (hA ▸ ha) hn, hA, hB, h.siftData.pr_eq hn3,
    h.sieve.getLsbD_eq_admits12 hn (Int.toNat_emod_lt a (by lia)) (Int.toNat_emod_lt b (by lia))
      (Int.toNat_emod_lt i (by lia)).le hj]
  have hP0 : (0 : ℤ) ≠ (sievingPrime g.pnn n : ℕ) := by lia
  refine CurveTables.admits12_congr ?_ ?_ ?_ <;> push_cast <;>
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hP0.symm)]
  · exact Int.emod_emod ..
  · exact Int.emod_emod ..
  · exact ((Int.mod_modEq i _).mul_left 64).add_right _

/-- The bit `j` of the word `r < p` of the row of `(a, b)` of the sieve table of the `n`-th prime
`p` of the first two stages is the class test at `(a, b, 64 i + j)` for `r = i mod p`. -/
theorem getLsbD_sieveTab_eq_admits12 (hpre : CheckPointPre g sd s nums a b i k res) {n : ℕ}
    (hn : n < g.sievePrimes2) (j : ℕ) :
    ((g.sieve.sieveTab[n]!)[s.rowptr[n]! + (sd.res0[k * sd.npr + n]! + res[n]!) %
      sd.pr[n]!]!).toBitVec.getLsbD j =
      (decide (j < 64) && g.curve.admits12 g.pnn[n]! a b (64 * i + j)) := by
  obtain ⟨h, hw, hA, hB, -, hres, ha, -⟩ := hpre
  rw [(hres n (h.lt_sievePrimes3 hn)).2.2]
  rcases lt_or_ge j 64 with hj | hj
  · rw [h.getLsbD_sieveTab_eq_admits12 hw hA hB ha hn i hj, decide_eq_true hj, Bool.true_and]
  · rw [BitVec.getLsbD_of_ge _ _ hj, decide_eq_false (by lia), Bool.false_and]

private theorem checkPointInvariant_step (hpre : CheckPointPre g sd s nums a b i k res)
    (hc : ForIn.toList [g.sievePrimes1:g.sievePrimes2] = pref ++ cur :: suff)
    (hi : CheckPointInvariant g nums a b i pref (cur :: suff) w) {r : ℕ}
    (hr : r = (sd.res0[k * sd.npr + cur]! + res[cur]!) % sd.pr[cur]!) :
    CheckPointInvariant g nums a b i (pref ++ [cur]) suff
      (w &&& (g.sieve.sieveTab[cur]!)[s.rowptr[cur]! + r]!) := by
  have hcur : cur < g.sievePrimes2 := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  intro j
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, hi j, hr, getLsbD_sieveTab_eq_admits12 hpre hcur j,
    List.all_append]
  rcases lt_or_ge j 64 with hj | hj
  · simp [hj, Bool.and_assoc]
  · simp [BitVec.getLsbD_of_ge _ _ hj]

private theorem residue2_eq_sub_of_le (hpre : CheckPointPre g sd s nums a b i k res)
    (hc : ForIn.toList [g.sievePrimes1:g.sievePrimes2] = pref ++ cur :: suff)
    (hle : sd.pr[cur]! ≤ sd.res0[k * sd.npr + cur]! + res[cur]!) :
    sd.res0[k * sd.npr + cur]! + res[cur]! - sd.pr[cur]! =
      (sd.res0[k * sd.npr + cur]! + res[cur]!) % sd.pr[cur]! := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  obtain ⟨hs, -, -, -, -, hres, -⟩ := hpre
  have := hres cur (hs.lt_sievePrimes3 hcur)
  rw [Nat.mod_eq_ite_of_lt_two_mul (by lia)]
  simp [hle]

private theorem CheckPointInvariant.wordPoints_eq
    (hi : CheckPointInvariant g nums a b i (ForIn.toList [g.sievePrimes1:g.sievePrimes2]) [] w) :
    g.check.wordPoints (fun c ↦ w.toBitVec.getLsbD (c % 64).toNat && coprimeKeeps a b c &&
      stage3Keeps g a b c) a b i =
    g.check.wordPoints (fun c ↦ nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c &&
      coprimeKeeps a b c && stage3Keeps g a b c) a b i := by
  simp only [CheckGlobals.wordPoints]
  congr 1
  refine List.filter_congr fun c hc ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  rw [Int.toNat_mul_add_emod_of_lt (by lia [List.mem_range.mp hj]), hi j,
    Std.Legacy.Range.toList_eq_range', stage2Keeps]

private theorem CheckPointInvariant.wordPoints_eq_nil
    (hi : CheckPointInvariant g nums a b i (ForIn.toList [g.sievePrimes1:g.sievePrimes2]) [] w)
    (hw : ¬(w != 0) = true) :
    g.check.wordPoints (fun c ↦ nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c &&
      coprimeKeeps a b c && stage3Keeps g a b c) a b i = [] := by
  rw [← hi.wordPoints_eq, show w = 0 by simpa using hw]
  simp [CheckGlobals.wordPoints]

private theorem checkPoint_checkBits_pre (hpre : CheckPointPre g sd s nums a b i k res)
    (hi : CheckPointInvariant g nums a b i (ForIn.toList [g.sievePrimes1:g.sievePrimes2]) [] w) :
    CheckBitsPre g sd s w a b i (k * sd.npr) res := by
  obtain ⟨h, -, -, -, h3, hres, ha, haH, hbH, ha0, hbits⟩ := hpre
  refine ⟨h, h3, hres, ha, haH, hbH, ha0, fun c hc hw ↦ hbits c hc ?_⟩
  rw [hi] at hw
  exact (Bool.and_eq_true _ _).mp hw |>.1

private theorem CheckPointPre.row3 (hpre : CheckPointPre g sd s nums a b i k res) :
    Row3Cache.WF g sd s.row3 := by
  obtain ⟨-, -, -, -, h3, -⟩ := hpre
  exact h3

end CheckPointLoop

/-- `check_point` prints the points over the triples `(a, b, c)` of the bits `c` of the word `nums`
of index `i` of the row `(a, b)` that the second stage, the test of coprimality and the third stage
admit (`JPoints.stage2Keeps`, `JPoints.coprimeKeeps`, `JPoints.stage3Keeps`), `c` increasing, only
the first under `-1`, for `0 ≤ a ≤ H`, `|b| ≤ H`, `b ≥ 1` for `a = 0`, the bits of `nums` within the
height bound, the rows of the sieve tables of `row_setup` for the row (`JPoints.RowSetupCache.WF`)
and the residues of the word at the position `k`: the word and-ed with the word of the row of each
second-stage prime at the residue of `i` (`JPoints.getLsbD_sieveTab_eq_admits12`), and its bits left
handed to `check_bits` (`JPoints.checkBits_spec`). It keeps the data of the third stage consistent
and changes no other field of the state but the counters and the output. The flag returned says
whether it stopped at a point under `-1`. -/
@[spec]
theorem checkPoint_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (nums : UInt64)
    (a b i : ℤ) (k : ℕ) (res : Array ℕ) :
    ⦃ IsStageSetup g sd ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧ s.rowSetup.lastA = a ∧
      s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧ WordResidues g sd (k * sd.npr) res i ∧
      0 ≤ a ∧ a ≤ g.check.height ∧ |b| ≤ g.check.height ∧ (a = 0 → 1 ≤ b) ∧
      ∀ c ∈ wordCols i, nums.toBitVec.getLsbD (c % 64).toNat = true → |c| ≤ g.check.height ⦄
    checkPoint g sd s nums a b i k res
    ⦃ fun r ↦ r.2 = { s with
          row3 := r.2.row3, numSurv1 := r.2.numSurv1, numSurv2 := r.2.numSurv2,
          numSurv3 := r.2.numSurv3, out := r.2.out } ∧
        Row3Cache.WF g sd r.2.row3 ∧
        r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint (g.check.wordPoints
          (fun c ↦ nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c &&
            coprimeKeeps a b c && stage3Keeps g a b c) a b i)) ∧
        r.1 = (g.check.onePoint && !(g.check.wordPoints (fun c ↦
          nums.toBitVec.getLsbD (c % 64).toNat && stage2Keeps g a b c && coprimeKeeps a b c &&
            stage3Keeps g a b c) a b i).isEmpty) ⦄ := by
  vcgen [checkPoint] invariants
  · CheckPointInvariant g nums a b i
  all_goals try dsimp only at *
  all_goals first
    | exact checkPointInvariant_nil
    | exact checkPoint_checkBits_pre ‹_› ‹_›
    | rwa [← CheckPointInvariant.wordPoints_eq ‹_›]
    | (rw [CheckPointInvariant.wordPoints_eq_nil ‹_› ‹_›]; simpa using CheckPointPre.row3 ‹_›)
    | exact checkPointInvariant_break ‹_› ‹_› ‹_›
    | exact checkPointInvariant_step ‹_› ‹_› ‹_› (residue2_eq_sub_of_le ‹_› ‹_› ‹_›)
    | exact checkPointInvariant_step ‹_› ‹_› ‹_› (Nat.mod_eq_of_lt (Nat.lt_of_not_le ‹_›)).symm

end JPoints

end
