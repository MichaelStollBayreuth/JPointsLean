/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Scan

import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.DoubleArith
import JPoints.Proof.RowSetup
import Mathlib.Data.Int.ModEq
import Std.Tactic.Do

/-!
# The first stage of the sieve and the sieve of a row in the box

The contracts of the walks of the first stage and of the sieve of a row of the box. A walk of a
first-stage prime (`WALK`, `JPoints.walk_spec`) sets each word of its range of the bit array to an
operation of its old value and of the word of the row of the sieve table at the residue of the word,
when the walk is well formed (`JPoints.WalkSpec.WF`) as `init_sift` (`JPoints.initSiftWalk_isWalk`)
and `walk_parts` (`JPoints.walkParts_spec`) make it. The sieve of a chunk (`sift0`,
`JPoints.sift0_spec`) leaves in its bit array the bits of the mask of the row, of the first stage,
of the words of the row and off the excluded third coordinate, and prints the points that the scan
of its words finds, those of the row in the words of the chunk (`JPoints.rowRangePoints`); and
`sift` (`JPoints.sift_spec`) prints those of the whole row (`JPoints.rowPoints`), chunk after
chunk, only the first under `-1`, keeping the state of the thread consistent
(`JPoints.SiftState.WF`).

## Main definitions

* `JPoints.WalkWordsInvariant`, `JPoints.WalkInvariant`: the invariants of the loops of a walk.
* `JPoints.WalkSpec.WF`, `JPoints.WalkSpec.IsWalk`: a walk as `init_sift` and `walk_parts` make it.
* `JPoints.tabBits`: the bits of the rows of the sieve tables of first-stage primes for a word.
* `JPoints.FillInvariant`, `JPoints.WalksInvariant`, `JPoints.FillPost`: the fill of the bit array
  and the walks over it.
* `JPoints.ChunkWalks`: the walks of a chunk.
* `JPoints.Sift0Pre`, `JPoints.SiftPost`: the condition and the postcondition of the sieve of a
  chunk.
* `JPoints.SiftCont`, `JPoints.SiftInvariant`: the invariant of the loop of `sift` over the chunks.

## Main statements

* `JPoints.walkWords_spec`, `JPoints.walk_spec`: a walk.
* `JPoints.WalkSpec.isWalk_of_head_eq_min`, `JPoints.initSiftWalk_isWalk`,
  `JPoints.walkParts_spec`: a walk by its certificates, and the walks of `init_sift` and of
  `walk_parts`.
* `JPoints.sift0Fill_spec`, `JPoints.sift0Masks_spec`, `JPoints.sift0_spec`,
  `JPoints.SiftPost.of_scanPost`: the sieve of a chunk.
* `JPoints.sift_spec`: the sieve of a row in the box.
* `JPoints.IsStageSetup.chunkWalks`, `JPoints.IsStageSetup.range_chunk_lt`,
  `JPoints.IsRowSetup.rangeKeeps_chunk`, `JPoints.IsRowSetup.rowRangePoints_eq_chunk`: the chunks of
  a row.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, proved by `vcgen` with named
invariants, each verification condition closed by a lemma stated in its own shape, the invariants
irreducible in the proofs of the contracts. A walk reads the word `(first + t) mod p` of the row of
the sieve table for its word `t`, whatever its head, full periods and tail; the bits of the rows of
the sieve tables are the class tests of the tables of the curve by `JPoints.SieveTables.WF`. The
words of a chunk are positions in the bit array; the chunk `k` covers the words
`min (w_low_all + k array_size, w_high_all)` up to the next, so that the chunks cover the row in
order (`JPoints.IsRowSetup.rowRangePoints_chunk_succ`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The walk -/

/-- The invariant of the loop of `JPoints.walkWords` from the bit array `survivors`, its word `surv`
and the word `siv1` of the table `tab` on, with the operation `op`: the size of the bit array kept,
both indices moved on by the words done, the words done set to `op` of their old values and of the
words of the table, and the other words unchanged. -/
def WalkWordsInvariant (tab survivors : Array UInt64) (surv siv1 : ℕ)
    (op : UInt64 → UInt64 → UInt64) : Std.WP.Invariant ℕ (Array UInt64 × ℕ × ℕ) Prop :=
  fun pref _ st ↦ st.1.size = survivors.size ∧ st.2.1 = surv + pref.length ∧
    st.2.2 = siv1 + pref.length ∧
    (∀ u < pref.length, st.1[surv + u]! = op survivors[surv + u]! tab[siv1 + u]!) ∧
    ∀ m, (m < surv ∨ surv + pref.length ≤ m) → st.1[m]! = survivors[m]!

section WalkWords

variable {tab survivors : Array UInt64} {surv siv1 cnt : ℕ} {op : UInt64 → UInt64 → UInt64}

private theorem walkWordsInvariant_nil {l : List ℕ} :
    WalkWordsInvariant tab survivors surv siv1 op [] l (survivors, surv, siv1) :=
  ⟨rfl, rfl, rfl, nofun, fun _ _ ↦ rfl⟩

private theorem walkWordsInvariant_post {sv : Array UInt64} {su si : ℕ}
    (h : WalkWordsInvariant tab survivors surv siv1 op (ForIn.toList [:cnt]) [] (sv, su, si)) :
    sv.size = survivors.size ∧ su = surv + cnt ∧ si = siv1 + cnt ∧
      (∀ u < cnt, sv[surv + u]! = op survivors[surv + u]! tab[siv1 + u]!) ∧
      ∀ m, (m < surv ∨ surv + cnt ≤ m) → sv[m]! = survivors[m]! := by
  simpa only [WalkWordsInvariant, Std.Legacy.Range.length_toList_zero_start] using h

private theorem walkWordsInvariant_step {pref suff : List ℕ} {cur : ℕ} {sv : Array UInt64}
    {su si : ℕ} (hcnt : surv + cnt ≤ survivors.size)
    (hc : ForIn.toList [:cnt] = pref ++ cur :: suff)
    (h : WalkWordsInvariant tab survivors surv siv1 op pref (cur :: suff) (sv, su, si)) :
    WalkWordsInvariant tab survivors surv siv1 op (pref ++ [cur]) suff
      (sv.set! su (op sv[su]! tab[si]!), su + 1, si + 1) := by
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := h
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  simp only [WalkWordsInvariant, List.length_append, List.length_singleton]
  refine ⟨by simp [h1], by lia, by lia, fun u hu ↦ ?_, fun m hm ↦ ?_⟩
  · rw [Array.getElem!_set! (by lia)]
    split_ifs with hu'
    · obtain rfl : u = pref.length := by lia
      rw [← hu', h5 _ (by lia)]
    · exact h4 u (by lia)
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h5 m (by lia)

end WalkWords

attribute [local irreducible] WalkWordsInvariant in
/-- The `cnt` steps of a loop of `WALK` set the words `surv + u` of the bit array to `op` of their
old values and of the words `siv1 + u` of the table, leave the other words alone, and move both
indices on by `cnt`, within the bit array. -/
@[spec]
theorem walkWords_spec (tab survivors : Array UInt64) (surv siv1 cnt : ℕ)
    (op : UInt64 → UInt64 → UInt64) :
    ⦃ surv + cnt ≤ survivors.size ⦄
    walkWords tab survivors surv siv1 cnt op
    ⦃ fun r ↦ r.1.size = survivors.size ∧ r.2.1 = surv + cnt ∧ r.2.2 = siv1 + cnt ∧
        (∀ u < cnt, r.1[surv + u]! = op survivors[surv + u]! tab[siv1 + u]!) ∧
        ∀ m, (m < surv ∨ surv + cnt ≤ m) → r.1[m]! = survivors[m]! ⦄ := by
  vcgen [walkWords] invariants
  · WalkWordsInvariant tab survivors surv siv1 op
  all_goals with_reducible first
    | exact walkWordsInvariant_nil
    | exact walkWordsInvariant_post ‹_›
    | exact walkWordsInvariant_step ‹_› ‹_› ‹_›

/-- A walk `w` of the prime `p` as `init_sift` and `walk_parts` make it: its first word `first` in
`[1, p]`, its head not beyond the end of the period of the row, its tail shorter than a period, and
the head up to the end of the period when full periods or a tail follow, so that word `t` of the
walk reads word `(first + t) mod p` of the row (`JPoints.walk_spec`). -/
structure WalkSpec.WF (w : WalkSpec) (p : ℕ) : Prop where
  /-- The first word is in `[1, p]`. -/
  first_pos : 0 < w.first
  /-- The head ends at the end of the period of the row at the latest. -/
  first_add_head_le : w.first + w.head ≤ p
  /-- The tail is shorter than a period. -/
  tail_lt : w.tail < p
  /-- Full periods and a tail follow a head up to the end of the period of the row. -/
  first_add_head_eq : w.nper ≠ 0 ∨ w.tail ≠ 0 → w.first + w.head = p

/-- The invariant of the loop of `JPoints.walk` over the full periods of the walk `w` of the prime
`p`, from the bit array `sv`, for the row from the index `r0` of the table `tab` and the words from
`surv0` on: the size kept, the index into the bit array after the head and the periods done, the
index `r0 + first + head` into the table, the words of the head and of the periods done set to `op`
of their old values and of the words `(first + t) mod p` of the row, and the other words
unchanged. -/
def WalkInvariant (tab sv : Array UInt64) (r0 surv0 p : ℕ) (w : WalkSpec)
    (op : UInt64 → UInt64 → UInt64) : Std.WP.Invariant ℕ (Array UInt64 × ℕ × ℕ) Prop :=
  fun pref _ st ↦ st.1.size = sv.size ∧ st.2.1 = surv0 + (w.head + pref.length * p) ∧
    st.2.2 = r0 + w.first + w.head ∧
    (∀ t < w.head + pref.length * p,
      st.1[surv0 + t]! = op sv[surv0 + t]! tab[r0 + (w.first + t) % p]!) ∧
    ∀ m, (m < surv0 ∨ surv0 + (w.head + pref.length * p) ≤ m) → st.1[m]! = sv[m]!

section Walk

variable {tab sv S : Array UInt64} {r0 surv0 p : ℕ} {w : WalkSpec} {op : UInt64 → UInt64 → UInt64}
  {surv siv1 : ℕ}

private theorem walkInvariant_init
    (hpre : w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size)
    (hS : S.size = sv.size ∧ surv = surv0 + w.head ∧ siv1 = r0 + w.first + w.head ∧
      (∀ u < w.head, S[surv0 + u]! = op sv[surv0 + u]! tab[r0 + w.first + u]!) ∧
      ∀ m, m < surv0 ∨ surv0 + w.head ≤ m → S[m]! = sv[m]!) {l : List ℕ} :
    WalkInvariant tab sv r0 surv0 p w op [] l (S, surv, siv1) := by
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hS
  refine ⟨h1, by simp, rfl, fun t ht ↦ ?_, fun m hm ↦ h5 m (by simpa using hm)⟩
  simp only [List.length_nil, Nat.zero_mul, Nat.add_zero] at ht
  rw [h4 t ht, Nat.mod_eq_of_lt (by lia [hpre.1.first_add_head_le]), Nat.add_assoc]

/-- The postcondition of `JPoints.walkWords` from the bit array `S` and the indices `su` and `si`
over `cnt` words, for the result `(T, su', si')`. -/
private abbrev WalkWordsPost (tab S : Array UInt64) (su si cnt : ℕ) (op : UInt64 → UInt64 → UInt64)
    (T : Array UInt64) (su' si' : ℕ) : Prop :=
  T.size = S.size ∧ su' = su + cnt ∧ si' = si + cnt ∧
    (∀ u < cnt, T[su + u]! = op S[su + u]! tab[si + u]!) ∧
    ∀ m, (m < su ∨ su + cnt ≤ m) → T[m]! = S[m]!

-- The words of a walk after `k ≤ p` more words read from the start of the row on: from the `N`
-- words read up to the end of a period, `(f + N) mod p = 0`, set by `op` to the words
-- `(f + t) mod p` of the row and the other words unchanged, and the `k` words from `surv0 + N` on
-- set by `op` to the words of the row from `r0` on.
private theorem walkWords_extend {T : Array UInt64} {f N k : ℕ} (hN : (f + N) % p = 0)
    (hk : k ≤ p) (h4 : ∀ t < N, S[surv0 + t]! = op sv[surv0 + t]! tab[r0 + (f + t) % p]!)
    (h5 : ∀ m, (m < surv0 ∨ surv0 + N ≤ m) → S[m]! = sv[m]!)
    (g4 : ∀ u < k, T[surv0 + N + u]! = op S[surv0 + N + u]! tab[r0 + u]!)
    (g5 : ∀ m, (m < surv0 + N ∨ surv0 + N + k ≤ m) → T[m]! = S[m]!) :
    (∀ t < N + k, T[surv0 + t]! = op sv[surv0 + t]! tab[r0 + (f + t) % p]!) ∧
      ∀ m, (m < surv0 ∨ surv0 + (N + k) ≤ m) → T[m]! = sv[m]! := by
  refine ⟨fun t ht ↦ ?_, fun m hm ↦ ?_⟩
  · by_cases htl : t < N
    · rw [g5 _ (by lia), h4 t htl]
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt htl)
      rw [← Nat.add_assoc f, Nat.add_mod, hN, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by lia), ← Nat.add_assoc, g4 u (by lia), h5 _ (by lia)]
  · rw [g5 m (by lia), h5 m (by lia)]

-- A walk reads `(f + h + q p) mod p = 0` after its head and full periods, for `f + h = p`.
private theorem add_add_mul_mod_eq_zero {f h q : ℕ} (hfh : f + h = p) :
    (f + (h + q * p)) % p = 0 := by
  rw [← Nat.add_assoc, hfh, Nat.add_mul_mod_self_right, Nat.mod_self]

private theorem walkInvariant_tail_pre
    (hpre : w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size)
    (hi : WalkInvariant tab sv r0 surv0 p w op (ForIn.toList [:w.nper]) [] (S, surv, siv1)) :
    surv + w.tail ≤ S.size := by
  obtain ⟨h1, h2, -⟩ := hi
  simp only [Std.Legacy.Range.length_toList_zero_start] at h2
  lia

private theorem walkInvariant_step_pre
    (hpre : w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size) {pref suff : List ℕ}
    {cur : ℕ} (hc : ForIn.toList [:w.nper] = pref ++ cur :: suff)
    (hi : WalkInvariant tab sv r0 surv0 p w op pref (cur :: suff) (S, surv, siv1)) :
    surv + p ≤ S.size := by
  obtain ⟨h1, h2, -⟩ := hi
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have : (pref.length + 1) * p ≤ w.nper * p := Nat.mul_le_mul_right p (by lia)
  lia [Nat.add_mul pref.length 1 p]

private theorem walkInvariant_post
    (hi : WalkInvariant tab sv r0 surv0 p w op (ForIn.toList [:w.nper]) [] (S, surv, siv1))
    (ht : ¬(w.tail != 0) = true) :
    S.size = sv.size ∧
      (∀ t < w.head + w.nper * p + w.tail,
        S[surv0 + t]! = op sv[surv0 + t]! tab[r0 + (w.first + t) % p]!) ∧
      ∀ m, (m < surv0 ∨ surv0 + (w.head + w.nper * p + w.tail) ≤ m) → S[m]! = sv[m]! := by
  obtain ⟨h1, -, -, h4, h5⟩ := hi
  simp only [Std.Legacy.Range.length_toList_zero_start] at h4 h5
  simp only [bne_iff_ne, ne_eq, not_not] at ht
  simpa [ht] using ⟨h1, h4, h5⟩

private theorem walkInvariant_post_tail {T : Array UInt64} {surv' siv1' : ℕ}
    (hpre : w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size)
    (hi : WalkInvariant tab sv r0 surv0 p w op (ForIn.toList [:w.nper]) [] (S, surv, siv1))
    (ht : (w.tail != 0) = true)
    (hT : WalkWordsPost tab S surv (siv1 - p) w.tail op T surv' siv1') :
    T.size = sv.size ∧
      (∀ t < w.head + w.nper * p + w.tail,
        T[surv0 + t]! = op sv[surv0 + t]! tab[r0 + (w.first + t) % p]!) ∧
      ∀ m, (m < surv0 ∨ surv0 + (w.head + w.nper * p + w.tail) ≤ m) → T[m]! = sv[m]! := by
  simp only [WalkInvariant, Std.Legacy.Range.length_toList_zero_start] at hi
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hi
  obtain ⟨g1, -, -, g4, g5⟩ := hT
  have hfh := hpre.1.first_add_head_eq (.inr (by simpa using ht))
  have htp := hpre.1.tail_lt
  rw [Nat.add_assoc, hfh, Nat.add_sub_cancel] at g4
  exact ⟨by rw [g1, h1],
    walkWords_extend (add_add_mul_mod_eq_zero hfh) htp.le h4 h5 g4 g5⟩

private theorem walkInvariant_step {T : Array UInt64} {surv' siv1' : ℕ}
    (hpre : w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size) {pref suff : List ℕ}
    {cur : ℕ} (hc : ForIn.toList [:w.nper] = pref ++ cur :: suff)
    (hi : WalkInvariant tab sv r0 surv0 p w op pref (cur :: suff) (S, surv, siv1))
    (hT : WalkWordsPost tab S surv (siv1 - p) p op T surv' siv1') :
    WalkInvariant tab sv r0 surv0 p w op (pref ++ [cur]) suff (T, surv', siv1') := by
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hi
  obtain ⟨g1, rfl, rfl, g4, g5⟩ := hT
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  have hfh := hpre.1.first_add_head_eq (.inl (by lia))
  rw [Nat.add_assoc r0, hfh, Nat.add_sub_cancel] at g4 ⊢
  obtain ⟨e4, e5⟩ := walkWords_extend (add_add_mul_mod_eq_zero hfh) le_rfl h4 h5 g4 g5
  simp only [WalkInvariant, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
  rw [← Nat.add_assoc w.head]
  exact ⟨by rw [g1, h1], by lia, by lia, e4, e5⟩

end Walk

attribute [local irreducible] WalkInvariant in
/-- `WALK` with a well formed walk `w` of the prime `p` sets each word `surv0 + t` of its range of
the bit array to `op` of its old value and of the word `(first + t) mod p` of the row of the sieve
table from `rowptr[n]` on, and leaves the other words alone: the head reads the words from `first`
on, each full period and the tail those from the start of the row on. -/
@[spec]
theorem walk_spec (g : SiftGlobals) (rowptr : Array ℕ) (sv : Array UInt64) (surv0 n p : ℕ)
    (w : WalkSpec) (op : UInt64 → UInt64 → UInt64) :
    ⦃ w.WF p ∧ surv0 + (w.head + w.nper * p + w.tail) ≤ sv.size ⦄
    walk g rowptr sv surv0 n p w op
    ⦃ fun r ↦ r.size = sv.size ∧
        (∀ t < w.head + w.nper * p + w.tail, r[surv0 + t]! =
          op sv[surv0 + t]! (g.sieve.sieveTab[n]!)[rowptr[n]! + (w.first + t) % p]!) ∧
        ∀ m, (m < surv0 ∨ surv0 + (w.head + w.nper * p + w.tail) ≤ m) →
          r[m]! = sv[m]! ⦄ := by
  vcgen [walk] invariants
  · WalkInvariant (g.sieve.sieveTab[n]!) sv rowptr[n]! surv0 p w op
  all_goals try dsimp only at *
  all_goals with_reducible first
    | lia
    | exact walkInvariant_init ‹_› ‹_›
    | exact walkInvariant_tail_pre ‹_› ‹_›
    | exact walkInvariant_step_pre ‹_› ‹_› ‹_›
    | exact walkInvariant_post ‹_› ‹_›
    | exact walkInvariant_step ‹_› ‹_› ‹_› ‹_›
    | exact walkInvariant_post_tail ‹_› ‹_› ‹_› ‹_›

/-- The walk `w` of the prime `p` over `len` words from a word `i` of a row on: well formed
(`JPoints.WalkSpec.WF`), its head, full periods and tail making up the `len` words, and its first
word congruent to `i` modulo `p`, so that the walk reads for word `i + t` of the row the word
`(i + t) mod p` of the row of the sieve table (`JPoints.WalkSpec.IsWalk.mod_eq`). -/
structure WalkSpec.IsWalk (w : WalkSpec) (p len : ℕ) (i : ℤ) : Prop extends w.WF p where
  /-- The walk covers the `len` words. -/
  length_eq : w.head + w.nper * p + w.tail = len
  /-- Its first word is that of the word `i` of the row. -/
  first_emod : (w.first : ℤ) % p = i % p

/-- A walk `w` of the prime `p` over `len` words from the word `i` of a row on, by its certificates:
a first word in `[1, p]` congruent to `i` modulo `p`, a head up to the end of the period of the row
or of the words, and full periods and a tail shorter than a period that make up the rest. -/
theorem WalkSpec.isWalk_of_head_eq_min {w : WalkSpec} {p len : ℕ} {i : ℤ} (hf0 : 0 < w.first)
    (hfp : w.first ≤ p) (hfe : (w.first : ℤ) % p = i % p) (hh : w.head = min (p - w.first) len)
    (hlen : w.head + w.nper * p + w.tail = len) (ht : w.tail < p) : w.IsWalk p len i := by
  refine ⟨⟨hf0, by lia, ht, fun h' ↦ ?_⟩, hlen, hfe⟩
  rcases h' with h' | h'
  · lia [Nat.mul_le_mul_right p (Nat.one_le_iff_ne_zero.mpr h')]
  · lia

-- The walk of `init_sift` by its first word and its head.
private theorem WalkSpec.isWalk_of_div {p range f h : ℕ} {i : ℤ} (hp : 0 < p) (hf0 : 0 < f)
    (hfp : f ≤ p) (hfe : (f : ℤ) % p = i % p) (hh : h = min (p - f) range) :
    ({ first := f, head := h, nper := (range - h) / p,
        tail := range - h - (range - h) / p * p } : WalkSpec).IsWalk p range i :=
  isWalk_of_head_eq_min hf0 hfp hfe hh (by dsimp only; lia [Nat.div_add_mod (range - h) p])
    (by dsimp only; lia [Nat.div_add_mod (range - h) p, Nat.mod_lt (range - h) hp])

/-- The walk that `init_sift` makes of the prime `p` over the chunk of `range` words from the word
`wLow` on. -/
theorem initSiftWalk_isWalk {p : ℕ} (hp : 0 < p) (wLow : ℤ) (range : ℕ) :
    (initSiftWalk p wLow range).run.IsWalk p range wLow := by
  have h1 : 0 ≤ wLow % p := Int.emod_nonneg _ (by lia)
  have h2 : wLow % p < p := Int.emod_lt_of_pos _ (by lia)
  simp only [initSiftWalk, Id.run, pure]
  by_cases hneg : wLow.tmod p < 0
  · simp only [hneg, ↓reduceIte, Int.tmod_add_natCast_eq_emod hneg]
    split_ifs <;> refine WalkSpec.isWalk_of_div hp ?_ ?_ ?_ (by lia) <;>
      simp_all only [beq_iff_eq] <;> first | lia | simp [Int.toNat_of_nonneg h1, *]
  · simp only [Int.tmod_natCast_eq_emod hneg]
    split_ifs <;> refine WalkSpec.isWalk_of_div hp ?_ ?_ ?_ (by lia) <;>
      simp_all only [beq_iff_eq] <;> first | lia | simp [Int.toNat_of_nonneg h1, *]

section WalkParts

variable {sd : SiftData} {n p : ℕ} {w : WalkSpec} {off len : ℕ}

-- The precondition of `JPoints.walkParts`.
private abbrev WalkPartsPre (sd : SiftData) (n p : ℕ) (w : WalkSpec) (off len : ℕ) : Prop :=
  (∃ g : SiftGlobals, IsStageSetup g sd ∧ n < g.sievePrimes3 ∧ off ≤ g.arraySize ∧
    len ≤ g.arraySize) ∧ p = sd.pr[n]! ∧ 0 < w.first ∧ w.first ≤ p ∧ len < 2 ^ 48

private theorem walkParts_isWalk (hpre : WalkPartsPre sd n p w off len) {f h : ℕ} (hf0 : 0 < f)
    (hfp : f ≤ p) (hfe : (f : ℤ) % p = (w.first + off) % p) (hh : h = min (p - f) len) :
    ({ first := f, head := h,
        nper := (Double.ofInt ↑(len - h - sd.res0[(len - h) * sd.npr + n]!) * sd.invp[n]! +
          0.5).toInt64.toInt.toNat,
        tail := sd.res0[(len - h) * sd.npr + n]! } : WalkSpec).IsWalk p len (w.first + off) := by
  obtain ⟨⟨g, hs, hn, -, hlen⟩, rfl, -, -, hlen48⟩ := hpre
  have hp := hs.three_le_pr hn
  have hr : sd.res0[(len - h) * sd.npr + n]! = (len - h) % sd.pr[n]! :=
    hs.siftData.res0_eq (by lia) hn
  have hk : len - h - (len - h) % sd.pr[n]! = (len - h) / sd.pr[n]! * sd.pr[n]! := by
    have := Nat.mod_add_div (len - h) sd.pr[n]!
    rw [Nat.mul_comm] at this
    lia
  have hq := Double.toInt_toInt64_ofInt_mul_one_div_add_half (k := (len - h) / sd.pr[n]!)
    (p := sd.pr[n]!) (by lia) (by lia [Nat.div_mul_le_self (len - h) sd.pr[n]!])
  rw [hr, hk, hs.siftData.invp_eq hn, hq, Int.toNat_natCast]
  exact WalkSpec.isWalk_of_head_eq_min hf0 hfp hfe hh
    (by dsimp only; lia [Nat.div_add_mod (len - h) sd.pr[n]!]) (Nat.mod_lt _ (by lia))

private theorem walkParts_res0 (hpre : WalkPartsPre sd n p w off len) :
    sd.res0[off * sd.npr + n]! = off % p := by
  obtain ⟨⟨g, hs, hn, hoff, -⟩, rfl, -⟩ := hpre
  exact hs.siftData.res0_eq hoff hn

private theorem walkParts_emod {f r : ℕ} (hr : r = off % p)
    (hf : f + p = w.first + r ∨ f = w.first + r) :
    (f : ℤ) % p = (w.first + off) % p := by
  have := Nat.mod_add_div off p
  rcases hf with hf | hf
  · exact Int.modEq_iff_dvd.mpr ⟨(off / p : ℕ) + 1, by lia⟩
  · exact Int.modEq_iff_dvd.mpr ⟨(off / p : ℕ), by lia⟩

private theorem walkParts_vc (hpre : WalkPartsPre sd n p w off len) {f h : ℕ}
    (hf : f + p = w.first + sd.res0[off * sd.npr + n]! ∧ p < w.first + sd.res0[off * sd.npr + n]! ∨
      f = w.first + sd.res0[off * sd.npr + n]! ∧ ¬p < w.first + sd.res0[off * sd.npr + n]!)
    (hh : h = min (p - f) len) :
    ({ first := f, head := h,
        nper := (Double.ofInt ↑(len - h - sd.res0[(len - h) * sd.npr + n]!) * sd.invp[n]! +
          0.5).toInt64.toInt.toNat,
        tail := sd.res0[(len - h) * sd.npr + n]! } : WalkSpec).IsWalk p len (w.first + off) := by
  have hr := walkParts_res0 hpre
  have : off % p < p := by
    obtain ⟨⟨g, hs, hn, -⟩, rfl, -⟩ := hpre
    exact Nat.mod_lt off (by lia [hs.three_le_pr hn])
  exact walkParts_isWalk hpre (by lia) (by lia) (walkParts_emod hr (by lia)) hh

end WalkParts

/-- `walk_parts` makes of the walk `w` of the `n`-th prime `p` over a chunk the walk over the `len`
words from the position `off` of the chunk on (`JPoints.WalkSpec.IsWalk`), its first word that of
`w` moved on by `off`, its full periods counted in doubles exactly
(`JPoints.Double.toInt_toInt64_ofInt_mul_one_div_add_half`). The globals of the sieve, which it does
not read, enter through what they say of the static data. -/
@[spec]
theorem walkParts_spec (sd : SiftData) (n p : ℕ) (w : WalkSpec) (off len : ℕ) :
    ⦃ (∃ g : SiftGlobals, IsStageSetup g sd ∧ n < g.sievePrimes3 ∧ off ≤ g.arraySize ∧
        len ≤ g.arraySize) ∧ p = sd.pr[n]! ∧ 0 < w.first ∧ w.first ≤ p ∧ len < 2 ^ 48 ⦄
    walkParts sd n p w off len
    ⦃ fun r ↦ r.IsWalk p len (w.first + off) ⦄ := by
  vcgen [walkParts]
  all_goals exact walkParts_vc ‹_› (by lia) (by lia)

/-- Whether the rows of the sieve tables of the primes of the indices `l`, from the indices
`rowptr[n]` on in `sieve_tab[n]`, have the bit `j` in their words `i mod p` for the word `i` of a
row, for the globals `g` and the static data `sd` of the sieve: the bit that the walks of these
primes leave in the word of the bit array for the word `i`
(`JPoints.IsStageSetup.tabBits_range_eq_stage1Keeps` for the rows of `(a, b)`). -/
def tabBits (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (l : List ℕ) (i : ℤ) (j : ℕ) :
    Bool :=
  l.all fun n ↦ ((g.sieve.sieveTab[n]!)[rowptr[n]! + (i % sd.pr[n]!).toNat]!).toBitVec.getLsbD j

/-- The invariant of the loop of `JPoints.sift0Fill` and `JPoints.siftRangeFill` that fills the
words of the bit array `sv` from `surv0` on with the mask `mask`: the size kept, the index after the
words done, the words done set to the mask, the other words unchanged. -/
def FillInvariant (sv : Array UInt64) (surv0 : ℕ) (mask : UInt64) :
    Std.WP.Invariant ℕ (Array UInt64 × ℕ) Prop :=
  fun pref _ st ↦ st.1.size = sv.size ∧ st.2 = surv0 + pref.length ∧
    (∀ t < pref.length, st.1[surv0 + t]! = mask) ∧
    ∀ m, (m < surv0 ∨ surv0 + pref.length ≤ m) → st.1[m]! = sv[m]!

private theorem tabBits_nil (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (i : ℤ) (j : ℕ) :
    tabBits g sd rowptr [] i j = true := rfl

private theorem tabBits_append (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (l₁ l₂ : List ℕ)
    (i : ℤ) (j : ℕ) :
    tabBits g sd rowptr (l₁ ++ l₂) i j =
      (tabBits g sd rowptr l₁ i j && tabBits g sd rowptr l₂ i j) :=
  List.all_append

theorem tabBits_singleton (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (n : ℕ) (i : ℤ)
    (j : ℕ) : tabBits g sd rowptr [n] i j =
      ((g.sieve.sieveTab[n]!)[rowptr[n]! + (i % sd.pr[n]!).toNat]!).toBitVec.getLsbD j := by
  simp [tabBits]

/-- The word `(first + t) mod p` of the row of the sieve table that a walk reads at the position `t`
from its start is that of the word `i + t` of the row, for a walk from a word congruent to `i`. -/
theorem WalkSpec.IsWalk.mod_eq {w : WalkSpec} {p len : ℕ} {i : ℤ} (hw : w.IsWalk p len i) (t : ℕ) :
    (w.first + t) % p = ((i + t) % p).toNat := by
  have hp : 0 < p := lt_of_lt_of_le hw.first_pos (by lia [hw.first_add_head_le])
  rw [← Int.toNat_natCast ((w.first + t) % p), Int.natCast_mod, Nat.cast_add, Int.add_emod,
    hw.first_emod, ← Int.add_emod]

/-- The postcondition of `JPoints.sift0Fill` and `JPoints.siftRangeFill` for the bit array `sv`, the
chunk `ch`, the `range` words from `surv0` on and the mask `mask`, and the result `(F, n)`: the size
kept, the first-stage prime `n ≤ sieve_primes1` to go on with, each bit of these words that of the
mask and of the rows of the sieve tables of the primes before `n`, the other words unchanged. -/
abbrev FillPost (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (sv : Array UInt64)
    (ch : ChunkSpec) (surv0 range : ℕ) (mask : UInt64) (F : Array UInt64) (n : ℕ) : Prop :=
  F.size = sv.size ∧ n ≤ g.sievePrimes1 ∧
    (∀ t < range, ∀ j, (F[surv0 + t]!).toBitVec.getLsbD j = (mask.toBitVec.getLsbD j &&
      tabBits g sd rowptr (List.range n) (ch.wLow + (surv0 + t : ℕ)) j)) ∧
    ∀ m, (m < surv0 ∨ surv0 + range ≤ m) → F[m]! = sv[m]!

section Fill

variable {sv S : Array UInt64} {surv0 range : ℕ} {mask : UInt64} {pref suff : List ℕ} {cur su : ℕ}

theorem fillInvariant_nil {l : List ℕ} : FillInvariant sv surv0 mask [] l (sv, surv0) :=
  ⟨rfl, rfl, nofun, fun _ _ ↦ rfl⟩

theorem fillInvariant_step (hc : ForIn.toList [:range] = pref ++ cur :: suff)
    (h : FillInvariant sv surv0 mask pref (cur :: suff) (S, su)) (hr : surv0 + range ≤ sv.size) :
    FillInvariant sv surv0 mask (pref ++ [cur]) suff (S.set! su mask, su + 1) := by
  obtain ⟨h1, rfl, h3, h4⟩ := h
  have hl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hc
  simp only [FillInvariant, List.length_append, List.length_singleton]
  refine ⟨by simp [h1], by lia, fun t ht ↦ ?_, fun m hm ↦ ?_⟩
  · rw [Array.getElem!_set! (by lia)]
    split_ifs with ht'
    · rfl
    · exact h3 t (by lia)
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h4 m (by lia)

theorem fillInvariant_post {g : SiftGlobals} {sd : SiftData} {rowptr : Array ℕ}
    {ch : ChunkSpec} (h : FillInvariant sv surv0 mask (ForIn.toList [:range]) [] (S, su)) :
    FillPost g sd rowptr sv ch surv0 range mask S 0 := by
  simp only [FillInvariant, Std.Legacy.Range.length_toList_zero_start] at h
  obtain ⟨h1, -, h3, h4⟩ := h
  exact ⟨h1, Nat.zero_le _, fun t ht j ↦ by simp [h3 t ht, tabBits_nil], h4⟩

end Fill

section FillWalk

variable {g : SiftGlobals} {sd : SiftData} {rowptr : Array ℕ} {sv S : Array UInt64}
  {ch : ChunkSpec} {surv0 range : ℕ} {mask : UInt64}

private theorem fill_walk_pre
    (hpre : (¬g.sievePrimes1 = 0 → (ch.walk[0]!).IsWalk sd.pr[0]! range (ch.wLow + surv0)) ∧
      surv0 + range ≤ sv.size) (h : ¬(g.sievePrimes1 == 0) = true) :
    (ch.walk[0]!).WF sd.pr[0]! ∧
      surv0 + ((ch.walk[0]!).head + (ch.walk[0]!).nper * sd.pr[0]! + (ch.walk[0]!).tail) ≤
        sv.size := by
  have hw := hpre.1 (by simpa using h)
  exact ⟨hw.toWF, hw.length_eq ▸ hpre.2⟩

private theorem fill_walk_post
    (hpre : (¬g.sievePrimes1 = 0 → (ch.walk[0]!).IsWalk sd.pr[0]! range (ch.wLow + surv0)) ∧
      surv0 + range ≤ sv.size) (h : ¬(g.sievePrimes1 == 0) = true)
    (hS : S.size = sv.size ∧
      (∀ t < (ch.walk[0]!).head + (ch.walk[0]!).nper * sd.pr[0]! + (ch.walk[0]!).tail,
        S[surv0 + t]! = fillOp mask sv[surv0 + t]!
          (g.sieve.sieveTab[0]!)[rowptr[0]! + ((ch.walk[0]!).first + t) % sd.pr[0]!]!) ∧
      ∀ m, m < surv0 ∨ surv0 + ((ch.walk[0]!).head + (ch.walk[0]!).nper * sd.pr[0]! +
        (ch.walk[0]!).tail) ≤ m → S[m]! = sv[m]!) :
    FillPost g sd rowptr sv ch surv0 range mask S 1 := by
  have hw := hpre.1 (by simpa using h)
  obtain ⟨h1, h2, h3⟩ := hS
  rw [hw.length_eq] at h2 h3
  refine ⟨h1, Nat.one_le_iff_ne_zero.mpr (by simpa using h), fun t ht j ↦ ?_, h3⟩
  rw [h2 t ht, fillOp, UInt64.toBitVec_and, BitVec.getLsbD_and, hw.mod_eq, List.range_one,
    tabBits_singleton, Nat.cast_add, Int.add_assoc]

end FillWalk

/-- The fill of `sift0` leaves in each word of the chunk the bits of the mask and of the row of the
sieve table of the first first-stage prime, by its walk, and the first-stage prime to go on
with. -/
@[spec]
theorem sift0Fill_spec (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (sv : Array UInt64)
    (ch : ChunkSpec) (surv0 range : ℕ) (mask : UInt64) :
    ⦃ (g.sievePrimes1 ≠ 0 → (ch.walk[0]!).IsWalk sd.pr[0]! range (ch.wLow + surv0)) ∧
      surv0 + range ≤ sv.size ⦄
    sift0Fill g sd rowptr sv ch surv0 range mask
    ⦃ fun r ↦ FillPost g sd rowptr sv ch surv0 range mask r.1 r.2 ⦄ := by
  vcgen [sift0Fill] invariants
  · FillInvariant sv surv0 mask
  all_goals with_reducible first
    | exact fillInvariant_nil
    | exact fillInvariant_post ‹_›
    | exact fillInvariant_step ‹_› ‹_› (by lia)
    | exact fill_walk_pre ‹_› ‹_›
    | exact fill_walk_post ‹_› ‹_› ‹_›

/-- The masks of `sift0` and-ed into the first word of the first chunk (`begmask`) and into the last
word of the last chunk (`endmask`), and the bit of `c0` cleared in its word. -/
@[spec]
theorem sift0Masks_spec (g : SiftGlobals) (sd : SiftData) (sv : Array UInt64) (ch : ChunkSpec)
    (k range : ℕ) (c0 : ℤ) :
    ⦃ range ≤ sv.size ⦄
    sift0Masks g sd sv ch k range c0
    ⦃ fun r ↦ r.size = sv.size ∧ ∀ t < range, ∀ j, (r[t]!).toBitVec.getLsbD j =
        (sv[t]!.toBitVec.getLsbD j && (!(k == 0 && t == 0) || g.begmask.toBitVec.getLsbD j) &&
          (!(k == sd.numChunks - 1 && t == range - 1) || g.endmask.toBitVec.getLsbD j) &&
          !(decide (ch.wLow ≤ c0 >>> longShift ∧ c0 >>> longShift < ch.wHigh) &&
            t == (c0 >>> longShift - ch.wLow).toNat && j == (c0 % 64).toNat)) ⦄ := by
  vcgen [sift0Masks]
  all_goals
    try refine ⟨by simp, ?_⟩
    intro t ht j
    have ht' : t < sv.size := by lia
    have hn : (c0 % (longLength : ℤ)).toNat < 64 := by simp only [longLength]; lia
    try simp only [Array.getLsbD_getElem!_set!_and_not, Array.size_set!, ht', hn]
    try simp only [Array.getLsbD_getElem!_set!_and, Array.size_set!, ht']
    simp only [longLength, Nat.cast_ofNat] at *
    grind

/-- The test of `sift0` that clears the bit of `c0` in the word of the position `t` of a chunk is
whether `c0` is the third coordinate `64 (w_low + t) + j` of the bit `j`. -/
private theorem c0_cond_eq {wLow wHigh c0 : ℤ} {t j : ℕ} (ht : t < (wHigh - wLow).toNat)
    (hj : j < 64) :
    (decide (wLow ≤ c0 >>> longShift ∧ c0 >>> longShift < wHigh) &&
      t == (c0 >>> longShift - wLow).toNat && j == (c0 % 64).toNat) =
      (64 * (wLow + t) + j == c0) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Int.shiftRight_longShift]
  lia

theorem IsStageSetup.tabBits_range_eq_stage1Keeps {g : SiftGlobals} {sd : SiftData}
    (h : IsStageSetup g sd) {rowptr : Array ℕ} {c : RowSetupCache}
    (hw : RowSetupCache.WF g sd rowptr c) {a b : ℤ} (hA : c.lastA = a) (hB : c.lastB = b)
    (ha : 0 ≤ a) (i : ℤ) {j : ℕ} (hj : j < 64) :
    tabBits g sd rowptr (List.range g.sievePrimes1) i j = stage1Keeps g a b (64 * i + j) := by
  refine List.all_congr_left fun n hn ↦ h.getLsbD_sieveTab_eq_admits12 hw hA hB ha ?_ i hj
  lia [List.mem_range.mp hn, h.sievePrimes1_le_sievePrimes2]

/-- The invariant of the loops of `sift0` and `sift_range` over the first-stage primes after the
first, from the bit array `S` that the fill and the masks leave, over the `len` words from `surv0`
on of the chunk `ch`: the size kept, and each bit of these words that of `S` and of the rows of the
sieve tables of the primes done (`JPoints.tabBits`). -/
def WalksInvariant (g : SiftGlobals) (sd : SiftData) (rowptr : Array ℕ) (S : Array UInt64)
    (ch : ChunkSpec) (surv0 len : ℕ) : Std.WP.Invariant ℕ (Array UInt64) Prop :=
  fun pref _ sv ↦ sv.size = S.size ∧ ∀ t < len, ∀ j, (sv[surv0 + t]!).toBitVec.getLsbD j =
    (S[surv0 + t]!.toBitVec.getLsbD j && tabBits g sd rowptr pref (ch.wLow + (surv0 + t : ℕ)) j)

/-- The walks of the first-stage primes over the chunk `ch` as `init_sift` makes them, for the
globals `g` and the static data `sd` of the sieve: the walk of the `n`-th prime over the words of
the chunk from its first word on (`JPoints.WalkSpec.IsWalk`). -/
def ChunkWalks (g : SiftGlobals) (sd : SiftData) (ch : ChunkSpec) : Prop :=
  ∀ n < g.sievePrimes1, (ch.walk[n]!).IsWalk sd.pr[n]! (ch.wHigh - ch.wLow).toNat ch.wLow

/-! ### The chunks of a row -/

namespace IsStageSetup

variable {g : SiftGlobals} {sd : SiftData} (h : IsStageSetup g sd)
include h

theorem one_le_wHighAll_sub_wLowAll : 1 ≤ sd.wHighAll - sd.wLowAll := by
  have := h.check.one_le_height
  rw [h.siftData.wHighAll_eq, h.siftData.wLowAll_eq, Int.shiftRight_longShift,
    Int.shiftRight_longShift]
  lia

theorem range_chunk_le {k : ℕ} (hk : k < sd.numChunks) :
    ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat ≤ g.arraySize := by
  rw [h.siftData.wHigh_chunk hk, h.siftData.wLow_chunk hk]
  lia

theorem range_chunk_lt {k : ℕ} (hk : k < sd.numChunks) :
    ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat < 2 ^ 48 := by
  have := h.check.height_le_maxHeight
  have := h.check.one_le_height
  have := maxHeight_lt_two_pow_32
  have hlo := h.siftData.wLow_chunk hk
  have hhi := h.siftData.wHigh_chunk hk
  have e1 := h.siftData.wHighAll_eq
  have e2 := h.siftData.wLowAll_eq
  rw [Int.shiftRight_longShift] at e1 e2
  lia

theorem chunkWalks {k : ℕ} (hk : k < sd.numChunks) : ChunkWalks g sd (sd.chunks[k]!) :=
    fun n hn ↦ by
  have hn3 : n < g.sievePrimes3 := by
    lia [h.sievePrimes1_le_sievePrimes2, h.sievePrimes2_le_sievePrimes3]
  rw [h.siftData.walk_chunk hk hn, h.siftData.pr_eq hn3]
  exact initSiftWalk_isWalk (by lia [h.three_le_pr hn3, h.pr_eq hn3]) _ _

end IsStageSetup

namespace IsRowSetup

variable {g : SiftGlobals} {sd : SiftData} (h : IsRowSetup g sd)
include h

private theorem natCast_numChunks :
    (sd.numChunks : ℤ) = (sd.wHighAll - sd.wLowAll - 1) / g.arraySize + 1 := by
  have h1 := h.one_le_wHighAll_sub_wLowAll
  have hA := h.one_le_arraySize
  have h0 : 0 ≤ (sd.wHighAll - sd.wLowAll - 1) / g.arraySize := Int.ediv_nonneg (by lia) (by lia)
  rw [h.siftData.numChunks_eq, ceilDiv, ite_eq_right (by lia),
    Int.tdiv_eq_ediv_of_nonneg (by lia), Int.toNat_of_nonneg (by lia)]
  ring

private theorem lt_numChunks_iff {k : ℕ} :
    k < sd.numChunks ↔ (k : ℤ) * g.arraySize < sd.wHighAll - sd.wLowAll := by
  have hA := h.one_le_arraySize
  have := h.natCast_numChunks
  rw [← Int.ofNat_lt, this, Int.lt_add_one_iff, Int.le_ediv_iff_mul_le (by lia)]
  lia

private theorem eq_numChunks_sub_one_iff {k : ℕ} (hk : k < sd.numChunks) :
    k = sd.numChunks - 1 ↔ sd.wHighAll - sd.wLowAll ≤ ((k : ℤ) + 1) * g.arraySize := by
  have := h.lt_numChunks_iff (k := k + 1)
  push_cast at this
  lia

private theorem wLow_chunk_lt {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wLow < sd.wHighAll := by
  have := h.lt_numChunks_iff.mp hk
  rw [h.siftData.wLow_chunk hk]
  push_cast
  lia

private theorem bne_wLowAll {k : ℕ} (hk : k < sd.numChunks) (t : ℕ) :
    ((sd.chunks[k]!).wLow + t != sd.wLowAll) = !(k == 0 && t == 0) := by
  have hA := h.one_le_arraySize
  have hlo := h.siftData.wLow_chunk hk
  have hk0 : ((k * g.arraySize : ℕ) : ℤ) = 0 ↔ k = 0 := by
    push_cast; simp only [mul_eq_zero]; lia
  rw [bne, Bool.eq_iff_iff]
  simp only [beq_eq_false_iff_ne, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp,
    beq_iff_eq]
  lia

private theorem bne_wHighAll_sub_one {k : ℕ} (hk : k < sd.numChunks) {t : ℕ}
    (ht : t < ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat) :
    ((sd.chunks[k]!).wLow + t != sd.wHighAll - 1) = !(k == sd.numChunks - 1 &&
      t == ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat - 1) := by
  have hlast := h.eq_numChunks_sub_one_iff hk
  have hlt := h.lt_numChunks_iff.mp hk
  have hlo := h.siftData.wLow_chunk hk
  have hhi := h.siftData.wHigh_chunk hk
  rw [bne, Bool.eq_iff_iff]
  simp only [beq_eq_false_iff_ne, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_imp,
    beq_iff_eq]
  lia

/-- The third coordinates of the bits `j` of the word of the position `t` of the `k`-th chunk lie in
the row by the masks of the first and the last word, which `sift0` applies to the first word of the
first chunk and to the last word of the last. -/
theorem rangeKeeps_chunk {k : ℕ} (hk : k < sd.numChunks) {t : ℕ}
    (ht : t < ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat) {j : ℕ} (hj : j < 64) :
    rangeKeeps g sd (64 * ((sd.chunks[k]!).wLow + t) + j) =
      ((!(k == 0 && t == 0) || g.begmask.toBitVec.getLsbD j) &&
        (!(k == sd.numChunks - 1 &&
          t == ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat - 1) ||
          g.endmask.toBitVec.getLsbD j)) := by
  have hlt := h.wLow_chunk_lt hk
  have hlo := h.siftData.wLow_chunk hk
  have hhi := h.siftData.wHigh_chunk hk
  have hi : (64 * ((sd.chunks[k]!).wLow + t) + j) >>> longShift = (sd.chunks[k]!).wLow + t := by
    rw [Int.shiftRight_longShift]; lia
  have hj' : ((64 * ((sd.chunks[k]!).wLow + t) + j) % 64).toNat = j := by lia
  simp only [rangeKeeps, hi, hj', h.bne_wLowAll hk, h.bne_wHighAll_sub_one hk ht]
  rw [decide_eq_true (by lia), Bool.true_and]

theorem wLow_add_range_chunk {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wLow + (((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat : ℕ) =
      (sd.chunks[k]!).wHigh := by
  have := h.wLow_chunk_lt hk
  have := h.one_le_arraySize
  rw [h.siftData.wHigh_chunk hk, h.siftData.wLow_chunk hk] at *
  lia

theorem wLow_chunk_eq_min {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wLow = min (sd.wLowAll + (k * g.arraySize : ℕ)) sd.wHighAll := by
  have := h.wLow_chunk_lt hk
  rw [h.siftData.wLow_chunk hk] at *
  lia

theorem wHigh_chunk_eq_min {k : ℕ} (hk : k < sd.numChunks) :
    (sd.chunks[k]!).wHigh = min (sd.wLowAll + ((k + 1) * g.arraySize : ℕ)) sd.wHighAll := by
  rw [h.siftData.wHigh_chunk hk]
  push_cast
  ring_nf

theorem min_numChunks :
    min (sd.wLowAll + (sd.numChunks * g.arraySize : ℕ)) sd.wHighAll = sd.wHighAll := by
  have := h.lt_numChunks_iff (k := sd.numChunks)
  push_cast at this ⊢
  lia

theorem wHigh_chunk_eq_wLow_chunk {k : ℕ} (hk : k + 1 < sd.numChunks) :
    (sd.chunks[k]!).wHigh = (sd.chunks[k + 1]!).wLow := by
  rw [h.wHigh_chunk_eq_min (by lia), h.wLow_chunk_eq_min hk]

private theorem wLow_chunk_zero (hk : 0 < sd.numChunks) : (sd.chunks[0]!).wLow = sd.wLowAll := by
  have := h.one_le_wHighAll_sub_wLowAll
  rw [h.wLow_chunk_eq_min hk]
  simp only [Nat.zero_mul, Nat.cast_zero, Int.add_zero]
  lia

private theorem wHigh_chunk_last {k : ℕ} (hk : k + 1 = sd.numChunks) :
    (sd.chunks[k]!).wHigh = sd.wHighAll := by
  rw [h.wHigh_chunk_eq_min (by lia), hk, h.min_numChunks]

theorem succ_lt_numChunks {k : ℕ} {i : ℤ} (hk : k < sd.numChunks) (hi : i < sd.wHighAll)
    (hw : (sd.chunks[k]!).wHigh ≤ i) : k + 1 < sd.numChunks := by
  by_contra hc
  have := h.wHigh_chunk_last (k := k) (by lia)
  lia

theorem pos_of_lt_wLow_chunk {k : ℕ} {i : ℤ} (hk : k < sd.numChunks) (hi : sd.wLowAll ≤ i)
    (hw : i < (sd.chunks[k]!).wLow) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h.wLow_chunk_zero hk] at hw; lia
  · exact hk0

theorem wHigh_chunk_le {k k' : ℕ} (hk : k ≤ k') (hk' : k' < sd.numChunks) :
    (sd.chunks[k]!).wHigh ≤ (sd.chunks[k']!).wHigh := by
  rw [h.wHigh_chunk_eq_min (by lia), h.wHigh_chunk_eq_min hk']
  lia [Nat.mul_le_mul_right g.arraySize (show k + 1 ≤ k' + 1 by lia)]

theorem rowRangePoints_chunk_succ (a b : ℤ) {k : ℕ} (hk : k < sd.numChunks) :
    rowRangePoints g sd a b sd.wLowAll (min (sd.wLowAll + (k * g.arraySize : ℕ)) sd.wHighAll) ++
        rowRangePoints g sd a b (sd.chunks[k]!).wLow (sd.chunks[k]!).wHigh =
      rowRangePoints g sd a b sd.wLowAll
        (min (sd.wLowAll + ((k + 1) * g.arraySize : ℕ)) sd.wHighAll) := by
  have := h.one_le_wHighAll_sub_wLowAll
  rw [h.wLow_chunk_eq_min hk, h.wHigh_chunk_eq_min hk, rowRangePoints_append _ _ _ _ (by lia)]
  push_cast
  lia

theorem rowRangePoints_eq_chunk (a b : ℤ) {k : ℕ} (hk : k < sd.numChunks) :
    rowRangePoints g sd a b sd.wLowAll sd.wHighAll =
      rowRangePoints g sd a b sd.wLowAll (min (sd.wLowAll + (k * g.arraySize : ℕ)) sd.wHighAll) ++
        rowRangePoints g sd a b (sd.chunks[k]!).wLow (sd.chunks[k]!).wHigh ++
        rowRangePoints g sd a b (min (sd.wLowAll + ((k + 1) * g.arraySize : ℕ)) sd.wHighAll)
          sd.wHighAll := by
  have := h.one_le_wHighAll_sub_wLowAll
  rw [h.rowRangePoints_chunk_succ a b hk, rowRangePoints_append _ _ _ _ (by push_cast; lia)
    (by lia)]

end IsRowSetup

section Walks

variable {g : SiftGlobals} {sd : SiftData} {rowptr : Array ℕ} {S sv T : Array UInt64}
  {ch : ChunkSpec} {surv0 len n0 cur : ℕ} {pref suff : List ℕ}

theorem walksInvariant_nil {l : List ℕ} : WalksInvariant g sd rowptr S ch surv0 len [] l S :=
  ⟨rfl, fun _ _ _ ↦ by simp [tabBits_nil]⟩

theorem walksInvariant_step {w : WalkSpec} {i0 : ℤ}
    (hv : WalksInvariant g sd rowptr S ch surv0 len pref (cur :: suff) sv)
    (hw : w.IsWalk sd.pr[cur]! len i0) (hi0 : i0 % sd.pr[cur]! = (ch.wLow + surv0) % sd.pr[cur]!)
    (hT : T.size = sv.size ∧
      (∀ t < w.head + w.nper * sd.pr[cur]! + w.tail, T[surv0 + t]! = andOp sv[surv0 + t]!
        (g.sieve.sieveTab[cur]!)[rowptr[cur]! + (w.first + t) % sd.pr[cur]!]!) ∧
      ∀ m, (m < surv0 ∨ surv0 + (w.head + w.nper * sd.pr[cur]! + w.tail) ≤ m) → T[m]! = sv[m]!) :
    WalksInvariant g sd rowptr S ch surv0 len (pref ++ [cur]) suff T := by
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨g1, g2, -⟩ := hT
  rw [hw.length_eq] at g2
  refine ⟨g1.trans h1, fun t ht j ↦ ?_⟩
  rw [g2 t ht, andOp, UInt64.toBitVec_and, BitVec.getLsbD_and, h2 t ht j, hw.mod_eq,
    tabBits_append, tabBits_singleton, Bool.and_assoc]
  congr 4
  rw [Int.add_emod, hi0, ← Int.add_emod, Nat.cast_add, Int.add_assoc]

end Walks

-- The postcondition of `JPoints.sift0Masks`.
private abbrev MasksPost (g : SiftGlobals) (sd : SiftData) (sv : Array UInt64) (ch : ChunkSpec)
    (k range : ℕ) (c0 : ℤ) (M : Array UInt64) : Prop :=
  M.size = sv.size ∧ ∀ t < range, ∀ j, (M[t]!).toBitVec.getLsbD j =
    (sv[t]!.toBitVec.getLsbD j && (!(k == 0 && t == 0) || g.begmask.toBitVec.getLsbD j) &&
      (!(k == sd.numChunks - 1 && t == range - 1) || g.endmask.toBitVec.getLsbD j) &&
      !(decide (ch.wLow ≤ c0 >>> longShift ∧ c0 >>> longShift < ch.wHigh) &&
        t == (c0 >>> longShift - ch.wLow).toNat && j == (c0 % 64).toNat))

/-- The precondition of `JPoints.sift0` for the state `s`, the row `(a, b)`, the `k`-th chunk, the
mask `mask` and the excluded third coordinate `c0`: what the sieve of a row reads
(`JPoints.IsRowSetup`), a chunk of the row, the rows of the sieve tables of the row
(`JPoints.RowSetupCache.WF` with `(last_a, last_b) = (a, b)`), consistent data of the third stage, a
bit array of `array_size + 1` words, `0 ≤ a ≤ H`, `|b| ≤ H`, `b ≥ 1` for `a = 0`, and the mask and
`c0` of the row (`JPoints.siftMask`). -/
abbrev Sift0Pre (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (k : ℕ)
    (mask : UInt64) (c0 : ℤ) : Prop :=
  IsRowSetup g sd ∧ k < sd.numChunks ∧ RowSetupCache.WF g sd s.rowptr s.rowSetup ∧
    s.rowSetup.lastA = a ∧ s.rowSetup.lastB = b ∧ Row3Cache.WF g sd s.row3 ∧
    s.survivors.size = g.arraySize + 1 ∧ 0 ≤ a ∧ a ≤ g.check.height ∧ |b| ≤ g.check.height ∧
    (a = 0 → 1 ≤ b) ∧ mask = (siftMask g a b).2 ∧ c0 = (siftMask g a b).1

theorem tabBits_range_append {g : SiftGlobals} {sd : SiftData} {rowptr : Array ℕ} {n N : ℕ}
    (hn : n ≤ N) (i : ℤ) (j : ℕ) :
    (tabBits g sd rowptr (List.range n) i j && tabBits g sd rowptr (ForIn.toList [n:N]) i j) =
      tabBits g sd rowptr (List.range N) i j := by
  have e := List.range'_append_1 (s := 0) (m := n) (n := N - n)
  rw [Nat.zero_add, Nat.add_sub_cancel' hn] at e
  rw [← tabBits_append, Std.Legacy.Range.toList_eq_range', List.range_eq_range',
    List.range_eq_range', e]

/-- The postcondition of the sieve of a chunk or of a range of words of a chunk (`JPoints.sift0`,
`JPoints.siftRange`) for the state `s`, the points `L` that it finds and the result `r`: `s` with
its own bit array, of the same size, data of the third stage, counters and output, consistent data
of the third stage, the points printed after the output of `s`, only the first under `-1`, and the
flag of a point under `-1`. -/
def SiftPost (g : SiftGlobals) (sd : SiftData) (s : SiftState) (L : List (ℤ × ℤ × ℤ × ℤ))
    (r : Bool × SiftState) : Prop :=
  r.2 = { s with
      survivors := r.2.survivors, row3 := r.2.row3, numSurv1 := r.2.numSurv1,
      numSurv2 := r.2.numSurv2, numSurv3 := r.2.numSurv3, out := r.2.out } ∧
    r.2.survivors.size = s.survivors.size ∧ Row3Cache.WF g sd r.2.row3 ∧
    r.2.out = s.out.appendPoints g.check (firstIf g.check.onePoint L) ∧
    r.1 = (g.check.onePoint && !L.isEmpty)

/-- The postcondition of the sieve of a chunk or of a range from that of the scan of its words
(`JPoints.ScanPost`) on a bit array of the size of that of `s`. -/
theorem SiftPost.of_scanPost {g : SiftGlobals} {sd : SiftData} {s : SiftState}
    {L : List (ℤ × ℤ × ℤ × ℤ)} {r : Bool × SiftState} {S' : Array UInt64}
    (hr : ScanPost g sd { s with survivors := S' } L r) (hsize : S'.size = s.survivors.size) :
    SiftPost g sd s L r := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hsv : r.2.survivors = S' := congr(SiftState.survivors $h1)
  exact ⟨SiftState.eq_with_survivors_of_eq_with h1, by rw [hsv, hsize], h2, h3, h4⟩

section Sift0

variable {g : SiftGlobals} {sd : SiftData} {s : SiftState} {a b : ℤ} {k : ℕ} {mask : UInt64}
  {c0 : ℤ}

private theorem sift0_bits (hpre : Sift0Pre g sd s a b k mask c0) {F M S' : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat mask F n)
    (hM : MasksPost g sd F (sd.chunks[k]!) k
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat (ForIn.toList [n:g.sievePrimes1]) [] S')
    {t : ℕ} (ht : t < ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat) {j : ℕ} (hj : j < 64) :
    (S'[t]!).toBitVec.getLsbD j = (maskKeeps g a b (64 * ((sd.chunks[k]!).wLow + t) + j) &&
      stage1Keeps g a b (64 * ((sd.chunks[k]!).wLow + t) + j) &&
      rangeKeeps g sd (64 * ((sd.chunks[k]!).wLow + t) + j) &&
      (64 * ((sd.chunks[k]!).wLow + t) + j != c0)) := by
  obtain ⟨h, hk, hw, hA, hB, -, -, ha, -, -, -, hmask, -⟩ := hpre
  have e := hS.2 t ht j
  have e' := hF.2.2.1 t ht j
  simp only [Nat.zero_add] at e e'
  rw [e, hM.2 t ht j, e', h.rangeKeeps_chunk hk ht hj, c0_cond_eq ht hj, maskKeeps,
    ← hmask, Int.toNat_mul_add_emod_of_lt (by lia),
    ← h.tabBits_range_eq_stage1Keeps hw hA hB ha _ hj, ← tabBits_range_append hF.2.1, bne]
  ac_rfl

private theorem sift0_fill_pre (hpre : Sift0Pre g sd s a b k mask c0) :
    (¬g.sievePrimes1 = 0 → (sd.chunks[k]!).walk[0]!.IsWalk sd.pr[0]!
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat ((sd.chunks[k]!).wLow + (0 : ℕ))) ∧
      0 + ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat ≤ s.survivors.size := by
  obtain ⟨h, hk, -, -, -, -, hsize, -⟩ := hpre
  refine ⟨fun h0 ↦ by simpa using h.chunkWalks hk 0 (by lia), ?_⟩
  lia [h.range_chunk_le hk]

private theorem sift0_masks_pre (hpre : Sift0Pre g sd s a b k mask c0) {F : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat mask F n) :
    ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat ≤ F.size := by
  lia [hpre.1.range_chunk_le hpre.2.1, hF.1, hpre.2.2.2.2.2.2.1]

private theorem sift0_walk_pre (hpre : Sift0Pre g sd s a b k mask c0) {F M sv : Array UInt64}
    {n cur : ℕ} {pref suff : List ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat mask F n)
    (hM : MasksPost g sd F (sd.chunks[k]!) k
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat c0 M)
    (hc : ForIn.toList [n:g.sievePrimes1] = pref ++ cur :: suff)
    (hv : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat pref (cur :: suff) sv) :
    ((sd.chunks[k]!).walk[cur]!).WF sd.pr[cur]! ∧
      0 + (((sd.chunks[k]!).walk[cur]!).head + ((sd.chunks[k]!).walk[cur]!).nper * sd.pr[cur]! +
        ((sd.chunks[k]!).walk[cur]!).tail) ≤ sv.size := by
  have hw := hpre.1.chunkWalks hpre.2.1 cur (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)
  refine ⟨hw.toWF, ?_⟩
  rw [hw.length_eq, hv.1, hM.1, hF.1]
  lia [hpre.1.range_chunk_le hpre.2.1, hpre.2.2.2.2.2.2.1]

private theorem sift0_walk_step (hpre : Sift0Pre g sd s a b k mask c0) {M sv T : Array UInt64}
    {n cur : ℕ} {pref suff : List ℕ} (hc : ForIn.toList [n:g.sievePrimes1] = pref ++ cur :: suff)
    (hv : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat pref (cur :: suff) sv)
    (hT : T.size = sv.size ∧
      (∀ t < ((sd.chunks[k]!).walk[cur]!).head + ((sd.chunks[k]!).walk[cur]!).nper * sd.pr[cur]! +
          ((sd.chunks[k]!).walk[cur]!).tail, T[0 + t]! = andOp sv[0 + t]!
        (g.sieve.sieveTab[cur]!)[s.rowptr[cur]! + (((sd.chunks[k]!).walk[cur]!).first + t) %
          sd.pr[cur]!]!) ∧
      ∀ m, (m < 0 ∨ 0 + (((sd.chunks[k]!).walk[cur]!).head +
              ((sd.chunks[k]!).walk[cur]!).nper * sd.pr[cur]! +
          ((sd.chunks[k]!).walk[cur]!).tail) ≤ m) →
        T[m]! = sv[m]!) :
    WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat (pref ++ [cur]) suff T :=
  walksInvariant_step hv (hpre.1.chunkWalks hpre.2.1 cur
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)) (by simp) hT

private theorem sift0_scan_pre (hpre : Sift0Pre g sd s a b k mask c0) {F M S' : Array UInt64}
    {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat mask F n)
    (hM : MasksPost g sd F (sd.chunks[k]!) k
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat (ForIn.toList [n:g.sievePrimes1]) []
      S') :
    ScanPre g sd { s with survivors := S' } a b (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat := by
  obtain ⟨h, hk, hw, hA, hB, h3, -, ha, haH, hbH, ha0, -⟩ := id hpre
  exact ⟨h.toIsStageSetup, hw, hA, hB, h3, ha, haH, hbH, ha0,
    fun i _ hi ↦ h.wordResidues hk (by lia [h.range_chunk_le hk]),
    fun i _ hi c hc hbit ↦ h.abs_le_of_getLsbD (fun j hj ↦ sift0_bits hpre hF hM hS hi hj) hc hbit⟩

private theorem sift0_post (hpre : Sift0Pre g sd s a b k mask c0) {F M S' : Array UInt64} {n : ℕ}
    (hF : FillPost g sd s.rowptr s.survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat mask F n)
    (hM : MasksPost g sd F (sd.chunks[k]!) k
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat c0 M)
    (hS : WalksInvariant g sd s.rowptr M (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat (ForIn.toList [n:g.sievePrimes1]) []
      S') {r : Bool × SiftState}
    (hr : ScanPost g sd { s with survivors := S' } (scanPoints g S' a b (sd.chunks[k]!)
      (List.range' 0 (((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat - 0))) r) :
    SiftPost g sd s (rowRangePoints g sd a b (sd.chunks[k]!).wLow (sd.chunks[k]!).wHigh) r := by
  obtain ⟨h, hk, -, -, -, -, -, ha, -, -, ha0, -, hc0⟩ := id hpre
  rw [h.scanPoints_eq_rowRangePoints ha ha0 hc0 (Nat.zero_le _)
    (fun t _ ht j hj ↦ sift0_bits hpre hF hM hS ht hj), Nat.cast_zero, Int.add_zero,
    h.wLow_add_range_chunk hk] at hr
  exact SiftPost.of_scanPost hr (by rw [hS.1, hM.1, hF.1])

end Sift0

attribute [local irreducible] WalksInvariant ScanPost in
/-- `sift0` prints the points of the row `(a, b)` in the words of the `k`-th chunk
(`JPoints.rowRangePoints`), only the first under `-1`: its bit array holds after the fill, the masks
and the walks the bits of the mask of the row, of the first stage and of the words of the row, off
`c0`, which the scan of its words passes to the second stage (`JPoints.scanWords_spec`). It changes
no other field of the state but the bit array, the data of the third stage, the counters and the
output (`JPoints.SiftPost`). -/
@[spec]
theorem sift0_spec (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) (k : ℕ)
    (mask : UInt64) (c0 : ℤ) :
    ⦃ Sift0Pre g sd s a b k mask c0 ⦄
    sift0 g sd s a b k mask c0
    ⦃ fun r ↦ SiftPost g sd s
        (rowRangePoints g sd a b (sd.chunks[k]!).wLow (sd.chunks[k]!).wHigh) r ⦄ := by
  vcgen [sift0, sift0Fill_spec, sift0Masks_spec, walk_spec, scanWords_spec] invariants
  · WalksInvariant g sd s.rowptr survivors (sd.chunks[k]!) 0
      ((sd.chunks[k]!).wHigh - (sd.chunks[k]!).wLow).toNat
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact sift0_fill_pre ‹_›
    | exact sift0_masks_pre ‹_› ‹_›
    | exact walksInvariant_nil
    | exact sift0_scan_pre ‹_› ‹_› ‹_› ‹_›
    | exact sift0_post ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact sift0_walk_pre ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact sift0_walk_step ‹_› ‹_› ‹_› ‹_›

/-- The state `s'` of `sift` after some chunks, from the state `s` after `row_setup`, with the
points `L` of these chunks: `s` with its own bit array, of the same size, data of the third stage,
counters and output, consistent data of the third stage, the points printed after the output of `s`,
and none under `-1`. -/
def SiftCont (g : SiftGlobals) (sd : SiftData) (s s' : SiftState) (L : List (ℤ × ℤ × ℤ × ℤ)) :
    Prop :=
  s' = { s with
      survivors := s'.survivors, row3 := s'.row3, numSurv1 := s'.numSurv1,
      numSurv2 := s'.numSurv2, numSurv3 := s'.numSurv3, out := s'.out } ∧
    s'.survivors.size = s.survivors.size ∧ Row3Cache.WF g sd s'.row3 ∧
    s.out.Searched g.check L s'.out

/-- The invariant of the loop of `JPoints.sift` over the chunks of the row `(a, b)`, from the state
`s` after `row_setup`, whose state is the result of an early return and the state of the thread:
before a return, the state after the chunks before the cursor (`JPoints.SiftCont`), whose words are
those of the row from `w_low_all` up to the first word of the chunk of the cursor; after it, the
postcondition (`JPoints.SiftPost`) for the whole row. -/
def SiftInvariant (g : SiftGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) :
    Std.WP.Invariant ℕ (Option (Bool × SiftState) × SiftState) Prop :=
  fun pref suff st ↦ st.1.elim
    (SiftCont g sd s st.2 (rowRangePoints g sd a b sd.wLowAll
      (min (sd.wLowAll + (pref.length * g.arraySize : ℕ)) sd.wHighAll)))
    fun r ↦ suff = [] ∧ SiftPost g sd s (rowRangePoints g sd a b sd.wLowAll sd.wHighAll) r

-- The precondition of `JPoints.sift`.
private abbrev SiftPre (bg : BandGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) : Prop :=
  IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ∧
    |b| ≤ bg.sift.check.height ∧ (a = 0 → 1 ≤ b)


/-- The state after the sieve of a row is consistent: `row_setup` and the sieve of the chunks change
only the rows, the statics of `row_setup`, the bit array, the data of the third stage, the counters
and the output. -/
private theorem SiftState.WF.of_sift {bg : BandGlobals} {sd : SiftData} {s s1 st : SiftState}
    {a b : ℤ}
    (hs : s.WF bg sd) (hrs : RowSetupPost bg.sift sd s a b s1)
    (hst : st = { s1 with
      survivors := st.survivors, row3 := st.row3, numSurv1 := st.numSurv1,
      numSurv2 := st.numSurv2, numSurv3 := st.numSurv3, out := st.out })
    (hsize : st.survivors.size = s1.survivors.size) (h3 : Row3Cache.WF bg.sift sd st.row3) :
    st.WF bg sd := by
  have e1 : s1.survivors = s.survivors := congr(SiftState.survivors $(hrs.1))
  have e2 : s1.tube = s.tube := congr(SiftState.tube $(hrs.1))
  have e3 : s1.curChunk = s.curChunk := congr(SiftState.curChunk $(hrs.1))
  rw [hst]
  exact ⟨hsize.trans (e1 ▸ hs.size_survivors), hrs.2.1, h3, e2 ▸ hs.tube, e3 ▸ hs.curChunk_lt⟩

section Sift

variable {bg : BandGlobals} {sd : SiftData} {s s1 st s' : SiftState} {a b : ℤ}
  {pref suff : List ℕ} {cur : ℕ} {o : Option (Bool × SiftState)}

private theorem sift_rowSetup_pre (hpre : SiftPre bg sd s a b) :
    IsStageSetup bg.sift sd ∧ RowSetupCache.WF bg.sift sd s.rowptr s.rowSetup ∧ 0 ≤ a ∧
      |b| ≤ bg.sift.check.height :=
  ⟨hpre.1.isStageSetup, hpre.2.1.rowSetup, hpre.2.2.1, hpre.2.2.2.2.1⟩

private theorem siftInvariant_init (hpre : SiftPre bg sd s a b)
    (hrs : RowSetupPost bg.sift sd s a b s1) {l : List ℕ} :
    SiftInvariant bg.sift sd s1 a b [] l (none, s1) := by
  have := hpre.1.isRowSetup.one_le_wHighAll_sub_wLowAll
  have hm : min (sd.wLowAll + (([] : List ℕ).length * bg.sift.arraySize : ℕ)) sd.wHighAll =
      sd.wLowAll := by simp; lia
  refine ⟨rfl, rfl, hrs.1 ▸ hpre.2.1.row3, ?_, fun _ ↦ ?_⟩ <;>
    simp only [hm, rowRangePoints_self, Output.appendPoints_nil]

private theorem SiftInvariant.cont
    (hv : SiftInvariant bg.sift sd s1 a b pref (cur :: suff) (o, st)) :
    o = none ∧ SiftCont bg.sift sd s1 st (rowRangePoints bg.sift sd a b sd.wLowAll
      (min (sd.wLowAll + (pref.length * bg.sift.arraySize : ℕ)) sd.wHighAll)) :=
  Option.eq_none_and_of_elim_cons hv

private theorem sift_sift0_pre (hpre : SiftPre bg sd s a b) (hrs : RowSetupPost bg.sift sd s a b s1)
    (hc : ForIn.toList [:sd.numChunks] = pref ++ cur :: suff)
    (hv : SiftInvariant bg.sift sd s1 a b pref (cur :: suff) (o, st)) :
    IsRowSetup bg.sift sd ∧ cur < sd.numChunks ∧ RowSetupCache.WF bg.sift sd st.rowptr st.rowSetup ∧
      st.rowSetup.lastA = a ∧ st.rowSetup.lastB = b ∧ Row3Cache.WF bg.sift sd st.row3 ∧
      st.survivors.size = bg.sift.arraySize + 1 ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ∧
      |b| ≤ bg.sift.check.height ∧ (a = 0 → 1 ≤ b) := by
  obtain ⟨-, hst, hsize, h3, -⟩ := hv.cont
  have e1 : s1.survivors = s.survivors := congr(SiftState.survivors $(hrs.1))
  obtain ⟨hS, hs, ha, haH, hbH, ha0⟩ := hpre
  rw [hst]
  exact ⟨hS.isRowSetup, Std.Legacy.Range.lt_of_toList_eq_append_cons hc, hrs.2.1, hrs.2.2.1,
    hrs.2.2.2, h3, hsize.trans (e1 ▸ hs.size_survivors), ha, haH, hbH, ha0⟩

private theorem siftInvariant_return (hpre : SiftPre bg sd s a b)
    (hc : ForIn.toList [:sd.numChunks] = pref ++ cur :: suff)
    (hv : SiftInvariant bg.sift sd s1 a b pref (cur :: suff) (o, st)) {found : Bool}
    (hp : SiftPost bg.sift sd st
      (rowRangePoints bg.sift sd a b (sd.chunks[cur]!).wLow (sd.chunks[cur]!).wHigh) (found, s'))
    (hf : (found && bg.sift.check.onePoint) = true) :
    SiftInvariant bg.sift sd s1 a b (ForIn.toList [:sd.numChunks]) [] (some (true, s'), s') := by
  obtain ⟨-, hst, hsize, -, hout, h1⟩ := hv.cont
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc] at hout h1
  obtain ⟨e1, e2⟩ := Output.appendPoints_firstIf_of_found (out := s1.out)
    (R := rowRangePoints bg.sift sd a b
      (min (sd.wLowAll + ((cur + 1) * bg.sift.arraySize : ℕ)) sd.wHighAll) sd.wHighAll) h1 g5 hf
  rw [← hout, ← g4] at e1
  rw [← hpre.1.isRowSetup.rowRangePoints_eq_chunk a b
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)] at e1 e2
  exact ⟨rfl, SiftState.with_survivors_trans hst g1, g2.trans hsize, g3, e1, e2⟩

private theorem siftInvariant_next (hpre : SiftPre bg sd s a b)
    (hc : ForIn.toList [:sd.numChunks] = pref ++ cur :: suff)
    (hv : SiftInvariant bg.sift sd s1 a b pref (cur :: suff) (o, st)) {found : Bool}
    (hp : SiftPost bg.sift sd st
      (rowRangePoints bg.sift sd a b (sd.chunks[cur]!).wLow (sd.chunks[cur]!).wHigh) (found, s'))
    (hf : ¬(found && bg.sift.check.onePoint) = true) :
    SiftInvariant bg.sift sd s1 a b (pref ++ [cur]) suff (none, s') := by
  obtain ⟨-, hst, hsize, -, hout, h1⟩ := hv.cont
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  dsimp only at g1 g2 g3 g4 g5
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc] at hout h1
  obtain ⟨e1, e2⟩ := Output.appendPoints_firstIf_of_not_found (out := s1.out) h1 g5 hf
  rw [← hout, ← g4] at e1
  rw [hpre.1.isRowSetup.rowRangePoints_chunk_succ a b
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hc)] at e1 e2
  have hl : (pref ++ [cur]).length = cur + 1 := by
    simp [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hc]
  exact ⟨SiftState.with_survivors_trans hst g1, g2.trans hsize, g3, hl ▸ e1, hl ▸ e2⟩

private theorem siftInvariant_post_some (hpre : SiftPre bg sd s a b)
    (hrs : RowSetupPost bg.sift sd s a b s1)
    (hv : SiftInvariant bg.sift sd s1 a b (ForIn.toList [:sd.numChunks]) [] (o, st)) {x : Bool}
    {y : SiftState} (ho : o = some (x, y)) :
    y.WF bg sd ∧ y.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint (rowPoints bg.sift sd a b)) ∧
      x = (bg.sift.check.onePoint && !(rowPoints bg.sift sd a b).isEmpty) := by
  subst ho
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hv
  have e : s1.out = s.out := congr(SiftState.out $(hrs.1))
  rw [rowPoints_eq_rowRangePoints, ← e]
  exact ⟨hpre.2.1.of_sift hrs h1 h2 h3, h4, h5⟩

private theorem siftInvariant_post_none (hpre : SiftPre bg sd s a b)
    (hrs : RowSetupPost bg.sift sd s a b s1)
    (hv : SiftInvariant bg.sift sd s1 a b (ForIn.toList [:sd.numChunks]) [] (o, st))
    (ho : o = none) :
    st.WF bg sd ∧ st.out = s.out.appendPoints bg.sift.check
        (firstIf bg.sift.check.onePoint (rowPoints bg.sift sd a b)) ∧
      false = (bg.sift.check.onePoint && !(rowPoints bg.sift sd a b).isEmpty) := by
  subst ho
  obtain ⟨h1, h2, h3, h4, h5⟩ := hv
  dsimp only at h1 h2 h3 h4
  have e : s1.out = s.out := congr(SiftState.out $(hrs.1))
  rw [Std.Legacy.Range.length_toList_zero_start, hpre.1.isRowSetup.min_numChunks] at h4 h5
  rw [rowPoints_eq_rowRangePoints, ← e]
  exact ⟨hpre.2.1.of_sift hrs h1 h2 h3, Output.Searched.post ⟨h4, h5⟩⟩

end Sift

attribute [local irreducible] SiftInvariant SiftPost in
/-- `sift` prints the points of the row `(a, b)` of the first coordinate `0 ≤ a ≤ H`, `|b| ≤ H` and
`b ≥ 1` for `a = 0`, that its sieve finds (`JPoints.rowPoints`): after `row_setup`, the chunks of
the row in order (`JPoints.sift0_spec`), in each the bits of the fill and the masks, the walks of
the first stage, the words left passed to the second stage, the bits left to the third stage, the
test of coprimality and the exact check, `c` increasing; only the first point under `-1`. The flag
returned says whether it stopped at a point under `-1`. -/
@[spec]
theorem sift_spec (bg : BandGlobals) (sd : SiftData) (s : SiftState) (a b : ℤ) :
    ⦃ IsSieveSetup bg sd ∧ s.WF bg sd ∧ 0 ≤ a ∧ a ≤ bg.sift.check.height ∧
      |b| ≤ bg.sift.check.height ∧ (a = 0 → 1 ≤ b) ⦄
    sift bg.sift sd s a b
    ⦃ fun r ↦ r.2.WF bg sd ∧ r.2.out = s.out.appendPoints bg.sift.check
          (firstIf bg.sift.check.onePoint (rowPoints bg.sift sd a b)) ∧
        r.1 = (bg.sift.check.onePoint && !(rowPoints bg.sift sd a b).isEmpty) ⦄ := by
  vcgen [sift] invariants
  · SiftInvariant bg.sift sd s a b
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact sift_rowSetup_pre ‹_›
    | exact siftInvariant_init ‹_› ‹_›
    | exact siftInvariant_post_some ‹_› ‹_› ‹_› ‹_›
    | exact siftInvariant_post_none ‹_› ‹_› ‹_› ‹_›
    | exact sift_sift0_pre ‹_› ‹_› ‹_› ‹_›
    | exact siftInvariant_return ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact siftInvariant_next ‹_› ‹_› ‹_› ‹_› ‹_›

end JPoints

end
