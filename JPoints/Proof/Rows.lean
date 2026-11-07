/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Admits
public import JPoints.Proof.RowWords
public import Mathlib.Data.Nat.Prime.Defs

import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.Reduction
import Std.Tactic.Do

/-!
# The contracts of the sieve tables of the first two stages

The sieve tables that `init_sieve` builds for the sieving primes of the first two stages of
`j-points` are those of the class tests of the tables of the curve (`JPoints.SieveTables.WF`,
`JPoints.CurveTables.admits12`). For each prime `p = prime[n]`, `init_sieve` first writes the
pattern of each row `(a, b)` into the row `(a, b)` of `help`, `kp` bits for the least multiple
`kp = ⌈64 / p⌉ p` of `p` above `64`: the clear sets the words of the rows to `0` and those of the
row `(0, 0)` to all ones (`JPoints.initSieveClear_spec`), the points at infinity set bits of the
rows `(0, b)` (`JPoints.initSieveInfinity_spec`, `JPoints.InfinityBits`) and the exact table of the
third stage bits of the rows `(a, b)` with `a ≠ 0` (`JPoints.initSieveOnJ_spec`, `JPoints.OnJBits`),
each loop or-ing single bits into the words (`JPoints.OrBits`). The bits so set are those of the
classes that the first two stages admit (`JPoints.patternBits_iff`), by the inverses modulo the
prime that `invert` computes and Fermat's little theorem
(`JPoints.mul_mod_eq_mod_iff_eq_mul_refInverse_mod`, in `JPoints.Proof.Reduction`). The rows of the
table are then the windows of these patterns (`JPoints.initSieveRows_spec`), which gives the table
of the prime (`JPoints.initSievePrime_spec`) and, prime by prime, the sieve tables
(`JPoints.SieveInvariant`, for `JPoints.initSieve_spec`).

## Main definitions

* `JPoints.ClearInvariant`, `JPoints.SetOnesInvariant`: the invariants of the clear.
* `JPoints.OrBits`: an array of words is another with bits of its rows set.
* `JPoints.PatternArgs`, `JPoints.RowResidues`: the arguments of the patterns of the rows, and the
  bits that their innermost loops set.
* `JPoints.InfinityBits`, `JPoints.InfinityRows`: the bits of the points at infinity.
* `JPoints.OnJBits`, `JPoints.OnJCols`, `JPoints.OnJRows`: the bits of the exact table of the third
  stage.
* `JPoints.PrimeArgs`: the arguments of the table of a prime.
* `JPoints.SieveInvariant`: the invariant of the loop over the sieving primes.

## Main statements

* `JPoints.initSieveClear_spec`, `JPoints.initSieveInfinity_spec`, `JPoints.initSieveOnJ_spec`:
  the patterns of the rows.
* `JPoints.patternBits_iff`: the bits of the patterns are the classes that the first two stages
  admit.
* `JPoints.initSievePrime_spec`: the table of a prime.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. The loops that set the bits of the patterns
are described relative to the array at their start (`JPoints.OrBits` of the array at the start and
the array of the loop), so that the bits that each loop sets are those of its own iterations; the
invariants of the inner loops name the counters of the outer loops and the array at their own
start. The rows of `help` belong to the pairs `(a, b)` of residues below `MAX_TABLE_PRIME`, the row
`(a, b)` from word `(a MAX_TABLE_PRIME + b) helpWidth` on, so that the rows of a prime
`p ≤ MAX_TABLE_PRIME` are told apart by `Nat.eq_and_eq_of_mul_add_eq_mul_add`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The clear -/

/-- The invariant of the loops of `JPoints.initSieveClear` that clear the rows of `help`, with the
words `w ≤ aa` of the rows `(a, b)`, `a, b < p`, before `(A, B, C)` in the order of the loops
cleared: the size kept, and these words `0`. -/
def ClearInvariant (help : Array UInt64) (p aa A B C : ℕ) (h : Array UInt64) : Prop :=
  h.size = help.size ∧ ∀ a < p, ∀ b < p, ∀ w ≤ aa, (a < A ∨ a = A ∧ (b < B ∨ b = B ∧ w < C)) →
    h[(a * maxTablePrime + b) * helpWidth + w]! = 0

/-- The invariant of the last loop of `JPoints.initSieveClear`, after `k` words: the words `w ≤ aa`
of the rows `(a, b)`, `a, b < p`, of `help` all ones for `a = b = 0` and `w < k`, and `0` for the
others. -/
def SetOnesInvariant (help : Array UInt64) (p aa k : ℕ) (h : Array UInt64) : Prop :=
  h.size = help.size ∧ ∀ a < p, ∀ b < p, ∀ w ≤ aa,
    h[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 ∧ w < k then ~~~0 else 0

private theorem clearInvariant_init (help : Array UInt64) (p aa : ℕ) :
    ClearInvariant help p aa ([] : List ℕ).length 0 0 help :=
  ⟨rfl, fun _ _ _ _ _ _ h ↦ by simp at h⟩

private theorem ClearInvariant.nil_of_length_a {help h : Array UInt64} {p aa : ℕ}
    {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : ClearInvariant help p aa pref.length 0 0 h) :
    ClearInvariant help p aa cur ([] : List ℕ).length 0 h := by
  rwa [List.length_nil, ← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

private theorem ClearInvariant.nil_of_length_b {help h : Array UInt64} {p aa A : ℕ}
    {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : ClearInvariant help p aa A pref.length 0 h) :
    ClearInvariant help p aa A cur ([] : List ℕ).length h := by
  rwa [List.length_nil, ← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

private theorem ClearInvariant.set! {help h : Array UInt64} {p aa A B : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:aa + 1] = pref ++ cur :: suff)
    (hinv : ClearInvariant help p aa A B pref.length h) :
    ClearInvariant help p aa A B (pref ++ [cur]).length
      (h.set! ((A * maxTablePrime + B) * helpWidth + cur) 0) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  obtain ⟨h1, h2⟩ := hinv
  rw [List.length_append, List.length_singleton]
  refine ⟨by rw [Array.size_set!, h1], fun a ha b hb w hw hab ↦ ?_⟩
  by_cases he : (A * maxTablePrime + B) * helpWidth + cur = (a * maxTablePrime + b) * helpWidth + w
  · rw [← he]
    exact Array.getElem!_set!_default h _
  · rw [Array.getElem!_set!_ne _ _ _ _ he]
    exact h2 a ha b hb w hw (by rcases hab with hab | ⟨rfl, hab | ⟨rfl, hab⟩⟩ <;> grind)

private theorem ClearInvariant.succ_b {help h : Array UInt64} {p aa A : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : ClearInvariant help p aa A cur (ForIn.toList [:aa + 1]).length h) :
    ClearInvariant help p aa A (pref ++ [cur]).length 0 h := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  exact ⟨hinv.1, fun a ha b hb w hw hab ↦ hinv.2 a ha b hb w hw (by lia)⟩

private theorem ClearInvariant.succ_a {help h : Array UInt64} {p aa : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : ClearInvariant help p aa cur (ForIn.toList [:p]).length 0 h) :
    ClearInvariant help p aa (pref ++ [cur]).length 0 0 h := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  exact ⟨hinv.1, fun a ha b hb w hw hab ↦ hinv.2 a ha b hb w hw (by lia)⟩

private theorem ClearInvariant.setOnesInvariant {help h : Array UInt64} {p aa : ℕ}
    (hinv : ClearInvariant help p aa (ForIn.toList [:p]).length 0 0 h) :
    SetOnesInvariant help p aa ([] : List ℕ).length h := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  exact ⟨hinv.1, fun a ha b hb w hw ↦ by simpa using hinv.2 a ha b hb w hw (.inl ha)⟩

-- The words `w < JPoints.helpWidth` of the rows `(a, b)` of `help` other than `(0, 0)` lie beyond
-- the words of the row `(0, 0)`.
private theorem eq_zero_and_eq_zero_of_mul_add_mul_add_lt {a b w : ℕ}
    (h : (a * maxTablePrime + b) * helpWidth + w < helpWidth) : a = 0 ∧ b = 0 := by
  have h0 : a * maxTablePrime + b = 0 := by
    by_contra h0
    lia [Nat.le_mul_of_pos_left helpWidth (Nat.pos_of_ne_zero h0)]
  obtain ⟨ha0, rfl⟩ := Nat.add_eq_zero_iff.mp h0
  exact ⟨(Nat.mul_eq_zero.mp ha0).resolve_right
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) three_le_maxTablePrime)), rfl⟩

private theorem SetOnesInvariant.set! {help h : Array UInt64} {p aa : ℕ}
    (pre : aa < helpWidth ∧ helpWidth ≤ help.size) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:aa + 1] = pref ++ cur :: suff)
    (hinv : SetOnesInvariant help p aa pref.length h) :
    SetOnesInvariant help p aa (pref ++ [cur]).length (h.set! cur (~~~0)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2⟩ := hinv
  rw [List.length_append, List.length_singleton]
  refine ⟨by rw [Array.size_set!, h1], fun a ha b hb w hw ↦ ?_⟩
  by_cases he : cur = (a * maxTablePrime + b) * helpWidth + w
  · obtain ⟨rfl, rfl⟩ := eq_zero_and_eq_zero_of_mul_add_mul_add_lt (he ▸ (by lia : cur < helpWidth))
    rw [← he, Array.getElem!_set!_self _ _ _ (by lia)]
    simp only [Nat.zero_mul, Nat.zero_add] at he
    simp [he, hc]
  · rw [Array.getElem!_set!_ne _ _ _ _ he, h2 a ha b hb w hw]
    by_cases hab : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [Nat.zero_mul, Nat.zero_add, true_and] at he ⊢
      split_ifs <;> lia
    · grind

private theorem SetOnesInvariant.post {help h : Array UInt64} {p aa : ℕ}
    (hinv : SetOnesInvariant help p aa (ForIn.toList [:aa + 1]).length h) :
    h.size = help.size ∧ ∀ a < p, ∀ b < p, ∀ w ≤ aa,
      h[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 then ~~~0 else 0 := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  refine ⟨hinv.1, fun a ha b hb w hw ↦ ?_⟩
  rw [hinv.2 a ha b hb w hw]
  simp [show w < aa + 1 by lia]

attribute [local irreducible] ClearInvariant SetOnesInvariant in
/-- The clear of `init_sieve` sets the words `w ≤ aa` of the rows `(a, b)`, `a, b < p`, of `help`
to `0`, and then those of the row `(0, 0)` to all ones, for `aa < JPoints.helpWidth`. -/
@[spec]
theorem initSieveClear_spec (help : Array UInt64) (p aa : ℕ) :
    ⦃ aa < helpWidth ∧ helpWidth ≤ help.size ⦄ initSieveClear help p aa
    ⦃ fun r ↦ r.size = help.size ∧ ∀ a < p, ∀ b < p, ∀ w ≤ aa,
        r[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 then ~~~0 else 0 ⦄ := by
  vcgen [initSieveClear] invariants
  | inv1 => fun pref _ h ↦ ClearInvariant help p aa pref.length 0 0 h
  | inv2 => fun pref _ h ↦ SetOnesInvariant help p aa pref.length h
  | inv3 _ a _ _ _ _ => fun pref _ h ↦ ClearInvariant help p aa a pref.length 0 h
  | inv4 _ a _ _ _ _ _ b _ _ _ _ => fun pref _ h ↦ ClearInvariant help p aa a b pref.length h
  all_goals with_reducible first
    | exact clearInvariant_init help p aa
    | exact ClearInvariant.nil_of_length_a ‹_› ‹_›
    | exact ClearInvariant.nil_of_length_b ‹_› ‹_›
    | exact ClearInvariant.set! ‹_› ‹_›
    | exact ClearInvariant.succ_b ‹_› ‹_›
    | exact ClearInvariant.succ_a ‹_› ‹_›
    | exact ClearInvariant.setOnesInvariant ‹_›
    | exact SetOnesInvariant.set! ‹_› ‹_› ‹_›
    | exact SetOnesInvariant.post ‹_›

/-! ### Bits set in the rows -/

/-- `help'` is `help` with the bits of `S` set in the rows `(a, b)`, `a, b < p`: the two arrays have
the size of `help` in `init_sieve`, and bit `i < 64 helpWidth` of the row `(a, b)` of `help'`, from
word `(a MAX_TABLE_PRIME + b) helpWidth` on (`JPoints.wordsBit`), is set exactly when it is set in
`help` or `S a b i` holds. -/
def OrBits (help help' : Array UInt64) (p : ℕ) (S : ℕ → ℕ → ℕ → Prop) : Prop :=
  help.size = maxTablePrime * maxTablePrime * helpWidth ∧
    help'.size = maxTablePrime * maxTablePrime * helpWidth ∧
    ∀ a < p, ∀ b < p, ∀ i < 64 * helpWidth,
      (wordsBit help' ((a * maxTablePrime + b) * helpWidth) i = true ↔
        wordsBit help ((a * maxTablePrime + b) * helpWidth) i = true ∨ S a b i)

theorem OrBits.self {help : Array UInt64} {p : ℕ} {S : ℕ → ℕ → ℕ → Prop}
    (hsz : help.size = maxTablePrime * maxTablePrime * helpWidth)
    (hS : ∀ a < p, ∀ b < p, ∀ i < 64 * helpWidth, ¬S a b i) : OrBits help help p S :=
  ⟨hsz, hsz, fun a ha b hb i hi ↦ by simp [hS a ha b hb i hi]⟩

theorem OrBits.trans {h0 h1 h2 : Array UInt64} {p : ℕ} {S S' : ℕ → ℕ → ℕ → Prop}
    (h : OrBits h0 h1 p S) (h' : OrBits h1 h2 p S') :
    OrBits h0 h2 p fun a b i ↦ S a b i ∨ S' a b i :=
  ⟨h.1, h'.2.1, fun a ha b hb i hi ↦ by
    rw [h'.2.2 a ha b hb i hi, h.2.2 a ha b hb i hi, or_assoc]⟩

theorem OrBits.congr {h0 h1 : Array UInt64} {p : ℕ} {S S' : ℕ → ℕ → ℕ → Prop}
    (h : OrBits h0 h1 p S) (hS : ∀ a < p, ∀ b < p, ∀ i < 64 * helpWidth, (S a b i ↔ S' a b i)) :
    OrBits h0 h1 p S' :=
  ⟨h.1, h.2.1, fun a ha b hb i hi ↦ by rw [h.2.2 a ha b hb i hi, hS a ha b hb i hi]⟩

/-- The word of bit `i < 64 helpWidth` of the row `(a, b)`, `a, b < p ≤ MAX_TABLE_PRIME`, of `help`
or-ed with the word of that bit: bit `i` of the row set. -/
private theorem OrBits.set!_or {help : Array UInt64} {p a b i : ℕ}
    (hsize : help.size = maxTablePrime * maxTablePrime * helpWidth) (hp : p ≤ maxTablePrime)
    (ha : a < p) (hb : b < p) (hi : i < 64 * helpWidth) :
    OrBits help (help.set! ((a * maxTablePrime + b) * helpWidth + i / 64)
        (help[(a * maxTablePrime + b) * helpWidth + i / 64]! ||| 1 <<< (i % 64).toUInt64)) p
      fun a' b' i' ↦ a' = a ∧ b' = b ∧ i' = i := by
  refine ⟨hsize, (Array.size_set! ..).trans hsize, fun a' ha' b' hb' i' hi' ↦ ?_⟩
  have hW : i / 64 < helpWidth := by lia
  have hW' : i' / 64 < helpWidth := by lia
  simp only [wordsBit]
  by_cases he : (a * maxTablePrime + b) * helpWidth + i / 64 =
    (a' * maxTablePrime + b') * helpWidth + i' / 64
  · obtain ⟨h1, h2⟩ := Nat.eq_and_eq_of_mul_add_eq_mul_add hW hW' he
    obtain ⟨rfl, rfl⟩ := Nat.eq_and_eq_of_mul_add_eq_mul_add (by lia) (by lia) h1
    have hj : (a * maxTablePrime + b) * helpWidth + i / 64 < help.size :=
      Nat.lt_of_lt_of_eq (Nat.mul_add_mul_add_lt (by lia) (by lia) hW) hsize.symm
    rw [← he, Array.getElem!_set!_self _ _ _ hj, Nat.toUInt64_eq,
      UInt64.getLsbD_or_one_shiftLeft _ (by lia)]
    simp only [Bool.or_eq_true, decide_eq_true_eq, true_and]
    exact or_congr_right ⟨fun h ↦ by lia, fun h ↦ by rw [h]⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ he]
    refine (or_iff_left fun ⟨h1, h2, h3⟩ ↦ he ?_).symm
    rw [h1, h2, h3]

/-- The arguments of the patterns of the rows of `init_sieve` for the prime `p` and the multiple
`kp` of `p`: the table `bits` of the words with one bit set, `help` of its size, and
`0 < p ≤ MAX_TABLE_PRIME`, `p ≤ kp ≤ 64 helpWidth`. -/
structure PatternArgs (bits help : Array UInt64) (p kp : ℕ) : Prop where
  /-- The words with one bit set. -/
  bits {k : ℕ} (hk : k < 64) : bits[k]! = 1 <<< k.toUInt64
  /-- The size of `help`. -/
  size_help : help.size = maxTablePrime * maxTablePrime * helpWidth
  /-- The prime is positive. -/
  pos : 0 < p
  /-- The prime has a sieve table. -/
  le_maxTablePrime : p ≤ maxTablePrime
  /-- The pattern holds a period at least. -/
  le_kp : p ≤ kp
  /-- The pattern fits the rows of `help`. -/
  kp_le : kp ≤ 64 * helpWidth

/-- The bits `i₀ + t p`, `t < T`, of the row `(a, b)`: those that the innermost loops of the
patterns of `init_sieve` set. -/
def RowResidues (a b i0 p T a' b' i : ℕ) : Prop := a' = a ∧ b' = b ∧ ∃ t < T, i = i0 + t * p

private theorem OrBits.rowResidues_nil {h0 h : Array UInt64} {p : ℕ} {S : ℕ → ℕ → ℕ → Prop}
    (hinv : OrBits h0 h p S) (a b i0 : ℕ) :
    OrBits h h p (RowResidues a b i0 p ([] : List ℕ).length) :=
  .self hinv.2.1 fun _ _ _ _ _ _ ⟨_, _, _, ht, _⟩ ↦ absurd ht (Nat.not_lt_zero _)

/-- A step of the innermost loops of the patterns of `init_sieve`, in the shape of the verification
condition: bit `i₀ + t p` of the row `(a, b)` set. -/
private theorem OrBits.rowResidues_append_singleton {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {a b i0 : ℕ} (ha : a < p) (hb : b < p) (hi0 : i0 < p)
    {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:(kp - i0 + p - 1) / p] = pref ++ cur :: suff) {h0 h : Array UInt64}
    (hinv : OrBits h0 h p (RowResidues a b i0 p pref.length)) :
    OrBits h0 (h.set! ((a * maxTablePrime + b) * helpWidth + (i0 + cur * p) >>> longShift)
        (h[(a * maxTablePrime + b) * helpWidth + (i0 + cur * p) >>> longShift]! |||
          bits[i0 + cur * p &&& longMask]!)) p
      (RowResidues a b i0 p (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hi := ((Nat.exists_lt_eq_add_mul_iff hi0 pre.le_kp _).mp
    ⟨cur, Std.Legacy.Range.lt_of_toList_eq_append_cons hl, rfl⟩).1
  have := pre.kp_le
  rw [shiftRight_longShift, and_longMask, pre.bits (Nat.mod_lt _ (by decide))]
  refine (hinv.trans (.set!_or hinv.2.1 pre.le_maxTablePrime ha hb (by lia))).congr
    fun a' _ b' _ i' _ ↦ ?_
  rw [List.length_append, List.length_singleton, hc]
  simp only [RowResidues]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, t, ht, h3⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, t, ht, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, t, by lia, h3⟩
    · exact ⟨h1, h2, cur, by lia, h3⟩
  · rcases (show t < cur ∨ t = cur by lia) with ht | rfl
    · exact .inl ⟨h1, h2, t, ht, h3⟩
    · exact .inr ⟨h1, h2, h3⟩

/-! ### The points at infinity -/

/-- The bits of the rows `(0, b)`, `0 < b < p`, for the residues `c < C` with `f(c)` a square
modulo `p = prime[n]`: the bits `i < kp` with `i ≡ b c (mod p)`, those that the loops of the points
at infinity of `init_sieve` set for these `c`. -/
def InfinityBits (ct : CurveTables) (n p kp C a b i : ℕ) : Prop :=
  a = 0 ∧ 0 < b ∧ i < kp ∧ ∃ c < C, ct.isFSquare[n * maxPrimeEven + c]! = true ∧ i % p = b * c % p

/-- The bits of the rows `(0, b)`, `0 < b ≤ B`, for the residue `c`: the bits `i < kp` with
`i ≡ b c (mod p)`. -/
def InfinityRows (p kp c B a b i : ℕ) : Prop :=
  a = 0 ∧ 0 < b ∧ b ≤ B ∧ i < kp ∧ i % p = b * c % p

private theorem orBits_infinityBits_nil {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) (ct : CurveTables) (n : ℕ) :
    OrBits help help p (InfinityBits ct n p kp ([] : List ℕ).length) :=
  .self pre.size_help fun _ _ _ _ _ _ ⟨_, _, _, _, hc, _⟩ ↦ absurd hc (Nat.not_lt_zero _)

private theorem OrBits.infinityBits_post {help h : Array UInt64} {ct : CurveTables} {n p kp : ℕ}
    (hinf : ct.hasInfinity[n]! = true)
    (hinv : OrBits help h p (InfinityBits ct n p kp (ForIn.toList [:p]).length)) :
    OrBits help h p fun a b i ↦ ct.hasInfinity[n]! = true ∧ InfinityBits ct n p kp p a b i := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  exact hinv.congr fun _ _ _ _ _ _ ↦ (and_iff_right hinf).symm

private theorem orBits_infinityBits_of_not {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {ct : CurveTables} {n : ℕ}
    (hinf : ¬ct.hasInfinity[n]! = true) :
    OrBits help help p fun a b i ↦ ct.hasInfinity[n]! = true ∧ InfinityBits ct n p kp p a b i :=
  .self pre.size_help fun _ _ _ _ _ _ h ↦ hinf h.1

private theorem OrBits.infinityBits_append_singleton_of_not {help h : Array UInt64}
    {ct : CurveTables}
    {n p kp : ℕ} {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : OrBits help h p (InfinityBits ct n p kp pref.length))
    (hf : ¬ct.isFSquare[n * maxPrimeEven + cur]! = true) :
    OrBits help h p (InfinityBits ct n p kp (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine hinv.congr fun a _ b _ i _ ↦ ?_
  simp only [InfinityBits, List.length_append, List.length_singleton]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨c, hc', h⟩ ↦ ⟨c, by lia, h⟩, fun ⟨c, hc', h⟩ ↦ ⟨c, ?_, h⟩⟩
  rcases (show c < pref.length ∨ c = cur by lia) with h' | rfl
  · exact h'
  · exact absurd h.1 hf

private theorem OrBits.infinityRows_nil {help h : Array UInt64} {ct : CurveTables} {n p kp : ℕ}
    {C : ℕ} (hinv : OrBits help h p (InfinityBits ct n p kp C)) (c : ℕ) :
    OrBits h h p (InfinityRows p kp c ([] : List ℕ).length) :=
  .self hinv.2.1 fun _ _ _ _ _ _ ⟨_, h1, h2, _⟩ ↦ absurd h2 (by simp; lia)

private theorem OrBits.infinityBits_append_singleton {help h h' : Array UInt64} {ct : CurveTables}
    {n p kp : ℕ} {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : OrBits help h p (InfinityBits ct n p kp pref.length))
    (hf : ct.isFSquare[n * maxPrimeEven + cur]! = true)
    (hrows : OrBits h h' p (InfinityRows p kp cur (ForIn.toList [1:p]).length)) :
    OrBits help h' p (InfinityBits ct n p kp (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList] at hrows
  refine (hinv.trans hrows).congr fun a _ b hb i _ ↦ ?_
  simp only [InfinityBits, InfinityRows, List.length_append, List.length_singleton]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, c, hc', h4⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, h3, c, hc', h4⟩ | ⟨h1, h2, -, h3, h4⟩
    · exact ⟨h1, h2, h3, c, by lia, h4⟩
    · exact ⟨h1, h2, h3, cur, by lia, hf, h4⟩
  · rcases (show c < pref.length ∨ c = cur by lia) with h' | rfl
    · exact .inl ⟨h1, h2, h3, c, h', h4⟩
    · exact .inr ⟨h1, h2, by lia, h3, h4.2⟩

private theorem OrBits.infinityRows_append_singleton {bits help h0 h h' : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {c : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [1:p] = pref ++ cur :: suff)
    (hinv : OrBits h0 h p (InfinityRows p kp c pref.length))
    (hrow : OrBits h h' p (RowResidues 0 cur (cur * c % p) p
      (ForIn.toList [:(kp - cur * c % p + p - 1) / p]).length)) :
    OrBits h0 h' p (InfinityRows p kp c (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList_zero_start] at hrow
  refine (hinv.trans hrow).congr fun a _ b hb i _ ↦ ?_
  simp only [InfinityRows, RowResidues, List.length_append, List.length_singleton,
    Nat.exists_lt_eq_add_mul_iff (Nat.mod_lt _ pre.pos) pre.le_kp]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4, h5⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, rfl, h4, h5⟩
    · exact ⟨h1, h2, by lia, h4, h5⟩
    · exact ⟨h1, by lia, by lia, h4, h5⟩
  · rcases (show b ≤ pref.length ∨ b = cur by lia) with h' | rfl
    · exact .inl ⟨h1, h2, h', h4, h5⟩
    · exact .inr ⟨h1, rfl, h4, h5⟩

/-- A step of the innermost loop of the points at infinity of `init_sieve`, in the shape of the
verification condition: bit `b c mod p + t p` of the row `(0, b)` set. -/
private theorem OrBits.rowResidues_zero_append_singleton {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {prefB suffB : List ℕ} {b : ℕ}
    (hlb : ForIn.toList [1:p] = prefB ++ b :: suffB) {c : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:(kp - b * c % p + p - 1) / p] = pref ++ cur :: suff)
    {h0 h : Array UInt64} (hinv : OrBits h0 h p (RowResidues 0 b (b * c % p) p pref.length)) :
    OrBits h0 (h.set! (b * helpWidth + (b * c % p + cur * p) >>> longShift)
        (h[b * helpWidth + (b * c % p + cur * p) >>> longShift]! |||
          bits[b * c % p + cur * p &&& longMask]!)) p
      (RowResidues 0 b (b * c % p) p (pref ++ [cur]).length) := by
  have := OrBits.rowResidues_append_singleton pre pre.pos
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hlb) (Nat.mod_lt _ pre.pos) hl hinv
  rwa [Nat.zero_mul, Nat.zero_add] at this

attribute [local irreducible] OrBits InfinityBits InfinityRows RowResidues in
/-- The loops of the points at infinity of `init_sieve` for the prime `p = prime[n]` set, in the
rows `(0, b)`, `0 < b < p`, of `help`, the bits `i < kp` with `i ≡ b c (mod p)` for the residues
`c < p` with `f(c)` a square modulo `p`, when the curve has points at infinity modulo `p`
(`JPoints.InfinityBits`), and no others. -/
@[spec]
theorem initSieveInfinity_spec (bits : Array UInt64) (ct : CurveTables) (help : Array UInt64)
    (n p kp : ℕ) :
    ⦃ PatternArgs bits help p kp ⦄ initSieveInfinity bits ct help n p kp
    ⦃ fun r ↦ OrBits help r p fun a b i ↦
        ct.hasInfinity[n]! = true ∧ InfinityBits ct n p kp p a b i ⦄ := by
  vcgen [initSieveInfinity] invariants
  | inv1 => fun pref _ h ↦ OrBits help h p (InfinityBits ct n p kp pref.length)
  | inv2 _ c _ _ hc _ _ => fun pref _ h ↦ OrBits hc h p (InfinityRows p kp c pref.length)
  | inv3 _ c _ _ _ _ _ _ b _ _ hb _ => fun pref _ h ↦
      OrBits hb h p (RowResidues 0 b (b * c % p) p pref.length)
  all_goals with_reducible first
    | exact orBits_infinityBits_nil ‹_› ct n
    | exact OrBits.infinityBits_post ‹_› ‹_›
    | exact orBits_infinityBits_of_not ‹_› ‹_›
    | exact OrBits.infinityBits_append_singleton_of_not ‹_› ‹_› ‹_›
    | exact OrBits.infinityRows_nil ‹_› _
    | exact OrBits.infinityBits_append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact OrBits.rowResidues_nil ‹_› _ _ _
    | exact OrBits.infinityRows_append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact OrBits.rowResidues_zero_append_singleton ‹_› ‹_› ‹_› ‹_›

/-! ### The exact table of the third stage -/

/-- The bits of the rows `(a, b')`, `0 < a < p`, for the classes `(1, b, c)` with `b < B` that the
exact table of the third stage admits modulo `p = prime[n]`: the bits `i < kp` of the row
`(a, a b mod p)` with `i ≡ a c (mod p)`, those that the loops of `init_sieve` over the exact table
set for these `b`. -/
def OnJBits (ct : CurveTables) (n p kp B a b' i : ℕ) : Prop :=
  0 < a ∧ i < kp ∧ ∃ b < B, ∃ c < p,
    ct.isPointOnJ[(n * maxPrimeEven + b) * maxPrimeEven + c]! = true ∧ b' = a * b % p ∧
      i % p = a * c % p

/-- The bits of the rows `(a, b')`, `0 < a < p`, for the classes `(1, b, c)` with `c < C` that the
exact table of the third stage admits modulo `p = prime[n]`: the bits `i < kp` of the row
`(a, a b mod p)` with `i ≡ a c (mod p)`. -/
def OnJCols (ct : CurveTables) (n p kp b C a b' i : ℕ) : Prop :=
  0 < a ∧ i < kp ∧ ∃ c < C, ct.isPointOnJ[(n * maxPrimeEven + b) * maxPrimeEven + c]! = true ∧
    b' = a * b % p ∧ i % p = a * c % p

/-- The bits of the rows `(a, a b mod p)`, `0 < a ≤ A`, for the class `(1, b, c)`: the bits
`i < kp` with `i ≡ a c (mod p)`. -/
def OnJRows (p kp b c A a b' i : ℕ) : Prop :=
  0 < a ∧ a ≤ A ∧ b' = a * b % p ∧ i < kp ∧ i % p = a * c % p

private theorem orBits_onJBits_nil {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) (ct : CurveTables) (n : ℕ) :
    OrBits help help p (OnJBits ct n p kp ([] : List ℕ).length) :=
  .self pre.size_help fun _ _ _ _ _ _ ⟨_, _, _, hb, _⟩ ↦ absurd hb (Nat.not_lt_zero _)

private theorem OrBits.onJBits_post {help h : Array UInt64} {ct : CurveTables} {n p kp : ℕ}
    (hinv : OrBits help h p (OnJBits ct n p kp (ForIn.toList [:p]).length)) :
    OrBits help h p (OnJBits ct n p kp p) := by
  rwa [Std.Legacy.Range.length_toList_zero_start] at hinv

private theorem OrBits.onJCols_nil {help h : Array UInt64} {ct : CurveTables} {n p kp B : ℕ}
    (hinv : OrBits help h p (OnJBits ct n p kp B)) (b : ℕ) :
    OrBits h h p (OnJCols ct n p kp b ([] : List ℕ).length) :=
  .self hinv.2.1 fun _ _ _ _ _ _ ⟨_, _, _, hc, _⟩ ↦ absurd hc (Nat.not_lt_zero _)

private theorem OrBits.onJBits_append_singleton {help h h' : Array UInt64} {ct : CurveTables}
    {n p kp : ℕ} {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : OrBits help h p (OnJBits ct n p kp pref.length))
    (hcols : OrBits h h' p (OnJCols ct n p kp cur (ForIn.toList [:p]).length)) :
    OrBits help h' p (OnJBits ct n p kp (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList_zero_start] at hcols
  refine (hinv.trans hcols).congr fun a _ b' _ i _ ↦ ?_
  simp only [OnJBits, OnJCols, List.length_append, List.length_singleton]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, b, hb, c, hc', h3⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, b, hb, c, hc', h3⟩ | ⟨h1, h2, c, hc', h3⟩
    · exact ⟨h1, h2, b, by lia, c, hc', h3⟩
    · exact ⟨h1, h2, cur, by lia, c, hc', h3⟩
  · rcases (show b < pref.length ∨ b = cur by lia) with h' | rfl
    · exact .inl ⟨h1, h2, b, h', c, hc', h3⟩
    · exact .inr ⟨h1, h2, c, hc', h3⟩

private theorem OrBits.onJCols_append_singleton_of_not {h0 h : Array UInt64} {ct : CurveTables}
    {n p kp b : ℕ} {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : OrBits h0 h p (OnJCols ct n p kp b pref.length))
    (hj : ¬ct.isPointOnJ[(n * maxPrimeEven + b) * maxPrimeEven + cur]! = true) :
    OrBits h0 h p (OnJCols ct n p kp b (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine hinv.congr fun a _ b' _ i _ ↦ ?_
  simp only [OnJCols, List.length_append, List.length_singleton]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨c, hc', h⟩ ↦ ⟨c, by lia, h⟩, fun ⟨c, hc', h⟩ ↦ ⟨c, ?_, h⟩⟩
  rcases (show c < pref.length ∨ c = cur by lia) with h' | rfl
  · exact h'
  · exact absurd h.1 hj

private theorem OrBits.onJRows_nil {h0 h : Array UInt64} {ct : CurveTables} {n p kp b C : ℕ}
    (hinv : OrBits h0 h p (OnJCols ct n p kp b C)) (c : ℕ) :
    OrBits h h p (OnJRows p kp b c ([] : List ℕ).length) :=
  .self hinv.2.1 fun _ _ _ _ _ _ ⟨h1, h2, _⟩ ↦ absurd h2 (by simp; lia)

private theorem OrBits.onJCols_append_singleton {h0 h h' : Array UInt64} {ct : CurveTables}
    {n p kp b : ℕ} {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    (hinv : OrBits h0 h p (OnJCols ct n p kp b pref.length))
    (hj : ct.isPointOnJ[(n * maxPrimeEven + b) * maxPrimeEven + cur]! = true)
    (hrows : OrBits h h' p (OnJRows p kp b cur (ForIn.toList [1:p]).length)) :
    OrBits h0 h' p (OnJCols ct n p kp b (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList] at hrows
  refine (hinv.trans hrows).congr fun a ha b' _ i _ ↦ ?_
  simp only [OnJCols, OnJRows, List.length_append, List.length_singleton]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, c, hc', h3, h4, h5⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, c, hc', h3⟩ | ⟨h1, -, h3, h4, h5⟩
    · exact ⟨h1, h2, c, by lia, h3⟩
    · exact ⟨h1, h4, cur, by lia, hj, h3, h5⟩
  · rcases (show c < pref.length ∨ c = cur by lia) with h' | rfl
    · exact .inl ⟨h1, h2, c, h', h3, h4, h5⟩
    · exact .inr ⟨h1, by lia, h4, h2, h5⟩

private theorem OrBits.onJRows_append_singleton {bits help h0 h h' : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {b c : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [1:p] = pref ++ cur :: suff)
    (hinv : OrBits h0 h p (OnJRows p kp b c pref.length))
    (hrow : OrBits h h' p (RowResidues cur (cur * b % p) (cur * c % p) p
      (ForIn.toList [:(kp - cur * c % p + p - 1) / p]).length)) :
    OrBits h0 h' p (OnJRows p kp b c (pref ++ [cur]).length) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [Std.Legacy.Range.length_toList_zero_start] at hrow
  refine (hinv.trans hrow).congr fun a _ b' _ i _ ↦ ?_
  simp only [OnJRows, RowResidues, List.length_append, List.length_singleton,
    Nat.exists_lt_eq_add_mul_iff (Nat.mod_lt _ pre.pos) pre.le_kp]
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4, h5⟩ ↦ ?_⟩
  · rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨rfl, h3, h4, h5⟩
    · exact ⟨h1, by lia, h3, h4, h5⟩
    · exact ⟨by lia, by lia, h3, h4, h5⟩
  · rcases (show a ≤ pref.length ∨ a = cur by lia) with h' | rfl
    · exact .inl ⟨h1, h', h3, h4, h5⟩
    · exact .inr ⟨rfl, h3, h4, h5⟩

/-- A step of the innermost loop of `init_sieve` over the exact table, in the shape of the
verification condition: bit `a c mod p + t p` of the row `(a, a b mod p)` set. -/
private theorem OrBits.rowResidues_mul_append_singleton {bits help : Array UInt64} {p kp : ℕ}
    (pre : PatternArgs bits help p kp) {b c : ℕ} {prefA suffA : List ℕ} {a : ℕ}
    (hla : ForIn.toList [1:p] = prefA ++ a :: suffA) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:(kp - a * c % p + p - 1) / p] = pref ++ cur :: suff)
    {h0 h : Array UInt64}
    (hinv : OrBits h0 h p (RowResidues a (a * b % p) (a * c % p) p pref.length)) :
    OrBits h0 (h.set! ((a * maxTablePrime + a * b % p) * helpWidth +
          (a * c % p + cur * p) >>> longShift)
        (h[(a * maxTablePrime + a * b % p) * helpWidth + (a * c % p + cur * p) >>> longShift]! |||
          bits[a * c % p + cur * p &&& longMask]!)) p
      (RowResidues a (a * b % p) (a * c % p) p (pref ++ [cur]).length) :=
  OrBits.rowResidues_append_singleton pre (Std.Legacy.Range.lt_of_toList_eq_append_cons hla)
    (Nat.mod_lt _ pre.pos) (Nat.mod_lt _ pre.pos) hl hinv

attribute [local irreducible] OrBits OnJBits OnJCols OnJRows RowResidues in
/-- The loops of `init_sieve` over the exact table of the third stage for the prime `p = prime[n]`
set, in the rows `(a, b')`, `0 < a < p`, of `help`, the bits `i < kp` of the row `(a, a b mod p)`
with `i ≡ a c (mod p)` for the classes `(1, b, c)`, `b, c < p`, that the table admits
(`JPoints.OnJBits`), and no others. -/
@[spec]
theorem initSieveOnJ_spec (bits : Array UInt64) (ct : CurveTables) (help : Array UInt64)
    (n p kp : ℕ) :
    ⦃ PatternArgs bits help p kp ⦄ initSieveOnJ bits ct help n p kp
    ⦃ fun r ↦ OrBits help r p (OnJBits ct n p kp p) ⦄ := by
  vcgen [initSieveOnJ] invariants
  | inv1 => fun pref _ h ↦ OrBits help h p (OnJBits ct n p kp pref.length)
  | inv2 _ b _ _ hb _ => fun pref _ h ↦ OrBits hb h p (OnJCols ct n p kp b pref.length)
  | inv3 _ b _ _ _ _ _ c _ _ hc _ _ => fun pref _ h ↦ OrBits hc h p (OnJRows p kp b c pref.length)
  | inv4 _ b _ _ _ _ _ c _ _ _ _ _ _ a _ _ ha _ => fun pref _ h ↦
      OrBits ha h p (RowResidues a (a * b % p) (a * c % p) p pref.length)
  all_goals with_reducible first
    | exact orBits_onJBits_nil ‹_› ct n
    | exact OrBits.onJBits_post ‹_›
    | exact OrBits.onJCols_nil ‹_› _
    | exact OrBits.onJBits_append_singleton ‹_› ‹_› ‹_›
    | exact OrBits.onJCols_append_singleton_of_not ‹_› ‹_› ‹_›
    | exact OrBits.onJRows_nil ‹_› _
    | exact OrBits.onJCols_append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact OrBits.rowResidues_nil ‹_› _ _ _
    | exact OrBits.onJRows_append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact OrBits.rowResidues_mul_append_singleton ‹_› ‹_› ‹_› ‹_›

/-! ### The classes that the patterns admit -/

/-- The patterns of `init_sieve` in the rows `(0, b)`, `0 < b < p`: when the curve has points at
infinity modulo `p`, the bits `i < kp` with `i ≡ b c (mod p)` for the `c` with `f(c)` a square
modulo `p` are those whose class `(0, b, i)` the first two stages admit. -/
private theorem infinityBits_iff {ct : CurveTables} {n kp : ℕ} (hn : n < numPrimes) {b : ℕ}
    (hb0 : 0 < b) (hb : b < primeTable[n]!) (i : ℕ) :
    (ct.hasInfinity[n]! = true ∧ InfinityBits ct n primeTable[n]! kp primeTable[n]! 0 b i) ↔
      i < kp ∧ ct.admits12 n 0 b i = true := by
  have hp := prime_getElem!_primeTable hn
  have hp0 := hp.pos
  simp only [InfinityBits, CurveTables.admits12, Int.toNat_natCast_emod, Int.zero_emod,
    Int.toNat_zero, Nat.mod_eq_of_lt hb, ↓reduceIte, show (b == 0) = false by simp; lia,
    Bool.false_or, Bool.and_eq_true, true_and, hb0]
  refine ⟨fun ⟨hinf, hi, c, hc, hf, he⟩ ↦ ⟨hi, hinf, ?_⟩, fun ⟨hi, hinf, hf⟩ ↦ ⟨hinf, hi, _,
    Nat.mod_lt _ hp0, hf, ?_⟩⟩
  · rwa [Nat.mod_mul_mod, ← (mul_mod_eq_mod_iff_eq_mul_refInverse_mod hp hb0 hb hc).mp he.symm]
  · exact (((mul_mod_eq_mod_iff_eq_mul_refInverse_mod hp hb0 hb (Nat.mod_lt _ hp0)).mpr
      rfl).trans (Nat.mod_mod _ _)).symm

/-- The patterns of `init_sieve` in the rows `(a, b)`, `0 < a < p`: the bits `i < kp` of the row
`(a, a b' mod p)` with `i ≡ a c (mod p)` for the classes `(1, b', c)` that the exact table admits
are those whose class `(a, b, i)` the first two stages admit. -/
private theorem onJBits_iff {ct : CurveTables} {n kp : ℕ} (hn : n < numPrimes) {a b : ℕ}
    (ha0 : 0 < a)
    (ha : a < primeTable[n]!) (hb : b < primeTable[n]!) (i : ℕ) :
    OnJBits ct n primeTable[n]! kp primeTable[n]! a b i ↔ i < kp ∧ ct.admits12 n a b i = true := by
  have hp := prime_getElem!_primeTable hn
  have hp0 := hp.pos
  have hiff {x y : ℕ} (hx : x < primeTable[n]!) :=
    mul_mod_eq_mod_iff_eq_mul_refInverse_mod (y := y) hp ha0 ha hx
  simp only [OnJBits, CurveTables.admits12, Int.toNat_natCast_emod, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.ne_of_gt ha0, ↓reduceIte, ha0, true_and]
  refine and_congr_right fun _ ↦ ⟨fun ⟨b', hb', c, hc, hj, he, he'⟩ ↦ ?_, fun hj ↦
    ⟨_, Nat.mod_lt _ hp0, _, Nat.mod_lt _ hp0, hj, ?_, ?_⟩⟩
  · obtain rfl := (hiff (y := b) hb').mp (by rw [← he, Nat.mod_eq_of_lt hb])
    obtain rfl := (hiff (y := i) hc).mp he'.symm
    rwa [Nat.mod_mul_mod]
  · exact (((hiff (y := b) (Nat.mod_lt _ hp0)).mpr rfl).trans (Nat.mod_eq_of_lt hb)).symm
  · exact (((hiff (y := i % primeTable[n]!) (Nat.mod_lt _ hp0)).mpr rfl).trans
      (Nat.mod_mod _ _)).symm

/-- The bits that the patterns of `init_sieve` set in the row `(a, b)`, `a, b < p`, for the prime
`p = prime[n]` of the table: every bit of the row `(0, 0)`, and the bits `i < kp` whose class
`(a, b, i)` modulo `p` the first two stages admit (`JPoints.CurveTables.admits12`). -/
theorem patternBits_iff {ct : CurveTables} {n kp : ℕ} (hn : n < numPrimes) {a b : ℕ}
    (ha : a < primeTable[n]!) (hb : b < primeTable[n]!) (i : ℕ) :
    (a = 0 ∧ b = 0 ∨ (ct.hasInfinity[n]! = true ∧
        InfinityBits ct n primeTable[n]! kp primeTable[n]! a b i) ∨
      OnJBits ct n primeTable[n]! kp primeTable[n]! a b i) ↔
      a = 0 ∧ b = 0 ∨ i < kp ∧ ct.admits12 n a b i = true := by
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simp
    · have : ¬OnJBits ct n primeTable[n]! kp primeTable[n]! 0 b i := fun h ↦ absurd h.1 (by lia)
      simp only [infinityBits_iff hn hb0 hb, this, or_false, Nat.ne_of_gt hb0, and_false,
        false_or, Nat.cast_zero]
  · have : ¬(ct.hasInfinity[n]! = true ∧ InfinityBits ct n primeTable[n]! kp primeTable[n]! a b i)
      := fun h ↦ absurd h.2.1 (by lia)
    simp only [onJBits_iff hn ha0 ha hb, this, false_or, Nat.ne_of_gt ha0, false_and]

/-! ### The table of a prime -/

-- An odd `p > 1` does not divide `64`.
private theorem sixty_four_mod_ne_zero {p : ℕ} (hodd : p % 2 = 1) (hp1 : 1 < p) :
    64 % p ≠ 0 := fun h ↦ by
  have hc : Nat.Coprime p (2 ^ 6) :=
    Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd))
  lia [hc.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero h)]

-- `kp = ⌈64 / p⌉ p` of `init_sieve` for an odd `p > 1` is `(⌊64 / p⌋ + 1) p`.
private theorem add_sub_one_div_mul_eq {p : ℕ} (hodd : p % 2 = 1) (hp1 : 1 < p) :
    (64 + p - 1) / p * p = (64 / p + 1) * p := by
  have h := Nat.div_add_mod 64 p
  have hlt := Nat.mod_lt 64 (show 0 < p by lia)
  have hne := sixty_four_mod_ne_zero hodd hp1
  rw [Nat.div_eq_of_lt_le (k := 64 / p + 1) (by rw [Nat.add_one_mul]; lia)
    (by rw [Nat.add_one_mul, Nat.add_one_mul]; lia)]

-- The last word `aa = max(1, p >> LONG_SHIFT)` of the clear of `init_sieve` for an odd `p`.
private theorem one_eq_div_add_one_mul_div {p : ℕ} (hodd : p % 2 = 1)
    (h : (p >>> longShift == 0) = true) : 1 = (64 / p + 1) * p / 64 := by
  rw [beq_iff_eq, shiftRight_longShift] at h
  lia [Nat.lt_div_add_one_mul 64 (p := p) (by lia), Nat.div_add_one_mul_le 64 p]

private theorem shiftRight_eq_div_add_one_mul_div {p : ℕ} (hodd : p % 2 = 1)
    (h : ¬(p >>> longShift == 0) = true) : p >>> longShift = (64 / p + 1) * p / 64 := by
  rw [beq_iff_eq, shiftRight_longShift] at h
  rw [shiftRight_longShift, Nat.div_eq_of_lt (show 64 < p by lia), Nat.zero_add, Nat.one_mul]

/-- The arguments of the table of the prime `prime[n]` in `init_sieve`: the tables of `init_main`
(`JPoints.Tables.WF`), a prime of the table of at most `MAX_TABLE_PRIME`, and `help` of its
size. -/
structure PrimeArgs (t : Tables) (n : ℕ) (help : Array UInt64) : Prop where
  /-- The tables of `init_main`. -/
  tables : t.WF
  /-- A prime of the table. -/
  lt_numPrimes : n < numPrimes
  /-- The prime has a sieve table. -/
  le_maxTablePrime : primeTable[n]! ≤ maxTablePrime
  /-- The size of `help`. -/
  size_help : help.size = maxTablePrime * maxTablePrime * helpWidth

theorem PrimeArgs.three_le {t : Tables} {n : ℕ} {help : Array UInt64} (h : PrimeArgs t n help) :
    3 ≤ primeTable[n]! :=
  three_le_getElem!_primeTable h.lt_numPrimes

theorem PrimeArgs.odd {t : Tables} {n : ℕ} {help : Array UInt64} (h : PrimeArgs t n help) :
    primeTable[n]! % 2 = 1 :=
  Nat.odd_iff.mp ((prime_getElem!_primeTable h.lt_numPrimes).odd_of_ne_two (by lia [h.three_le]))

theorem PrimeArgs.one_le {t : Tables} {n : ℕ} {help : Array UInt64} (h : PrimeArgs t n help) :
    1 ≤ primeTable[n]! :=
  le_trans (by decide) h.three_le

private theorem PrimeArgs.clearArgs_one {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help) : 1 < helpWidth ∧ helpWidth ≤ help.size := by
  have h3 := three_le_maxTablePrime
  refine ⟨by simp [helpWidth], ?_⟩
  rw [h.size_help]
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by lia) (by lia))

private theorem PrimeArgs.clearArgs_shiftRight {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help) :
    primeTable[n]! >>> longShift < helpWidth ∧ helpWidth ≤ help.size := by
  have := h.le_maxTablePrime
  refine ⟨?_, h.clearArgs_one.2⟩
  rw [shiftRight_longShift, helpWidth, longLength]
  lia

private theorem PrimeArgs.patternArgs {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help) {h' : Array UInt64}
    (hsz : h'.size = maxTablePrime * maxTablePrime * helpWidth) :
    PatternArgs t.bits h' primeTable[n]!
      ((longLength + primeTable[n]! - 1) / primeTable[n]! * primeTable[n]!) := by
  have hM := h.le_maxTablePrime
  have := Nat.div_add_one_mul_le 64 primeTable[n]!
  rw [longLength, add_sub_one_div_mul_eq h.odd (by lia [h.three_le])]
  refine ⟨fun hk ↦ h.tables.bits hk, hsz, by lia [h.three_le], hM, ?_, ?_⟩
  · rw [Nat.add_one_mul]
    exact Nat.le_add_left _ _
  · simp only [helpWidth, longLength]
    lia

private theorem PrimeArgs.patternArgs_of_clear {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help) {h' : Array UInt64} {R : Prop} (hc : h'.size = help.size ∧ R) :
    PatternArgs t.bits h' primeTable[n]!
      ((longLength + primeTable[n]! - 1) / primeTable[n]! * primeTable[n]!) :=
  h.patternArgs (hc.1.trans h.size_help)

private theorem PrimeArgs.patternArgs_of_orBits {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help) {h0 h' : Array UInt64} {S : ℕ → ℕ → ℕ → Prop}
    (ho : OrBits h0 h' primeTable[n]! S) :
    PatternArgs t.bits h' primeTable[n]!
      ((longLength + primeTable[n]! - 1) / primeTable[n]! * primeTable[n]!) :=
  h.patternArgs ho.2.1

theorem PrimeArgs.rowArgs {t : Tables} {n : ℕ} {help : Array UInt64} (h : PrimeArgs t n help)
    {rowlen : ℕ} (hr : rowlen = primeTable[n]! + 1) {h0 h' : Array UInt64}
    {S : ℕ → ℕ → ℕ → Prop} (ho : OrBits h0 h' primeTable[n]! S) :
    RowArgs (Array.replicate (primeTable[n]! * primeTable[n]! * rowlen) 0) h' primeTable[n]! :=
  ⟨h.three_le, h.odd, h.le_maxTablePrime, by rw [Array.size_replicate, hr], ho.2.1⟩

/-- `⌈64 / p⌉ p` of `init_sieve` for the prime `p`, `kp = k p` for
`k = (LONG_LENGTH + p - 1) / p`. -/
local notation:max "multipleAbove " p:max => (longLength + p - 1) / p * p

/-- The bits of the rows `(a, b)`, `a, b < p`, of `help` after the clear of `init_sieve`, in its
words `w ≤ aa`: every bit of the row `(0, 0)`, and none of the others. -/
private theorem wordsBit_of_clear {h1 : Array UInt64} {p aa : ℕ}
    (hclear : ∀ a < p, ∀ b < p, ∀ w ≤ aa,
      h1[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 then ~~~0 else 0)
    {a b i : ℕ} (ha : a < p) (hb : b < p) (hi : i / 64 ≤ aa) :
    wordsBit h1 ((a * maxTablePrime + b) * helpWidth) i = decide (a = 0 ∧ b = 0) := by
  rw [wordsBit, hclear a ha b hb _ hi]
  split_ifs with hab
  · rw [UInt64.getLsbD_allOnes, decide_eq_true (Nat.mod_lt i (by decide)), decide_eq_true hab]
  · simp [hab]

/-- The bits of the rows `(a, b)`, `a, b < p`, of `help` that the clear, the points at infinity and
the exact table of the third stage leave for the prime `p = prime[n]` of the table: every bit of the
row `(0, 0)`, and the bits `i < (⌊64 / p⌋ + 1) p` whose class `(a, b, i)` the first two stages
admit (`JPoints.patternBits_iff`). -/
private theorem PrimeArgs.wordsBit_iff {t : Tables} {n : ℕ} {help : Array UInt64}
    (h : PrimeArgs t n help)
    {ct : CurveTables} {aa : ℕ} (haa : aa = (64 / primeTable[n]! + 1) * primeTable[n]! / 64)
    {h1 : Array UInt64}
    (hclear : h1.size = help.size ∧ ∀ a < primeTable[n]!, ∀ b < primeTable[n]!, ∀ w ≤ aa,
      h1[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 then ~~~0 else 0)
    {h2 : Array UInt64} (hinf : OrBits h1 h2 primeTable[n]! fun a b i ↦
      ct.hasInfinity[n]! = true ∧
        InfinityBits ct n primeTable[n]! (multipleAbove primeTable[n]!) primeTable[n]! a b i)
    {h3 : Array UInt64} (honj : OrBits h2 h3 primeTable[n]!
      (OnJBits ct n primeTable[n]! (multipleAbove primeTable[n]!) primeTable[n]!))
    {a b i : ℕ} (ha : a < primeTable[n]!) (hb : b < primeTable[n]!)
    (hi : i < 64 * ((64 / primeTable[n]! + 1) * primeTable[n]! / 64 + 1)) :
    wordsBit h3 ((a * maxTablePrime + b) * helpWidth) i = true ↔
      a = 0 ∧ b = 0 ∨ i < (64 / primeTable[n]! + 1) * primeTable[n]! ∧ ct.admits12 n a b i = true
    := by
  have hW : i < 64 * helpWidth := by
    have := Nat.div_add_one_mul_le 64 primeTable[n]!
    have := h.le_maxTablePrime
    simp only [helpWidth, longLength]
    lia
  rw [honj.2.2 a ha b hb i hW, hinf.2.2 a ha b hb i hW,
    wordsBit_of_clear hclear.2 ha hb (by rw [haa]; lia), decide_eq_true_iff, or_assoc,
    patternBits_iff h.lt_numPrimes ha hb i, longLength,
    add_sub_one_div_mul_eq h.odd (by lia [h.three_le])]

/-- The table of the prime `p = prime[n]` from the patterns that the clear, the points at infinity
and the exact table of the third stage leave in `help` (`JPoints.PrimeArgs.wordsBit_iff`) and its
rows (`JPoints.initSieveRows_spec`): bit `j` of word `w ≤ p` of the row `(a, b)` is the class test
of `(a, b, 64 w + j)` of the first two stages. -/
private theorem PrimeArgs.post {t : Tables} {n : ℕ} {help : Array UInt64} (h : PrimeArgs t n help)
    {ct : CurveTables} {aa : ℕ} (haa : aa = (64 / primeTable[n]! + 1) * primeTable[n]! / 64)
    {h1 : Array UInt64}
    (hclear : h1.size = help.size ∧ ∀ a < primeTable[n]!, ∀ b < primeTable[n]!, ∀ w ≤ aa,
      h1[(a * maxTablePrime + b) * helpWidth + w]! = if a = 0 ∧ b = 0 then ~~~0 else 0)
    {h2 : Array UInt64} (hinf : OrBits h1 h2 primeTable[n]! fun a b i ↦
      ct.hasInfinity[n]! = true ∧
        InfinityBits ct n primeTable[n]! (multipleAbove primeTable[n]!) primeTable[n]! a b i)
    {h3 : Array UInt64} (honj : OrBits h2 h3 primeTable[n]!
      (OnJBits ct n primeTable[n]! (multipleAbove primeTable[n]!) primeTable[n]!))
    {tab help' : Array UInt64}
    (hrows : help'.size = h3.size ∧ ∀ G, HelpPatterns G primeTable[n]! h3 →
      ∀ a < primeTable[n]!, ∀ b < primeTable[n]!, RowWindows (G a b) primeTable[n]!
        (primeTable[n]! + 1) tab ((a * primeTable[n]! + b) * (primeTable[n]! + 1))) :
    help'.size = maxTablePrime * maxTablePrime * helpWidth ∧
      ∀ a < primeTable[n]!, ∀ b < primeTable[n]!, ∀ w ≤ primeTable[n]!, ∀ j < 64,
        tab[(a * primeTable[n]! + b) * (primeTable[n]! + 1) + w]!.toBitVec.getLsbD j =
          ct.admits12 n a b (64 * w + j : ℕ) := by
  have hG : HelpPatterns (fun a b x ↦ ct.admits12 n a b x) primeTable[n]! h3 := by
    intro a ha b hb i hi
    have key := h.wordsBit_iff haa hclear hinf honj ha hb hi
    dsimp only
    rw [CurveTables.admits12_natCast_mod]
    refine ⟨fun hiP ↦ Bool.eq_iff_iff.mpr (key.trans ⟨fun h ↦ ?_, fun h ↦ .inr ⟨hiP, h⟩⟩),
      fun h' ↦ ?_⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨-, h⟩ <;> simp [h]
    · rcases key.mp h' with ⟨rfl, rfl⟩ | ⟨-, h⟩ <;> simp [h]
  exact ⟨hrows.1.trans honj.2.1, fun a ha b hb w hw j hj ↦
    ((hrows.2 _ hG a ha b hb w (by lia) j).1 hj).trans (ct.admits12_natCast_mod n a b _)⟩

attribute [local irreducible] OrBits in
/-- `init_sieve` builds the table of the prime `p = prime[n] ≤ MAX_TABLE_PRIME` of the table from
the tables of `init_main` and of the curve: bit `j` of word `w ≤ p` of the row `(a, b)`,
`a, b < p`, from word `(a p + b) (p + 1)` on, is the class test of `(a, b, 64 w + j)` modulo `p` of
the first two stages of the sieve (`JPoints.CurveTables.admits12`); `help` keeps its size. -/
@[spec]
theorem initSievePrime_spec (t : Tables) (ct : CurveTables) (n : ℕ) (help : Array UInt64) :
    ⦃ PrimeArgs t n help ⦄ initSievePrime t ct n help
    ⦃ fun r ↦ r.2.size = maxTablePrime * maxTablePrime * helpWidth ∧
        ∀ a < primeTable[n]!, ∀ b < primeTable[n]!, ∀ w ≤ primeTable[n]!, ∀ j < 64,
          r.1[(a * primeTable[n]! + b) * (primeTable[n]! + 1) + w]!.toBitVec.getLsbD j =
            ct.admits12 n a b (64 * w + j : ℕ) ⦄ := by
  vcgen [initSievePrime]
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact PrimeArgs.one_le ‹_›
    | exact PrimeArgs.clearArgs_one ‹_›
    | exact PrimeArgs.clearArgs_shiftRight ‹_›
    | exact PrimeArgs.patternArgs_of_clear ‹_› ‹_›
    | exact PrimeArgs.patternArgs_of_orBits ‹_› ‹_›
    | exact PrimeArgs.rowArgs ‹_› ‹_› ‹_›
    | exact PrimeArgs.post ‹_› (one_eq_div_add_one_mul_div (PrimeArgs.odd ‹_›) ‹_›) ‹_› ‹_› ‹_›
        ‹_›
    | exact PrimeArgs.post ‹_› (shiftRight_eq_div_add_one_mul_div (PrimeArgs.odd ‹_›) ‹_›) ‹_›
        ‹_› ‹_› ‹_›

/-! ### The sieve tables -/

/-- The invariant of the loop of `JPoints.initSieve` over the sieving primes of the first two
stages, after the first `k`: `sieve_tab` and `help` keep their sizes, and the tables of these
primes are built (`JPoints.SieveTables.WF`). -/
def SieveInvariant (ct : CurveTables) (pnn : Array ℕ) (k : ℕ)
    (s : Array (Array UInt64) × Array UInt64) : Prop :=
  s.1.size = numPrimes ∧ s.2.size = maxTablePrime * maxTablePrime * helpWidth ∧
    SieveTables.WF ⟨s.1, s.2⟩ ct pnn k

theorem sieveInvariant_init (ct : CurveTables) (pnn : Array ℕ) :
    SieveInvariant ct pnn ([] : List ℕ).length
      (SieveTables.initial.sieveTab, SieveTables.initial.help) :=
  ⟨Array.size_replicate .., Array.size_replicate .., ⟨fun hn ↦ absurd hn (Nat.not_lt_zero _)⟩⟩

theorem SieveInvariant.post {ct : CurveTables} {pnn : Array ℕ} {sp2 : ℕ}
    {sieveTab : Array (Array UInt64)} {help : Array UInt64}
    (h : SieveInvariant ct pnn (ForIn.toList [:sp2]).length (sieveTab, help)) :
    SieveTables.WF { sieveTab, help } ct pnn sp2 := by
  rw [Std.Legacy.Range.length_toList_zero_start] at h
  exact h.2.2

theorem SieveInvariant.primeArgs {t : Tables} {pnn : Array ℕ} {sp2 : ℕ}
    (pre : t.WF ∧ sp2 ≤ numPrimes ∧ (∀ n < sp2, pnn[n]! < numPrimes) ∧
      ∀ n < sp2, sievingPrime pnn n ≤ maxTablePrime)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    {ct : CurveTables} {sieveTab : Array (Array UInt64)} {help : Array UInt64}
    (h : SieveInvariant ct pnn pref.length (sieveTab, help)) : PrimeArgs t pnn[cur]! help :=
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  ⟨pre.1, pre.2.2.1 cur hc, pre.2.2.2 cur hc, h.2.1⟩

/-- A step of the loop of `JPoints.initSieve`, in the shape of the verification condition: the
table of the next sieving prime stored (`JPoints.initSievePrime_spec`). -/
theorem SieveInvariant.append_singleton {t : Tables} {pnn : Array ℕ} {sp2 : ℕ}
    (pre : t.WF ∧ sp2 ≤ numPrimes ∧ (∀ n < sp2, pnn[n]! < numPrimes) ∧
      ∀ n < sp2, sievingPrime pnn n ≤ maxTablePrime)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    {ct : CurveTables} {sieveTab : Array (Array UInt64)} {help : Array UInt64}
    (h : SieveInvariant ct pnn pref.length (sieveTab, help)) {tab help' : Array UInt64}
    (hp : help'.size = maxTablePrime * maxTablePrime * helpWidth ∧
      ∀ a < primeTable[pnn[cur]!]!, ∀ b < primeTable[pnn[cur]!]!, ∀ w ≤ primeTable[pnn[cur]!]!,
        ∀ j < 64,
          tab[(a * primeTable[pnn[cur]!]! + b) * (primeTable[pnn[cur]!]! + 1) + w]!.toBitVec.getLsbD
            j = ct.admits12 pnn[cur]! a b (64 * w + j : ℕ)) :
    SieveInvariant ct pnn (pref ++ [cur]).length (sieveTab.set! cur tab, help') := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, -, ⟨h3⟩⟩ := h
  rw [List.length_append, List.length_singleton]
  refine ⟨by rw [Array.size_set!, h1], hp.1, ⟨fun {n'} hn {a b w j} ha hb hw hj ↦ ?_⟩⟩
  dsimp only
  rcases (show n' < pref.length ∨ n' = cur by lia) with hn' | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact h3 hn' ha hb hw hj
  · rw [Array.getElem!_set!_self _ _ _ (by rw [h1]; lia [pre.2.1])]
    exact hp.2 _ ha _ hb _ hw _ hj

end JPoints

end
