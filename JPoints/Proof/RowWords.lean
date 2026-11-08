/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Rows
public import Std.WP

import JPoints.Proof.Bits
import JPoints.Proof.Constants
import JPoints.Proof.Containers
import JPoints.Proof.VCSimp
import Mathlib.Data.Nat.Prime.Basic
import Std.Tactic.Do

/-!
# The contracts of the words of the rows of the sieve tables

The words of the rows of the sieve tables of the first two stages of `j-points` from the patterns
that `init_sieve` leaves in `help`. The pattern of the row `(a, b)` of a prime `p` is a function
`g` of period `p` on the bits; the row of `help` holds its first `P` bits, for the least multiple
`P = (⌊64 / p⌋ + 1) p` of `p` above `64`, in its words `0, …, ⌊P / 64⌋` (`JPoints.PatternPrefix`),
and word `w ≤ p` of the row of the table is to be its window at the bit `64 w`
(`JPoints.RowWindows`). The words below `⌊P / 64⌋` are copied; the others come from the rotation of
the words of the row of `help` as a ring (`JPoints.RingState`, `JPoints.initSieveRotate_spec`), in
which the word at the cursor holds the `P % 64` bits after the last window written and the others
the following 64 bits each; word `p` repeats word `0` (`JPoints.initSieveRow_spec`). The rows are
written one after the other, each from its pattern, which the rows before it leave in place
(`JPoints.initSieveRows_spec`).

## Main definitions

* `JPoints.SievePeriodInvariant`: the invariant of the loop of `sieve_period`.
* `JPoints.WindowBits`: a word holds bits of a pattern of a period.
* `JPoints.RingState`, `JPoints.RotateArgs`, `JPoints.RotateInvariant`: the ring of the rotation,
  its arguments and the invariant of its loop.
* `JPoints.wordsBit`, `JPoints.PatternPrefix`, `JPoints.RowWindows`: the bits of the words of an
  array, the prefix of a pattern in its words, and words that are the windows of a pattern.
* `JPoints.RowArgs`, `JPoints.RowCopyInvariant`, `JPoints.RowRepeatInvariant`: the arguments of the
  rows of a prime and the invariants of the copies of `init_sieve`.
* `JPoints.HelpPatterns`, `JPoints.RowsInvariant`: the prefixes of the patterns in the rows of
  `help`, and the invariant of the loops over the rows.

## Main statements

* `JPoints.sievePeriod_spec`, `JPoints.sieveRowlen_spec`: the period and the length of a row.
* `JPoints.initSieveRotate_spec`: the rotation writes the windows of every pattern whose ring
  `help` holds.
* `JPoints.initSieveRow_spec`, `JPoints.initSieveRows_spec`: the rows of the table of a prime are
  the windows of the patterns whose prefixes the rows of `help` hold.

## Implementation notes

The contracts are triples of `Std.WP` on the components in `Id`, for `vcgen`, each verification
condition discharged by a lemma stated in its own shape. The pattern of a row, which the program
does not mention, is quantified in the postconditions, as a function `g` of period `p` on the bits
(`g ((s + t) % p)` for bit `t` from the bit `s` on). A word that holds fewer than 64 bits of the
pattern may have the higher bits set where the pattern has them: the word `⌊P / 64⌋` of the row
`(0, 0)` of `help` is all ones. The rotation needs of the prime only that `P` is a multiple of `p`
with `P % 64 ≠ 0`, which holds for an odd `p`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints

/-! ### The length of a row -/

/-- The invariant of the loop of `JPoints.sievePeriod` for a period `p ≥ 1`: the period stays `p`,
since the loop does not run. -/
def SievePeriodInvariant (p : ℕ) : Std.WP.WhileInvariant ℕ Prop :=
  .mk fun _ P ↦ P = p

private theorem sievePeriodInvariant_init (p : ℕ) : SievePeriodInvariant p false p := rfl

private theorem SievePeriodInvariant.eq {p P : ℕ} {b : Bool}
    (h : SievePeriodInvariant p b P) : P = p := h

private theorem SievePeriodInvariant.exit {p P mb : ℕ}
    (h : 1 - P = mb ∧ SievePeriodInvariant p false P) :
    SievePeriodInvariant p true P :=
  h.2

/-- The loop of `JPoints.sievePeriod` does not run for `p ≥ 1`. -/
private theorem SievePeriodInvariant.add_of_lt_one {p P mb : ℕ} (hp : 1 ≤ p)
    (h : 1 - P = mb ∧ SievePeriodInvariant p false P) (hP : P < 1) :
    1 - (P + p) < mb ∧ SievePeriodInvariant p false (P + p) :=
  absurd (h.2.eq ▸ hP) (Nat.not_lt.mpr hp)

attribute [local irreducible] SievePeriodInvariant in
/-- `sieve_period(p)` is `p` for `p ≥ 1`, the width of the walk being one word. -/
@[spec]
theorem sievePeriod_spec (p : ℕ) : ⦃ 1 ≤ p ⦄ sievePeriod p ⦃ fun r ↦ r = p ⦄ := by
  vcgen [sievePeriod] invariants
  · SievePeriodInvariant p
  · .ofMeasure fun P : ℕ ↦ 1 - P
  all_goals try vc_simp
  all_goals with_reducible first
    | exact sievePeriodInvariant_init p
    | exact SievePeriodInvariant.eq ‹_›
    | exact SievePeriodInvariant.exit ‹_›
    | exact SievePeriodInvariant.add_of_lt_one ‹_› ‹_› ‹_›

/-- `sieve_rowlen(p)` is `p + 1` for `p ≥ 1`. -/
@[spec]
theorem sieveRowlen_spec (p : ℕ) : ⦃ 1 ≤ p ⦄ sieveRowlen p ⦃ fun r ↦ r = p + 1 ⦄ := by
  vcgen [sieveRowlen]
  exact congr($(‹_›) + 1)

/-! ### Windows of a pattern -/

/-- The word `x` holds the `n` bits of the pattern `g` of period `m` from `s` on: bit `t < n` of `x`
is `g ((s + t) % m)`, and every bit set in `x`, also beyond the first `n`, is one of the
pattern. -/
def WindowBits (g : ℕ → Bool) (m s n : ℕ) (x : UInt64) : Prop :=
  ∀ t, (t < n → x.toBitVec.getLsbD t = g ((s + t) % m)) ∧
    (x.toBitVec.getLsbD t = true → g ((s + t) % m) = true)

private theorem WindowBits.congr_left {g : ℕ → Bool} {m s s' n : ℕ} {x : UInt64}
    (h : WindowBits g m s n x) (hs : s % m = s' % m) : WindowBits g m s' n x := fun t ↦ by
  rw [Nat.add_mod, ← hs, ← Nat.add_mod]
  exact h t

/-- The `k < 64` bits of the pattern from `s` on in `x`, or-ed with the `n` bits from `s + k` on in
`y` shifted left by `k`: the `min (k + n) 64` bits from `s` on. -/
private theorem WindowBits.or_shiftLeft {g : ℕ → Bool} {m s k n : ℕ} {x y : UInt64}
    (hx : WindowBits g m s k x) (hy : WindowBits g m (s + k) n y) (hk : k < 64) :
    WindowBits g m s (min (k + n) 64) (x ||| y <<< UInt64.ofNat k) := fun t ↦ by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.getLsbD_shiftLeft_ofNat _ hk]
  have hxt := hx t
  by_cases ht : k ≤ t
  · have hyt := hy (t - k)
    rw [show s + k + (t - k) = s + t by lia] at hyt
    refine ⟨fun ht' ↦ ?_, fun h ↦ ?_⟩
    · rw [hyt.1 (by lia)] at *
      cases hg : g ((s + t) % m) <;> simp_all
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.elim hxt.2 fun h ↦ hyt.2 h.2
  · simp only [ht, decide_false, Bool.and_false, Bool.false_and, Bool.or_false]
    exact ⟨fun _ ↦ hxt.1 (by lia), hxt.2⟩

/-- The bits from `s` on in `x`, shifted right by `k < 64`: the bits from `s + k` on. -/
theorem WindowBits.shiftRight {g : ℕ → Bool} {m s n k : ℕ} {x : UInt64}
    (h : WindowBits g m s n x) (hk : k < 64) :
    WindowBits g m (s + k) (n - k) (x >>> UInt64.ofNat k) := fun t ↦ by
  rw [UInt64.getLsbD_shiftRight_ofNat _ hk, show s + k + t = s + (k + t) by lia]
  exact ⟨fun ht ↦ (h (k + t)).1 (by lia), (h (k + t)).2⟩

/-! ### The rotation -/

/-- The ring of the words `he + k`, `k ≤ wp`, of `help` in the rotation of `init_sieve` at the bit
`s` of the pattern `g` of period `m`, with the cursor at `a1 ≤ wp`: word `a1` of the ring holds the
`ds` bits from `s` on, and word `(a1 + 1 + k) mod (wp + 1)` the 64 bits from `s + ds + 64 k` on,
for `k < wp`. -/
def RingState (g : ℕ → Bool) (m wp ds s he a1 : ℕ) (help : Array UInt64) : Prop :=
  a1 ≤ wp ∧ WindowBits g m s ds help[he + a1]! ∧
    ∀ k < wp, WindowBits g m (s + ds + 64 * k) 64 help[he + (a1 + 1 + k) % (wp + 1)]!

/-- The word that a step of the ring writes: the 64 bits from `s` on. -/
theorem RingState.out {g : ℕ → Bool} {m wp ds s he a1 : ℕ} {help : Array UInt64}
    (h : RingState g m wp ds s he a1 help) (hwp : 0 < wp) (hds : ds < 64) :
    WindowBits g m s 64
      (help[he + a1]! ||| help[he + if a1 = wp then 0 else a1 + 1]! <<< UInt64.ofNat ds) := by
  obtain ⟨ha1, hcur, hrest⟩ := h
  have hnext := hrest 0 hwp
  rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero, ← Nat.ite_eq_add_one_mod_add_one ha1] at hnext
  have h' := hcur.or_shiftLeft hnext hds
  rwa [Nat.min_eq_right (by lia)] at h'

/-- After a step of the ring, the word at the new cursor `t`, shifted right by `diff = 64 - ds`,
holds the `ds` bits from `s + 64` on. -/
theorem RingState.cur {g : ℕ → Bool} {m wp ds diff s he a1 t : ℕ} {help : Array UInt64}
    (h : RingState g m wp ds s he a1 help) (hwp : 0 < wp) (hds0 : 0 < ds) (hd : ds + diff = 64)
    (hn : he + wp < help.size) (ht : t = (a1 + 1) % (wp + 1)) (hta : a1 ≠ t) (htle : t ≤ wp)
    (x : UInt64) :
    WindowBits g m (s + 64) ds (((help.set! (he + a1) x).set! (he + t)
      ((help.set! (he + a1) x)[he + t]! >>> UInt64.ofNat diff))[he + t]!) := by
  rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!]; lia),
    Array.getElem!_set!_ne _ _ _ _ (by lia)]
  have h0 := h.2.2 0 hwp
  rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero, ← ht] at h0
  have h' := h0.shiftRight (k := diff) (by lia)
  rwa [show 64 - diff = ds by lia, show s + ds + diff = s + 64 by lia] at h'

/-- After a step of the ring, the words after the new cursor `t` hold the 64 bits from
`s + 64 + ds + 64 k` on: the words of the ring before the step moved on by one, the last the word
`x` written, for a ring of a multiple `64 wp + ds` of the period `m`. -/
theorem RingState.rest {g : ℕ → Bool} {m wp ds diff s he a1 t : ℕ} {help : Array UInt64}
    (h : RingState g m wp ds s he a1 help) (hm : m ∣ 64 * wp + ds) (hn : he + wp < help.size)
    (ht : t = (a1 + 1) % (wp + 1)) (hta : a1 ≠ t) {x : UInt64} (hout : WindowBits g m s 64 x) :
    ∀ k < wp, WindowBits g m (s + 64 + ds + 64 * k) 64 (((help.set! (he + a1) x).set! (he + t)
      ((help.set! (he + a1) x)[he + t]! >>> UInt64.ofNat diff))[he + (t + 1 + k) % (wp + 1)]!) := by
  intro k hk
  have ha1 := h.1
  have hidx : (t + 1 + k) % (wp + 1) = (a1 + (k + 2)) % (wp + 1) := by
    rw [ht, Nat.add_assoc, Nat.mod_add_mod]
    exact congr($(show a1 + 1 + (1 + k) = a1 + (k + 2) by lia) % (wp + 1))
  rw [Nat.mod_eq_ite_of_lt_two_mul (a := a1 + 1) (q := wp + 1) (by lia)] at ht
  rw [hidx, Nat.mod_eq_ite_of_lt_two_mul (a := a1 + (k + 2)) (q := wp + 1) (by lia)]
  by_cases hk' : k + 1 < wp
  · rw [Array.getElem!_set!_ne _ _ _ _ (by split <;> split at ht <;> lia),
      Array.getElem!_set!_ne _ _ _ _ (by split <;> lia)]
    have := h.2.2 (k + 1) hk'
    rw [show a1 + 1 + (k + 1) = a1 + (k + 2) by lia,
      Nat.mod_eq_ite_of_lt_two_mul (a := a1 + (k + 2)) (q := wp + 1) (by lia)] at this
    rwa [show s + 64 + ds + 64 * k = s + ds + 64 * (k + 1) by lia]
  · simp only [show wp + 1 ≤ a1 + (k + 2) by lia, ↓reduceIte]
    rw [show a1 + (k + 2) - (wp + 1) = a1 by lia, Array.getElem!_set!_ne _ _ _ _ (by lia),
      Array.getElem!_set!_self _ _ _ (by lia)]
    refine hout.congr_left ?_
    obtain ⟨q, hq⟩ := hm
    rw [show s + 64 + ds + 64 * k = s + m * q by lia, Nat.add_mul_mod_self_left]

/-- A step of the ring of `init_sieve`: the word at the cursor `a1` or-ed with the next word shifted
left by `ds`, the 64 bits from `s` on, the cursor moved on to the next word, and that word shifted
right by `diff = 64 - ds`; for a ring of a multiple `64 wp + ds` of the period `m`, with `0 < wp`
and `0 < ds < 64`: the ring at `s + 64`. -/
private theorem RingState.rotate {g : ℕ → Bool} {m wp ds diff s he a1 : ℕ} {help : Array UInt64}
    (h : RingState g m wp ds s he a1 help) (hm : m ∣ 64 * wp + ds) (hwp : 0 < wp) (hds0 : 0 < ds)
    (hds : ds < 64) (hd : ds + diff = 64) (hn : he + wp < help.size) :
    RingState g m wp ds (s + 64) he (if a1 = wp then 0 else a1 + 1)
      ((help.set! (he + a1) (help[he + a1]! ||| help[he + if a1 = wp then 0 else a1 + 1]! <<<
          UInt64.ofNat ds)).set! (he + if a1 = wp then 0 else a1 + 1)
        ((help.set! (he + a1) (help[he + a1]! ||| help[he + if a1 = wp then 0 else a1 + 1]! <<<
          UInt64.ofNat ds))[he + if a1 = wp then 0 else a1 + 1]! >>> UInt64.ofNat diff)) := by
  have hout := h.out hwp hds
  have ha1 := h.1
  have ht := Nat.ite_eq_add_one_mod_add_one ha1
  generalize hT : (if a1 = wp then 0 else a1 + 1) = t at ht hout ⊢
  have htle : t ≤ wp := by rw [← hT]; split <;> lia
  have hta : a1 ≠ t := by rw [← hT]; split <;> lia
  exact ⟨htle, h.cur hwp hds0 hd hn ht hta htle _, h.rest hm hn ht hta hout⟩

/-- The arguments of the rotation of `init_sieve` for a prime `p` (`JPoints.initSieveRotate`): the
ring of `wp + 1` words of `help` from `he` on, `0 < wp ≤ p`, holds a multiple `64 wp + ds` of `p`
bits, `0 < ds < 64`; `diff = 64 - ds`, `diffMask` the mask of the low `diff` bits; the row of the
table from `si` on and the ring lie within the arrays. -/
structure RotateArgs (tab help : Array UInt64) (p si he wp ds diff : ℕ) (diffMask : UInt64) :
    Prop where
  /-- The ring has a full word. -/
  wp_pos : 0 < wp
  /-- The rotation starts within the row. -/
  wp_le : wp ≤ p
  /-- The last word of the ring is not empty. -/
  ds_pos : 0 < ds
  /-- The last word of the ring is not full. -/
  ds_lt : ds < 64
  /-- The shift right of the rotation. -/
  add_diff : ds + diff = 64
  /-- The mask of the low `diff` bits. -/
  mask : diffMask = (1 <<< UInt64.ofNat diff) - 1
  /-- The ring holds a multiple of the period. -/
  dvd : p ∣ 64 * wp + ds
  /-- The row lies within the table. -/
  tab_size : si + p ≤ tab.size
  /-- The ring lies within `help`. -/
  help_size : he + wp < help.size

/-- A step of the rotation of `init_sieve` for one pattern: from the ring at the bit `64 (wp + k)`
and the words `wp, …, wp + k - 1` of the row at `si` its windows, the ring at the next 64 bits and
word `wp + k` the window at `64 (wp + k)`. -/
private theorem RingState.rotate_windows {g : ℕ → Bool} {p si he wp ds diff k c1 : ℕ}
    {tab help : Array UInt64} (h : RingState g p wp ds (64 * (wp + k)) he c1 help)
    (hw : ∀ w < k, WindowBits g p (64 * (wp + w)) 64 tab[si + (wp + w)]!)
    (hm : p ∣ 64 * wp + ds) (hwp : 0 < wp) (hds0 : 0 < ds) (hds : ds < 64) (hd : ds + diff = 64)
    (hn : he + wp < help.size) (htab : si + (wp + k) < tab.size) :
    RingState g p wp ds (64 * (wp + (k + 1))) he (if c1 = wp then 0 else c1 + 1)
        ((help.set! (he + c1) (help[he + c1]! ||| help[he + if c1 = wp then 0 else c1 + 1]! <<<
            UInt64.ofNat ds)).set! (he + if c1 = wp then 0 else c1 + 1)
          ((help.set! (he + c1) (help[he + c1]! ||| help[he + if c1 = wp then 0 else c1 + 1]! <<<
            UInt64.ofNat ds))[he + if c1 = wp then 0 else c1 + 1]! >>> UInt64.ofNat diff)) ∧
      ∀ w < k + 1, WindowBits g p (64 * (wp + w)) 64 (tab.set! (si + (wp + k))
        (help.set! (he + c1) (help[he + c1]! ||| help[he + if c1 = wp then 0 else c1 + 1]! <<<
          UInt64.ofNat ds))[he + c1]!)[si + (wp + w)]! := by
  have hrot := h.rotate hm hwp hds0 hds hd hn
  rw [show 64 * (wp + k) + 64 = 64 * (wp + (k + 1)) by lia] at hrot
  refine ⟨hrot, fun w hw' ↦ ?_⟩
  rcases (show w = k ∨ w < k by lia) with rfl | hw'
  · rw [Array.getElem!_set!_self _ _ _ htab, Array.getElem!_set!_self _ _ _ (by lia [h.1])]
    exact h.out hwp hds
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact hw w hw'

/-- The invariant of the loop of `JPoints.initSieveRotate` from the table `tab` and the array
`help`, after `k` steps from word `wp` of the row at `si` on: the sizes kept, the cursor within the
ring, the words of the table other than the words `wp, …, wp + k - 1` of the row and the words of
`help` outside the ring at `he` kept; and for every pattern `g` of period `p` whose ring `help`
holds at the bit `64 wp` with the cursor at `wp`, the ring at the bit `64 (wp + k)`, and the words
`wp, …, wp + k - 1` of the row the windows of `g` at their bits. -/
def RotateInvariant (tab help : Array UInt64) (p si he wp ds k : ℕ)
    (st : Array UInt64 × Array UInt64 × ℕ) : Prop :=
  st.1.size = tab.size ∧ st.2.1.size = help.size ∧ st.2.2 ≤ wp ∧
    (∀ j, (j < si + wp ∨ si + wp + k ≤ j) → st.1[j]! = tab[j]!) ∧
    (∀ j, (j < he ∨ he + wp < j) → st.2.1[j]! = help[j]!) ∧
    ∀ g, RingState g p wp ds (64 * wp) he wp help →
      RingState g p wp ds (64 * (wp + k)) he st.2.2 st.2.1 ∧
        ∀ w < k, WindowBits g p (64 * (wp + w)) 64 st.1[si + (wp + w)]!

private theorem rotateInvariant_init (tab help : Array UInt64) (p si he wp ds : ℕ) :
    RotateInvariant tab help p si he wp ds ([] : List ℕ).length (tab, help, wp) :=
  ⟨rfl, rfl, le_rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ h ↦ ⟨by simpa using h, nofun⟩⟩

/-- A step of the rotation, in the shape of the verification condition. -/
private theorem RotateInvariant.append_singleton {tab help : Array UInt64} {p si he wp ds diff : ℕ}
    {diffMask : UInt64} (pre : RotateArgs tab help p si he wp ds diff diffMask)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [wp:p] = pref ++ cur :: suff)
    {st : Array UInt64 × Array UInt64 × ℕ}
    (h : RotateInvariant tab help p si he wp ds pref.length st) :
    RotateInvariant tab help p si he wp ds (pref ++ [cur]).length
      (st.1.set! (si + cur) (st.2.1.set! (he + st.2.2) (st.2.1[he + st.2.2]! |||
          (st.2.1[he + if (st.2.2 == wp) = true then 0 else st.2.2 + 1]! &&& diffMask) <<<
            UInt64.ofNat ds))[he + st.2.2]!,
        (st.2.1.set! (he + st.2.2) (st.2.1[he + st.2.2]! |||
            (st.2.1[he + if (st.2.2 == wp) = true then 0 else st.2.2 + 1]! &&& diffMask) <<<
              UInt64.ofNat ds)).set! (he + if (st.2.2 == wp) = true then 0 else st.2.2 + 1)
          ((st.2.1.set! (he + st.2.2) (st.2.1[he + st.2.2]! |||
              (st.2.1[he + if (st.2.2 == wp) = true then 0 else st.2.2 + 1]! &&& diffMask) <<<
                UInt64.ofNat ds))[he + if (st.2.2 == wp) = true then 0 else st.2.2 + 1]! >>>
            UInt64.ofNat diff),
        if (st.2.2 == wp) = true then 0 else st.2.2 + 1) := by
  obtain ⟨tab', help', c1⟩ := st
  obtain ⟨hs1, hs2, hc, htab, hhelp, hg⟩ := h
  dsimp only at hs1 hs2 hc htab hhelp hg ⊢
  obtain rfl := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hsz := pre.help_size
  have htsz := pre.tab_size
  have hcp := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hwp0 := pre.wp_pos
  simp only [beq_iff_eq, pre.mask,
    UInt64.and_one_shiftLeft_sub_one_shiftLeft _ pre.add_diff pre.ds_pos pre.ds_lt]
  rw [List.length_append, List.length_singleton]
  refine ⟨by simp [hs1], by simp [hs2], by split <;> lia, fun j hj ↦ ?_, fun j hj ↦ ?_,
    fun g hR ↦ (hg g hR).1.rotate_windows (hg g hR).2 pre.dvd hwp0 pre.ds_pos pre.ds_lt
      pre.add_diff (by lia) (by lia)⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), htab j (by lia)]
  · rw [Array.getElem!_set!_ne _ _ _ _ (by split <;> lia), Array.getElem!_set!_ne _ _ _ _ (by lia),
      hhelp j hj]

private theorem RotateInvariant.post {tab help : Array UInt64} {p si he wp ds : ℕ}
    {st : Array UInt64 × Array UInt64 × ℕ}
    (h : RotateInvariant tab help p si he wp ds (ForIn.toList [wp:p]).length st) :
    st.1.size = tab.size ∧ st.2.1.size = help.size ∧
      (∀ j, (j < si + wp ∨ si + p ≤ j) → st.1[j]! = tab[j]!) ∧
      (∀ j, (j < he ∨ he + wp < j) → st.2.1[j]! = help[j]!) ∧
      ∀ g, RingState g p wp ds (64 * wp) he wp help →
        ∀ w, wp ≤ w → w < p → WindowBits g p (64 * w) 64 st.1[si + w]! := by
  rw [Std.Legacy.Range.length_toList] at h
  obtain ⟨hs1, hs2, -, htab, hhelp, hg⟩ := h
  refine ⟨hs1, hs2, fun j hj ↦ htab j (by lia), hhelp, fun g hR w hw hwp' ↦ ?_⟩
  have := (hg g hR).2 (w - wp) (by lia)
  rwa [show wp + (w - wp) = w by lia] at this

attribute [local irreducible] RotateInvariant in
/-- The rotation of `init_sieve` writes the words `wp, …, p - 1` of the row of the table at `si`
from the ring of `help` at `he`: for every pattern `g` of period `p` whose ring `help` holds at the
bit `64 wp` with the cursor at `wp` (`JPoints.RingState`), word `w` of the row is the window of `g`
at the bit `64 w`. It changes no other word of the table and no word of `help` outside the
ring. -/
@[spec]
theorem initSieveRotate_spec (tab help : Array UInt64) (p si he wp ds diff : ℕ)
    (diffMask : UInt64) :
    ⦃ RotateArgs tab help p si he wp ds diff diffMask ⦄
    initSieveRotate tab help p si he wp ds diff diffMask
    ⦃ fun r ↦ r.1.size = tab.size ∧ r.2.size = help.size ∧
        (∀ j, (j < si + wp ∨ si + p ≤ j) → r.1[j]! = tab[j]!) ∧
        (∀ j, (j < he ∨ he + wp < j) → r.2[j]! = help[j]!) ∧
        ∀ g, RingState g p wp ds (64 * wp) he wp help →
          ∀ w, wp ≤ w → w < p → WindowBits g p (64 * w) 64 r.1[si + w]! ⦄ := by
  vcgen [initSieveRotate] invariants
  · fun pref _ st ↦ RotateInvariant tab help p si he wp ds pref.length st
  all_goals with_reducible first
    | exact rotateInvariant_init tab help p si he wp ds
    | exact RotateInvariant.post ‹_›
    | exact RotateInvariant.append_singleton ‹_› ‹_› ‹_›

/-! ### The bits of the words of an array -/

/-- Bit `i` of the words of `xs` from `o` on: bit `i % 64` of word `o + i / 64`. -/
def wordsBit (xs : Array UInt64) (o i : ℕ) : Bool := xs[o + i / 64]!.toBitVec.getLsbD (i % 64)

private theorem wordsBit_mul_add {xs : Array UInt64} {o w t : ℕ} (ht : t < 64) :
    wordsBit xs o (64 * w + t) = xs[o + w]!.toBitVec.getLsbD t := by
  rw [wordsBit, show (64 * w + t) / 64 = w by lia, show (64 * w + t) % 64 = t by lia]

/-- The first `L` words of `xs` from `o` on hold the first `P` bits of the pattern `g` of period
`m`: bit `i < P` is `g (i % m)`, and every bit `i < 64 L` that is set is one of the pattern. -/
def PatternPrefix (g : ℕ → Bool) (m P L : ℕ) (xs : Array UInt64) (o : ℕ) : Prop :=
  ∀ i < 64 * L, (i < P → wordsBit xs o i = g (i % m)) ∧ (wordsBit xs o i = true → g (i % m) = true)

/-- The words `w < L` of `xs` from `o` on are the windows of the pattern `g` of period `m`, word `w`
its bits `64 w, …, 64 w + 63`. -/
def RowWindows (g : ℕ → Bool) (m L : ℕ) (xs : Array UInt64) (o : ℕ) : Prop :=
  ∀ w < L, WindowBits g m (64 * w) 64 xs[o + w]!

/-- Word `w < L` of a prefix of `P` bits of the pattern holds its `n ≤ 64` bits from `64 w` on, for
`64 w + n ≤ P`. -/
private theorem PatternPrefix.windowBits {g : ℕ → Bool} {m P L : ℕ} {xs : Array UInt64} {o : ℕ}
    (h : PatternPrefix g m P L xs o) {w n : ℕ} (hw : w < L) (hn : 64 * w + n ≤ P) (hn64 : n ≤ 64) :
    WindowBits g m (64 * w) n xs[o + w]! := fun t ↦ by
  by_cases ht : t < 64
  · have := h (64 * w + t) (by lia)
    rw [wordsBit_mul_add ht] at this
    exact ⟨fun htn ↦ this.1 (by lia), this.2⟩
  · rw [BitVec.getLsbD_of_ge _ _ (by lia)]
    exact ⟨fun htn ↦ absurd htn (by lia), nofun⟩

/-- A prefix of `P = 64 wp + ds` bits of the pattern in the words `0, …, wp`, for a multiple `P` of
the period, is the ring of the rotation at the bit `64 wp` with the cursor at `wp`. -/
private theorem PatternPrefix.ringState {g : ℕ → Bool} {m P wp ds : ℕ} {xs : Array UInt64} {o : ℕ}
    (h : PatternPrefix g m P (wp + 1) xs o) (hP : P = 64 * wp + ds) (hds : ds ≤ 64)
    (hm : m ∣ P) : RingState g m wp ds (64 * wp) o wp xs := by
  refine ⟨le_rfl, h.windowBits (by lia) (by lia) hds, fun k hk ↦ ?_⟩
  rw [show (wp + 1 + k) % (wp + 1) = k by rw [Nat.add_comm, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by lia)]]
  refine (h.windowBits (by lia) (by lia) le_rfl).congr_left ?_
  obtain ⟨q, hq⟩ := hm
  rw [show 64 * wp + ds + 64 * k = 64 * k + m * q by lia, Nat.add_mul_mod_self_left]

theorem PatternPrefix.of_eq {g : ℕ → Bool} {m P L : ℕ} {xs xs' : Array UInt64} {o : ℕ}
    (h : PatternPrefix g m P L xs o) (heq : ∀ w < L, xs'[o + w]! = xs[o + w]!) :
    PatternPrefix g m P L xs' o := fun i hi ↦ by
  have := h i hi
  rwa [wordsBit, ← heq _ (by lia), ← wordsBit] at this

theorem RowWindows.of_eq {g : ℕ → Bool} {m L : ℕ} {xs xs' : Array UInt64} {o : ℕ}
    (h : RowWindows g m L xs o) (heq : ∀ w < L, xs'[o + w]! = xs[o + w]!) :
    RowWindows g m L xs' o := fun w hw ↦ heq w hw ▸ h w hw

/-! ### The words of the ring of a prime -/

/-- The number of full words of the ring of `init_sieve` for the prime `p`, `wp = p1 >> LONG_SHIFT`
for `p1 = (LONG_LENGTH / p + 1) p`. -/
local notation:max "ringWords " p:max => ((longLength / p + 1) * p) >>> longShift

/-- The number of bits of the last word of the ring of `init_sieve` for the prime `p`,
`diff_shift = p1 & LONG_MASK` for `p1 = (LONG_LENGTH / p + 1) p`. -/
local notation:max "ringBits " p:max => ((longLength / p + 1) * p) &&& longMask

-- For an odd `p > 1`, the multiple `(⌊64 / p⌋ + 1) p` of `p` is not a multiple of `64`: `64`,
-- prime to `p`, would divide `⌊64 / p⌋ + 1`, which lies between `1` and `63`.
private theorem div_add_one_mul_mod_ne_zero {p : ℕ} (hp : p % 2 = 1) (hp1 : 1 < p) :
    (64 / p + 1) * p % 64 ≠ 0 := fun h ↦ by
  have hc : Nat.Coprime (2 ^ 6) p :=
    Nat.Coprime.pow_left 6 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp))
  have := Nat.le_of_dvd (Nat.succ_pos _) (hc.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h))
  lia [Nat.div_le_div_left hp1 (show 0 < 2 by lia) (a := 64)]

-- The ring has fewer words than a row of `help`.
private theorem div_add_one_mul_div_lt_helpWidth {p : ℕ} (hp : p ≤ maxTablePrime) :
    (64 / p + 1) * p / 64 < helpWidth := by
  rw [helpWidth, longLength]
  lia [Nat.div_add_one_mul_le 64 p]

private theorem div_add_one_mul_div_eq (p : ℕ) : (64 / p + 1) * p / 64 = ringWords p := by
  simp only [shiftRight_longShift, longLength]

private theorem div_add_one_mul_eq (p : ℕ) :
    (64 / p + 1) * p = 64 * ringWords p + ringBits p := by
  simp only [shiftRight_longShift, and_longMask, longLength]
  lia

/-- The arguments of the rows of the table of a prime `p` in `init_sieve`: an odd `p ≥ 3` of at
most `MAX_TABLE_PRIME`, a table of `p * p` rows of `p + 1` words, and `help` with its rows of
`JPoints.helpWidth` words for the classes modulo `MAX_TABLE_PRIME`. -/
structure RowArgs (tab help : Array UInt64) (p : ℕ) : Prop where
  /-- The prime is at least `3`. -/
  three_le : 3 ≤ p
  /-- The prime is odd. -/
  odd : p % 2 = 1
  /-- The prime has a sieve table. -/
  le_maxTablePrime : p ≤ maxTablePrime
  /-- The size of the table. -/
  size_tab : tab.size = p * p * (p + 1)
  /-- The size of `help`. -/
  size_help : help.size = maxTablePrime * maxTablePrime * helpWidth

theorem RowArgs.one_le {tab help : Array UInt64} {p a b : ℕ}
    (h : RowArgs tab help p ∧ a < p ∧ b < p) : 1 ≤ p :=
  le_trans (by decide) h.1.three_le

private theorem RowArgs.of_size {tab help tab' help' : Array UInt64} {p : ℕ}
    (h : RowArgs tab help p)
    (htab : tab'.size = tab.size) (hhelp : help'.size = help.size) : RowArgs tab' help' p :=
  ⟨h.three_le, h.odd, h.le_maxTablePrime, htab ▸ h.size_tab, hhelp ▸ h.size_help⟩

/-- The ring of `init_sieve` for an odd `p ≥ 3` of at most `MAX_TABLE_PRIME` and its words in
`help`: the least multiple `P = (⌊64 / p⌋ + 1) p` of `p` above `64`, `P / 64` full words with
`0 < P / 64 ≤ p` and `P / 64 < JPoints.helpWidth`, and `0 < P % 64` bits in the last word. -/
private theorem rotateArgs_of_rowArgs {tab help t : Array UInt64} {p a b rowlen : ℕ}
    (pre : RowArgs tab help p ∧ a < p ∧ b < p) (hr : rowlen = p + 1) (ht : t.size = tab.size) :
    RotateArgs t help p ((a * p + b) * rowlen) ((a * maxTablePrime + b) * helpWidth) (ringWords p)
      (ringBits p) (longLength - ringBits p)
      ((1 <<< (longLength - ringBits p).toUInt64) - 1) := by
  obtain ⟨⟨hp3, hodd, hpM, hsz, hhsz⟩, ha, hb⟩ := pre
  subst hr
  simp only [shiftRight_longShift, and_longMask, longLength]
  have h64 := Nat.lt_div_add_one_mul 64 (p := p) (by lia)
  have hle := Nat.div_add_one_mul_le 64 p
  have hne := div_add_one_mul_mod_ne_zero hodd (by lia)
  have hlt : (a * maxTablePrime + b) * helpWidth + (64 / p + 1) * p / 64 <
      maxTablePrime * maxTablePrime * helpWidth :=
    Nat.mul_add_mul_add_lt (by lia) (by lia) (div_add_one_mul_div_lt_helpWidth hpM)
  refine ⟨by lia, by lia, by lia, Nat.mod_lt _ (by lia), by lia, rfl, ?_, ?_, by lia⟩
  · rw [Nat.div_add_mod]
    exact Nat.dvd_mul_left p _
  · rw [ht, hsz]
    lia [Nat.mul_add_mul_add_lt ha hb (show p < p + 1 by lia)]

/-- The invariant of the first loop of `JPoints.initSieveRow`, after `k` words: the words
`0, …, k - 1` of the row at `si` of the table copied from the words of `help` at `he`, the other
words and the size of the table kept. -/
def RowCopyInvariant (tab help : Array UInt64) (si he k : ℕ) (t : Array UInt64) : Prop :=
  t.size = tab.size ∧ (∀ j, (j < si ∨ si + k ≤ j) → t[j]! = tab[j]!) ∧
    ∀ c < k, t[si + c]! = help[he + c]!

private theorem rowCopyInvariant_init (tab help : Array UInt64) (si he : ℕ) :
    RowCopyInvariant tab help si he ([] : List ℕ).length tab :=
  ⟨rfl, fun _ _ ↦ rfl, nofun⟩

private theorem RowCopyInvariant.size_eq {tab help t : Array UInt64} {si he k : ℕ}
    (h : RowCopyInvariant tab help si he k t) : t.size = tab.size :=
  h.1

/-- A step of the first loop of `JPoints.initSieveRow`, in the shape of the verification
condition. -/
private theorem RowCopyInvariant.append_singleton {tab help : Array UInt64} {p a b rowlen : ℕ}
    (pre : RowArgs tab help p ∧ a < p ∧ b < p) (hr : rowlen = p + 1) {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:ringWords p] = pref ++ cur :: suff) {t : Array UInt64}
    (h : RowCopyInvariant tab help ((a * p + b) * rowlen) ((a * maxTablePrime + b) * helpWidth)
      pref.length t) :
    RowCopyInvariant tab help ((a * p + b) * rowlen) ((a * maxTablePrime + b) * helpWidth)
      (pref ++ [cur]).length
      (t.set! ((a * p + b) * rowlen + cur) help[(a * maxTablePrime + b) * helpWidth + cur]!) := by
  obtain ⟨⟨hp3, -, -, hsz, -⟩, ha, hb⟩ := pre
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hwp : ringWords p ≤ p := by
    rw [shiftRight_longShift, longLength]
    lia [Nat.div_add_one_mul_le 64 p]
  obtain ⟨h1, h2, h3⟩ := h
  subst hr hc
  rw [List.length_append, List.length_singleton]
  refine ⟨by simp [h1], fun j hj ↦ ?_, fun c hc' ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h2 j (by lia)]
  · rcases (show c = pref.length ∨ c < pref.length by lia) with rfl | hc'
    · rw [Array.getElem!_set!_self _ _ _ (by
        rw [h1, hsz]; exact Nat.mul_add_mul_add_lt ha hb (by lia))]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h3 c hc']

/-- The invariant of the last loop of `JPoints.initSieveRow`, after `k` words: the words
`p, …, p + k - 1` of the row at `si` of the table copied from the words `0, …, k - 1`, the other
words and the size of the table kept. -/
def RowRepeatInvariant (tab : Array UInt64) (p si k : ℕ) (t : Array UInt64) : Prop :=
  t.size = tab.size ∧ (∀ j, (j < si + p ∨ si + p + k ≤ j) → t[j]! = tab[j]!) ∧
    ∀ c < k, t[si + p + c]! = tab[si + c]!

private theorem rowRepeatInvariant_init (tab : Array UInt64) (p si : ℕ) :
    RowRepeatInvariant tab p si ([] : List ℕ).length tab :=
  ⟨rfl, fun _ _ ↦ rfl, nofun⟩

/-- A step of the last loop of `JPoints.initSieveRow`, in the shape of the verification condition:
the table `tab'` after the rotation has the size of the table `t1` after the first loop. -/
private theorem RowRepeatInvariant.append_singleton {tab help : Array UInt64} {p a b rowlen : ℕ}
    (pre : RowArgs tab help p ∧ a < p ∧ b < p) (hr : rowlen = p + 1) {si he k : ℕ}
    {t1 : Array UInt64} (hcopy : RowCopyInvariant tab help si he k t1)
    {tab' : Array UInt64} {R : Prop} (hrot : tab'.size = t1.size ∧ R)
    {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [p:rowlen] = pref ++ cur :: suff) {t : Array UInt64}
    (h : RowRepeatInvariant tab' p ((a * p + b) * rowlen) pref.length t) :
    RowRepeatInvariant tab' p ((a * p + b) * rowlen) (pref ++ [cur]).length
      (t.set! ((a * p + b) * rowlen + cur) t[(a * p + b) * rowlen + cur - p]!) := by
  have hsz : tab'.size = tab.size := hrot.1.trans hcopy.size_eq
  obtain ⟨⟨hp3, -, -, htab, -⟩, ha, hb⟩ := pre
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨h1, h2, h3⟩ := h
  subst hr hc
  have hi := Nat.mul_add_mul_add_lt ha hb (show p + pref.length < p + 1 by lia)
  rw [List.length_append, List.length_singleton]
  refine ⟨by simp [h1], fun j hj ↦ ?_, fun c hc' ↦ ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h2 j (by lia)]
  · rcases (show c = pref.length ∨ c < pref.length by lia) with rfl | hc'
    · rw [Nat.add_assoc, Array.getElem!_set!_self _ _ _ (by rw [h1, hsz, htab]; lia),
        show (a * p + b) * (p + 1) + (p + pref.length) - p = (a * p + b) * (p + 1) + pref.length
          by lia, h2 _ (by lia)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), h3 c hc']

/-- The words `w < p` of the row at `si` of the table after the copies of the first `wp` words of
the row at `he` of `help` (`t1`) and the rotation (`tab'`), for a pattern `g` whose first
`P = 64 wp + ds` bits `help` holds, `P` a multiple of `p`: the windows of `g`. -/
private theorem windowBits_of_rotate {help t1 tab' : Array UInt64} {p si he wp ds : ℕ}
    {g : ℕ → Bool}
    (hP : p ∣ 64 * wp + ds) (hds : ds < 64)
    (hpat : PatternPrefix g p (64 * wp + ds) (wp + 1) help he)
    (hcopy : ∀ c < wp, t1[si + c]! = help[he + c]!)
    (htab : ∀ j, j < si + wp → tab'[j]! = t1[j]!)
    (hrot : RingState g p wp ds (64 * wp) he wp help →
      ∀ w, wp ≤ w → w < p → WindowBits g p (64 * w) 64 tab'[si + w]!) {w : ℕ} (hw : w < p) :
    WindowBits g p (64 * w) 64 tab'[si + w]! := by
  by_cases hww : w < wp
  · rw [htab _ (by lia), hcopy w hww]
    exact hpat.windowBits (by lia) (by lia) le_rfl
  · exact hrot (hpat.ringState rfl hds.le hP) w (by lia) hw

/-- The words `0, …, p` of a row whose words below `p` are the windows of a pattern of period `p`
and whose word `p` repeats word `0`: the windows of the pattern. -/
private theorem rowWindows_of_windowBits {g : ℕ → Bool} {p si : ℕ} {tab t : Array UInt64}
    (hp : 0 < p)
    (hw : ∀ w < p, WindowBits g p (64 * w) 64 tab[si + w]!)
    (htab : ∀ j, j < si + p → t[j]! = tab[j]!) (hrep : t[si + p]! = tab[si]!) :
    RowWindows g p (p + 1) t si := fun w hw' ↦ by
  rcases (show w < p ∨ w = p by lia) with hwp | rfl
  · rw [htab _ (by lia)]
    exact hw w hwp
  · rw [hrep]
    simpa using (hw 0 hp).congr_left (by simp)

/-- The row `(a, b)` of the table of `p` from the copies of the words of the pattern, the rotation
and the copy of word `0` to word `p`, in the shape of the postcondition. -/
private theorem initSieveRow_post {tab help : Array UInt64} {p a b rowlen : ℕ}
    (pre : RowArgs tab help p ∧ a < p ∧ b < p) (hr : rowlen = p + 1) {t1 : Array UInt64}
    (hcopy : RowCopyInvariant tab help ((a * p + b) * rowlen) ((a * maxTablePrime + b) * helpWidth)
      (ForIn.toList [:ringWords p]).length t1)
    {tab' help' : Array UInt64}
    (hrot : tab'.size = t1.size ∧ help'.size = help.size ∧
      (∀ j, (j < (a * p + b) * rowlen + ringWords p ∨ (a * p + b) * rowlen + p ≤ j) →
        tab'[j]! = t1[j]!) ∧
      (∀ j, (j < (a * maxTablePrime + b) * helpWidth ∨
        (a * maxTablePrime + b) * helpWidth + ringWords p < j) → help'[j]! = help[j]!) ∧
      ∀ g, RingState g p (ringWords p) (ringBits p) (64 * ringWords p)
          ((a * maxTablePrime + b) * helpWidth) (ringWords p) help →
        ∀ w, ringWords p ≤ w → w < p → WindowBits g p (64 * w) 64 tab'[(a * p + b) * rowlen + w]!)
    {t3 : Array UInt64}
    (hrep : RowRepeatInvariant tab' p ((a * p + b) * rowlen) (ForIn.toList [p:rowlen]).length t3) :
    t3.size = tab.size ∧ help'.size = help.size ∧
      (∀ j, (j < (a * p + b) * (p + 1) ∨ (a * p + b) * (p + 1) + p < j) → t3[j]! = tab[j]!) ∧
      (∀ j, (j < (a * maxTablePrime + b) * helpWidth ∨
        (a * maxTablePrime + b) * helpWidth + helpWidth ≤ j) → help'[j]! = help[j]!) ∧
      ∀ g, PatternPrefix g p ((64 / p + 1) * p) ((64 / p + 1) * p / 64 + 1) help
          ((a * maxTablePrime + b) * helpWidth) →
        RowWindows g p (p + 1) t3 ((a * p + b) * (p + 1)) := by
  have hargs := rotateArgs_of_rowArgs pre hr hcopy.1
  have hwpp := hargs.wp_le
  have hW := div_add_one_mul_div_lt_helpWidth pre.1.le_maxTablePrime
  subst hr
  obtain ⟨hs1, hs2, htab1, hhelp1, hg⟩ := hrot
  obtain ⟨hs3, htab3, hrep3⟩ := hrep
  obtain ⟨hs0, htab0, hcopy0⟩ := hcopy
  rw [Std.Legacy.Range.length_toList, Nat.add_sub_cancel_left] at htab3 hrep3
  rw [Std.Legacy.Range.length_toList_zero_start] at htab0 hcopy0
  rw [div_add_one_mul_div_eq] at hW
  refine ⟨by rw [hs3, hs1, hs0], hs2, fun j hj ↦ ?_, fun j hj ↦ hhelp1 j (by lia), fun g hpat ↦ ?_⟩
  · rw [htab3 j (by lia), htab1 j (by lia), htab0 j (by lia)]
  rw [div_add_one_mul_div_eq, div_add_one_mul_eq] at hpat
  refine rowWindows_of_windowBits (by lia [pre.1.three_le]) (fun w hw ↦ windowBits_of_rotate
    (div_add_one_mul_eq p ▸ Dvd.intro_left _ rfl) hargs.ds_lt hpat hcopy0
    (fun j hj ↦ htab1 j (.inl hj)) (hg g) hw) (fun j hj ↦ htab3 j (.inl hj)) ?_
  simpa using hrep3 0 (by lia)

attribute [local irreducible] RowCopyInvariant RowRepeatInvariant in
/-- `init_sieve` writes the row `(a, b)` of the table of an odd `p ≥ 3` of at most
`MAX_TABLE_PRIME` from its pattern in the row `(a, b)` of `help`: for every pattern `g` of period
`p` whose first `P = (⌊64 / p⌋ + 1) p` bits the first `⌊P / 64⌋ + 1` words of the row of `help`
hold (`JPoints.PatternPrefix`), the words `0, …, p` of the row of the table are the windows of `g`
(`JPoints.RowWindows`): the words below `⌊P / 64⌋` copied, the others by the rotation of the ring
(`JPoints.initSieveRotate_spec`), and word `p` a copy of word `0`. It changes no other word of the
table and no word of `help` outside the row `(a, b)`. -/
@[spec]
theorem initSieveRow_spec (tab help : Array UInt64) (p a b : ℕ) :
    ⦃ RowArgs tab help p ∧ a < p ∧ b < p ⦄ initSieveRow tab help p a b
    ⦃ fun r ↦ r.1.size = tab.size ∧ r.2.size = help.size ∧
        (∀ j, (j < (a * p + b) * (p + 1) ∨ (a * p + b) * (p + 1) + p < j) → r.1[j]! = tab[j]!) ∧
        (∀ j, (j < (a * maxTablePrime + b) * helpWidth ∨
          (a * maxTablePrime + b) * helpWidth + helpWidth ≤ j) → r.2[j]! = help[j]!) ∧
        ∀ g, PatternPrefix g p ((64 / p + 1) * p) ((64 / p + 1) * p / 64 + 1) help
            ((a * maxTablePrime + b) * helpWidth) →
          RowWindows g p (p + 1) r.1 ((a * p + b) * (p + 1)) ⦄ := by
  vcgen [initSieveRow] invariants
  · fun pref _ t ↦ RowCopyInvariant tab help ((a * p + b) * rowlen)
      ((a * maxTablePrime + b) * helpWidth) pref.length t
  · fun pref _ t ↦ RowRepeatInvariant tab p ((a * p + b) * rowlen) pref.length t
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact rowCopyInvariant_init _ _ _ _
    | exact rowRepeatInvariant_init _ _ _
    | exact RowCopyInvariant.append_singleton ‹_› ‹_› ‹_› ‹_›
    | exact RowRepeatInvariant.append_singleton ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact rotateArgs_of_rowArgs ‹_› ‹_› (RowCopyInvariant.size_eq ‹_›)
    | exact initSieveRow_post ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact RowArgs.one_le ‹_›

/-! ### The rows of a table -/

/-- The rows `(a, b)`, `a, b < p`, of `help` hold the prefixes of the patterns `G a b` of period
`p` that `init_sieve` rotates: the first `P = (⌊64 / p⌋ + 1) p` bits in the first `⌊P / 64⌋ + 1`
words of the row (`JPoints.PatternPrefix`). -/
def HelpPatterns (G : ℕ → ℕ → ℕ → Bool) (p : ℕ) (help : Array UInt64) : Prop :=
  ∀ a < p, ∀ b < p, PatternPrefix (G a b) p ((64 / p + 1) * p) ((64 / p + 1) * p / 64 + 1) help
    ((a * maxTablePrime + b) * helpWidth)

/-- The invariant of the loops of `JPoints.initSieveRows` from the table `tab` and the array `help`,
with the rows `(a, b)` before `(A, B)` in the order of the loops written (`a < A`, or `a = A` and
`b < B`): the sizes kept, the rows of `help` not yet rotated kept, and for every family `G` of
patterns whose prefixes the rows of `help` hold (`JPoints.HelpPatterns`), the rows of the table
written the windows of their patterns. -/
def RowsInvariant (tab help : Array UInt64) (p A B : ℕ) (s : Array UInt64 × Array UInt64) :
    Prop :=
  s.1.size = tab.size ∧ s.2.size = help.size ∧
    (∀ a < p, ∀ b < p, (A < a ∨ a = A ∧ B ≤ b) → ∀ w < helpWidth,
      s.2[(a * maxTablePrime + b) * helpWidth + w]! =
        help[(a * maxTablePrime + b) * helpWidth + w]!) ∧
    ∀ G, HelpPatterns G p help → ∀ a < p, ∀ b < p, (a < A ∨ a = A ∧ b < B) →
      RowWindows (G a b) p (p + 1) s.1 ((a * p + b) * (p + 1))

private theorem rowsInvariant_init (tab help : Array UInt64) (p : ℕ) :
    RowsInvariant tab help p ([] : List ℕ).length 0 (tab, help) :=
  ⟨rfl, rfl, fun _ _ _ _ _ _ _ ↦ rfl, fun _ _ _ _ _ _ h ↦ by simp at h⟩

private theorem RowsInvariant.nil_of_length {tab help : Array UInt64} {p : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff) {t h : Array UInt64}
    (hinv : RowsInvariant tab help p pref.length 0 (t, h)) :
    RowsInvariant tab help p cur ([] : List ℕ).length (t, h) := by
  rwa [List.length_nil, ← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]

private theorem RowsInvariant.succ_zero {tab help : Array UInt64} {p : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff) {t h : Array UInt64}
    (hinv : RowsInvariant tab help p cur (ForIn.toList [:p]).length (t, h)) :
    RowsInvariant tab help p (pref ++ [cur]).length 0 (t, h) := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  exact ⟨h1, h2, fun a ha b hb hab ↦ h3 a ha b hb (by lia),
    fun G hG a ha b hb hab ↦ h4 G hG a ha b hb (by lia)⟩

private theorem RowsInvariant.post {tab help : Array UInt64} {p : ℕ} {t h : Array UInt64}
    (hinv : RowsInvariant tab help p (ForIn.toList [:p]).length 0 (t, h)) :
    h.size = help.size ∧ ∀ G, HelpPatterns G p help → ∀ a < p, ∀ b < p,
      RowWindows (G a b) p (p + 1) t ((a * p + b) * (p + 1)) := by
  rw [Std.Legacy.Range.length_toList_zero_start] at hinv
  exact ⟨hinv.2.1, fun G hG a ha b hb ↦ hinv.2.2.2 G hG a ha b hb (.inl ha)⟩

private theorem RowsInvariant.rowArgs {tab help : Array UInt64} {p : ℕ} (pre : RowArgs tab help p)
    {prefA suffA : List ℕ} {A : ℕ} (hlA : ForIn.toList [:p] = prefA ++ A :: suffA)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:p] = pref ++ cur :: suff)
    {t h : Array UInt64} (hinv : RowsInvariant tab help p A pref.length (t, h)) :
    RowArgs t h p ∧ A < p ∧ cur < p :=
  ⟨pre.of_size hinv.1 hinv.2.1, Std.Legacy.Range.lt_of_toList_eq_append_cons hlA,
    Std.Legacy.Range.lt_of_toList_eq_append_cons hl⟩

/-- A row of the loops of `JPoints.initSieveRows`, in the shape of the verification condition: the
row `(A, b)` written by `JPoints.initSieveRow_spec` from its pattern in `help`, which the rows
before it left in place, and the other rows of the table and of `help` kept. -/
private theorem RowsInvariant.append_singleton {tab help : Array UInt64} {p : ℕ}
    (pre : RowArgs tab help p) {prefA suffA : List ℕ} {A : ℕ}
    (hlA : ForIn.toList [:p] = prefA ++ A :: suffA) {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:p] = pref ++ cur :: suff) {t h : Array UInt64}
    (hinv : RowsInvariant tab help p A pref.length (t, h)) {tab' help' : Array UInt64}
    (hrow : tab'.size = t.size ∧ help'.size = h.size ∧
      (∀ j, (j < (A * p + cur) * (p + 1) ∨ (A * p + cur) * (p + 1) + p < j) → tab'[j]! = t[j]!) ∧
      (∀ j, (j < (A * maxTablePrime + cur) * helpWidth ∨
        (A * maxTablePrime + cur) * helpWidth + helpWidth ≤ j) → help'[j]! = h[j]!) ∧
      ∀ g, PatternPrefix g p ((64 / p + 1) * p) ((64 / p + 1) * p / 64 + 1) h
          ((A * maxTablePrime + cur) * helpWidth) →
        RowWindows g p (p + 1) tab' ((A * p + cur) * (p + 1))) :
    RowsInvariant tab help p A (pref ++ [cur]).length (tab', help') := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcp := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hpM := pre.le_maxTablePrime
  have hW := div_add_one_mul_div_lt_helpWidth hpM
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrow
  rw [List.length_append, List.length_singleton]
  refine ⟨r1.trans h1, r2.trans h2, fun a ha b hb hab w hw ↦ ?_, fun G hG a ha b hb hab ↦ ?_⟩
  · exact (r4 _ (Nat.mul_add_mul_add_lt_or_le_of_ne (by lia) (by lia) (by lia) hw)).trans
      (h3 a ha b hb (by lia) w hw)
  · by_cases hab' : a = A ∧ b = cur
    · obtain ⟨rfl, rfl⟩ := hab'
      exact r5 _ ((hG a ha b hb).of_eq fun w hw ↦ h3 a ha b hb (by lia) w (by lia))
    · refine (h4 G hG a ha b hb (by lia)).of_eq fun w hw ↦ r3 _ ?_
      lia [Nat.mul_add_mul_add_lt_or_le_of_ne hb hcp hab' hw]

attribute [local irreducible] RowsInvariant in
/-- `init_sieve` writes every row `(a, b)`, `a, b < p`, of the table of an odd `p ≥ 3` of at most
`MAX_TABLE_PRIME` from its pattern in `help` (`JPoints.initSieveRow_spec`): for every family `G` of
patterns of period `p` whose prefixes the rows of `help` hold (`JPoints.HelpPatterns`), the words
`0, …, p` of the row `(a, b)` of the table are the windows of `G a b`. -/
@[spec]
theorem initSieveRows_spec (tab help : Array UInt64) (p : ℕ) :
    ⦃ RowArgs tab help p ⦄ initSieveRows tab help p
    ⦃ fun r ↦ r.2.size = help.size ∧ ∀ G, HelpPatterns G p help → ∀ a < p, ∀ b < p,
        RowWindows (G a b) p (p + 1) r.1 ((a * p + b) * (p + 1)) ⦄ := by
  vcgen [initSieveRows] invariants
  | inv1 => fun pref _ s ↦ RowsInvariant tab help p pref.length 0 s
  | inv2 _ a _ _ _ _ _ => fun pref _ s ↦ RowsInvariant tab help p a pref.length s
  all_goals try dsimp only at *
  all_goals with_reducible first
    | exact rowsInvariant_init tab help p
    | exact RowsInvariant.nil_of_length ‹_› ‹_›
    | exact RowsInvariant.succ_zero ‹_› ‹_›
    | exact RowsInvariant.post ‹_›
    | exact RowsInvariant.rowArgs ‹_› ‹_› ‹_› ‹_›
    | exact RowsInvariant.append_singleton ‹_› ‹_› ‹_› ‹_› ‹_›

end JPoints

end
