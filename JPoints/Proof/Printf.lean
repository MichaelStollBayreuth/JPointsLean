/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Printf
public import JPoints.Spec.Basic
public import Std.WP

import JPoints.Proof.VCSimp
import Mathlib.Tactic.IntervalCases
import Std.Tactic.Do

/-!
# The text of a point

What `emit_point` and `printf_mpz` print for a point of the curve searched, under an admitted format
of the points: the point of the curve given (`JPoints.backPoint`) under the pieces of the format, by
`printf` (`JPoints.Printf.emitPoint_eq_render`) and by `gmp_printf`
(`JPoints.Printf.run_printfMpz_eq_render`), the latter for a point whose first nonzero coordinate is
positive. The scan of `printf_mpz` makes exactly the length modifier `l` of each conversion of an
admitted format a `Z`, so that `gmp_printf` reads the format that it gives with the same pieces
(`JPoints.Printf.rewriteFormat_spec`, `JPoints.Printf.parseFormat_run_rewriteFormat`): a conversion
is its `%`, flags, width and precision, all characters of the scan (`JPoints.Printf.scanChars`),
then its `l` and its `d`, and the reading of a format takes the characters of the scan alike for `l`
and for `Z` (`JPoints.Printf.readChar_of_mem_scanChars`).

## Main definitions

* `JPoints.Printf.readPrefix`: the state and the pieces after a part of a format.
* `JPoints.Printf.ReadState.InConversion`: the reading inside a conversion, before its length
  modifier.
* `JPoints.Printf.RewriteInvariant`, `JPoints.Printf.RewriteScanInvariant`: the invariants of the
  two loops of `JPoints.Printf.rewriteFormat`.

## Main statements

* `JPoints.Printf.readFormat_append`: the reading of a format, part by part.
* `JPoints.Printf.ReadState.InConversion.exists_readPrefix_eq_length`,
  `JPoints.Printf.exists_readPrefix_percent_eq_length`: the reading of a conversion, alike for `l`
  and `Z`.
* `JPoints.Printf.rewriteFormat_spec`, `JPoints.Printf.parseFormat_run_rewriteFormat`: the format
  that `printf_mpz` gives `gmp_printf` has the pieces of the format of `-f`.
* `JPoints.Printf.emitPoint_eq_render`, `JPoints.Printf.run_printfMpz_eq_render`: the text of a
  point.
* `JPoints.Printf.printLong_eq_toString`, `JPoints.Printf.printMpz_eq_printLong`: a conversion
  without flags, width or precision prints the decimal text.

## Implementation notes

The contract of `JPoints.Printf.rewriteFormat` is proved by `vcgen` with the two invariants, each
verification condition discharged by a lemma in its own shape. The outer invariant splits the copy
`fmt` and the format at the index `i` into a prefix, read alike with `Z` and with `l` into the same
state and pieces, and the same rest; the state is outside a conversion, or after the `l` of one
whose `d` comes next. The character `fmt[k]` that the C code reads with a `NUL` past the end is the
term `if h : k < fmt.size then fmt[k] else '\x00'` of the verification conditions.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace JPoints.Printf

/-! ### Reading a format part by part -/

/-- The state and the pieces after the characters `s` of a format read from the state `st`, for the
length modifier `len` (`JPoints.Printf.readChar`), or `none` when one of them cannot come where it
does: the reading of a part of a format, which `JPoints.Printf.readFormat` completes
(`JPoints.Printf.readFormat_append`). -/
def readPrefix (len : Char) : ReadState → List Char → Option (ReadState × List Piece)
  | st, [] => some (st, [])
  | st, ch :: s => (readChar len st ch).bind fun x ↦
      (readPrefix len x.1 s).map fun y ↦ (y.1, x.2 ++ y.2)

@[simp]
theorem readPrefix_nil (len : Char) (st : ReadState) : readPrefix len st [] = some (st, []) :=
  rfl

theorem readPrefix_cons (len : Char) (st : ReadState) (ch : Char) (s : List Char) :
    readPrefix len st (ch :: s) = (readChar len st ch).bind fun x ↦
      (readPrefix len x.1 s).map fun y ↦ (y.1, x.2 ++ y.2) :=
  rfl

theorem readPrefix_append (len : Char) (st : ReadState) (s t : List Char) :
    readPrefix len st (s ++ t) = (readPrefix len st s).bind fun x ↦
      (readPrefix len x.1 t).map fun y ↦ (y.1, x.2 ++ y.2) := by
  induction s generalizing st with
  | nil => simp
  | cons ch s ih =>
    simp [readPrefix_cons, ih, Option.bind_assoc, Option.map_bind, Option.bind_map,
      Function.comp_def]

@[simp]
theorem readPrefix_singleton (len : Char) (st : ReadState) (ch : Char) :
    readPrefix len st [ch] = readChar len st ch := by
  simp [readPrefix_cons]

theorem readFormat_cons (len : Char) (st : ReadState) (ch : Char) (s : List Char) :
    readFormat len st (ch :: s) = (readChar len st ch).bind fun x ↦
      (readFormat len x.1 s).map (x.2 ++ ·) := by
  simp [readFormat, Option.map_eq_bind]

theorem readFormat_cons_ne_none_iff {len : Char} {st : ReadState} {ch : Char} {s : List Char} :
    readFormat len st (ch :: s) ≠ none ↔
      ∃ x, readChar len st ch = some x ∧ readFormat len x.1 s ≠ none := by
  rw [readFormat_cons]
  cases readChar len st ch <;> simp

/-- The reading of a format, part by part: the pieces of the first part `s` and the state after
it (`JPoints.Printf.readPrefix`), then those of the rest `t` from that state. -/
theorem readFormat_append (len : Char) (st : ReadState) (s t : List Char) :
    readFormat len st (s ++ t) = (readPrefix len st s).bind fun x ↦
      (readFormat len x.1 t).map (x.2 ++ ·) := by
  induction s generalizing st with
  | nil => simp
  | cons ch s ih => simp [readFormat, readPrefix_cons, ih, Option.bind_assoc, Option.map_eq_bind]

/-! ### The characters of the scan of `printf_mpz` -/

theorem scanChars_eq : scanChars =
    ['-', '+', ' ', '#', '\'', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.'] := by
  decide

theorem mem_scanChars_of_isDigit {ch : Char} (h : ch.isDigit) : ch ∈ scanChars := by
  rw [Char.isDigit_iff_toNat] at h
  rw [← Char.ofNat_toNat ch]
  obtain ⟨h1, h2⟩ := h
  generalize ch.toNat = n at *
  simp only [Char.reduceToNat] at h1 h2
  interval_cases n <;> decide

/-- The reading of a format is inside a conversion, before its length modifier: after its `%`, in
its flags, in its width or in its precision. -/
def ReadState.InConversion : ReadState → Prop
  | .flags _ | .width _ | .precision _ => True
  | .text | .length _ => False

/-- Inside a conversion, a character of the scan of `printf_mpz` is read alike for the length
modifiers `l` and `Z`, completes no piece and leaves the reading inside the conversion, where a `%`
cannot come any more. -/
theorem readChar_of_mem_scanChars {st : ReadState} (hst : st.InConversion) {ch : Char}
    (hch : ch ∈ scanChars) :
    readChar 'Z' st ch = readChar 'l' st ch ∧ ∀ x ∈ readChar 'l' st ch,
      x.2 = [] ∧ x.1.InConversion ∧ readChar 'l' x.1 '%' = none := by
  rw [scanChars_eq] at hch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
  cases st <;> simp only [ReadState.InConversion] at hst <;>
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [readChar, readWidth, flagChars, ReadState.InConversion]

/-- Inside a conversion, a character beyond those of the scan of `printf_mpz` that the reading for
`l` takes, other than the `%` of a `%%`, is the length modifier `l`, read as the reading for `Z`
reads `Z`. -/
theorem readChar_of_notMem_scanChars {st : ReadState} (hst : st.InConversion) {ch : Char}
    (hch : ch ∉ scanChars) (hpct : readChar 'l' st '%' = none ∨ ch ≠ '%')
    (h : readChar 'l' st ch ≠ none) :
    ch = 'l' ∧ ∃ c, readChar 'l' st 'l' = some (.length c, []) ∧
      readChar 'Z' st 'Z' = some (.length c, []) := by
  have hd : ¬ch.isDigit := fun hd ↦ hch (mem_scanChars_of_isDigit hd)
  have hf : ch ∉ flagChars := fun hf ↦ hch ((by decide : ∀ c ∈ flagChars, c ∈ scanChars) ch hf)
  have hp : ch ≠ '.' := by rintro rfl; exact hch (by decide)
  cases st <;> simp only [ReadState.InConversion] at hst <;>
    simp_all [readChar, readWidth, flagChars]
  grind

/-! ### The reading of a conversion -/

/-- The characters `body` of the scan of `printf_mpz` and the character after them, read inside a
conversion: for a format that the reading for `l` takes, that character is the length modifier
`l`, and the readings of `body` with `l` and with `Z` reach the same state after their length
modifiers. -/
theorem ReadState.InConversion.exists_readPrefix_eq_length {st : ReadState}
    (hst : st.InConversion) {body rest : List Char} (hbody : ∀ ch ∈ body, ch ∈ scanChars)
    (hrest : ∀ ch ∈ rest.head?, ch ∉ scanChars)
    (hpct : readChar 'l' st '%' = none ∨ (body ++ rest).head? ≠ some '%')
    (h : readFormat 'l' st (body ++ rest) ≠ none) :
    ∃ c rest', rest = 'l' :: rest' ∧ readPrefix 'l' st (body ++ ['l']) = some (.length c, []) ∧
      readPrefix 'Z' st (body ++ ['Z']) = some (.length c, []) ∧
      readFormat 'l' (.length c) rest' ≠ none := by
  induction body generalizing st with
  | nil =>
    obtain _ | ⟨ch, rest⟩ := rest
    · cases st <;> simp_all [readFormat, ReadState.InConversion]
    obtain ⟨x, hx, hr⟩ := readFormat_cons_ne_none_iff.mp h
    obtain ⟨rfl, c, hl, hZ⟩ := readChar_of_notMem_scanChars hst (hrest ch rfl)
      (by simpa using hpct) (by simp [hx])
    obtain rfl : x = (.length c, []) := Option.some.inj (hx.symm.trans hl)
    exact ⟨c, rest, rfl, by simpa using hl, by simpa using hZ, hr⟩
  | cons ch body ih =>
    obtain ⟨hZ, hx⟩ := readChar_of_mem_scanChars hst (hbody ch (.head _))
    obtain ⟨x, hxl, hr⟩ := readFormat_cons_ne_none_iff.mp h
    obtain ⟨hx2, hx1, hpct'⟩ := hx x hxl
    obtain ⟨c, rest', hrest', hl, hz, hr'⟩ :=
      ih hx1 (fun c hc ↦ hbody c (.tail _ hc)) (.inl hpct') hr
    exact ⟨c, rest', hrest', by simp [readPrefix_cons, hxl, hl, hx2],
      by simp [readPrefix_cons, hZ, hxl, hz, hx2], hr'⟩

/-- A conversion of a format that the reading for `l` takes, read from its `%`: after the
characters `body` of the scan of `printf_mpz`, not starting a `%%`, comes its length modifier `l`,
and the readings with `l` and with `Z` reach the same state after their length modifiers. -/
theorem exists_readPrefix_percent_eq_length {body rest : List Char}
    (hbody : ∀ ch ∈ body, ch ∈ scanChars) (hrest : ∀ ch ∈ rest.head?, ch ∉ scanChars)
    (hpct : (body ++ rest).head? ≠ some '%')
    (h : readFormat 'l' .text ('%' :: (body ++ rest)) ≠ none) :
    ∃ c rest', rest = 'l' :: rest' ∧
      readPrefix 'l' .text ('%' :: (body ++ ['l'])) = some (.length c, []) ∧
      readPrefix 'Z' .text ('%' :: (body ++ ['Z'])) = some (.length c, []) ∧
      readFormat 'l' (.length c) rest' ≠ none := by
  obtain ⟨x, hx, hr⟩ := readFormat_cons_ne_none_iff.mp h
  obtain rfl : x = (.flags ⟨[], 0, none⟩, []) := by simpa [readChar] using hx.symm
  obtain ⟨c, rest', hr', hl, hz, hw⟩ := ReadState.InConversion.exists_readPrefix_eq_length
    (st := .flags ⟨[], 0, none⟩) trivial hbody hrest (.inr hpct) hr
  exact ⟨c, rest', hr', by simp [readPrefix_cons, readChar, hl],
    by simp [readPrefix_cons, readChar, hz], hw⟩

/-- Outside a conversion, or after its length modifier, a character other than `%` is read alike
for `l` and for `Z`, and the reading is then outside a conversion. -/
theorem readChar_eq_some_and_fst_eq_text {st : ReadState}
    (hst : st = .text ∨ ∃ c, st = .length c) {ch : Char} (hch : ch ≠ '%')
    {x : ReadState × List Piece} (hx : readChar 'l' st ch = some x) :
    readChar 'Z' st ch = some x ∧ x.1 = .text := by
  rcases hst with rfl | ⟨c, rfl⟩ <;> simp only [readChar, hch, ite_false] at hx ⊢
  · exact ⟨hx, by rw [← Option.some.inj hx]⟩
  · simp only [Option.ite_none_right_eq_some] at hx
    obtain ⟨h, hx⟩ := hx
    simp [h, ← Option.some.inj hx]

theorem eq_text_of_readFormat_percent_ne_none {st : ReadState}
    (hst : st = .text ∨ ∃ c, st = .length c) {s : List Char}
    (h : readFormat 'l' st ('%' :: s) ≠ none) : st = .text := by
  rcases hst with rfl | ⟨c, rfl⟩
  · rfl
  · simp [readFormat_cons, readChar] at h

/-! ### The loops of `printf_mpz` -/

/-- The invariant of the outer loop of `JPoints.Printf.rewriteFormat` on the format `format`, at the
copy `fmt` and the index `i`: the copy and the format split at `i` into prefixes `u` and `v` and the
same rest `w`, the prefix of the copy read with `Z` and that of the format with `l` into the same
state and pieces, outside a conversion or after the length modifier of one, from which the reading
for `l` takes the rest; after the loop, the rest is empty. -/
def RewriteInvariant (format : String) : Std.WP.WhileInvariant (Array Char × ℕ) Prop :=
  .mk fun exit (fmt, i) ↦ ∃ u v w st P, fmt.toList = u ++ w ∧ format.toList = v ++ w ∧
    u.length = i ∧ v.length = i ∧ readPrefix 'Z' .text u = some (st, P) ∧
    readPrefix 'l' .text v = some (st, P) ∧ readFormat 'l' st w ≠ none ∧
    (st = .text ∨ ∃ c, st = .length c) ∧ (exit = true → w = [])

/-- The invariant of the inner loop of `JPoints.Printf.rewriteFormat`, the scan after the `%` at the
index `i` of the copy `fmt`, at the index `k`: the characters from `i + 1` to `k` are those of the
scan (`JPoints.Printf.scanChars`); after the loop, the character at `k`, if any, is not. -/
def RewriteScanInvariant (fmt : Array Char) (i : ℕ) : Std.WP.WhileInvariant ℕ Prop :=
  .mk fun exit k ↦ i + 1 ≤ k ∧ k ≤ fmt.size ∧
    (∀ ch ∈ (fmt.toList.drop (i + 1)).take (k - (i + 1)), ch ∈ scanChars) ∧
    (exit = true → ∀ ch ∈ (fmt.toList.drop k).head?, ch ∉ scanChars)

/- The character at the index `j` of the copy as the C code reads it, with a `NUL` past the end. -/
private theorem dite_getElem_eq (xs : Array Char) (j : ℕ) :
    (if h : j < xs.size then xs[j] else '\x00') = xs.toList[j]?.getD '\x00' := by
  rw [Array.getElem?_toList]
  split <;> simp [*]

private theorem getElem?_append_cons_add_one {α : Type*} (u w : List α) (a : α) (n : ℕ) :
    (u ++ a :: w)[u.length + 1 + n]? = w[n]? := by
  rw [List.getElem?_append_right (by lia), show u.length + 1 + n - u.length = n + 1 by lia,
    List.getElem?_cons_succ]

variable {format : String} {f : List Piece} {fmt : Array Char} {i k : ℕ}

/-- The invariant of the outer loop after the parts `t₁` of the copy and `t₂` of the format, read
alike from the state of the prefixes. -/
theorem rewriteInvariant_of_readPrefix {fmt' : Array Char} {i' : ℕ} {u v w t₁ t₂ : List Char}
    {st : ReadState} {x : ReadState × List Piece} {P : List Piece}
    (hu : fmt'.toList = u ++ t₁ ++ w) (hv : format.toList = v ++ t₂ ++ w)
    (hui : (u ++ t₁).length = i') (hvi : (v ++ t₂).length = i')
    (hZ : readPrefix 'Z' .text u = some (st, P)) (hl : readPrefix 'l' .text v = some (st, P))
    (hZ' : readPrefix 'Z' st t₁ = some x) (hl' : readPrefix 'l' st t₂ = some x)
    (hw : readFormat 'l' x.1 w ≠ none) (hst : x.1 = .text ∨ ∃ c, x.1 = .length c) :
    RewriteInvariant format false (fmt', i') :=
  ⟨u ++ t₁, v ++ t₂, w, x.1, P ++ x.2, hu, hv, hui, hvi, by simp [readPrefix_append, hZ, hZ'],
    by simp [readPrefix_append, hl, hl'], hw, hst, nofun⟩

theorem rewriteInvariant_zero (hf : readFormat 'l' .text format.toList = some f) :
    RewriteInvariant format false ({ toList := format.toList }, 0) :=
  ⟨[], [], format.toList, .text, [], rfl, rfl, rfl, rfl, rfl, rfl, by simp [hf], .inl rfl, nofun⟩

theorem RewriteInvariant.size_eq {exit : Bool} (h : RewriteInvariant format exit (fmt, i)) :
    fmt.size = format.toList.length := by
  obtain ⟨u, v, w, -, -, hu, hv, hui, hvi, -⟩ := h
  rw [← Array.length_toList, hu, hv]
  simp [hui, hvi]

theorem RewriteInvariant.post (hf : readFormat 'l' .text format.toList = some f)
    (h : RewriteInvariant format true (fmt, i)) :
    readFormat 'Z' .text (String.ofList fmt.toList).toList = some f := by
  obtain ⟨u, v, w, st, P, hu, hv, -, -, hZ, hl, hw, -, hnil⟩ := h
  obtain rfl := hnil rfl
  obtain rfl : st = .text := by cases st <;> simp_all [readFormat]
  rw [hv, readFormat_append, hl] at hf
  rw [String.toList_ofList, hu, readFormat_append, hZ]
  simpa [readFormat] using hf

theorem RewriteInvariant.exit {mb : ℕ}
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : ¬i < format.toList.length) : RewriteInvariant format true (fmt, i) := by
  obtain ⟨-, u, v, w, st, P, hu, hv, hui, hvi, hZ, hl, hw, hst, -⟩ := h
  refine ⟨u, v, w, st, P, hu, hv, hui, hvi, hZ, hl, hw, hst, fun _ ↦ ?_⟩
  rw [hv] at hlt
  simp only [List.length_append, hvi] at hlt
  exact List.eq_nil_of_length_eq_zero (by lia)

/-- A character other than `%` is passed over. -/
theorem RewriteInvariant.add_one {mb : ℕ} (hi : ¬fmt[i]! = '%')
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length) :
    format.toList.length + 1 - (i + 1) < mb ∧ RewriteInvariant format false (fmt, i + 1) := by
  obtain ⟨rfl, u, v, w, st, P, hu, hv, rfl, hvi, hZ, hl, hw, hst, -⟩ := h
  obtain _ | ⟨ch, w⟩ := w
  · simp [hv, hvi] at hlt
  rw [← Array.getElem!_toList, hu] at hi
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right, le_refl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some] at hi
  obtain ⟨x, hx, hw⟩ := readFormat_cons_ne_none_iff.mp hw
  obtain ⟨hxZ, hx1⟩ := readChar_eq_some_and_fst_eq_text hst hi hx
  exact ⟨by lia, rewriteInvariant_of_readPrefix (t₁ := [ch]) (t₂ := [ch]) (by simp [hu])
    (by simp [hv]) (by simp) (by simp [hvi]) hZ hl (by simpa using hxZ) (by simpa using hx) hw
    (.inl hx1)⟩

/-- A `%%` is passed over. -/
theorem RewriteInvariant.add_two {mb : ℕ} (hi : fmt[i]! = '%')
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : (if h : i + 1 < fmt.size then fmt[i + 1] else '\x00') = '%') :
    format.toList.length + 1 - (i + 1 + 1) < mb ∧
      RewriteInvariant format false (fmt, i + 1 + 1) := by
  obtain ⟨rfl, u, v, w, st, P, hu, hv, rfl, hvi, hZ, hl, hw, hst, -⟩ := h
  rw [dite_getElem_eq, hu] at h1
  rw [← Array.getElem!_toList, hu] at hi
  obtain _ | ⟨c₁, _ | ⟨c₂, w⟩⟩ := w
  · simp [hv, hvi] at hlt
  · simp at h1
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right, le_refl, Nat.sub_self,
    Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    le_add_iff_nonneg_right, zero_le] at hi h1
  subst hi h1
  obtain rfl := eq_text_of_readFormat_percent_ne_none hst hw
  refine ⟨by lia, rewriteInvariant_of_readPrefix (t₁ := ['%', '%']) (t₂ := ['%', '%']) (w := w)
    (x := (.text, [.char '%'])) (by simp [hu]) (by simp [hv]) (by simp) (by simp [hvi]) hZ hl ?_
    ?_ ?_ (.inl rfl)⟩ <;> simp_all [readPrefix_cons, readFormat_cons, readChar]

/-- The scan after a `%` starts at the next character. -/
theorem rewriteScanInvariant_add_one {mb : ℕ}
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length) : RewriteScanInvariant fmt i false (i + 1) :=
  ⟨le_rfl, by lia [h.2.size_eq], by simp, nofun⟩

theorem RewriteScanInvariant.add_one {mb mb' : ℕ}
    (ho : format.toList.length + 1 - i = mb' ∧ RewriteInvariant format false (fmt, i))
    (h : format.toList.length - k = mb ∧ RewriteScanInvariant fmt i false k)
    (hk : k < format.toList.length ∧ fmt[k]! ∈ scanChars) :
    format.toList.length - (k + 1) < mb ∧ RewriteScanInvariant fmt i false (k + 1) := by
  obtain ⟨rfl, hik, -, hbody, -⟩ := h
  have hs := ho.2.size_eq
  refine ⟨by lia, by lia, by lia, fun ch hch ↦ ?_, nofun⟩
  rw [show k + 1 - (i + 1) = k - (i + 1) + 1 by lia, List.take_add_one, List.mem_append] at hch
  refine hch.elim (hbody ch) fun hch ↦ ?_
  simp only [List.getElem?_drop, show i + 1 + (k - (i + 1)) = k by lia, Array.getElem?_toList,
    Option.mem_toList, getElem?_pos fmt k (by lia : k < fmt.size), Option.some.injEq] at hch
  rw [← hch, ← getElem!_pos fmt k (by lia)]
  exact hk.2

theorem RewriteScanInvariant.exit {mb mb' : ℕ}
    (ho : format.toList.length + 1 - i = mb' ∧ RewriteInvariant format false (fmt, i))
    (h : format.toList.length - k = mb ∧ RewriteScanInvariant fmt i false k)
    (hk : ¬(k < format.toList.length ∧ fmt[k]! ∈ scanChars)) :
    RewriteScanInvariant fmt i true k := by
  obtain ⟨-, hik, hks, hbody, -⟩ := h
  have hs := ho.2.size_eq
  refine ⟨hik, hks, hbody, fun _ ch hch ↦ ?_⟩
  rw [List.head?_drop, Array.getElem?_toList] at hch
  rcases Nat.lt_or_ge k fmt.size with hlt | hge
  · rw [getElem?_pos fmt k hlt, Option.mem_def, Option.some.injEq] at hch
    rw [← hch]
    exact fun h ↦ hk ⟨by lia, by rwa [getElem!_pos fmt k hlt]⟩
  · simp [getElem?_neg fmt k (by lia)] at hch

/-- After the scan of a conversion from its `%` at the index `i` to the index `k`, the copy and the
format have the length modifier `l` at `k`, and their prefixes up to it, the copy's with `Z`, are
read alike into the state after the length modifier. -/
theorem RewriteInvariant.exists_conversion {mb : ℕ} (hi : fmt[i]! = '%')
    (hk : RewriteScanInvariant fmt i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < fmt.size then fmt[i + 1] else '\x00') = '%') :
    ∃ U V W c P, fmt.toList = U ++ 'l' :: W ∧ format.toList = V ++ 'l' :: W ∧
      U.length = k ∧ V.length = k ∧ readPrefix 'Z' .text (U ++ ['Z']) = some (.length c, P) ∧
      readPrefix 'l' .text (V ++ ['l']) = some (.length c, P) ∧
      readFormat 'l' (.length c) W ≠ none := by
  obtain ⟨-, u, v, w, st, P, hu, hv, rfl, hvi, hZ, hl, hw, hst, -⟩ := h
  obtain ⟨hik, -, hbody, hrest⟩ := hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hik
  obtain _ | ⟨ch, w⟩ := w
  · simp [hv, hvi] at hlt
  rw [← Array.getElem!_toList, hu, List.getElem!_eq_getElem?_getD,
    List.getElem?_append_right le_rfl, Nat.sub_self] at hi
  obtain rfl : ch = '%' := hi
  rw [dite_getElem_eq, hu, ← Nat.add_zero (u.length + 1), getElem?_append_cons_add_one] at h1
  rw [hu, List.head?_drop, getElem?_append_cons_add_one] at hrest
  obtain rfl := eq_text_of_readFormat_percent_ne_none hst hw
  obtain ⟨c, W, hW, hpl, hpZ, hfW⟩ := exists_readPrefix_percent_eq_length (body := w.take n)
    (rest := w.drop n) (by simpa [hu] using hbody) (by simpa using hrest rfl)
    (fun h ↦ h1 (by simp_all [List.head?_eq_getElem?])) (by simpa using hw)
  have hw' : w = w.take n ++ 'l' :: W := by rw [← hW, List.take_append_drop]
  have hn : (w.take n).length = n := by have := congr(List.length $hw'); simp at this ⊢; lia
  refine ⟨u ++ '%' :: w.take n, v ++ '%' :: w.take n, W, c, P, ?_, ?_, by simp [hn]; lia,
    by simp [hn]; lia, by simp [readPrefix_append, hZ, hpZ], by simp [readPrefix_append, hl, hpl],
    hfW⟩ <;> simp only [hu, hv] <;> nth_rw 1 [hw'] <;> simp

/-- After the scan of a conversion, its length modifier made a `Z`: the reading of the copy and of
the format is after the length modifier at the index `k + 1`. -/
theorem RewriteInvariant.set_add_one {mb : ℕ} (hi : fmt[i]! = '%')
    (hk : RewriteScanInvariant fmt i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < fmt.size then fmt[i + 1] else '\x00') = '%') :
    format.toList.length + 1 - (k + 1) < mb ∧
      RewriteInvariant format false (fmt.set! k 'Z', k + 1) := by
  obtain ⟨U, V, W, c, P, hU, hV, hUk, hVk, hZ, hl, hw⟩ :=
    RewriteInvariant.exists_conversion hi hk h hlt h1
  refine ⟨by obtain ⟨hik, -⟩ := hk; lia, ⟨U ++ ['Z'], V ++ ['l'], W, .length c, P, ?_,
    by simp [hV], by simp [hUk], by simp [hVk], hZ, hl, hw, .inr ⟨c, rfl⟩, nofun⟩⟩
  simp [hU, ← hUk, List.set_append_right]

/-- After the scan of a conversion, its length modifier `l` and its `d` follow. -/
theorem RewriteInvariant.lengthModifier {mb : ℕ} (hi : fmt[i]! = '%')
    (hk : RewriteScanInvariant fmt i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < fmt.size then fmt[i + 1] else '\x00') = '%') :
    (if h : k < fmt.size then fmt[k] else '\x00') = 'l' ∧
      (if h : k + 1 < fmt.size then fmt[k + 1] else '\x00') = 'd' := by
  obtain ⟨U, V, W, c, P, hU, -, rfl, -, -, -, hw⟩ :=
    RewriteInvariant.exists_conversion hi hk h hlt h1
  obtain _ | ⟨d, W⟩ := W
  · simp [readFormat] at hw
  obtain ⟨y, hy, -⟩ := readFormat_cons_ne_none_iff.mp hw
  simp only [readChar, Option.ite_none_right_eq_some] at hy
  simp [dite_getElem_eq, hU, hy.1.1]

attribute [local irreducible] RewriteInvariant RewriteScanInvariant in
/-- On a format that `printf` reads (with the length modifier `l`) as the pieces `f`, the scan of
`printf_mpz` gives a format that `gmp_printf` reads (with `Z`) as the same pieces. -/
@[spec]
theorem rewriteFormat_spec (format : String) (f : List Piece) :
    ⦃ readFormat 'l' .text format.toList = some f ⦄ rewriteFormat format
    ⦃ fun r ↦ readFormat 'Z' .text r.toList = some f ⦄ := by
  vcgen [rewriteFormat] invariants
  | inv1 => RewriteInvariant format
  | inv2 => .ofMeasure fun s : Array Char × ℕ ↦ format.toList.length + 1 - s.2
  | inv3 fmt i _ _ _ _ _ => RewriteScanInvariant fmt i
  | inv4 => .ofMeasure fun k : ℕ ↦ format.toList.length - k
  all_goals try vc_simp [Array.getInternal_eq_getElem, List.size_toArray]
  all_goals with_reducible first
    | exact rewriteInvariant_zero ‹_›
    | exact RewriteInvariant.post ‹_› ‹_›
    | exact RewriteInvariant.add_two ‹_› ‹_› ‹_› ‹_›
    | exact rewriteScanInvariant_add_one ‹_› ‹_›
    | exact RewriteInvariant.set_add_one ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact absurd (RewriteInvariant.lengthModifier ‹_› ‹_› ‹_› ‹_› ‹_›) ‹_›
    | exact RewriteScanInvariant.add_one ‹_› ‹_› ‹_›
    | exact RewriteScanInvariant.exit ‹_› ‹_› ‹_›
    | exact RewriteInvariant.add_one ‹_› ‹_› ‹_›
    | exact RewriteInvariant.exit ‹_› ‹_›

/-! ### The text of a point -/

/-- A conversion `%ld` without flags, width or precision prints the decimal text of the integer. -/
theorem printLong_eq_toString (n : ℤ) : printLong ⟨[], 0, none⟩ n = toString n := by
  rcases lt_or_ge n 0 with h | h
  · simp [printLong, Int.repr_eq_ite, Nat.repr_eq_ofList_toDigits, h, show ¬0 ≤ n by lia,
      show (-n).toNat = n.natAbs by lia]
  · simp [printLong, Int.repr_eq_ite, Nat.repr_eq_ofList_toDigits, h, show ¬n < 0 by lia,
      show n.toNat = n.natAbs by lia]

/-- A conversion without flags, width or precision prints an integer alike by `gmp_printf` and by
`printf`. -/
theorem printMpz_eq_printLong (n : ℤ) : printMpz ⟨[], 0, none⟩ n = printLong ⟨[], 0, none⟩ n := by
  simp [printMpz, printLong]

theorem parseFormat_eq_some_iff {len : Char} {s : String} {f : List Piece} :
    parseFormat len s = some f ↔
      readFormat len .text s.toList = some f ∧ (f.filter (· matches .conv _)).length ≤ 4 := by
  simp only [parseFormat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq]
  exact ⟨fun ⟨ps, hps, hle, hf⟩ ↦ hf ▸ ⟨hps, hle⟩, fun ⟨hps, hle⟩ ↦ ⟨f, hps, hle, rfl⟩⟩

/-- `gmp_printf` reads the format that `printf_mpz` makes of an admitted format with its pieces. -/
theorem parseFormat_run_rewriteFormat {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) :
    parseFormat 'Z' (rewriteFormat format).run = some f := by
  rw [parseFormat_eq_some_iff] at hf ⊢
  exact ⟨Std.WP.Id.of_run_eq_wp rfl _ ((rewriteFormat_spec format f).le_wp hf.1), hf.2⟩

/-- `emit_point` prints the point of the curve given (`JPoints.backPoint`) under the pieces of an
admitted format by `printf`. -/
theorem emitPoint_eq_render {rev neg : Bool} {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    emitPoint rev neg format a b c d = render printLong f [a', b', c', d'] := by
  cases rev <;> cases neg <;>
    simp only [backPoint, emitPoint, hf, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> simp only [h]

/-- `printf_mpz` prints the point of the curve given (`JPoints.backPoint`) under the pieces of an
admitted format by `gmp_printf`, for a point whose first nonzero coordinate is positive: without a
reversal or a negation it takes the point as it is. -/
theorem run_printfMpz_eq_render {rev neg : Bool} {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) {a b c d a' b' c' d' : ℤ}
    (hn : 0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c))
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    (printfMpz rev neg format a b c d).run = render printMpz f [a', b', c', d'] := by
  cases rev <;> cases neg <;> simp only [backPoint, printfMpz, Id.run_bind,
    parseFormat_run_rewriteFormat hf, Bool.false_eq_true, ↓reduceIte, Bool.or_self, Bool.or_true,
    Bool.true_or, true_and, false_and, Id.run_pure] at h ⊢
  · simp only [show ¬(a < 0 ∨ a = 0 ∧ (b < 0 ∨ b = 0 ∧ c < 0)) by lia, ↓reduceIte,
      Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  all_goals simp only [h]

end JPoints.Printf

end
