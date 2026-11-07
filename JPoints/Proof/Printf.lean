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
`printf` (`JPoints.Printf.emitPoint_eq_render`), and by `gmp_printf` under the pieces rewritten by
`JPoints.Printf.Piece.gmpSpec` (`JPoints.Printf.run_printfMpz_eq_render`) for a point whose first
nonzero coordinate is positive. Both print the same text
(`JPoints.Printf.render_printMpz_map_gmpSpec`), since `gmp_spec` drops the flags that `gmp_printf`
reads otherwise than `printf` (`JPoints.Printf.printMpz_gmpSpec`). The scan of `printf_mpz` finds
exactly the conversions of an admitted format, and the format that it builds for `gmp_printf` has
the pieces of the format, each conversion rewritten by `JPoints.Printf.Conversion.gmpSpec`
(`JPoints.Printf.rewriteFormat_spec`, `JPoints.Printf.parseFormat_run_rewriteFormat`): a conversion
is its `%`, flags, width and precision, all characters of the scan (`JPoints.Printf.scanChars`),
then its `l` and its `d` (`JPoints.Printf.readChar_of_mem_scanChars`), and the reading for `Z` takes
the flags, the width and the precision that `gmp_spec` writes of them, followed by `Z`, as the
conversion that `JPoints.Printf.Conversion.gmpSpec` makes (`JPoints.Printf.readPrefix_gmpSpec`).

## Main definitions

* `JPoints.Printf.readPrefix`: the state and the pieces after a part of a format.
* `JPoints.Printf.ReadState.InConversion`: the reading inside a conversion, before its length
  modifier.
* `JPoints.Printf.RewriteInvariant`, `JPoints.Printf.RewriteScanInvariant`: the invariants of the
  two loops of `JPoints.Printf.rewriteFormat`.

## Main statements

* `JPoints.Printf.readFormat_append`: the reading of a format, part by part.
* `JPoints.Printf.ReadState.InConversion.exists_readPrefix_eq_length`,
  `JPoints.Printf.exists_readPrefix_percent_eq_length`: the reading of a conversion.
* `JPoints.Printf.readPrefix_gmpSpec`: the reading of the conversion that `gmp_spec` writes.
* `JPoints.Printf.rewriteFormat_spec`, `JPoints.Printf.parseFormat_run_rewriteFormat`: the format
  that `printf_mpz` gives `gmp_printf` has the pieces of the format of `-f`, each rewritten by
  `JPoints.Printf.Piece.gmpSpec`.
* `JPoints.Printf.emitPoint_eq_render`, `JPoints.Printf.run_printfMpz_eq_render`: the text of a
  point.
* `JPoints.Printf.printMpz_gmpSpec`, `JPoints.Printf.render_printMpz_map_gmpSpec`: `gmp_printf`
  under the rewritten pieces prints what `printf` prints under the pieces of the format.
* `JPoints.Printf.printLong_eq_toString`: a conversion without flags, width or precision prints the
  decimal text.

## Implementation notes

The contract of `JPoints.Printf.rewriteFormat` is proved by `vcgen` with the two invariants, each
verification condition discharged by a lemma in its own shape. The outer invariant splits the format
at the index `i` into a prefix and a rest; the format built so far, read with `Z`, and the prefix,
read with `l`, give pieces that correspond under `JPoints.Printf.Piece.gmpSpec`, outside a
conversion or after the length modifier of one whose `d` comes next. The flags, the width and the
precision of a conversion are taken apart as `gmp_spec` takes them, by `List.takeWhile` and
`List.dropWhile`, and read part by part. The character `format[k]` that the C code reads with a
`NUL` past the end is the term `if h : k < l.length then ⟨l⟩[k] else '\x00'` of the verification
conditions.
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
private theorem readPrefix_nil (len : Char) (st : ReadState) : readPrefix len st [] = some
    (st, []) :=
  rfl

private theorem readPrefix_cons (len : Char) (st : ReadState) (ch : Char) (s : List Char) :
    readPrefix len st (ch :: s) = (readChar len st ch).bind fun x ↦
      (readPrefix len x.1 s).map fun y ↦ (y.1, x.2 ++ y.2) :=
  rfl

private theorem readPrefix_append (len : Char) (st : ReadState) (s t : List Char) :
    readPrefix len st (s ++ t) = (readPrefix len st s).bind fun x ↦
      (readPrefix len x.1 t).map fun y ↦ (y.1, x.2 ++ y.2) := by
  induction s generalizing st with
  | nil => simp
  | cons ch s ih =>
    simp [readPrefix_cons, ih, Option.bind_assoc, Option.map_bind, Option.bind_map,
      Function.comp_def]

@[simp]
private theorem readPrefix_singleton (len : Char) (st : ReadState) (ch : Char) :
    readPrefix len st [ch] = readChar len st ch := by
  simp [readPrefix_cons]

private theorem readFormat_cons (len : Char) (st : ReadState) (ch : Char) (s : List Char) :
    readFormat len st (ch :: s) = (readChar len st ch).bind fun x ↦
      (readFormat len x.1 s).map (x.2 ++ ·) := by
  simp [readFormat, Option.map_eq_bind]

private theorem readFormat_cons_ne_none_iff {len : Char} {st : ReadState} {ch : Char}
    {s : List Char} :
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

private theorem scanChars_eq : scanChars =
    ['-', '+', ' ', '#', '\'', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.'] := by
  decide

private theorem mem_scanChars_of_isDigit {ch : Char} (h : ch.isDigit) : ch ∈ scanChars := by
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

/-- Inside a conversion, a character of the scan of `printf_mpz` completes no piece and leaves the
reading inside the conversion, where a `%` cannot come any more. -/
theorem readChar_of_mem_scanChars {st : ReadState} (hst : st.InConversion) {ch : Char}
    (hch : ch ∈ scanChars) :
    ∀ x ∈ readChar 'l' st ch, x.2 = [] ∧ x.1.InConversion ∧ readChar 'l' x.1 '%' = none := by
  rw [scanChars_eq] at hch
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
  cases st <;> simp only [ReadState.InConversion] at hst <;>
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    simp [readChar, readWidth, flagChars, ReadState.InConversion]

/-- Inside a conversion, a character beyond those of the scan of `printf_mpz` that the reading
takes, other than the `%` of a `%%`, is the length modifier `l`. -/
private theorem readChar_of_notMem_scanChars {st : ReadState} (hst : st.InConversion) {ch : Char}
    (hch : ch ∉ scanChars) (hpct : readChar 'l' st '%' = none ∨ ch ≠ '%')
    (h : readChar 'l' st ch ≠ none) :
    ch = 'l' ∧ ∃ c, readChar 'l' st 'l' = some (.length c, []) := by
  have hd : ¬ch.isDigit := fun hd ↦ hch (mem_scanChars_of_isDigit hd)
  have hf : ch ∉ flagChars := fun hf ↦ hch ((by decide : ∀ c ∈ flagChars, c ∈ scanChars) ch hf)
  have hp : ch ≠ '.' := by rintro rfl; exact hch (by decide)
  cases st <;> simp only [ReadState.InConversion] at hst <;>
    simp_all [readChar, readWidth, flagChars]
  grind

/-! ### The reading of a conversion -/

/-- The characters `body` of the scan of `printf_mpz` and the character after them, read inside a
conversion: for a format that the reading takes, that character is the length modifier `l`. -/
theorem ReadState.InConversion.exists_readPrefix_eq_length {st : ReadState}
    (hst : st.InConversion) {body rest : List Char} (hbody : ∀ ch ∈ body, ch ∈ scanChars)
    (hrest : ∀ ch ∈ rest.head?, ch ∉ scanChars)
    (hpct : readChar 'l' st '%' = none ∨ (body ++ rest).head? ≠ some '%')
    (h : readFormat 'l' st (body ++ rest) ≠ none) :
    ∃ c rest', rest = 'l' :: rest' ∧ readPrefix 'l' st (body ++ ['l']) = some (.length c, []) ∧
      readFormat 'l' (.length c) rest' ≠ none := by
  induction body generalizing st with
  | nil =>
    obtain _ | ⟨ch, rest⟩ := rest
    · cases st <;> simp_all [readFormat, ReadState.InConversion]
    obtain ⟨x, hx, hr⟩ := readFormat_cons_ne_none_iff.mp h
    obtain ⟨rfl, c, hl⟩ := readChar_of_notMem_scanChars hst (hrest ch rfl)
      (by simpa using hpct) (by simp [hx])
    obtain rfl : x = (.length c, []) := Option.some.inj (hx.symm.trans hl)
    exact ⟨c, rest, rfl, by simpa using hl, hr⟩
  | cons ch body ih =>
    obtain ⟨x, hxl, hr⟩ := readFormat_cons_ne_none_iff.mp h
    obtain ⟨hx2, hx1, hpct'⟩ := readChar_of_mem_scanChars hst (hbody ch (.head _)) x hxl
    obtain ⟨c, rest', hrest', hl, hr'⟩ :=
      ih hx1 (fun c hc ↦ hbody c (.tail _ hc)) (.inl hpct') hr
    exact ⟨c, rest', hrest', by simp [readPrefix_cons, hxl, hl, hx2], hr'⟩

/-- A conversion of a format that the reading takes, read from its `%`: after the characters `body`
of the scan of `printf_mpz`, not starting a `%%`, comes its length modifier `l`. -/
theorem exists_readPrefix_percent_eq_length {body rest : List Char}
    (hbody : ∀ ch ∈ body, ch ∈ scanChars) (hrest : ∀ ch ∈ rest.head?, ch ∉ scanChars)
    (hpct : (body ++ rest).head? ≠ some '%')
    (h : readFormat 'l' .text ('%' :: (body ++ rest)) ≠ none) :
    ∃ c rest', rest = 'l' :: rest' ∧
      readPrefix 'l' (.flags ⟨[], 0, none⟩) (body ++ ['l']) = some (.length c, []) ∧
      readFormat 'l' (.length c) rest' ≠ none := by
  obtain ⟨x, hx, hr⟩ := readFormat_cons_ne_none_iff.mp h
  obtain rfl : x = (.flags ⟨[], 0, none⟩, []) := by simpa [readChar] using hx.symm
  exact ReadState.InConversion.exists_readPrefix_eq_length (st := .flags ⟨[], 0, none⟩) trivial
    hbody hrest (.inr hpct) hr

/-! ### The reading of the conversion that `gmp_spec` writes -/

/- The step of the reading of a digit of a width. -/
private def widthStep (n : ℕ) (ch : Char) : ℕ := 10 * n + (ch.toNat - '0'.toNat)

/- The step of the reading of a digit of a precision. -/
private def precisionStep (p : Option (Option ℕ)) (ch : Char) : Option (Option ℕ) :=
  some (some (10 * p.join.getD 0 + (ch.toNat - '0'.toNat)))

/- The precision that the characters `pr` after the width of a conversion give, `none` when they
are no precision. -/
private def precisionOf : List Char → Option (Option (Option ℕ))
  | [] => some none
  | ch :: ds => if ch = '.' ∧ ds.all Char.isDigit then some (ds.foldl precisionStep (some none))
    else none

private theorem readPrefix_flags_append {len : Char} {fl : List Char}
    (hfl : ∀ ch ∈ fl, ch ∈ flagChars) (c : Conversion) (t : List Char) :
    readPrefix len (.flags c) (fl ++ t) =
      readPrefix len (.flags { c with flags := c.flags ++ fl }) t := by
  induction fl generalizing c with
  | nil => simp
  | cons ch fl ih =>
    have hch : ch ≠ '%' := by rintro rfl; exact absurd (hfl _ (.head _)) (by decide)
    simp [readPrefix_cons, readChar, hch, hfl ch (.head _), ih (fun c hc ↦ hfl c (.tail _ hc))]

private theorem readPrefix_flags_eq_width {len : Char} {t : List Char} (ht : t ≠ [])
    (h : ∀ ch ∈ t.head?, ch ∉ flagChars ∧ ch ≠ '%') (c : Conversion) :
    readPrefix len (.flags c) t = readPrefix len (.width c) t := by
  obtain ⟨ch, t, rfl⟩ := List.exists_cons_of_ne_nil ht
  obtain ⟨h1, h2⟩ := h ch rfl
  simp [readPrefix_cons, readChar, h1, h2]

private theorem readPrefix_width_append {len : Char} {w : List Char}
    (hw : ∀ ch ∈ w, ch.isDigit) (c : Conversion) (t : List Char) :
    readPrefix len (.width c) (w ++ t) =
      readPrefix len (.width { c with width := w.foldl widthStep c.width }) t := by
  induction w generalizing c with
  | nil => simp
  | cons ch w ih =>
    simp [readPrefix_cons, readChar, readWidth, hw ch (.head _),
      ih (fun c hc ↦ hw c (.tail _ hc)), widthStep]

private theorem readPrefix_precision_append_len {len : Char} (hlen : len ∉ scanChars)
    {ds : List Char} (hds : ∀ ch ∈ ds, ch ∈ scanChars) (F : List Char) (W : ℕ)
    (q : Option (Option ℕ)) :
    readPrefix len (.precision ⟨F, W, q⟩) (ds ++ [len]) =
      if ds.all Char.isDigit then some (.length ⟨F, W, ds.foldl precisionStep q⟩, [])
      else none := by
  have hd : ¬len.isDigit := fun h ↦ hlen (mem_scanChars_of_isDigit h)
  induction ds generalizing q with
  | nil => simp [readPrefix_cons, readChar, hd]
  | cons ch ds ih =>
    have hne : ch ≠ len := fun h ↦ hlen (h ▸ hds ch (.head _))
    by_cases hc : ch.isDigit
    · simp [readPrefix_cons, readChar, hc, ih (fun c hc ↦ hds c (.tail _ hc)), precisionStep]
    · simp [readPrefix_cons, readChar, hc, hne]

private theorem readPrefix_width_append_len {len : Char} (hlen : len ∉ scanChars)
    {pr : List Char} (hpr : ∀ ch ∈ pr, ch ∈ scanChars) (hd : ∀ ch ∈ pr.head?, ¬ch.isDigit)
    (F : List Char) (W : ℕ) :
    readPrefix len (.width ⟨F, W, none⟩) (pr ++ [len]) =
      (precisionOf pr).map fun p ↦ (.length ⟨F, W, p⟩, []) := by
  have hld : ¬len.isDigit := fun h ↦ hlen (mem_scanChars_of_isDigit h)
  have hlp : len ≠ '.' := by rintro rfl; exact hlen (by decide)
  obtain _ | ⟨ch, ds⟩ := pr
  · simp [readPrefix_cons, readChar, readWidth, hld, hlp, precisionOf]
  have hne : ch ≠ len := fun h ↦ hlen (h ▸ hpr ch (.head _))
  have hc := hd ch rfl
  by_cases hdot : ch = '.'
  · subst hdot
    have h1 : readChar len (.width ⟨F, W, none⟩) '.' = some (.precision ⟨F, W, some none⟩, []) := by
      simp [readChar, readWidth, hc]
    rw [List.cons_append, readPrefix_cons, h1, Option.bind_some,
      readPrefix_precision_append_len hlen (fun c hc ↦ hpr c (.tail _ hc))]
    simp only [precisionOf, true_and]
    split_ifs <;> simp
  · simp [readPrefix_cons, readChar, readWidth, hc, hdot, hne, precisionOf]

/- The reading of flags `F`, a width `wd` and a precision `pr` of a conversion, after its `%`, and
of the length modifier `len` after them. -/
private theorem readPrefix_conversion {len : Char} (hlen : len ∉ scanChars) (hpct : len ≠ '%')
    {F wd pr : List Char} (hF : ∀ ch ∈ F, ch ∈ flagChars) (hwd : ∀ ch ∈ wd, ch.isDigit)
    (hpr : ∀ ch ∈ pr, ch ∈ scanChars) (hd : ∀ ch ∈ pr.head?, ¬ch.isDigit)
    (hh : ∀ ch ∈ (wd ++ pr).head?, ch ∉ flagChars ∧ ch ≠ '%') :
    readPrefix len (.flags ⟨[], 0, none⟩) (F ++ (wd ++ (pr ++ [len]))) =
      (precisionOf pr).map fun p ↦ (.length ⟨F, wd.foldl widthStep 0, p⟩, []) := by
  have hlf : len ∉ flagChars := fun h ↦ hlen ((by decide : ∀ c ∈ flagChars, c ∈ scanChars) _ h)
  have hh' : ∀ ch ∈ (wd ++ (pr ++ [len])).head?, ch ∉ flagChars ∧ ch ≠ '%' := by
    intro ch hch
    rw [← List.append_assoc, List.head?_append] at hch
    cases h : (wd ++ pr).head? <;> simp_all
  rw [readPrefix_flags_append hF, readPrefix_flags_eq_width (by simp) hh',
    readPrefix_width_append hwd]
  exact readPrefix_width_append_len hlen hpr hd F _

private theorem foldl_precisionStep (ds : List Char) (n : ℕ) :
    ∃ m, ds.foldl precisionStep (some (some n)) = some (some m) := by
  induction ds generalizing n with
  | nil => exact ⟨n, rfl⟩
  | cons ch ds ih => exact ih _

private theorem isSome_precisionOf (pr : List Char) :
    (precisionOf pr).isSome =
      (pr.isEmpty || pr.head? == some '.' && pr.tail.all Char.isDigit) := by
  obtain _ | ⟨ch, ds⟩ := pr
  · rfl
  · simp only [precisionOf, List.isEmpty_cons, List.head?_cons, List.tail_cons, Bool.false_or]
    by_cases h : ch = '.' ∧ ds.all Char.isDigit
    · simp [h]
    · simp only [h, ↓reduceIte]
      simpa using h

/- The precision after `gmp_spec`, which makes a `.` alone `.0`. -/
private theorem precisionOf_append {pr : List Char} {q : Option (Option ℕ)}
    (h : precisionOf pr = some q) :
    precisionOf (pr ++ if pr == ['.'] then ['0'] else []) =
      some (q.map fun p ↦ some (p.getD 0)) ∧ (!pr.isEmpty) = q.isSome := by
  obtain _ | ⟨ch, ds⟩ := pr
  · obtain rfl : q = none := by simpa [precisionOf] using h.symm
    simp [precisionOf]
  have hc : ch = '.' ∧ ds.all Char.isDigit := by
    simp only [precisionOf] at h
    split at h
    · assumption
    · exact absurd h (by simp)
  obtain ⟨rfl, hds⟩ := hc
  obtain rfl : q = ds.foldl precisionStep (some none) := by simpa [precisionOf, hds] using h.symm
  obtain _ | ⟨d, ds⟩ := ds
  · simp [precisionOf, precisionStep]
  obtain ⟨m, hm⟩ := foldl_precisionStep ds (10 * 0 + (d.toNat - '0'.toNat))
  have hq : (d :: ds).foldl precisionStep (some none) = some (some m) := hm
  simp [precisionOf, hds, hq]

private theorem head?_append_zero (pr : List Char) :
    (pr ++ if pr == ['.'] then ['0'] else []).head? = pr.head? := by
  obtain _ | ⟨x, pr⟩ := pr <;> simp

private theorem mem_append_zero {pr : List Char} (hpr : ∀ ch ∈ pr, ch ∈ scanChars) :
    ∀ ch ∈ pr ++ if pr == ['.'] then ['0'] else [], ch ∈ scanChars := by
  intro ch hch
  rcases List.mem_append.mp hch with h | h
  · exact hpr ch h
  · split at h
    · rw [List.mem_singleton.mp h]
      decide
    · simp at h

/- The flags `fl`, the width `wd` and the precision `pr` of a conversion that the reading for `l`
takes: they are what `gmp_spec` rewrites, and the reading for `Z` takes what it writes. -/
private theorem readPrefix_gmpSpec_split {fl wd pr : List Char} {c : Conversion}
    (hF : ∀ ch ∈ fl, ch ∈ flagChars) (hwd : ∀ ch ∈ wd, ch.isDigit)
    (hpr : ∀ ch ∈ pr, ch ∈ scanChars) (hd : ∀ ch ∈ pr.head?, ¬ch.isDigit)
    (hh : ∀ ch ∈ (wd ++ pr).head?, ch ∉ flagChars ∧ ch ≠ '%')
    (h : readPrefix 'l' (.flags ⟨[], 0, none⟩) (fl ++ (wd ++ (pr ++ ['l']))) =
      some (.length c, [])) :
    (pr.isEmpty || pr.head? == some '.' && pr.tail.all Char.isDigit) = true ∧
      readPrefix 'Z' (.flags ⟨[], 0, none⟩) (fl.filter (fun ch ↦ !(ch == ' ' && fl.contains '+' ||
        ch == '0' && (fl.contains '-' || !pr.isEmpty))) ++
          (wd ++ (pr ++ ((if pr == ['.'] then ['0'] else []) ++ ['Z'])))) =
        some (.length c.gmpSpec, []) := by
  rw [readPrefix_conversion (by decide) (by decide) hF hwd hpr hd hh] at h
  obtain ⟨q, hq, hc⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hz, hsome⟩ := precisionOf_append hq
  refine ⟨by rw [← isSome_precisionOf, hq]; rfl, ?_⟩
  rw [← List.append_assoc pr, readPrefix_conversion (by decide) (by decide)
    (fun ch hch ↦ hF ch (List.mem_filter.mp hch).1) hwd (mem_append_zero hpr)
    (head?_append_zero pr ▸ hd)
    (by rwa [List.head?_append, head?_append_zero, ← List.head?_append]), hz]
  cases hc
  simp [Conversion.gmpSpec, hsome]

/- The flags, the width and the precision of a conversion taken apart as `gmp_spec` takes them. -/
private theorem split_scanChars {body : List Char} (hbody : ∀ ch ∈ body, ch ∈ scanChars) :
    (∀ ch ∈ body.takeWhile (· ∈ flagChars), ch ∈ flagChars) ∧
      (∀ ch ∈ (body.dropWhile (· ∈ flagChars)).takeWhile Char.isDigit, ch.isDigit) ∧
      (∀ ch ∈ (body.dropWhile (· ∈ flagChars)).dropWhile Char.isDigit, ch ∈ scanChars) ∧
      (∀ ch ∈ ((body.dropWhile (· ∈ flagChars)).dropWhile Char.isDigit).head?, ¬ch.isDigit) ∧
      ∀ ch ∈ ((body.dropWhile (· ∈ flagChars)).takeWhile Char.isDigit ++
        (body.dropWhile (· ∈ flagChars)).dropWhile Char.isDigit).head?,
          ch ∉ flagChars ∧ ch ≠ '%' := by
  refine ⟨fun ch hch ↦ by simpa using List.all_eq_true.mp List.all_takeWhile ch hch,
    fun ch hch ↦ List.all_eq_true.mp List.all_takeWhile ch hch, fun ch hch ↦
      hbody ch (((List.dropWhile_sublist _).trans (List.dropWhile_sublist _)).subset hch), ?_, ?_⟩
  · have := List.head?_dropWhile_not Char.isDigit (body.dropWhile (· ∈ flagChars))
    intro ch hch
    simp_all
  · rw [List.takeWhile_append_dropWhile]
    intro ch hch
    have := List.head?_dropWhile_not (· ∈ flagChars) body
    have hm : ch ∈ body := (List.dropWhile_sublist _).subset (List.mem_of_mem_head? hch)
    exact ⟨by simp_all, fun h ↦ absurd (h ▸ hbody ch hm) (by decide)⟩

/-- The flags, the width and the precision `body` of a conversion that the reading for `l` takes,
after its `%` and before its length modifier `l`: what `gmp_spec` writes of them, followed by `Z`,
the reading for `Z` takes as the conversion `JPoints.Printf.Conversion.gmpSpec` of it. -/
theorem readPrefix_gmpSpec {body : List Char} (hbody : ∀ ch ∈ body, ch ∈ scanChars)
    {c : Conversion}
    (h : readPrefix 'l' (.flags ⟨[], 0, none⟩) (body ++ ['l']) = some (.length c, [])) :
    readPrefix 'Z' (.flags ⟨[], 0, none⟩) (gmpSpec body ++ ['Z']) =
      some (.length c.gmpSpec, []) := by
  obtain ⟨hF, hwd, hpr, hd, hh⟩ := split_scanChars hbody
  rw [← List.takeWhile_append_dropWhile (p := (· ∈ flagChars)) (l := body),
    ← List.takeWhile_append_dropWhile (p := Char.isDigit) (l := body.dropWhile _)] at h
  simp only [gmpSpec]
  generalize body.takeWhile (· ∈ flagChars) = fl at h hF ⊢
  generalize (body.dropWhile (· ∈ flagChars)).takeWhile Char.isDigit = wd at h hwd hh ⊢
  generalize (body.dropWhile (· ∈ flagChars)).dropWhile Char.isDigit = pr at h hpr hd hh ⊢
  simp only [List.append_assoc] at h
  obtain ⟨hok, hZ⟩ := readPrefix_gmpSpec_split hF hwd hpr hd hh h
  simp only [hok, ↓reduceIte, List.append_assoc]
  exact hZ

/-! ### The loops of `printf_mpz` -/

/-- Outside a conversion, or after its length modifier, a character other than `%` is read for `l`
and for `Z` from the states that correspond under `JPoints.Printf.Conversion.gmpSpec` into the
pieces that correspond under `JPoints.Printf.Piece.gmpSpec`, outside a conversion. -/
private theorem readChar_gmpSpec {st stZ : ReadState}
    (hst : st = .text ∧ stZ = .text ∨ ∃ c, st = .length c ∧ stZ = .length c.gmpSpec)
    {ch : Char} (hch : ch ≠ '%') {x : ReadState × List Piece} (hx : readChar 'l' st ch = some x) :
    readChar 'Z' stZ ch = some (x.1, x.2.map Piece.gmpSpec) ∧ x.1 = .text := by
  rcases hst with ⟨rfl, rfl⟩ | ⟨c, rfl, rfl⟩ <;> simp only [readChar, hch, ite_false] at hx ⊢
  · simp [← Option.some.inj hx, Piece.gmpSpec]
  · simp only [Option.ite_none_right_eq_some] at hx
    obtain ⟨h, hx⟩ := hx
    have : (c.precision.map fun p ↦ some (p.getD 0)).join.getD 0 = c.precision.join.getD 0 := by
      rcases c with ⟨_, _, _ | _ | _⟩ <;> rfl
    simp [← Option.some.inj hx, h, this, Conversion.gmpSpec, Piece.gmpSpec]

private theorem eq_text_of_readFormat_percent_ne_none {st stZ : ReadState}
    (hst : st = .text ∧ stZ = .text ∨ ∃ c, st = .length c ∧ stZ = .length c.gmpSpec)
    {s : List Char} (h : readFormat 'l' st ('%' :: s) ≠ none) : st = .text ∧ stZ = .text := by
  rcases hst with h' | ⟨c, rfl, -⟩
  · exact h'
  · simp [readFormat_cons, readChar] at h

/-- The invariant of the outer loop of `JPoints.Printf.rewriteFormat` on the format `format`, at the
format `fmt` built so far and the index `i`: the format splits at `i` into a prefix `v` and a rest
`w`; the reading of `fmt` with `Z` and that of `v` with `l` give the pieces that correspond under
`JPoints.Printf.Piece.gmpSpec`, and are both outside a conversion or after the length modifiers of
conversions that correspond under `JPoints.Printf.Conversion.gmpSpec`, from which the reading for
`l` takes the rest; after the loop, the rest is empty. -/
def RewriteInvariant (format : String) : Std.WP.WhileInvariant (Array Char × ℕ) Prop :=
  .mk fun exit (fmt, i) ↦ ∃ v w st stZ P, format.toList = v ++ w ∧ v.length = i ∧
    readPrefix 'Z' .text fmt.toList = some (stZ, P.map Piece.gmpSpec) ∧
    readPrefix 'l' .text v = some (st, P) ∧ readFormat 'l' st w ≠ none ∧
    (st = .text ∧ stZ = .text ∨ ∃ c, st = .length c ∧ stZ = .length c.gmpSpec) ∧
    (exit = true → w = [])

/-- The invariant of the inner loop of `JPoints.Printf.rewriteFormat`, the scan after the `%` at the
index `i` of the format `fmt`, at the index `k`: the characters from `i + 1` to `k` are those of the
scan (`JPoints.Printf.scanChars`); after the loop, the character at `k`, if any, is not. -/
def RewriteScanInvariant (fmt : Array Char) (i : ℕ) : Std.WP.WhileInvariant ℕ Prop :=
  .mk fun exit k ↦ i + 1 ≤ k ∧ k ≤ fmt.size ∧
    (∀ ch ∈ (fmt.toList.drop (i + 1)).take (k - (i + 1)), ch ∈ scanChars) ∧
    (exit = true → ∀ ch ∈ (fmt.toList.drop k).head?, ch ∉ scanChars)

/- The character at the index `j` of the format as the C code reads it, with a `NUL` past the
end. -/
private theorem dite_getElem_eq (l : List Char) (j : ℕ) :
    (if h : j < l.length then (⟨l⟩ : Array Char)[j] else '\x00') = l[j]?.getD '\x00' := by
  split <;> simp [*]

private theorem getElem?_append_cons_add_one {α : Type*} (u w : List α) (a : α) (n : ℕ) :
    (u ++ a :: w)[u.length + 1 + n]? = w[n]? := by
  rw [List.getElem?_append_right (by lia), show u.length + 1 + n - u.length = n + 1 by lia,
    List.getElem?_cons_succ]

variable {format : String} {f : List Piece} {fmt : Array Char} {i k : ℕ}

/-- The invariant of the outer loop after the part `t` of the format and the part `tZ` appended to
the format built, read alike from the states of the prefixes. -/
private theorem rewriteInvariant_of_readPrefix {fmt' : Array Char} {i' : ℕ}
    {v w t tZ : List Char} {st stZ xZ : ReadState} {P : List Piece} {x : ReadState × List Piece}
    (hv : format.toList = v ++ t ++ w) (hvi : (v ++ t).length = i')
    (hfmt : fmt'.toList = fmt.toList ++ tZ)
    (hZ : readPrefix 'Z' .text fmt.toList = some (stZ, P.map Piece.gmpSpec))
    (hl : readPrefix 'l' .text v = some (st, P))
    (hZ' : readPrefix 'Z' stZ tZ = some (xZ, x.2.map Piece.gmpSpec))
    (hl' : readPrefix 'l' st t = some x) (hw : readFormat 'l' x.1 w ≠ none)
    (hst : x.1 = .text ∧ xZ = .text ∨ ∃ c, x.1 = .length c ∧ xZ = .length c.gmpSpec) :
    RewriteInvariant format false (fmt', i') :=
  ⟨v ++ t, w, x.1, xZ, P ++ x.2, by simp [hv], hvi, by simp [hfmt, readPrefix_append, hZ, hZ'],
    by simp [readPrefix_append, hl, hl'], hw, hst, nofun⟩

private theorem rewriteInvariant_zero (hf : readFormat 'l' .text format.toList = some f) :
    RewriteInvariant format false ({ toList := [] }, 0) :=
  ⟨[], format.toList, .text, .text, [], rfl, rfl, rfl, rfl, by simp [hf], .inl ⟨rfl, rfl⟩, nofun⟩

private theorem RewriteInvariant.post (hf : readFormat 'l' .text format.toList = some f)
    (h : RewriteInvariant format true (fmt, i)) :
    readFormat 'Z' .text (String.ofList fmt.toList).toList = some (f.map Piece.gmpSpec) := by
  obtain ⟨v, w, st, stZ, P, hv, -, hZ, hl, hw, hst, hnil⟩ := h
  obtain rfl := hnil rfl
  obtain ⟨rfl, rfl⟩ : st = .text ∧ stZ = .text := by
    rcases hst with h | ⟨c, rfl, -⟩
    · exact h
    · simp [readFormat] at hw
  rw [hv, readFormat_append, hl] at hf
  rw [String.toList_ofList, ← List.append_nil fmt.toList, readFormat_append, hZ]
  simp_all [readFormat]

private theorem RewriteInvariant.exit {mb : ℕ}
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : ¬i < format.toList.length) : RewriteInvariant format true (fmt, i) := by
  obtain ⟨-, v, w, st, stZ, P, hv, hvi, hZ, hl, hw, hst, -⟩ := h
  refine ⟨v, w, st, stZ, P, hv, hvi, hZ, hl, hw, hst, fun _ ↦ ?_⟩
  rw [hv] at hlt
  simp only [List.length_append, hvi] at hlt
  exact List.eq_nil_of_length_eq_zero (by lia)

/-- A character other than `%` is copied. -/
private theorem RewriteInvariant.add_one {mb : ℕ}
    (hi : ¬({ toList := format.toList } : Array Char)[i]! = '%')
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length) :
    format.toList.length + 1 - (i + 1) < mb ∧
      RewriteInvariant format false (fmt.push ({ toList := format.toList } : Array Char)[i]!,
        i + 1) := by
  obtain ⟨rfl, v, w, st, stZ, P, hv, rfl, hZ, hl, hw, hst, -⟩ := h
  obtain _ | ⟨ch, w⟩ := w
  · simp [hv] at hlt
  have hch : ({ toList := format.toList } : Array Char)[v.length]! = ch := by
    rw [← Array.getElem!_toList, hv]
    simp
  rw [hch] at hi ⊢
  obtain ⟨x, hx, hw⟩ := readFormat_cons_ne_none_iff.mp hw
  obtain ⟨hxZ, hx1⟩ := readChar_gmpSpec hst hi hx
  exact ⟨by lia, rewriteInvariant_of_readPrefix (t := [ch]) (tZ := [ch]) (by simp [hv])
    (by simp) (by simp) hZ hl (by simpa using hxZ) (by simpa using hx) hw (.inl ⟨hx1, hx1⟩)⟩

/-- A `%%` is copied. -/
private theorem RewriteInvariant.add_two {mb : ℕ}
    (hi : ({ toList := format.toList } : Array Char)[i]! = '%')
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : (if h : i + 1 < format.toList.length then
      ({ toList := format.toList } : Array Char)[i + 1] else '\x00') = '%') :
    format.toList.length + 1 - (i + 1 + 1) < mb ∧
      RewriteInvariant format false
        ((fmt.push ({ toList := format.toList } : Array Char)[i]!).push '%', i + 1 + 1) := by
  obtain ⟨rfl, v, w, st, stZ, P, hv, rfl, hZ, hl, hw, hst, -⟩ := h
  rw [dite_getElem_eq, hv] at h1
  rw [hi]
  rw [← Array.getElem!_toList, hv] at hi
  obtain _ | ⟨c₁, _ | ⟨c₂, w⟩⟩ := w
  · simp [hv] at hlt
  · simp at h1
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right, le_refl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_sub_cancel_left, List.getElem?_cons_succ,
    le_add_iff_nonneg_right, zero_le] at hi h1
  subst hi h1
  obtain ⟨rfl, rfl⟩ := eq_text_of_readFormat_percent_ne_none hst hw
  refine ⟨by lia, rewriteInvariant_of_readPrefix (t := ['%', '%']) (tZ := ['%', '%']) (w := w)
    (x := (.text, [.char '%'])) (xZ := .text) (by simp [hv]) (by simp) (by simp) hZ hl ?_ ?_ ?_
    (.inl ⟨rfl, rfl⟩)⟩ <;> simp_all [readPrefix_cons, readFormat_cons, readChar, Piece.gmpSpec]

/-- The scan after a `%` starts at the next character. -/
private theorem rewriteScanInvariant_add_one (hlt : i < format.toList.length) :
    RewriteScanInvariant { toList := format.toList } i false (i + 1) :=
  ⟨le_rfl, by simpa using hlt, by simp, nofun⟩

private theorem RewriteScanInvariant.add_one {mb : ℕ}
    (h : format.toList.length - k = mb ∧
      RewriteScanInvariant { toList := format.toList } i false k)
    (hk : k < format.toList.length ∧ ({ toList := format.toList } : Array Char)[k]! ∈ scanChars) :
    format.toList.length - (k + 1) < mb ∧
      RewriteScanInvariant { toList := format.toList } i false (k + 1) := by
  obtain ⟨rfl, hik, -, hbody, -⟩ := h
  refine ⟨by lia, by lia, by simpa using hk.1, fun ch hch ↦ ?_, nofun⟩
  rw [show k + 1 - (i + 1) = k - (i + 1) + 1 by lia, List.take_add_one, List.mem_append] at hch
  refine hch.elim (hbody ch) fun hch ↦ ?_
  have hk' : format.toList[k]? = some ch := by
    simpa [show i + 1 + (k - (i + 1)) = k by lia] using hch
  simpa [List.getElem!_eq_getElem?_getD, hk'] using hk.2

private theorem RewriteScanInvariant.exit {mb : ℕ}
    (h : format.toList.length - k = mb ∧
      RewriteScanInvariant { toList := format.toList } i false k)
    (hk : ¬(k < format.toList.length ∧
      ({ toList := format.toList } : Array Char)[k]! ∈ scanChars)) :
    RewriteScanInvariant { toList := format.toList } i true k := by
  obtain ⟨-, hik, hks, hbody, -⟩ := h
  refine ⟨hik, hks, hbody, fun _ ch hch hs ↦ hk ?_⟩
  have hk' : format.toList[k]? = some ch := by simpa [List.head?_drop] using hch
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hk'
  exact ⟨hlt, by simpa [List.getElem!_eq_getElem?_getD, hk'] using hs⟩

/-- After the scan of a conversion from its `%` at the index `i` to the index `k`: the format is the
prefix `v` up to `i`, the `%`, the characters `body` of the scan, the length modifier `l` and a
rest `W`; the readings of the prefix and of the format built are outside a conversion, and the
reading takes the conversion. -/
private theorem RewriteInvariant.exists_conversion {mb : ℕ}
    (hi : ({ toList := format.toList } : Array Char)[i]! = '%')
    (hk : RewriteScanInvariant { toList := format.toList } i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < format.toList.length then
      ({ toList := format.toList } : Array Char)[i + 1] else '\x00') = '%') :
    ∃ v body W c P, format.toList = v ++ '%' :: (body ++ 'l' :: W) ∧ v.length = i ∧
      v.length + 1 + body.length = k ∧ (∀ ch ∈ body, ch ∈ scanChars) ∧
      readPrefix 'Z' .text fmt.toList = some (.text, P.map Piece.gmpSpec) ∧
      readPrefix 'l' .text v = some (.text, P) ∧
      readPrefix 'l' (.flags ⟨[], 0, none⟩) (body ++ ['l']) = some (.length c, []) ∧
      readFormat 'l' (.length c) W ≠ none := by
  obtain ⟨-, v, w, st, stZ, P, hv, rfl, hZ, hl, hw, hst, -⟩ := h
  obtain ⟨hik, -, hbody, hrest⟩ := hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hik
  obtain _ | ⟨ch, w⟩ := w
  · simp [hv] at hlt
  obtain rfl : ch = '%' := by
    rw [← Array.getElem!_toList, hv] at hi
    simpa using hi
  rw [dite_getElem_eq, hv, ← Nat.add_zero (v.length + 1), getElem?_append_cons_add_one] at h1
  simp only [hv, List.head?_drop, getElem?_append_cons_add_one] at hrest
  obtain ⟨rfl, rfl⟩ := eq_text_of_readFormat_percent_ne_none hst hw
  obtain ⟨c, W, hW, hpl, hfW⟩ := exists_readPrefix_percent_eq_length (body := w.take n)
    (rest := w.drop n) (by simpa [hv] using hbody) (by simpa using hrest)
    (fun h ↦ h1 (by simp_all [List.head?_eq_getElem?])) (by simpa using hw)
  have hw' : w = w.take n ++ 'l' :: W := by rw [← hW, List.take_append_drop]
  have hn : (w.take n).length = n := by have := congr(List.length $hw'); simp at this ⊢; lia
  exact ⟨v, w.take n, W, c, P, by rw [hv, ← hw'], rfl, by lia, by simpa [hv] using hbody, hZ, hl,
    hpl, hfW⟩

/-- After the scan of a conversion, the flags, the width and the precision as `gmp_spec` writes them
and a `Z` for its length modifier `l`: the reading of the format and of the format built is after
the length modifiers of conversions that correspond under `JPoints.Printf.Conversion.gmpSpec`, at
the index `k + 1`. -/
private theorem RewriteInvariant.conversion {mb : ℕ}
    (hi : ({ toList := format.toList } : Array Char)[i]! = '%')
    (hk : RewriteScanInvariant { toList := format.toList } i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < format.toList.length then
      ({ toList := format.toList } : Array Char)[i + 1] else '\x00') = '%') :
    format.toList.length + 1 - (k + 1) < mb ∧
      RewriteInvariant format false
        ((fmt.push ({ toList := format.toList } : Array Char)[i]! ++
          { toList := gmpSpec (({ toList := format.toList } : Array Char).extract
            (i + 1) k).toList }).push 'Z', k + 1) := by
  have hks := hk.2.1
  obtain ⟨v, body, W, c, P, hv, rfl, rfl, hbody, hZ, hl, hc, hW⟩ :=
    RewriteInvariant.exists_conversion hi hk h hlt h1
  have hb : (format.toList.drop (v.length + 1)).take body.length = body := by simp [hv]
  refine ⟨by simp at hks; lia [h.1], rewriteInvariant_of_readPrefix
    (t := '%' :: (body ++ ['l'])) (tZ := '%' :: (gmpSpec body ++ ['Z'])) (x := (.length c, []))
    (xZ := .length c.gmpSpec) (by simp [hv]) (by simp; lia) (by simp [hb, hi]) hZ hl ?_ ?_ hW
    (.inr ⟨c, rfl, rfl⟩)⟩
  · simp [readPrefix_cons, readChar, readPrefix_gmpSpec hbody hc]
  · simp [readPrefix_cons, readChar, hc]

/-- After the scan of a conversion, its length modifier `l` and its `d` follow. -/
private theorem RewriteInvariant.lengthModifier {mb : ℕ}
    (hi : ({ toList := format.toList } : Array Char)[i]! = '%')
    (hk : RewriteScanInvariant { toList := format.toList } i true k)
    (h : format.toList.length + 1 - i = mb ∧ RewriteInvariant format false (fmt, i))
    (hlt : i < format.toList.length)
    (h1 : ¬(if h : i + 1 < format.toList.length then
      ({ toList := format.toList } : Array Char)[i + 1] else '\x00') = '%') :
    (if h : k < format.toList.length then
      ({ toList := format.toList } : Array Char)[k] else '\x00') = 'l' ∧
    (if h : k + 1 < format.toList.length then
      ({ toList := format.toList } : Array Char)[k + 1] else '\x00') = 'd' := by
  obtain ⟨v, body, W, c, P, hv, rfl, rfl, -, -, -, -, hW⟩ :=
    RewriteInvariant.exists_conversion hi hk h hlt h1
  obtain _ | ⟨d, W⟩ := W
  · simp [readFormat] at hW
  obtain ⟨y, hy, -⟩ := readFormat_cons_ne_none_iff.mp hW
  simp only [readChar, Option.ite_none_right_eq_some] at hy
  have hv' : format.toList = (v ++ '%' :: body) ++ 'l' :: d :: W := by simp [hv]
  have hlen : v.length + 1 + body.length = (v ++ '%' :: body).length := by simp; lia
  rw [dite_getElem_eq, dite_getElem_eq, hv', hlen, List.getElem?_append_right le_rfl,
    List.getElem?_append_right (by lia), Nat.sub_self, Nat.add_sub_cancel_left]
  simp [hy.1.1]

attribute [local irreducible] RewriteInvariant RewriteScanInvariant in
/-- On a format that `printf` reads (with the length modifier `l`) as the pieces `f`, the format
that `printf_mpz` builds is one that `gmp_printf` reads (with `Z`) as the pieces
`f.map JPoints.Printf.Piece.gmpSpec`. -/
@[spec]
theorem rewriteFormat_spec (format : String) (f : List Piece) :
    ⦃ readFormat 'l' .text format.toList = some f ⦄ rewriteFormat format
    ⦃ fun r ↦ readFormat 'Z' .text r.toList = some (f.map Piece.gmpSpec) ⦄ := by
  vcgen [rewriteFormat] invariants
  | inv1 => RewriteInvariant format
  | inv2 => .ofMeasure fun s : Array Char × ℕ ↦ format.toList.length + 1 - s.2
  | inv3 _ i _ _ _ _ _ => RewriteScanInvariant { toList := format.toList } i
  | inv4 => .ofMeasure fun k : ℕ ↦ format.toList.length - k
  all_goals try vc_simp [Array.getInternal_eq_getElem, List.size_toArray]
  all_goals with_reducible first
    | exact rewriteInvariant_zero ‹_›
    | exact RewriteInvariant.post ‹_› ‹_›
    | exact RewriteInvariant.add_two ‹_› ‹_› ‹_› ‹_›
    | exact rewriteScanInvariant_add_one ‹_›
    | exact RewriteInvariant.conversion ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact absurd (RewriteInvariant.lengthModifier ‹_› ‹_› ‹_› ‹_› ‹_›) ‹_›
    | exact RewriteScanInvariant.add_one ‹_› ‹_›
    | exact RewriteScanInvariant.exit ‹_› ‹_›
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

theorem Conversion.mem_flags_gmpSpec {c : Conversion} {ch : Char} :
    ch ∈ c.gmpSpec.flags ↔ ch ∈ c.flags ∧ (ch = ' ' → '+' ∉ c.flags) ∧
      (ch = '0' → '-' ∉ c.flags ∧ c.precision = none) := by
  simp [Conversion.gmpSpec]
  grind

/-- The sign that `gmp_printf` prints for a nonnegative integer under a conversion rewritten by
`JPoints.Printf.Conversion.gmpSpec` (`JPoints.Printf.printMpz`) is the one that `printf` prints
under the conversion (`JPoints.Printf.printLong`): `+` when it is a flag, else ` ` when that is
one, since `gmp_spec` drops ` ` beside `+`. -/
theorem Conversion.toList_find?_reverse_flags_gmpSpec (c : Conversion) :
    (c.gmpSpec.flags.reverse.find? (· ∈ ['+', ' '])).toList =
      if '+' ∈ c.flags then ['+'] else if ' ' ∈ c.flags then [' '] else [] := by
  rcases h : c.gmpSpec.flags.reverse.find? (· ∈ ['+', ' ']) with _ | ch
  · grind [Conversion.mem_flags_gmpSpec, List.find?_eq_none.mp h '+', List.find?_eq_none.mp h ' ']
  · grind [Conversion.mem_flags_gmpSpec, List.mem_of_find?_eq_some h]

/-- `gmp_printf` prints an integer under a conversion rewritten by
`JPoints.Printf.Conversion.gmpSpec` as `printf` prints it under the conversion: `gmp_spec` drops
the flags that `gmp_printf` reads otherwise than `printf`, ` ` beside `+` and `0` beside `-` or a
precision, and writes the precision `0` for a `.` without digits. -/
theorem printMpz_gmpSpec (c : Conversion) (n : ℤ) : printMpz c.gmpSpec n = printLong c n := by
  simp only [printMpz, printLong, Conversion.mem_flags_gmpSpec,
    Conversion.toList_find?_reverse_flags_gmpSpec]
  rcases c with ⟨fl, w, _ | p⟩
  · by_cases h : '-' ∈ fl <;> by_cases h0 : '0' ∈ fl <;> simp [Conversion.gmpSpec, h, h0]
  · by_cases h : p.getD 0 = 0 ∧ n = 0 <;> simp [Conversion.gmpSpec, h, Nat.add_assoc]

/-- `gmp_printf` prints under the pieces of a format rewritten by `JPoints.Printf.Piece.gmpSpec`,
the pieces that `printf_mpz` gives it, what `printf` prints under the pieces of the format
(`JPoints.Printf.printMpz_gmpSpec`). -/
theorem render_printMpz_map_gmpSpec (f : List Piece) (xs : List ℤ) :
    render printMpz (f.map Piece.gmpSpec) xs = render printLong f xs := by
  fun_induction render printLong f xs <;> simp [render, Piece.gmpSpec, printMpz_gmpSpec, *]

private theorem parseFormat_eq_some_iff {len : Char} {s : String} {f : List Piece} :
    parseFormat len s = some f ↔
      readFormat len .text s.toList = some f ∧ (f.filter (· matches .conv _)).length ≤ 4 := by
  simp only [parseFormat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq]
  exact ⟨fun ⟨ps, hps, hle, hf⟩ ↦ hf ▸ ⟨hps, hle⟩, fun ⟨hps, hle⟩ ↦ ⟨f, hps, hle, rfl⟩⟩

private theorem length_filter_map_gmpSpec (f : List Piece) :
    ((f.map Piece.gmpSpec).filter (· matches .conv _)).length =
      (f.filter (· matches .conv _)).length := by
  induction f with
  | nil => rfl
  | cons p f ih => cases p <;> simp [Piece.gmpSpec, ih]

/-- `gmp_printf` reads the format that `printf_mpz` makes of an admitted format with its pieces,
each rewritten by `JPoints.Printf.Piece.gmpSpec`. -/
theorem parseFormat_run_rewriteFormat {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) :
    parseFormat 'Z' (rewriteFormat format).run = some (f.map Piece.gmpSpec) := by
  rw [parseFormat_eq_some_iff] at hf ⊢
  exact ⟨Std.WP.Id.of_run_eq_wp rfl _ ((rewriteFormat_spec format f).le_wp hf.1),
    (length_filter_map_gmpSpec f).trans_le hf.2⟩

/-- `emit_point` prints the point of the curve given (`JPoints.backPoint`) under the pieces of an
admitted format by `printf`. -/
theorem emitPoint_eq_render {rev neg : Bool} {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    emitPoint rev neg format a b c d = render printLong f [a', b', c', d'] := by
  cases rev <;> cases neg <;>
    simp only [backPoint, emitPoint, hf, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> simp only [h]

/-- `printf_mpz` prints the point of the curve given (`JPoints.backPoint`) by `gmp_printf` under the
pieces of an admitted format, each rewritten by `JPoints.Printf.Piece.gmpSpec`, for a point whose
first nonzero coordinate is positive: without a reversal or a negation it takes the point as it
is. -/
theorem run_printfMpz_eq_render {rev neg : Bool} {format : String} {f : List Piece}
    (hf : parseFormat 'l' format = some f) {a b c d a' b' c' d' : ℤ}
    (hn : 0 < a ∨ a = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c))
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    (printfMpz rev neg format a b c d).run =
      render printMpz (f.map Piece.gmpSpec) [a', b', c', d'] := by
  cases rev <;> cases neg <;> simp only [backPoint, printfMpz, Id.run_bind,
    parseFormat_run_rewriteFormat hf, Bool.false_eq_true, ↓reduceIte, Bool.or_self, Bool.or_true,
    Bool.true_or, true_and, false_and, Id.run_pure] at h ⊢
  · simp only [show ¬(a < 0 ∨ a = 0 ∧ (b < 0 ∨ b = 0 ∧ c < 0)) by lia, ↓reduceIte,
      Prod.mk.injEq] at h
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  all_goals simp only [h]

end JPoints.Printf

end
