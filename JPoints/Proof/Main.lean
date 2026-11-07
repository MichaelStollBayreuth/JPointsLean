/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Proof.Program

import JPoints.Mathlib.Data.List.Basic
import JPoints.Mathlib.Data.Nat.Digits.Defs
import JPoints.Proof.BruteForce
import JPoints.Proof.Containers
import JPoints.Proof.Input
import JPoints.Proof.Printf
import JPoints.Proof.Transform

/-!
# The main theorems

What the program prints, in the terms of the specification. On a command line that `read_input`
accepts (`JPoints.Cli.Input.WF.of_readInput_eq_ok`), unless the sieve has no primes at all, which
`-N` with a value of at most `0` gives, under Sturm's theorem (`JPoints.SturmTheorem`), under `-q`
and with an admitted format of `-f`, the program prints the points of the specification
(`JPoints.orderedPoints`), only the first under `-1`, each in the format, and exits with the status
`0` (`JPoints.Program.run_eq_of_readInput_eq_ok_of_quiet`); without `-q` it prints them after the
head of the report, the message of the curve searched and the text of the choice of the sieve, and
before the numbers of the survivors and of the points
(`JPoints.Program.exists_run_eq_of_readInput_eq_ok_of_quiet_eq_false`). The points of the
specification are the points of the curve given (`JPoints.mem_orderedPoints_iff`), each once
(`JPoints.nodup_orderedPoints`), so that under the default format the points that the program
prints, read back from its text, are the points of the curve, each once
(`JPoints.Program.mem_iff_isPoint_of_run_eq`, `JPoints.Program.nodup_of_run_eq`). The real region
needs a height bound of at most `2 ^ 26`, which `read_input` gives: it refuses larger ones
(`MAX_SEARCH_HEIGHT`, `JPoints.maxSearchHeight`), and up to `2 ^ 26` the products of `row_region`
stay below `2 ^ 53`, where the rounding of the ends of its excluded intervals stays within their
margins. Sturm's theorem, which Mathlib lacks, is needed for the isolating intervals of the real
roots that `real_roots_init` computes, on which the real region and the tube rely.

## Main definitions

* `JPoints.defaultPointText`: the text of a point under the default format of the points.
* `JPoints.Cli.Input.dboundOption`, `JPoints.Cli.Input.pointText`: the bound on the fourth
  coordinate and the text of a point for the globals of the command line.

## Main statements

* `JPoints.mem_orderedPoints_iff`, `JPoints.nodup_orderedPoints`: the points of the specification
  are the points of the curve given, each once.
* `JPoints.textOf_firstIf_flatMap_orderedTriples`: the text of the points that the search of `main`
  prints is that of the points of the specification.
* `JPoints.Program.run_eq_of_readInput_eq_ok_of_quiet`: the program under `-q`.
* `JPoints.Program.exists_run_eq_of_readInput_eq_ok_of_quiet_eq_false`: the program without `-q`.
* `JPoints.Program.eq_firstIf_orderedPoints_of_run_eq`, `JPoints.Program.mem_iff_isPoint_of_run_eq`,
  `JPoints.Program.nodup_of_run_eq`: the points that the program prints under `-q` and the default
  format.

## Implementation notes

The theorems on the program are proved from the contracts of `read_input`, `init_main` and the
search of `main` (`JPoints.Cli.readInput_spec`, `JPoints.initMain_spec`,
`JPoints.Program.mainSearch_spec`, `JPoints.Program.mainSearch_spec_of_quiet_eq_false`); the
program `JPoints.Program.run` is a function, not a component in `Id`, and its value is computed
from the values of its parts. The text that the exact check prints for a point is that of the point
of the curve given (`JPoints.CheckGlobals.text_eq_pointText`). The texts of the points under the
default format are read back at their newlines, and the decimal numbers in each at the separators
`, ` (`List.append_cons_inj_of_notMem_left`, `Int.toString_injective`). The points of the
specification are those of the brute force of the curve searched taken back to the curve given
(`JPoints.orderedPoints_eq_map_bruteForce`), which are the points of the curve given
(`JPoints.isPoint_backPoint_iff`).
-/

@[expose] public section

open scoped Std.WP

namespace JPoints

/-! ### The points of the specification -/

/-- The points of the specification are the points of the curve given, for every curve that the
program does not refuse: those of the curve searched, a curve that the program does not refuse
either (`JPoints.length_searchedCoeffs_le`, `JPoints.degree_searchedCoeffs`,
`JPoints.squarefree_poly_searchedCoeffs`), are the points of its brute force
(`JPoints.mem_bruteForce_iff`), and taken back (`JPoints.backPoint`) they are the points of the
curve given (`JPoints.isPoint_backPoint_iff`), since the reversal of a sextic with `f₀ = 0` and the
negation of a quintic keep the Kummer equation, the lifting, the normalization and the bounds, and
the map back is its own inverse on the normalized points (`JPoints.backPoint_backPoint`). -/
theorem mem_orderedPoints_iff {cs : List ℤ} (h7 : cs.length ≤ 7) (h5 : 5 ≤ degree cs)
    (hsq : Squarefree (poly cs)) {H : ℕ} {all : Bool} {W : Option ℕ} {p : ℤ × ℤ × ℤ × ℤ} :
    p ∈ orderedPoints cs H all W ↔ IsPoint cs H all W p := by
  have h5' : 5 ≤ degree (searchedCoeffs cs).1 := by
    rw [degree_searchedCoeffs h7]
    split_ifs <;> lia
  rw [orderedPoints_eq_map_bruteForce, List.mem_map]
  simp only [mem_bruteForce_iff (length_searchedCoeffs_le h7) h5'
    (squarefree_poly_searchedCoeffs h7 hsq)]
  constructor
  · rintro ⟨⟨a, b, c, d⟩, hq, rfl⟩
    exact (isPoint_backPoint_iff hq.2.2.1).mpr hq
  · intro hp
    obtain ⟨a, b, c, d⟩ := p
    exact ⟨_, (isPoint_backPoint_iff (isNormalized_backPoint _ _ hp.2.2.1)).mp
      (by rwa [backPoint_backPoint _ _ hp.2.2.1]), backPoint_backPoint _ _ hp.2.2.1⟩

/-- The points of the specification are distinct: those of the curve searched are
(`JPoints.nodup_bruteForce`), and the map back is injective on them (`JPoints.injOn_backPoint`). -/
theorem nodup_orderedPoints (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    (orderedPoints cs H all W).Nodup := by
  rw [orderedPoints_eq_map_bruteForce]
  exact (nodup_bruteForce _ H all W).map_on fun p hp q hq h ↦
    injOn_backPoint _ _ (isNormalized_of_mem_bruteForce hp) (isNormalized_of_mem_bruteForce hq) h

/-! ### The text of the points -/

/-- The text of the point `p` under the default format of the points, `(%ld, %ld, %ld, %ld)\n`:
its four coordinates in decimal, between parentheses and separated by commas, on a line of its own.
The definition takes the coordinates by projections, without a pattern match, so that the
comparator challenge, which restates it with the specification in one module, elaborates it to the
same term. -/
def defaultPointText (p : ℤ × ℤ × ℤ × ℤ) : String :=
  s!"({p.1}, {p.2.1}, {p.2.2.1}, {p.2.2.2})\n"

/-- Under the default format, `printf` and `gmp_printf` print a point alike. -/
private theorem pointText_eq_defaultPointText {f : List Printf.Piece}
    (hf : Printf.parseFormat 'l' "(%ld, %ld, %ld, %ld)\n" = some f) (hmax dmax : ℕ)
    (p : ℤ × ℤ × ℤ × ℤ) : pointText f hmax dmax p = defaultPointText p := by
  obtain rfl : f = [.char '(', .conv ⟨[], 0, none⟩, .char ',', .char ' ', .conv ⟨[], 0, none⟩,
      .char ',', .char ' ', .conv ⟨[], 0, none⟩, .char ',', .char ' ', .conv ⟨[], 0, none⟩,
      .char ')', .char '\n'] := Option.some.inj (hf.symm.trans (by decide))
  -- the pieces rewritten, not the texts compared by `rfl`, whose check overflows the stack of the
  -- external checker `nanoda`
  have hs (s : String) : toString s = s := rfl
  have hsep (s : String) : ','.toString ++ (' '.toString ++ s) = ", " ++ s := by
    rw [← String.append_assoc, show ','.toString ++ ' '.toString = ", " by decide]
  simp only [pointText, Printf.render, Printf.printMpz_eq_printLong, ite_self,
    Printf.printLong_eq_toString, defaultPointText, String.append_assoc, String.append_empty, hs,
    hsep, show '('.toString = "(" by decide, show ')'.toString ++ '\n'.toString = ")\n" by decide]

/- The characters of the text of `(a, b, c, d)` under the default format before its newline. -/
private def pointChars (a b c d : ℤ) : List Char :=
  '(' :: ((toString a).toList ++ ',' :: ' ' :: ((toString b).toList ++ ',' :: ' ' ::
    ((toString c).toList ++ ',' :: ' ' :: ((toString d).toList ++ [')']))))

private theorem toList_defaultPointText (a b c d : ℤ) :
    (defaultPointText (a, b, c, d)).toList = pointChars a b c d ++ ['\n'] := by
  simp [defaultPointText, pointChars, ToString.toString]

private theorem eq_of_pointChars_eq {a b c d a' b' c' d' : ℤ}
    (h : pointChars a b c d = pointChars a' b' c' d') : (a, b, c, d) = (a', b', c', d') := by
  have hc (n : ℤ) : ',' ∉ (toString n).toList :=
    Int.notMem_toList_toString (by decide) (by decide) n
  simp only [pointChars, List.cons.injEq, true_and] at h
  obtain ⟨ha, h⟩ := (List.append_cons_inj_of_notMem_left (hc a) (hc a')).mp h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := (List.append_cons_inj_of_notMem_left (hc b) (hc b')).mp h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hc', h⟩ := (List.append_cons_inj_of_notMem_left (hc c) (hc c')).mp h
  simp only [List.cons.injEq, true_and] at h
  simp only [Int.toString_injective (String.toList_inj.mp ha), Int.toString_injective
    (String.toList_inj.mp hb), Int.toString_injective (String.toList_inj.mp hc'),
    Int.toString_injective (String.toList_inj.mp (List.append_cancel_right h))]

/- Two texts of points under the default format, each followed by a text, are equal only for the
same point and the same text after it: each text of a point ends at its only newline. -/
private theorem eq_and_eq_of_defaultPointText_append_eq {p q : ℤ × ℤ × ℤ × ℤ} {s t : String}
    (h : defaultPointText p ++ s = defaultPointText q ++ t) : p = q ∧ s = t := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c', d'⟩ := q
  have hc (n : ℤ) : '\n' ∉ n.repr.toList := Int.notMem_toList_toString (by decide) (by decide) n
  have hn (a b c d : ℤ) : '\n' ∉ pointChars a b c d := by simp [pointChars, hc]
  have h := congr(String.toList $h)
  simp only [String.toList_append, toList_defaultPointText, List.append_assoc,
    List.singleton_append] at h
  obtain ⟨h, hst⟩ := (List.append_cons_inj_of_notMem_left (hn a b c d) (hn a' b' c' d')).mp h
  exact ⟨eq_of_pointChars_eq h, String.toList_inj.mp hst⟩

/-- The points can be read back from their texts under the default format: each text ends at its
only newline, and the decimal numbers in it are separated by `, ` (`String.join_map_injective`). -/
private theorem join_map_defaultPointText_injective :
    Function.Injective fun L : List (ℤ × ℤ × ℤ × ℤ) ↦ String.join (L.map defaultPointText) :=
  String.join_map_injective
    (fun ⟨a, b, c, d⟩ h ↦ by simp [← String.toList_inj, toList_defaultPointText] at h)
    fun _ _ _ _ ↦ eq_and_eq_of_defaultPointText_append_eq

/-! ### The program -/

/-- The bound on the fourth coordinate that the specification takes (`JPoints.IsPoint`) for the
globals `input` that `read_input` leaves: the value of `-w` or the height bound, and none when the
fourth coordinate is not bounded, under `-a` without `-w`. -/
abbrev Cli.Input.dboundOption (input : Cli.Input) : Option ℕ :=
  if input.dbounded then some input.dbound.toNat else none

/-- The text of a point under the format of the pieces `f` (`JPoints.pointText`) for the globals
`input` that `read_input` leaves, with the bounds of the path of machine words of
`check_one_point_final`: `MAX_HEIGHT` under `-a` and the height bound otherwise for the first three
coordinates; for the fourth the value of `-w` or the height bound when the fourth coordinate is
bounded below `MAX_HEIGHT`, and `MAX_HEIGHT` otherwise. -/
abbrev Cli.Input.pointText (input : Cli.Input) (f : List Printf.Piece) : ℤ × ℤ × ℤ × ℤ → String :=
  JPoints.pointText f (if input.allPoints then maxHeight else input.height.toNat)
    (if input.dbounded ∧ input.dbound < maxHeight then input.dbound.toNat else maxHeight)

/-- The text of the points that the search of `main` prints for the globals of the exact check that
it sets (`JPoints.checkGlobalsOf`) is that of the points of the specification
(`JPoints.orderedPoints`), only the first under `-1`, each by `JPoints.Cli.Input.pointText` under
the format of `-f`. -/
theorem textOf_firstIf_flatMap_orderedTriples {input : Cli.Input} {f : List Printf.Piece}
    (hf : Printf.parseFormat 'l' input.printFormat = some f) :
    (checkGlobalsOf input).textOf (firstIf input.onePoint
        ((orderedTriples input.height.toNat).flatMap (checkGlobalsOf input).points)) =
      String.join ((firstIf input.onePoint (orderedPoints input.coeffs.toList input.height.toNat
        input.allPoints input.dboundOption)).map (input.pointText f)) := by
  rw [orderedPoints_eq_map_flatMap_pointsOver, ← map_firstIf, List.map_map, CheckGlobals.textOf]
  congr 1
  refine List.map_congr_left fun p hp ↦ ?_
  obtain ⟨t, -, hp⟩ := List.mem_flatMap.mp ((firstIf_sublist _ _).subset hp)
  have hP := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨a, b, c, d⟩ := p
  exact CheckGlobals.text_eq_pointText hf hP.2.2.1

namespace Program

private theorem run_mainHead_of_quiet {input : Cli.Input} (h : input.quiet = true) :
    (mainHead input).run = "" := by
  simp [mainHead, h]

/-- On a command line that `read_input` accepts with an admitted format of `-f`, the program prints
the head of the report and then the text of the search of `main`, and exits with the status `0`. -/
private theorem run_eq_of_readInput_eq_ok {args : List String} {input : Cli.Input}
    {f : List Printf.Piece} (hi : (Cli.readInput args.toArray).run = .ok input)
    (hf : Printf.parseFormat 'l' input.printFormat = some f) :
    run args =
      ((mainHead input).run ++ (mainSearch (initMain Tables.initial).run input).run, 0) := by
  have h2 := Cli.two_le_size_of_readInput_eq_ok hi
  have hc := Cli.toList_ne_of_readInput_eq_ok hi
  simp only [List.size_toArray] at h2 hc
  simp [run, hi, hf, hc, show ¬args.length < 2 by lia]

/-- The main theorem: on a command line that `read_input` accepts, under `-q` and with an admitted
format of `-f` (of the pieces `f`), the program prints the points of the specification
(`JPoints.orderedPoints`) for the coefficients, the height bound, `-a` and `-w`
(`JPoints.Cli.Input.dboundOption`), in their order, only the first under `-1`, each by
`JPoints.Cli.Input.pointText`, and exits with the status `0`; it needs Sturm's theorem, unless the
sieve has no primes at all, which `-N` with a value of at most `0` gives. The real region needs a
height bound of at most `2 ^ 26`, which `read_input` gives: it refuses larger ones
(`MAX_SEARCH_HEIGHT`, `JPoints.maxSearchHeight`), and up to `2 ^ 26` the products of `row_region`
stay below `2 ^ 53`, where the rounding of the ends of its excluded intervals stays within their
margins. -/
theorem run_eq_of_readInput_eq_ok_of_quiet {args : List String} {input : Cli.Input}
    {f : List Printf.Piece} (hi : (Cli.readInput args.toArray).run = .ok input)
    (hq : input.quiet = true) (hf : Printf.parseFormat 'l' input.printFormat = some f)
    (hS : input.sievePrimes3 = 0 ∨ SturmTheorem) :
    run args = (String.join ((firstIf input.onePoint (orderedPoints input.coeffs.toList
      input.height.toNat input.allPoints input.dboundOption)).map (input.pointText f)), 0) := by
  have hs : (mainSearch (initMain Tables.initial).run input).run = _ :=
    (mainSearch_spec _ input).le_wp
      ⟨initMain_spec.le_wp trivial, .of_readInput_eq_ok hi, hq, hS⟩
  rw [run_eq_of_readInput_eq_ok hi hf, run_mainHead_of_quiet hq, hs,
    textOf_firstIf_flatMap_orderedTriples hf, String.empty_append]

/-- On a command line that `read_input` accepts, without `-q` and with an admitted format of `-f`
(of the pieces `f`), the program prints the head of the report, the message of `normalise_curve`,
the text of the choice of the sieve (`JPoints.choiceText`) for the tables of `init_main` and the
globals of the choice that `main` sets (`JPoints.choiceGlobalsOf`), the points of the specification
(`JPoints.orderedPoints`) as under `-q`, and the numbers of the survivors of the stages and of the
points found (messages 12 and 2) for some totals of the counters, and exits with the status `0`; it
needs Sturm's theorem, unless the sieve has no primes at all, which `-N` with a value of at most `0`
gives. -/
theorem exists_run_eq_of_readInput_eq_ok_of_quiet_eq_false {args : List String}
    {input : Cli.Input} {f : List Printf.Piece} (hi : (Cli.readInput args.toArray).run = .ok input)
    (hq : input.quiet = false) (hf : Printf.parseFormat 'l' input.printFormat = some f)
    (hS : input.sievePrimes3 = 0 ∨ SturmTheorem) :
    ∃ totals : Totals, run args = ((mainHead input).run ++
      (normalizeCurve input.coeffs input.degree.toNat false).run.2 ++
      choiceText (initMain Tables.initial).run (choiceGlobalsOf input) {} ++
      String.join ((firstIf input.onePoint (orderedPoints input.coeffs.toList input.height.toNat
        input.allPoints input.dboundOption)).map (input.pointText f)) ++
      (message { choice := choiceGlobalsOf input, totals } 12 0).run ++
      (message { choice := choiceGlobalsOf input, totals } 2 0).run, 0) := by
  obtain ⟨totals, hs⟩ := Std.WP.Id.of_run_eq_wp rfl _
    ((mainSearch_spec_of_quiet_eq_false (initMain Tables.initial).run input).le_wp
      ⟨initMain_spec.le_wp trivial, .of_readInput_eq_ok hi, hq, hS⟩)
  refine ⟨totals, ?_⟩
  rw [run_eq_of_readInput_eq_ok hi hf, hs, textOf_firstIf_flatMap_orderedTriples hf]
  simp only [String.append_assoc]

/-- On a command line that `read_input` accepts under `-q` and the default format of the points, the
points that the program prints, read back from its text (`JPoints.defaultPointText`), are the points
of the specification (`JPoints.orderedPoints`), only the first under `-1`; it needs Sturm's theorem,
unless the sieve has no primes at all, which `-N` with a value of at most `0` gives. -/
theorem eq_firstIf_orderedPoints_of_run_eq {args : List String} {input : Cli.Input}
    (hi : (Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ SturmTheorem)
    {L : List (ℤ × ℤ × ℤ × ℤ)} (hL : (run args).1 = String.join (L.map defaultPointText)) :
    L = firstIf input.onePoint (orderedPoints input.coeffs.toList input.height.toNat
      input.allPoints input.dboundOption) := by
  obtain ⟨f, hf'⟩ := Option.isSome_iff_exists.mp
    (by decide : (Printf.parseFormat 'l' "(%ld, %ld, %ld, %ld)\n").isSome)
  rw [run_eq_of_readInput_eq_ok_of_quiet hi hq (hf ▸ hf') hS,
    (funext (pointText_eq_defaultPointText hf' _ _) : input.pointText f = defaultPointText)] at hL
  exact join_map_defaultPointText_injective hL.symm

/-- On a command line that `read_input` accepts under `-q`, without `-1` and with the default format
of the points, the points that the program prints, read back from its text
(`JPoints.defaultPointText`), are exactly the points of the curve given (`JPoints.IsPoint`) for the
height bound, `-a` and `-w`; it needs Sturm's theorem, unless the sieve has no primes at all, which
`-N` with a value of at most `0` gives. -/
theorem mem_iff_isPoint_of_run_eq {args : List String} {input : Cli.Input}
    (hi : (Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ SturmTheorem)
    (h1 : input.onePoint = false) {L : List (ℤ × ℤ × ℤ × ℤ)}
    (hL : (run args).1 = String.join (L.map defaultPointText)) {p : ℤ × ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint input.coeffs.toList input.height.toNat input.allPoints
      input.dboundOption p := by
  have hw := Cli.Input.WF.of_readInput_eq_ok hi
  rw [eq_firstIf_orderedPoints_of_run_eq hi hq hf hS hL, h1, firstIf_false]
  exact mem_orderedPoints_iff (by simp [hw.size_coeffs])
    (by lia [hw.degree_coeffs, hw.five_le_degree]) hw.squarefree

/-- On a command line that `read_input` accepts under `-q` and the default format of the points, the
program prints each point at most once; it needs Sturm's theorem, unless the sieve has no primes at
all, which `-N` with a value of at most `0` gives. -/
theorem nodup_of_run_eq {args : List String} {input : Cli.Input}
    (hi : (Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ SturmTheorem)
    {L : List (ℤ × ℤ × ℤ × ℤ)} (hL : (run args).1 = String.join (L.map defaultPointText)) :
    L.Nodup := by
  rw [eq_firstIf_orderedPoints_of_run_eq hi hq hf hS hL]
  exact (firstIf_sublist _ _).nodup (nodup_orderedPoints _ _ _ _)

end Program

end JPoints

end
