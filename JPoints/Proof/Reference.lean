/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints.Model.Check
public import JPoints.Spec.Basic
public import Mathlib.Order.Prod.Lex.Basic

import JPoints.Mathlib.RingTheory.Int.Basic
import JPoints.Proof.Order
import JPoints.Proof.Poly
import JPoints.Proof.Printf
import Mathlib.Algebra.Order.Ring.Abs

/-!
# The reference layer

What the contracts of the search say, in the terms of the specification. Over each triple `t` of
the search lie the points `JPoints.pointsOver cs H all W t`: the candidates of the Kummer equation
over `t` that are points, in the order of its roots; the list of the points of the specification,
`JPoints.orderedPoints`, is that of the points over the triples of `JPoints.orderedTriples H` of
the curve searched, taken back to the curve given. The globals of the exact check
(`JPoints.CheckGlobals`) name the curve searched and the bounds of the search, and so the points
over a triple (`JPoints.CheckGlobals.points`), and the text that the check prints for a point that
it finds (`JPoints.CheckGlobals.text`), by `printf` on machine words or by `gmp_printf` on GMP
integers; at the top this is the text of the point of the curve given (`JPoints.pointText`). Under
`-1` the program prints the first point only (`JPoints.firstIf`).

The search takes the triples in the order of `JPoints.orderedTriples H`: first those on the conic
`b² = 4ac` (`JPoints.conicTriples`), `(0, 0, 1)` and then those of the double points
(`JPoints.doubleTriples`), then the others (`JPoints.mainTriples`), unit of work by unit of work,
the first coordinate `a` (`JPoints.unitTriples`). It drops triples by tests that keep every triple
over which a point lies, so that the points over the triples it keeps are those over all of them
(`List.flatMap_filter_of_ne`).

## Main definitions

* `JPoints.pointsOver`: the points over a triple.
* `JPoints.HasPointOver`: a point of the Kummer surface that lifts lies over a triple.
* `JPoints.CheckGlobals.coeffList`, `JPoints.CheckGlobals.H`, `JPoints.CheckGlobals.W`,
  `JPoints.CheckGlobals.points`: the curve searched, the bounds and the points over a triple.
* `JPoints.CheckGlobals.WF`: the globals of the exact check as `main` sets them.
* `JPoints.CheckGlobals.hmax`, `JPoints.CheckGlobals.dmax`, `JPoints.CheckGlobals.wordsPath`,
  `JPoints.CheckGlobals.text`, `JPoints.CheckGlobals.textOf`: the text of the points found.
* `JPoints.firstIf`: the first element only, under `-1`.
* `JPoints.pointText`: the text of a point of the curve given.
* `JPoints.conicTriples`, `JPoints.mainTriples`, `JPoints.doubleTriples`, `JPoints.unitTriples`,
  `JPoints.doubleRow`:
  the parts of the enumeration.

## Main statements

* `JPoints.orderedPoints_eq_map_flatMap_pointsOver`: the points of the specification are the
  points over the triples of the curve searched, taken back.
* `JPoints.CheckGlobals.one_le_H`, `JPoints.CheckGlobals.degree_le_six`: the bounds of the
  globals of the exact check.
* `JPoints.backPoint_eq_or_eq_neg`: the map back as a signed permutation.
* `JPoints.max_abs_eq_and_abs_eq_of_backPoint_eq`, `JPoints.CheckGlobals.text_eq_pointText`: the
  text of a point found is that of the point of the curve given.
* `JPoints.firstIf_append`, `JPoints.map_firstIf`, `JPoints.firstIf_append_of_imp`,
  `JPoints.firstIf_append_of_ne_nil`, `JPoints.firstIf_sublist`,
  `JPoints.firstIf_eq_self_of_length_le_one`: the first point of a concatenation, and of a list
  mapped, the first point is one of the list, and a list of at most one point is printed whole.
* `JPoints.mem_doubleTriples_iff`, `JPoints.mem_conicTriples_iff`, `JPoints.pairwise_boxTriples`,
  `JPoints.pairwise_doubleTriples`, `JPoints.pairwise_ite_append_doubleTriples`: the triples of the
  conic, and the lexicographic order of the triples.
* `JPoints.orderedTriples_eq_append`, `JPoints.conicTriples_eq`, `JPoints.mainTriples_eq`,
  `JPoints.flatMap_orderedTriples`: the decomposition of the enumeration.

## Implementation notes

The definitions are on Mathlib and on the specification, and read the structures of the model
(`JPoints.CheckGlobals`, `JPoints.Printf.Piece`). The bounds and the curve that the globals of the
exact check hold are abbreviations, so that they unfold where the specification is needed. The
triples on the conic are those of the double points after `(0, 0, 1)` because both lists are in
lexicographic order and have the same elements (`List.Pairwise.eq_of_mem_iff`).
-/

@[expose] public section

namespace JPoints

/-! ### The points over a triple -/

/-- The points over the triple `t` of the curve with the coefficients `cs`, within the bounds `H`,
`all` and `W` of the search: the candidates of the Kummer equation over `t`
(`JPoints.kummerPoints`) that are points (`JPoints.IsPoint`), in the order of its roots, the order
in which the program prints them. -/
def pointsOver (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) (t : ℤ × ℤ × ℤ) :
    List (ℤ × ℤ × ℤ × ℤ) :=
  (kummerPoints (cs.getD · 0) t).filter (IsPoint cs H all W)

/-- The points of the specification are the points over the triples of the search of the curve
searched (`JPoints.searchedCoeffs`), taken back to the curve given. -/
theorem orderedPoints_eq_map_flatMap_pointsOver (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    orderedPoints cs H all W = ((orderedTriples H).flatMap
      (pointsOver (searchedCoeffs cs).1 H all W)).map
        (backPoint (searchedCoeffs cs).2.1 (searchedCoeffs cs).2.2) := by
  rw [orderedPoints]
  generalize searchedCoeffs cs = x
  obtain ⟨cs', rev, neg⟩ := x
  exact congr(List.map _ $List.filter_flatMap)

/-- A point of the Kummer surface of the curve with the coefficients `cs` that comes from a
rational point of the Jacobian lies over the triple `t`, whatever the bounds of the search: a
candidate of `JPoints.kummerPoints` over `t` for which `JPoints.Lifts` holds. The tests of the
sieve keep the triples over which such a point lies; every point over a triple is one
(`JPoints.hasPointOver_of_pointsOver_ne_nil`). -/
def HasPointOver (cs : List ℤ) (t : ℤ × ℤ × ℤ) : Prop :=
  ∃ p ∈ kummerPoints (cs.getD · 0) t, Lifts (cs.getD · 0) p.1 p.2.1 p.2.2.1 p.2.2.2

theorem hasPointOver_of_pointsOver_ne_nil {cs : List ℤ} {H : ℕ} {all : Bool} {W : Option ℕ}
    {t : ℤ × ℤ × ℤ} (h : pointsOver cs H all W t ≠ []) : HasPointOver cs t := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hk, hP⟩ := List.mem_filter.mp hp
  exact ⟨p, hk, (of_decide_eq_true hP).2.1⟩

/-! ### The globals of the exact check -/

namespace CheckGlobals

/-- The coefficients `f₀, …, f₆` of the curve searched, the list `cs` of the specification. -/
abbrev coeffList (gl : CheckGlobals) : List ℤ := gl.curve.coeffs.toList

/-- The height bound as a natural number, the bound `H` of the specification. -/
abbrev H (gl : CheckGlobals) : ℕ := gl.height.toNat

/-- The bound on the fourth coordinate, the bound `W` of the specification: the bound of `-w`, or
the height bound, when the fourth coordinate is bounded, and none otherwise. -/
abbrev W (gl : CheckGlobals) : Option ℕ := if gl.dbounded then some gl.dbound.toNat else none

/-- The points over the triple `t` of the curve searched within the bounds of the search
(`JPoints.pointsOver`). -/
abbrev points (gl : CheckGlobals) (t : ℤ × ℤ × ℤ) : List (ℤ × ℤ × ℤ × ℤ) :=
  pointsOver gl.coeffList gl.H gl.allPoints gl.W t

/-- The globals of the exact check as `main` sets them from a command line that `read_input`
accepts: the curve searched has seven coefficients and the degree of their list, `5` or `6`; the
coefficients of the quartic `K₀` are those of `kummer_init`; `1 ≤ height ≤ MAX_HEIGHT`; the bound
on the fourth coordinate is at least `1` when there is one, and there is one unless `-a` is
given. -/
structure WF (gl : CheckGlobals) : Prop where
  /-- The curve searched has seven coefficients. -/
  size_coeffs : gl.curve.coeffs.size = 7
  /-- The degree of the curve searched is that of its coefficients. -/
  degree_coeffList : degree gl.coeffList = gl.curve.degree
  /-- The curve searched has degree at least `5`. -/
  five_le_degree : 5 ≤ gl.curve.degree
  /-- The coefficients of the quartic `K₀` are those of `kummer_init`. -/
  kummer_eq : gl.kummer = kummerInit gl.curve.coeffs
  /-- The height bound is positive. -/
  one_le_height : 1 ≤ gl.height
  /-- The height bound is at most `MAX_HEIGHT`. -/
  height_le_maxHeight : gl.height ≤ maxHeight
  /-- The bound on the fourth coordinate is positive when there is one. -/
  one_le_dbound : gl.dbounded = true → 1 ≤ gl.dbound
  /-- The fourth coordinate is bounded unless `-a` is given. -/
  allPoints_of_dbounded_eq_false : gl.dbounded = false → gl.allPoints = true

theorem one_le_H {gl : CheckGlobals} (hgl : gl.WF) : 1 ≤ gl.H := by
  lia [hgl.one_le_height]

theorem degree_le_six {gl : CheckGlobals} (hgl : gl.WF) : gl.curve.degree ≤ 6 :=
  hgl.degree_coeffList ▸ degree_toList_le_six hgl.size_coeffs

/-! ### The text of the points found -/

/-- The bound on the first three coordinates of a point on the path of machine words of
`check_one_point_final`, the numerator of its bound `h = H / m` of the scale: `MAX_HEIGHT` under
`-a`, else the height bound. -/
abbrev hmax (gl : CheckGlobals) : ℕ := if gl.allPoints then maxHeight else gl.height.toNat

/-- The bound `dmax` on the fourth coordinate of a point on the path of machine words of
`check_one_point_final`: the bound of `-w` or the height bound when the fourth coordinate is
bounded below `MAX_HEIGHT`, else `MAX_HEIGHT`. -/
abbrev dmax (gl : CheckGlobals) : ℕ :=
  if gl.dbounded = true ∧ gl.dbound < maxHeight then gl.dbound.toNat else maxHeight

/-- Whether `check_one_point_final` checks and prints the point `(a, b, c, d)` of the curve
searched on machine words (`JPoints.checkOnePointWords`), rather than on GMP integers
(`JPoints.checkOnePointMpz`): its first three coordinates at most `JPoints.CheckGlobals.hmax` and
its fourth at most `JPoints.CheckGlobals.dmax` in absolute value, which for the scale `g` of the
point over a triple of maximum `m` is `g ≤ hmax / m`. -/
def wordsPath (gl : CheckGlobals) : ℤ × ℤ × ℤ × ℤ → Bool
  | (a, b, c, d) => decide (max |a| (max |b| |c|) ≤ gl.hmax ∧ |d| ≤ gl.dmax)

/-- The text that the exact check prints for the point `(a, b, c, d)` of the curve searched that
it finds: by `printf` (`JPoints.Printf.emitPoint`) on the path of machine words
(`JPoints.CheckGlobals.wordsPath`), by `gmp_printf` (`JPoints.Printf.printfMpz`) otherwise, under
the format of `-f`, the point taken back to the curve given. -/
def text (gl : CheckGlobals) : ℤ × ℤ × ℤ × ℤ → String
  | (a, b, c, d) => if gl.wordsPath (a, b, c, d) then
      Printf.emitPoint gl.curve.reversed gl.curve.negated gl.printFormat a b c d
    else (Printf.printfMpz gl.curve.reversed gl.curve.negated gl.printFormat a b c d).run

/-- The text that the exact check prints for the points `L` of the curve searched that it finds,
in their order. -/
def textOf (gl : CheckGlobals) (L : List (ℤ × ℤ × ℤ × ℤ)) : String := String.join (L.map gl.text)

@[simp]
theorem textOf_nil (gl : CheckGlobals) : gl.textOf [] = "" := by
  simp [textOf]

@[simp]
theorem textOf_cons (gl : CheckGlobals) (p : ℤ × ℤ × ℤ × ℤ) (L : List (ℤ × ℤ × ℤ × ℤ)) :
    gl.textOf (p :: L) = gl.text p ++ gl.textOf L := by
  simp [textOf]

@[simp]
theorem textOf_append (gl : CheckGlobals) (L₁ L₂ : List (ℤ × ℤ × ℤ × ℤ)) :
    gl.textOf (L₁ ++ L₂) = gl.textOf L₁ ++ gl.textOf L₂ := by
  simp [textOf]

end CheckGlobals

/-! ### The first point -/

/-- The list `L`, or its first element only when `b` holds: what the program prints of the points
that it finds under `-1` (`b`), where it stops at the first. -/
def firstIf {α : Type*} (b : Bool) (L : List α) : List α := if b then L.take 1 else L

section firstIf

variable {α β : Type*}

@[simp]
theorem firstIf_false (L : List α) : firstIf false L = L := rfl

@[simp]
theorem firstIf_true (L : List α) : firstIf true L = L.take 1 := rfl

@[simp]
theorem firstIf_nil (b : Bool) : firstIf b ([] : List α) = [] := by
  cases b <;> rfl

/-- The first element of a concatenation under `-1` is that of the first part, unless it is
empty. -/
theorem firstIf_append (b : Bool) (L₁ L₂ : List α) :
    firstIf b (L₁ ++ L₂) = firstIf b L₁ ++ if b = true ∧ L₁ ≠ [] then [] else firstIf b L₂ := by
  cases b <;> cases L₁ <;> simp

theorem map_firstIf (f : α → β) (b : Bool) (L : List α) :
    (firstIf b L).map f = firstIf b (L.map f) := by
  cases b <;> simp [List.map_take]

theorem firstIf_sublist (b : Bool) (L : List α) : (firstIf b L).Sublist L := by
  cases b
  · exact .refl L
  · exact L.take_sublist 1

/-- A list of at most one element is printed whole, under `-1` or not. -/
theorem firstIf_eq_self_of_length_le_one (b : Bool) {L : List α} (h : L.length ≤ 1) :
    firstIf b L = L := by
  cases b
  · rfl
  · exact List.take_of_length_le h

/-- A list that is empty under `-1` is printed whole. -/
theorem firstIf_eq_self_of_imp {b : Bool} {L : List α} (h : b = true → L = []) :
    firstIf b L = L := by
  cases b <;> simp_all

/-- The first element of a concatenation under `-1` when the first part is empty under `-1`. -/
theorem firstIf_append_of_imp {b : Bool} {L₁ L₂ : List α} (h : b = true → L₁ = []) :
    firstIf b L₁ ++ firstIf b L₂ = firstIf b (L₁ ++ L₂) := by
  cases b <;> simp_all

/-- Under `-1`, the first element of a list whose first part is empty and whose second is not is
that of the second part. -/
theorem firstIf_append_of_ne_nil {b : Bool} {L₁ L₂ L₃ : List α} (hb : b = true)
    (h₁ : b = true → L₁ = []) (h₂ : L₂ ≠ []) :
    firstIf b L₁ ++ firstIf b L₂ = firstIf b (L₁ ++ L₂ ++ L₃) := by
  obtain ⟨x, L₂, rfl⟩ := List.exists_cons_of_ne_nil h₂
  simp [hb, h₁ hb]

end firstIf

/-! ### The text of a point of the curve given -/

/-- The text that the program prints for the point `p` of the curve given, under the admitted
format of the pieces `f` (`JPoints.Printf.parseFormat`): by `printf` (`JPoints.Printf.printLong`)
when its first three coordinates are at most `hmax` and its fourth at most `dmax` in absolute value,
the path of machine words of the exact check, and by `gmp_printf` (`JPoints.Printf.printMpz`)
otherwise. The two differ under some flags of a format. The definition takes the coordinates by
projections, without a pattern match, so that the comparator challenge, which restates it with the
specification in one module, elaborates it to the same term. -/
def pointText (f : List Printf.Piece) (hmax dmax : ℕ) (p : ℤ × ℤ × ℤ × ℤ) : String :=
  if max |p.1| (max |p.2.1| |p.2.2.1|) ≤ hmax ∧ |p.2.2.2| ≤ dmax then
    Printf.render Printf.printLong f [p.1, p.2.1, p.2.2.1, p.2.2.2]
  else Printf.render Printf.printMpz f [p.1, p.2.1, p.2.2.1, p.2.2.2]

/-- The map back to the curve given is the exchange of the first and the third coordinate after a
reversal and the negation of the second after a negation, followed by a sign. -/
theorem backPoint_eq_or_eq_neg (rev neg : Bool) (a b c d : ℤ) :
    backPoint rev neg (a, b, c, d) =
        (if rev then c else a, if neg then -b else b, if rev then a else c, d) ∨
      backPoint rev neg (a, b, c, d) =
        (-(if rev then c else a), -(if neg then -b else b), -(if rev then a else c), -d) := by
  cases rev <;> cases neg <;> simp only [backPoint] <;> split_ifs <;> simp

/-- The map back to the curve given (`JPoints.backPoint`) keeps the largest absolute value of the
first three coordinates and the absolute value of the fourth. -/
theorem max_abs_eq_and_abs_eq_of_backPoint_eq {rev neg : Bool} {a b c d a' b' c' d' : ℤ}
    (h : backPoint rev neg (a, b, c, d) = (a', b', c', d')) :
    max |a'| (max |b'| |c'|) = max |a| (max |b| |c|) ∧ |d'| = |d| := by
  rcases backPoint_eq_or_eq_neg rev neg a b c d with h' | h' <;> rw [h] at h' <;>
    simp only [Prod.mk.injEq] at h' <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h' <;>
    cases rev <;> cases neg <;> simp [abs_neg, max_comm, max_left_comm]

/-- The text that the exact check prints for a normalized point `p` of the curve searched is that
of the point of the curve given, under an admitted format: both paths take the point back
(`JPoints.backPoint`), which keeps the absolute values of the coordinates
(`JPoints.max_abs_eq_and_abs_eq_of_backPoint_eq`), and the format that `printf_mpz` gives
`gmp_printf` has the pieces of the format of `-f` (`JPoints.Printf.run_printfMpz_eq_render`). -/
theorem CheckGlobals.text_eq_pointText {gl : CheckGlobals} {f : List Printf.Piece}
    (hf : Printf.parseFormat 'l' gl.printFormat = some f) {p : ℤ × ℤ × ℤ × ℤ}
    (hp : IsNormalized p.1 p.2.1 p.2.2.1 p.2.2.2) :
    gl.text p = pointText f gl.hmax gl.dmax (backPoint gl.curve.reversed gl.curve.negated p) := by
  obtain ⟨a, b, c, d⟩ := p
  generalize hq : backPoint gl.curve.reversed gl.curve.negated (a, b, c, d) = q
  obtain ⟨a', b', c', d'⟩ := q
  obtain ⟨hm, hd⟩ := max_abs_eq_and_abs_eq_of_backPoint_eq hq
  rw [text, pointText, wordsPath, Printf.emitPoint_eq_render hf hq,
    Printf.run_printfMpz_eq_render hf hp.2 hq, hm, hd]
  simp only [decide_eq_true_eq]

/-! ### The parts of the enumeration -/

/-- The triples of `JPoints.orderedTriples H` on the conic `b² = 4ac`, in lexicographic order:
`(0, 0, 1)` and the triples of the double points, which the program searches first. -/
def conicTriples (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  (boxTriples H).filter fun (a, b, c) ↦ b ^ 2 = 4 * a * c

/-- The triples of `JPoints.orderedTriples H` off the conic `b² = 4ac`, in lexicographic order:
those of the main search. -/
def mainTriples (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  (boxTriples H).filter fun (a, b, c) ↦ b ^ 2 ≠ 4 * a * c

theorem orderedTriples_eq_append (H : ℕ) : orderedTriples H = conicTriples H ++ mainTriples H :=
  rfl

/-- The triples `(s², 2st, t²)` of the double points with the first coordinate `s²`, in the order
of `find_double_points`: the `t` coprime to `s` with `t² ≤ H` and `|2st| ≤ H`, increasing. -/
def doubleRow (H : ℕ) (s : ℤ) : List (ℤ × ℤ × ℤ) :=
  ((intRange H).filter fun t : ℤ ↦ t ^ 2 ≤ H ∧ |2 * s * t| ≤ H ∧ Int.gcd s t = 1).map
    fun t ↦ (s ^ 2, 2 * s * t, t ^ 2)

/-- The triples `(s², 2st, t²)` of the double points, in the order of `find_double_points`: the
`s ≥ 1` with `s² ≤ H` in increasing order, and for each the triples of its row
(`JPoints.doubleRow`). -/
def doubleTriples (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  (List.range' 1 H.sqrt).flatMap fun s : ℕ ↦ doubleRow H s

theorem mem_doubleTriples_iff {H : ℕ} {a b c : ℤ} :
    (a, b, c) ∈ doubleTriples H ↔ ∃ s t : ℤ, 0 < s ∧ s ^ 2 ≤ H ∧ t ^ 2 ≤ H ∧ |2 * s * t| ≤ H ∧
      Int.gcd s t = 1 ∧ (a, b, c) = (s ^ 2, 2 * s * t, t ^ 2) := by
  simp only [doubleTriples, doubleRow, List.mem_flatMap, List.mem_range'_1, List.mem_map,
    List.mem_filter, mem_intRange_iff, decide_eq_true_eq]
  refine ⟨fun ⟨s, hs, t, ⟨_, h⟩, he⟩ ↦ ⟨s, t, by lia, ?_, h.1, h.2.1, h.2.2, he.symm⟩,
    fun ⟨s, t, hs, hsH, h⟩ ↦ ?_⟩
  · rw [sq]
    exact_mod_cast Nat.le_sqrt.mp (by lia)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hs.le
  refine ⟨n, ⟨by lia, Nat.lt_one_add_iff.mpr (Nat.le_sqrt.mpr (by rw [sq] at hsH; lia))⟩, t,
    ⟨?_, h.1, h.2.1, h.2.2.1⟩, h.2.2.2.symm⟩
  rw [Int.abs_eq_natAbs]
  exact (Int.natAbs_le_self_sq t).trans h.1

/-- The triples of the box are in lexicographic order. -/
theorem pairwise_boxTriples (H : ℕ) :
    (boxTriples H).Pairwise fun x y ↦ toLex (x.1, toLex x.2) < toLex (y.1, toLex y.2) := by
  refine .filter _ (List.pairwise_flatMap.mpr ⟨fun a _ ↦ List.pairwise_flatMap.mpr
    ⟨fun b _ ↦ List.pairwise_map.mpr ((pairwise_lt_intRange H).imp fun h ↦ ?_),
      (pairwise_lt_intRange H).imp fun h x hx y hy ↦ ?_⟩, List.pairwise_lt_range.imp
        fun h x hx y hy ↦ ?_⟩)
  · simp [Prod.Lex.toLex_lt_toLex, h]
  · simp only [List.mem_map] at hx hy
    obtain ⟨c, -, rfl⟩ := hx
    obtain ⟨c', -, rfl⟩ := hy
    simp [Prod.Lex.toLex_lt_toLex, h]
  · simp only [List.mem_flatMap, List.mem_map] at hx hy
    obtain ⟨b, -, c, -, rfl⟩ := hx
    obtain ⟨b', -, c', -, rfl⟩ := hy
    simp [Prod.Lex.toLex_lt_toLex, h]

/-- The triples of the double points are in lexicographic order: `s²` increases with `s`, and `2st`
with `t` for each `s > 0`. -/
theorem pairwise_doubleTriples (H : ℕ) :
    (doubleTriples H).Pairwise fun x y ↦ toLex (x.1, toLex x.2) < toLex (y.1, toLex y.2) := by
  refine List.pairwise_flatMap.mpr ⟨fun s hs ↦ List.pairwise_map.mpr
    (((pairwise_lt_intRange H).filter _).imp fun h ↦ ?_),
      (List.pairwise_lt_range' (s := 1) (n := H.sqrt) 1).imp fun h x hx y hy ↦ ?_⟩
  · simp only [List.mem_range'_1] at hs
    simp only [Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or]
    exact .inl (mul_lt_mul_of_pos_left h (by lia))
  · simp only [doubleRow, List.mem_map] at hx hy
    obtain ⟨t, -, rfl⟩ := hx
    obtain ⟨t', -, rfl⟩ := hy
    simp only [Prod.Lex.toLex_lt_toLex]
    exact .inl (mod_cast Nat.pow_lt_pow_left h two_ne_zero)

/-- `(0, 0, 1)`, when it is in the box, and then the triples of the double points are in
lexicographic order. -/
theorem pairwise_ite_append_doubleTriples (H : ℕ) :
    ((if 1 ≤ H then [(0, 0, 1)] else []) ++ doubleTriples H).Pairwise
      fun x y : ℤ × ℤ × ℤ ↦ toLex (x.1, toLex x.2) < toLex (y.1, toLex y.2) := by
  refine List.pairwise_append.mpr ⟨by split_ifs <;> simp, pairwise_doubleTriples H,
    fun x hx ⟨a, b, c⟩ hy ↦ ?_⟩
  split_ifs at hx <;> simp only [List.mem_singleton, List.not_mem_nil] at hx
  subst hx
  obtain ⟨s, _, hs, -, -, -, -, he⟩ := mem_doubleTriples_iff.mp hy
  simp only [Prod.mk.injEq] at he
  simp only [Prod.Lex.toLex_lt_toLex, he.1]
  exact .inl (by positivity)

theorem mem_conicTriples_iff {H : ℕ} {a b c : ℤ} :
    (a, b, c) ∈ conicTriples H ↔ (a, b, c) = (0, 0, 1) ∧ 1 ≤ H ∨ (a, b, c) ∈ doubleTriples H := by
  rw [conicTriples, List.mem_filter, mem_boxTriples_iff, mem_doubleTriples_iff, decide_eq_true_eq]
  refine ⟨fun ⟨⟨hg, hn, ha, hb, hc⟩, h⟩ ↦ ?_, ?_⟩
  · rcases hn with ha0 | ⟨rfl, hn⟩
    · obtain ⟨s, t, hs, hst, he⟩ := Int.exists_eq_of_sq_eq_four_mul_mul hg ha0 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inr ⟨s, t, hs, by simpa using ha, by simpa using hc, hb, hst, rfl⟩
    · obtain rfl : b = 0 := by simpa using h
      simp only [gcd_zero_left, normalize_idem, lt_self_iff_false, true_and, false_or] at hg hn
      obtain rfl : c = 1 := (Int.normalize_of_nonneg hn.le).symm.trans hg
      exact .inl ⟨rfl, by simpa using hc⟩
  · rintro (⟨h, hH⟩ | ⟨s, t, hs, hsH, htH, hst, hg, he⟩)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨⟨by decide, by simp, by simp, by simp, by simpa⟩, by simp⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨⟨Int.gcd_sq_gcd_two_mul_mul_sq_eq_one hg, .inl (by positivity), by simpa, hst,
        by simpa⟩, by ring⟩

/-- The triples on the conic are `(0, 0, 1)` and those of the double points: a coprime triple with
`b² = 4ac` and `a > 0` is `(s², 2st, t²)` with `s > 0` and `gcd(s, t) = 1`
(`Int.exists_eq_of_sq_eq_four_mul_mul`), and these come in the lexicographic order of `(s, t)`
(`JPoints.pairwise_doubleTriples`). -/
theorem conicTriples_eq (H : ℕ) :
    conicTriples H = (if 1 ≤ H then [(0, 0, 1)] else []) ++ doubleTriples H := by
  refine (List.map_injective_iff (f := fun t : ℤ × ℤ × ℤ ↦ toLex (t.1, toLex t.2))).mpr
    (fun x y h ↦ Prod.ext_iff.mpr (by simpa using h)) (List.Pairwise.eq_of_mem_iff
      (List.pairwise_map.mpr ((pairwise_boxTriples H).filter _))
      (List.pairwise_map.mpr (pairwise_ite_append_doubleTriples H)) fun y ↦ ?_)
  have hmem (t : ℤ × ℤ × ℤ) :
      t ∈ conicTriples H ↔ t ∈ (if 1 ≤ H then [(0, 0, 1)] else []) ++ doubleTriples H := by
    obtain ⟨a, b, c⟩ := t
    rw [mem_conicTriples_iff, List.mem_append]
    split_ifs with hH <;> simp [hH]
  simp only [List.mem_map, hmem]

/-- The triples of the main search with the first coordinate `a`: the coprime triples `(a, b, c)`
of the box off the conic `b² = 4ac` whose first nonzero coordinate is positive, in lexicographic
order, `b` increasing and for each `b` the third coordinate `c`, as the main search takes them for
the unit of work of `a` (for `a = 0` the rows `b ≥ 1`). -/
def unitTriples (H a : ℕ) : List (ℤ × ℤ × ℤ) :=
  (intRange H).flatMap fun b ↦
    ((intRange H).filter fun c ↦ gcd (a : ℤ) (gcd b c) = 1 ∧
        (0 < (a : ℤ) ∨ (a : ℤ) = 0 ∧ (0 < b ∨ b = 0 ∧ 0 < c)) ∧ b ^ 2 ≠ 4 * a * c).map
      fun c ↦ ((a : ℤ), b, c)

theorem mainTriples_eq (H : ℕ) : mainTriples H = (List.range (H + 1)).flatMap (unitTriples H) := by
  rw [mainTriples, boxTriples, List.filter_filter, List.filter_flatMap]
  refine List.flatMap_congr fun a _ ↦ ?_
  rw [unitTriples, List.filter_flatMap]
  refine List.flatMap_congr fun b _ ↦ ?_
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun c _ ↦ Bool.eq_iff_iff.mpr ?_
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `List.flatMap` over the triples of the search for `H ≥ 1`: over `(0, 0, 1)`, over the
triples of the double points (`JPoints.doubleTriples`) and over those of the main search
(`JPoints.mainTriples`), in this order. -/
theorem flatMap_orderedTriples {β : Type*} {H : ℕ} (hH : 1 ≤ H) (f : ℤ × ℤ × ℤ → List β) :
    (orderedTriples H).flatMap f =
      f (0, 0, 1) ++ (doubleTriples H).flatMap f ++ (mainTriples H).flatMap f := by
  simp [orderedTriples_eq_append, conicTriples_eq, hH]

end JPoints

end
