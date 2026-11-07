/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import JPoints

/-!
# Comparator solutions

Proofs of the statements of `comparator/Challenge.lean` by the theorems of the library; see
`comparator/README.md`.
-/

@[expose] public section

theorem challenge_mem_bruteForce_iff (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ)
    (p : ℤ × ℤ × ℤ × ℤ) (h7 : cs.length ≤ 7) (h5 : 5 ≤ JPoints.degree cs)
    (hsq : Squarefree (JPoints.poly cs)) :
    p ∈ JPoints.bruteForce cs H all W ↔ JPoints.IsPoint cs H all W p :=
  JPoints.mem_bruteForce_iff h7 h5 hsq

theorem challenge_nodup_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    (JPoints.bruteForce cs H all W).Nodup :=
  JPoints.nodup_bruteForce cs H all W

theorem challenge_bruteForce_eq_filter_flatMap_kummerPoints (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    JPoints.bruteForce cs H all W =
      ((JPoints.orderedTriples H).flatMap (JPoints.kummerPoints (cs.getD · 0))).filter
        (JPoints.IsPoint cs H all W) :=
  JPoints.bruteForce_eq_filter_flatMap_kummerPoints cs H all W

theorem challenge_orderedPoints_eq_map_bruteForce (cs : List ℤ) (H : ℕ) (all : Bool)
    (W : Option ℕ) :
    JPoints.orderedPoints cs H all W =
      (JPoints.bruteForce (JPoints.searchedCoeffs cs).1 H all W).map
        (JPoints.backPoint (JPoints.searchedCoeffs cs).2.1 (JPoints.searchedCoeffs cs).2.2) :=
  JPoints.orderedPoints_eq_map_bruteForce cs H all W

theorem challenge_mem_orderedPoints_iff (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ)
    (p : ℤ × ℤ × ℤ × ℤ) (h7 : cs.length ≤ 7) (h5 : 5 ≤ JPoints.degree cs)
    (hsq : Squarefree (JPoints.poly cs)) :
    p ∈ JPoints.orderedPoints cs H all W ↔ JPoints.IsPoint cs H all W p :=
  JPoints.mem_orderedPoints_iff h7 h5 hsq

theorem challenge_nodup_orderedPoints (cs : List ℤ) (H : ℕ) (all : Bool) (W : Option ℕ) :
    (JPoints.orderedPoints cs H all W).Nodup :=
  JPoints.nodup_orderedPoints cs H all W

theorem challenge_run_eq_of_readInput_eq_ok_of_quiet (args : List String)
    (input : JPoints.Cli.Input) (f : List JPoints.Printf.Piece)
    (hi : (JPoints.Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : JPoints.Printf.parseFormat 'l' input.printFormat = some f)
    (hS : input.sievePrimes3 = 0 ∨ JPoints.SturmTheorem) :
    JPoints.Program.run args =
      (String.join ((JPoints.firstIf input.onePoint (JPoints.orderedPoints input.coeffs.toList
        input.height.toNat input.allPoints input.dboundOption)).map (input.pointText f)), 0) :=
  JPoints.Program.run_eq_of_readInput_eq_ok_of_quiet hi hq hf hS

theorem challenge_eq_firstIf_orderedPoints_of_run_eq (args : List String)
    (input : JPoints.Cli.Input) (hi : (JPoints.Cli.readInput args.toArray).run = .ok input)
    (hq : input.quiet = true) (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ JPoints.SturmTheorem) (L : List (ℤ × ℤ × ℤ × ℤ))
    (hL : (JPoints.Program.run args).1 = String.join (L.map JPoints.defaultPointText)) :
    L = JPoints.firstIf input.onePoint (JPoints.orderedPoints input.coeffs.toList
      input.height.toNat input.allPoints input.dboundOption) :=
  JPoints.Program.eq_firstIf_orderedPoints_of_run_eq hi hq hf hS hL

theorem challenge_mem_iff_isPoint_of_run_eq (args : List String) (input : JPoints.Cli.Input)
    (hi : (JPoints.Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ JPoints.SturmTheorem)
    (h1 : input.onePoint = false) (L : List (ℤ × ℤ × ℤ × ℤ))
    (hL : (JPoints.Program.run args).1 = String.join (L.map JPoints.defaultPointText))
    (p : ℤ × ℤ × ℤ × ℤ) :
    p ∈ L ↔ JPoints.IsPoint input.coeffs.toList input.height.toNat input.allPoints
      input.dboundOption p :=
  JPoints.Program.mem_iff_isPoint_of_run_eq hi hq hf hS h1 hL

theorem challenge_nodup_of_run_eq (args : List String) (input : JPoints.Cli.Input)
    (hi : (JPoints.Cli.readInput args.toArray).run = .ok input) (hq : input.quiet = true)
    (hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n")
    (hS : input.sievePrimes3 = 0 ∨ JPoints.SturmTheorem) (L : List (ℤ × ℤ × ℤ × ℤ))
    (hL : (JPoints.Program.run args).1 = String.join (L.map JPoints.defaultPointText)) :
    L.Nodup :=
  JPoints.Program.nodup_of_run_eq hi hq hf hS hL

end
