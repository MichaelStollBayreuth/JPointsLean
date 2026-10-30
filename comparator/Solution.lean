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

end
