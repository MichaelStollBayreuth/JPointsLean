# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator), "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` (Lean v4.35.0 and later), certify the main
theorems of the project independently of the repository's own build, using only the permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`).

## What is checked

- [`Challenge.lean`](Challenge.lean) may import only Mathlib and the model (`JPoints.Model`);
  `scripts/check_layout.py` checks this. It restates the specification verbatim: all of
  `JPoints/Spec/Basic.lean`, in its order and without its examples, the points (`degree`, `poly`,
  the Kummer equation `kummerK2`, `kummerK1`, `kummerK0`, `kummer`, the polynomials of the lifting
  test `auxA2`, `auxB2`, `sexticForm`, and `Lifts`, `IsNormalized`, `InBounds`, `IsPoint` with their
  decidability) and their order (`intRange`, `boxTriples`, `orderedTriples`, `kummerRoots`,
  `kummerPoints`, `searchedCoeffs`, `backPoint`, `orderedPoints`). It states the main theorems with
  `sorry`.
- [`Solution.lean`](Solution.lean) imports the library and proves the same statements by its
  theorems.

The statements speak about the brute-force reference `JPoints.bruteForce` of the model, which the
challenge imports. The model is trusted in the sense that it is the code the executables run, and
nothing else, and a definition of it, which elaborates without Mathlib, is never restated. The
specification, by contrast, is reproduced in the challenge, so a solution whose library changed it
is rejected. Of Mathlib, the challenge imports exactly the Mathlib modules among the public imports
of the file of the specification that it restates (`Mathlib.Algebra.GCDMonoid.Nat`,
`Mathlib.Algebra.Polynomial.Basic` and `Mathlib.Algebra.Squarefree.Basic`, the last for
`Squarefree`), so that the restated definitions elaborate to the same terms as there. The
specification is one file, restated in its order: Lean shares the auxiliary definitions of the
pattern matches of equal shape within a module (the match on a quadruple of `backPoint` is that of
`IsPoint` when both are in one module), so that a restatement of two files in one module would
elaborate to other constants, which comparator rejects.

## The four statements

`challenges.json` lists four statements. They hold for every coefficient list `cs`, height bound
`H`, option `-a` (`all`) and bound `W` of `-w`:

- membership (`challenge_mem_bruteForce_iff`): for every curve that the program does not refuse
  (at most seven coefficients, degree at least 5, `poly cs` squarefree), `bruteForce cs H all W`
  holds exactly the points (`IsPoint`);
- no duplicates (`challenge_nodup_bruteForce`), for every curve;
- the order of the search (`challenge_bruteForce_eq_filter_flatMap_kummerPoints`): for every curve,
  the brute-force reference is the list of the candidates of `kummerPoints` over the triples of
  `orderedTriples H` in turn that are points;
- the order of the program (`challenge_orderedPoints_eq_map_bruteForce`): `orderedPoints` is the
  brute-force reference of the curve searched (`searchedCoeffs`), its points taken back to the curve
  given (`backPoint`).

On 2026-10-30 `lake comparator --paranoid` accepted the four statements, with Lean's kernel and the
five external checkers.

Comparator certifies these statements and their proofs; it does not certify that the executable
`j-points-brute` runs the brute-force reference.

## How Comparator checks them

`lake comparator` builds and exports both modules inside a `bubblewrap` sandbox (it never loads
the project's `.olean` files into its own process) and checks that each challenge theorem in the
solution

1. proves the **same statement** as in the challenge, comparing the full bodies (not just the
   types) of every definition the statement refers to, so the specification of the library must
   be the challenge's restatement exactly;
2. uses no axioms beyond `permitted_axioms`; in particular a `native_decide` or `bv_decide`
   anywhere below a main theorem makes it fail, and `scripts/check_layout.py` forbids both in the
   project;
3. is accepted by the Lean kernel and, with `--paranoid`, by every external checker bundled with
   Lean (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

## Running

Run from the repository root; the only prerequisite besides Lean is `bubblewrap` (`bwrap`) with
unprivileged user namespaces (or installed setuid root):

```bash
scripts/run-comparator.sh --paranoid    # the certification: Lean's kernel and the external checkers
scripts/run-comparator.sh               # Lean's kernel only
```

The script builds the library (`lake build JPointsModel JPoints`) and runs `lake comparator
--config comparator/challenges.json` with the options given. Exit code `0` (and `Your solution is
okay!`) means that the check passed, `1` that it was rejected, `2` that it could not start (no
`bwrap`, no `lake-manifest.json`, a missing or malformed configuration). The library is built
first, outside the sandbox, where the caller's environment applies (the sandbox clears it but for
`PATH`), so that the sandboxed builds of `Challenge` and `Solution` find it current and only replay
it. `lake comparator` writes the exports into the temporary directory of the system (`TMPDIR`).
