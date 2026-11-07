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
  `kummerPoints`, `searchedCoeffs`, `backPoint`, `orderedPoints`). After it, it restates verbatim
  the definitions that the theorems on the program use: Sturm's theorem as a proposition
  (`SturmTheorem`, from `JPoints/Spec/Sturm.lean`), the first point only under `-1` (`firstIf`) and
  the text of a point under an admitted format of `-f` (`pointText`), both from
  `JPoints/Proof/Reference.lean`, and from `JPoints/Proof/Main.lean` the text of a point under the
  default format (`defaultPointText`) and the bound on the fourth coordinate and the text of a point
  for the globals of the command line (`Cli.Input.dboundOption`, `Cli.Input.pointText`). It states
  the main theorems with `sorry`.
- [`Solution.lean`](Solution.lean) imports the library and proves the same statements by its
  theorems.

The statements speak about the brute-force reference `JPoints.bruteForce` and the program
`JPoints.Program.run` of the model, which the challenge imports, together with the command line
that the program reads (`JPoints.Cli.readInput`, `JPoints.Cli.Input`) and the formats of `-f`
(`JPoints.Printf.parseFormat`, with `JPoints.Printf.Piece.gmpSpec`, their pieces in the format that
`printf_mpz` builds for `gmp_printf`). The model is trusted in the sense that it is the code the
executables run, and nothing else, and a definition of it, which elaborates without Mathlib, is
never restated. The specification and the definitions on top of it, by contrast, are reproduced in
the challenge, so a solution whose library changed them is rejected. Of Mathlib, the challenge
imports exactly the Mathlib modules among the public imports of the files whose definitions it
restates, so that the restated definitions elaborate to the same terms as there:
`Mathlib.Algebra.GCDMonoid.Nat`, `Mathlib.Algebra.Polynomial.Basic` and
`Mathlib.Algebra.Squarefree.Basic` (the last for `Squarefree`) of `JPoints/Spec/Basic.lean`;
`Mathlib.Algebra.Polynomial.Sturm.Sequence`, `Mathlib.Basic.Real.Basic` and
`Mathlib.Data.List.SignVariations` of `JPoints/Spec/Sturm.lean`; `Mathlib.Order.Prod.Lex.Basic`
of `JPoints/Proof/Reference.lean` (`JPoints/Proof/Main.lean` imports no Mathlib module publicly).
The specification is one file, restated in its order: Lean shares the auxiliary definitions of
the pattern matches of equal shape within a module (the match on a quadruple of `IsPoint` serves
every later match on a quadruple of the module), so that a restatement of two files with such
matches in one module would elaborate to other constants, which comparator rejects. For this
reason the definitions restated from the other files have no pattern match: `pointText` and
`defaultPointText` take the coordinates of a point by projections.

## The ten statements

`challenges.json` lists ten statements. The first six hold for every coefficient list `cs`, height
bound `H`, option `-a` (`all`) and bound `W` of `-w`:

- membership (`challenge_mem_bruteForce_iff`): for every curve that the program does not refuse
  (at most seven coefficients, degree at least 5, `poly cs` squarefree), `bruteForce cs H all W`
  holds exactly the points (`IsPoint`);
- no duplicates (`challenge_nodup_bruteForce`), for every curve;
- the order of the search (`challenge_bruteForce_eq_filter_flatMap_kummerPoints`): for every curve,
  the brute-force reference is the list of the candidates of `kummerPoints` over the triples of
  `orderedTriples H` in turn that are points;
- the order of the program (`challenge_orderedPoints_eq_map_bruteForce`): `orderedPoints` is the
  brute-force reference of the curve searched (`searchedCoeffs`), its points taken back to the curve
  given (`backPoint`);
- the points of the specification (`challenge_mem_orderedPoints_iff`): for every curve that the
  program does not refuse, `orderedPoints cs H all W` holds exactly the points of the curve given
  (`IsPoint`);
- their distinctness (`challenge_nodup_orderedPoints`): `orderedPoints cs H all W` has no
  duplicates, for every curve.

The other four are about the program of the model, `JPoints.Program.run`, on a command line `args`
that `read_input` accepts (`(JPoints.Cli.readInput args.toArray).run = .ok input`), under `-q`
(`input.quiet = true`), assuming Sturm's theorem unless the sieve has no primes at all, which `-N`
with a value of at most `0` gives (`input.sievePrimes3 = 0 ∨ SturmTheorem`). No hypothesis bounds
the height: `read_input` refuses height bounds above `MAX_SEARCH_HEIGHT`, `2 ^ 26`
(`maxSearchHeight`), which keeps the products of `row_region` below `2 ^ 53`, where the rounding of
the ends of its excluded intervals stays within their margins. The points of the specification are
those of `orderedPoints` for the coefficients, the height bound, `-a` and `-w` of the command line
(`Cli.Input.dboundOption`).

- the output (`challenge_run_eq_of_readInput_eq_ok_of_quiet`): with an admitted format of `-f` (of
  the pieces `f`), the program prints the points of the specification in their order, only the
  first under `-1` (`firstIf`), each by `Cli.Input.pointText`, and exits with the status `0`;
- the points read back (`challenge_eq_firstIf_orderedPoints_of_run_eq`): under the default format
  of the points, `(%ld, %ld, %ld, %ld)\n`, a list `L` of points whose texts (`defaultPointText`)
  make up what the program prints is the list of the points of the specification, only the first
  under `-1`;
- membership (`challenge_mem_iff_isPoint_of_run_eq`): under the default format and without `-1`,
  such a list `L` holds exactly the points of the curve given (`IsPoint`);
- no duplicates (`challenge_nodup_of_run_eq`): under the default format, such a list `L` has no
  duplicates.

On 2026-11-07 `lake comparator --paranoid` accepted the ten statements, with Lean's kernel and the
five external checkers.

Comparator certifies these statements and their proofs; it does not certify that the executables
`j-points-brute` and `j-points-model` run the brute-force reference and the program of the model
(`JPoints.Program.main`, which `j-points-model` runs, writes the text of `JPoints.Program.run` and
returns its status).

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
