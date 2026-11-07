# JPointsLean

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 model of [`j-points`](https://github.com/MichaelStollBayreuth/j-points), the C program
that finds the rational points of bounded height on the Jacobian of a curve of genus 2,
`y² = f(x)` with `f` of degree 5 or 6, by sieving the first three coordinates of their images on
the Kummer surface; with proofs that the program of the model prints exactly the points of a short
specification, in the order of the specification, for every choice of the sieve, and a record of
which Lean definition models which lines of C. It does for `j-points` what
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean) does for `ratpoints`, from
which `j-points` descends.

The C code is that of `j-points` 3.0.1.

## What is verified

The specification (`JPoints/Spec`, on Mathlib only): for the coefficient list of `f`, the height
bound `H`, the option `-a` and the bound of `-w`, the points `(a, b, c, d)` on the Kummer surface of
the Jacobian of `y² = f(x)`, in the coordinates of Cassels and Flynn, that come from rational points
of the Jacobian (for `a ≠ 0` both auxiliary polynomials `A₂` and `B₂` of the lifting test of
`j-points` take square values; for `a = 0` the leading coefficient of `f` and, for `b ≠ 0`, the
value `b⁶ f(c / b)` are squares), with coprime coordinates whose first nonzero one among `a, b, c`
is positive, within the bounds of the command line (`JPoints.IsPoint`); and the list of these
points in the order in which `j-points` finds them (`JPoints.orderedPoints`).

The model (`JPoints/Model`, on Lean core and `Std` only) translates `j-points` function by
function: the reading of the command line, the choice of the sieving primes by the cost model, the
tables of the curve at each prime, the three stages of the sieve on 64-bit words, the sieve at 2,
the box, the tube around the real points and the real region of each row with their doubles as
IEEE 754 bits, the exact check by the lifting test, and the printing. The proofs
(`JPoints/Proof`) give each component a contract and prove, for every curve the program accepts,
every value of the floats of the cost model and every choice of the sieve that follows from them:

- the output (`JPoints.Program.run_eq_of_readInput_eq_ok_of_quiet`): on a command line that
  `read_input` accepts, under `-q`, the program prints the points of the specification in their
  order, only the first under `-1`, each in the format of `-f`, and exits with the status `0`;
  without `-q` it prints them in the same way inside its report
  (`JPoints.Program.exists_run_eq_of_readInput_eq_ok_of_quiet_eq_false`);
- the points read back from the output under the default format
  (`JPoints.Program.eq_firstIf_orderedPoints_of_run_eq`): they are the list of the specification;
  without `-1` exactly the points of the curve given (`JPoints.Program.mem_iff_isPoint_of_run_eq`),
  each once (`JPoints.Program.nodup_of_run_eq`).

These theorems have one hypothesis. Sturm's theorem, which Mathlib does not have, is a `Prop`-valued
definition (`JPoints.SturmTheorem`, `JPoints/Spec/Sturm.lean`) assumed by the runs whose sieve uses
the real region, that is all but those whose sieve has no primes at all, which `-N 0` gives. No
hypothesis bounds the height: `j-points` refuses height bounds above `MAX_SEARCH_HEIGHT`, `2 ^ 26`,
and up to it the products that `row_region` computes in doubles stay below `2 ^ 53`, so that the
ends of its excluded intervals keep within their margins; at larger height bounds the real region
could drop words that hold points.

The brute-force reference of the model (`JPoints.bruteForce`), which tests every coprime triple
`(a, b, c)` of the box by the exact check of `j-points`, is proved to list exactly the points of
the specification, each once, in its order. Run as `j-points-brute`, it agrees with the 122 lists
of points that Magma's Kummer package made independently for the curves of the C repository's
`test4`, and with `j-points` itself (`scripts/brutetest.py`).

Comparator certifies ten statements: the four theorems on the program under `-q`, the points of
the specification and their distinctness, and four on the brute-force reference; on
2026-11-08 `lake comparator --paranoid` accepted them, with Lean's kernel and the five external
checkers (`comparator/README.md`). Every theorem of the project depends on the axioms `propext`,
`Classical.choice` and `Quot.sound` only, and none has a `sorry`.

## What is not verified

- The C code itself. The model is a faithful translation, and the record of the correspondence
  (`correspondence/`) covers every line of code of the C files: the lines that the model covers in
  the docstrings of its declarations, the others excluded from the model, each with its reason. The
  program of the model, `j-points-model`, prints what `j-points` prints, byte for byte, on every
  set of the differential tests (`scripts/difftest.py`).
- The threads of `j-points`, the management of its memory, its instrumentation, and the builds other
  than the default one for x86-64 (the vector walk of the AVX2 build among them): the model follows
  the sequential path of the default build.
- The values of glibc's `log` and `pow` in the cost model, which chooses the sieve: the proofs hold
  for every value of these floats, and what the program prints does not depend on the choice.
- The numbers of the survivors of the stages in the report without `-q`: the theorem on that report
  says only that some totals of the counters are printed.

## Layout

- `JPoints/Model`: the executable model, plain code on Lean core and `Std` without Mathlib.
- `JPoints/Spec`: the specification, on Mathlib only, so that it can be read without the model.
- `JPoints/Proof`: the proofs that the model meets the specification: a contract (a `@[spec]`
  triple) for each component of the model, proved by `vcgen`, and the main theorems in
  `JPoints/Proof/Main.lean`.
- `JPoints/Mathlib`: lemmas that belong in Mathlib.
- `BruteMain.lean`: the program `j-points-brute`, the brute-force reference.
- `ModelMain.lean`: the program `j-points-model`, the faithful model of `j-points`.
- `comparator/`: the comparator challenge, its solution and the description of the statements.
- `correspondence/`: the record of which Lean declaration models which lines of the C code, and
  which lines are excluded from the model and why (`README.md` there).
- `formalization.yaml`: the description of the formalization in the schema of the self-reports.
- `scripts/`: the check of the layout (`check_layout.py`: the imports of each part, no `partial`,
  `unsafe`, `implemented_by` or `extern` in the model, no `native_decide` anywhere), the style lint
  (`style_lint.py`), the test of the brute-force reference (`brutetest.py`), the comparator run
  (`run-comparator.sh`), the check of the correspondence record (`correspondence.py`, which reads
  the docstrings of the model with `Correspondence.lean`), the differential tests of the model's
  program `j-points-model` against `j-points` (`difftest.py`, with the command lines of
  `difftest_cases.py`: the suites of the C repository, random curves, the options, the errors,
  random command lines and failed writes, compared byte for byte, and the formats of `-f` that the
  model refuses, which it alone runs), the build of the model and the proofs with other values of
  the compile-time constants, each variant meeting the facts about them that the proofs use
  (`constants_check.py`), and the tests of the scripts.

## Building and checking

```sh
lake exe cache get                        # Mathlib's build
lake build --wfail JPointsModel           # the model, without Mathlib
lake build --wfail JPoints                # everything
python3 scripts/check_layout.py
python3 scripts/style_lint.py JPoints BruteMain.lean ModelMain.lean
python3 -m unittest discover -s scripts -p 'test_*.py'
lake build j-points-brute                 # the brute-force reference as a program
lake build j-points-model                 # the model's program
python3 scripts/brutetest.py --repo J --jpoints J/j-points    # J: j-points at the pin, built
scripts/run-comparator.sh --paranoid      # comparator, which needs bubblewrap
python3 scripts/correspondence.py check --repo J      # J: a clone of j-points with the pin
python3 scripts/correspondence.py coverage --repo J   # the lines of C not recorded
python3 scripts/difftest.py --repo J --c J/j-points   # the model's program against j-points
python3 scripts/difftest.py --repo J --c J/j-points --sets ci   # the reduced set of CI
python3 scripts/constants_check.py --workdir tmp/constants-check --targets JPointsModel,JPoints
```

`difftest.py` and `constants_check.py` describe their options at their top. CI runs all but
comparator, the differential tests beyond their set `ci` and the constants check, and checks
that `JPoints.lean` imports every module (`lake exe mk_all --check --lib
JPoints`) and that no line of a Lean file is longer than 100 characters.

## Licence

Apache 2.0, see `LICENSE`.
