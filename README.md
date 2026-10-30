# JPointsLean

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 model of [`j-points`](https://github.com/MichaelStollBayreuth/j-points), the C program
that finds the rational points of bounded height on the Jacobian of a curve of genus 2,
`y² = f(x)` with `f` of degree 5 or 6, by sieving the first three coordinates of their images on
the Kummer surface; with proofs, to come, that the model meets a short specification for every
choice of the sieve, and a record of which Lean definition models which lines of C. It does for
`j-points` what [RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean) does for
`ratpoints`, from which `j-points` descends.

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

The brute-force reference of the model (`JPoints.bruteForce`), which tests every coprime triple
`(a, b, c)` of the box by the exact check of `j-points`, is proved to list exactly these points,
each once, in the order of the specification; comparator certifies the four statements
(`comparator/`). Run as `j-points-brute`, it agrees with the 122 lists of points that Magma's
Kummer package made independently for the curves of the C repository's `test4`, and with `j-points`
itself (`scripts/brutetest.py`).

To come: the faithful model of `j-points`, function by function, and the proof that it meets the
specification for every choice of the sieve.

## State

The specification, the brute-force reference with its proofs and the comparator challenge for
them; and what the repository shares with RatpointsLean, from which those files are taken: the
doubles of the C code by their IEEE 754 bits (`JPoints/Model/Double.lean`) with their values and
rounding (`JPoints/Proof/Double.lean`, `JPoints/Proof/Rounding.lean`), the lemmas on 64-bit words
and on containers that the contracts need, the simplification of the verification conditions, the
statement of Sturm's theorem (`JPoints/Spec/Sturm.lean`), and the checks of the layout and the
style. The record of the correspondence with the C code (`correspondence/`) has the pin, the C
files and the lines excluded from the model, with their reasons; the lines that the model covers
are recorded in the docstrings of its declarations as they are written.

## Layout

- `JPoints/Model`: the executable model, plain code on Lean core and `Std` without Mathlib.
- `JPoints/Spec`: the specification, on Mathlib only, so that it can be read without the model.
- `JPoints/Proof`: the proofs that the model meets the specification.
- `JPoints/Mathlib`: lemmas that belong in Mathlib.
- `BruteMain.lean`: the program `j-points-brute`, the brute-force reference.
- `comparator/`: the comparator challenge, its solution and the description of the statements.
- `correspondence/`: the record of which Lean declaration models which lines of the C code, and
  which lines are excluded from the model and why (`README.md` there).
- `scripts/`: the check of the layout (`check_layout.py`: the imports of each part, no `partial`,
  `unsafe`, `implemented_by` or `extern` in the model, no `native_decide` anywhere), the style lint
  (`style_lint.py`), the test of the brute-force reference (`brutetest.py`), the comparator run
  (`run-comparator.sh`), the check of the correspondence record (`correspondence.py`, which reads
  the docstrings of the model with `Correspondence.lean`), the differential tests of the model's
  program `j-points-model` against `j-points` (`difftest.py`, with the command lines of
  `difftest_cases.py`: the suites of the C repository, random curves, the options, the errors,
  random command lines and failed writes, compared byte for byte), the build of the model with
  other values of its compile-time constants (`constants_check.py`), and the tests of the
  scripts.

## Building and checking

```sh
lake exe cache get                        # Mathlib's build
lake build --wfail JPointsModel           # the model, without Mathlib
lake build --wfail JPoints                # everything
python3 scripts/check_layout.py
python3 scripts/style_lint.py JPoints BruteMain.lean
python3 -m unittest discover -s scripts -p 'test_*.py'
lake build j-points-brute                 # the brute-force reference as a program
python3 scripts/brutetest.py --repo J --jpoints J/j-points    # J: j-points at the pin, built
scripts/run-comparator.sh --paranoid      # comparator, which needs bubblewrap
python3 scripts/correspondence.py check --repo J      # J: a clone of j-points with the pin
python3 scripts/correspondence.py coverage --repo J   # the lines of C not yet recorded
python3 scripts/difftest.py --repo J --c J/j-points   # the model's program against j-points
python3 scripts/difftest.py --repo J --c J/j-points --sets ci   # the reduced set of CI
python3 scripts/constants_check.py --workdir tmp/constants-check   # other values of the constants
```

`difftest.py` and `constants_check.py` describe their options at their top. CI runs all but
comparator, the check of the correspondence record, the differential tests and the constants
check, and checks that `JPoints.lean` imports every module (`lake exe mk_all --check --lib
JPoints`) and that no line of a Lean file is longer than 100 characters.

## Licence

Apache 2.0, see `LICENSE`.
