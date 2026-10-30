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

## What will be verified

The specification: the program returns a list of coordinate vectors `(a, b, c, d)` in `P³(ℚ)` that
contains exactly the points on the Kummer surface of the curve at which both auxiliary polynomials
of the lifting test take square values (the test by which `j-points` decides that a point of the
Kummer surface lifts to a rational point of the Jacobian), within the bounds of the command line on
the coordinates, and normalized as `j-points` prints them.

## State

The repository is being set up. So far it holds what it shares with RatpointsLean: the doubles of
the C code by their IEEE 754 bits (`JPoints/Model/Double.lean`) with their values and rounding
(`JPoints/Proof/Double.lean`, `JPoints/Proof/Rounding.lean`), the lemmas on 64-bit words and on
containers that the contracts need, the simplification of the verification conditions, and the
statement of Sturm's theorem (`JPoints/Spec/Sturm.lean`); and the checks of the layout and the
style.

## Layout

- `JPoints/Model`: the executable model, plain code on Lean core and `Std` without Mathlib.
- `JPoints/Spec`: the specification, on Mathlib only, so that it can be read without the model.
- `JPoints/Proof`: the proofs that the model meets the specification.
- `JPoints/Mathlib`: lemmas that belong in Mathlib.
- `scripts/`: the check of the layout (`check_layout.py`: the imports of each part, no `partial`,
  `unsafe`, `implemented_by` or `extern` in the model, no `native_decide` anywhere), the style lint
  (`style_lint.py`) and their tests.

## Building and checking

```sh
lake exe cache get                        # Mathlib's build
lake build --wfail JPointsModel           # the model, without Mathlib
lake build --wfail JPoints                # everything
python3 scripts/check_layout.py
python3 scripts/style_lint.py JPoints
python3 -m unittest discover -s scripts -p 'test_*.py'
```

CI runs these, and checks that `JPoints.lean` imports every module (`lake exe mk_all --check --lib
JPoints`) and that no line of a Lean file is longer than 100 characters.

## Licence

Apache 2.0, see `LICENSE`.
