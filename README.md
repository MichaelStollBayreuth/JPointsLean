# JPointsLean

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/JPointsLean/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/JPointsLean/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/JPointsLean/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/JPointsLean/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 model of [`j-points`](https://github.com/MichaelStollBayreuth/j-points), the C program
that finds the rational points of bounded height on the Jacobian of a curve of genus 2,
`y² = f(x)` with `f` of degree 5 or 6, by sieving the first three coordinates of their images on
the Kummer surface; with proofs that the program of the model prints exactly the points of a short
specification, in the order of the specification, for every choice of the sieve, and a record of
which Lean definition models which lines of C. It does for `j-points` what
[RatpointsLean](https://github.com/MichaelStollBayreuth/RatpointsLean) does for `ratpoints`, from
which `j-points` descends. Several parts are adapted from RatpointsLean, each file saying so in its
header: the doubles of the model with their rounding and their proofs, the reading of the numbers
of the command line, the lemmas on words and containers, the tactic `vc_simp`, Sturm's theorem as a
proposition, and the scripts of the layout check, of the correspondence record and of comparator.

The C code is that of `j-points` 3.0.2, the release that `correspondence/j-points.toml` pins.
Release 3.0.1 fixes the defects that an audit of the C code for what a proof would need found
before the modeling; release 3.0.2 fixes those that the modeling and the proofs met, one of them by
refusing height bounds above `2 ^ 26`, and it drops the code that no input reaches and reads the
command line strictly. The change log of `j-points` (`CHANGE_LOG.md`) lists them all.

The blueprint (the specification, the main theorems with their proofs in outline, the model and its
contracts, the link to the C code) and the API documentation are at
<https://michaelstollbayreuth.github.io/JPointsLean/>.

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
  `read_input` accepts, under `-q` and with a format of `-f` that the model admits, the program
  prints the points of the specification in their order, only the first under `-1`, each in that
  format, and exits with the status `0`; without `-q` it prints them in the same way inside its
  report (`JPoints.Program.exists_run_eq_of_readInput_eq_ok_of_quiet_eq_false`);
- the points read back from the output under the default format
  (`JPoints.Program.eq_firstIf_orderedPoints_of_run_eq`): they are the list of the specification;
  without `-1` exactly the points of the curve given (`JPoints.Program.mem_iff_isPoint_of_run_eq`),
  each once (`JPoints.Program.nodup_of_run_eq`).

The hypotheses of these theorems (`JPoints/Proof/Main.lean`) are those of the command line,
`hi : (Cli.readInput args.toArray).run = .ok input` (`read_input` accepts the arguments `args` and
sets the globals `input`) and `hq : input.quiet = true` (`-q`; the theorem on the report has
`hq : input.quiet = false`); that of the format,
`hf : Printf.parseFormat 'l' input.printFormat = some f` (an admitted format, of the pieces `f`;
for the points read back `hf : input.printFormat = "(%ld, %ld, %ld, %ld)\n"`, the default format,
and for their membership also `h1 : input.onePoint = false`, no `-1`); and
`hS : input.sievePrimes3 = 0 ∨ SturmTheorem`.

Sturm's theorem, which Mathlib does not have, is a `Prop`-valued definition
(`JPoints.SturmTheorem`, `JPoints/Spec/Sturm.lean`), a hypothesis and not an axiom. The tube and
the real region rest on the intervals of the real roots of `f` that `j-points` isolates by Sturm
sequences, so the theorems assume it unless the sieve has no primes at all, which `-N 0` gives. The
theorems cover every height bound that `j-points` accepts: it refuses those above
`MAX_SEARCH_HEIGHT`, `2 ^ 26`, up to which the products that `row_region` computes in doubles stay
below `2 ^ 53`, so that the ends of its excluded intervals keep within their margins.

The brute-force reference of the model (`JPoints.bruteForce`), which tests every coprime triple
`(a, b, c)` of the box by the exact check of `j-points`, is proved to list exactly the points of
the specification, each once, in its order. Run as `j-points-brute`, it agrees with the 122
reference lists of `testbase4` in the C repository (the 61 curves of `testcurves2` at height 30,
with and without `-a`), which Magma made with its Kummer package by a brute force of its own,
independently of `j-points` (`mkref4.m`), and with `j-points` itself (`scripts/brutetest.py`).

Comparator certifies ten statements: the four theorems on the program under `-q`, the points of
the specification and their distinctness, and four on the brute-force reference; on
2026-11-08 `lake comparator --paranoid` accepted them, with Lean's kernel and the five external
checkers (`comparator/README.md`). The theorem on the run without `-q` is proved but not
certified. Every theorem of the project depends on the axioms `propext`, `Classical.choice` and
`Quot.sound` only, and none has a `sorry`.

## What one has to trust

- The specification (`JPoints/Spec`), which the comparator challenge restates verbatim, with the
  definitions of Lean core and Mathlib that it is written in; the four definitions on top of it that
  the statements use (`JPoints.firstIf`, `JPoints.pointText`, `JPoints.defaultPointText`,
  `JPoints.Cli.Input.dboundOption`); and the definitions of the model that the statements name: the
  program (`JPoints.Program.run`), `read_input` and its globals (`JPoints.Cli.readInput`,
  `JPoints.Cli.Input`), the formats of `-f` (`JPoints.Printf.parseFormat`) with the rules of
  `printf` by which they print (`JPoints.Printf.render`, `JPoints.Printf.printLong`), and the
  brute-force reference (`JPoints.bruteForce`).
- Lean's kernel and Comparator.
- That `j-points-model` writes the text of `JPoints.Program.run` and returns its exit status, and
  that Lean's compiler and runtime run the definitions as they are: the model has no `partial`,
  `unsafe`, `implemented_by` or `extern` (`scripts/check_layout.py`), so the compiled code is that
  of the definitions that the proofs see.
- Sturm's theorem (`JPoints.SturmTheorem`), in the runs that assume it.

## What is not verified

- The C code itself. Lean has no semantics of C, and no proof relates the model to the C code. The
  model is a faithful translation, and the record of the correspondence (`correspondence/`) covers
  every line of code of the C files: the lines that the model covers in the docstrings of its
  declarations, the others excluded from the model, each with its reason. The program of the
  model, `j-points-model`, prints what `j-points` prints, byte for byte, on every set of the
  differential tests (`scripts/difftest.py`).
- The threads of `j-points`, the management of its memory and its instrumentation: the model
  follows the sequential path of the C code, and the differential tests compare runs with threads
  too.
- The builds other than the default one: the vector builds (`make VECTOR=sse2` and
  `make VECTOR=avx2`) and a build with the constants of the cost model that `make tune` measures
  (`tuning.mk`). The model is the default build on x86-64 with LP64, glibc and GMP.
- The platform: the model rounds each operation on doubles as IEEE 754 prescribes, as the code that
  gcc makes of the default build does on x86-64, prints as glibc's `printf` and GMP's `gmp_printf`
  print, and sorts the rates of the primes as glibc's `qsort` does. That the platform does the same
  is checked by the differential tests, not proved; of the sort, the proofs use only that it
  permutes the entries (`JPoints.toList_qsort_perm`).
- The values of glibc's `log` and `pow` in the cost model, which chooses the sieve. The proofs hold
  for every value of these floats, and the points printed do not depend on them. The report
  without `-q` names the primes and the mode chosen, which do depend on them (and on the CPU), so
  the differential tests run both programs on one machine.
- The formats of `-f` that the model does not admit. `j-points` passes any format to `printf`; the
  model admits the formats whose conversions are `%[flags][width][.precision]ld`, with the flags
  `-`, `+`, `#`, `'`, `0` and the space and a width and a precision of at most 4095
  (`JPoints.Printf.maxField`), at most four of them, and `%%` (`JPoints.Printf.parseFormat`). It
  refuses every other format before it prints anything else, with a message of its own and the
  exit status 11 (`JPoints.Program.formatRefusal`), and the theorems on the program assume an
  admitted format.
- The numbers of the survivors of the stages in the report without `-q`: the theorem on that report
  says only that some totals of the counters are printed.

## The programs

`j-points-model 'a_0 a_1 ... a_d' h [options]` is the program of the model, with the command line,
the options, the messages and the exit statuses of `j-points`, which the
[README of `j-points`](https://github.com/MichaelStollBayreuth/j-points#usage) describes. It accepts
`-t`, but runs the units of work in turn on one thread, and it refuses the formats of `-f` that it
does not admit. For instance, the points of height at most 30 on
`y² = x⁶ + 12x⁵ + 55x⁴ + 128x³ + 171x² + 116x + 21`, the curve of the suite `test1` of `j-points`:

```console
$ lake build j-points-model
$ .lake/build/bin/j-points-model '21 116 171 128 55 12 1' 30 -q
(0, 0, 1, -19)
(0, 1, -2, 26)
(1, -6, -1, -24)
(1, -4, -3, 28)
```

`j-points-brute 'a_0 a_1 ... a_d' H [-a] [-w W]` prints the points of the brute-force reference
`JPoints.bruteForce`, one per line in the default format of `j-points`. It does not check the
curve: the theorem on its points is about the curves that `j-points` accepts. For instance, the
points of height at most 10 on `y² = x⁵ + 1`:

```console
$ lake build j-points-brute
$ .lake/build/bin/j-points-brute '1 0 0 0 0 1' 10
(1, 0, 0, 0)
(0, 1, -1, 1)
(0, 1, 0, 0)
(1, -1, 0, 2)
(1, 2, 2, 0)
```

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
- `blueprint/`: the blueprint: the specification, the main theorems with their proofs in outline,
  the model and its contracts, the parts of the sieve, the link to the C code and, generated from
  the record, the table of the correspondence (`leanblueprint pdf`, `leanblueprint web`; then
  `lake env lean blueprint/checkdecls.lean` checks its Lean names).
- `formalization.yaml`: the metadata of the formalization in the schema of
  [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) (v0.4).
- `scripts/`: the checks, each script with its tests (`test_*.py`):
  - `check_layout.py`: the imports of each part, no `partial`, `unsafe`, `implemented_by` or
    `extern` in the model, no `native_decide` anywhere;
  - `style_lint.py`: the style lint;
  - `correspondence.py`: the check of the correspondence record, which reads the docstrings of the
    model with `Correspondence.lean`;
  - `difftest.py`: the differential tests of `j-points-model` against `j-points`, with the command
    lines of `difftest_cases.py`: the suites of the C repository, random curves, the options, the
    errors, random command lines and failed writes, compared byte for byte; on the formats of `-f`
    that the model refuses only the model runs, and its refusal is checked;
  - `brutetest.py`: the test of the brute-force reference;
  - `constants_check.py`: the build of the model and the proofs with other values of the
    compile-time constants, each variant meeting the facts about them that the proofs use;
  - `run-comparator.sh`: the comparator run.

## Building and checking

The project builds with the Lean toolchain that `lean-toolchain` names (Lean v4.35.0), which
[elan](https://github.com/leanprover/elan) installs, and with Mathlib at the revision of
`lake-manifest.json`, whose build `lake exe cache get` fetches. The scripts need Python 3.11 or
later, and comparator needs bubblewrap (`bwrap`). The checks against the C code need a clone of
`j-points` at the pin (`J`, a path of one's choice) in its default build (no `make tune`, no
`VECTOR`), which needs GMP and make. From the root of this repository:

```sh
git clone https://github.com/MichaelStollBayreuth/j-points J
git -C J checkout "$(python3 scripts/correspondence.py pin --field commit)"
make -C J j-points
```

Then:

```sh
lake exe cache get                        # Mathlib's build
lake build --wfail JPointsModel           # the model, without Mathlib
lake build --wfail JPoints                # the specification and the proofs
lake build j-points-model j-points-brute  # the two programs
python3 scripts/check_layout.py
python3 scripts/style_lint.py JPoints BruteMain.lean ModelMain.lean
python3 -m unittest discover -s scripts -p 'test_*.py'
scripts/run-comparator.sh --paranoid      # comparator
python3 scripts/correspondence.py check --complete --repo J   # the record of the C code
python3 scripts/correspondence.py coverage --repo J           # the lines of C not recorded
python3 scripts/brutetest.py --repo J --jpoints J/j-points    # the brute-force reference
python3 scripts/difftest.py --repo J --c J/j-points           # the model's program against C
python3 scripts/difftest.py --repo J --c J/j-points --sets ci # the reduced set of CI
python3 scripts/constants_check.py --workdir tmp/constants-check --targets JPointsModel,JPoints
```

The environment variables `JPOINTS_REPO` and `JPOINTS_BIN` can stand for `--repo J` and
`--c J/j-points`. `difftest.py` and `constants_check.py` describe their options at their top; the
constants check builds copies of the project in its workdir, here in the untracked `tmp/`. CI
(`.github/workflows/build-project.yml`) runs all but comparator, the differential tests beyond
their set `ci` and the constants check, and checks that `JPoints.lean` imports every module
(`lake exe mk_all --check --lib JPoints`) and that no line of a Lean file is longer than 100
characters.

## License

Apache 2.0 (`LICENSE`). The C code of `j-points` is under the GNU General Public License, version
2 or later; its copyright notices name Michael Stoll alone.
