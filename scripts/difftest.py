#!/usr/bin/env python3
"""Differential tests of the model's program j-points-model against j-points at the pin.

usage: scripts/difftest.py [--model CMD] [--c PATH] [--repo PATH] [--rev REV] [--sets LIST]
                           [--timeout S] [--memory BYTES] [--output-cap BYTES] [--seed S]
                           [--random N] [--fuzz N] [--ci-height H] [--max-height H]
                           [--any-build] [--list] [--max-failures N] [-v]

Runs the model's program and the C program on the same command lines and compares their standard
outputs, their standard errors and their exit statuses byte for byte; the model's standard error
must be empty. On a format of -f that it does not admit, the model prints a refusal of its own and
exits with the status 11, where the C program passes the format to printf: on those command lines
(the set formats) the model runs alone, and its run is compared with the refusal. The model runs
with LEAN_ABORT_ON_PANIC=1, so that a panic of the Lean runtime (an index out of bounds, after
which the program would go on with a default value) ends it by SIGABRT, which the comparison of
the exit status catches. Every run has a timeout, a cap on its address space and a cap on the size
of its outputs (they go to temporary files, so that the harness never holds more). The sets of
command lines:

  test1 test2 test3 test4 testbrute testrich testthreads
          the suites of the C repository's Makefile (its TESTS), read from the clone (--repo) at
          the pin (--rev): the command lines of the Makefile's recipes, those of test2.sh,
          test4.sh and testbrute.sh over the curves of testcurves2 or testcurves-rich, with the
          variables (JPOPTS, CURVES, H) that the recipes set, and the invocations of test3.sh,
          each compared on its whole output, before the filter that test3.sh applies and
          unsorted (the scripts sort the points, the comparison takes them in their order);
  ci      the suites of the Makefile with every height bound above --ci-height cut to it (and
          above 30 for the runs without sieving, -N 0, which check every triple), the
          sets options (cut the same way), errors, formats and writes, the searches of
          difftest_cases.CI_EXTRA (the condition at 2, which needs the height 500), and 20 random
          searches and 10 rounds of fuzz: the set for CI;
  random  --random random searches on random curves of degree 5 and 6 at small heights
          (difftest_cases.random_run, seeded by --seed);
  options the modes and stages of the sieve, the pins, -s, -c, -a, -w, -1, -q, -f and -t
          (difftest_cases.OPTION_CASES); the formats of -f, here and in fuzz, are those of
          difftest_cases.FORMATS, whose conversions are %[flags][width][.precision]ld and %%,
          the formats that the model prints as the C program does;
  errors  the errors 2 to 6, 9 and 10, the order of the checks, also before the refusal of a
          format of -f, -c list (difftest_cases.ERROR_CASES);
  formats the formats of -f that the model refuses (difftest_cases.REFUSAL_CASES, with the
          formats difftest_cases.REFUSED_FORMATS), the model alone: its standard output must be
          difftest_cases.REFUSAL, its exit status difftest_cases.REFUSAL_STATUS and its standard
          error empty;
  fuzz    --fuzz rounds of eight random command lines (difftest_cases.random_command_lines);
  writes  the searches of difftest_cases.WRITE_CASES with a standard output that fails: a pipe
          whose reader is gone, which ends the C program by SIGPIPE at its first write, where the
          model, whose runtime ignores SIGPIPE, is to exit quietly with the status 141 that a shell
          reports for SIGPIPE (or be ended by SIGPIPE too); and /dev/full, whose failed writes both
          programs ignore, with the same exit status;
  long    searches for which the C program takes more than a few seconds
          (difftest_cases.LONG_CASES), each with a timeout of at least six hours (the model
          takes up to about two and a half): run on demand, not by default.

The default sets are test1, test2, test3, test4, testbrute, testrich, testthreads, random,
options, errors, formats, fuzz and writes; `--sets all` adds long. A command line whose height bound
(its second word, a decimal) is above --max-height is skipped and counted.

The model modelled is the default build of the C program (no tuning.mk, the scalar sieve): the
harness refuses a C program whose `-c list` does not print the defaults of the cost model of
JPoints/Model/Constants.lean (--any-build lifts that). The report of a search names the primes that
the cost model chooses with glibc's log and pow, which depend on the CPU: compare on one machine.

Options:
  --model CMD      the model's program, a command line split as a shell splits it; for
                   `lake exe NAME ...` the harness first runs `lake build NAME`, since lake prints
                   its build lines on the standard error when it builds before it runs; default:
                   .lake/build/bin/j-points-model
  --c PATH         the C program j-points built at the pin (default: the environment variable
                   JPOINTS_BIN, else j-points on the PATH)
  --repo PATH      a clone of j-points that contains the pin (default: JPOINTS_REPO), for the
                   suites of the Makefile
  --rev REV        the revision of the test files (default: the commit of the pin in
                   correspondence/j-points.toml)
  --sets LIST      comma-separated sets; `all` stands for the default sets and long
  --timeout S      the timeout of a run, in seconds (default 3600: the model takes up to about
                   1000 s on a run of the default sets)
  --memory BYTES   the cap on the address space of a run (default 12e9: the Lean runtime reserves
                   address space for its threads far beyond what it uses)
  --output-cap B   the cap on the size of each output of a run (default 64 MiB)
  --seed S         the seed of random and fuzz (default 1)
  --random N       the number of random searches (default 200)
  --fuzz N         the number of rounds of fuzz (default 50)
  --ci-height H    the largest height bound of the set ci (default 100)
  --max-height H   skip the command lines whose height bound is above H
  --any-build      run against a C program that is not the default build
  --list           print the command lines of the sets, do not run them
  --max-failures N the failures printed per set (default 20)
  -v               print every comparison

Prints one line per set (the comparisons, the failures, the time of each program, wall clock and
CPU) and the failures, and exits 0 if every comparison is equal, 1 if one is not, 2 for an error
in the arguments or the setup.
"""
import argparse
import os
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from random import Random

sys.path.insert(0, str(Path(__file__).resolve().parent))
import difftest_cases  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'correspondence' / 'j-points.toml'
CONSTANTS = ROOT / 'JPoints' / 'Model' / 'Constants.lean'
MAX_HEIGHT = 3037000499
TIMEOUT = 3600
MEMORY = 12 * 10 ** 9
OUTPUT_CAP = 64 * 2 ** 20
CI_RANDOM = 20
CI_FUZZ = 10
# The largest height bound of the runs of ci without sieving (-N 0), which test every triple.
CI_UNSIEVED = 30
# The timeout of the runs of the set long, at least.
LONG_TIMEOUT = 21600
# The environment of the model: a panic of the Lean runtime ends it by SIGABRT.
MODEL_ENV = {'LEAN_ABORT_ON_PANIC': '1'}
# The suites of the Makefile, the sets of difftest_cases, and the default sets.
MAKE_SETS = ['test1', 'test2', 'test3', 'test4', 'testbrute', 'testrich', 'testthreads']
OTHER_SETS = ['ci', 'random', 'options', 'errors', 'formats', 'fuzz', 'writes', 'long']
DEFAULT_SETS = MAKE_SETS + ['random', 'options', 'errors', 'formats', 'fuzz', 'writes']
ALL_SETS = DEFAULT_SETS + ['long']
# What the recipes and the scripts look like at the pin: the harness expands them as these lines
# say, and refuses scripts without them.
SCRIPT_LINES = {
    'test2.sh': ['CURVES=${CURVES:-testcurves2}',
                 '"$JP" "$coeffs" "$h" -q $JPOPTS | LC_ALL=C sort'],
    'test4.sh': ['"$JP" "$coeffs" 30 -q $JPOPTS | LC_ALL=C sort',
                 '"$JP" "$coeffs" 30 -q -a $JPOPTS | LC_ALL=C sort'],
    'testbrute.sh': ['H=${H:-50}', 'CURVES=${CURVES:-testcurves2}', 'for opt in "" "-a"; do',
                     'sieved=$("$JP" "$coeffs" $H -q $opt $JPOPTS | LC_ALL=C sort)',
                     'exact=$("$JP" "$coeffs" $H -q $opt -n 0 -N 0 $JPOPTS | LC_ALL=C sort)'],
    'test3.sh': ['t() {', 'f() {', 'e() {'],
}
CURVE_LOOP = "grep -v '^#' \"$CURVES\" | grep -v '^$' | while IFS=';' read -r coeffs h comment"
CURVE_LOOP4 = "grep -v '^#' testcurves2 | grep -v '^$' | while IFS=';' read -r coeffs h comment"
SHELL_OPS = ('>', '>>', '2>&1', '|', '||', '&&', ';', '<')
ASSIGNMENT = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*=')


class SetupError(Exception):
    """An error in the arguments or the setup."""


@dataclass
class Case:
    """A command line to compare: its arguments (after the program), a note, and how the standard
    output is given: `run` (a file, which is compared), `pipe` (a pipe whose reader is gone) or
    `full` (/dev/full), or `refusal` (a file, the model alone, compared with the refusal of the
    format of -f); and its timeout, if not that of the command line."""
    args: list
    note: str = ''
    kind: str = 'run'
    timeout: float | None = None


@dataclass
class Result:
    """A run of a program: its outputs, its exit status (minus the signal that ended it), its wall
    clock and CPU time, and whether it timed out or wrote beyond the cap."""
    stdout: bytes = b''
    stderr: bytes = b''
    status: int = 0
    wall: float = 0.0
    cpu: float = 0.0
    timed_out: bool = False
    capped: bool = False


@dataclass
class Tally:
    """What a set compared and found, with the times of the two programs."""
    compared: int = 0
    skipped: int = 0
    failures: list = field(default_factory=list)
    c_wall: float = 0.0
    c_cpu: float = 0.0
    m_wall: float = 0.0
    m_cpu: float = 0.0


# ------------------------------------------------------------------------------------------------
# The suites of the C repository


def git_show(repo, rev, path):
    r = subprocess.run(['git', '-C', str(repo), 'show', f'{rev}:{path}'], capture_output=True)
    if r.returncode != 0:
        raise SetupError(f'git show {rev}:{path} in {repo}: {r.stderr.decode().strip()}')
    return r.stdout.decode('utf-8')


def make_tests(makefile):
    """The suites of the Makefile, the value of its TESTS, in their order."""
    for line in makefile.splitlines():
        m = re.match(r'^TESTS\s*=\s*(.*)$', line)
        if m:
            return m.group(1).split()
    raise SetupError('the Makefile has no TESTS')


def recipes(makefile):
    """The recipe lines of each target of the Makefile, as {target: [line, ...]}."""
    out, target = {}, None
    for line in makefile.splitlines():
        if line.startswith('\t'):
            if target is not None:
                out[target].append(line[1:])
            continue
        if line.startswith('#') or not line.strip():
            continue
        m = re.match(r'^([A-Za-z0-9_.-]+)\s*:(?!=)', line)
        target = m.group(1) if m else None
        if target is not None:
            out[target] = []
    return out


def command_of(line):
    """The command of a recipe line that runs ./j-points or a test script: (env, program, args),
    the assignments before it, `time` dropped, and the words up to the first redirection, pipe or
    list operator; None for any other line."""
    try:
        words = shlex.split(line)
    except ValueError:
        return None
    env = {}
    while words and ASSIGNMENT.match(words[0]):
        k, _, v = words.pop(0).partition('=')
        env[k] = v
    if words and words[0] == 'time':
        words.pop(0)
    if not words or not (words[0] == './j-points' or re.match(r'^\./test\w*\.sh$', words[0])):
        return None
    args = []
    for w in words[1:]:
        if w in SHELL_OPS or w.startswith('>'):
            break
        args.append(w)
    if any('$' in w for w in args) or any('$' in v for v in env.values()):
        raise SetupError(f'a variable in the recipe line {line!r}, which the harness does not '
                         f'expand')
    return env, words[0][2:], args


def curve_lines(text):
    """The (coefficients, height) of a curve list as `grep -v '^#' | grep -v '^$' | while IFS=';'
    read -r coeffs h comment` reads it: the lines that are neither comments nor empty, split at
    their first two semicolons."""
    out = []
    for line in text.splitlines():
        if line.startswith('#') or line == '':
            continue
        parts = line.split(';', 2)
        out.append((parts[0], parts[1] if len(parts) > 1 else ''))
    return out


def test3_lines(text):
    """The invocations of test3.sh: (function, args) for each call of t, f and e, the filter of f
    dropped; the arguments as the shell gives them (no line may expand a variable)."""
    out = []
    for line in text.splitlines():
        m = re.match(r'^([tfe])(\s|$)', line)
        if not m:
            continue
        if '$' in line:
            raise SetupError(f'test3.sh: a variable in {line!r}, which the harness does not '
                             f'expand')
        words = shlex.split(line)
        fn, args = words[0], words[1:]
        if fn == 'f':
            args = args[1:]
        out.append((fn, args))
    return out


def check_script(name, text):
    for want in SCRIPT_LINES.get(name, []):
        if want not in text:
            raise SetupError(f'{name} at the pin has no line {want!r}: the harness does not know '
                             f'this version of it')
    if name in ('test2.sh', 'testbrute.sh') and CURVE_LOOP not in text:
        raise SetupError(f'{name}: no loop {CURVE_LOOP!r}')
    if name == 'test4.sh' and CURVE_LOOP4 not in text:
        raise SetupError(f'{name}: no loop {CURVE_LOOP4!r}')


def script_runs(name, env, files):
    """The command lines that the test script `name` runs with the variables `env`, over the
    files `files` ({name: text}) of the repository."""
    check_script(name, files[name])
    jpopts = env.get('JPOPTS', '').split()
    if name == 'test2.sh':
        cs = curve_lines(files[env.get('CURVES', 'testcurves2')])
        return [[c, h, '-q', *jpopts] for c, h in cs]
    if name == 'test4.sh':
        cs = curve_lines(files['testcurves2'])
        return [run for c, _ in cs for run in ([c, '30', '-q', *jpopts],
                                               [c, '30', '-q', '-a', *jpopts])]
    if name == 'testbrute.sh':
        cs = curve_lines(files[env.get('CURVES', 'testcurves2')])
        h = env.get('H', '50')
        return [run for c, _ in cs for opt in ([], ['-a'])
                for run in ([c, h, '-q', *opt, *jpopts], [c, h, '-q', *opt, '-n', '0', '-N', '0',
                                                          *jpopts])]
    if name == 'test3.sh':
        return [args + (jpopts if fn in 'tf' else []) for fn, args in test3_lines(files[name])]
    raise SetupError(f'a recipe runs {name}, which the harness does not know')


def make_suite(target, files):
    """The command lines of the suite `target` of the Makefile."""
    lines = recipes(files['Makefile']).get(target)
    if lines is None:
        raise SetupError(f'the Makefile has no target {target}')
    runs = []
    for line in lines:
        cmd = command_of(line)
        if cmd is None:
            continue
        env, prog, args = cmd
        if prog == 'j-points':
            runs.append(args)
        else:
            runs += script_runs(prog, env, files)
    if not runs:
        raise SetupError(f'the target {target} of the Makefile runs nothing that the harness knows')
    return runs


REPO_FILES = ['Makefile', 'test2.sh', 'test3.sh', 'test4.sh', 'testbrute.sh', 'testcurves2',
              'testcurves-rich']


def repo_files(repo, rev):
    return {name: git_show(repo, rev, name) for name in REPO_FILES}


# ------------------------------------------------------------------------------------------------
# The sets


def height_of(args):
    """The height bound of a command line, its second word if that is a decimal, else None."""
    if len(args) >= 2 and re.fullmatch(r'\d+', args[1]):
        return int(args[1])
    return None


def unsieved(args):
    """Whether the command line pins no sieving primes at all (-N 0), so that the program checks
    every triple of the box exactly."""
    return any(a == '-N' and b.strip() == '0' for a, b in zip(args, args[1:]))


def cut_heights(runs, h, h0=None):
    """The command lines with every height bound in (h, MAX_HEIGHT] cut to h, and in (h0,
    MAX_HEIGHT] cut to h0 for the runs without sieving (if h0 is given), each line once."""
    out, seen = [], set()
    for args in runs:
        k = height_of(args)
        cap = min(h, h0) if h0 is not None and unsieved(args) else h
        if k is not None and cap < k <= MAX_HEIGHT:
            args = [args[0], str(cap), *args[2:]]
        key = tuple(args)
        if key not in seen:
            seen.add(key)
            out.append(args)
    return out


def cases_of(pairs, kind='run'):
    return [Case(list(args), note, kind) for args, note in pairs]


def build_set(name, cfg):
    """The cases of the set `name`."""
    if name in MAKE_SETS:
        return [Case(args, name) for args in make_suite(name, cfg.files)]
    if name == 'random':
        rng = Random(cfg.seed)
        return [Case(difftest_cases.random_run(rng), f'random {i}') for i in range(cfg.random)]
    if name == 'options':
        return cases_of(difftest_cases.OPTION_CASES)
    if name == 'errors':
        return cases_of(difftest_cases.ERROR_CASES)
    if name == 'formats':
        return cases_of(difftest_cases.REFUSAL_CASES, 'refusal')
    if name == 'fuzz':
        rng = Random(cfg.seed)
        return [Case(args, f'fuzz {i}.{j}') for i in range(cfg.fuzz)
                for j, args in enumerate(difftest_cases.random_command_lines(rng))]
    if name == 'writes':
        return (cases_of(difftest_cases.WRITE_CASES, 'pipe') +
                cases_of(difftest_cases.WRITE_CASES, 'full'))
    if name == 'long':
        return [Case(list(args), note, timeout=max(cfg.timeout, LONG_TIMEOUT))
                for args, note in difftest_cases.LONG_CASES]
    if name == 'ci':
        runs = [args for t in MAKE_SETS for args in make_suite(t, cfg.files)]
        runs += [args for args, _ in difftest_cases.OPTION_CASES]
        cases = [Case(args, 'ci') for args in cut_heights(runs, cfg.ci_height, CI_UNSIEVED)]
        cases += cases_of(difftest_cases.CI_EXTRA)
        cases += cases_of(difftest_cases.ERROR_CASES)
        cases += build_set('formats', cfg)
        rng = Random(cfg.seed)
        cases += [Case(difftest_cases.random_run(rng), f'ci random {i}') for i in range(CI_RANDOM)]
        rng = Random(cfg.seed)
        cases += [Case(args, f'ci fuzz {i}.{j}') for i in range(CI_FUZZ)
                  for j, args in enumerate(difftest_cases.random_command_lines(rng))]
        return cases + build_set('writes', cfg)
    raise SetupError(f'no set {name}')


# ------------------------------------------------------------------------------------------------
# Running and comparing


def address_cap(limit):
    """The soft and hard limits of RLIMIT_AS for a cap of `limit` bytes, within the hard limit of
    the harness itself."""
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    soft = limit if hard == resource.RLIM_INFINITY else min(limit, hard)
    return soft, hard


def run_program(cmd, args, cfg, env=None, kind='run', timeout=None):
    """Run the command `cmd` (a list) on the arguments `args`: a Result. The outputs go to
    temporary files, each capped at cfg.output_cap bytes (a write beyond ends the program by
    SIGXFSZ); for the kinds `pipe` and `full` the standard output is a pipe whose reader is gone,
    or /dev/full."""
    mem = address_cap(cfg.memory)

    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_AS, mem)
        resource.setrlimit(resource.RLIMIT_FSIZE, (cfg.output_cap, cfg.output_cap))

    full_env = {**os.environ, **(env or {})}
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        read_end = write_end = None
        if kind == 'pipe':
            read_end, write_end = os.pipe()
            os.close(read_end)
            stdout = write_end
        elif kind == 'full':
            stdout = open('/dev/full', 'wb')
        else:
            stdout = out
        res = Result()
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        t0 = time.monotonic()
        try:
            p = subprocess.Popen([*cmd, *args], stdin=subprocess.DEVNULL, stdout=stdout,
                                 stderr=err, env=full_env, cwd=str(ROOT), preexec_fn=limits,
                                 start_new_session=True)
        finally:
            if write_end is not None:
                os.close(write_end)
            if kind == 'full':
                stdout.close()
        try:
            res.status = p.wait(timeout=timeout or cfg.timeout)
        except subprocess.TimeoutExpired:
            res.timed_out = True
            for sig in (signal.SIGTERM, signal.SIGKILL):
                try:
                    os.killpg(p.pid, sig)
                except ProcessLookupError:
                    break
                try:
                    p.wait(timeout=10)
                    break
                except subprocess.TimeoutExpired:
                    pass
            res.status = p.returncode if p.returncode is not None else -signal.SIGKILL
        res.wall = time.monotonic() - t0
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        res.cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
        for f, attr in ((out, 'stdout'), (err, 'stderr')):
            f.seek(0)
            data = f.read(cfg.output_cap + 1)
            setattr(res, attr, data)
            if len(data) >= cfg.output_cap:
                res.capped = True
        if res.status == -signal.SIGXFSZ:
            res.capped = True
    return res


def first_difference(a, b):
    """The first line where the outputs a (the C program's) and b (the model's) differ, as text."""
    la, lb = a.split(b'\n'), b.split(b'\n')
    for i, (x, y) in enumerate(zip(la, lb)):
        if x != y:
            return f'line {i + 1}: the C program {x[:200]!r}, the model {y[:200]!r}'
    if len(la) != len(lb):
        i = min(len(la), len(lb))
        return (f'the C program has {len(la) - i} lines more' if len(la) > len(lb) else
                f'the model has {len(lb) - i} lines more') + f' after line {i}'
    return 'they differ'


def differences(case, c, m, timeout):
    """How the model's run `m` differs from the C program's run `c` on `case` (for a refusal, from
    the refusal, `refusal_result`): a list of texts, empty if they are equal."""
    out = []
    if c.timed_out:
        out.append(f'the C program did not end within {timeout} s')
    if m.timed_out:
        out.append(f'the model did not end within {timeout} s')
    if c.capped or m.capped:
        out.append('an output beyond the cap ' +
                   ('of the C program' if c.capped else 'of the model'))
    if case.kind == 'pipe' and c.status == -signal.SIGPIPE:
        if m.status not in (-signal.SIGPIPE, 128 + signal.SIGPIPE):
            out.append(f'exit status: the C program ended by SIGPIPE, the model {m.status} (not '
                       f'{128 + signal.SIGPIPE})')
    elif c.status != m.status:
        out.append(f'exit status: the C program {c.status}, the model {m.status}')
    if case.kind in ('run', 'refusal') and c.stdout != m.stdout:
        out.append(f'standard output ({len(c.stdout)} and {len(m.stdout)} bytes): '
                   f'{first_difference(c.stdout, m.stdout)}')
    if m.stderr:
        out.append(f'the model wrote to its standard error: {m.stderr[:300]!r}')
    elif c.stderr:
        out.append(f'the C program wrote to its standard error: {c.stderr[:300]!r}')
    return out


def refusal_result():
    """The run that the model must make on a command line whose format of -f it refuses: the
    refusal on the standard output, the status of the refusal, nothing on the standard error."""
    return Result(stdout=difftest_cases.REFUSAL.encode(), status=difftest_cases.REFUSAL_STATUS)


def shell_word(w):
    """A word as a shell reads it back: quoted by shlex, or as $'...' with escapes when it holds a
    control character, so that a command line stays on one line."""
    if not any(ord(ch) < 32 or ord(ch) == 127 for ch in w):
        return shlex.quote(w)
    esc = {'\n': '\\n', '\t': '\\t', '\r': '\\r', '\x0b': '\\v', '\x0c': '\\f', '\\': '\\\\',
           "'": "\\'"}
    return "$'" + ''.join(esc.get(ch, f'\\x{ord(ch):02x}' if ord(ch) < 32 or ord(ch) == 127
                                  else ch) for ch in w) + "'"


def shell_line(args):
    return ' '.join(shell_word(w) for w in args)


def compare_set(name, cases, cfg):
    tally = Tally()
    for case in cases:
        h = height_of(case.args)
        if cfg.max_height is not None and h is not None and h > cfg.max_height:
            tally.skipped += 1
            continue
        if case.kind == 'refusal':
            c = refusal_result()
            m = run_program(cfg.model, case.args, cfg, env=MODEL_ENV, timeout=case.timeout)
        else:
            c = run_program(cfg.c, case.args, cfg, kind=case.kind, timeout=case.timeout)
            m = run_program(cfg.model, case.args, cfg, env=MODEL_ENV, kind=case.kind,
                            timeout=case.timeout)
        tally.compared += 1
        tally.c_wall += c.wall
        tally.c_cpu += c.cpu
        tally.m_wall += m.wall
        tally.m_cpu += m.cpu
        diffs = differences(case, c, m, case.timeout or cfg.timeout)
        label = f'{case.note}: {shell_line(case.args)}' + \
            ('' if case.kind == 'run' else ' (the model alone, against the refusal of the format)'
             if case.kind == 'refusal' else f' (standard output: {case.kind})')
        if diffs:
            tally.failures.append((label, diffs))
        if cfg.verbose:
            print(('FAIL ' if diffs else 'ok   ') + label, flush=True)
    return tally


# ------------------------------------------------------------------------------------------------
# The setup


def cost_defaults(text):
    """The defaults of the cost model in Constants.lean, as `j-points -c list` prints them: one line
    `NAME value` per constant, in the order of the definitions `def costX : Float := v`, the name
    the upper case of X, the value as %g prints it."""
    lines = []
    for m in re.finditer(r'^def cost(\w+) : Float := (\S+)$', text, re.MULTILINE):
        lines.append(f'{m.group(1).upper()} {float(m.group(2)):g}\n')
    return ''.join(lines)


def pin_commit():
    return tomllib.loads(RECORD.read_text())['pin']['commit']


def find_c(given):
    if given:
        return given
    if os.environ.get('JPOINTS_BIN'):
        return os.environ['JPOINTS_BIN']
    found = shutil.which('j-points')
    if not found:
        raise SetupError('no C program: give --c PATH, set JPOINTS_BIN or put j-points on the '
                         'PATH')
    return found


def executable(cmd):
    """Whether the first word of the command `cmd` (a list) is an executable."""
    exe = cmd[0]
    if os.sep in exe:
        return os.access(exe, os.X_OK) and not os.path.isdir(exe)
    return shutil.which(exe) is not None


def setup(argv):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--model', default=str(ROOT / '.lake' / 'build' / 'bin' / 'j-points-model'))
    ap.add_argument('--c')
    ap.add_argument('--repo', default=os.environ.get('JPOINTS_REPO'))
    ap.add_argument('--rev')
    ap.add_argument('--sets', default=','.join(DEFAULT_SETS))
    ap.add_argument('--timeout', type=float, default=TIMEOUT)
    ap.add_argument('--memory', type=float, default=MEMORY)
    ap.add_argument('--output-cap', type=int, default=OUTPUT_CAP)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--random', type=int, default=200)
    ap.add_argument('--fuzz', type=int, default=50)
    ap.add_argument('--ci-height', type=int, default=100)
    ap.add_argument('--max-height', type=int)
    ap.add_argument('--any-build', action='store_true')
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--max-failures', type=int, default=20)
    ap.add_argument('-v', '--verbose', action='store_true')
    cfg = ap.parse_args(argv)
    cfg.memory = int(cfg.memory)
    sets = []
    for s in cfg.sets.split(','):
        sets += [t for t in (ALL_SETS if s == 'all' else [s]) if t and t not in sets]
    cfg.sets = sets
    for s in cfg.sets:
        if s not in MAKE_SETS + OTHER_SETS:
            raise SetupError(f'no set {s} (the sets: {", ".join(MAKE_SETS + OTHER_SETS)})')
    cfg.files = None
    if any(s in MAKE_SETS or s == 'ci' for s in cfg.sets):
        if not cfg.repo:
            raise SetupError('the suites of the Makefile need a clone of j-points: give --repo '
                             'PATH or set JPOINTS_REPO')
        cfg.files = repo_files(cfg.repo, cfg.rev or pin_commit())
    if cfg.list:
        return cfg
    cfg.model = shlex.split(cfg.model)
    if cfg.model and os.sep in cfg.model[0]:
        cfg.model[0] = os.path.abspath(cfg.model[0])
    cfg.c = [os.path.abspath(find_c(cfg.c))]
    if len(cfg.model) >= 3 and os.path.basename(cfg.model[0]) == 'lake' and cfg.model[1] == 'exe':
        r = subprocess.run([cfg.model[0], 'build', cfg.model[2]], cwd=str(ROOT),
                           stdin=subprocess.DEVNULL, capture_output=True)
        if r.returncode != 0:
            raise SetupError(f'lake build {cfg.model[2]} failed: '
                             f'{r.stdout.decode(errors="replace")[-2000:]}')
    for cmd, what in ((cfg.model, 'the model'), (cfg.c, 'the C program')):
        if not cmd or not executable(cmd):
            raise SetupError(f'{what}: {" ".join(cmd)} is not an executable' +
                             (' (lake build j-points-model, or give --model)'
                              if what == 'the model' else ''))
    if not cfg.any_build:
        got = run_program(cfg.c, ['-c', 'list'], cfg)
        want = cost_defaults(CONSTANTS.read_text())
        if got.stdout.decode('latin-1') != want or got.status != 0:
            raise SetupError(f'{cfg.c[0]} is not the default build (its -c list differs from the '
                             f'defaults of {CONSTANTS.relative_to(ROOT)}: a tuning.mk or another '
                             f'VECTOR); --any-build to run it anyway')
    return cfg


def fmt(seconds):
    return f'{seconds:.1f} s'


def main(argv=None):
    try:
        cfg = setup(argv)
        sets = [(name, build_set(name, cfg)) for name in cfg.sets]
    except SetupError as e:
        print(f'difftest: {e}', file=sys.stderr)
        return 2
    if cfg.list:
        try:
            for name, cases in sets:
                for case in cases:
                    print(f'{name}\t{case.kind}\t{shell_line(case.args)}')
        except BrokenPipeError:
            sys.stdout = None
        return 0
    total, failed = 0, 0
    for name, cases in sets:
        tally = compare_set(name, cases, cfg)
        skipped = f', {tally.skipped} skipped above the height {cfg.max_height}' \
            if tally.skipped else ''
        print(f'{name}: {tally.compared} compared, {len(tally.failures)} failed{skipped}; '
              f'the C program {fmt(tally.c_wall)} (CPU {fmt(tally.c_cpu)}), '
              f'the model {fmt(tally.m_wall)} (CPU {fmt(tally.m_cpu)})', flush=True)
        for label, diffs in tally.failures[:cfg.max_failures]:
            print(f'  FAIL {label}')
            for d in diffs:
                print(f'       {d}')
        if len(tally.failures) > cfg.max_failures:
            print(f'  ... {len(tally.failures) - cfg.max_failures} more failures')
        total += tally.compared
        failed += len(tally.failures)
    print(f'difftest: {total} compared, {failed} failed')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
