#!/usr/bin/env python3
"""Build copies of JPointsLean with other values of the compile-time constants of the model.

No proof of the project may depend on the values of the compile-time constants of the model, the
definitions of `JPoints/Model/Constants.lean` that model the macros of `j-points` (`numPrimes`,
`primeTable`, `maxTablePrime`, `defaultSize`, `samplePairs`, `tubeBand`, `tubeEps`, the defaults
of the cost model, ...), beyond the facts that this file decides. This script checks that: it
builds copies of the committed project with other values of the constants and reports for each
copy whether the targets (by default the model, `JPointsModel`; with `--targets` also the library
`JPoints`, the specification and the proofs) still build. It builds the project once for each
variant, one after the other, so it runs on demand and not in CI.

Usage:

    python3 scripts/constants_check.py --workdir DIR [--repo DIR] [--targets T,...]
        [--variant NAME:const=value,...]... [--keep] [--prepare-only] [--lake PATH]
        [--timeout SECONDS]

    --workdir DIR      where the copies and the logs go (required): a folder outside the
                       repository, or one inside its folder tmp/, which git ignores; never
                       elsewhere inside the repository
    --repo DIR         the repository (default: the one this script lies in, as scripts/), only
                       read
    --targets T,...    the lake targets to build (default JPointsModel); a target other than
                       JPointsModel needs Mathlib, which must then be up to date in the
                       repository's packages
    --variant SPEC     NAME:const=value,const=value,...; may be repeated, and replaces the
                       built-in list VARIANTS below, which runs when no --variant is given
    --keep             keep the copies (WORKDIR/NAME); the logs (WORKDIR/logs) always stay
    --prepare-only     stop each variant before its first lake command and keep the copy
    --lake PATH        the lake to run (default: the toolchain's own, run from the elan
                       toolchains folder without the elan proxy, else `lake` on the PATH)
    --timeout SECONDS  stop a build that takes longer (default 7200)

A constant that a variant names must be a definition of Constants.lean at HEAD, of one of the
kinds:

    def <name> : Nat := <value>          (or Int, Bool, Float, Option Nat), on one line
    def <name> : Double := ⟨0x...⟩       a double by its bits, on one line
    def <name> : Array Nat :=            an array of natural numbers, `#[...]` on the lines after,
      #[..., ...]                        up to its closing bracket

otherwise the script stops before it copies anything. In VARIANTS the values are Python integers
(natural numbers for a `Nat`), `True` and `False` for a `Bool` (`true` and `false` in Lean),
Python floats for a `Float`, `Opt(None)` or `Opt(n)` for an `Option Nat` (`none`, `some n`),
`Dbl('1.5e-5')` for a `Double`, a decimal (or hexadecimal) literal that the script turns into the
bits of the nearest double, as a C compiler turns the literal of the macro into a double, and
`Arr([3, 5, 7])` for an `Array Nat`. In a --variant the values are written as in Lean: `17`,
`-1`, `true`, `0.45`, `1e6`, `none`, `some 3`, a decimal literal for a `Double`, and `[3 5 7]`
(blanks between the entries) for an `Array Nat`.

What it does for each variant, one after the other (never two builds at a time):

1. It copies the repository's HEAD (`git archive HEAD | tar -x`) into WORKDIR/NAME, fresh each
   run. Only committed work is checked: the working tree of the repository plays no part.
2. It lets the copy use the repository's packages without rebuilding them: the copy's
   `.lake/packages` is a symlink to REPO/.lake/packages. Before any lake command it checks that
   every package of the copy's manifest sits there at the manifest's revision (else lake would
   check out another revision, or even delete and clone the package, inside the repository) and
   that every `[[require]]` of the lakefile is in the manifest (else lake would clone a package
   there). When a target needs Mathlib, `lake build --no-build Mathlib` in the copy must then
   succeed (exit status 0, which `--no-build` turns into 3 when a target is out of date, and no
   `error:` line), or the variant is aborted, since a rebuild of Mathlib would write into the
   repository's packages and take hours.
3. It sets the variant's values in the copy's JPoints/Model/Constants.lean, asserting that each
   definition it replaces occurs exactly once.
4. It removes the `#guard` commands from the copy's JPoints/**/*.lean, the examples of the model
   that test the default values against the C program on purpose and are not proofs, and reports
   how many per file. A command is removed from a line that begins with `#guard` followed by white
   space or the end of the line (so never `#guard_msgs`, which the proofs use for their axiom
   guards), outside block comments, up to the next blank line or the next line that starts at
   column 0 (a new command or comment); an `open ... in` or `set_option ... in` line right above
   it goes with it.
5. It builds the targets: `LEAN_NUM_THREADS=2 lake build <targets>` in the copy, with the output
   in WORKDIR/logs/NAME-build.log, and decides success by the log alone: `Build completed
   successfully` and no line beginning with `error:` (never by an exit status).
6. It checks that nothing under REPO/.lake/packages was modified while the variant ran and that
   the log shows no job built outside the project; a change is reported and makes the exit
   status 1.

At the end it prints one line per variant: OK or FAIL, the times and the log, and for a failure
the first errors with their file, their line (and the line at HEAD where guards were removed above
it) and the declaration they are in. Without --keep each copy is deleted after its variant.

Exit status: 0 if every variant builds, 1 if one does not, 2 for an error in the arguments or the
setup. The script needs only the Python standard library (3.11 or later, for tomllib).
"""

import argparse
import json
import os
import re
import shutil
import signal
import struct
import subprocess
import sys
import time
import tomllib
from pathlib import Path

DEFAULT_REPO = str(Path(__file__).resolve().parent.parent)
CONSTANTS_FILE = 'JPoints/Model/Constants.lean'
GUARD_DIR = 'JPoints'
DEFAULT_TARGETS = ['JPointsModel']
# The targets that build on the model alone, without Mathlib.
MODEL_TARGETS = {'JPointsModel', 'j-points-model', 'j-points-brute'}
# The modules and executables of the project, whose `Built` lines are expected in a log.
PROJECT_PREFIXES = ('JPoints', 'BruteMain', 'ModelMain', 'j-points')
MAX_ERRORS = 5


class Opt:
    """A value of a constant of type `Option Nat`: `Opt(None)` for `none`, `Opt(n)` for
    `some n`."""
    def __init__(self, n):
        self.n = n


class Dbl:
    """A value of a constant of type `JPoints.Double`: a decimal or hexadecimal literal, whose
    nearest double (Python's `float`, correctly rounded, as a C compiler rounds a literal) gives
    the bits."""
    def __init__(self, text):
        self.text = text
        self.bits = struct.unpack('>Q', struct.pack('>d', literal_float(text)))[0]


class Arr:
    """A value of a constant of type `Array Nat`: its entries."""
    def __init__(self, items):
        self.items = list(items)


def literal_float(text):
    """The double of a decimal literal or of a hexadecimal one (`0x1p-3`)."""
    t = text.strip()
    if re.match(r'^[+-]?0[xX]', t):
        return float.fromhex(t)
    return float(t)


def odd_primes(n):
    return [p for p in range(3, n + 1, 2) if all(p % q for q in range(3, int(p ** 0.5) + 1, 2))]


COSTS = ['costAnd', 'costSize', 'costWord', 'costTest2', 'costBit', 'costRow3', 'costTest3',
         'costExact', 'costRow', 'costCell', 'costTword', 'costTtest', 'costTrow', 'costRrow',
         'costRexcl', 'costRcut', 'costRange', 'costPass', 'costTable', 'costInit']

# The built-in variants: a name and the values of the constants it changes. Each is a build that the
# C code admits: the table of the primes ends at MAX_PRIME with NUM_PRIMES entries, MAX_PRIME_EVEN
# is the least power of 2 above MAX_PRIME and at most 256 (so that the operands of MODP stay below
# 2^24 and those of MOD3 below 2^16), MAX_TABLE_PRIME is a prime of the table; DEFAULT_SIZE,
# SAMPLE_PAIRS, TUBE_BAND, TUBE_RANGES and TUBE_ROWS are positive; ROW_RANGES is at least 9 (the
# ranges that the eight exclusions of a row can leave); L is at least 5 (a polynomial of degree 4 in
# each variable); ROOT_BITS keeps the products of a height bound and two roots far below the largest
# double (at most 480); TUBE_EPS between tubeEpsMin of JPoints/Proof/Constants.lean (2^-47, the
# least margin that the proofs of the tube admit) and 1, TUBE_BIG at most 2^997 (just above its default), ROW_BEYOND
# above MAX_HEIGHT + LONG_LENGTH and below 2^63
# (so that an end of a range of the real region within it converts to a long); the constants
# of the cost model are positive, as a tuning.mk sets them. The word (LONG_LENGTH and what follows
# from it, MAX_HEIGHT, HALF_MASK) is not varied: the model fixes the 64-bit words of LP64, as the C
# code needs them. `debug` is the build with DEBUG > 0, which selects the short table; `short` cuts
# the table at 61 and gives every prime of it a sieve table; A takes the smallest values and B large
# ones; `avx2` has the defaults of the cost model of the build VECTOR=avx2 (VW = 4), `tuned` the
# values of a tuning.mk, and `eps` a margin of the tube just above the least that the proofs
# admit.
VARIANTS = {
    'debug': {'numPrimes': 5, 'maxPrime': 13, 'maxPrimeEven': 16, 'maxTablePrime': 13,
              'primeTable': Arr([3, 5, 7, 11, 13])},
    'short': {'numPrimes': 17, 'maxPrime': 61, 'maxPrimeEven': 64, 'maxTablePrime': 61,
              'primeTable': Arr(odd_primes(61))},
    'A': {'maxTablePrime': 3, 'defaultSize': 1, 'samplePairs': 1, 'rootBits': 64,
          'tubeBand': 1, 'tubeRanges': 1, 'tubeRows': 1, 'rowRanges': 9, 'coeffRow': 5,
          'tubeEps': Dbl('1e-3'), 'tubeBig': Dbl('1e100'), 'rowBeyond': Dbl('3.1e9'),
          **{c: round(0.001 * (i + 1), 3) for i, c in enumerate(COSTS)}},
    'B': {'maxTablePrime': 251, 'defaultSize': 100000, 'samplePairs': 1000000, 'rootBits': 300,
          'tubeBand': 65536, 'tubeRanges': 100, 'tubeRows': 4096, 'rowRanges': 64,
          'coeffRow': 7, 'tubeEps': Dbl('2e-5'), 'tubeBig': Dbl('1e200'),
          'rowBeyond': Dbl('1e15'), **{c: 1e6 * (i + 1) for i, c in enumerate(COSTS)}},
    'avx2': {'costAnd': 0.45, 'costSize': 450.0, 'costTest2': 4.0},
    'tuned': {'costAnd': 0.71, 'costSize': 912.5, 'costWord': 48.0, 'costTest2': 6.25,
              'costBit': 27.0, 'costExact': 1450.0, 'costCell': 290.0, 'costTtest': 2.5,
              'costTable': 11.0, 'costInit': 95.0},
    'eps': {'tubeEps': Dbl('7.5e-15')},
}

# Environment variables that would change what lake does in the copy (package URLs, an artifact
# cache, another search path); they are removed from the environment of the lake commands.
DROPPED_ENV = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE', 'LAKE_HOME',
               'LAKE_PKG_URL_MAP', 'LAKE_ARTIFACT_CACHE', 'LAKE_CACHE_DIR', 'LAKE_CACHE_KEY',
               'LAKE_NO_CACHE')

_MODIFIERS = r'(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|public|noncomputable)\s+)*'
_LINE_TYPE = r'(?:Nat|ℕ|Int|ℤ|Bool|Float|Option Nat|Double)'
DEF_RE = re.compile(r'^' + _MODIFIERS + r'def\s+(?P<name>[^\s:]+)\s*:\s*(?P<type>'
                    + _LINE_TYPE + r'|Array Nat)\s*:=', re.MULTILINE)
KINDS = {'Nat': 'nat', 'ℕ': 'nat', 'Int': 'int', 'ℤ': 'int', 'Bool': 'bool', 'Float': 'float',
         'Option Nat': 'option', 'Double': 'double', 'Array Nat': 'array'}
GUARD_RE = re.compile(r'#guard(?=[ \t\r\n]|$)')
MODIFIER_IN_RE = re.compile(r'^(?:open|set_option)\b.*\bin\s*$')
COMMAND_START_RE = re.compile(r'(?:[A-Za-z_@#«]|--|/-)')
ANSI_RE = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')
ERROR_LINE_RE = re.compile(r'^\s*error:', re.MULTILINE)
WARNING_LINE_RE = re.compile(r'^\s*warning:', re.MULTILINE)
LEAN_ERROR_RE = re.compile(
    r'^\s*error:\s*(?:\./)*(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):\s*(?P<msg>.*)$')
LOG_ITEM_RE = re.compile(r'^\s*(?:error:|warning:|info:|trace:|[✖⚠✔ℹ•]|Some required|Build )')
DECL_RE = re.compile(
    r'^' + _MODIFIERS + r'(?:(?:partial|unsafe|meta|nonrec)\s+)*'
    r'(?P<kind>theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)'
    r'\b\s*(?P<name>[^\s:({\[]*)')
COMMAND_RE = re.compile(r'^(?P<cmd>#[A-Za-z_]+)')
BUILT_RE = re.compile(r'^\S*\s*\[\d+/\d+\] Built (\S+)', re.MULTILINE)
VARIANT_NAME_RE = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_.-]*$')


class SetupError(Exception):
    """An error in the arguments or the setup, before or outside a build."""


def log(msg=''):
    print(msg, flush=True)


def fmt_time(seconds):
    seconds = int(round(seconds))
    return f'{seconds // 60}m{seconds % 60:02d}s'


def array_text(items, indent='  ', width=100):
    """An `Array Nat` literal on the lines after its definition, wrapped at `width` columns."""
    lines, cur = [], indent + '#['
    words = [str(n) for n in items]
    for i, w in enumerate(words):
        piece = w + (', ' if i + 1 < len(words) else ']')
        if len(cur) + len(piece.rstrip()) > width:
            lines.append(cur.rstrip())
            cur = indent + '  '
        cur += piece
    if not words:
        cur += ']'
    lines.append(cur.rstrip())
    return '\n' + '\n'.join(lines)


def lean_value(value):
    """A value of a constant as Lean writes it: `true`/`false` for a Boolean, a literal with a
    decimal point or an exponent for a float (`repr`, which Lean reads as the same double), the
    anonymous constructor of the bits for a `Double`, `#[...]` for an array."""
    if isinstance(value, bool):
        return 'true' if value else 'false'
    if isinstance(value, float):
        s = repr(value)
        return s if ('.' in s or 'e' in s) else s + '.0'
    if isinstance(value, Opt):
        return 'none' if value.n is None else f'some {value.n}'
    if isinstance(value, Dbl):
        return f'⟨0x{value.bits:016x}⟩'
    if isinstance(value, Arr):
        return '#[' + ', '.join(str(n) for n in value.items) + ']'
    return str(value)


def show_value(value):
    """A value as the report shows it."""
    if isinstance(value, Dbl):
        return f'{value.text} ({lean_value(value)})'
    if isinstance(value, Arr):
        return '[' + ' '.join(str(n) for n in value.items) + ']'
    return lean_value(value)


def fmt_consts(consts):
    return ' '.join(f'{k}={show_value(v)}' for k, v in consts.items())


# ---------------------------------------------------------------------------------------------
# The constants and the variants


def const_line_re(name):
    """The one-line definition `def <name> : T := <value>`, T one of the kinds of one line, with
    the type and the value as groups."""
    return re.compile(r'^(?P<head>' + _MODIFIERS + r'def\s+' + re.escape(name)
                      + r'\s*:\s*(?P<type>' + _LINE_TYPE + r')\s*:=[ \t]*)(?P<value>\S[^\n]*?)'
                      r'[ \t]*$', re.MULTILINE)


def array_re(name):
    """The definition `def <name> : Array Nat := #[...]`, the literal on the same line or on the
    lines after, with the literal as a group."""
    return re.compile(r'^(?P<head>' + _MODIFIERS + r'def\s+' + re.escape(name)
                      + r'\s*:\s*Array Nat\s*:=)(?P<value>\s*#\[[^\]]*\])', re.MULTILINE)


def kind_of(name, text):
    """The kind of the constant `name` of the text of Constants.lean, checking that its
    definition occurs exactly once in a form that the script can set."""
    known = {m.group('name'): m.group('type') for m in DEF_RE.finditer(text)}
    if name not in known:
        raise SetupError(f'{name} is not a constant of {CONSTANTS_FILE} that the script can set '
                         f'(it has: {", ".join(known)})')
    kind = KINDS[known[name]]
    rx = array_re(name) if kind == 'array' else const_line_re(name)
    if len(rx.findall(text)) != 1 or len(DEF_RE.findall(text)) != len(known):
        raise SetupError(f'the definition of {name} does not occur exactly once, in the form '
                         f'that the script sets, in {CONSTANTS_FILE}')
    return kind


def value_kind(value):
    if isinstance(value, bool):
        return 'bool'
    if isinstance(value, int):
        return 'int'
    return {float: 'float', Opt: 'option', Dbl: 'double', Arr: 'array'}.get(type(value), '?')


def check_variants(variants, constants_text):
    """Every constant of every variant is a constant of Constants.lean at HEAD that the script can
    set, and its value has the kind of the constant: an integer for an `Int`, a natural number for
    a `Nat`, a Boolean, a float, an `Opt`, a `Dbl`, an `Arr` of natural numbers."""
    for name, consts in variants.items():
        for key, value in consts.items():
            try:
                kind = kind_of(key, constants_text)
            except SetupError as e:
                raise SetupError(f'variant {name}: {e}') from None
            have = value_kind(value)
            ok = (have == kind or (kind == 'nat' and have == 'int' and value >= 0)) and \
                not (kind == 'array' and any(not isinstance(n, int) or isinstance(n, bool) or
                                             n < 0 for n in value.items)) and \
                not (kind == 'option' and value.n is not None and value.n < 0)
            if not ok:
                raise SetupError(f'variant {name}: {key} takes a value of the kind {kind}, not '
                                 f'{show_value(value)}')


def parse_value(text):
    """A value of a --variant as written there: an integer, `true`/`false`, a float, `none`,
    `some n` or `[a b c]`; a float stays text, which `resolve` turns into a `Float` or a
    `Double`."""
    t = text.strip()
    if re.fullmatch(r'-?\d+', t):
        return int(t)
    if t in ('true', 'false'):
        return t == 'true'
    if t == 'none':
        return Opt(None)
    m = re.fullmatch(r'some\s+(\d+)', t)
    if m:
        return Opt(int(m.group(1)))
    m = re.fullmatch(r'\[([\d\s]*)\]', t)
    if m:
        return Arr(int(n) for n in m.group(1).split())
    if re.fullmatch(r'[+-]?(?:\d+\.\d*(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?|\d+[eE][+-]?\d+|'
                    r'0[xX][0-9a-fA-F.]+[pP][+-]?\d+)', t):
        return t
    raise SetupError(f'{text!r} is not an integer, true, false, a float, none, some n or [a b c]')


def resolve(consts, constants_text):
    """The values of a --variant with each float, written as text, made a `Float` or a `Double`
    as the constant is one, and each integer of a `Float` or a `Double` the same."""
    out = {}
    for key, value in consts.items():
        kind = kind_of(key, constants_text)
        if kind in ('float', 'double') and (isinstance(value, str) or value_kind(value) == 'int'):
            value = Dbl(str(value)) if kind == 'double' else literal_float(str(value))
        elif isinstance(value, str):
            raise SetupError(f'{key} is of the kind {kind}, not a float: {value}')
        out[key] = value
    return out


def parse_variant(spec):
    """`NAME:const=value,...` as (name, {const: value}), the values by parse_value."""
    name, sep, rest = spec.partition(':')
    if not sep or not VARIANT_NAME_RE.match(name):
        raise SetupError(f'--variant {spec!r}: expected NAME:const=value,... with a plain NAME')
    consts = {}
    for item in filter(None, (s.strip() for s in rest.split(','))):
        key, eq, value = item.partition('=')
        key = key.strip()
        if not eq or not key:
            raise SetupError(f'--variant {spec!r}: {item!r} is not const=value')
        if key in consts:
            raise SetupError(f'--variant {spec!r}: {key} is set twice')
        try:
            consts[key] = parse_value(value)
        except SetupError as e:
            raise SetupError(f'--variant {spec!r}: {key}: {e}') from None
    if not consts:
        raise SetupError(f'--variant {spec!r}: no constants')
    return name, consts


def set_constants(text, consts):
    """`text` with the values of `consts`; each definition must occur exactly once."""
    for key, value in consts.items():
        if isinstance(value, Arr):
            text, count = array_re(key).subn(
                lambda m: m.group('head') + array_text(value.items), text)
        else:
            text, count = const_line_re(key).subn(
                lambda m: m.group('head') + lean_value(value), text)
        if count != 1:
            raise SetupError(f'the definition of {key} occurs {count} times in {CONSTANTS_FILE}, '
                             f'not once')
    return text


# ---------------------------------------------------------------------------------------------
# The #guard commands


def block_depth_after(depth, line):
    """The nesting depth of block comments after `line`, given the depth before it."""
    i, n = 0, len(line)
    while i < n:
        if depth > 0:
            if line.startswith('/-', i):
                depth, i = depth + 1, i + 2
            elif line.startswith('-/', i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
            continue
        if line.startswith('--', i):
            break
        if line.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif line[i] == '"':
            i += 1
            while i < n and line[i] != '"':
                i += 2 if line[i] == '\\' else 1
            i += 1
        elif line[i] == "'" and i + 2 < n and line[i + 2] == "'":
            i += 3
        else:
            i += 1
    return depth


def strip_guards(text, path):
    """`text` without its `#guard` commands: (new text, number removed, line map), where the line
    map gives for each line of the new text its line number in `text`."""
    lines = text.splitlines(keepends=True)
    kept = []
    removed = 0
    depth = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if depth == 0 and GUARD_RE.match(line):
            if kept and MODIFIER_IN_RE.match(kept[-1][1]):
                kept.pop()
            j = i + 1
            while j < len(lines) and lines[j].strip() and lines[j][0] in ' \t':
                j += 1
            if j < len(lines) and lines[j].strip() and not COMMAND_START_RE.match(lines[j]):
                raise SetupError(f'{path}:{i + 1}: cannot tell where this #guard ends '
                                 f'(line {j + 1} starts at column 0 but begins no command)')
            for k in range(i, j):
                depth = block_depth_after(depth, lines[k])
            if depth != 0:
                raise SetupError(f'{path}:{i + 1}: this #guard leaves a block comment open')
            removed += 1
            i = j
            continue
        kept.append((i + 1, line))
        depth = block_depth_after(depth, line)
        i += 1
    return ''.join(line for _, line in kept), removed, [n for n, _ in kept]


def strip_guards_in_tree(copy):
    """Remove the #guard commands of every Lean file under copy/JPoints: the counts per file and
    the line maps of the files that changed."""
    counts, line_maps = {}, {}
    for path in sorted((copy / GUARD_DIR).rglob('*.lean')):
        rel = path.relative_to(copy).as_posix()
        text = path.read_text(encoding='utf-8')
        new_text, removed, line_map = strip_guards(text, rel)
        if removed:
            path.write_text(new_text, encoding='utf-8')
            counts[rel] = removed
            line_maps[rel] = line_map
    return counts, line_maps


# ---------------------------------------------------------------------------------------------
# The copy and the shared packages


def git(repo, *args):
    res = subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=True)
    if res.returncode != 0:
        raise SetupError(f'git -C {repo} {" ".join(args)}: {res.stderr.strip()}')
    return res.stdout.strip()


def remove_copy(copy, workdir):
    """Delete the copy, never following the symlink to the shared packages."""
    if copy.is_symlink():
        copy.unlink()
        return
    if not copy.exists():
        return
    if copy.resolve().parent != workdir.resolve():
        raise SetupError(f'refusing to delete {copy}: not directly inside {workdir}')
    packages = copy / '.lake' / 'packages'
    if packages.is_symlink():
        packages.unlink()
    shutil.rmtree(copy)


def export_head(repo, dest):
    """`git -C repo archive HEAD | tar -x -C dest`, checking both commands."""
    archive = subprocess.Popen(['git', '-C', str(repo), 'archive', '--format=tar', 'HEAD'],
                               stdout=subprocess.PIPE)
    tar = subprocess.run(['tar', '-x', '-C', str(dest)], stdin=archive.stdout)
    archive.stdout.close()
    if archive.wait() != 0 or tar.returncode != 0:
        raise SetupError(f'git archive HEAD | tar -x into {dest} failed')


def find_lake(copy, override):
    if override:
        return override
    toolchain = (copy / 'lean-toolchain').read_text().strip()
    elan_home = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan'))
    lake = (elan_home / 'toolchains' / toolchain.replace('/', '--').replace(':', '---')
            / 'bin' / 'lake')
    if lake.is_file() and os.access(lake, os.X_OK):
        return str(lake)
    found = shutil.which('lake')
    if not found:
        raise SetupError(f'no lake for the toolchain {toolchain}')
    return found


def check_packages(repo, copy):
    """The shared packages folder, after checking that lake will neither check out, nor delete,
    nor clone a package in it: every package of the copy's manifest is there at the manifest's
    revision, and every `[[require]]` of the lakefile is in the manifest. Returns the folder and
    a list of warnings."""
    manifest = json.loads((copy / 'lake-manifest.json').read_text())
    shared = repo / manifest.get('packagesDir', '.lake/packages')
    if not shared.is_dir():
        raise SetupError(f'{shared} does not exist: build the repository first')
    problems, warnings, names = [], [], set()
    for entry in manifest.get('packages', []):
        name = entry['name']
        if name.startswith('«') and name.endswith('»'):
            name = name[1:-1]
        names.add(name)
        if entry.get('type') != 'git':
            problems.append(f'{name}: a dependency of type {entry.get("type")} is not supported')
            continue
        pkg = shared / name
        if not (pkg / '.git').exists():
            problems.append(f'{name}: no git repository at {pkg}')
            continue
        head = git(pkg, 'rev-parse', '--verify', 'HEAD')
        if head != entry['rev']:
            problems.append(f'{name}: at {head}, but the manifest of HEAD has {entry["rev"]}')
        url = subprocess.run(['git', '-C', str(pkg), 'remote', 'get-url', 'origin'],
                             capture_output=True, text=True).stdout.strip()

        def norm(u):
            u = u.rstrip('/')
            return u[:-4] if u.endswith('.git') else u

        if norm(url) != norm(entry.get('url', '')):
            warnings.append(f'{name}: remote {url!r}, manifest {entry.get("url")!r}')
    lakefile = copy / 'lakefile.toml'
    if lakefile.exists():
        config = tomllib.loads(lakefile.read_text())
        for req in config.get('require', []):
            if req.get('name') not in names:
                problems.append(f'require {req.get("name")!r} of the lakefile is not in the '
                                'manifest')
    else:
        warnings.append('no lakefile.toml: the requirements were not compared with the manifest')
    if problems:
        raise SetupError('the shared packages do not match the manifest of HEAD (lake would '
                         'change them):\n  ' + '\n  '.join(problems))
    return shared, warnings


def changed_since(root, stamp, limit=8):
    """Up to `limit` paths under `root` (symlinks not followed) modified at or after `stamp`."""
    hits = []
    try:
        if os.lstat(root).st_mtime >= stamp:
            hits.append(str(root))
    except FileNotFoundError:
        return hits
    for dirpath, dirnames, filenames in os.walk(root):
        for entry in dirnames + filenames:
            path = os.path.join(dirpath, entry)
            try:
                if os.lstat(path).st_mtime >= stamp:
                    hits.append(path)
                    if len(hits) >= limit:
                        return hits
            except FileNotFoundError:
                pass
    return hits


# ---------------------------------------------------------------------------------------------
# lake


def lake_env():
    env = {k: v for k, v in os.environ.items() if k not in DROPPED_ENV}
    env['LEAN_NUM_THREADS'] = '2'
    return env


def run_logged(cmd, cwd, log_path, timeout):
    """Run `cmd` in `cwd` with its output in `log_path`: the log text, the exit status (None on a
    timeout) and whether it timed out."""
    with open(log_path, 'w', encoding='utf-8') as out:
        out.write(f'# cwd: {cwd}\n# LEAN_NUM_THREADS=2 {" ".join(cmd)}\n')
        out.flush()
        proc = subprocess.Popen(cmd, cwd=cwd, env=lake_env(), stdout=out,
                                stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                start_new_session=True)
        timed_out = False
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_group(proc)
        except BaseException:
            kill_group(proc)
            raise
    text = ANSI_RE.sub('', Path(log_path).read_text(encoding='utf-8', errors='replace'))
    return text, (None if timed_out else proc.returncode), timed_out


def kill_group(proc):
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(proc.pid, sig)
        except ProcessLookupError:
            return
        try:
            proc.wait(timeout=20)
            return
        except subprocess.TimeoutExpired:
            pass


def parse_errors(text, copy, line_maps):
    """The Lean errors of a build log: (file, line, line at HEAD or None, declaration, message
    lines)."""
    lines = text.splitlines()
    errors = []
    for i, line in enumerate(lines):
        m = LEAN_ERROR_RE.match(line)
        if not m:
            continue
        msg = [m.group('msg')]
        for cont in lines[i + 1:i + 4]:
            if LOG_ITEM_RE.match(cont):
                break
            msg.append(cont)
        rel, lineno = m.group('file'), int(m.group('line'))
        rel = os.path.relpath(rel, copy) if os.path.isabs(rel) else os.path.normpath(rel)
        head_line = None
        if rel in line_maps and 0 < lineno <= len(line_maps[rel]):
            head_line = line_maps[rel][lineno - 1]
        errors.append((rel, lineno, head_line, enclosing_decl(copy / rel, lineno), msg))
    return errors


def enclosing_decl(path, lineno):
    """The declaration or command of `path` that contains line `lineno`, as far as one can tell."""
    try:
        lines = path.read_text(encoding='utf-8').splitlines()
    except OSError:
        return '?'
    for k in range(min(lineno, len(lines)) - 1, -1, -1):
        m = DECL_RE.match(lines[k])
        if m:
            return f'{m.group("kind")} {m.group("name")}'.strip()
        m = COMMAND_RE.match(lines[k])
        if m:
            cmd = lines[k].strip()
            if cmd.endswith(' in') and k + 1 < len(lines):
                cmd += ' ' + lines[k + 1].strip()
            return f'`{cmd}` (line {k + 1})'
    return '?'


# ---------------------------------------------------------------------------------------------
# A variant


def run_variant(name, consts, args, workdir, logs_dir, repo):
    """Prepare and build one variant: a result dict."""
    res = {'name': name, 'consts': consts, 'status': 'FAIL', 'errors': [], 'details': [],
           'notes': []}
    t0 = time.monotonic()
    copy = workdir / name
    tag = f'[{name}]'
    log(f'{tag} {fmt_consts(consts)}')
    remove_copy(copy, workdir)
    copy.mkdir(parents=True)
    export_head(repo, copy)

    shared, warnings = check_packages(repo, copy)
    for w in warnings:
        log(f'{tag} warning: {w}')
        res['notes'].append(w)
    (copy / '.lake').mkdir()
    (copy / '.lake' / 'packages').symlink_to(shared.resolve(), target_is_directory=True)

    constants = copy / CONSTANTS_FILE
    constants.write_text(set_constants(constants.read_text(encoding='utf-8'), consts),
                         encoding='utf-8')
    counts, line_maps = strip_guards_in_tree(copy)
    for rel, count in counts.items():
        log(f'{tag}   {rel}: {count} #guard command{"s" if count != 1 else ""} removed')
    log(f'{tag}   {sum(counts.values())} #guard commands removed in {len(counts)} files')
    res['guards'] = counts
    res['setup_time'] = time.monotonic() - t0
    if args.prepare_only:
        res['status'] = 'PREPARED'
        res['total_time'] = time.monotonic() - t0
        return res

    lake = find_lake(copy, args.lake)
    stamp = time.time()
    if any(t not in MODEL_TARGETS for t in args.targets):
        t1 = time.monotonic()
        nobuild_log = logs_dir / f'{name}-mathlib-nobuild.log'
        log(f'{tag} lake build --no-build Mathlib (log {nobuild_log})')
        text, status, timed_out = run_logged([lake, 'build', '--no-build', 'Mathlib'], copy,
                                             nobuild_log, args.timeout)
        res['nobuild_time'] = time.monotonic() - t1
        res['nobuild_log'] = str(nobuild_log)
        # Not a piped status: lake's own, which `--no-build` sets when a target is out of date.
        if status != 0 or ERROR_LINE_RE.search(text):
            res['log'] = str(nobuild_log)
            res['abort'] = ('aborted: `lake build --no-build Mathlib` in the copy says that '
                            'Mathlib is not up to date in the shared packages; nothing was built')
            lines = [ln.strip() for ln in text.splitlines()
                     if ln.strip() and not ln.startswith('#')]
            res['details'] = [ln for ln in lines if re.match(r'(?:✖|error:)', ln)] or lines[-6:]
            res['total_time'] = time.monotonic() - t0
            res['changed'] = changed_since(shared.resolve(), stamp)
            return res

    t2 = time.monotonic()
    build_log = logs_dir / f'{name}-build.log'
    log(f'{tag} LEAN_NUM_THREADS=2 lake build {" ".join(args.targets)} (log {build_log})')
    # Success is judged by the log alone; the exit status is only recorded.
    text, status, timed_out = run_logged([lake, 'build', *args.targets], copy, build_log,
                                         args.timeout)
    res['build_time'] = time.monotonic() - t2
    res['build_status'] = status
    res['log'] = str(build_log)
    res['warnings'] = len(WARNING_LINE_RE.findall(text))
    jobs = re.search(r'Build completed successfully(?: \((\d+) jobs?\))?', text)
    if jobs and not ERROR_LINE_RE.search(text) and not timed_out:
        res['status'] = 'OK'
        res['jobs'] = jobs.group(1)
    else:
        res['errors'] = parse_errors(text, copy, line_maps)
        if timed_out:
            res['notes'].append(f'timed out after {args.timeout} s')
        if not res['errors']:
            res['details'] = [ln.strip() for ln in text.splitlines() if ERROR_LINE_RE.match(ln)]
    # Lake prints a `Built` line for every job it runs: one outside the project means that a
    # dependency was rebuilt, inside the shared packages.
    outside = sorted({m for m in BUILT_RE.findall(text) if not m.startswith(PROJECT_PREFIXES)})
    if outside:
        res['notes'].append('built outside the project: ' + ', '.join(outside[:10]))
    res['changed'] = changed_since(shared.resolve(), stamp)
    res['total_time'] = time.monotonic() - t0
    log(f'{tag} {res["status"]} after {fmt_time(res["total_time"])}')
    return res


def report(results, head):
    log()
    log(f'== constants check of {head}')
    for r in results:
        times = []
        if 'nobuild_time' in r:
            times.append(f'no-build check {fmt_time(r["nobuild_time"])}')
        if 'build_time' in r:
            times.append(f'build {fmt_time(r["build_time"])}')
        if 'total_time' in r:
            times.append(f'total {fmt_time(r["total_time"])}')
        extra = []
        if r['status'] == 'OK':
            extra.append(f'{r.get("jobs") or "?"} jobs, {r.get("warnings", 0)} warning lines')
        if r.get('abort'):
            extra.append(r['abort'])
        if r.get('changed'):
            extra.append('THE SHARED PACKAGES CHANGED')
        log(f'{r["status"]:<5} {r["name"]}  {fmt_consts(r["consts"])}  {", ".join(times)}'
            f'{"  " + "; ".join(extra) if extra else ""}  log: {r.get("log", "-")}')
        for rel, lineno, head_line, decl, msg in r['errors'][:MAX_ERRORS]:
            at_head = f' (line {head_line} at HEAD)' if head_line not in (None, lineno) else ''
            log(f'        {rel}:{lineno}{at_head} in {decl}: {msg[0]}')
            for cont in msg[1:]:
                log(f'            {cont}')
        if len(r['errors']) > MAX_ERRORS:
            log(f'        ... {len(r["errors"]) - MAX_ERRORS} more errors in the log')
        for line in r['details'][:MAX_ERRORS]:
            log(f'        {line}')
        if len(r['details']) > MAX_ERRORS:
            log(f'        ... {len(r["details"]) - MAX_ERRORS} more lines in the log')
        for note in r['notes']:
            log(f'        note: {note}')
        for path in r.get('changed', []):
            log(f'        changed: {path}')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--repo', default=DEFAULT_REPO, help='the repository (only read)')
    parser.add_argument('--workdir', required=True,
                        help='where the copies and the logs go '
                             '(inside the repository only under tmp/)')
    parser.add_argument('--targets', default=','.join(DEFAULT_TARGETS),
                        help='the lake targets to build (default JPointsModel)')
    parser.add_argument('--variant', action='append', default=[],
                        metavar='NAME:const=value,...',
                        help='a variant (may be repeated; replaces the built-in list)')
    parser.add_argument('--keep', action='store_true', help='keep the copies')
    parser.add_argument('--prepare-only', action='store_true',
                        help='stop each variant before its first lake command (implies --keep)')
    parser.add_argument('--lake', help='the lake executable to run')
    parser.add_argument('--timeout', type=int, default=7200,
                        help='stop a build after this many seconds (default 7200)')
    args = parser.parse_args(argv)
    args.targets = [t for t in args.targets.split(',') if t]

    try:
        repo = Path(args.repo).resolve()
        workdir = Path(args.workdir).absolute()
        if (workdir.resolve() == repo or repo in workdir.resolve().parents) and \
                (repo / 'tmp') not in [workdir.resolve(), *workdir.resolve().parents]:
            raise SetupError(f'the workdir {workdir} lies inside the repository {repo} '
                             '(only its untracked tmp/ may hold copies)')
        if not args.targets:
            raise SetupError('no targets')
        head = git(repo, 'rev-parse', '--short', 'HEAD')
        constants_text = git(repo, 'show', f'HEAD:{CONSTANTS_FILE}')
        if args.variant:
            variants = {}
            for spec in args.variant:
                name, consts = parse_variant(spec)
                if name in variants:
                    raise SetupError(f'variant {name} is given twice')
                variants[name] = resolve(consts, constants_text)
        else:
            variants = VARIANTS
        check_variants(variants, constants_text)
        workdir.mkdir(parents=True, exist_ok=True)
        logs_dir = workdir / 'logs'
        logs_dir.mkdir(exist_ok=True)
        log(f'repository {repo} at HEAD {head}; workdir {workdir}; targets '
            f'{" ".join(args.targets)}')
    except SetupError as e:
        print(f'constants_check: {e}', file=sys.stderr)
        return 2
    results = []
    for name, consts in variants.items():
        try:
            results.append(run_variant(name, consts, args, workdir, logs_dir, repo))
        except SetupError as e:
            # A setup that fails (the shared packages, the copy) fails for the later variants too.
            report(results, head)
            print(f'constants_check: variant {name}: {e}', file=sys.stderr)
            return 2
        finally:
            if not (args.keep or args.prepare_only):
                remove_copy(workdir / name, workdir)
    report(results, head)
    return 0 if all(r['status'] in ('OK', 'PREPARED') and not r.get('changed')
                    for r in results) else 1


if __name__ == '__main__':
    sys.exit(main())
