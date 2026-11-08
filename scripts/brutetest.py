#!/usr/bin/env python3
"""The brute-force reference against the reference lists of the C repository and against j-points.

usage: scripts/brutetest.py [--brute PATH] [--jpoints PATH] [--repo PATH] [--rev REV]
                            [--height H]

For every curve of `testcurves2` of the C repository (`--repo`, default `$JPOINTS_REPO`) at the
revision `--rev` (default: the commit of the pin in `correspondence/j-points.toml`):

1. the points of `j-points-brute` (`--brute`, default `.lake/build/bin/j-points-brute`) at the
   height bound 30, with and without `-a`, sorted as `LC_ALL=C sort` sorts them, against
   `testbase4`, which Magma made with its Kummer package by brute force over the coprime triples,
   independently of j-points (`mkref4.m` of the C repository);
2. if `--jpoints` gives the program `j-points` built at that revision, its points at the height
   bound `--height` (default 30) with the options of `OPTION_SETS` against those of
   `j-points-brute`: in their order for the curves that j-points searches as given, sorted for the
   curves that it reverses or negates (it then prints the points in the order of the curve
   searched, which the brute-force reference does not model).

Prints one line per comparison, `ok` or `FAIL` with the difference, and exits 1 if any fails.
"""
import argparse
import os
import subprocess
import sys
import tomllib
from pathlib import Path

OPTION_SETS = [[], ['-a'], ['-w', '10'], ['-a', '-w', '100']]
RECORD = Path(__file__).resolve().parent.parent / 'correspondence' / 'j-points.toml'


def pin_commit():
    return tomllib.loads(RECORD.read_text())['pin']['commit']


def git_show(repo, rev, name):
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{name}'], check=True,
                          capture_output=True, text=True).stdout


def curves(text):
    """The coefficient strings of the curves of a `testcurves2` text, in their order."""
    out = []
    for line in text.splitlines():
        if line.strip() and not line.startswith('#'):
            out.append(line.split(';')[0].strip())
    return out


def reference_blocks(text):
    """The point lists of a `testbase4` text, keyed by (coefficients, height, with -a)."""
    blocks, key = {}, None
    for line in text.splitlines():
        if line.startswith('# j-points '):
            rest = line[len('# j-points '):]
            coeffs, tail = rest[1:].split("' ", 1)
            parts = tail.split()
            key = (coeffs, int(parts[0]), '-a' in parts[1:])
            blocks[key] = []
        elif line.strip():
            blocks[key].append(line.strip())
    return blocks


def degree(cs):
    d = len(cs) - 1
    while d > 0 and cs[d] == 0:
        d -= 1
    return max(d, 0)


def transformed(coeffs):
    """Whether j-points reverses or negates the curve (`normalise_curve`)."""
    cs = [int(c) for c in coeffs.split()]
    cs += [0] * (7 - len(cs))
    if degree(cs) == 6 and cs[0] == 0 and abs(cs[1]) == 1:
        return True
    return degree(cs) == 5 and cs[5] == -1


def points(prog, coeffs, height, opts, quiet):
    args = [prog, coeffs, str(height)] + (['-q'] if quiet else []) + opts
    r = subprocess.run(args, capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        raise RuntimeError(f'{" ".join(args)}: exit {r.returncode}: {r.stderr.strip()}')
    return [line for line in r.stdout.splitlines() if line.strip()]


def compare(label, got, want):
    if got == want:
        print(f'ok {label}: {len(got)} points')
        return True
    print(f'FAIL {label}')
    print(f'  missing: {[p for p in want if p not in got]}')
    print(f'  extra:   {[p for p in got if p not in want]}')
    if sorted(got) == sorted(want):
        print('  (the same points, in another order)')
    return False


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--brute', default='.lake/build/bin/j-points-brute')
    ap.add_argument('--jpoints')
    ap.add_argument('--repo', default=os.environ.get('JPOINTS_REPO'))
    ap.add_argument('--rev')
    ap.add_argument('--height', type=int, default=30)
    a = ap.parse_args(argv)
    if not a.repo:
        print('no C repository: give --repo or set JPOINTS_REPO', file=sys.stderr)
        return 2
    rev = a.rev or pin_commit()
    cs_list = curves(git_show(a.repo, rev, 'testcurves2'))
    ref = reference_blocks(git_show(a.repo, rev, 'testbase4'))
    ok = True
    for coeffs in cs_list:
        for all_points in (False, True):
            opts = ['-a'] if all_points else []
            got = sorted(points(a.brute, coeffs, 30, opts, False))
            ok &= compare(f"testbase4 '{coeffs}' 30 {' '.join(opts)}".rstrip(),
                          got, ref[(coeffs, 30, all_points)])
    if a.jpoints:
        for coeffs in cs_list:
            for opts in OPTION_SETS:
                got = points(a.brute, coeffs, a.height, opts, False)
                want = points(a.jpoints, coeffs, a.height, opts, True)
                label = f"j-points '{coeffs}' {a.height} {' '.join(opts)}".rstrip()
                if transformed(coeffs):
                    ok &= compare(label + ' (sorted)', sorted(got), sorted(want))
                else:
                    ok &= compare(label, got, want)
    print('brutetest: ' + ('all ok' if ok else 'FAILED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
