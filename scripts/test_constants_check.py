#!/usr/bin/env python3
"""Tests of scripts/constants_check.py that need no lake: the variants against the constants of the
repository, the values as Lean writes them (the bits of a double, an array), the option --variant,
and the removal of the `#guard` commands, on examples and on every Lean file of the library.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import struct
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import constants_check as cc  # noqa: E402

REPO = Path(cc.DEFAULT_REPO)
CONSTANTS = (REPO / cc.CONSTANTS_FILE).read_text(encoding='utf-8')


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


class Variants(unittest.TestCase):
    def test_builtin_variants_fit_the_constants(self):
        cc.check_variants(cc.VARIANTS, CONSTANTS)

    def test_set_constants(self):
        for name, consts in cc.VARIANTS.items():
            text = cc.set_constants(CONSTANTS, consts)
            for key, value in consts.items():
                with self.subTest(variant=name, constant=key):
                    if isinstance(value, cc.Arr):
                        m = cc.array_re(key).search(text)
                        got = [int(n) for n in m.group('value').strip()[2:-1].split(',')]
                        self.assertEqual(got, value.items)
                    else:
                        m = cc.const_line_re(key).search(text)
                        self.assertEqual(m.group('value'), cc.lean_value(value))
            self.assertTrue(all(len(line) <= 100 for line in text.splitlines()), name)

    def test_set_constants_examples(self):
        text = cc.set_constants(CONSTANTS, cc.VARIANTS['debug'])
        for line in ('def numPrimes : Nat := 5', 'def maxPrimeEven : Nat := 16',
                     'def primeTable : Array Nat :=\n  #[3, 5, 7, 11, 13]\n'):
            self.assertIn(line, text)
        text = cc.set_constants(CONSTANTS, cc.VARIANTS['A'])
        for line in ('def tubeBand : Nat := 1', 'def costAnd : Float := 0.001',
                     f'def tubeEps : Double := ⟨0x{bits(1e-3):016x}⟩'):
            self.assertIn(line + '\n', text)
        # the other constants keep their values
        self.assertIn('def numPrimes : Nat := 53\n', text)
        self.assertIn('def rowBeyond : Double := ⟨0x41edcd6500000000⟩'.replace(
            '0x41edcd6500000000', f'0x{bits(3.1e9):016x}'), text)
        # the default table, set again, is the text of Constants.lean
        text = cc.set_constants(CONSTANTS, {'primeTable': cc.Arr(cc.odd_primes(251))})
        self.assertEqual(text, CONSTANTS)

    def test_default_table(self):
        """The table of Constants.lean is that of the odd primes up to 251, which the variants
        `short` and `debug` cut."""
        m = cc.array_re('primeTable').search(CONSTANTS)
        got = [int(n) for n in m.group('value').strip()[2:-1].replace('\n', ' ').split(',')]
        self.assertEqual(got, cc.odd_primes(251))
        self.assertEqual(cc.VARIANTS['short']['primeTable'].items, got[:17])
        self.assertEqual(cc.VARIANTS['debug']['primeTable'].items, got[:5])

    def test_consistent_tables(self):
        """In every variant that sets the table, the macros fit it."""
        for name, consts in cc.VARIANTS.items():
            if 'primeTable' not in consts:
                continue
            t = consts['primeTable'].items
            with self.subTest(variant=name):
                self.assertEqual(consts['numPrimes'], len(t))
                self.assertEqual(consts['maxPrime'], t[-1])
                e = consts['maxPrimeEven']
                self.assertTrue(e & (e - 1) == 0 and e // 2 <= t[-1] < e)
                self.assertIn(consts['maxTablePrime'], t)

    def test_kinds(self):
        self.assertEqual(cc.kind_of('numPrimes', CONSTANTS), 'nat')
        self.assertEqual(cc.kind_of('costAnd', CONSTANTS), 'float')
        self.assertEqual(cc.kind_of('tubeEps', CONSTANTS), 'double')
        self.assertEqual(cc.kind_of('primeTable', CONSTANTS), 'array')
        for name in ('halfMask', 'version', 'floorDiv', 'noSuchConstant'):
            with self.subTest(name=name), self.assertRaises(cc.SetupError):
                cc.kind_of(name, CONSTANTS)

    def test_unknown_constant(self):
        with self.assertRaises(cc.SetupError):
            cc.check_variants({'X': {'noSuchConstant': 1}}, CONSTANTS)
        with self.assertRaises(cc.SetupError):
            cc.set_constants('def a : Nat := 1\n', {'b': 2})

    def test_wrong_kind(self):
        for consts in ({'numPrimes': True}, {'numPrimes': 1.5}, {'numPrimes': -1},
                       {'costAnd': 3}, {'costAnd': cc.Dbl('3')}, {'tubeEps': 1e-5},
                       {'primeTable': [3, 5]}, {'primeTable': cc.Arr([3, -5])},
                       {'numPrimes': cc.Opt(3)}, {'numPrimes': cc.Arr([3])}):
            with self.subTest(consts=consts), self.assertRaises(cc.SetupError):
                cc.check_variants({'X': consts}, CONSTANTS)

    def test_twice(self):
        with self.assertRaises(cc.SetupError):
            cc.set_constants('def a : Nat := 1\ndef a : Nat := 2\n', {'a': 3})
        with self.assertRaises(cc.SetupError):
            cc.kind_of('a', 'def a : Nat := 1\ndef a : Nat := 2\n')


class Values(unittest.TestCase):
    def test_lean_value(self):
        for value, lean in ((True, 'true'), (False, 'false'), (-1, '-1'), (17, '17'),
                            (0.5, '0.5'), (1e9, '1000000000.0'), (1e-12, '1e-12'),
                            (cc.Opt(None), 'none'), (cc.Opt(3), 'some 3'),
                            (cc.Dbl('1.5e-5'), '⟨0x3eef75104d551d69⟩'),
                            (cc.Dbl('1e300'), '⟨0x7e37e43c8800759c⟩'),
                            (cc.Dbl('4e9'), '⟨0x41edcd6500000000⟩'),
                            (cc.Dbl('0x1p-3'), '⟨0x3fc0000000000000⟩'),
                            (cc.Dbl('-0.0'), '⟨0x8000000000000000⟩'),
                            (cc.Arr([3, 5, 7]), '#[3, 5, 7]')):
            with self.subTest(value=value):
                self.assertEqual(cc.lean_value(value), lean)

    def test_nearest_double(self):
        """A literal between two doubles goes to the nearer one, a tie to the even one, as a C
        compiler rounds it."""
        self.assertEqual(cc.Dbl('9007199254740993').bits, bits(9007199254740992.0))
        self.assertEqual(cc.Dbl('9007199254740995').bits, bits(9007199254740996.0))
        self.assertEqual(cc.Dbl('0.1').bits, 0x3fb999999999999a)
        self.assertEqual(cc.Dbl('1e-320').bits, 0x7e8)

    def test_array_text(self):
        self.assertEqual(cc.array_text([3, 5]), '\n  #[3, 5]')
        text = cc.array_text(cc.odd_primes(251))
        self.assertTrue(all(len(line) <= 100 for line in text.splitlines()))
        self.assertEqual(text.count('\n'), 3)

    def test_parse_variant(self):
        name, consts = cc.parse_variant('X1:numPrimes=5, costAnd=0.45,tubeEps=1e-4,'
                                        'primeTable=[3 5 7 11 13],costSize=450,tubeBig=1e200')
        self.assertEqual(name, 'X1')
        consts = cc.resolve(consts, CONSTANTS)
        self.assertEqual(consts['numPrimes'], 5)
        self.assertEqual(consts['costAnd'], 0.45)
        self.assertEqual(consts['costSize'], 450.0)
        self.assertIsInstance(consts['costSize'], float)
        self.assertEqual(consts['tubeEps'].bits, bits(1e-4))
        self.assertEqual(consts['tubeBig'].bits, bits(1e200))
        self.assertEqual(consts['primeTable'].items, [3, 5, 7, 11, 13])
        cc.check_variants({name: consts}, CONSTANTS)
        self.assertIsInstance(cc.parse_value('none'), cc.Opt)
        self.assertEqual(cc.parse_value('some 4').n, 4)
        self.assertEqual(cc.parse_value('false'), False)

    def test_parse_variant_errors(self):
        for spec in ('X', 'X:', ':numPrimes=1', 'X:numPrimes', 'X:numPrimes=1,numPrimes=2',
                     'X:numPrimes=foo', 'a/b:numPrimes=1', 'X:primeTable=[3,5]'):
            with self.subTest(spec=spec), self.assertRaises(cc.SetupError):
                cc.parse_variant(spec)
        with self.assertRaises(cc.SetupError):
            cc.resolve({'numPrimes': '1.5'}, CONSTANTS)


EXAMPLE = '''def f : Nat := 1

#guard f = 1

open Foo in
#guard f
  = 1
theorem t : f = 1 := rfl
/--
info: x
-/
#guard_msgs in
#print axioms t
/-
#guard f = 2
-/
'''


class Guards(unittest.TestCase):
    def test_example(self):
        text, removed, line_map = cc.strip_guards(EXAMPLE, 'Example.lean')
        self.assertEqual(removed, 2)
        self.assertEqual(line_map, [1, 2, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16])
        lines = EXAMPLE.splitlines(keepends=True)
        self.assertEqual(text, ''.join(lines[n - 1] for n in line_map))
        self.assertIn('#guard_msgs in\n', text)
        self.assertIn('/-\n#guard f = 2\n-/\n', text)
        self.assertNotIn('open Foo in', text)

    def test_unclear_end(self):
        with self.assertRaises(cc.SetupError):
            cc.strip_guards('#guard f\n= 1\n', 'Example.lean')

    def test_library(self):
        """Every Lean file of the library loses its `#guard` commands and nothing else that the
        build needs: no `#guard` command is left outside comments, and every `#guard_msgs`
        stays."""
        total = 0
        for path in sorted((REPO / cc.GUARD_DIR).rglob('*.lean')):
            rel = path.relative_to(REPO).as_posix()
            text = path.read_text(encoding='utf-8')
            with self.subTest(file=rel):
                new_text, removed, _ = cc.strip_guards(text, rel)
                total += removed
                self.assertEqual(new_text.count('#guard_msgs'), text.count('#guard_msgs'))
                depth = 0
                for line in new_text.splitlines():
                    if depth == 0:
                        self.assertIsNone(cc.GUARD_RE.match(line), line)
                    depth = cc.block_depth_after(depth, line)
        self.assertGreater(total, 0)


class Arguments(unittest.TestCase):
    def test_workdir_inside_the_repository(self):
        for workdir in (str(REPO), str(REPO / 'scripts' / 'x')):
            with self.subTest(workdir=workdir), contextlib.redirect_stderr(io.StringIO()) as err:
                self.assertEqual(cc.main(['--workdir', workdir, '--prepare-only']), 2)
            self.assertIn('lies inside the repository', err.getvalue())

    def test_bad_variant(self):
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(cc.main(['--workdir', '/nonexistent-dir-for-the-test/x',
                                      '--variant', 'X:noSuchConstant=1']), 2)
        self.assertIn('noSuchConstant is not a constant', err.getvalue())


if __name__ == '__main__':
    unittest.main()
