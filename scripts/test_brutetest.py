#!/usr/bin/env python3
"""Tests of scripts/brutetest.py: the reading of the test files of the C repository, the curves that
j-points transforms, and the comparisons, with stand-ins for the two programs.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import brutetest as bt  # noqa: E402

CURVES = """# a comment
1 4 3 -8 2 8 7;30;a sextic

0 1 2 -1 3 1 1;30;reversed
5 -2 3 1 -1 -1;30;negated
"""

BASE = """# j-points '1 4 3 -8 2 8 7' 30
(1, -1, 0, -8)
(7, 6, 3, -2)
# j-points '1 4 3 -8 2 8 7' 30 -a
(7, 6, -9, -74)
# j-points '0 1 2 -1 3 1 1' 30
# j-points '0 1 2 -1 3 1 1' 30 -a
(0, 1, 0, 0)
# j-points '5 -2 3 1 -1 -1' 30
# j-points '5 -2 3 1 -1 -1' 30 -a
"""


class Reading(unittest.TestCase):
    def test_curves(self):
        self.assertEqual(bt.curves(CURVES), ['1 4 3 -8 2 8 7', '0 1 2 -1 3 1 1', '5 -2 3 1 -1 -1'])

    def test_reference_blocks(self):
        blocks = bt.reference_blocks(BASE)
        self.assertEqual(blocks[('1 4 3 -8 2 8 7', 30, False)], ['(1, -1, 0, -8)', '(7, 6, 3, -2)'])
        self.assertEqual(blocks[('1 4 3 -8 2 8 7', 30, True)], ['(7, 6, -9, -74)'])
        self.assertEqual(blocks[('0 1 2 -1 3 1 1', 30, False)], [])
        self.assertEqual(len(blocks), 6)

    def test_transformed(self):
        self.assertTrue(bt.transformed('0 1 2 -1 3 1 1'))
        self.assertTrue(bt.transformed('0 -1 2 -1 3 1 1'))
        self.assertTrue(bt.transformed('5 -2 3 1 -1 -1'))
        self.assertTrue(bt.transformed('5 -2 3 1 -1 -1 0'))
        self.assertFalse(bt.transformed('0 1 -3 2 1 1'))
        self.assertFalse(bt.transformed('0 2 2 -1 3 1 1'))
        self.assertFalse(bt.transformed('1 4 3 -8 2 8 7'))


class Comparisons(unittest.TestCase):
    """The comparisons, with a git repository holding the two files and shell stand-ins for
    j-points-brute and j-points that print the reference lists, or one point too many."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        d = Path(self.tmp.name)
        repo = d / 'repo'
        repo.mkdir()
        (repo / 'testcurves2').write_text(CURVES)
        (repo / 'testbase4').write_text(BASE)
        env = dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t',
                   GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')
        for cmd in (['init', '-q'], ['add', '.'], ['commit', '-qm', 'x'], ['tag', 'v1']):
            subprocess.run(['git', '-C', str(repo)] + cmd, check=True, env=env)
        self.repo = str(repo)
        # the stand-in prints the block of testbase4 for its curve and -a, ignoring the height
        prog = ('#!/bin/sh\npython3 - "$@" <<\'EOF\'\nimport sys\nsys.path.insert(0, %r)\n'
                'import brutetest as bt\nb = bt.reference_blocks(open(%r).read())\n'
                'print("\\n".join(b[(sys.argv[1], 30, "-a" in sys.argv[3:])]))\n%sEOF\n')
        here = str(Path(__file__).resolve().parent)
        self.good = d / 'good'
        self.good.write_text(prog % (here, str(repo / 'testbase4'), ''))
        self.bad = d / 'bad'
        self.bad.write_text(prog % (here, str(repo / 'testbase4'), 'print("(1, 1, 1, 1)")\n'))
        for p in (self.good, self.bad):
            p.chmod(0o755)

    def tearDown(self):
        self.tmp.cleanup()

    def run_main(self, args):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = bt.main(['--repo', self.repo, '--rev', 'v1'] + args)
        return code, out.getvalue()

    def test_all_ok(self):
        code, out = self.run_main(['--brute', str(self.good), '--jpoints', str(self.good)])
        self.assertEqual(code, 0, out)
        self.assertIn('brutetest: all ok', out)

    def test_extra_point(self):
        code, out = self.run_main(['--brute', str(self.bad)])
        self.assertEqual(code, 1)
        self.assertIn("FAIL testbase4 '1 4 3 -8 2 8 7' 30", out)
        self.assertIn('(1, 1, 1, 1)', out)

    def test_no_repository(self):
        saved = os.environ.pop('JPOINTS_REPO', None)
        try:
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(bt.main(['--brute', str(self.good)]), 2)
        finally:
            if saved is not None:
                os.environ['JPOINTS_REPO'] = saved


if __name__ == '__main__':
    unittest.main()
