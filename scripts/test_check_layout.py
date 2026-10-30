#!/usr/bin/env python3
"""Tests of scripts/check_layout.py on a throwaway source tree.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_layout as cl  # noqa: E402

GOOD = {
    'JPoints.lean': 'module\npublic import JPoints.Model\npublic import JPoints.Spec\n'
                    'public import JPoints.Proof\n',
    'JPoints/Model.lean': 'module\npublic import JPoints.Model.A\n',
    'JPoints/Model/A.lean': 'module\npublic import Std.Data.HashMap\n'
                            '-- a partial def in a comment\n/-- a docstring: native_decide -/\n'
                            'def f : Nat := 1\n',
    'JPoints/Spec.lean': 'module\npublic import Mathlib.Data.Int.GCD\n',
    'JPoints/Proof.lean': 'module\npublic import JPoints.Model\npublic import JPoints.Spec\n'
                          'public import Mathlib.Tactic\n',
    'comparator/Challenge.lean': 'module\npublic import Mathlib.Data.Int.GCD\n'
                                 'public import JPoints.Model\n',
    'comparator/Solution.lean': 'module\npublic import JPoints\n',
    'ModelMain.lean': 'module\nimport JPoints.Model\n',
}


class Layout(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.saved = cl.ROOT
        cl.ROOT = Path(self.tmp.name)

    def tearDown(self):
        cl.ROOT = self.saved
        self.tmp.cleanup()

    def run_with(self, changes):
        files = dict(GOOD, **changes)
        for rel, text in files.items():
            p = cl.ROOT / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cl.main()
        return code, out.getvalue()

    def test_good(self):
        code, out = self.run_with({})
        self.assertEqual(code, 0, out)

    def test_model_imports(self):
        code, out = self.run_with({'JPoints/Model/A.lean': 'module\nimport Mathlib.Tactic\n',
                                   'ModelMain.lean': 'import Lean\n'})
        self.assertEqual(code, 1)
        self.assertIn('FAIL import-model JPoints/Model/A.lean:2', out)
        self.assertIn('FAIL import-main ModelMain.lean:1', out)

    def test_model_restrictions(self):
        body = ('module\nset_option experimental.vcgen true\npartial def g : Nat → Nat := id\n'
                'unsafe def h : Nat := 0\n@[implemented_by h] def k : Nat := 0\n'
                '@[extern "lean_k"] opaque m : Nat\n')
        code, out = self.run_with({'JPoints/Model/A.lean': body})
        self.assertEqual(code, 1)
        for rule in ('experimental', 'partial', 'unsafe', 'implemented_by', 'extern'):
            self.assertIn(f'FAIL {rule} JPoints/Model/A.lean', out)

    def test_axioms_everywhere(self):
        code, out = self.run_with({
            'JPoints/Proof.lean': GOOD['JPoints/Proof.lean'] +
            'example : 2 + 2 = 4 := by native_decide\nexample : True := by decide +native\n',
            'comparator/Solution.lean': GOOD['comparator/Solution.lean'] +
            'example (x : BitVec 2) : x = x := by bv_decide\n'})
        self.assertEqual(code, 1)
        self.assertEqual(out.count('FAIL axiom'), 3, out)

    def test_spec_and_challenge_imports(self):
        code, out = self.run_with({
            'JPoints/Spec.lean': 'module\npublic import JPoints.Model\n'
                                   'public import JPoints.Mathlib.Foo\n',
            'JPoints/Mathlib/Foo.lean': 'module\npublic import Mathlib.Tactic\n',
            'comparator/Challenge.lean': 'module\npublic import JPoints.Spec\n'})
        self.assertEqual(code, 1)
        self.assertIn('FAIL import-spec JPoints/Spec.lean:2', out)
        self.assertIn('FAIL import-spec JPoints/Spec.lean:3', out)  # Mathlib only
        self.assertIn('FAIL import-challenge comparator/Challenge.lean:2', out)

    def test_roots(self):
        code, out = self.run_with({'JPoints/Model/B.lean': 'module\n',
                                   'JPoints/Proof/C.lean': 'module\n'})
        self.assertEqual(code, 1)
        self.assertIn('JPoints.Model does not import JPoints.Model.B', out)
        self.assertIn('JPoints.Proof does not import JPoints.Proof.C', out)

    def test_import_all(self):
        code, out = self.run_with({
            'JPoints/Model.lean': 'module\npublic import JPoints.Model.A\n'
                                    'import all JPoints.Model.B\n',
            'JPoints/Model/B.lean': 'module\n'})
        self.assertEqual(code, 0, out)

    def test_transitive_root(self):
        code, out = self.run_with({
            'JPoints/Model/A.lean': 'module\npublic import JPoints.Model.B\n',
            'JPoints/Model/B.lean': 'module\n'})
        self.assertEqual(code, 0, out)


if __name__ == '__main__':
    unittest.main()
