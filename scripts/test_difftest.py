#!/usr/bin/env python3
"""Tests of scripts/difftest.py and scripts/difftest_cases.py: the reading of the Makefile and of
the test scripts, the sets, the comparison of two runs, and whole runs of the harness on fake
programs; with JPOINTS_REPO set, also the suites of the C repository at the pin.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import os
import re
import resource
import signal
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from random import Random
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
import difftest as dt  # noqa: E402
import difftest_cases as dc  # noqa: E402

MAKEFILE = '''# a Makefile
TESTS = test1 test2 testx
FAIL = { echo ${FAILED}; false; }

test1: j-points testbase
\ttime ./j-points '1 2 3 4 5 6 7' 200 -q > test.out
\tcmp -s testbase test.out || ${FAIL}

# a comment between rules
test2: j-points testbase2 test2.sh
\t./test2.sh > test2.out 2>&1
\tcmp -s testbase2 test2.out || ${FAIL}

testx: j-points
\t./j-points '1 0 0 0 0 0 1' 20 -q -t 2 > x.out
\tJPOPTS=-a\\ -t\\ 3 CURVES=curves-b ./test2.sh > x.out 2>&1
\tH=7 ./testbrute.sh > x.out || ${FAIL}
\t./test4.sh > x.out 2>&1

clean:
\trm -f *.out
'''
CURVES = '# a comment\n\n1 2 3 4 5 6 7;63;random\n-1 0 0 0 0 1;100;x;y\n'
CURVES_B = '2 0 0 0 0 0 3;30;b\n'
TEST2 = ('JP=${JP:-./j-points}\nCURVES=${CURVES:-testcurves2}\n' + dt.CURVE_LOOP + '; do\n'
         '  "$JP" "$coeffs" "$h" -q $JPOPTS | LC_ALL=C sort\ndone\n')
TEST4 = (dt.CURVE_LOOP4 + '; do\n  "$JP" "$coeffs" 30 -q $JPOPTS | LC_ALL=C sort\n'
         '  "$JP" "$coeffs" 30 -q -a $JPOPTS | LC_ALL=C sort\ndone\n')
TESTBRUTE = ('H=${H:-50}\nCURVES=${CURVES:-testcurves2}\n' + dt.CURVE_LOOP + '; do\n'
             '  for opt in "" "-a"; do\n'
             '    sieved=$("$JP" "$coeffs" $H -q $opt $JPOPTS | LC_ALL=C sort)\n'
             '    exact=$("$JP" "$coeffs" $H -q $opt -n 0 -N 0 $JPOPTS | LC_ALL=C sort)\n'
             '  done\ndone\n')
TEST3 = '''#!/bin/sh
t() { printf '#'; for a; do printf ' <%s>' "$a"; done; echo; "$JP" "$@" $JPOPTS | LC_ALL=C sort; }
f() { filter=$1; shift; "$JP" "$@" $JPOPTS | eval "$filter"; }
e() { printf '#'; for a; do printf ' <%s>' "$a"; done; echo; "$JP" "$@"; }
t '1 2 3 4 5 6 7' 20 -q -a
f 'cat; echo' '1 2 3 4 5 6 7' 60 -q -f '<%ld:%ld>\\t\\\\\\n'
f "grep -v '^This is j-points'" '1 2 3 4 5 6 7' 100 -c AND=0.63
e
e '1 2 3 4 5' 100
'''
FILES = {'Makefile': MAKEFILE, 'test2.sh': TEST2, 'test4.sh': TEST4, 'testbrute.sh': TESTBRUTE,
         'test3.sh': TEST3, 'testcurves2': CURVES, 'curves-b': CURVES_B}


class Makefile(unittest.TestCase):
    def test_tests_and_recipes(self):
        self.assertEqual(dt.make_tests(MAKEFILE), ['test1', 'test2', 'testx'])
        r = dt.recipes(MAKEFILE)
        self.assertEqual(r['test2'], ['./test2.sh > test2.out 2>&1',
                                      'cmp -s testbase2 test2.out || ${FAIL}'])
        self.assertEqual(r['clean'], ['rm -f *.out'])
        self.assertNotIn('FAIL', r)

    def test_command_of(self):
        self.assertEqual(dt.command_of("time ./j-points '1 2' 200 -q > test.out"),
                         ({}, 'j-points', ['1 2', '200', '-q']))
        self.assertEqual(dt.command_of('JPOPTS=-a\\ -t\\ 3 CURVES=c ./test2.sh > o 2>&1'),
                         ({'JPOPTS': '-a -t 3', 'CURVES': 'c'}, 'test2.sh', []))
        self.assertIsNone(dt.command_of('cmp -s testbase test.out || ${FAIL}'))
        self.assertIsNone(dt.command_of('rm -f *.out'))
        with self.assertRaises(dt.SetupError):
            dt.command_of('./j-points "$X" 10')

    def test_suites(self):
        self.assertEqual(dt.make_suite('test1', FILES), [['1 2 3 4 5 6 7', '200', '-q']])
        self.assertEqual(dt.make_suite('test2', FILES),
                         [['1 2 3 4 5 6 7', '63', '-q'], ['-1 0 0 0 0 1', '100', '-q']])
        runs = dt.make_suite('testx', FILES)
        c1, c2 = '1 2 3 4 5 6 7', '-1 0 0 0 0 1'
        self.assertEqual(runs, [
            ['1 0 0 0 0 0 1', '20', '-q', '-t', '2'],
            ['2 0 0 0 0 0 3', '30', '-q', '-a', '-t', '3'],
            [c1, '7', '-q'], [c1, '7', '-q', '-n', '0', '-N', '0'],
            [c1, '7', '-q', '-a'], [c1, '7', '-q', '-a', '-n', '0', '-N', '0'],
            [c2, '7', '-q'], [c2, '7', '-q', '-n', '0', '-N', '0'],
            [c2, '7', '-q', '-a'], [c2, '7', '-q', '-a', '-n', '0', '-N', '0'],
            [c1, '30', '-q'], [c1, '30', '-q', '-a'], [c2, '30', '-q'], [c2, '30', '-q', '-a']])
        with self.assertRaises(dt.SetupError):
            dt.make_suite('clean', FILES)
        with self.assertRaises(dt.SetupError):
            dt.make_suite('nosuch', FILES)

    def test_unknown_script(self):
        files = dict(FILES, **{'test2.sh': TEST2.replace('"$h" -q', '"$h"')})
        with self.assertRaises(dt.SetupError):
            dt.make_suite('test2', files)

    def test_test3(self):
        self.assertEqual(dt.test3_lines(TEST3), [
            ('t', ['1 2 3 4 5 6 7', '20', '-q', '-a']),
            ('f', ['1 2 3 4 5 6 7', '60', '-q', '-f', '<%ld:%ld>\\t\\\\\\n']),
            ('f', ['1 2 3 4 5 6 7', '100', '-c', 'AND=0.63']),
            ('e', []), ('e', ['1 2 3 4 5', '100'])])
        runs = dt.script_runs('test3.sh', {'JPOPTS': '-t 2'}, FILES)
        self.assertEqual(runs[0], ['1 2 3 4 5 6 7', '20', '-q', '-a', '-t', '2'])
        self.assertEqual(runs[3], [])
        with self.assertRaises(dt.SetupError):
            dt.test3_lines("t '1 2' $H\n")

    def test_curve_lines(self):
        self.assertEqual(dt.curve_lines(CURVES), [('1 2 3 4 5 6 7', '63'),
                                                  ('-1 0 0 0 0 1', '100')])
        self.assertEqual(dt.curve_lines(' 1 2 ; 3\nx\n'), [(' 1 2 ', ' 3'), ('x', '')])


class Sets(unittest.TestCase):
    def test_heights(self):
        self.assertEqual(dt.height_of(['1 2', '300', '-q']), 300)
        self.assertIsNone(dt.height_of(['1 2', '+300']))
        self.assertIsNone(dt.height_of(['-c', 'list']))
        runs = [['a', '300', '-q'], ['a', '100', '-q'], ['a', '3037000500'], ['a', '0'],
                ['a', '50'], ['a', '9999', '-q']]
        self.assertEqual(dt.cut_heights(runs, 100),
                         [['a', '100', '-q'], ['a', '3037000500'], ['a', '0'], ['a', '50']])
        runs = [['a', '50', '-q', '-n', '0', '-N', '0'], ['a', '50', '-N', ' 0'],
                ['a', '50', '-N', '01'], ['a', '20', '-N', '0'], ['a', '200', '-N', '0']]
        self.assertEqual(dt.cut_heights(runs, 100, 30),
                         [['a', '30', '-q', '-n', '0', '-N', '0'], ['a', '30', '-N', ' 0'],
                          ['a', '50', '-N', '01'], ['a', '20', '-N', '0'], ['a', '30', '-N', '0']])
        self.assertTrue(dt.unsieved(['a', '5', '-N', '0']))
        self.assertFalse(dt.unsieved(['a', '5', '-n', '0']))

    def test_sets_without_repo(self):
        cfg = SimpleNamespace(seed=3, random=7, fuzz=2, files=None, ci_height=100)
        self.assertEqual(len(dt.build_set('random', cfg)), 7)
        self.assertEqual(len(dt.build_set('fuzz', cfg)), 16)
        writes = dt.build_set('writes', cfg)
        self.assertEqual({c.kind for c in writes}, {'pipe', 'full'})
        self.assertEqual(len(writes), 2 * len(dc.WRITE_CASES))
        self.assertEqual([c.args for c in dt.build_set('random', cfg)],
                         [c.args for c in dt.build_set('random', cfg)])
        with self.assertRaises(dt.SetupError):
            dt.build_set('nosuch', cfg)
        cfg.timeout = 60
        self.assertTrue(all(c.timeout == dt.LONG_TIMEOUT for c in dt.build_set('long', cfg)))

    def test_ci(self):
        cfg = SimpleNamespace(seed=1, random=0, fuzz=0, files=dict(
            FILES, Makefile=MAKEFILE.replace('TESTS = test1 test2 testx', 'TESTS = test1')),
            ci_height=50)
        saved = dt.MAKE_SETS
        dt.MAKE_SETS = ['test1', 'test2']
        try:
            cases = dt.build_set('ci', cfg)
        finally:
            dt.MAKE_SETS = saved
        args = [c.args for c in cases]
        self.assertIn(['1 2 3 4 5 6 7', '50', '-q'], args)
        self.assertNotIn(['1 2 3 4 5 6 7', '200', '-q'], args)
        for a, _ in dc.CI_EXTRA + dc.ERROR_CASES:
            self.assertIn(a, args)
        self.assertEqual(sum(c.kind != 'run' for c in cases), 2 * len(dc.WRITE_CASES))


def result(**kw):
    return dt.Result(**kw)


class Compare(unittest.TestCase):
    def test_equal(self):
        c = result(stdout=b'(1, 0, 0, 1)\n', status=0)
        self.assertEqual(dt.differences(dt.Case([]), c, result(stdout=b'(1, 0, 0, 1)\n'), 9), [])

    def test_stdout(self):
        c = result(stdout=b'a\nb\nc\n')
        d = dt.differences(dt.Case([]), c, result(stdout=b'a\nB\nc\n'), 9)
        self.assertEqual(len(d), 1)
        self.assertIn("line 2: the C program b'b', the model b'B'", d[0])
        d = dt.differences(dt.Case([]), c, result(stdout=b'a\nb\nc'), 9)
        self.assertIn('the C program has 1 lines more after line 3', d[0])
        d = dt.differences(dt.Case([]), c, result(stdout=b'a\nb\nc\nd\n'), 9)
        self.assertIn("line 4: the C program b'', the model b'd'", d[0])
        d = dt.differences(dt.Case([]), c, result(stdout=b'a\nb\nc\n\n'), 9)
        self.assertIn('the model has 1 lines more after line 4', d[0])

    def test_status_and_stderr(self):
        c = result(stdout=b'x', status=3)
        d = dt.differences(dt.Case([]), c, result(stdout=b'x', status=0, stderr=b'panic'), 9)
        self.assertEqual(len(d), 2)
        self.assertIn('exit status: the C program 3, the model 0', d[0])
        self.assertIn("standard error: b'panic'", d[1])
        self.assertIn('the C program wrote', dt.differences(
            dt.Case([]), result(stderr=b'x'), result(), 9)[0])

    def test_pipe(self):
        case = dt.Case([], kind='pipe')
        c = result(status=-signal.SIGPIPE)
        self.assertEqual(dt.differences(case, c, result(status=141), 9), [])
        self.assertEqual(dt.differences(case, c, result(status=-signal.SIGPIPE), 9), [])
        self.assertTrue(dt.differences(case, c, result(status=0), 9))
        self.assertTrue(dt.differences(case, c, result(status=141, stderr=b'e'), 9))
        self.assertTrue(dt.differences(case, result(status=0), result(status=141), 9))
        # the outputs are not compared: there are none
        self.assertEqual(dt.differences(dt.Case([], kind='full'), result(stdout=b'a'),
                                        result(stdout=b'b'), 9), [])

    def test_timeouts_and_caps(self):
        d = dt.differences(dt.Case([]), result(), result(timed_out=True), 7)
        self.assertEqual(d, ['the model did not end within 7 s'])
        d = dt.differences(dt.Case([]), result(timed_out=True), result(), 7)
        self.assertEqual(d, ['the C program did not end within 7 s'])
        d = dt.differences(dt.Case([]), result(), result(capped=True), 7)
        self.assertEqual(d, ['an output beyond the cap of the model'])

    def test_shell_line(self):
        args = ['1 2', "it's", 'a\tb\nc\x0bd\x0c\re\\f\x01', '', '%ld\\n']
        line = dt.shell_line(args)
        self.assertNotIn('\n', line)
        r = subprocess.run(['bash', '-c', 'printf "%s\\0" ' + line], capture_output=True)
        self.assertEqual(r.stdout.decode().split('\0')[:-1], args)

    def test_address_cap(self):
        soft, hard = dt.address_cap(10 ** 9)
        self.assertLessEqual(soft, 10 ** 9)
        if hard != resource.RLIM_INFINITY:
            self.assertLessEqual(soft, hard)

    def test_cost_defaults(self):
        text = dt.CONSTANTS.read_text()
        lines = dt.cost_defaults(text).splitlines()
        self.assertEqual(len(lines), 20)
        self.assertEqual([ln.split()[0] for ln in lines], dc.COST_NAMES)
        self.assertEqual(lines[0], 'AND 0.63')
        self.assertIn('EXACT 1300', lines)
        self.assertIn('TEST2 5.6', lines)


# A fake C program: the -c list of the defaults; else its arguments, one per line, and the exit
# status the number of its arguments modulo 3, or 141 when a write fails without ending it. A fake
# model: the same, but it differs on an argument DIFF (the output), ERR (the standard error),
# STATUS (the exit status) and SLOW (it sleeps), and ignores SIGPIPE.
FAKE = r'''#!/bin/sh
if [ "$#" = 2 ] && [ "$1" = -c ] && [ "$2" = list ]; then
  printf '%s' "$LIST"; exit 0
fi
MODEL=@MODEL@
[ "$MODEL" = 1 ] && trap '' PIPE
for a in "$@"; do
  if [ "$MODEL" = 1 ] && [ "$a" = DIFF ]; then a=diff; fi
  printf '%s\n' "$a" 2>/dev/null || exit 141
  if [ "$MODEL" = 1 ] && [ "$a" = ERR ]; then printf 'oops' >&2; fi
  if [ "$MODEL" = 1 ] && [ "$a" = SLOW ]; then sleep 5; fi
done
if [ "$MODEL" = 1 ] && [ "$1" = STATUS ]; then exit 9; fi
exit $(($# % 3))
'''


class Fakes(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        d = Path(self.dir.name)
        self.c, self.model = d / 'c', d / 'model'
        for path, model in ((self.c, '0'), (self.model, '1')):
            path.write_text(FAKE.replace('@MODEL@', model))
            path.chmod(path.stat().st_mode | stat.S_IXUSR)
        os.environ['LIST'] = dt.cost_defaults(dt.CONSTANTS.read_text())
        self.cfg = SimpleNamespace(c=[str(self.c)], model=[str(self.model)], timeout=2,
                                   memory=dt.MEMORY, output_cap=1000, max_height=None,
                                   verbose=False)

    def tearDown(self):
        self.dir.cleanup()
        del os.environ['LIST']

    def test_compare_set(self):
        cases = [dt.Case(['a', '5']), dt.Case(['DIFF', '5']), dt.Case(['b', 'ERR']),
                 dt.Case(['STATUS']), dt.Case(['SLOW', '1', '2']), dt.Case(['x' * 600, 'y' * 600]),
                 dt.Case(['a', '900'])]
        self.cfg.max_height = 800
        t = dt.compare_set('fake', cases, self.cfg)
        self.assertEqual(t.compared, 6)
        self.assertEqual(t.skipped, 1)
        failed = {label.split(': ', 1)[1]: diffs for label, diffs in t.failures}
        self.assertEqual(sorted(failed), sorted(['DIFF 5', 'b ERR', 'STATUS', 'SLOW 1 2',
                                                 'x' * 600 + ' ' + 'y' * 600]))
        self.assertIn('standard output', failed['DIFF 5'][0])
        self.assertIn("standard error: b'oops'", failed['b ERR'][0])
        self.assertIn('exit status: the C program 1, the model 9', failed['STATUS'][0])
        self.assertIn('the model did not end within 2 s', failed['SLOW 1 2'][0])
        self.assertIn('beyond the cap', failed['x' * 600 + ' ' + 'y' * 600][0])

    def test_main(self):
        argv = ['--c', str(self.c), '--model', str(self.c), '--sets', 'writes,errors',
                '--timeout', '10']
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(dt.main(argv), 0)
        self.assertRegex(out.getvalue(), r'writes: 12 compared, 0 failed')
        self.assertIn(f'difftest: {12 + len(dc.ERROR_CASES)} compared, 0 failed', out.getvalue())
        argv = ['--c', str(self.c), '--model', str(self.model), '--sets', 'writes',
                '--timeout', '10']
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(dt.main(argv), 0)
        # a model that does not ignore SIGPIPE nor exit 141 on a closed pipe
        self.model.write_text(FAKE.replace('@MODEL@', '2').replace('|| exit 141', '|| true'))
        wrapper = f'sh -c "trap \'\' PIPE; exec {self.model} \\"$@\\"" model'
        argv = ['--c', str(self.c), '--model', wrapper, '--sets', 'writes', '--timeout', '10']
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(dt.main(argv), 1)
        self.assertIn('the C program ended by SIGPIPE', out.getvalue())

    def test_lake_exe(self):
        """With `lake exe NAME`, the harness builds NAME first: a fake lake that runs the fake C
        program for `exe` and records `build`, or fails it."""
        d = Path(self.dir.name)
        lake = d / 'lake'
        lake.write_text(f'#!/bin/sh\nif [ "$1" = build ]; then echo "$2" >> {d}/built; '
                        f'[ "$2" = good ]; exit $?; fi\nshift 2\nexec {self.c} "$@"\n')
        lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(dt.main(['--c', str(self.c), '--model', f'{lake} exe good',
                                      '--sets', 'writes']), 0)
        self.assertEqual((d / 'built').read_text(), 'good\n')
        with contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(dt.main(['--c', str(self.c), '--model', f'{lake} exe bad',
                                      '--sets', 'writes']), 2)
        self.assertIn('lake build bad failed', err.getvalue())

    def test_setup_errors(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(dt.main(['--c', str(self.c), '--model', '/no/such', '--sets',
                                      'errors']), 2)
            self.assertEqual(dt.main(['--c', str(self.c), '--sets', 'nosuch']), 2)
            os.environ['LIST'] = 'AND 0.45\n'
            self.assertEqual(dt.main(['--c', str(self.c), '--model', str(self.c), '--sets',
                                      'writes']), 2)
        self.assertIn('is not the default build', err.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(dt.main(['--c', str(self.c), '--model', str(self.c), '--sets',
                                      'writes', '--any-build']), 0)


ADMITTED = re.compile(r"%%|%[-+ #'0]*[0-9]*(?:\.[0-9]*)?ld")


def unescape(s):
    return re.sub(r'\\([nt\\])', lambda m: {'n': '\n', 't': '\t', '\\': '\\'}[m.group(1)], s)


class Cases(unittest.TestCase):
    def test_shapes(self):
        for args, note in (dc.OPTION_CASES + dc.ERROR_CASES + dc.WRITE_CASES + dc.LONG_CASES +
                           dc.CI_EXTRA):
            with self.subTest(args=args):
                self.assertIsInstance(note, str)
                self.assertTrue(all(isinstance(a, str) for a in args))
                h = dt.height_of(args)
                if h is not None and h > 600 and (args, note) not in dc.LONG_CASES:
                    self.assertTrue('-x' in args or h > dt.MAX_HEIGHT or h in (1000, 4500), args)

    def test_formats(self):
        """Every format of FORMATS has conversions %[flags][width][.precision]ld and %% only, at
        most four of the first."""
        for f in dc.FORMATS:
            with self.subTest(format=f):
                s = unescape(f)
                rest = ADMITTED.sub('', s)
                self.assertNotIn('%', rest)
                self.assertLessEqual(len(re.findall(r'(?<!%)%[^%]', s.replace('%%', ''))), 4)

    def test_random(self):
        rng = Random(5)
        for _ in range(300):
            args = dc.random_run(rng)
            words = args[0].split()
            self.assertIn(len(words), (6, 7, 8))
            self.assertIn(int(args[1]), dc.HEIGHTS)
        self.assertEqual(dc.random_run(Random(9)), dc.random_run(Random(9)))

    def test_fuzz(self):
        rng = Random(2)
        for _ in range(100):
            lines = dc.random_command_lines(rng)
            self.assertEqual(len(lines), 8)
            for args in lines:
                self.assertTrue(all(isinstance(a, str) for a in args))
                h = dt.height_of(args)
                self.assertTrue(h is None or h <= 20 or args[-1] == '-x', args)

    def test_costs(self):
        self.assertEqual(dc.ALL_INF.count('=inf'), 20)
        rng = Random(4)
        for _ in range(200):
            self.assertIsInstance(dc.random_costs(rng), str)


REPO = os.environ.get('JPOINTS_REPO')


@unittest.skipUnless(REPO and Path(REPO).is_dir(), 'JPOINTS_REPO is not set')
class TheSuites(unittest.TestCase):
    def test_counts(self):
        files = dt.repo_files(REPO, dt.pin_commit())
        self.assertEqual(dt.make_tests(files['Makefile']), dt.MAKE_SETS)
        counts = {t: len(dt.make_suite(t, files)) for t in dt.MAKE_SETS}
        self.assertEqual(counts, {'test1': 1, 'test2': 61, 'test3': 57, 'test4': 122,
                                  'testbrute': 244, 'testrich': 14, 'testthreads': 76})
        test3 = dt.make_suite('test3', files)
        self.assertIn(['1 178 817 -274 16 1', '60', '-q', '-f', '<%ld:%ld:%ld:%ld>\\t\\\\\\n'],
                      test3)
        self.assertIn([], test3)
        rich = dt.make_suite('testrich', files)
        self.assertTrue(all(r[2:] == ['-q', '-a'] for r in rich))
        threads = dt.make_suite('testthreads', files)
        self.assertEqual(threads[0], ['21 116 171 128 55 12 1', '2000', '-q', '-t', '2'])
        self.assertEqual(threads[1][2:], ['-q', '-t', '3'])
        self.assertEqual(threads[-1][2:], ['-q', '-a', '-t', '3'])


if __name__ == '__main__':
    unittest.main()
