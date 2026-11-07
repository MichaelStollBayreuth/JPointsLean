"""The hand-written command lines and the random generators of scripts/difftest.py.

OPTION_CASES force each mode of the sieve (the box, the tube, the tube cut to the real region, the
real region), the condition at 2, each stage and the pins of -n, -M, -N and -p, the chunks of -s,
the constants of the cost model of -c (each name, huge and tiny values, the least normal double),
and the options -a, -w, -1, -q, -f (with the formats of FORMATS) and -t, whose value the model
ignores; ERROR_CASES give the errors 2 to 6, 9 and 10, the strict reading of the coefficients
(blanks, signs, separators) and of the options (words of two characters, counts that are not
negative), the values of -c that are not positive normal doubles (infinities, overflows, subnormals,
the values just below the least normal double that strtod rounds to it with ERANGE), the order of
the checks (also before the refusal of a format of -f) and `-c list`; REFUSAL_CASES give formats of -f that the model refuses
(REFUSED_FORMATS), with its message REFUSAL and its exit status REFUSAL_STATUS; CI_EXTRA are
the searches of the set ci above its height bound; WRITE_CASES
are run with a standard output that fails (a closed pipe, a full device); LONG_CASES are searches
for which the C program takes more than a few seconds, outside the default sets. random_run gives
a random search on a random curve of degree 5 or 6 at a small height, random_command_lines eight
random command lines for the fuzz set. An argument is a str. Every height bound above about 300 is
either a search that the C program finishes within a second or followed by an option that fails,
so that neither program searches.
"""

# The curves of the cases.
P = '21 116 171 128 55 12 1'              # test1: a monic sextic with many points
Q = '1 178 817 -274 16 1'                 # a monic quintic: a square first coordinate
R = '0 -1 2 -1 3 1 1'                     # f0 = 0, f1 = -1: reversed and negated
NEG = '1 2 3 4 5 -1'                      # a quintic with leading coefficient -1: negated
D5 = '1 2 -1 3 1 2'                       # a quintic that is not monic
RICH = '1 1 -2 -15 13 2 1'                # point-rich (ratpoints' testdata-many.h #28)
NONE = '-3 0 0 0 0 0 -5'                  # no points up to the height 30
# coordinates beyond a machine word with -a, real roots of f near 10^10 and 2 10^10
BIG = ('0 400000000000000000000 -200000000060000000000 -399999999969999999998 '
       '200000000059999999999 -30000000002 1')
# lambda (x - 10^17)(x^4 - 1): a real root near 10^17 (test3.sh, invocation 52)
FAR = ('-15999999989999968000000020000000000000000000 159999999899999680000000200 0 0 '
       '15999999989999968000000020000000000000000000 -159999999899999680000000200')
RECORD = '247747600 -985905640 567207969 2396040466 52485681 -470135160 82342800'

# The names of the constants of the cost model (cost_names of j-points.c), in their order.
COST_NAMES = ['AND', 'SIZE', 'WORD', 'TEST2', 'BIT', 'ROW3', 'TEST3', 'EXACT', 'ROW', 'CELL',
              'TWORD', 'TTEST', 'TROW', 'RROW', 'REXCL', 'RCUT', 'RANGE', 'PASS', 'TABLE',
              'INIT']
ALL_INF = ','.join(f'{n}=inf' for n in COST_NAMES)
ALL_HUGE = ','.join(f'{n}=1e30' for n in COST_NAMES)
# The constants that the reports of test3.sh pin to the values of the scalar build.
SCALAR = 'AND=0.63,SIZE=756,TEST2=5.6,TTEST=2'

# Formats for -f: conversions %[flags][width][.precision]ld and %%, at most four of them, the
# escapes \n, \t and \\ that unescape interprets, a backslash that it keeps, characters beyond
# ASCII in UTF-8, fewer than four conversions, none, and the empty format.
FORMATS = ['(%ld, %ld, %ld, %ld)\\n', '[%ld:%ld:%ld:%ld]', '%ld %ld %ld %ld\\n',
           '<%ld|%ld|%ld|%ld>\\t\\\\\\n', '%5ld%-5ld|%+ld % ld\\n', '%05ld %.3ld %8.4ld %-+6ld\\n',
           "%'ld %#ld %0ld %-0ld\\n", '%.0ld|%.0ld|%.0ld|%.0ld\\n', '%.ld %3.ld\\n',
           '%%%ld%%\\n', '%ld\\n', '%ld,%ld\\n', '', 'x\\qy\\n', '\\', '%%',
           '[%24ld|%-3ld|%+ld|%ld] %%;', 'ü%ldé %ld\\n', '%  ld%++ld%- ld\\n',
           '%-024ld|%020ld\\n']

# Formats for -f that the model refuses: a conversion other than %ld (another type, another length,
# none), more than four conversions, a % that starts no conversion, a field beyond 4095, a width or
# a precision from an argument, a position, and a conversion after a % that starts none. The model
# prints REFUSAL and exits with the status REFUSAL_STATUS, where j-points passes the format to
# printf as it is; the set formats runs the model alone on them.
REFUSED_FORMATS = ['%d', '%s', '%ld %ld %ld %ld %ld', '%ld %', '%', '%lld', '%lx', '%lu', '%hd',
                   '%zd', '%Zd', '%ld%n', '%4096ld', '%.4096ld', '%*ld', '%.*ld', '%1$ld', '%l%ld',
                   '%5%', '%ld \\%d', '(%ld, %ld, %ld, %f)\\n']
REFUSAL = ('\nThe format of -f may have only %ld conversions (with flags, width and precision), '
           'at most four,\nand %%.\n\n')
REFUSAL_STATUS = 11

OPTION_CASES = [
    # the modes of the sieve, in reports (message 4 names the mode and the primes)
    ([P, '100'], 'the report: the tube, the default without -a'),
    ([P, '100', '-a'], 'the report with -a: the box'),
    ([P, '300', '-c', 'RCUT=1e-9,RROW=1e-9,REXCL=1e-9,CELL=1e-9'],
     'the tube cut to the real region'),
    ([P, '300', '-a', '-c', 'ROW=1e7,RROW=1,RANGE=1,PASS=1,REXCL=1'], 'the real region'),
    ([P, '300', '-c', 'ROW=1e7,RROW=1,RANGE=1,PASS=1,REXCL=1,CELL=1e9'],
     'the real region with the bound on the fourth coordinate'),
    ([P, '300', '-c', 'CELL=1e6'], 'the tube priced out: the box'),
    ([P, '300', '-q', '-a', '-c', 'ROW=1e7,RROW=1,RANGE=1,PASS=1,REXCL=1'],
     'the real region, the points'),
    ([P, '300', '-q', '-c', 'RCUT=1e-9,RROW=1e-9,REXCL=1e-9,CELL=1e-9'],
     'the tube cut to the real region, the points'),
    ([FAR, '256', '-a', '-c', 'ROW=1e7,RROW=1,RANGE=1,PASS=1,REXCL=1'],
     'the real region of a curve with a real root near 10^17'),
    ([P, '499'], 'just below the height of the condition at 2'),
    ([P, '500'], 'the condition at 2'),
    ([P, '600', '-a'], 'the condition at 2 with -a'),
    ([Q, '600'], 'the condition at 2 on a monic quintic'),
    ([P, '300', '-w', '20'], 'the tube of -w below the height'),
    ([P, '300', '-a', '-w', '20'], 'the tube of -w with -a'),
    ([BIG, '10', '-a'], 'the report of a search with coordinates beyond a machine word'),
    ([R, '100'], 'the report of a reversed and negated curve'),
    ([NEG, '100'], 'the report of a negated quintic'),
    ([D5, '100'], 'the report of a quintic that is not monic'),
    ([NONE, '100'], 'a report without points'),
    ([P, '64'], 'a height bound of a full word'),
    ([P, '63', '-a'], 'a height bound one below a full word'),
    ([P, '65', '-a', '-w', '1'], 'a height bound one above a full word, -w 1'),
    ([P, '1'], 'the height bound 1'),
    ([P, '1', '-a'], 'the height bound 1 with -a'),
    # the stages and the numbers of the primes
    ([P, '40', '-n', '0', '-N', '0'], 'no sieving: every triple checked exactly'),
    ([P, '40', '-q', '-a', '-N', '0'], 'no sieving with -a'),
    ([P, '300', '-n', '0'], 'no first stage'),
    ([P, '150', '-M', '0'], 'the third stage alone'),
    ([P, '100', '-a', '-M', '0'], 'the third stage alone, with -a'),
    ([P, '300', '-n', '3', '-M', '6', '-N', '9'], 'all three stages pinned'),
    ([P, '300', '-N', '9', '-M', '6', '-n', '3'], 'all three stages pinned, in reverse order'),
    ([P, '150', '-n', '9', '-M', '6', '-N', '3'], 'the pins cut to -n <= -M <= -N'),
    ([P, '300', '-a', '-n', '20', '-N', '25'], 'many primes in the first stage'),
    ([P, '300', '-M', '20', '-N', '20'], 'no third stage'),
    ([P, '300', '-n', '2', '-N', '30'], 'a large third stage'),
    ([P, '100', '-a', '-n', '1', '-M', '1', '-N', '53'],
     'every prime, most of them in the third'),
    ([P, '100', '-p', '3'], 'three primes considered'),
    ([P, '300', '-p', '100'], '-p above the number of primes: cut to it'),
    ([P, '300', '-p', '53', '-a'], '-p 53'),
    ([P, '150', '-n', '10', '-p', '5'], '-n above -p'),
    ([P, '150', '-p', '5', '-n', '10', '-M', '12'], '-p before -n and -M'),
    ([P, '40', '-q', '-n', '0', '-M', '0', '-N', '0'], 'all pins 0'),
    ([P, '300', '-q', '-a', '-n', '53', '-N', '53'], 'more first-stage primes than tables'),
    # the size of the bit array
    ([P, '300', '-q', '-s', '1'], '-s 1: several chunks'),
    ([P, '1000', '-q', '-s', '1'], '-s 1 at a larger height'),
    ([P, '300', '-q', '-a', '-s', '1'], '-s 1 in the box'),
    ([P, '300', '-q', '-a', '-s', '2'], '-s 2'),
    ([P, '64', '-q', '-s', '1000000'], '-s above the bit array: cut to it'),
    ([P, '100', '-q', '-s', '9223372036854775807'], '-s 2^63 - 1'),
    ([Q, '600', '-q', '-s', '1'], '-s 1 on a monic quintic'),
    # the constants of the cost model
    *[([P, '300', '-c', f'{n}=1e6'], f'-c {n}=1e6') for n in COST_NAMES],
    *[([P, '300', '-a', '-c', f'{n}=1e-6'], f'-c {n}=1e-6 with -a') for n in COST_NAMES],
    ([P, '300', '-c', 'SIZE=1.7976931348623157e308'], '-c SIZE=DBL_MAX: the largest double'),
    ([P, '300', '-c', 'TEST2=2.2250738585072014e-308'], '-c TEST2=DBL_MIN: the least normal'),
    ([P, '300', '-c', 'WORD=0x1p-1022'], '-c WORD=0x1p-1022: the least normal'),
    ([P, '300', '-c', 'BIT=0x1p-3'], '-c BIT=0x1p-3: a hexadecimal constant'),
    ([P, '300', '-c', 'TROW=+.5e-3,TWORD=1.,TTEST= 5'], '-c with +.5e-3, 1. and a leading blank'),
    ([P, '300', '-c', 'AND=1,AND=2'], '-c with a name twice: the last value'),
    ([P, '300', '-c', 'CELL=1e30'], 'the tube at a huge cost'),
    ([P, '30', '-c', 'EXACT=1e-300'], 'the exact check almost free'),
    ([P, '30', '-c', 'EXACT=1e30'], 'the exact check at a huge cost'),
    ([P, '30', '-c', ALL_HUGE], 'every constant huge'),
    ([P, '100', '-a', '-c', 'TABLE=1e30,INIT=1e30'], 'the tables at a huge cost'),
    ([P, '100', '-n', '3', '-M', '6', '-N', '9', '-c', SCALAR],
     'the report of test3.sh with the scalar constants'),
    (['-c', 'list'], '-c list: the constants in force'),
    # the bound on the fourth coordinate, -1, -q
    ([P, '100', '-q', '-w', '500'], '-w above the height'),
    ([P, '100', '-q', '-w', '1'], '-w 1'),
    ([P, '100', '-q', '-a', '-w', '9223372036854775807'], '-a -w 2^63 - 1'),
    ([Q, '60', '-q', '-a', '-w', '100000'], '-a -w on a monic quintic'),
    ([P, '100', '-q', '-1'], '-1: the first point'),
    ([P, '100', '-1'], '-1 in a report'),
    ([P, '100', '-q', '-a', '-1'], '-1 with -a'),
    ([NONE, '100', '-q', '-1'], '-1 without a point'),
    ([R, '300', '-q', '-1'], '-1 on a reversed curve'),
    ([BIG, '10', '-q', '-a', '-1'], '-1 with coordinates beyond a machine word'),
    ([P, '100', '-q', '-q'], '-q twice'),
    # the format of -f
    *[([P, '60', '-q', '-f', f], f'-f {f!r}') for f in FORMATS],
    *[([BIG, '10', '-q', '-a', '-f', f], f'-f {f!r} with coordinates beyond a word')
      for f in FORMATS],
    *[([R, '60', '-q', '-a', '-f', f], f'-f {f!r} on a reversed curve') for f in FORMATS[:6]],
    ([P, '60', '-f', '%ld %ld %ld %ld\\n'], '-f in a report'),
    ([P, '60', '-q', '-f', '%ld\\n', '-f', '<%ld>\\n'], '-f twice: the last one'),
    ([P, '60', '-q', '-f', '%d', '-f', '<%ld>\\n'], '-f twice: a refused format replaced'),
    # the number of threads, which the model reads and ignores
    ([P, '300', '-q', '-t', '2'], '-t 2'),
    ([P, '300', '-q', '-a', '-t', '3'], '-t 3 with -a'),
    ([P, '300', '-q', '-t', '64'], '-t 64'),
    ([P, '100', '-t', '4'], '-t 4 in a report'),
    ([P, '100', '-q', '-1', '-t', '4'], '-1 with -t 4: one thread'),
    ([BIG, '10', '-q', '-a', '-t', '3', '-f', '[%24ld|%-3ld|%+ld|%ld] %%;'],
     '-t 3 with coordinates beyond a word and a format'),
    ([RICH, '300', '-q', '-a', '-t', '5'], '-t 5 on a point-rich curve'),
]

C8 = '1 2 3 4 5 6 7 8'
C7 = '1 2 3 4 5 6 7'

ERROR_CASES = [
    # error 2, and -c list
    ([], 'no arguments: error 2'),
    ([C7], 'one argument: error 2'),
    (['-c'], '-c alone: error 2'),
    (['-c', 'list', '5'], '-c list with a third argument: read as coefficients'),
    (['-c', 'LIST'], '-c LIST: read as coefficients'),
    (['list', '-c'], 'list -c: read as coefficients'),
    # error 3
    ([C8, '100'], 'eight coefficients: error 3'),
    ([C7 + ' 0', '100'], 'eight coefficients, the last 0: error 3'),
    (['1 2 x', '10'], 'a letter: error 3'),
    (['1\t2 3 4 5 6 7', '10', '-q'], 'a tab as a blank'),
    (['\t1 178 817 \t-274 16\t1\t', '20', '-q'], 'tabs and spaces around and between'),
    (['1\n2 3 4 5 6 7', '10'], 'a line feed is no blank: error 3'),
    (['1 2 3\x0b4 5 6 7', '10'], 'a vertical tab is no blank: error 3'),
    (['1-6 5 22 22 8 1', '10'], 'no blank before a sign: error 3'),
    (['1 6 5 22 22 8 -', '10'], 'a lone sign at the end: error 3'),
    (['1 178 817 - 274 16 1', '10'], 'a lone sign before a blank: error 3'),
    (['+-5 1 0 0 0 1', '10'], 'two signs: error 3'),
    (['1 2 3 4 5 6 +', '10'], 'a lone + at the end: error 3'),
    (['1 0 0 0 0 1,', '10'], 'a comma after the last coefficient: error 3'),
    (['1 2 -', '10'], 'a lone sign, error 3 before error 5'),
    (['1 0 0 0 0 -1 -', 'abc'], 'a lone sign, error 3 before error 4'),
    ([C7 + ' ', '10', '-q'], 'a trailing blank'),
    (['  ' + C7, '10', '-q'], 'leading blanks'),
    (['1  2   3 4 5 6 7', '10', '-q'], 'several blanks between'),
    (['1 2 3 4 5 6 7 -', '10'], 'a sign after the seventh coefficient: error 3'),
    (['+1 +2 +3 +4 +5 +6 +7', '10', '-q'], 'all with +'),
    (['-0 1 2 3 4 5 6', '10', '-q'], '-0 is 0'),
    (['1 2 3 4 5 6 7x', '10'], 'a letter after the seventh coefficient: error 3'),
    (['1 2 3 4 5 6 7,', '10'], 'a comma after the seventh coefficient: error 3'),
    # error 5
    (['1 2 3 4 5', '100'], 'degree 4: error 5'),
    (['0 0 0 0 0 0 0', '100'], 'the zero polynomial: error 5'),
    (['', '100'], 'no coefficients: error 5'),
    (['   ', '100'], 'only blanks: error 5'),
    (['1 2 3 4 5 0 0', '10'], 'zero leading coefficients dropped: degree 4, error 5'),
    (['-', '10'], 'a lone sign: error 3'),
    (['\t\t', '10'], 'only tabs: error 5'),
    (['+5', '10'], 'one coefficient: error 5'),
    (['1 2 3 4 5 6 0', '10', '-q'], 'a zero leading coefficient dropped: degree 5'),
    # error 9
    (['2 0 5 0 4 0 1', '100'], '(x^2 + 1)^2 (x^2 + 2): error 9'),
    (['1 -2 1 0 1 -2 1', '100'], '(x - 1)^2 (x^4 + 1): error 9'),
    (['0 0 1 0 0 1', '100'], 'x^2 (x^3 + 1): error 9'),
    (['2 0 5 0 4 0 1', '0'], 'error 9 comes before error 4'),
    # error 4
    ([C7, '0'], 'height 0: error 4'),
    ([C7, '-1'], 'height -1: error 4'),
    ([C7, '67108865'], 'height above MAX_SEARCH_HEIGHT: error 4'),
    ([C7, '67108864', '-x'], 'height MAX_SEARCH_HEIGHT accepted, then -x: error 6'),
    ([C7, '3037000499'], 'height MAX_HEIGHT, above MAX_SEARCH_HEIGHT: error 4'),
    ([C7, '3037000500'], 'height above MAX_HEIGHT: error 4'),
    ([C7, 'abc'], 'height abc: error 4'),
    ([C7, ''], 'an empty height: error 4'),
    ([C7, '1e3', '-q'], 'height 1e3 reads as 1'),
    ([C7, ' \t7', '-q'], 'blanks before the height'),
    ([C7, '+5', '-q'], 'height +5'),
    ([C7, '10abc', '-q'], 'height 10abc reads as 10'),
    ([C7, '9223372036854775808'], 'height 2^63: out of range, error 4'),
    ([C7, '-9223372036854775809'], 'height below -2^63: error 4'),
    ([C7, '0x10'], 'height 0x10 reads as 0: error 4'),
    ([C7, '+ 5'], 'a blank after the sign: error 4'),
    # error 6
    ([C7, '10', '-x'], 'an unknown option: error 6'),
    ([C7, '10', 'q'], 'a word without -: error 6'),
    ([C7, '10', '-'], 'a lone -: error 6'),
    ([C7, '10', ''], 'an empty word: error 6'),
    *[([C7, '10', '-q', '-' + o], f'-{o} without its value: error 6') for o in 'nMNpswtfc'],
    *[([C7, '10', '-q', '-' + o, 'x'], f'-{o} x: error 6') for o in 'nMNpswt'],
    *[([C7, '10', '-q', '-' + o, ' 3 '], f'-{o} with blanks around: accepted') for o in 'nMNpswt'],
    *[([C7, '10', '-q', '-' + o, '9223372036854775808'], f'-{o} 2^63: error 6')
      for o in 'nMNpswt'],
    ([C7, '10', '-q', '-s', '0'], '-s 0: error 6'),
    ([C7, '10', '-q', '-s', '-1'], '-s -1: error 6'),
    ([C7, '10', '-q', '-p', '0'], '-p 0: error 6'),
    ([C7, '10', '-q', '-p', '-3'], '-p -3: error 6'),
    ([C7, '10', '-q', '-w', '0'], '-w 0: error 6'),
    ([C7, '10', '-q', '-w', '-5'], '-w -5: error 6'),
    ([C7, '10', '-q', '-w', '1000000000000000000000000000000'], '-w above a long: error 6'),
    ([C7, '10', '-q', '-t', '0'], '-t 0: error 6'),
    ([C7, '10', '-q', '-t', '-1'], '-t -1: error 6'),
    ([C7, '10', '-q', '-n5'], '-n5: not a word of two characters, error 6'),
    ([C7, '10', '-q', '-n5', '7'], '-n5 7: error 6'),
    ([C7, '10', '-q', '-nx', '5'], '-nx 5: error 6'),
    ([C7, '10', '-quiet'], '-quiet: error 6'),
    ([C7, '10', '-q', '-all'], '-all: error 6'),
    ([C7, '10', '-q', '-1x'], '-1x: error 6'),
    ([C7, '10', '-q', '-cfoo', 'AND=1'], '-cfoo AND=1: error 6'),
    ([C7, '10', '-q', '--'], '--: error 6'),
    ([C7, '10', '-q', '-qq'], '-qq: error 6'),
    ([C7, '10', '-q', '-é'], '-é, two characters and three bytes: error 6'),
    ([C7, '10', '-q', '-n', '-1'], '-n -1: error 6'),
    ([C7, '10', '-q', '-M', '-2'], '-M -2: error 6'),
    ([C7, '10', '-q', '-N', '-1'], '-N -1: error 6'),
    ([C7, '10', '-q', '-n', '-5', '-M', '-1', '-N', '-2'], 'negative pins: error 6'),
    ([C7, '10', '-q', '-n', '0', '-M', '0', '-N', '0'], 'all pins 0: accepted'),
    ([C7, '10', '-q', '-n', '5x'], '-n 5x is -n 5'),
    ([C7, '10', '-q', '-a', '-x'], 'an unknown option after a good one: error 6'),
    # error 10
    *[([C7, '10', '-q', '-c', v], f'-c {v!r}: error 10')
      for v in ['FOO=1', 'AND', 'AND=0', 'AND=-1', 'AND=nan', 'AND=NAN', 'AND=', 'AND=1x',
                '=1', 'AND=1,,SIZE=2', ',', 'and=1', 'AND=1e-400', 'AND=5 ', 'AND=-inf',
                'AND=1;SIZE=2', 'AND=1,FOO=2', 'ANDX=1', 'AN=1', 'AND==1', 'AND=0x', 'AND=-0',
                '', 'AND=0.63,', 'AND=1, SIZE=2', 'AND=inf', 'AND=INFINITY', 'AND=1e999',
                'AND=1.7976931348623159e308', 'AND=0x1p1024', 'AND=1e-320', 'AND=4.9e-324',
                'AND=0x1p-1030', 'AND=0x1p-1074', 'AND=2.2250738585072011e-308',
                'AND=2.2250738585072012e-308', 'AND=2.225073858507201e-308',
                'AND=0x1.fffffffffffffp-1023', 'AND=0x1.fffffffffffff4p-1023',
                'SIZE=1,TEST2=inf', ALL_INF]],
    *[([C7, '10', '-q', '-c', v], f'-c {v!r}: accepted')
      for v in ['AND=1e-300', 'AND=2.2250738585072013e-308', 'AND=2.2250738585072014e-308',
                'AND=0x1p-1022', 'AND=0x1.fffffffffffff8p-1023', 'AND=0x1.fffffffffffffcp-1023',
                'AND=1.7976931348623157e308']],
    # the order of the checks
    ([C8, 'abc'], 'error 3 before error 4'),
    (['1 2 3 4', 'abc'], 'error 5 before error 4'),
    (['2 0 5 0 4 0 1', 'abc', '-x'], 'error 9 before error 4'),
    ([C7, 'abc', '-x'], 'error 4 before error 6'),
    ([C7, '10', '-c', 'FOO=1', '-x'], 'error 10 at -c, before the -x after it'),
    ([C7, '10', '-x', '-c', 'FOO=1'], 'error 6 at -x, before the -c after it'),
    ([C7, '10', '-n', 'x', '-c', 'FOO=1'], 'error 6 at -n x'),
    ([C7, 'abc', '-f', '%d'], 'error 4 before the refusal of the format'),
    ([C7, '10', '-f', '%s', '-x'], 'error 6 before the refusal of the format'),
    ([C7, '10', '-f', '%s', '-c', 'FOO=1'], 'error 10 before the refusal of the format'),
]

# The command lines with a format of -f that the model refuses, which it refuses once the command
# line is read, before any message: the set formats.
REFUSAL_CASES = [
    *[([P, '60', '-q', '-f', f], f'-f {f!r}') for f in REFUSED_FORMATS],
    *[([P, '60', '-f', f], f'-f {f!r} without -q') for f in REFUSED_FORMATS[:3]],
    ([P, '60', '-q', '-f', '%ld\\n', '-f', '%d'], '-f twice: an admitted format replaced'),
    ([BIG, '10', '-a', '-1', '-f', '%lu %lu %lu %lu\\n'], '-f with -a and -1'),
]

# The searches of the set ci that need a height bound above its own: the condition at 2.
CI_EXTRA = [
    ([P, '500'], 'the condition at 2'),
    ([P, '600', '-q', '-a'], 'the condition at 2 with -a'),
]

# Searches run with a standard output that fails: once a pipe whose reader is gone, once
# /dev/full. Their outputs: a short one (a part of one buffer), a long one (many buffers), none,
# an error message and a report.
WRITE_CASES = [
    ([P, '100', '-q'], 'a short output'),
    ([RICH, '300', '-q', '-a'], 'a long output'),
    ([NONE, '30', '-q'], 'no output'),
    ([C7, '0'], 'error 4'),
    ([], 'error 2'),
    ([P, '100'], 'a report'),
]

# Searches for which the C program takes more than a few seconds: not in the default sets.
LONG_CASES = [
    ([P, '2000', '-q', '-a'], 'test1 with -a (about 2 s for the C program, 1 min for the model)'),
    ([P, '5000', '-q'], 'test1 at 5000 (about 5 s, the model about 2 h)'),
    ([Q, '20000', '-q'], 'a monic quintic at 20000 (about 10 s, the model about 1 h)'),
    ([RICH, '3000', '-q', '-a'],
     'a point-rich curve at 3000 with -a (about 10 s, the model about 4 min)'),
    ([RECORD, '3000', '-q', '-a'],
     'the record curve at 3000 with -a (about 7 s, the model about 4 min)'),
    ([P, '300', '-q', '-n', '0', '-N', '0'],
     'no sieving at 300 (about 35 s, the model about 2 min)'),
    ([P, '5000'], 'the report of test1 at 5000 (about 5 s, the model about 2 h)'),
]

# The height bounds of the random searches: small ones, and those around a full word.
HEIGHTS = (1, 2, 3, 5, 10, 20, 30, 50, 63, 64, 65, 100, 127, 128, 129, 200)
SIZES = (1, 3, 10, 10, 10, 100, 10 ** 4, 10 ** 9, 10 ** 20)


def random_curve(rng):
    """A coefficient list of a random curve of degree 5 or 6: small or large coefficients, at times
    a monic quintic, one with leading coefficient -1 (negated by the program), a sextic with
    f0 = 0 and f1 = +-1 (reversed), a square leading coefficient (points at infinity), a root at 0,
    or a zero after the leading coefficient (dropped)."""
    deg = rng.choice((5, 6))
    size = rng.choice(SIZES)
    cs = [rng.randint(-size, size) for _ in range(deg + 1)]
    while cs[deg] == 0:
        cs[deg] = rng.randint(-size, size)
    k = rng.random()
    if deg == 5 and k < 0.2:
        cs[5] = 1
    elif deg == 5 and k < 0.3:
        cs[5] = -1
    elif deg == 6 and k < 0.15:
        cs[0], cs[1] = 0, rng.choice((-1, 1))
    elif deg == 6 and k < 0.3:
        cs[6] = rng.randint(1, 10) ** 2
    elif k < 0.35:
        cs[0] = 0
    words = [str(c) for c in cs]
    if rng.random() < 0.05:
        words.append('0')
    return ' '.join(words)


def random_run(rng):
    """A random search: a random curve at a height of HEIGHTS, with -q mostly, and at times -a, -w,
    -1 and pins of the stages."""
    h = rng.choice(HEIGHTS)
    opts = []
    if rng.random() < 0.8:
        opts.append('-q')
    if rng.random() < 0.3:
        opts.append('-a')
    if rng.random() < 0.2:
        opts += ['-w', str(rng.choice((1, 2, max(1, h // 2), h, 2 * h, 10 ** 6)))]
    if rng.random() < 0.1:
        opts.append('-1')
    if rng.random() < 0.1:
        opts += ['-n', str(rng.randint(0, 12)), '-N', str(rng.randint(1, 30))]
    return [random_curve(rng), str(h), *opts]


# C white space (isspace in the C locale), which strtol and strtod skip; scan_mpz skips only the
# blanks ' ' and '\t'.
SPACE = ' \t\n\x0b\x0c\r'
LONG_OPTS = 'nMNpswt'


def random_digits(rng, alphabet, lengths=(0, 1, 1, 2, 3)):
    return ''.join(rng.choice(alphabet) for _ in range(rng.choice(lengths)))


def random_long(rng):
    """A word for strtol in base 10, often malformed or beyond a long."""
    p = []
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE))
    if rng.random() < 0.4:
        p.append(rng.choice(['+', '-', '+', '-', '--', '+-', '- ']))
    if rng.random() < 0.3:
        p.append(rng.choice(['9223372036854775807', '9223372036854775808', '9223372036854775806',
                             '09223372036854775807', '18446744073709551616',
                             '99999999999999999999', '922337203685477580', '3037000499',
                             '3037000500']))
    else:
        p.append(random_digits(rng, '0123456789', (0, 1, 1, 2, 5)))
    if rng.random() < 0.15:
        p.append(rng.choice(['x', '.0', 'e3', ' 1', '\t', 'L', '_000', ',']))
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE) * rng.randint(1, 2))
    return ''.join(p)


def random_double(rng):
    """A word for strtod: a decimal or hexadecimal constant, an infinity or a NaN, often
    malformed, at times with white space and a sign."""
    p = []
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE) * rng.randint(1, 2))
    if rng.random() < 0.4:
        p.append(rng.choice('+-'))
    k = rng.random()
    if k < 0.15:
        p.append(rng.choice(['inf', 'INF', 'Inf', 'infinity', 'Infinity', 'INFINITY', 'iNfInItY',
                             'infinit', 'infx', 'nan', 'NaN', 'NAN', 'nan(1)', 'nan()', 'nan(',
                             'in', 'i', 'infinityy']))
    elif k < 0.25:
        p.append(rng.choice(['1e999', '1e308', '1.7976931348623157e308', '1e-320', '4.9e-324',
                             '2.4703282292062327e-324', '1e-400', '0x1p-1074', '0x1p-1075',
                             '2.2250738585072011e-308', '2.2250738585072012e-308',
                             '2.2250738585072013e-308', '2.2250738585072014e-308',
                             '0x1.fffffffffffffp-1023', '0x1.fffffffffffff8p-1023', '0x1p-1022',
                             '0x1p-1030']))
    else:
        hexa = k < 0.45
        if hexa:
            p.append(rng.choice(['0x', '0X', '0x', 'x', '0', '00x']))
        digits = '0123456789abcdefABCDEF' if hexa else '0123456789'
        m = random_digits(rng, digits)
        if rng.random() < 0.5:
            m += '.' + random_digits(rng, digits, (0, 0, 1, 2))
        p.append(m)
        if rng.random() < 0.5:
            e = rng.choice('pPeE' if hexa else 'eEpP')
            if rng.random() < 0.4:
                e += rng.choice('+-')
            e += random_digits(rng, '0123456789', (0, 1, 1, 2, 3))
            p.append(e)
    if rng.random() < 0.15:
        p.append(rng.choice(['x', '.', 'e', ' 1', '\t', '5', 'f', 'L', '+', 'p1']))
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE))
    return ''.join(p)


def random_costs(rng):
    """An argument for -c: one to three NAME=value, at times with a name that is no constant,
    a lower-case one, a missing `=` or value, empty items, and values for strtod."""
    items = []
    for _ in range(rng.choice((1, 1, 2, 3))):
        k = rng.random()
        if k < 0.05:
            items.append(rng.choice(['', 'FOO=1', 'and=1', 'AND', '=1', 'AN=1']))
            continue
        name = rng.choice(COST_NAMES)
        items.append(f'{name}={random_double(rng) if k < 0.6 else rng.choice(["1e6", "1e-6"])}')
    s = ','.join(items)
    if rng.random() < 0.1:
        s += ','
    return s


def random_coefficients(rng):
    """A coefficient list for scan_mpz: 0 to 9 words, valid in half of the cases, separated by one
    or more blanks (spaces and tabs), in the other half at times by other white space, which
    scan_mpz does not skip, or by nothing, and with words that it refuses (a lone sign, two signs,
    a letter or a sign after the digits)."""
    n = rng.choice([0, 1, 2, 5, 6, 6, 7, 7, 7, 8, 9])
    valid = rng.random() < 0.5
    ws = []
    for _ in range(n):
        w = ''
        if rng.random() < 0.3:
            w += rng.choice(['+', '-'] if valid else ['+', '-', '+', '-', '--', '-+'])
        w += random_digits(rng, '0123456789', (1, 1, 2, 3, 25) if valid else (0, 1, 1, 2, 3, 25))
        if not valid and rng.random() < 0.1:
            w += rng.choice(['x', '.5', ',', '-', '+1', 'e2', '_0'])
        ws.append(w)
    seps = [rng.choice([' ', ' ', '  ', ' ', '\t', '\n', '\x0b', ''] if not valid
                       else [' ', ' ', '   ', '\t', ' \t'])
            for _ in range(len(ws) + 1)]
    s = ''.join(seps[i] + ws[i] for i in range(len(ws))) + seps[-1]
    return s if rng.random() < 0.7 else s.strip(' ')


def random_options(rng):
    """One to four options, some unknown, some longer than two characters (which the program
    refuses), most with a random argument."""
    letters = 'nMNpswtcfqa1xyzbdeghk-'
    opts = []
    for _ in range(rng.choice([1, 1, 2, 3, 4])):
        if rng.random() < 0.05:
            opts.append(rng.choice(['', 'q', 'foo', '-']))
            continue
        o = '-' + rng.choice(letters)
        if rng.random() < 0.2:
            o += rng.choice(['x', 'q', 'uiet', 'll', '1', '0'])
        opts.append(o)
        if o[1] in LONG_OPTS and rng.random() < 0.9:
            opts.append(random_long(rng))
        elif o[1] == 'c' and rng.random() < 0.9:
            opts.append(random_costs(rng))
        elif o[1] == 'f' and rng.random() < 0.9:
            opts.append(rng.choice(FORMATS))
    return opts


def random_command_lines(rng):
    """Eight random command lines: a coefficient list at the height 1, a height bound followed by an
    option that fails, the argument of an option that takes a long and of -c, random options, and
    a format, on curves with points at small heights."""
    o = rng.choice(LONG_OPTS)
    return [[random_coefficients(rng), '1', '-q'],
            [random_coefficients(rng), '2'],
            [P, random_long(rng), '-x'],
            [P, '5', '-q', '-' + o, random_long(rng)],
            [P, '5', '-q', '-c', random_costs(rng)],
            [rng.choice([P, Q, R, NEG]), str(rng.randint(1, 5)), *random_options(rng)],
            [rng.choice([P, Q, R, NEG]), str(rng.randint(1, 20)), '-q',
             *rng.choice([[], ['-a']]), '-f', rng.choice(FORMATS)],
            [rng.choice([P, Q, R, NEG, BIG]), str(rng.randint(1, 10)), *random_options(rng),
             *random_options(rng)]]
