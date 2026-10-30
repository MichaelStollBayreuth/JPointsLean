#!/usr/bin/env python3
"""Checks the layering of the Lean sources (README.md, Layout) and the restrictions on the model.

usage: scripts/check_layout.py

Prints `FAIL <rule> <file>:<line>: <text>` for every violation and exits 1 if there is one.

- Imports. The model (`JPoints/Model`) imports only Lean core and `Std`; the specification
  (`JPoints/Spec`) only Mathlib, so that it can be read without the model; the candidates for
  Mathlib (`JPoints/Mathlib`) only Mathlib and its dependencies; `comparator/Challenge.lean` only
  Mathlib and the model (it restates the specification); the root of the executable
  (`ModelMain.lean`) only the model.
- Roots. The part roots `JPoints/Model.lean`, `JPoints/Spec.lean` and `JPoints/Proof.lean` import,
  directly or not, every module of their folder, so that `lake build JPointsModel` builds the
  whole model and `scripts/Correspondence.lean` sees every declaration of it.
- The model is plain executable code that the proofs are about: no experimental options, and no
  `partial`, `unsafe`, `implemented_by` or `extern`, which would let the executable run code that
  the proofs do not see.
- Axioms: no `native_decide`, `decide +native`, `bv_decide`, `bv_check` or `ofReduceBool`
  anywhere, since each adds an axiom that comparator rejects.

Comments and docstrings are not checked.

Adapted from scripts/check_layout.py of RatpointsLean
(https://github.com/MichaelStollBayreuth/RatpointsLean).
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from style_lint import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)')

# Allowed import prefixes per part: a module `M` may be imported if `M` is one of the prefixes or
# starts with one of them followed by a dot.
ALLOWED = {
    'model': ['Init', 'Std', 'JPoints.Model'],
    'spec': ['Init', 'Std', 'Mathlib', 'JPoints.Spec'],
    'mathlib': ['Init', 'Std', 'Lean', 'Batteries', 'Qq', 'Aesop', 'Mathlib', 'JPoints.Mathlib'],
    'challenge': ['Init', 'Std', 'Mathlib', 'JPoints.Model'],
    'main': ['Init', 'Std', 'JPoints.Model'],
}
EXECUTABLE_ROOTS = ('ModelMain.lean', 'BruteMain.lean')
FORBIDDEN_EVERYWHERE = [
    ('axiom', r'\bnative_decide\b|\bdecide\s*\+native\b|\bbv_decide\b|\bbv_check\b|ofReduceBool'),
]
FORBIDDEN_IN_MODEL = [
    ('experimental', r'\bset_option\s+experimental\.'),
    ('partial', r'\bpartial\s+def\b'),
    ('unsafe', r'\bunsafe\b'),
    ('implemented_by', r'\bimplemented_by\b'),
    ('extern', r'@\[\s*extern\b|\bextern\s+"'),
]


def module_of(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def part_of(path):
    rel = path.relative_to(ROOT).as_posix()
    if rel == 'JPoints/Model.lean' or rel.startswith('JPoints/Model/'):
        return 'model'
    if rel == 'JPoints/Spec.lean' or rel.startswith('JPoints/Spec/'):
        return 'spec'
    if rel.startswith('JPoints/Mathlib/'):
        return 'mathlib'
    if rel == 'comparator/Challenge.lean':
        return 'challenge'
    if rel in EXECUTABLE_ROOTS:
        return 'main'
    return None


def allowed(mod, prefixes):
    return any(mod == p or mod.startswith(p + '.') for p in prefixes)


def main():
    files = sorted([*ROOT.glob('JPoints/**/*.lean'), *ROOT.glob('comparator/*.lean')])
    files += [p for p in (ROOT / 'JPoints.lean', *(ROOT / r for r in EXECUTABLE_ROOTS))
              if p.exists()]
    fails = []

    def fail(rule, path, i, text):
        fails.append(f'FAIL {rule} {path.relative_to(ROOT)}:{i + 1}: {text.strip()}')

    imports = {}
    for path in files:
        raw = path.read_text(encoding='utf-8').split('\n')
        code = strip_comments(raw)
        part = part_of(path)
        imports[module_of(path)] = []
        for i, line in enumerate(code):
            m = IMPORT.match(line)
            if m:
                imports[module_of(path)].append(m.group(1))
                if part and not allowed(m.group(1), ALLOWED[part]):
                    fail(f'import-{part}', path, i, raw[i])
            rules = FORBIDDEN_EVERYWHERE
            if part == 'model':
                rules = rules + FORBIDDEN_IN_MODEL
            for rule, pat in rules:
                if re.search(pat, line):
                    fail(rule, path, i, raw[i])
    for root in ('JPoints.Model', 'JPoints.Spec', 'JPoints.Proof'):
        seen, todo = set(), [root]
        while todo:
            mod = todo.pop()
            if mod not in seen:
                seen.add(mod)
                todo += [m for m in imports.get(mod, []) if m in imports]
        path = ROOT / (root.replace('.', '/') + '.lean')
        for mod in sorted(m for m in imports if m.startswith(root + '.') and m not in seen):
            fail('root', path, 0, f'{root} does not import {mod}')
    print('\n'.join(fails))
    print(f'layout: {len(fails)} fails in {len(files)} files')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
