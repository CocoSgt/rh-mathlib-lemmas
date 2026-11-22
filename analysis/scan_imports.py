#!/usr/bin/env python3
"""Scan every .lean file under source/src: path, line count, imports.
Output: analysis/imports.jsonl (one record per file) plus analysis/summary.txt
Read-only on source/. Internal = module name starting with one of the repo's own roots.
"""
import json, os, re, sys, time
from collections import Counter, defaultdict

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'source', 'src')
ROOT = os.path.normpath(ROOT)
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'imports.jsonl')

TOP = ['BuildAid','CompanionTheory','Development','Formalism','GroundTheory','Lemmata',
       'PositivityTheory','ReciprocityTheory','Supplements','Statements','Main']

imp_re = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)')

def modname(path):
    rel = os.path.relpath(path, ROOT)
    return rel[:-5].replace(os.sep, '.')

records = []
t0 = time.time()
nfiles = 0
for dp, dn, fn in os.walk(ROOT):
    for f in fn:
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        imps = []
        nlines = 0
        with open(p, 'r', encoding='utf-8', errors='replace') as fh:
            for line in fh:
                nlines += 1
                m = imp_re.match(line)
                if m:
                    imps.append(m.group(1))
        mod = modname(p)
        records.append({'mod': mod, 'lines': nlines, 'imports': imps})
        nfiles += 1
print(f'scanned {nfiles} files in {time.time()-t0:.1f}s', file=sys.stderr)

with open(OUT, 'w') as fh:
    for r in records:
        fh.write(json.dumps(r) + '\n')

# ---- summary ----
def top_of(mod):
    return mod.split('.')[0]

by_top = defaultdict(lambda: [0, 0])          # files, lines
by_top_imports = defaultdict(Counter)         # top -> Counter(imported top)
mathlib_importers = Counter()
no_internal = Counter()
total_lines = 0
for r in records:
    t = top_of(r['mod'])
    by_top[t][0] += 1
    by_top[t][1] += r['lines']
    total_lines += r['lines']
    internal = [i for i in r['imports'] if top_of(i) in TOP]
    for i in r['imports']:
        by_top_imports[t][top_of(i)] += 1
    if any(top_of(i) == 'Mathlib' or top_of(i) in ('Batteries','Aesop','Qq','ProofWidgets','Lean','Std','Init') for i in r['imports']):
        mathlib_importers[t] += 1
    if not internal:
        no_internal[t] += 1

lines = []
lines.append(f'total files {len(records)}  total lines {total_lines}')
lines.append('')
lines.append('top-level lib | files | lines | files importing Mathlib/others | files with NO internal imports (leaf files)')
for t in TOP:
    if t in by_top:
        lines.append(f'{t} | {by_top[t][0]} | {by_top[t][1]} | {mathlib_importers[t]} | {no_internal[t]}')
lines.append('')
lines.append('import edges between top-level libs (row imports column): count of import statements')
for t in TOP:
    if t in by_top:
        row = by_top_imports[t]
        lines.append(f'{t} -> ' + ', '.join(f'{k}:{v}' for k, v in row.most_common() if k != t))
        lines.append(f'   (self-imports within {t}: {row.get(t,0)})')
with open(os.path.join(os.path.dirname(OUT), 'summary.txt'), 'w') as fh:
    fh.write('\n'.join(lines) + '\n')
print('\n'.join(lines))
