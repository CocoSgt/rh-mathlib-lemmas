#!/usr/bin/env python3
"""For every theorem/lemma in a *leaf* file (no internal imports) extract the statement text and
flag whether it mentions a def/structure/abbrev/instance declared in the same file (which would
make it project-specific). Output: analysis/leaf_theorems.jsonl"""
import json, os, re, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', 'source', 'src'))
decls = [json.loads(l) for l in open(os.path.join(HERE, 'decls.jsonl'))]
by_mod = {}
for d in decls:
    if d['leaf']:
        by_mod.setdefault(d['mod'], []).append(d)

out = []
t0 = time.time()
for mod, ds in by_mod.items():
    path = os.path.join(ROOT, mod.replace('.', os.sep) + '.lean')
    try:
        lines = open(path, encoding='utf-8', errors='replace').read().split('\n')
    except FileNotFoundError:
        continue
    local_defs = [d['short'] for d in ds if d['kind'] in ('def','structure','abbrev','instance','inductive','class','opaque')]
    local_thms = {d['short'] for d in ds if d['kind'] in ('theorem','lemma')}
    for d in ds:
        if d['kind'] not in ('theorem', 'lemma'):
            continue
        i = d['line'] - 1
        stmt = []
        depth = 0
        for j in range(i, min(i + 40, len(lines))):
            L = lines[j]
            # stop at ':=' at bracket depth 0 (approx) or 'where'
            k = 0
            stop = False
            while k < len(L):
                ch = L[k]
                if ch in '([{': depth += 1
                elif ch in ')]}': depth -= 1
                elif L.startswith(':=', k) and depth <= 0:
                    stop = True; break
                k += 1
            if stop:
                stmt.append(L[:k])
                break
            stmt.append(L)
            if j > i and re.match(r'^\s*where\s*$', L):
                break
        text = ' '.join(s.strip() for s in stmt if s.strip())
        text = re.sub(r'\s+', ' ', text)
        words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", text))
        uses_local = sorted(w for w in words if w in local_defs)
        uses_local_thm = sorted(w for w in words if w in local_thms and w != d['short'])
        out.append({'mod': mod, 'line': d['line'], 'name': d['name'], 'private': d['private'],
                    'stmt': text, 'uses_local_def': uses_local, 'uses_local_thm': uses_local_thm,
                    'n_local_defs_in_file': len(local_defs), 'file_lines': len(lines)})
print(f'{len(out)} leaf theorems in {time.time()-t0:.1f}s', file=sys.stderr)
with open(os.path.join(HERE, 'leaf_theorems.jsonl'), 'w') as fh:
    for r in out:
        fh.write(json.dumps(r) + '\n')
clean = [r for r in out if not r['uses_local_def']]
print('clean (no same-file def referenced):', len(clean), ' non-private:', sum(1 for r in clean if not r['private']))
