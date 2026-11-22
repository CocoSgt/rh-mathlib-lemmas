#!/usr/bin/env python3
"""Second-level breakdown from analysis/imports.jsonl: files, lines, and cross-import edges
between <Lib>.<Sub> modules. Usage: breakdown.py <Lib> [depth]"""
import json, os, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
recs = [json.loads(l) for l in open(os.path.join(HERE, 'imports.jsonl'))]
TOP = ['BuildAid','CompanionTheory','Development','Formalism','GroundTheory','Lemmata',
       'PositivityTheory','ReciprocityTheory','Supplements','Statements','Main']

def key(mod, depth):
    parts = mod.split('.')
    return '.'.join(parts[:depth])

def main():
    lib = sys.argv[1]
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    files = defaultdict(lambda: [0, 0])
    edges = defaultdict(Counter)
    for r in recs:
        if not r['mod'].startswith(lib + '.'):
            continue
        k = key(r['mod'], depth)
        files[k][0] += 1
        files[k][1] += r['lines']
        for i in r['imports']:
            if i.startswith(lib + '.'):
                ik = key(i, depth)
                if ik != k:
                    edges[k][ik] += 1
    print(f'== {lib} at depth {depth}: {sum(v[0] for v in files.values())} files, {sum(v[1] for v in files.values())} lines')
    for k, (nf, nl) in sorted(files.items(), key=lambda kv: -kv[1][1]):
        outs = ', '.join(f'{b}:{c}' for b, c in edges[k].most_common(6))
        print(f'{k:50s} files={nf:7d} lines={nl:10d}  -> {outs}')

if __name__ == '__main__':
    main()
