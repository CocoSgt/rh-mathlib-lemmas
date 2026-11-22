#!/usr/bin/env python3
"""Transitive import closure of a module (default Main), summarised per top-level and
depth-2 module. Usage: closure.py [Module] [depth]"""
import json, os, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
recs = {r['mod']: r for r in (json.loads(l) for l in open(os.path.join(HERE, 'imports.jsonl')))}
TOP = ['BuildAid','CompanionTheory','Development','Formalism','GroundTheory','Lemmata',
       'PositivityTheory','ReciprocityTheory','Supplements','Statements','Main']

def closure(root):
    seen = set(); stack = [root]
    while stack:
        m = stack.pop()
        if m in seen or m not in recs: continue
        seen.add(m)
        stack.extend(recs[m]['imports'])
    return seen

def main():
    root = sys.argv[1] if len(sys.argv) > 1 else 'Main'
    depth = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    seen = closure(root)
    files = [recs[m] for m in seen]
    tot_lines = sum(r['lines'] for r in files)
    print(f'closure of {root}: {len(files)} files, {tot_lines} lines')
    by = defaultdict(lambda: [0, 0])
    for r in files:
        k = '.'.join(r['mod'].split('.')[:depth])
        by[k][0] += 1; by[k][1] += r['lines']
    for k, (nf, nl) in sorted(by.items(), key=lambda kv: -kv[1][1]):
        print(f'{k:55s} files={nf:7d} lines={nl:10d}')
    # per top-level
    print('-- per top-level --')
    bt = defaultdict(lambda: [0,0])
    for r in files:
        t = r['mod'].split('.')[0]; bt[t][0]+=1; bt[t][1]+=r['lines']
    for k,(nf,nl) in sorted(bt.items(), key=lambda kv:-kv[1][1]):
        print(f'{k:25s} files={nf:7d} lines={nl:10d}')
    json.dump(sorted(seen), open(os.path.join(HERE, f'closure_{root.replace(".", "_")}.json'), 'w'))

if __name__ == '__main__':
    main()
