#!/usr/bin/env python3
"""Dump clean leaf theorems (non-private by default) for a module prefix.
Usage: dump_leaf.py <prefix> [--all] [--max N] [--private] [--min-len N] [--grep REGEX]
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
rows = [json.loads(l) for l in open(os.path.join(HERE, 'leaf_theorems.jsonl'))]
args = sys.argv[1:]
prefix = args[0] if args and not args[0].startswith('--') else ''
show_private = '--private' in args
mx = 400
if '--max' in args: mx = int(args[args.index('--max') + 1])
pat = None
if '--grep' in args: pat = re.compile(args[args.index('--grep') + 1])
sel = [r for r in rows if r['mod'].startswith(prefix) and not r['uses_local_def']
       and (show_private or not r['private'])]
if pat:
    sel = [r for r in sel if pat.search(r['stmt'])]
sel.sort(key=lambda r: (r['mod'], r['line']))
for r in sel[:mx]:
    s = r['stmt']
    # strip universe/explicit noise a bit for readability
    print(f"### {r['mod']}:{r['line']}  {r['name']}{'  [private]' if r['private'] else ''}")
    print(s[:1500])
    print()
print(f'-- {len(sel)} shown of {len(sel)} (prefix={prefix!r}, private={show_private})', file=sys.stderr)
