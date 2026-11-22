#!/usr/bin/env python3
"""lookup.py NAME [NAME...]: find declarations (by short or full name) in analysis/decls.jsonl."""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
pats = sys.argv[1:]
hits = {p: [] for p in pats}
with open(os.path.join(HERE, 'decls.jsonl')) as fh:
    for line in fh:
        d = json.loads(line)
        for p in pats:
            if d['name'] == p or d['short'] == p or d['name'].endswith('.' + p):
                hits[p].append(d)
for p in pats:
    hs = hits[p]
    print(f'## {p}: {len(hs)} hit(s)')
    for d in hs[:40]:
        print(f"   {d['kind']:8s} {'private ' if d['private'] else ''}{d['name']}  @ {d['mod'].replace('.', '/')}.lean:{d['line']}  [{'leaf' if d['leaf'] else 'internal'}]")
    if len(hs) > 40:
        print(f'   ... {len(hs)-40} more')
