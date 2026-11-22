#!/usr/bin/env python3
"""Index every declaration in source/src: kind, full name, file, line, plus file-level info
(namespace, opens, whether the file imports internal modules, whether it is a leaf).
Output: analysis/decls.jsonl ; analysis/leaf_files.json
"""
import json, os, re, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', 'source', 'src'))
TOP = ['BuildAid','CompanionTheory','Development','Formalism','GroundTheory','Lemmata',
       'PositivityTheory','ReciprocityTheory','Supplements','Statements','Main']

decl_re = re.compile(r'^(\s*)(?:@\[[^\]]*\]\s*)?(?:(private|protected|noncomputable|unsafe|partial)\s+)*'
                     r'(theorem|lemma|def|structure|class|abbrev|instance|inductive|opaque|axiom)\s+'
                     r'([A-Za-z_][A-Za-z0-9_.\'!]*)')
ns_re = re.compile(r'^\s*(?:private\s+)?namespace\s+([A-Za-z0-9_.]+)')
end_re = re.compile(r'^\s*end\b\s*([A-Za-z0-9_.]*)')
open_re = re.compile(r'^\s*open\s+(?:scoped\s+)?(.*)$')
import_re = re.compile(r'^\s*import\s+([A-Za-z0-9_.]+)')

def modname(path):
    return os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')

def is_internal(mod):
    return mod.split('.')[0] in TOP

t0 = time.time()
decls = []
leaf = {}
nfiles = 0
for dp, dn, fn in os.walk(ROOT):
    for f in fn:
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        mod = modname(p)
        ns = []
        opens = []
        imports = []
        file_decls = []
        with open(p, 'r', encoding='utf-8', errors='replace') as fh:
            for ln, line in enumerate(fh, 1):
                m = import_re.match(line)
                if m:
                    imports.append(m.group(1)); continue
                m = ns_re.match(line)
                if m:
                    ns.append(m.group(1)); continue
                m = end_re.match(line)
                if m and m.group(1):
                    if ns and (ns[-1] == m.group(1) or ns[-1].split('.')[-1] == m.group(1).split('.')[-1]):
                        ns.pop()
                    continue
                m = open_re.match(line)
                if m:
                    opens.append(m.group(1).strip()); continue
                m = decl_re.match(line)
                if m:
                    kind = m.group(3); name = m.group(4)
                    mods = line[:m.start(3)]
                    full = '.'.join(ns + [name]) if ns else name
                    file_decls.append({'kind': kind, 'name': full, 'short': name, 'line': ln,
                                       'private': 'private' in mods, 'ns': '.'.join(ns)})
        internal = any(is_internal(i) for i in imports)
        leaf[mod] = {'lines': None, 'internal_imports': len([i for i in imports if is_internal(i)]),
                     'imports': imports, 'ns': ns, 'opens': opens}
        for d in file_decls:
            d['mod'] = mod
            d['leaf'] = not internal
            decls.append(d)
        nfiles += 1
print(f'{nfiles} files, {len(decls)} decls in {time.time()-t0:.1f}s', file=sys.stderr)

with open(os.path.join(HERE, 'decls.jsonl'), 'w') as fh:
    for d in decls:
        fh.write(json.dumps(d) + '\n')
json.dump(leaf, open(os.path.join(HERE, 'leaf_files.json'), 'w'))

from collections import Counter
c = Counter(d['kind'] for d in decls)
print('kinds:', c.most_common())
c2 = Counter((d['kind'], d['private']) for d in decls if d['leaf'])
print('leaf decls by (kind, private):', c2.most_common())
c3 = Counter(d['mod'].split('.')[0] + '.' + (d['mod'].split('.')[1] if '.' in d['mod'] else '')
             for d in decls if d['leaf'] and d['kind'] in ('theorem','lemma') and not d['private'])
print('non-private theorems in leaf files, per Lib.Sub (top 60):')
for k, v in c3.most_common(60):
    print(f'  {k}: {v}')
