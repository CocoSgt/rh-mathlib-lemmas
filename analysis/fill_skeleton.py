#!/usr/bin/env python3
"""Fill the {{PLACEHOLDERS}} of SKELETON.md from analysis/mainline_cone.txt (and the draft sizes
reported by analysis/extract_cone.py).  Run after mainline_cone.py."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..'))
txt = open(os.path.join(ROOT, 'analysis', 'mainline_cone.txt')).read()
md_path = os.path.join(ROOT, 'SKELETON.md')
md = open(md_path).read()

def cone(name, which):
    # tag  name  state decls files filelines (decllines)   prove decls files filelines (decllines)
    for line in txt.splitlines():
        m = re.match(r'(\S+)\s+(\S+)\s+(\d+)\s+(\d+)\s+(\d+)\s+\(\s*(\d+)\)\s+(\d+)\s+(\d+)\s+(\d+)\s+\(\s*(\d+)\)', line)
        if m and m.group(2) == name:
            g = m.groups()
            return (int(g[2]), int(g[3]), int(g[4]), int(g[5])) if which == 'state' else (int(g[6]), int(g[7]), int(g[8]), int(g[9]))
    raise SystemExit(f'no line for {name}')

def fmt(n):
    return f'{n:,}'

V = {}
for key, name in [('GAL', 'UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift'), ('RH', 'riemannHypothesis'),
                  ('VWIN', 'UpperTheory.One.vwin_of_row'),
                  ('LIT', 'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin'),
                  ('RECT', 'UpperTheory.Zero.LLC.recTExists'), ('PLUG', 'UpperTheory.Top.plugWin'),
                  ('ZFOG', 'UpperTheory.Top.zeroFreeAll_of_topG'), ('ECR', 'UpperTheory.FinalTheorems.everyCharacter_of_row'),
                  ('GREEN', 'GlobalTheory.GLq.Green'), ('VWINS', 'UpperTheory.Top.VWin'), ('ROW0B', 'UpperTheory.GalStar.Row0b'),
                  ('ISRECT', 'UpperTheory.Zero.LLC.IsRecT'), ('HYPS', 'GlobalTheory.Fc.Hyps'), ('HYPSA', 'GlobalTheory.Fc.HypsAlt'),
                  ('AWI', 'UpperTheory.One.Join.automorphic_window_of_inputs')]:
    st, pr = cone(name, 'state'), cone(name, 'prove')
    V[key + '_STATE'], V[key + '_SFILES'], V[key + '_SLINES'] = st[0], st[1], st[3]
    V[key + '_PROVE'], V[key + '_FILES'], V[key + '_LINES'] = pr[0], pr[1], pr[3]
V['GAL_PCT'] = f"{100 * V['GAL_PROVE'] / V['RH_PROVE']:.0f}"
V['SHARING'] = ''
m = re.search(r'pairwise sharing of cones.*?(?=\nhub files)', txt, re.S)
if m:
    block = m.group(0).strip().splitlines()
    rows = []
    for l in block[1:]:
        mm = re.match(r'\s+(.+?)\s+∩\s+(.+?)\s+(\d+)\s+/\s+(\d+)\s+/\s+(\d+)\s+J=([\d.]+)\s+\(\s*([\d.]+)% of the second\)', l)
        if mm:
            rows.append(f'| `{mm.group(1).strip()}` | `{mm.group(2).strip()}` | {int(mm.group(3)):,} | {int(mm.group(4)):,} | {int(mm.group(5)):,} | {mm.group(6)} |')
    if rows:
        V['SHARING'] = ('**共享情况**（层陈述锥之间、以及几条大证明锥之间的交集；完整矩阵见 `mainline_cone.txt`）：\n\n'
                        '| A | B | A∩B | A | B | Jaccard |\n|---|---|---:|---:|---:|---:|\n' + '\n'.join(rows))
V['ROW0B_DRAFT'] = '约 300–370'
V['ISRECT_DRAFT'] = '约 70–85'
V['NMOD'] = 'NMOD_PLACEHOLDER'
V['BUILD'] = 'BUILD_PLACEHOLDER'
left = sorted(set(re.findall(r'\{\{([A-Z0-9_]+)\}\}', md)))
missing = [k for k in left if k not in V]
if missing:
    raise SystemExit(f'missing values for {missing}')
for k in left:
    val = V[k]
    md = md.replace('{{' + k + '}}', fmt(val) if isinstance(val, int) else val)
open(md_path, 'w').write(md)
print('filled', len(left), 'placeholders; SHARING rows:', V['SHARING'].count('\n| `') if V['SHARING'] else 0)
for k in sorted(V):
    if isinstance(V[k], int):
        print(f'  {k} = {V[k]:,}')
