#!/usr/bin/env python3
"""Why do the two static proof cones of `Main.riemannHypothesis` differ (662,997 vs 223,420 declarations)?

A = analysis/mainline_graph.py (graph session; its pickles must exist: /tmp/mlg/idx.pkl, /tmp/mlg/graph.pkl,
    produced by `python3 analysis/mainline_graph.py --cache /tmp/mlg/idx.pkl --gcache /tmp/mlg/gcache.pkl --dump /tmp/mlg/graph.pkl`)
B = analysis/mainline_cone.py + depindex.py (strict mode), recomputed here from decls.jsonl / imports.jsonl.

The script reports (see conecheck.txt):
  1. set comparison of the two cones (by declaration name, `_root_.` prefixes normalised);
  2. B's structural blind spots: declarations that decls.jsonl only knows under a `_root_.` name
     (unreachable for B unless the use site also spells `_root_.`), and non-ASCII names (B's tokenizer is ASCII-only)
     -- and how much of A's cone lies below them;
  3. A's structural over-count: edges guessed from short names inside definition bodies (the `Formalism.BasicNotions.D7`
     case) -- cones recomputed without the out-edges of D7 and without edges to targets whose short name has <= 3 characters.
Runtime ~3 min, ~6 GB RAM, no Lean.  Read-only on source/.
"""
import pickle, sys, os, collections, time
PROJ = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
sys.path.insert(0, os.path.join(PROJ, 'analysis'))
OUT = os.path.join(PROJ, 'analysis', 'conecheck.txt')
t0 = time.time()
out = []
def P(*a):
    s = ' '.join(str(x) for x in a); out.append(s); print(s)

class Stub: pass
class Unp(pickle.Unpickler):
    def find_class(self, mod, name):
        if mod == '__main__' and name == 'Index': return Stub
        return super().find_class(mod, name)
idx = Unp(open('/tmp/mlg/idx.pkl', 'rb')).load(); decl = idx.decl; mod_name = idx.mod_name; N = len(decl)
names = [d[3] for d in decl]; short = [d[4] for d in decl]
g = pickle.load(open('/tmp/mlg/graph.pkl', 'rb')); S, P_ = g['stmt'], g['proof']

def closure(roots, allowed=None, block=frozenset(), shortcap=0, state=False):
    seen = set(roots); q = list(roots)
    while q:
        nq = []
        for u in q:
            if u in block: continue
            lst = list(S[u] or [])
            if not state or decl[u][2] not in (0, 1): lst += list(P_[u] or [])
            for d in lst:
                if d in seen or len(short[d]) <= shortcap or (allowed is not None and d not in allowed): continue
                seen.add(d); nq.append(d)
        q = nq
    return seen
norm = lambda n: n[7:] if n.startswith('_root_.') else n

root = g['rootids']['Main.riemannHypothesis'][0]
A = closure([root])
P(f'mainline proof cone of Main.riemannHypothesis -- two static methods compared  (generated {time.strftime("%Y-%m-%d %H:%M")})')
P(f'A (analysis/mainline_graph.py): {len(A):,} declarations (unique names {len({names[d] for d in A}):,}).')

# ---------------- B
dump = '/tmp/conecheck/B_rh.tsv'          # "idx<TAB>name<TAB>module<TAB>kind" per declaration of B's RH cone
if os.path.exists(dump):
    Bn = {norm(l.split('\t')[1]) for l in open(dump)}; lenB = len(Bn)
else:                                    # ~13 min: recompute B's cone from scratch
    from depindex import Index
    ix = Index(verbose=False); bd = ix.decls
    i = [i for i in ix.by_full.get('riemannHypothesis', []) if bd[i]['mod'] == 'Main'][0]
    B = ix.closure(i, ix.follow_prove, loose=False, minlen=1)
    Bn = {norm(bd[j]['name']) for j in B}; lenB = len(B)
An = {names[d] for d in A}
P(f'B (analysis/mainline_cone.py, strict): {lenB:,} declarations (unique names {len(Bn):,}).')
P(f'intersection {len(An & Bn):,}; A only {len(An - Bn):,}; B only {len(Bn - An):,}  ({100*len(An&Bn)/len(Bn):.1f}% of B lies inside A, {100*len(An&Bn)/len(An):.1f}% of A lies inside B).')

# ---------------- B's blind spots
rawB = set()
with open(os.path.join(PROJ, 'analysis', 'decls.jsonl')) as fh:
    for l in fh:
        k = l.find('"name": "')
        if k >= 0: rawB.add(l[k+9:l.find('"', k+9)])
R = {d for d in A if ('_root_.' + names[d]) in rawB and names[d] not in rawB}
NA = {d for d in A if not names[d].isascii()}
# B's per-root numbers: parse the summary written by analysis/mainline_cone.py (mode=strict)
Btxt = {}
for l in open(os.path.join(PROJ, 'analysis', 'mainline_cone.txt')):
    m = __import__('re').match(r'^\S+\s{2,}(\S+)\s+\d+\s+\d+\s+\d+\s+\(\s*\d+\)\s+(\d+)\s+\d+', l)
    if m: Btxt[m.group(1)] = f'{int(m.group(2)):,}'
P('')
P("1. B's structural blind spots (declarations that B cannot reach by construction):")
P(f'   decls.jsonl records {sum(1 for n in rawB if n.startswith("_root_.")):,} declarations ONLY under a name starting with `_root_.`;')
P(f'   depindex looks a plain reference `X.Y.z` up by that plain name, so every reference to such a declaration is dropped')
P(f'   (example: `theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound` …/NormPrimesImagQuadShortIntervalLowerBound.lean:8,')
P(f'    used as `GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound` in ShortNorms/Primes.lean:5 -- on the main line via supplyChi).')
P(f'   A-cone declarations of this kind: {len(R):,}; none of them is in B ({len(Bn & {norm(names[d]) for d in R})}).')
P(f'   Part of A reachable from them: {len(closure(R, allowed=A)):,} ({100*len(closure(R, allowed=A))/len(A):.1f}% of A).')
P(f'   A-cone declarations with a non-ASCII character in the name (B tokenises ASCII only): {len(NA):,}; reachable from them: {len(closure(NA, allowed=A)):,}.')
P(f'   B also drops every ambiguous short name (strict mode).')

# ---------------- A's over-count
D7 = [d for d in range(N) if names[d] == 'Formalism.BasicNotions.D7'][0]
P('')
P("2. A's structural over-count (edges guessed from short names / field names inside definition bodies):")
P(f'   `Formalism.BasicNotions.D7` (a 262-line structure) has {len(S[D7] or [])} outgoing statement edges in A, e.g. to')
P('   `Ad3.R.Om`, `UpperTheory.V.HV.Host.q`, `ChowFormHeightComparison₂.CF.C.loc`, `UpperTheory.V.Af.Fin.emb`, `Formalism.SA.A.LL` -- these are its')
P('   *field names* (Om, K, q, loc, emb, LL …), not references.  Green/HostExW/TopG/FamP … all mention D7, so a ~32,000-declaration')
P('   false subtree hangs under every non-glue layer.')
P('   Compiler ground truth for statement cones (these files compile in skeleton/ with Mathlib only): Green = 16 declarations,')
P('   VWin = 32 (+ Galois files), ZeroFreeAll = 4.')
P('')
P('   cone                          A        A minus D7-out-edges   A minus targets with <=3-char names      B')
rows = [('Main.riemannHypothesis', 'RH (whole main line)'), ('T.gal_row0b', '=> Row0b (Galois reps)'), ('T.recTExists', 'recTExists (local Langlands)'),
        ('T.vwin_of_row', 'vwin_of_row (=> VWin)'), ('T.green_of_regular', 'green_of_regular (Green)'), ('T.nonempty_hyps_DS', 'HypsAlt nonempty (analytic core)'),
        ('T.zero_free_green_vwin', 'zero_free_all_of_green_v_win'), ('T.every_char_lit_vWin', 'every_char_lit_vWin (literature pkg)'),
        ('T.supplyChi', 'supplyChi'), ('T.zeroFreeAll_of_topG', 'zeroFreeAll_of_topG'), ('T.imprimitive', 'imprimitive')]
Blab = {'=> Row0b (Galois reps)': 'galoisRepresentations_of_thetaLift', 'recTExists (local Langlands)': 'UpperTheory.Zero.LLC.recTExists', 'vwin_of_row (=> VWin)': 'UpperTheory.One.vwin_of_row',
        'HypsAlt nonempty (analytic core)': 'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound', 'zero_free_all_of_green_v_win': 'UpperTheory.Top.zero_free_all_of_green_v_win',
        'every_char_lit_vWin (literature pkg)': 'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin', 'supplyChi': 'UpperTheory.Top.supplyChi', 'zeroFreeAll_of_topG': 'UpperTheory.Top.zeroFreeAll_of_topG',
        'imprimitive': 'UpperTheory.Top.imprimitive', 'green_of_regular (Green)': 'GlobalTheory.GreenBridge.green_of_regular'}
P(f'   {"whole main line":28s} {len(A):>9,} {len(closure([root], block=frozenset([D7]))):>24,} {len(closure([root], shortcap=3)):>38,} {lenB:>9,}')
for key, lab in rows[1:]:
    r = g['rootids'][key][0]; a = len(closure([r])); b = len(closure([r], block=frozenset([D7]))); c = len(closure([r], shortcap=3))
    P(f'   {lab:28s} {a:>9,} {b:>24,} {c:>38,} {Btxt.get(Blab.get(lab, ''), "(n/a)"):>9s}')
P('   statement cones:')
for key, lab in [('P.Green', 'Green'), ('P.VWin', 'VWin'), ('P.ZeroFreeAll', 'ZeroFreeAll'), ('P.TopG', 'TopG'), ('P.HypsAlt', 'HypsAlt'), ('P.RecTExists', 'RecTExists'), ('P.Row0b', 'Row0b')]:
    r = g['rootids'][key][0]
    P(f'   {lab:28s} {len(closure([r], state=True)):>9,} {len(closure([r], state=True, block=frozenset([D7]))):>24,} {len(closure([r], state=True, shortcap=3)):>38,}')
P('   (the "<=3-char names" column also removes genuine short names such as `Sp`, `ev`, `KK`, so it under-counts; it is a sensitivity bound, not an estimate.)')
P('')
P('3. Manual samples (scripts not kept; seeds noted): 70 random declarations of A-only, seed 7 and 11 -- all 70 had an incoming edge whose')
P('   referenced name really occurs in the referencing declaration (e.g. `have h := genHasVal_powGen …`, `rw [hcol, comb_mul]`).')
P('   45 random edges of A (seed 3): about 39-42 clearly genuine, 3 references through section variables, 2-4 doubtful (`ea.symm` -> `…Pull.Tri.symm`).')
P(f'done in {time.time()-t0:.0f}s')
with open(OUT, 'w') as fh: fh.write('\n'.join(out) + '\n')
