#!/usr/bin/env python3
"""Static dependency graph of the mainline theorems (TASK.md step 6, "静态依赖图").

No compilation. For every mainline declaration we take its source text (line numbers from
`decls.jsonl`; source/ is only read), tokenise identifiers, resolve them against the index of
all 1,054,991 project declarations (namespace stack + `open` aware) and take the transitive
closure. Tokens that resolve to nothing are Mathlib/Lean names or bound variables.

For every root two cones are computed:
  * "state": what is needed to *state* the declaration in a Mathlib-only file
             (theorems contribute only their statement; defs/structures their whole text).
  * "prove": what is needed to *prove* it (full text of everything, transitively).

Resolution modes (`--loose`): strict = exact full names and unambiguous visible short names;
loose = additionally every visible candidate of an ambiguous short name. A declaration is visible only if its module is in the (transitive) import closure of the
using file, its namespace is open / an ancestor, or it is a root name; `x.member` tokens are resolved through the
declared type of `x` when it is a binder in the same declaration.

Outputs (analysis/mainline_cone.*):  [companion to the graph session's mainline_graph.*]
  .txt  summary: per root decls/files/lines for both cones, per-layer unions, Hyps used
  .tsv  one row per (root, cone, reachable declaration)
  .dot  Graphviz edges (direct references of the mainline declarations)
  .mmd  Mermaid graph of the mainline (also copied into SKELETON.md)
"""
import json, os, re, sys, time
from collections import defaultdict, Counter, deque

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, '..', 'source', 'src'))
LOOSE = '--loose' in sys.argv
OUT = os.path.join(HERE, 'mainline_cone' + ('_loose' if LOOSE else ''))

# (module, full name, tag).  tag: L1..L5 = layer conclusion; G = glue theorem; S = sub-input
ROOTS = [
    ('Main', 'riemannHypothesis', 'L5'),
    ('Statements', 'RiemannZetaZerosOnLine', 'L5'),
    ('Statements', 'DirichletLNonvanishingRightOfHalf', 'L4'),
    ('Statements', 'DirichletLZerosOnLine', 'L5'),
    ('Statements', 'PrimitiveDirichletLZerosOnLine', 'L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane', 'Claim.HalfPlane', 'L4'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane', 'Claim.Strip', 'L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane', 'Claim.Zeta', 'L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter', 'UpperTheory.EveryCharacter', 'L4'),
    ('Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions', 'Formalism.HC.ZeroFreeAll', 'L3'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.VWin', 'L2'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.VWinAt', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.WinPair', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.VAt', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.VVle', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.IsChiField', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN', 'UpperTheory.Top.PageN', 'S'),
    ('Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum', 'GlobalTheory.GLq.Green', 'L2'),
    ('Formalism.SharpRestriction.GlobalTheoremInputs', 'Formalism.MainNotions.LinkN', 'S'),
    ('Formalism.SharpRestriction.ParamsHeightRankConstant', 'Formalism.MainNotions.Closed', 'S'),
    ('Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DRS', 'GlobalTheory.Fc.DRS', 'S'),
    ('Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw', 'GlobalTheory.Fc.Hyps', 'S'),
    ('Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis', 'UpperTheory.GalStar.Row0b', 'L1'),
    ('Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec', 'UpperTheory.Zero.LLC.IsRecT', 'L1'),
    ('Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec', 'UpperTheory.Zero.LLC.RecTExists', 'L1'),
    # glue theorems, top-down
    ('Supplements.Kernels.MainTheorems', 'rhOfAll', 'G'),
    ('Supplements.Kernels.MainTheorems', 'allChi', 'G'),
    ('Supplements.Kernels.MainTheorems', 'critAll', 'G'),
    ('Supplements.Kernels.MainTheorems', 'claimAll', 'G'),
    ('Formalism.GammaFactorNonvanishing.RhOfRight', 'Formalism.VW.rh_of_right', 'G:L4>L5'),
    ('Formalism.GammaFactorNonvanishing.CritLine', 'Formalism.VW.rh_of_every', 'G:L4>L5'),
    ('Formalism.GammaFactorNonvanishing.CritLine', 'Formalism.VW.critLine', 'G:L4>L5'),
    ('Formalism.GammaFactorNonvanishing.CritLine', 'Formalism.VW.gammaFactor_ne_zero', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter', 'UpperTheory.riemannHypothesis_of_everyCharacter', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.strip', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.zeta', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.zeta_iff', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.prim_zero', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.prim_reflect', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.factor_ne_zero', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip', 'Claim.gamma_ne_zero', 'G:L4>L5'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive', 'UpperTheory.Top.imprimitive', 'G:L3>L4'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter', 'UpperTheory.Top.plugWin', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter', 'UpperTheory.Top.plugAll', 'G:L2>L4'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG', 'UpperTheory.Top.zeroFreeAll_of_topG', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG', 'UpperTheory.Top.TopG', 'S'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.ShapeWin', 'UpperTheory.Top.shapeWin', 'G:L2>L3'),
    ('Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ShapeOf', 'GlobalTheory.Fc.shape_of', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion', 'UpperTheory.FinalTheorems.everyCharacter', 'G:L2>L4'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion', 'UpperTheory.FinalTheorems.everyCharacter_of_row', 'G:L1>L4'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin', 'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin', 'G:L1>L4'),
    # the route actually used by Main.lean inside every_character_of_literature_of_vWin (TopPlug.lean, HypsAlt version)
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses', 'UpperTheory.Lit.every_character_of_theta_integrals_local_matching', 'G:L2>L4'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SiegelEisensteinSecondTermHypotheses', 'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound', 'G:L2'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug', 'UpperTheory.Top.every_character_of_green_v_win', 'G:L2>L4'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug', 'UpperTheory.Top.zero_free_all_of_green_v_win', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps', 'GlobalTheory.Fc.HypsAlt', 'S'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition', 'GlobalTheory.Fc.DefiniteSideCondition', 'S'),
    ('Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf', 'UpperTheory.Top.shape_closed_link_n_of_green', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi', 'UpperTheory.Top.supplyChi', 'G:L2>L3'),
    ('Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow', 'UpperTheory.One.vwin_of_row', 'G:L1>L2'),
    ('Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TopMainZj', 'UpperTheory.One.Join.automorphic_window_of_inputs', 'G:L1>L2'),
    ('Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists', 'UpperTheory.Zero.LLC.recTExists', 'G:L1'),
    ('Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc', 'galoisLocalGlobalStrong_recParameter', 'G:L1'),
    ('Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GaloisRepresentationsOfThetaLift', 'UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift', 'G:L1'),
    ('Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TLiftK', 'UpperTheory.TP.K.tLiftK', 'G:L1'),
]
LAYERS = {
    'L1 Row0b (with IsRecT)': ['UpperTheory.GalStar.Row0b', 'UpperTheory.Zero.LLC.IsRecT'],
    'L2 VWin + Green + HypsAlt': ['UpperTheory.Top.VWin', 'GlobalTheory.GLq.Green', 'Formalism.MainNotions.LinkN',
                                  'GlobalTheory.Fc.DefiniteSideCondition', 'Formalism.MainNotions.Closed', 'GlobalTheory.Fc.HypsAlt'],
    'L2b VWin + Green + Hyps(DRS)': ['UpperTheory.Top.VWin', 'GlobalTheory.GLq.Green', 'Formalism.MainNotions.LinkN',
                                     'GlobalTheory.Fc.DRS', 'Formalism.MainNotions.Closed', 'GlobalTheory.Fc.Hyps'],
    'L3 ZeroFreeAll': ['Formalism.HC.ZeroFreeAll'],
    'L4 EveryCharacter': ['UpperTheory.EveryCharacter'],
    'L5 RiemannHypothesis': ['Main.riemannHypothesis'],
}

t0 = time.time()
sys.path.insert(0, HERE)
from depindex import Index, strip_comments      # shared core (also used by extract_cone.py)

ix = Index(verbose=False)
decls = ix.decls
load_file = ix.load_file
def summarize(seen):
    n, f, fl, dl, kinds, libs = ix.summarize(seen)
    return n, f, fl, dl, Counter(kinds), Counter(libs)
MINLEN = 1   # identifiers of length >= 1 are resolved (bound variables are filtered by the import-closure visibility rule)
def refs(i, part, mode):
    return ix.refs(i, part, loose=(mode == 'loose'), minlen=MINLEN)
def closure(root_idx, mode, follow):
    return ix.closure(root_idx, follow, loose=(mode == 'loose'), minlen=MINLEN)
follow_state, follow_prove = ix.follow_state, ix.follow_prove

# ---------------------------------------------------------------- run
mode = 'loose' if LOOSE else 'strict'
rows, edges, report = [], [], []
report.append(f'mainline static dependency graph  (mode={mode}; generated {time.strftime("%Y-%m-%d %H:%M")})')
report.append('cone sizes are approximations: identifier resolution is textual (namespace + open aware),')
report.append('identifiers resolve only if their module is in the import closure of the use site (imports.jsonl); ambiguous names are ' +
              ('followed (loose)' if LOOSE else 'dropped (strict)') +
              '.')
report.append('"state" = what is needed to STATE the declaration (theorems: statement only);')
report.append('"prove" = what is needed to PROVE it (full text, transitive).')
report.append('')
report.append('tag         root                                                state: decls/files/filelines(decllines)   prove: decls/files/filelines(decllines)')
state = {}
for mod, name, tag in ROOTS:
    c = [i for i in ix.by_full.get(name, []) if decls[i]['mod'] == mod]
    if len(c) != 1:
        report.append(f'{tag:11s}  {name}: !! {len(c)} candidates in index')
        continue
    i = c[0]
    st, pr = closure(i, mode, follow_state), closure(i, mode, follow_prove)
    state[name] = (i, st, pr)
    a, b = summarize(st), summarize(pr)
    report.append(f'{tag:11s}  {name:51s} {a[0]:7d} {a[1]:6d} {a[2]:9d} ({a[3]:6d})          {b[0]:7d} {b[1]:6d} {b[2]:9d} ({b[3]:6d})')
    for m, seen in (('state', st), ('prove', pr)):
        for j in seen:
            d = decls[j]
            s, e = load_file(d['mod'])['spans'].get(j, (d['line'], d['line']))
            rows.append((name, m, tag, d['kind'], 'private' if d['private'] else 'public', d['name'], d['mod'], s, e))
    for p in ('stmt', 'full'):
        for j in refs(i, p, mode):
            edges.append((name, decls[j]['name'], decls[j]['kind'], p))

report.append('')
report.append('layer statement cones (union of the "state" cones of the layer conclusions):')
layer_union = {}
for ln, names in LAYERS.items():
    u = set()
    for n in names:
        if n in state:
            u |= state[n][1]
    layer_union[ln] = u
    a = summarize(u)
    thm = sum(1 for j in u if decls[j]['kind'] in ('theorem', 'lemma'))
    report.append(f'  {ln:26s} decls {a[0]:6d} (theorems {thm:5d})  files {a[1]:6d}  file lines {a[2]:9d}  decl lines {a[3]:7d}')
    report.append('      kinds: ' + ', '.join(f'{k}:{v}' for k, v in a[4].most_common()))
    report.append('      libs:  ' + ', '.join(f'{k}:{v}' for k, v in a[5].most_common(8)))

report.append('')
report.append("declaration `Hyps` referenced by UpperTheory.Top.plugWin (state cone):")
for rt, sn in (('UpperTheory.Top.plugWin', 'Hyps'), ('UpperTheory.Top.zero_free_all_of_green_v_win', 'HypsAlt')):
    if rt in state:
        for j in state[rt][1]:
            if decls[j]['short'] == sn:
                d = decls[j]
                report.append(f"  {d['name']}  @ {d['mod']}.lean:{d['line']} ({d['kind']})")

# Glue cones as "LayerN -> LayerN+1": prove cone of the glue theorem minus the state cone of its target layer
report.append('')
report.append('glue theorems: prove cone (files / file lines / decl lines) and how much of it is already inside the')
report.append('statement cone of the layer it concludes (so the rest is the real "glue" that must be extracted):')
for mod, name, tag in ROOTS:
    if tag.startswith('G:') and name in state:
        pr = state[name][2]
        target = {'L4>L5': 'L5 RiemannHypothesis', 'L3>L4': 'L4 EveryCharacter', 'L2>L3': 'L3 ZeroFreeAll',
                  'L2>L4': 'L4 EveryCharacter', 'L1>L4': 'L4 EveryCharacter', 'L1>L2': 'L2 VWin + Green + HypsAlt'}.get(tag[2:])
        a = summarize(pr)
        if target is None:
            report.append(f'  {name:60s} {a[1]:6d} files {a[2]:9d} lines ({a[3]:7d} decl lines); (input theorem, no target layer)')
            continue
        inside = pr & layer_union[target]
        report.append(f'  {name:60s} {a[1]:6d} files {a[2]:9d} lines ({a[3]:7d} decl lines); inside target layer statement cone: {len(inside)} decls')

# ---------------------------------------------------------------- sharing and hubs
report.append('')
report.append('pairwise sharing of cones (|A∩B| / |A| / |B|, Jaccard): layer statement cones, then the big glue prove cones')
def share(nameA, A, nameB, B):
    i = len(A & B)
    u = len(A | B)
    report.append(f'  {nameA:38s} ∩ {nameB:38s} {i:6d} / {len(A):6d} / {len(B):6d}   J={i/u if u else 0:.2f}   ({100*i/len(B) if B else 0:5.1f}% of the second)')
keys = list(layer_union)
for a in range(len(keys)):
    for b in range(a + 1, len(keys)):
        share(keys[a], layer_union[keys[a]], keys[b], layer_union[keys[b]])
report.append('')
big_glue = ['UpperTheory.Top.plugWin', 'UpperTheory.Top.zero_free_all_of_green_v_win', 'UpperTheory.One.vwin_of_row', 'UpperTheory.FinalTheorems.everyCharacter_of_row',
            'UpperTheory.Zero.LLC.recTExists', 'UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift', 'riemannHypothesis']
for a in range(len(big_glue)):
    for b in range(a + 1, len(big_glue)):
        if big_glue[a] in state and big_glue[b] in state:
            share(big_glue[a].split('.')[-1], state[big_glue[a]][2], big_glue[b].split('.')[-1], state[big_glue[b]][2])
report.append('')
report.append('hub files (most cone declarations) of each layer statement cone:')
# ---- which statements does the FINAL theorem actually depend on?  (is X in the prove cone of Main.riemannHypothesis)
ONPATH = ['UpperTheory.GalStar.Row0b', 'UpperTheory.Zero.LLC.RecTExists', 'UpperTheory.Zero.LLC.IsRecT',
          'UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift', 'UpperTheory.TP.K.tLiftK',
          'UpperTheory.One.vwin_of_row', 'UpperTheory.Top.VWin',
          'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin',
          'UpperTheory.Lit.every_character_of_theta_integrals_local_matching', 'RiemannHypothesis',
          # the route Main.lean really uses (TopPlug.lean, HypsAlt … DefiniteSideCondition):
          'UpperTheory.Top.every_character_of_green_v_win', 'UpperTheory.Top.imprimitive', 'UpperTheory.Top.zero_free_all_of_green_v_win',
          'Formalism.HC.ZeroFreeAll', 'UpperTheory.Top.zeroFreeAll_of_topG', 'GlobalTheory.GLq.Green', 'GlobalTheory.GreenBridge.green_of_regular',
          'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound', 'GlobalTheory.Fc.HypsAlt', 'GlobalTheory.Fc.DefiniteSideCondition',
          'UpperTheory.Top.supplyChi', 'UpperTheory.Top.shape_closed_link_n_of_green',
          # the parallel `plugWin` version (Hyps … DRS), not used by Main.lean:
          'GlobalTheory.Fc.Hyps', 'GlobalTheory.Fc.DRS', 'UpperTheory.Top.plugWin', 'UpperTheory.Top.plugAll', 'UpperTheory.Top.shapeWin']
EXP_IN = [n for n in ONPATH[:ONPATH.index('RiemannHypothesis')] if n != 'RiemannHypothesis']   # RH is Mathlib's def
EXP_IN += [n for n in ONPATH[ONPATH.index('RiemannHypothesis') + 1:ONPATH.index('GlobalTheory.Fc.Hyps')]]
EXP_OUT = ONPATH[ONPATH.index('GlobalTheory.Fc.Hyps') + 1:]
report.append('')
report.append('is the declaration in the prove cone of the final theorem `Main.riemannHypothesis`? (textual, strict)')
if 'riemannHypothesis' in state:
    rhc = {decls[j]['name'] for j in state['riemannHypothesis'][2]}
    for n in ONPATH:
        report.append(f"  {'IN    ' if n in rhc else 'not in'}  {n}")
    if all(n in rhc for n in EXP_IN) and not any(n in rhc for n in EXP_OUT):
        report.append('  => the final proof goes Row0b + RecTExists -> vwin_of_row -> VWin; then, INSIDE every_character_of_literature_of_vWin,')
        report.append('     Green + VWin + Nonempty (HypsAlt … DefiniteSideCondition) -> ZeroFreeAll (zero_free_all_of_green_v_win = zeroFreeAll_of_topG')
        report.append('     + shape_closed_link_n_of_green + supplyChi) -> EveryCharacter (imprimitive) -> RH.  The Hyps side condition is')
        report.append('     discharged inside the proof (nonempty_hyps_definite_side_of_closed_bound).  The parallel `plugWin`/`plugAll` version')
        report.append('     of EveryCharacter.lean (hypothesis `Hyps … DRS`) is NOT used by Main.lean.')
    else:
        report.append('  !! membership differs from the expected route; inspect manually:')
        report.append('     missing (expected IN): ' + ', '.join(n for n in EXP_IN if n not in rhc))
        report.append('     unexpected (expected not in): ' + ', '.join(n for n in EXP_OUT if n in rhc))
with open(OUT + '_layers.tsv', 'w') as fh:
    fh.write('layer\tkind\tvis\tname\tmodule\tstart\tend\n')
    for ln, u in layer_union.items():
        byfile = Counter(decls[i]['mod'] for i in u)
        report.append(f'  {ln}:')
        for mod, n in byfile.most_common(6):
            report.append(f'      {n:5d}  {mod}.lean')
        for i in u:
            d = decls[i]
            s, e = load_file(d['mod'])['spans'].get(i, (d['line'], d['line']))
            fh.write('\t'.join(map(str, (ln, d['kind'], 'private' if d['private'] else 'public', d['name'], d['mod'], s, e))) + '\n')
report.append('')
report.append('how the L2 cone splits between its inputs (statement cones):')
for n in ['UpperTheory.Top.VWin', 'GlobalTheory.GLq.Green', 'Formalism.MainNotions.LinkN', 'Formalism.MainNotions.Closed', 'GlobalTheory.Fc.DRS', 'GlobalTheory.Fc.Hyps', 'GlobalTheory.Fc.HypsAlt', 'GlobalTheory.Fc.DefiniteSideCondition']:
    if n in state:
        a = summarize(state[n][1])
        report.append(f'  {n:34s} decls {a[0]:6d}  files {a[1]:6d}  file lines {a[2]:9d}  decl lines {a[3]:7d}')

BIG = 2000   # cones larger than this are summarised in the .txt only (keeps the tsv small)
counts = Counter((r[0], r[1]) for r in rows)
with open(OUT + '.txt', 'w') as fh:
    fh.write('\n'.join(report) + '\n')
    fh.write(f'\n(the .tsv lists every declaration of each cone with <= {BIG} entries; bigger "prove" cones are only summarised here)\n')
with open(OUT + '.tsv', 'w') as fh:
    fh.write('root\tcone\ttag\tkind\tvis\tname\tmodule\tstart\tend\n')
    for r in rows:
        if counts[(r[0], r[1])] <= BIG:
            fh.write('\t'.join(map(str, r)) + '\n')
with open(OUT + '.dot', 'w') as fh:
    fh.write('digraph mainline {\n  rankdir=TB;\n  node [shape=box, fontname="Helvetica", fontsize=10];\n')
    for src, dst, kind, part in sorted(set(edges)):
        fh.write(f'  "{src}" -> "{dst}" [style={"solid" if part == "stmt" else "dashed"}];\n')
    fh.write('}\n')
print('\n'.join(report))
print(f'done in {time.time()-t0:.0f}s', file=sys.stderr)
