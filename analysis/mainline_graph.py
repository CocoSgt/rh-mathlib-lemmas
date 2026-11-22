#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Static dependency graph of the RH mainline (no Lean compilation).

Starting from the five theorems of source/src/Main.lean we follow the *proof
text* of every mainline theorem and record which declarations it mentions,
transitively.  The result is a declaration-level reference graph from which we
compute, for each mainline conclusion (EveryCharacter, ZeroFreeAll, VWin,
Green, Hyps-nonempty, Row0b, recTExists, ...), an approximate dependency cone:

  * proof cone      = every internal declaration needed to PROVE it
  * statement cone  = every internal definition needed just to STATE it
                      (bodies of defs/structures are followed, proofs of
                      theorems are not)

Method (all text-based, read-only on source/):

  pass A  scan every file once; locate declarations with the same regex as
          analysis/index_decls.py (plus `_root_` handling and Unicode names),
          record for each one its namespace stack, the `open` namespaces in
          scope and the file-level `variable` / `attribute` tokens.
  pass B  lazily, only for files reached by the BFS: split each declaration
          into STATEMENT (up to the first top-level `:=` / `where`) and PROOF,
          strip comments and strings, extract identifiers (dotted names
          included) and resolve them with Lean 4's scoping rules: current
          namespace prefixes innermost-first, then `open` namespaces, then
          root; `_root_.x` is absolute; `private` names resolve only inside
          their own file; dot notation `x.foo` / `x.A.foo` is resolved by the
          last one / two path components and only accepted when at most
          --dotcap candidates exist.  Local binder names are heuristically
          excluded from resolution.

Known limitations (all quantified in the output):
  * anonymous `instance : ...` declarations (3,360 in source/) are not nodes;
    type-class arguments are therefore invisible;
  * `export`ed names are not followed;
  * a reference through dot notation with > --dotcap candidates is dropped
    (counted as `tok_ambiguous`).

Usage:
  python3 analysis/mainline_graph.py                 # full run, writes analysis/mainline_graph.*
  python3 analysis/mainline_graph.py --show NAME     # direct references of NAME
  python3 analysis/mainline_graph.py --lookup PAT    # find declarations by (suffix) name
"""
import argparse, json, os, pickle, re, sys, time
from array import array
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, '..', 'source', 'src'))
KINDS = ['theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'instance', 'inductive',
         'opaque', 'axiom']
KIND_ID = {k: i for i, k in enumerate(KINDS)}
DECL_KW = frozenset(['theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'inductive',
                     'opaque', 'axiom', 'instance'])

# ---- lexical patterns -------------------------------------------------------
IDCH = r"[\w'′‵‴″‶⁗«»]"          # Lean identifier continuation characters
IDENT = r"[^\W\d]" + IDCH + "*"   # first char: letter or '_'
QUAL = re.compile(IDENT + r"(?:\." + IDENT + r")*")
IDSTART = re.compile(r"\s*" + IDENT + r"(?:\." + IDENT + r")*")
MODS = (r"(?:(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|local|scoped)\s+"
        r"|@\[[^\]]*\]\s*|attribute\s+\[[^\]]*\]\s*)*)")
KW = (r"theorem|lemma|def|structure|class|abbrev|instance|inductive|opaque|axiom|open|namespace|end|"
      r"section|variable|universe|import|example|mutual|export|deriving|syntax|macro|elab|notation|"
      r"infixl|infixr|infix|prefix|postfix|omit|include|run_cmd|module|register|set_option|"
      r"noncomputable|nonrec|private|protected|unsafe|partial|public|local|scoped|attribute|in")
LINE_RE = re.compile(r"^(?P<ind>\s*)(?P<mods>" + MODS + r")(?P<kw>" + KW +
                     r")(?![\w'′‵‴″«»])(?P<rest>.*)$")
# a command line (at indentation <= the declaration's own) ends a declaration
CMD_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*|attribute\s+\[[^\]]*\]\s*|"
                     r"(?:private|protected|noncomputable|nonrec|unsafe|partial|public|local|scoped)\s+)*"
                     r"(?:theorem|lemma|def|structure|class|abbrev|instance|inductive|opaque|axiom|open|"
                     r"namespace|end|section|variable|universe|import|example|mutual|export|deriving|"
                     r"syntax|macro|elab|notation|infixl|infixr|infix|prefix|postfix|omit|include|"
                     r"run_cmd|module|register|set_option|#\w+)(?![\w'′‵‴″«»])")
BCSCAN = re.compile(r'/-|-/')
STRING_RE = re.compile(r'"(?:[^"\\\n]|\\.)*"')
BRACKET_RE = re.compile(r'\[[^\]]*\]')
SPLIT_RE = re.compile(r'[(){}\[\]⟨⟩]|:=|\bwhere\b')
OPENERS = {'(', '[', '{', '⟨'}
IDENTS_IN = re.compile(IDENT)
BIND_RES = [  # heuristic binder capture (group 1 = binder names)
    re.compile(r"[(\[{]\s*(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:"),
    re.compile(r"[∀∃]\s+(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*(?:,|\|)"),
    re.compile(r"\bfun\s+(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*=>"),
    re.compile(r"\b(?:intro|intros|rintro|rename_i|next)\s+(" + IDENT + r"(?:\s+" + IDENT + r")*)"),
    re.compile(r"\b(?:have|haveI|let|letI|set|case|generalize|specialize)\s+(" + IDENT + r")"),
    re.compile(r"\b(?:obtain|rcases|rintro)\b[^\n]*?⟨([^⟩\n]*)⟩"),
]


def log(msg):
    print(f'[{time.strftime("%H:%M:%S")}] {msg}', file=sys.stderr, flush=True)


def clean_lines(raw):
    """Strip line/block comments (nested) and strings. Returns list of clean lines."""
    out = []
    depth = 0
    for ln in raw:
        ln = STRING_RE.sub('""', ln)
        buf = []
        i = 0
        n = len(ln)
        while i < n:
            if depth:
                m = BCSCAN.search(ln, i)
                if not m:
                    i = n
                    break
                if m.group() == '/-':
                    depth += 1
                else:
                    depth -= 1
                i = m.end()
                continue
            c = ln.find('--', i)
            b = ln.find('/-', i)
            if c >= 0 and (b < 0 or c < b):
                buf.append(ln[i:c])
                break
            if b >= 0:
                buf.append(ln[i:b])
                depth = 1
                i = b + 2
                continue
            buf.append(ln[i:])
            break
        out.append(''.join(buf))
    return out


# ============================================================================
# pass A: declaration index with scope context
# ============================================================================
class Index:
    def __init__(self):
        self.mods = {}            # mod -> line count
        self.decl = []            # (mod_id, line, kind, full, short, private, ns_prefixes, opens, ambient)
        self.mod_id = {}          # mod -> id
        self.mod_name = []
        self.by_mod = {}          # mod_id -> [decl ids] (sorted by line)
        self.full = {}            # full name -> ids
        self.short = {}           # last component -> ids
        self.pair = {}            # 'secondlast.last' -> ids
        self.shortset = set()
        self.stats = Counter()

    def scan(self):
        t0 = time.time()
        nfiles = 0
        for dp, dn, fn in os.walk(SRC):
            for f in fn:
                if not f.endswith('.lean'):
                    continue
                path = os.path.join(dp, f)
                mod = os.path.relpath(path, SRC)[:-5].replace(os.sep, '.')
                with open(path, 'r', encoding='utf-8', errors='replace') as fh:
                    raw = fh.read().split('\n')
                if raw and raw[-1] == '':
                    raw.pop()
                self.mods[mod] = len(raw)
                self.scan_file(mod, raw)
                nfiles += 1
                if nfiles % 30000 == 0:
                    log(f'  pass A: {nfiles} files, {len(self.decl)} decls, {time.time()-t0:.0f}s')
        self.finalize()
        self.stats['files'] = nfiles
        self.stats['lines'] = sum(self.mods.values())
        log(f'pass A done: {nfiles} files, {len(self.decl)} decls in {time.time()-t0:.0f}s; '
            + ', '.join(f'{k}={v}' for k, v in sorted(self.stats.items())))

    def scan_file(self, mod, raw):
        clean = clean_lines(raw)
        mid = len(self.mod_name)
        self.mod_id[mod] = mid
        self.mod_name.append(mod)
        self.by_mod[mid] = []
        stack = [{'kind': 'file', 'name': '', 'opens': [], 'vars': [], 'next': None}]
        ns = []          # full namespace prefixes, outermost first
        var_cont = False
        for i, s in enumerate(clean):
            m = LINE_RE.match(s)
            if not m:
                st = s.lstrip()
                if not st:
                    continue
                if var_cont and s[:1].isspace():
                    stack[-1]['vars'].extend(QUAL.findall(st))
                    continue
                if st.startswith('attribute ') and not s[:1].isspace():
                    stack[-1]['vars'].extend(QUAL.findall(BRACKET_RE.sub('', st[9:])))
                continue
            var_cont = False
            kw = m.group('kw')
            rest = m.group('rest')
            if kw in DECL_KW:
                nm = IDSTART.match(rest)
                if not nm:
                    self.stats['anon_instance'] += 1
                    stack[-1]['next'] = None
                    continue
                name = nm.group().strip()
                private = 'private' in m.group('mods')
                full = name[7:] if name.startswith('_root_.') else ((ns[-1] + '.' if ns else '') + name)
                short = full.rsplit('.', 1)[-1]
                opens = [o for sc in stack for o in sc['opens']]
                if stack[-1]['next']:
                    opens += stack[-1]['next']
                ambient = [v for sc in stack for v in sc['vars']]
                did = len(self.decl)
                self.decl.append((mid, i + 1, KIND_ID[kw], full, short, private,
                                  tuple(reversed(ns)), tuple(opens), tuple(ambient)))
                self.by_mod[mid].append(did)
                stack[-1]['next'] = None
                continue
            stack[-1]['next'] = None
            if kw == 'namespace':
                nm = rest.strip()
                ns.append((ns[-1] + '.' if ns else '') + nm)
                stack.append({'kind': 'ns', 'name': nm, 'opens': [], 'vars': [], 'next': None})
            elif kw == 'section':
                stack.append({'kind': 'sec', 'name': rest.strip(), 'opens': [], 'vars': [],
                              'next': None})
            elif kw == 'mutual':
                stack.append({'kind': 'mutual', 'name': '', 'opens': [], 'vars': [], 'next': None})
            elif kw == 'end':
                nm = rest.strip()
                k = len(stack) - 1
                if nm:
                    while k > 0:
                        e = stack[k]['name']
                        if e == nm or e.endswith('.' + nm) or e.rsplit('.', 1)[-1] == nm:
                            break
                        k -= 1
                    while len(stack) > max(k, 1):
                        if stack.pop()['kind'] == 'ns':
                            ns.pop()
                elif len(stack) > 1:
                    if stack.pop()['kind'] == 'ns':
                        ns.pop()
            elif kw == 'open':
                parts = [p for p in rest.split() if p not in ('scoped', 'public')]
                if parts and parts[-1] == 'in':
                    stack[-1]['next'] = parts[:-1]
                else:
                    stack[-1]['opens'].extend(parts)
            elif kw == 'variable':
                stack[-1]['vars'].extend(QUAL.findall(rest))
                var_cont = True
            elif kw == 'export':
                self.stats['export'] += 1

    def finalize(self):
        full = defaultdict(list)
        short = defaultdict(list)
        pair = defaultdict(list)
        for did, d in enumerate(self.decl):
            full[d[3]].append(did)
            short[d[4]].append(did)
            comps = d[3].split('.')
            if len(comps) >= 2:
                pair[comps[-2] + '.' + comps[-1]].append(did)
        self.full, self.short, self.pair = dict(full), dict(short), dict(pair)
        self.shortset = set(self.short)
        for d in self.decl:
            self.stats[KINDS[d[2]]] += 1


# ============================================================================
# pass B: tokens -> resolved edges, lazily per file
# ============================================================================
def split_stmt_proof(text, kind):
    if KINDS[kind] in ('structure', 'inductive', 'class'):
        return text, ''
    depth = 0
    for m in SPLIT_RE.finditer(text):
        t = m.group()
        if t in (':=', 'where'):
            if depth == 0:
                return text[:m.start()], text[m.end():]
        elif t in OPENERS:
            depth += 1
        else:
            depth = max(0, depth - 1)
    return text, ''


def binders(text):
    local = set()
    for k, r in enumerate(BIND_RES):
        for m in r.finditer(text):
            g = m.group(1)
            if not g:
                continue
            if k == 5:
                local.update(mm.group() for mm in IDENTS_IN.finditer(g))
            else:
                local.update(g.split())
    return local


class Graph:
    def __init__(self, idx, dotcap=6):
        self.idx = idx
        self.dotcap = dotcap
        n = len(idx.decl)
        self.kind = array('b', [d[2] for d in idx.decl])
        self.mod_of = array('i', [d[0] for d in idx.decl])
        self.stmt = [None] * n
        self.proof = [None] * n
        self.span = array('i', bytes(4 * n))
        self.done = bytearray(n)
        self.n_parsed = 0
        self.tokstats = Counter()

    def _vis(self, i, mid):
        d = self.idx.decl[i]
        return (not d[5]) or d[0] == mid

    def resolve(self, tok, ns, opens, mid, local, toks_all):
        idx = self.idx
        last = tok.rpartition('.')[2]
        if last not in idx.shortset:
            self.tokstats['unres_pruned'] += 1
            return ()
        ts = self.tokstats
        if tok.startswith('_root_.'):
            r = [i for i in idx.full.get(tok[7:], ()) if self._vis(i, mid)]
            if r:
                ts['res_abs'] += 1
                return r
        if '.' not in tok:
            if tok in local:
                ts['local'] += 1
                return ()
            for p in ns:
                r = idx.full.get(p + '.' + tok)
                if r:
                    r = [i for i in r if self._vis(i, mid)]
                    if r:
                        ts['res_ns'] += 1
                        return r
            for o in opens:
                r = idx.full.get(o + '.' + tok)
                if r:
                    r = [i for i in r if self._vis(i, mid)]
                    if r:
                        ts['res_open'] += 1
                        return r
            r = idx.full.get(tok)
            if r:
                r = [i for i in r if self._vis(i, mid)]
                if r:
                    ts['res_root'] += 1
                    return r
            ts['unres_simple'] += 1
            return ()
        for p in ns:
            r = idx.full.get(p + '.' + tok)
            if r:
                r = [i for i in r if self._vis(i, mid)]
                if r:
                    ts['res_ns'] += 1
                    return r
        for o in opens:
            r = idx.full.get(o + '.' + tok)
            if r:
                r = [i for i in r if self._vis(i, mid)]
                if r:
                    ts['res_open'] += 1
                    return r
        r = idx.full.get(tok)
        if r:
            r = [i for i in r if self._vis(i, mid)]
            if r:
                ts['res_root'] += 1
                return r
        # dot notation `x.foo` / `x.A.foo`: only on a (lower-case or bound) receiver, and the
        # candidate must live in the same file or in a namespace named after a type written here
        comps = tok.split('.')
        x0 = comps[0]
        if not (x0 in local or x0[:1].islower()):
            ts['unres_qual'] += 1
            return ()
        if len(comps) >= 3:
            key = comps[-2] + '.' + last
            suf = '.' + key
            c = [i for i in idx.pair.get(key, ()) if idx.decl[i][3].endswith(suf)]
        else:
            c = idx.short.get(last, ())
        c = [i for i in c if self._vis(i, mid)]
        def ok(i):
            if idx.decl[i][0] == mid:
                return True
            pc = idx.decl[i][3].split('.')
            return (pc[-2] if len(pc) > 1 else pc[0]) in toks_all
        c = [i for i in c if ok(i)]
        if 0 < len(c) <= self.dotcap:
            ts['res_dot'] += 1
            return c
        if c:
            ts['ambiguous'] += 1
        else:
            ts['unres_qual'] += 1
        return ()

    def parse_file(self, mid):
        mod = self.idx.mod_name[mid]
        path = os.path.join(SRC, mod.replace('.', '/') + '.lean')
        with open(path, 'r', encoding='utf-8', errors='replace') as fh:
            raw = fh.read().split('\n')
        if raw and raw[-1] == '':
            raw.pop()
        clean = clean_lines(raw)
        recs = self.idx.by_mod[mid]
        for k, did in enumerate(recs):
            if self.done[did]:
                continue
            d = self.idx.decl[did]
            l0 = d[1] - 1
            line = raw[l0]
            ind = len(line) - len(line.lstrip())
            lim = self.idx.decl[recs[k + 1]][1] - 1 if k + 1 < len(recs) else len(raw)
            j = l0 + 1
            while j < lim:
                ln = raw[j]
                if CMD_RE.match(ln) and (len(ln) - len(ln.lstrip())) <= ind:
                    break
                j += 1
            text = '\n'.join(clean[l0:j])
            self.span[did] = j - l0
            st, pf = split_stmt_proof(text, self.kind[did])
            local = binders(text)
            s_ids = set()
            p_ids = set()
            toks_all = set(QUAL.findall(text))
            toks = set(QUAL.findall(st))
            toks.update(d[8])
            for t in toks:
                for i in self.resolve(t, d[6], d[7], mid, local, toks_all):
                    if i != did:
                        s_ids.add(i)
            for t in set(QUAL.findall(pf)):
                for i in self.resolve(t, d[6], d[7], mid, local, toks_all):
                    if i != did:
                        p_ids.add(i)
            self.stmt[did] = array('i', sorted(s_ids))
            self.proof[did] = array('i', sorted(p_ids))
            self.done[did] = 1
        self.n_parsed += 1

    def edges(self, did, follow_proofs):
        if not self.done[did]:
            self.parse_file(self.mod_of[did])
        if follow_proofs or self.kind[did] not in (0, 1):
            return self.stmt[did], self.proof[did]
        return self.stmt[did], ()


def closure(g, roots, mode):
    """Transitive closure from `roots` as a bitmap (bytearray of len n_decls)."""
    seen = bytearray(len(g.kind))
    stack = list(roots)
    fp = mode == 'proof'
    while stack:
        d = stack.pop()
        if seen[d]:
            continue
        seen[d] = 1
        s, p = g.edges(d, fp)
        stack.extend(s)
        stack.extend(p)
    return seen


def bits(bmp):
    return [i for i in range(len(bmp)) if bmp[i]]


def bop(a, b, op):
    ia = int.from_bytes(a, 'little')
    ib = int.from_bytes(b, 'little')
    r = ia & ib if op == '&' else (ia | ib if op == '|' else ia & ~ib)
    return bytearray(r.to_bytes(len(a), 'little'))


def bcount(bmp):
    return int.from_bytes(bmp, 'little').bit_count()


def find(idx, name):
    if name in idx.full:
        return list(idx.full[name])
    suf = '.' + name
    out = list(idx.short.get(name, ()))
    out += [i for i, d in enumerate(idx.decl) if d[3].endswith(suf)]
    return sorted(set(out))


# ============================================================================
# mainline roots
# ============================================================================
# mode: proof = full dependency cone; stmt = definitions needed to state it only
MAINLINE_ROOTS = [
    # --- Main.lean ---------------------------------------------------------
    dict(id='Main.riemannHypothesis', name='riemannHypothesis', mode='proof', grp='Main'),
    dict(id='Main.riemannZeta_eq_zero_re', name='riemannZeta_eq_zero_re', mode='proof', grp='Main'),
    dict(id='Main.LFunction_ne_zero_of_half_lt_re', name='LFunction_ne_zero_of_half_lt_re', mode='proof', grp='Main'),
    dict(id='Main.LFunction_eq_zero_re', name='LFunction_eq_zero_re', mode='proof', grp='Main'),
    dict(id='Main.LFunction_eq_zero_re_of_isPrimitive', name='LFunction_eq_zero_re_of_isPrimitive', mode='proof', grp='Main'),
    # --- layer 1: top glue (expected Mathlib-only) --------------------------
    dict(id='T.rh_of_right', name='Formalism.VW.rh_of_right', mode='proof', grp='glue'),
    dict(id='T.rh_of_every', name='Formalism.VW.rh_of_every', mode='proof', grp='glue'),
    dict(id='T.critLine', name='Formalism.VW.critLine', mode='proof', grp='glue'),
    dict(id='T.rh_of_everyCharacter', name='UpperTheory.riemannHypothesis_of_everyCharacter', mode='proof', grp='glue'),
    dict(id='T.Claim.strip', name='Claim.strip', mode='proof', grp='glue'),
    dict(id='T.Claim.zeta', name='Claim.zeta', mode='proof', grp='glue'),
    # --- statements of the layer propositions ---------------------------------
    dict(id='P.EveryCharacter', name='UpperTheory.EveryCharacter', mode='stmt', grp='stmt'),
    dict(id='P.ZeroFreeAll', name='Formalism.HC.ZeroFreeAll', mode='stmt', grp='stmt'),
    dict(id='P.VWin', name='UpperTheory.Top.VWin', mode='stmt', grp='stmt'),
    dict(id='P.Row0b', name='UpperTheory.GalStar.Row0b', mode='stmt', grp='stmt'),
    dict(id='P.RecTExists', name='UpperTheory.Zero.LLC.RecTExists', mode='stmt', grp='stmt'),
    dict(id='P.Green', name='GlobalTheory.GLq.Green', mode='stmt', grp='stmt'),
    dict(id='P.Hyps', name='GlobalTheory.Fc.Hyps', mode='stmt', grp='stmt'),
    dict(id='P.HypsAlt', name='GlobalTheory.Fc.HypsAlt', mode='stmt', grp='stmt'),
    dict(id='P.DefiniteSideCondition', name='GlobalTheory.Fc.DefiniteSideCondition', mode='stmt', grp='stmt'),
    dict(id='P.Closed', name='Formalism.MainNotions.Closed', mode='stmt', grp='stmt'),
    dict(id='P.LinkN', name='Formalism.MainNotions.LinkN', mode='stmt', grp='stmt'),
    dict(id='P.TopG', name='UpperTheory.Top.TopG', mode='stmt', grp='stmt'),
    dict(id='P.TopShape', name='GlobalTheory.Fc.TopShape', mode='stmt', grp='stmt'),
    dict(id='P.OpenLiteratureStatements', name='UpperTheory.LiteratureTheorems.OpenLiteratureStatements', mode='stmt', grp='stmt'),
    dict(id='P.OpenImageCondition', name='UpperTheory.LiteratureTheorems.OpenImageCondition', mode='stmt', grp='stmt'),
    dict(id='P.IsRecT', name='UpperTheory.Zero.LLC.IsRecT', mode='stmt', grp='stmt'),
    dict(id='P.claimAll', name='claimAll', mode='stmt', grp='stmt'),
    dict(id='P.critAll', name='critAll', mode='stmt', grp='stmt'),
    # --- layer 3/4: EveryCharacter and its routes ------------------------------
    dict(id='T.everyCharacter', name='UpperTheory.FinalTheorems.everyCharacter', mode='proof', grp='every'),
    dict(id='T.everyCharacter_of_row', name='UpperTheory.FinalTheorems.everyCharacter_of_row', mode='proof', grp='every'),
    dict(id='T.every_char_lit_vWin', name='UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin', mode='proof', grp='every'),
    dict(id='T.every_char_theta_il', name='UpperTheory.Lit.every_character_of_theta_integrals_local_matching', mode='proof', grp='every'),
    dict(id='T.every_char_green_vwin', name='UpperTheory.Top.every_character_of_green_v_win', mode='proof', grp='zero'),
    dict(id='T.zero_free_green_vwin', name='UpperTheory.Top.zero_free_all_of_green_v_win', mode='proof', grp='zero'),
    dict(id='T.shape_closed_link_n', name='UpperTheory.Top.shape_closed_link_n_of_green', mode='proof', grp='zero'),
    dict(id='T.shape_of_hyps', name='GlobalTheory.Fc.forall_goal_of_shape_of_hyps', mode='proof', grp='zero'),
    dict(id='T.everyE₂', name='UpperTheory.Lit.everyE₂', mode='proof', grp='every'),
    dict(id='T.hypsE₂', name='UpperTheory.Lit.hypsE₂', mode='proof', grp='hyps'),
    # the route described in REPORT §1.3 (EveryCharacter.lean / plugAll, hypothesis Hyps N DRS)
    dict(id='T.plugAll', name='UpperTheory.Top.plugAll', mode='proof', grp='zero'),
    dict(id='T.plugWin', name='UpperTheory.Top.plugWin', mode='proof', grp='zero'),
    dict(id='T.zeroFreeAll_of_topG', name='UpperTheory.Top.zeroFreeAll_of_topG', mode='proof', grp='zero'),
    dict(id='T.imprimitive', name='UpperTheory.Top.imprimitive', mode='proof', grp='zero'),
    dict(id='T.shapeWin', name='UpperTheory.Top.shapeWin', mode='proof', grp='zero'),
    dict(id='T.shape_of', name='GlobalTheory.Fc.shape_of', mode='proof', grp='zero'),
    dict(id='T.supplyChi', name='UpperTheory.Top.supplyChi', mode='proof', grp='zero'),
    dict(id='T.green_of_regular', name='GlobalTheory.GreenBridge.green_of_regular', mode='proof', grp='green'),
    dict(id='T.nonempty_hyps_DS', name='UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound', mode='proof', grp='hyps'),
    dict(id='T.nonempty_hyps_UE', name='GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE', mode='proof', grp='hyps'),
    dict(id='T.nonempty_hyps_allRows', name='GlobalTheory.Fc.nonempty_hyps_of_allRows', mode='proof', grp='hyps'),
    # --- layer 2/3: window, Galois, local Langlands ---------------------------
    dict(id='T.vwin_of_row', name='UpperTheory.One.vwin_of_row', mode='proof', grp='window'),
    dict(id='T.automorphic_window', name='UpperTheory.One.Join.automorphic_window_of_inputs', mode='proof', grp='window'),
    dict(id='T.baseChangeN', name='UpperTheory.BaseChangeIdentities.baseChangeN', mode='proof', grp='window'),
    dict(id='T.gal_row0b', name='UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter', mode='proof', grp='gal'),
    dict(id='T.recTExists', name='UpperTheory.Zero.LLC.recTExists', mode='proof', grp='llc'),
]

# layers used for the overlap matrix (proof cones unless stated)
LAYERS = [
    ('L1 glue (rh_of_right … Claim.zeta)', ['T.rh_of_right', 'T.rh_of_every', 'T.critLine', 'T.rh_of_everyCharacter', 'T.Claim.strip', 'T.Claim.zeta']),
    ('L2 Galois rep (Row0b)', ['T.gal_row0b']),
    ('L2 local Langlands (recTExists)', ['T.recTExists']),
    ('L3 window (Row0b -> VWin)', ['T.vwin_of_row']),
    ('L4 Green', ['T.green_of_regular']),
    ('L4 Hyps nonempty (definite side)', ['T.nonempty_hyps_DS']),
    ('L4 ZeroFreeAll route (plugWin)', ['T.plugWin']),
    ('L4 EveryCharacter (every_char_lit_vWin)', ['T.every_char_lit_vWin']),
]


def lib2(mod):
    c = mod.split('.')
    return '.'.join(c[:2]) if c[0] == 'Development' else c[0]


class Reporter:
    def __init__(self, g):
        self.g = g
        self.idx = g.idx
        self.lines = []

    def w(self, s=''):
        self.lines.append(s)
        print(s, flush=True)

    def text(self):
        return '\n'.join(self.lines) + '\n'


def cone_stats(g, ids):
    idx = g.idx
    kinds = Counter()
    mods = {}
    dl = 0
    libs = defaultdict(lambda: [0, 0, 0])
    for d in ids:
        mid = idx.decl[d][0]
        mods[mid] = 1
        dl += g.span[d]
        kinds[KINDS[g.kind[d]]] += 1
    for mid in mods:
        mod = idx.mod_name[mid]
        n = idx.mods[mod]
        lb = libs[lib2(mod)]
        lb[1] += 1
        lb[2] += n
    for d in ids:
        libs[lib2(idx.mod_name[idx.decl[d][0]])][0] += 1
    thm = kinds['theorem'] + kinds['lemma']
    return dict(decls=len(ids), thm=thm, defs=len(ids) - thm, files=len(mods),
                flines=sum(idx.mods[idx.mod_name[m]] for m in mods), dlines=dl,
                kinds=kinds, libs=libs, mods=mods)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', default='', help='pickle cache for the pass-A index')
    ap.add_argument('--dotcap', type=int, default=6)
    ap.add_argument('--show', nargs='*', default=[])
    ap.add_argument('--lookup', nargs='*', default=[])
    ap.add_argument('--out', default=os.path.join(HERE, 'mainline_graph'))
    ap.add_argument('--no-bfs', action='store_true')
    ap.add_argument('--subset', nargs='*', default=[], help='only these root ids (debug)')
    ap.add_argument('--dump', default='', help='pickle cones+edges to this path (post-hoc analysis)')
    ap.add_argument('--gcache', default='', help='pickle cache of pass-B edges (speeds up re-runs)')
    args = ap.parse_args()

    idx = Index()
    if args.cache and os.path.exists(args.cache):
        log('loading index cache ' + args.cache)
        with open(args.cache, 'rb') as fh:
            idx = pickle.load(fh)
        log('index cache loaded: %d decls' % len(idx.decl))
    else:
        idx.scan()
        if args.cache:
            with open(args.cache, 'wb') as fh:
                pickle.dump(idx, fh, protocol=5)
    g = Graph(idx, args.dotcap)
    if args.gcache and os.path.exists(args.gcache):
        log('loading pass-B edge cache ' + args.gcache)
        with open(args.gcache, 'rb') as fh:
            c = pickle.load(fh)
        n = min(len(c['done']), len(g.done))
        for k in ('stmt', 'proof', 'span', 'done'):
            getattr(g, k)[:n] = c[k][:n]
        g.n_parsed = c['n_parsed']
        log(f'pass-B cache loaded: {sum(g.done):,} declarations')
    rep = Reporter(g)

    for pat in args.lookup:
        hits = find(idx, pat)
        rep.w(f'## lookup {pat}: {len(hits)}')
        for i in hits[:40]:
            d = idx.decl[i]
            rep.w(f"   {KINDS[d[2]]:8s} {'private ' if d[5] else ''}{d[3]}  @ "
                  f"{idx.mod_name[d[0]].replace('.', '/')}.lean:{d[1]}")
    for name in args.show:
        hits = find(idx, name)
        rep.w(f'## show {name}: {len(hits)}')
        for i in hits:
            d = idx.decl[i]
            g.parse_file(d[0])
            rep.w(f"-- {KINDS[d[2]]} {d[3]} @ {idx.mod_name[d[0]].replace('.', '/')}.lean:{d[1]} "
                  f"(span {g.span[i]} lines; ns={list(d[6])}; opens={len(d[7])})")
            s, p = g.stmt[i], g.proof[i]
            rep.w(f'   statement refs ({len(s)}): ' + ', '.join(idx.decl[t][3] for t in s))
            rep.w(f'   proof refs ({len(p)}): ' + ', '.join(idx.decl[t][3] for t in p))
    if args.show or args.lookup:
        rep.w('token stats: ' + ', '.join(f'{k}={v}' for k, v in sorted(g.tokstats.items())))
        return
    if args.no_bfs:
        return
    run_cones(g, rep, idx, args)


SPINE = [  # theorem whose direct proof references are costed one by one
    'UpperTheory.FinalTheorems.everyCharacter_of_row',
    'UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin',
    'UpperTheory.Lit.every_character_of_theta_integrals_local_matching',
    'UpperTheory.Top.every_character_of_green_v_win',
    'UpperTheory.Top.zero_free_all_of_green_v_win',
    'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound',
    'UpperTheory.Lit.everyE₂',
    'UpperTheory.Lit.hypsE₂',
    'UpperTheory.One.vwin_of_row',
    'UpperTheory.One.Join.automorphic_window_of_inputs',
    'UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter',
    'UpperTheory.Zero.LLC.recTExists',
    'UpperTheory.Top.plugWin',
    'UpperTheory.Top.shapeWin',
    'UpperTheory.Top.shape_closed_link_n_of_green',
    'GlobalTheory.Fc.S0.StageU.nonempty_hyps_of_classicalTheoremsUE',
    'GlobalTheory.GreenBridge.green_of_regular',
]
BIG = ['Main.riemannHypothesis', 'T.every_char_lit_vWin', 'T.plugAll', 'T.green_of_regular',
       'T.nonempty_hyps_DS', 'T.vwin_of_row', 'T.gal_row0b', 'T.recTExists']
FILELIST_MAX = 12500
FILELIST = ['T.rh_of_every', 'T.every_char_lit_vWin', 'T.plugAll', 'T.plugWin', 'T.vwin_of_row',
            'T.automorphic_window', 'T.gal_row0b', 'T.recTExists', 'T.green_of_regular',
            'T.nonempty_hyps_DS', 'T.nonempty_hyps_UE', 'T.nonempty_hyps_allRows',
            'T.zeroFreeAll_of_topG', 'T.imprimitive', 'T.shapeWin', 'T.baseChangeN']


def f0(n):
    return f'{n:,}'


def loc(idx, i):
    d = idx.decl[i]
    return f"{idx.mod_name[d[0]].replace('.', '/')}.lean:{d[1]}"


def dirbreak(idx, cone, g, depth):
    """decls / files / file-lines per module prefix of the given depth."""
    files = defaultdict(lambda: [0, 0])
    seen = set()
    dl = defaultdict(int)
    for d in cone:
        mod = idx.mod_name[idx.decl[d][0]]
        k = '.'.join(mod.split('.')[:depth])
        dl[k] += g.span[d]
        if idx.decl[d][0] not in seen:
            seen.add(idx.decl[d][0])
            files[k][0] += 1
            files[k][1] += idx.mods[mod]
    nd = defaultdict(int)
    for d in cone:
        nd['.'.join(idx.mod_name[idx.decl[d][0]].split('.')[:depth])] += 1
    return {k: (nd[k], files[k][0], files[k][1], dl[k]) for k in files}


def run_cones(g, rep, idx, args):
    roots = MAINLINE_ROOTS
    if args.subset:
        roots = [r for r in roots if r['id'] in args.subset]
    md = []
    cones, st, rootids = {}, {}, {}
    t0 = time.time()
    for r in roots:
        ids = find(idx, r['name'])
        if not ids:
            rep.w(f'!! root not found: {r["name"]}')
            continue
        bmp = closure(g, ids, r['mode'])
        cones[r['id']] = bmp
        rootids[r['id']] = ids
        st[r['id']] = cone_stats(g, bits(bmp))
        s = st[r['id']]
        log(f"{r['id']:34s} {r['mode']:5s} decls={s['decls']:>9,} files={s['files']:>8,} "
            f"flines={s['flines']:>12,} ({time.time()-t0:.0f}s, parsed {g.n_parsed:,} files)")
    ntok = ', '.join(f'{k}={v}' for k, v in sorted(g.tokstats.items()))
    cones_mode = {r['id']: r['mode'] for r in roots}

    def prow(rid):
        s = st[rid]
        return (f"{rid:34s} {cones_mode[rid]:5s} {f0(s['decls']):>9s} {f0(s['thm']):>8s} "
                f"{f0(s['defs']):>8s} {f0(s['files']):>7s} {f0(s['flines']):>11s} {f0(s['dlines']):>10s}")

    def files_of(bmp):
        return {idx.decl[i][0] for i in bits(bmp)}

    def flines_of(bmp):
        return sum(idx.mods[idx.mod_name[m]] for m in files_of(bmp))

    rep.w('# Mainline static dependency graph  (analysis/mainline_graph.py)')
    rep.w(f'generated {time.strftime("%Y-%m-%d %H:%M:%S")}; source {SRC}')
    rep.w(f'index: {f0(len(idx.decl))} declarations in {f0(len(idx.mod_name))} files / '
          f'{f0(sum(idx.mods.values()))} lines')
    rep.w()
    rep.w('## 1. Cones')
    rep.w('proof cone = all internal declarations reachable from the proof (statement + body);')
    rep.w('stmt cone  = definitions reachable from the statement only (bodies of defs/structures')
    rep.w('            followed, proofs of theorems not).  decl-lines = sum of declaration spans.')
    rep.w(f"{'root':34s} {'mode':5s} {'decls':>9s} {'thm':>8s} {'def':>8s} {'files':>7s} "
          f"{'file-lines':>11s} {'decl-lines':>10s}")
    md.append('| root | mode | decls | thm | def | files | file-lines | decl-lines |')
    md.append('|---|---|---:|---:|---:|---:|---:|---:|')
    for r in roots:
        if r['id'] in cones:
            rep.w(prow(r['id']))
            s = st[r['id']]
            md.append(f"| `{r['id']}` | {cones_mode[r['id']]} | {s['decls']:,} | {s['thm']:,} | "
                      f"{s['defs']:,} | {s['files']:,} | {s['flines']:,} | {s['dlines']:,} |")
    rep.w()
    rep.w(f'pass B parsed {f0(g.n_parsed)} files in {time.time()-t0:.0f}s; token resolution: {ntok}')
    rep.w()

    # ---------------- 2. glue validation ----------------
    rep.w('## 2. Top glue theorems: internal declarations in the proof cone (expected: none)')
    for rid in ['T.rh_of_right', 'T.rh_of_every', 'T.critLine', 'T.rh_of_everyCharacter',
                'T.Claim.strip', 'T.Claim.zeta']:
        if rid not in cones:
            continue
        rb = bytearray(len(g.kind))
        for i in rootids[rid]:
            rb[i] = 1
        c = bop(cones[rid], rb, '-')
        names = sorted(idx.decl[i][3] + ' <' + KINDS[g.kind[i]] + '>' for i in bits(c))
        rep.w(f"{rid:24s} {len(names):4d} internal decls" + ('' if not names else ': ' + ', '.join(names)))
    rep.w()

    # ---------------- 3. statement cones ----------------
    rep.w('## 3. Statement cones of the layer propositions (what must be ported to STATE them)')
    md.append('')
    md.append('| proposition | decls | def | thm | files | file-lines | decl-lines |')
    md.append('|---|---:|---:|---:|---:|---:|---:|')
    for r in roots:
        if r['grp'] != 'stmt' or r['id'] not in cones:
            continue
        s = st[r['id']]
        i0 = rootids[r['id']][0]
        rep.w(f"### {r['id']}  ({idx.decl[i0][3]} @ {loc(idx, i0)})")
        rep.w(f"    decls={f0(s['decls'])} (thm {s['thm']}, def {s['defs']})  files={f0(s['files'])}  "
              f"file-lines={f0(s['flines'])}  decl-lines={f0(s['dlines'])}")
        md.append(f"| `{r['id']}` | {s['decls']:,} | {s['defs']:,} | {s['thm']:,} | {s['files']:,} | "
                  f"{s['flines']:,} | {s['dlines']:,} |")
        members = sorted(bits(cones[r['id']]), key=lambda i: (idx.mod_name[idx.decl[i][0]], idx.decl[i][1]))
        for i in members[:80]:
            d = idx.decl[i]
            rep.w(f"    {KINDS[d[2]]:9s} {d[3]}   [{loc(idx, i)}]")
        if len(members) > 80:
            rep.w(f'    ... {len(members)-80} more')
    rep.w()

    # ---------------- 4. layers and overlaps ----------------
    rep.w('## 4. Layer cones (proof) and how much they share')
    layers = []
    for name, rids in LAYERS:
        u = None
        for rid in rids:
            if rid not in cones:
                continue
            u = cones[rid] if u is None else bop(u, cones[rid], '|')
        if u is None:
            continue
        layers.append((name, u))
        st['L:' + name] = cone_stats(g, bits(u))
    rep.w(f"{'layer':44s} {'decls':>9s} {'files':>7s} {'file-lines':>11s} {'decl-lines':>10s}")
    md.append('')
    md.append('| layer | decls | files | file-lines | exclusive decls / files / file-lines |')
    md.append('|---|---:|---:|---:|---:|')
    fsets = {name: files_of(u) for name, u in layers}
    for name, ua in layers:
        s = st['L:' + name]
        rep.w(f"{name:44s} {f0(s['decls']):>9s} {f0(s['files']):>7s} {f0(s['flines']):>11s} {f0(s['dlines']):>10s}")
    rep.w()
    rep.w('pairwise: shared declarations (row ∩ column); last column = exclusive to the row '
          '(decls / files / file-lines)')
    rep.w(f"{'layer':44s}" + ''.join(f'{i+1:>9d}' for i in range(len(layers))) + f"{'exclusive':>26s}")
    for a, (name, ua) in enumerate(layers):
        row = f'{name:44s}'
        others = None
        for b, (nb, ub) in enumerate(layers):
            if a == b:
                row += f"{'-':>9s}"
                continue
            others = ub if others is None else bop(others, ub, '|')
            row += f'{bcount(bop(ua, ub, "&")):>9d}'
        ex = bop(ua, others, '-')
        exf = files_of(ex)
        exl = sum(idx.mods[idx.mod_name[m]] for m in exf)
        row += f'{bcount(ex):>9d} / {len(exf):>6d} / {exl:>9d}'
        rep.w(row)
        md.append(f"| {name} | {st['L:' + name]['decls']:,} | {st['L:' + name]['files']:,} | "
                  f"{st['L:' + name]['flines']:,} | {bcount(ex):,} / {len(exf):,} / {exl:,} |")
    rep.w()
    rep.w('pairwise: shared files (row ∩ column) / shared file-lines')
    for a, (name, ua) in enumerate(layers):
        la_all = sum(idx.mods[idx.mod_name[m]] for m in fsets[name])
        row = f'{name:44s}'
        for b, (nb, ub) in enumerate(layers):
            if a == b:
                row += f"{'-':>18s}"
                continue
            ib = fsets[name] & fsets[nb]
            lb = sum(idx.mods[idx.mod_name[m]] for m in ib)
            lb_all = sum(idx.mods[idx.mod_name[m]] for m in fsets[nb])
            row += f'{len(ib):>6d} / {100*lb/max(1, lb_all):5.1f}%'
        rep.w(row)
    rep.w()
    union_all = None
    for _, u in layers:
        union_all = u if union_all is None else bop(union_all, u, '|')
    mainc = cones.get('Main.riemannHypothesis')
    if mainc is not None:
        resid = bop(mainc, union_all, '-')
        rf = files_of(resid)
        rep.w(f"union of layers: {f0(bcount(union_all))} decls / {f0(len(files_of(union_all)))} files; "
              f"Main cone: {f0(bcount(mainc))} decls / {f0(len(files_of(mainc)))} files; "
              f"Main minus union (spine + glue): {f0(bcount(resid))} decls / {len(rf)} files")
    rep.w()
    big = [u for name, u in layers if not name.startswith('L1')]
    core = None
    for u in big:
        core = u if core is None else bop(core, u, '&')
    if core is None:
        core = bytearray(len(g.kind))
    cs = cone_stats(g, bits(core))
    st['CORE'] = cs
    rep.w(f"core shared by ALL non-glue layers ({len(big)} layers): {f0(cs['decls'])} decls "
          f"(thm {f0(cs['thm'])}, def {f0(cs['defs'])}) / {f0(cs['files'])} files / "
          f"{f0(cs['flines'])} file-lines / {f0(cs['dlines'])} decl-lines")
    md.append(f"| **core shared by all non-glue layers** | {cs['decls']:,} | {cs['files']:,} | "
              f"{cs['flines']:,} | — |")
    rep.w('   per library (decls / files / file-lines):')
    for k, v in sorted(cs['libs'].items(), key=lambda kv: -kv[1][2]):
        rep.w(f'      {k:58s} {v[0]:>8d} / {v[1]:>6d} / {v[2]:>11d}')
    rep.w('   share of each layer that is core (decls):')
    for name, u in layers:
        if name.startswith('L1'):
            continue
        rep.w(f'      {name:44s} {100*bcount(bop(u, core, "&"))/max(1, bcount(u)):5.1f}%')
    rep.w()

    # ---------------- 5. library breakdown ----------------
    rep.w('## 5. Where the mass is: files and file-lines per library (depth-2 for Development)')
    BIG = [b for b in globals()['BIG'] if b in st] or list(cones)[:1]
    maink = 'Main.riemannHypothesis' if 'Main.riemannHypothesis' in st else BIG[0]
    rep.w(f"{'library':58s}" + ''.join(f'{b.replace("T.",""):>22s}' for b in BIG))
    libs = sorted({k for b in BIG for k in st[b]['libs']},
                  key=lambda k: -st[maink]['libs'][k][2])
    md.append('')
    md.append('| library | ' + ' | '.join('`' + b.replace('T.', '') + '`' for b in BIG) + ' |')
    md.append('|---|' + '---:|' * len(BIG))
    for k in libs:
        row = f'{k:58s}'
        cells = []
        for b in BIG:
            v = st[b]['libs'].get(k, [0, 0, 0])
            row += f"{v[1]:>7d}f {v[2]:>13d}L"
            cells.append(f'{v[1]:,} / {v[2]:,}')
        rep.w(row)
        md.append(f'| {k} | ' + ' | '.join(cells) + ' |')
    rep.w('(cells: files / file-lines)')
    rep.w()
    if mainc is not None:
        rep.w('Development depth-3 directories in the Main cone, by file-lines (top 25):')
        db = dirbreak(idx, bits(mainc), g, 3)
        for k, (nd, nf, nl, dl) in sorted(db.items(), key=lambda kv: -kv[1][2])[:25]:
            rep.w(f'   {k:90s} decls={nd:>8d} files={nf:>7d} lines={nl:>10d}')
        tot_lib = defaultdict(int)
        for m in idx.mods:
            tot_lib[lib2(m)] += 1
        rep.w('whole library vs Main cone, per top-level library (files in cone / files in library):')
        for k in sorted(tot_lib, key=lambda k: -tot_lib[k]):
            v = st[maink]['libs'].get(k, [0, 0, 0])
            rep.w(f'   {k:58s} {v[1]:>7d} / {tot_lib[k]:>7d}  ({100*v[1]/tot_lib[k]:5.1f}%)')
    rep.w()

    # ---------------- 6. spine cost breakdown ----------------
    rep.w('## 6. Cost of each direct input along the spine (cone of the referenced declaration, proof mode)')
    md.append('')
    md.append('| spine theorem | input | kind | decls | files | file-lines |')
    md.append('|---|---|---|---:|---:|---:|')
    for name in SPINE:
        hits = find(idx, name)
        if not hits:
            rep.w(f'!! not found {name}')
            continue
        i = hits[0]
        d = idx.decl[i]
        s, p = g.edges(i, True)
        pset = set(p)
        rep.w(f"### {d[3]}  [{loc(idx, i)}]  stmt refs {len(s)}, proof refs {len(p)}")
        costs = []
        for t in set(s) | pset:
            cs = cone_stats(g, bits(closure(g, [t], 'proof')))
            costs.append((cs['decls'], cs['files'], cs['flines'], t, t in pset))
        costs.sort(reverse=True)
        for nd, nf, nl, t, inp in costs:
            rep.w(f"   {'proof' if inp else 'stmt ':5s} {f0(nd):>8s} decls {nf:>6d} files {f0(nl):>10s} L   "
                  f"{KINDS[g.kind[t]]:9s} {idx.decl[t][3]}   [{loc(idx, t)}]")
            if inp:
                md.append(f"| `{d[3].rsplit('.', 1)[-1]}` | `{idx.decl[t][3]}` | {KINDS[g.kind[t]]} | "
                          f"{nd:,} | {nf:,} | {nl:,} |")
    rep.w()

    # ---------------- 7. hubs ----------------
    rep.w('## 7. Hubs: most-referenced declarations inside the Main cone')
    indeg = Counter()
    if mainc is not None:
        for d in bits(mainc):
            for t in g.stmt[d]:
                if mainc[t]:
                    indeg[t] += 1
            for t in g.proof[d]:
                if mainc[t]:
                    indeg[t] += 1
    rep.w(f"{'in-degree':>9s}  {'kind':9s} name   [location]")
    hubs = []
    md.append('')
    md.append('| in-degree | kind | name | location | lines |')
    md.append('|---:|---|---|---|---:|')
    for t, n in indeg.most_common(30):
        d = idx.decl[t]
        rep.w(f'{n:>9d}  {KINDS[d[2]]:9s} {d[3]}   [{loc(idx, t)}]  ({g.span[t]} lines)')
        hubs.append((n, KINDS[d[2]], d[3], loc(idx, t), g.span[t]))
        md.append(f'| {n:,} | {KINDS[d[2]]} | `{d[3]}` | {loc(idx, t)} | {g.span[t]} |')
    rep.w()

    # ---------------- outputs ----------------
    with open(args.out + '.txt', 'w') as fh:
        fh.write(rep.text())
    md.insert(0, '# mainline_graph tables (generated by analysis/mainline_graph.py)\n')
    with open(args.out + '.md', 'w') as fh:
        fh.write('\n'.join(md) + '\n')
    with open(args.out + '.files.txt', 'w') as fh:
        fh.write('# root\tmodule\tfile-lines\tdecls-in-cone\tcone-file-lines\n'
                 '# (only cones with at most FILELIST_MAX files; bigger ones see the per-library '
                 'tables in mainline_graph.txt)\n')
        for rid in FILELIST:
            if rid not in cones or st[rid]['files'] > FILELIST_MAX:
                continue
            bymod = defaultdict(list)
            for d in bits(cones[rid]):
                bymod[idx.decl[d][0]].append(d)
            for mid in sorted(bymod, key=lambda m: idx.mod_name[m]):
                fh.write(f"{rid}\t{idx.mod_name[mid]}\t{idx.mods[idx.mod_name[mid]]}\t"
                         f"{len(bymod[mid])}\t{st[rid]['flines']}\n")
    out = {'generated': time.strftime('%Y-%m-%d %H:%M:%S'), 'token_stats': dict(g.tokstats),
           'parsed_files': g.n_parsed,
           'cones': {rid: dict(decls=st[rid]['decls'], thm=st[rid]['thm'], defs=st[rid]['defs'],
                               files=st[rid]['files'], flines=st[rid]['flines'], dlines=st[rid]['dlines'],
                               kinds=dict(st[rid]['kinds']), libs={k: v for k, v in st[rid]['libs'].items()},
                               mode=cones_mode[rid],
                               name=next(r['name'] for r in roots if r['id'] == rid))
                    for rid in cones},
           'layers': {name: dict(decls=st['L:' + name]['decls'], files=st['L:' + name]['files'],
                                 flines=st['L:' + name]['flines']) for name, _ in layers},
           'hubs': [dict(indeg=n, kind=k, name=nm, loc=l, lines=s) for n, k, nm, l, s in hubs]}
    with open(args.out + '.json', 'w') as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    if args.gcache:
        with open(args.gcache, 'wb') as fh:
            pickle.dump(dict(stmt=g.stmt, proof=g.proof, span=g.span, done=g.done,
                             n_parsed=g.n_parsed), fh, protocol=5)
        log('wrote pass-B edge cache ' + args.gcache)
    if args.dump:
        with open(args.dump, 'wb') as fh:
            pickle.dump(dict(cones={k: bytes(v) for k, v in cones.items()}, rootids=rootids,
                             stmt=g.stmt, proof=g.proof, span=g.span), fh, protocol=5)
        log('dumped cones + edges to ' + args.dump)
    log(f'wrote {args.out}.txt / .md / .json / .files.txt')


if __name__ == '__main__':
    main()
