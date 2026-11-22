#!/usr/bin/env python3
"""Shared core for the step-6 static analysis of the main line (read-only on source/).

    from depindex import Index
    ix = Index()                       # decls.jsonl -> decls, by_full, by_short, by_mod (pickled)
    i  = ix.find('UpperTheory.Top.VWin')        # -> idx or None
    ix.refs(i, 'full')                 # direct project references (dict idx -> {'full'})
    ix.closure(i, ix.follow_state)     # statement cone (set of idx)

`refs` resolves identifiers textually: namespace stack + `open` aware, strict by default
(ambiguous short names dropped); `loose=True` follows every visible candidate.  Tokens shorter
than MINLEN (bound variables like `x`, `E`) are never followed.
"""
import json, os, pickle, re, sys, time
from collections import defaultdict, deque

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, '..', 'source', 'src'))
CACHE = os.path.join(HERE, '..', '.cache', 'decls_idx_v3.pkl')
MINLEN = 3
ident_re = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")   # ASCII only: same alphabet as decls.jsonl
# projection-style tokens whose head is a non-ASCII (Greek letter) variable: `ψ.ZeroFreeAbove`
ident_greek_re = re.compile(r"(?<![A-Za-z0-9_'.])([^\W\dA-Za-z_])[\w']*\.[A-Za-z_][A-Za-z0-9_']*")
open_re = re.compile(r'^\s*open\s+(?:scoped\s+)?(.*)$')
blank_re = re.compile(r'^\s*$')


def strip_comments(text):
    """Remove Lean comments and string literals (nested block comments handled)."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith('/-', i):
            depth += 1; i += 2; out.append(' '); continue
        if depth and text.startswith('-/', i):
            depth -= 1; i += 2; out.append(' '); continue
        if depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: break
            i = j; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == '\\': j += 1
                j += 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(text[i]); i += 1
    return ''.join(out)


class Index:
    def __init__(self, verbose=True):
        t0 = time.time()
        st = os.stat(os.path.join(HERE, 'decls.jsonl'))
        key = ('v3', st.st_mtime_ns, st.st_size)
        data = None
        if os.path.exists(CACHE):
            try:
                with open(CACHE, 'rb') as fh:
                    d = pickle.load(fh)
                if d.get('key') == key:
                    data = d
            except Exception:
                data = None
        if data is None:
            decls, by_full, by_short, by_mod = [], {}, defaultdict(list), defaultdict(list)
            with open(os.path.join(HERE, 'decls.jsonl')) as fh:
                for line in fh:
                    d = json.loads(line)
                    d['idx'] = len(decls)
                    decls.append(d)
                    by_full.setdefault(d['name'], []).append(d['idx'])
                    by_short[d['short']].append(d['idx'])
                    by_mod[d['mod']].append(d['idx'])
            by_tail = defaultdict(list)          # member -> [(parent, idx)], for projection-style refs `x.member`
            for i, d in enumerate(decls):
                if '.' in d['short']:
                    by_tail[d['short'].rsplit('.', 1)[1]].append((d['short'].rsplit('.', 1)[0], i))   # `def S.member`
                elif d['ns']:
                    by_tail[d['short']].append((d['ns'].split('.')[-1], i))                          # `namespace S` after `structure S`
            data = {'key': key, 'decls': decls, 'by_full': dict(by_full), 'by_short': dict(by_short),
                    'by_mod': dict(by_mod), 'by_tail': dict(by_tail)}
            os.makedirs(os.path.dirname(CACHE), exist_ok=True)
            tmp = CACHE + '.tmp'
            with open(tmp, 'wb') as fh:
                pickle.dump(data, fh, protocol=pickle.HIGHEST_PROTOCOL)
            os.replace(tmp, CACHE)
        self.decls, self.by_full, self.by_short, self.by_mod = (data['decls'], data['by_full'],
                                                                data['by_short'], data['by_mod'])
        self.by_tail = defaultdict(list, data.get('by_tail'))   # old caches: empty (rebuilt on demand)
        self.by_short = defaultdict(list, self.by_short)
        self.by_mod = defaultdict(list, self.by_mod)
        if not self.by_tail or isinstance(next(iter(self.by_tail.values())), int) if self.by_tail else True:
            self.by_tail = defaultdict(list)
            for i, d in enumerate(self.decls):
                if '.' in d['short']:
                    self.by_tail[d['short'].rsplit('.', 1)[1]].append((d['short'].rsplit('.', 1)[0], i))
                elif d['ns']:
                    self.by_tail[d['short']].append((d['ns'].split('.')[-1], i))
        self._vis = {}
        self.file_cache = {}
        self._refcache = {}
        if verbose:
            print(f'depindex: {len(self.decls)} decls loaded in {time.time()-t0:.0f}s', file=sys.stderr)

    # ------------------------------------------------------------ files
    def load_file(self, mod):
        if mod in self.file_cache:
            return self.file_cache[mod]
        path = os.path.join(SRC, mod.replace('.', '/') + '.lean')
        try:
            with open(path, encoding='utf-8', errors='replace') as fh:
                lines = fh.read().split('\n')
        except OSError:
            lines = []
        opens = set()
        for l in lines:
            m = open_re.match(l)
            if m:
                for o in m.group(1).split():
                    if o not in ('in', 'scoped'):
                        opens.add(o)
        idxs = sorted(self.by_mod.get(mod, []), key=lambda i: self.decls[i]['line'])
        spans = {}
        for i in idxs:
            s = self.decls[i]['line']
            if s - 1 >= len(lines):
                spans[i] = (s, s); continue
            ind = len(lines[s-1]) - len(lines[s-1].lstrip())
            e = s
            while e < len(lines):
                l = lines[e]                      # line number e+1
                if not blank_re.match(l) and (len(l) - len(l.lstrip())) <= ind:
                    break
                e += 1
            spans[i] = (s, e)                     # 1-based, lines s..e inclusive
        f = {'lines': lines, 'opens': opens, 'spans': spans, 'path': path}
        self.file_cache[mod] = f
        return f

    def decl_text(self, i, part='full'):
        """part: 'full' | 'stmt' (text before the first top-level ':=' / trailing 'where')"""
        d = self.decls[i]
        f = self.load_file(d['mod'])
        s, e = f['spans'].get(i, (d['line'], d['line']))
        text = strip_comments('\n'.join(f['lines'][s-1:e]))
        if part == 'full' or d['kind'] in ('structure', 'inductive', 'class', 'axiom', 'opaque'):
            return text
        m = re.search(r':=|\bwhere\s*$', text, re.M)
        return text if not m else text[:m.start()]

    # ------------------------------------------------------------ resolution
    def _imports(self):
        if not hasattr(self, '_imp'):
            imp = {}
            with open(os.path.join(HERE, 'imports.jsonl')) as fh:
                for line in fh:
                    r = json.loads(line)
                    imp[r['mod']] = r['imports']
            self._imp = imp
            self._clo = {}
        return self._imp

    def import_closure(self, mod):
        """set of modules transitively imported by `mod` (plus mod itself); cached."""
        self._imports()
        c = self._clo.get(mod)
        if c is not None:
            return c
        seen = {mod}
        q = deque([mod])
        imp = self._imp
        while q:
            m = q.popleft()
            for n in imp.get(m, ()):
                if n not in seen:
                    seen.add(n)
                    q.append(n)
        self._clo[mod] = seen
        return seen

    def visible(self, d, ctx):
        """Is declaration `d` visible by short name at `ctx` (a declaration record)?  Requires (i) its
        module to be (transitively) imported by ctx's module or the same file, and (ii) its namespace
        to be the root, an ancestor-or-equal of ctx's namespace, or opened in ctx's file."""
        ctx_mod, ctx_ns = ctx['mod'], ctx['ns']
        if d['mod'] != ctx_mod and d['mod'] not in self.import_closure(ctx_mod):
            return False
        ns = d['ns']
        if ns == '':
            return True
        if ctx_ns and (ctx_ns == ns or ctx_ns.startswith(ns + '.')):
            return True
        for o in self.load_file(ctx_mod)['opens']:
            if ns == o or ns.endswith('.' + o) or o == '_root_':
                return True
        return False

    def parent_visible(self, P, ctx):
        """Is the short name `P` (a structure/namespace) declared in an ancestor namespace of ctx or in an
        opened namespace of its file?  (i.e. would `P.member` resolve by dot notation there)"""
        key = (ctx['mod'], ctx['ns'], P)
        if key in self._vis:
            return self._vis[key]
        ctx_ns = ctx['ns']
        opens = self.load_file(ctx['mod'])['opens']
        anc = {'.'.join(ctx_ns.split('.')[:k]) for k in range(0, len(ctx_ns.split('.')) + 1)} if ctx_ns else {''}
        ok = False
        for j in self.by_short.get(P, []):
            dj = self.decls[j]
            if dj['mod'] != ctx['mod'] and dj['mod'] not in self.import_closure(ctx['mod']):
                continue
            ns = dj['ns']
            if ns in anc or any(ns == o or ns.endswith('.' + o) for o in opens):
                ok = True
                break
        self._vis[key] = ok
        return ok

    def find(self, name, mod=None):
        c = [i for i in self.by_full.get(name, []) if mod is None or self.decls[i]['mod'] == mod]
        return c[0] if len(c) == 1 else None

    def resolve(self, token, ctx_idx, loose=False, binders=None, minlen=None):
        """binders: map binder name -> head type name (from `refs`), used for `x.member` tokens."""
        ctx = self.decls[ctx_idx]
        if token.startswith('_root_.'):            # absolute name
            token = token[7:]
            if not token:
                return [], 'none'
        if len(token) < (MINLEN if minlen is None else minlen):
            return [], 'short1'
        ctx_ns = ctx['ns']
        if '.' in token:
            c = self.by_full.get(token, [])
            if len(c) == 1:
                return c, 'full'
            if len(c) > 1:
                return c, 'amb'
            parts = ctx_ns.split('.') if ctx_ns else []
            for k in range(len(parts), 0, -1):
                c = self.by_full.get('.'.join(parts[:k] + [token]), [])
                if len(c) == 1:
                    return c, 'full'
                if len(c) > 1:
                    return c, 'amb'
            head, tail = token.split('.', 1)
            out = []
            for h in self.by_short.get(head, []):
                if self.visible(self.decls[h], ctx):
                    out += self.by_full.get(self.decls[h]['name'] + '.' + tail, [])
            if len(out) == 1:
                return out, 'full'
            if out:
                return out, 'amb'
            # projection-style reference `x.member` (x a local variable, lower-case head):
            # member declarations `S.member` whose parent structure/namespace `S` is visible
            if head[:1].islower() and token.count('.') == 1:
                allj = self.by_tail.get(tail, [])
                if not allj:
                    return [], 'none'
                T = (binders or {}).get(head)
                if T:
                    # the receiver's type is declared in the same declaration: only `T.member` can match
                    typed = [j for (parent, j) in allj if parent == T]
                    if len(typed) == 1:
                        return typed, 'full'
                    return (typed, 'amb') if typed else ([], 'none')
                out = [j for (parent, j) in allj if self.parent_visible(parent, ctx)]
                if len(out) == 1:
                    return out, 'full'
                if out:
                    return out, 'amb'
                if len(allj) == 1:          # parent not visibly in scope, but only one `S.member` exists
                    return [allj[0][1]], 'amb'
                return [], 'none'
            return ([], 'none')
        c = [i for i in self.by_short.get(token, [])
             if self.visible(self.decls[i], ctx)]
        if not c:
            return [], 'none'
        return (c, 'short') if len(c) == 1 else (c, 'amb')

    def refs(self, i, part='full', loose=False, minlen=None):
        key = (i, part, loose, minlen)
        if key in self._refcache:
            return self._refcache[key]
        out = defaultdict(set)
        text = self.decl_text(i, part)
        # binder name -> head type name:  `(x : T …)`, `x : T →`, `∀ x : T,`, `fun x : T =>`
        binders = {}
        for m in re.finditer(r"(?:[\(\{\s∀,]|fun\s+)([^\W\d][\w']*|_[^\W\d][\w']*)\s*:\s*(?:∀[^,.]*,\s*)?([^\W\d][\w']*)", text):
            binders.setdefault(m.group(1), m.group(2))
        toks = set(ident_re.findall(text))
        for m in ident_greek_re.finditer(text):
            toks.add(text[m.start():].split()[0] if False else m.group(0))
        for t in toks:
            c, st = self.resolve(t, i, loose, binders, minlen)
            if not c or st == 'short1':
                continue
            if st == 'amb' and not loose:
                continue
            for j in c:
                out[j].add(part)
        self._refcache[key] = out
        return out

    def closure(self, root, follow, loose=False, minlen=None):
        seen = {root}
        q = deque([root])
        while q:
            i = q.popleft()
            for p in follow(i):
                for j in self.refs(i, p, loose, minlen):
                    if j not in seen:
                        seen.add(j)
                        q.append(j)
        return seen

    def follow_state(self, i):
        return ('full',) if self.decls[i]['kind'] not in ('theorem', 'lemma') else ('stmt',)

    def follow_prove(self, i):
        return ('full',)

    def lib_of(self, mod):
        p = mod.split('.')
        return p[0] + ('.' + p[1] if len(p) > 2 else '')

    def summarize(self, seen):
        files = {self.decls[i]['mod'] for i in seen}
        fl = dl = 0
        for i in seen:
            d = self.decls[i]
            s, e = self.load_file(d['mod'])['spans'].get(i, (d['line'], d['line']))
            dl += e - s
        for f in files:
            fl += len(self.load_file(f)['lines'])
        kinds = defaultdict(int)
        libs = defaultdict(int)
        for i in seen:
            kinds[self.decls[i]['kind']] += 1
            libs[self.lib_of(self.decls[i]['mod'])] += 1
        return len(seen), len(files), fl, dl, dict(kinds), dict(libs)
