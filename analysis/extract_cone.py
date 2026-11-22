#!/usr/bin/env python3
"""Draft a Mathlib-only Lean file that *states* a main-line conclusion together with every
project definition its statement needs (TASK.md step 6: "用到的本项目定义一并搬过来").

    python3 extract_cone.py UpperTheory.Top.VWin -o /tmp/cone/VWin.lean [--thms sorry|proof|skip]

Nothing is compiled here.  The statement cone (see depindex.py) is topologically sorted and each
declaration is copied verbatim (comments stripped, `private` removed, name fully qualified) into
its own `section`, preceded by the `variable` / `attribute` / `set_option` commands that were in
scope at its original position and by `open` commands reproducing its namespace + the file's
`open`s.  Theorems that occur as *terms* inside definitions are emitted with `sorry`
(`--thms sorry`, the default), with their proof (`--thms proof`, their own dependencies are then
added to the cone), or not at all (`--thms skip`, for a look at the definitions only).

The draft is meant to be compiled with `lake env lean`; what the compiler still complains about
is exactly what the textual analysis could not see (notation, instances, ambiguous names, ...).
"""
import argparse, os, re, sys, time
from collections import defaultdict, deque, Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depindex import Index, strip_comments, blank_re

decl_head = re.compile(r'^(\s*)((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(theorem|lemma|def|structure|class|abbrev|instance|inductive|opaque)\s+([^\W\d][\w\'.!]*)')
ns_re = re.compile(r'^\s*namespace\s+([^\s]+)')
sec_re = re.compile(r'^\s*(?:private\s+)?section\b')
end_re = re.compile(r'^\s*end\b\s*([^\s]*)')
ctx_re = re.compile(r'^\s*(variable\b|attribute\b|set_option\b|local\b|notation\b|scoped\b|syntax\b|macro\b|macro_rules\b|elab\b|open\b|instance\b|derive\b|@\[)')
MIRROR = 'https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/'


def indent(l):
    return len(l) - len(l.lstrip())


class FileCtx:
    """Per-file scan: block stack snapshots, context commands and opens with their scope."""
    def __init__(self, ix, mod):
        self.ix = ix
        f = ix.load_file(mod)
        self.lines = f['lines']
        self.stack_at = {}        # line -> tuple(stack) at that line (after processing the line)
        self.ctx = []             # (line, snapshot, text, kind)
        self.opens = []           # (line, snapshot, text)   file-level opens
        stack = []
        n = len(self.lines)
        k = 0
        while k < n:
            l = self.lines[k]
            ln = k + 1
            m = ns_re.match(l)
            if m:
                stack.append(m.group(1)); self.stack_at[ln] = tuple(stack); k += 1; continue
            if sec_re.match(l):
                stack.append('§'); self.stack_at[ln] = tuple(stack); k += 1; continue
            m = end_re.match(l)
            if m and stack:
                nm = m.group(1)
                if nm and stack[-1] != nm and stack[-1].split('.')[-1] != nm.split('.')[-1]:
                    # `end A` closing `namespace A.B`? pop until match
                    while stack and stack[-1] != nm and stack[-1].split('.')[-1] != nm.split('.')[-1]:
                        stack.pop()
                if stack:
                    stack.pop()
                self.stack_at[ln] = tuple(stack); k += 1; continue
            if blank_re.match(l):
                self.stack_at[ln] = tuple(stack); k += 1; continue
            # a command: find its extent (until the next non-blank line with indent <= own indent)
            ind = indent(l)
            e = k + 1
            while e < n and (blank_re.match(self.lines[e]) or indent(self.lines[e]) > ind):
                e += 1
            text = '\n'.join(self.lines[k:e])
            snap = tuple(stack)
            first = l.strip()
            if first.startswith('open') and not re.search(r'\bin\s*$', first.split('--')[0]):
                self.opens.append((ln, snap, ' '.join(first.split())))
            elif ctx_re.match(l) and not first.startswith('@[') and not first.startswith('instance'):
                if not first.startswith('local notation') and not first.startswith('notation') and \
                   not first.startswith('scoped notation') and not first.startswith('syntax') and \
                   not first.startswith('macro') and not first.startswith('elab'):
                    self.ctx.append((ln, snap, text, first.split()[0], e))     # e = 0-based end: lines ln..e
            for t in range(k, e):
                self.stack_at[t + 1] = tuple(stack)
            k = e


def in_scope(snap_cmd, line_cmd, snap_decl, line_decl):
    """command declared at (line_cmd, snap_cmd) is in scope for a decl at (line_decl, snap_decl)?"""
    return line_cmd < line_decl and snap_decl[:len(snap_cmd)] == snap_cmd


def qualify(ix, i):
    d = ix.decls[i]
    f = ix.load_file(d['mod'])
    s, e = f['spans'].get(i, (d['line'], d['line']))
    raw = f['lines'][s-1:e]
    first = raw[0]
    m = decl_head.match(first)
    if not m:
        return None
    mods = m.group(2).replace('private', '').replace('protected', '')
    newfirst = f"{m.group(1)}{mods}{m.group(3)} {d['name']}{first[m.end(4):]}"
    body = [newfirst] + raw[1:]
    return strip_comments('\n'.join(body)).rstrip() + '\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root')
    ap.add_argument('--mod', default=None)
    ap.add_argument('-o', '--out', default=None)
    ap.add_argument('--thms', default='sorry', choices=['sorry', 'proof', 'skip'])
    ap.add_argument('--loose', action='store_true')
    ap.add_argument('--minlen', type=int, default=2, help='follow identifiers of at least this length (default 2: Gn, Mt, ...)')
    a = ap.parse_args()
    t0 = time.time()
    ix = Index()
    root = ix.find(a.root, a.mod)
    if root is None:
        c = ix.by_full.get(a.root, [])
        sys.exit(f'root {a.root!r}: {len(c)} candidates: ' + '; '.join(ix.decls[i]["mod"] for i in c[:5]))
    loose = a.loose
    cone = ix.closure(root, ix.follow_state, loose, a.minlen)
    thms = sorted(i for i in cone if ix.decls[i]['kind'] in ('theorem', 'lemma'))
    proof_extra = set()
    if a.thms == 'proof':
        for t in thms:
            proof_extra |= ix.closure(t, ix.follow_prove, loose, a.minlen)
        cone |= proof_extra
    # topological order: DFS post-order on edges inside the cone
    edges = {}
    for i in cone:
        parts = ('full',) if (a.thms == 'proof' or ix.decls[i]['kind'] not in ('theorem', 'lemma')) else ('stmt',)
        edges[i] = [j for p in parts for j in ix.refs(i, p, loose, a.minlen) if j in cone and j != i]
    order, state = [], {}
    def dfs(u):
        state[u] = 1
        for v in edges.get(u, []):
            if state.get(v, 0) == 0:
                dfs(v)
        state[u] = 2
        order.append(u)
    sys.setrecursionlimit(100000)
    dfs(root)
    # ---- emit
    fctx = {}
    proj_all = set()                      # every namespace of the project (to tell Mathlib opens from project ones)
    for d in ix.decls:
        parts_ = (d['ns'].split('.') if d['ns'] else [])
        for k in range(1, len(parts_) + 1):
            proj_all.add('.'.join(parts_[:k]))
    existing = set()                      # namespaces in which something has been emitted so far
    emitted_short = {}                    # short name -> idx of declarations emitted so far
    out = ['/-', f'DRAFT (generated by analysis/extract_cone.py, {time.strftime("%Y-%m-%d %H:%M")}):',
           f'statement of `{ix.decls[root]["name"]}` with the project definitions it needs,',
           f'copied verbatim from the Alpöge–Claude Lean formalization of the Riemann Hypothesis',
           f'(https://alpo.ge/ ; mirror {MIRROR}), so that it compiles against Mathlib only.',
           f'Cone: {len(cone)} declarations in {len({ix.decls[i]["mod"] for i in cone})} files',
           f'({len(thms)} theorems used as terms; mode --thms {a.thms}).',
           'All mathematical credit belongs to Levent Alpöge and Claude.', '-/',
           'import Mathlib', '', 'noncomputable section', '']
    binder_re = re.compile(r"[{(\[]\s*([^\W\d][\w']*|_[^\W\d][\w']*)\s*:|(?<![\w'.])([^\W\d][\w']*|_[^\W\d][\w']*)\s*:\s*(?![=])")

    def var_names(txt):
        """explicit binder names of a `variable` command (rough)"""
        names = set()
        for m in binder_re.finditer(txt):
            names.add(m.group(1) or m.group(2))
        return {n for n in names if n not in ('Type', 'Prop', 'Sort')}

    def word_in(name, text):
        return re.search(r"(?<![A-Za-z0-9_'.])" + re.escape(name) + r"(?![A-Za-z0-9_'])", text) is not None

    for mod in {ix.decls[i]['mod'] for i in cone}:      # file contexts of the whole cone (for global attributes)
        if mod not in fctx:
            fctx[mod] = FileCtx(ix, mod)
    done_attrs = set()

    def emit_global_attrs(just_emitted):
        d = ix.decls[just_emitted]
        short = d['short'].split('.')[-1]
        for mod, fc in fctx.items():
            for (ln, sn, txt, kind, e) in fc.ctx:
                if kind != 'attribute' or 'local' in txt.split(']')[0] or (mod, ln) in done_attrs:
                    continue
                toks = re.findall(r"[^\W\d][\w'.]*", txt.strip().split(']')[-1])
                if not toks:
                    continue
                ok = all((t.split('.')[0] if '.' in t else t) == short for t in toks)
                if ok:
                    qual = txt.strip()
                    for t in sorted(toks, key=len, reverse=True):      # qualify targets (root level: no `open`)
                        head = t.split('.')[0]
                        full = ix.decls[emitted_short[head]]['name'] if head in emitted_short else head
                        qual = re.sub(r"(?<![A-Za-z0-9_'.])" + re.escape(t) + r"(?![A-Za-z0-9_'])", full + t[len(head):], qual)
                    out.append(qual)
                    done_attrs.add((mod, ln))

    for i in order:
        d = ix.decls[i]
        mod = d['mod']
        if mod not in fctx:
            fctx[mod] = FileCtx(ix, mod)
        fc = fctx[mod]
        f = ix.load_file(mod)
        s, e = f['spans'].get(i, (d['line'], d['line']))
        snap_d = fc.stack_at.get(s, tuple(d['ns'].split('.')) if d['ns'] else [])
        text = qualify(ix, i)
        if d['kind'] in ('theorem', 'lemma') and a.thms == 'skip':
            continue
        if text is None:
            out.append(f'-- !! could not parse declaration line of {d["name"]} ({mod}.lean:{s})')
            continue
        if d['kind'] in ('theorem', 'lemma') and a.thms == 'sorry':
            st = ix.decl_text(i, 'stmt')
            m = decl_head.match(st)
            text = f"{m.group(1)}{m.group(2).replace('private', '').replace('protected', '')}{m.group(3)} {d['name']}{st[m.end(4):]}".rstrip() + ' := sorry\n'
        # ---- open commands: ancestors of the namespace (if something exists there) + the file's opens in scope
        ns_parts = d['ns'].split('.') if d['ns'] else []
        anc = ['.'.join(ns_parts[:k]) for k in range(1, len(ns_parts) + 1) if '.'.join(ns_parts[:k]) in existing]
        opens = []
        for (_, sn, o) in fc.opens:
            if not in_scope(sn, _, snap_d, s):
                continue
            m = re.match(r'open\s+(scoped\s+)?(.*)', o)
            sc, names = (m.group(1) or ''), m.group(2).split()
            keep = [nm for nm in names if nm not in proj_all or nm in existing]   # Mathlib ns, or already emitted
            if keep:
                opens.append(('open ' + sc + ' '.join(keep)).strip())
        if anc:
            opens.insert(0, 'open ' + ' '.join(anc))
        # ---- variable / attribute commands in scope, kept when the declaration mentions their names
        decl_text = text
        ctxcmds = []
        all_var_names = set()
        scoped_cmds = [(ln, sn, txt, kind, e) for (ln, sn, txt, kind, e) in fc.ctx if in_scope(sn, ln, snap_d, s)]
        # command-local `… in` commands only apply to the declaration if nothing but blank lines sits between
        scoped_cmds = [c for c in scoped_cmds if not c[2].rstrip().endswith(' in')
                       or all(blank_re.match(l) for l in fc.lines[c[4]:s - 1])]
        local_in = [c for c in scoped_cmds if c[2].rstrip().endswith(' in')]
        scoped_cmds = [c for c in scoped_cmds if not c[2].rstrip().endswith(' in')] + local_in
        for (ln, sn, txt, kind, e) in scoped_cmds:
            if kind == 'variable':
                all_var_names |= var_names(txt)
        seen_ctx = set()
        for (ln, sn, txt, kind, e) in scoped_cmds:
            if txt in seen_ctx:
                continue
            seen_ctx.add(txt)
            if kind == 'variable':
                names = var_names(txt)
                used = any(word_in(n, decl_text) for n in names)
                # instance binders `[Fact g.Prime]` are pulled in automatically when their variables are used
                if not used:
                    idents = re.findall(r"(?<![\w'.])[^\W\d][\w']*", txt)
                    used = any(nm in all_var_names and word_in(nm, decl_text) for nm in idents if nm not in names)
                if used:
                    ctxcmds.append(txt)
            elif kind == 'attribute':
                toks = re.findall(r"[^\W\d][\w'.]*", txt.strip().split(']')[-1])
                tg = [t.split('.')[-1] for t in toks]
                def avail(t):
                    return t in emitted_short or ('.' in toks[tg.index(t)] and toks[tg.index(t)].split('.')[0] in emitted_short)
                if all(avail(t) for t in tg):
                    ctxcmds.append(txt.strip().replace('[local instance]', '[instance]'))
                elif tg:
                    ctxcmds.append('-- (not copied: attribute for ' + ' '.join(tg) + ', which is not in the cone)\n-- ' + txt.strip())
            elif kind == 'set_option':
                ctxcmds.append(txt)                       # harmless (heartbeats, pp)
            else:
                ctxcmds.append(txt)
        out.append(f'-- {mod}.lean:{s}-{e}  {d["kind"]}' + (' (PRIVATE in the original)' if d['private'] else ''))
        out.append('section')
        for o in opens:                 # plain opens: scoped to this section (so `variable` keeps instance binders)
            out.append(o)
        for c in ctxcmds:
            out.append(c)
        out.append(text.rstrip())
        out.append('end')
        out.append('')
        emitted_short[d['short'].split('.')[-1]] = i
        emit_global_attrs(i)
        for k in range(1, len(ns_parts) + 1):
            existing.add('.'.join(ns_parts[:k]))
    out.append('end')
    out.append('')
    res = '\n'.join(out)
    if a.out:
        os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
        with open(a.out, 'w') as fh:
            fh.write(res)
    kinds = Counter(ix.decls[i]['kind'] for i in order)
    summ = ix.summarize(set(order))
    print(f'{a.root}: cone {summ[0]} decls / {summ[1]} files / decl lines {summ[3]}; theorems-as-terms {len(thms)}'
          f'{"; + proof deps " + str(len(proof_extra)) if a.thms == "proof" else ""}; '
          f'kinds {dict(kinds)}; wrote {a.out or "(stdout)"} in {time.time()-t0:.0f}s', file=sys.stderr)
    if not a.out:
        print(res)


if __name__ == '__main__':
    main()
