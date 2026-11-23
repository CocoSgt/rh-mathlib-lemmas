#!/usr/bin/env python3
"""Brute-force checks for the roadmap `CharactersOfGLnOverFiniteFields`.

Everything here follows the definitions of the roadmap's `Suggested.lean` literally and evaluates
them on small groups: `GL₂(𝔽_q)` for several `q`, `GL₃(𝔽₂)` and `GL₃(𝔽₃)`.  Each check prints one
line `ok` or `FAIL`; the exit code is 1 if any check failed.

Usage:  python3 check_green_gl.py [case ...]        cases: gl2_2 gl2_3 gl2_4 gl2_5 gl2_7 gl3_2 gl3_3

Definitions taken from `Suggested.lean` (point for point):
  group            GL (Fin n) F; F_q sits inside one field F_{q^L}, L = lcm(1..n)       (`GL`)
  parabolic a      block upper triangular, block sizes (a, n - a)                    (`parabolic`)
  unipotent a      identity outside the upper-right a × (n - a) block               (`unipotentRadical`)
  pairing          ⟨φ, ψ⟩ = |G|⁻¹ ∑ g, φ g * ψ g⁻¹                                   (`characterPairing`)
  induction        Ind_P f (x) = ∑ over left-coset reps t of f (t⁻¹ x t) [t⁻¹ x t ∈ P] (`indClassFun`)
  hc induction     Ind_P (p ↦ α (Aₚ) * β (Bₚ))                                        (`harishChandraInduct`)
  Jacquet          J χ (m) = |Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ (m * u)                               (`jacquetRestrict`)
  psi              ψ s V g = s (charpoly g) - ∑_{W invariant, W ≠ V} ψ s W (g on W)     (`psi`)
  rootPowerSum     ∑_{P(α) = 0} θ (α) ^ k over the roots in the algebraic closure
  chiK             (-1)^(n-1) • psi (rootPowerSum θ k)                               (`chiK`)

Checks (numbers are the roadmap's sections):
  1.1  number of monic irreducibles of degree n over F_q
  2.2  size and uniqueness of the class with irreducible characteristic polynomial, and of a
       single Jordan block
  2.3  number of subspaces (Gaussian binomial identity)
  2.5  the non-split torus: scalars, elliptic elements, two bases give conjugate embeddings
  3.3  |Uₐ| = q^(a(n-a)), Uₐ ⊆ Pₐ normal, Pₐ = line / hyperplane stabiliser
  4.4  psi = s(charpoly) when charpoly is irreducible
  4.5  mass (psi s) over the fibre of f^m = |G| s(f) / (q^n - 1);  0 when P has two factors
  4.6  psi s at 1 = ∏ (1 - q^i) when s ((X-1)^j) = j
  5.2  ⟨ψ_k, Ψ_l⟩ = #{i < n : k q^i ≡ l [MOD q^n - 1]}   (the |G| factor of the first draft is wrong)
  6.1  ⟨χ_k, χ_k⟩ = 1 for regular k;  6.2 sums over Uₐ vanish;  6.3 degree ∏ (q^i - 1)
  6.5  GL₂ values of χ_k on scalars, Jordan blocks, split regular and elliptic matrices
  7.3  ⟨χ, Ind (α ⊗ β)⟩ = |L|⁻¹ ∑_m J χ (m) α (m₁⁻¹) β (m₂⁻¹)   (the complex-inverse form is wrong)
  7.5  ⟨Ind_P f, Ind_Q h⟩ = Σ_{t ∈ P\\G/Q} ⟨h^t, f⟩_{P ∩ tQt⁻¹} with no scalar factor, for arbitrary
       class functions f on P and h on Q; and for cuspidal data ⟨hcL L, hcL L'⟩ = number of
       bijections between the multisets
  7.6  GL₂: the character table (linear, Steinberg twists, principal series, cuspidal) is orthonormal,
       has q² - 1 rows, and every row pairs nontrivially with hcL of a list of cuspidal characters
  7.11 the number of distinct χ_k (regular k) is the number of monic irreducibles of degree n
"""
from __future__ import annotations

import cmath
import itertools
import math
import random
import sys
import time
from collections import Counter
from functools import lru_cache

TOL = 1e-6


# ============================================================================ finite fields
def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d)
            m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return sorted(fs)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def moebius(n):
    fs = prime_factors(n)
    if math.prod(fs) != n:
        return 0
    return (-1) ** len(fs)


def poly_trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def poly_divmod(a, b, p):
    a = a[:]
    inv = pow(b[-1], -1, p)
    q = [0] * max(0, len(a) - (len(b) - 1))
    while len(a) >= len(b) and any(a):
        d = len(a) - len(b)
        c = a[-1] * inv % p
        q[d] = c
        for i, bc in enumerate(b):
            a[d + i] = (a[d + i] - c * bc) % p
        poly_trim(a)
    return poly_trim(q), a


def poly_gcd(a, b, p):
    a, b = a[:], b[:]
    while any(b):
        _, r = poly_divmod(a, b, p)
        a, b = b, r
    return a


def poly_mulmod(a, b, g, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[i + j] = (r[i + j] + x * y) % p
    return poly_divmod(r, g, p)[1]


def poly_powmod(a, e, g, p):
    r, a = [1], poly_divmod(a, g, p)[1]
    while e:
        if e & 1:
            r = poly_mulmod(r, a, g, p)
        a = poly_mulmod(a, a, g, p)
        e >>= 1
    return r


def irreducible_poly(p, m):
    """The lexicographically first monic irreducible polynomial of degree m over F_p (low first)."""
    if m == 1:
        return [0, 1]
    for low in itertools.product(range(p), repeat=m):
        g = list(low) + [1]
        if poly_powmod([0, 1], p ** m, g, p) != [0, 1]:
            continue
        ok = True
        for t in prime_factors(m):
            h = poly_powmod([0, 1], p ** (m // t), g, p) + [0, 0]
            h[1] = (h[1] - 1) % p          # h = x^(p^(m/t)) - x mod g
            if len(poly_gcd(poly_trim(h), g, p)) > 1:
                ok = False
                break
        if ok:
            return g
    raise RuntimeError


class Field:
    """F_{p^m} = F_p[t]/(g); an element is an int (its base-p digits, low digit first)."""

    def __init__(self, p, m):
        self.p, self.m = p, m
        self.g = irreducible_poly(p, m)
        self.Q = p ** m
        self.digs = [[(a // p ** i) % p for i in range(m)] for a in range(self.Q)]
        self.add = [[0] * self.Q for _ in range(self.Q)]
        self.mul = [[0] * self.Q for _ in range(self.Q)]
        for a in range(self.Q):
            da = self.digs[a]
            for b in range(a, self.Q):
                db = self.digs[b]
                s = sum(((da[i] + db[i]) % p) * p ** i for i in range(m))
                self.add[a][b] = self.add[b][a] = s
                r = [0] * (2 * m - 1)
                for i, x in enumerate(da):
                    if x:
                        for j, y in enumerate(db):
                            if y:
                                r[i + j] = (r[i + j] + x * y) % p
                rem = poly_divmod(r, self.g, p)[1] + [0] * m
                c = sum(rem[i] * p ** i for i in range(m))
                self.mul[a][b] = self.mul[b][a] = c
        self.neg = [sum(((-x) % p) * p ** i for i, x in enumerate(d)) for d in self.digs]
        self.sub = [[self.add[a][self.neg[b]] for b in range(self.Q)] for a in range(self.Q)]
        self.inv = [None] * self.Q
        for a in range(1, self.Q):
            for b in range(1, self.Q):
                if self.mul[a][b] == 1:
                    self.inv[a] = b
                    break
        self.gamma = next(a for a in range(2, self.Q)
                          if all(self.pow(a, (self.Q - 1) // r) != 1 for r in prime_factors(self.Q - 1)))
        self.dlog = [None] * self.Q
        x = 1
        for k in range(self.Q - 1):
            self.dlog[x] = k
            x = self.mul[x][self.gamma]
        self.zeta = cmath.exp(2j * math.pi / (self.Q - 1))
        self._theta_pow = {}

    def pow(self, a, e):
        if a == 0:
            return 1 if e == 0 else 0
        e %= self.Q - 1
        r = 1
        while e:
            if e & 1:
                r = self.mul[r][a]
            a = self.mul[a][a]
            e >>= 1
        return r

    def theta(self, a):
        """A Teichmüller character of the big field: generator ↦ primitive (Q-1)-th root of unity."""
        return 0.0 if a == 0 else self.zeta ** self.dlog[a]

    def theta_pow(self, a, k):
        """θ(a)^k, cached."""
        if (a, k) not in self._theta_pow:
            self._theta_pow[(a, k)] = self.theta(a) ** k
        return self._theta_pow[(a, k)]

    def subfield(self, d):
        return [x for x in range(self.Q) if x == 0 or self.pow(x, self.p ** d) == x]


# ------------------------------------------------------------------------------ polynomials over a Field
def fp_mul(F, a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[i + j] = F.add[r[i + j]][F.mul[x][y]]
    return r


def fp_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def fp_eval(F, a, x):
    r = 0
    for c in reversed(a):
        r = F.add[F.mul[r][x]][c]
    return r


def fp_divmod(F, a, b):
    a = a[:]
    inv = F.inv[b[-1]]
    q = [0] * max(0, len(a) - (len(b) - 1))
    while len(a) >= len(b) and any(a):
        d = len(a) - len(b)
        c = F.mul[a[-1]][inv]
        q[d] = c
        for i, bc in enumerate(b):
            a[d + i] = F.sub[a[d + i]][F.mul[c][bc]]
        fp_trim(a)
    return fp_trim(q), a


def fp_powmod(F, a, e, g):
    r, a = [1], fp_divmod(F, a, g)[1]
    while e:
        if e & 1:
            r = fp_divmod(F, fp_mul(F, r, a), g)[1]
        a = fp_divmod(F, fp_mul(F, a, a), g)[1]
        e >>= 1
    return r


def fp_gcd(F, a, b):
    a, b = a[:], b[:]
    while any(b):
        _, r = fp_divmod(F, a, b)
        a, b = b, r
    if a and a[-1] != 1:
        icc = F.inv[a[-1]]
        a = [F.mul[icc][c] for c in a]
    return a


@lru_cache(maxsize=None)
def fp_roots(F_key, F, a):
    """Roots in F of the monic polynomial a (tuple), with multiplicity, as a tuple of (root, mult)."""
    a = list(a)
    roots = []
    while len(a) > 1:
        x = next((x for x in range(F.Q) if fp_eval(F, a, x) == 0), None)
        if x is None:
            break
        mult = 0
        while True:
            q, r = fp_divmod(F, a, [F.neg[x], 1])
            if r == [0]:
                mult += 1
                a = q
            else:
                break
        roots.append((x, mult))
    return tuple(roots)


def monic_polys(base, n):
    for low in itertools.product(base, repeat=n):
        yield list(low) + [1]


@lru_cache(maxsize=None)
def is_irreducible_over(F, q, P):
    """P (coefficients in F_q ⊂ F, as a tuple) is irreducible over F_q."""
    P = list(P)
    n = len(P) - 1
    if n == 0:
        return False
    x = [0, 1]
    if fp_powmod(F, x, q ** n, P) != fp_divmod(F, x, P)[1]:
        return False
    for t in prime_factors(n):
        h = fp_powmod(F, x, q ** (n // t), P) + [0, 0]
        h[1] = F.sub[h[1]][1]              # h = x^(q^(n/t)) - x mod P
        if len(fp_gcd(F, fp_trim(h), P)) > 1:
            return False
    return True


@lru_cache(maxsize=None)
def fp_factors(F, q, P):
    """Monic irreducible factors over F_q of the monic P with multiplicity."""
    P = fp_trim(list(P))
    out = Counter()
    deg = 1
    while deg <= (len(P) - 1) // 2 and len(P) > 1:
        for f in monic_polys(F.base, deg):
            if not is_irreducible_over(F, q, tuple(f)):
                continue
            while True:
                qq, r = fp_divmod(F, P, f)
                if r == [0]:
                    out[tuple(f)] += 1
                    P = qq
                else:
                    break
        deg += 1
    if len(P) > 1:
        out[tuple(P)] += 1
    return out


# ------------------------------------------------------------------------------ matrices over a Field
def matmul(F, A, B, n):
    C = [0] * (n * n)
    for i in range(n):
        Ai = A[i * n:(i + 1) * n]
        for j in range(n):
            s = 0
            for l in range(n):
                a = Ai[l]
                if a:
                    b = B[l * n + j]
                    if b:
                        s = F.add[s][F.mul[a][b]]
            C[i * n + j] = s
    return tuple(C)


def matvec(F, M, n, v):
    return tuple(sum_row(F, (F.mul[M[i * n + l]][v[l]] for l in range(n))) for i in range(n))


def sum_row(F, it):
    s = 0
    for x in it:
        s = F.add[s][x]
    return s


def det(F, M, n):
    A = [list(M[i * n:(i + 1) * n]) for i in range(n)]
    d = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = F.neg[d]
        d = F.mul[d][A[c][c]]
        icc = F.inv[A[c][c]]
        for r in range(c + 1, n):
            if A[r][c]:
                f = F.mul[A[r][c]][icc]
                for j in range(c, n):
                    A[r][j] = F.sub[A[r][j]][F.mul[f][A[c][j]]]
    return d


def matinv(F, M, n):
    A = [list(M[i * n:(i + 1) * n]) + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c])
        A[c], A[piv] = A[piv], A[c]
        icc = F.inv[A[c][c]]
        A[c] = [F.mul[icc][x] for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [F.sub[A[r][j]][F.mul[f][A[c][j]]] for j in range(2 * n)]
    return tuple(A[i][n + j] for i in range(n) for j in range(n))


def rref(F, rows, ncols):
    """Reduced row echelon form; returns (rows, pivot columns)."""
    A = [r[:] for r in rows]
    k = len(A)
    piv_cols, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, k) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        icc = F.inv[A[r][c]]
        A[r] = [F.mul[icc][x] for x in A[r]]
        for i in range(k):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [F.sub[A[i][j]][F.mul[f][A[r][j]]] for j in range(ncols)]
        piv_cols.append(c)
        r += 1
        if r == k:
            break
    return A, piv_cols


def solve_linear(F, rows, rhs):
    """Solves ∑_i x_i rows[i] = rhs (rows independent); returns x."""
    k, m = len(rows), len(rows[0])
    aug = [list(rows[i]) + [1 if j == i else 0 for j in range(k)] + [0] for i in range(k)]
    aug.append(list(rhs) + [0] * k + [1])
    A, piv = rref(F, aug, m + k + 1)
    if any(A[k][j] for j in range(m)):
        raise ValueError("not in the span")
    coef = A[k][m:]                      # (−x_1, …, −x_k, 1) up to a scalar
    scale = coef[k]
    return tuple(F.neg[F.mul[F.inv[scale]][coef[i]]] for i in range(k))


def charpoly(F, M, n):
    """det(X I - M), coefficients in F, constant term first (length n + 1)."""
    A = [[[F.neg[M[i * n + j]], 1 if i == j else 0] for j in range(n)] for i in range(n)]

    def rec(A):
        k = len(A)
        if k == 1:
            return A[0][0]
        r = [0]
        for j in range(k):
            if any(A[0][j]):
                t = fp_mul(F, A[0][j], rec([[A[i][jj] for jj in range(k) if jj != j] for i in range(1, k)]))
                if j % 2 == 1:
                    t = [F.neg[c] for c in t]
                N = max(len(r), len(t))
                r = r + [0] * (N - len(r))
                t = t + [0] * (N - len(t))
                r = [F.add[r[i]][t[i]] for i in range(N)]
        return r
    d = rec(A)
    return tuple(d + [0] * (n + 1 - len(d)))


# ============================================================================ GL_n(F_q) inside one big field
def in_parabolic(F, M, n, a):
    return all(M[i * n + j] == 0 for i in range(n) for j in range(n) if j < a and a <= i)


def in_unipotent(F, M, n, a):
    return all(M[i * n + j] == (1 if i == j else 0) for i in range(n) for j in range(n) if j < a or a <= i)


def small_span(F, basis, n):
    if not basis:
        yield tuple([0] * n)
        return
    for coeffs in itertools.product(F.base, repeat=len(basis)):
        w = [0] * n
        for c, b in zip(coeffs, basis):
            if c:
                for i in range(n):
                    w[i] = F.add[w[i]][F.mul[c][b[i]]]
        yield tuple(w)


class Universe:
    """One field F_{q^L} containing F_q, and the groups GL_n(F_q) for n = 0..nmax."""

    def __init__(self, q, nmax):
        p = next(d for d in range(2, q + 1) if q % d == 0)
        k = round(math.log(q, p))
        L = math.lcm(*range(1, max(nmax, 1) + 1))
        self.q, self.p, self.nmax = q, p, nmax
        self.F = Field(p, k * L)
        self.F.base = self.F.subfield(k)
        self.groups = {n: Group(self, n) for n in range(0, nmax + 1)}
        self._green = {}

    def green(self, d):
        """(psi_k, chi_k) of GL_d for every index k (dicts g ↦ value)."""
        if d not in self._green:
            G = self.groups[d]
            N = self.q ** d - 1
            psi = {k: psi_values(G, k) for k in range(N)}
            sign = (-1) ** (d - 1)
            chi = {k: {g: sign * v for g, v in psi[k].items()} for k in psi}
            self._green[d] = (psi, chi)
        return self._green[d]


class Group:
    def __init__(self, U, n):
        self.U, self.n, self.F, self.q = U, n, U.F, U.q
        self.elems = [M for M in itertools.product(U.F.base, repeat=n * n) if det(U.F, M, n)]
        self.index = {M: i for i, M in enumerate(self.elems)}
        self.G = len(self.elems)
        self.inv = [matinv(U.F, M, n) for M in self.elems]
        self.one = tuple(1 if i == j else 0 for i in range(n) for j in range(n))
        self._cp, self._cls, self._cache = {}, None, {}

    def charpoly(self, M):
        if M not in self._cp:
            self._cp[M] = charpoly(self.F, M, self.n)
        return self._cp[M]

    def mul(self, A, B):
        return matmul(self.F, A, B, self.n)

    def invm(self, A):
        return self.inv[self.index[A]]

    def classes(self):
        if self._cls is None:
            cls, reps = {}, []
            for M in self.elems:
                if M in cls:
                    continue
                reps.append(M)
                for h in self.elems:
                    cls[self.mul(self.mul(h, M), self.invm(h))] = len(reps) - 1
            self._cls, self.reps = cls, reps
        return self._cls, self.reps

    def conjugate(self, A, B):
        cls, _ = self.classes()
        return cls[A] == cls[B]

    def pairing(self, phi, psi):
        s = 0j
        for M in self.elems:
            s += phi(M) * psi(self.inv[self.index[M]])
        return s / self.G

    def parabolic(self, a):
        return self._sub("P", a, lambda M: in_parabolic(self.F, M, self.n, a))

    def unipotent(self, a):
        return self._sub("U", a, lambda M: in_unipotent(self.F, M, self.n, a))

    def _sub(self, kind, a, pred):
        key = (kind, a)
        if key not in self._cache:
            self._cache[key] = [M for M in self.elems if pred(M)]
        return self._cache[key]

    def subspaces(self):
        """All subspaces of F_q^n: dict frozenset(points) -> basis (tuple of row-reduced vectors)."""
        if "S" not in self._cache:
            F, n = self.F, self.n
            vecs = [v for v in itertools.product(F.base, repeat=n) if any(v)]
            subs = {}
            for r in range(0, n + 1):
                for S in itertools.combinations(vecs, r):
                    rows, piv = rref(F, [list(v) for v in S], n)
                    basis = tuple(tuple(rows[i]) for i in range(len(piv)))
                    subs[frozenset(small_span(F, basis, n))] = basis
            self._cache["S"] = subs
        return self._cache["S"]

    def whole(self):
        return frozenset(small_span(self.F, [self.one[i * self.n:(i + 1) * self.n] for i in range(self.n)], self.n))


# ============================================================================ class-function plumbing
def coset_reps(G, P):
    seen, reps = set(), []
    for g in G.elems:
        if g in seen:
            continue
        reps.append(g)
        for p in P:
            seen.add(G.mul(g, p))
    return reps


def induce(G, P, f):
    """Subgroup.indClassFun P f: x ↦ ∑_t f (t⁻¹ x t) over left-coset reps t with t⁻¹ x t ∈ P."""
    reps = coset_reps(G, P)
    Pset = set(P)
    cache = {}

    def ind(x):
        if x not in cache:
            s = 0j
            for t in reps:
                c = G.mul(G.mul(G.invm(t), x), t)
                if c in Pset:
                    s += f(c)
            cache[x] = s
        return cache[x]
    return ind


def zero(_):
    return 0j


def const_one(_):
    return 1 + 0j


def blocks(G, M, a, b):
    n = G.n
    return (tuple(M[i * n + j] for i in range(a) for j in range(a)),
            tuple(M[(a + i) * n + (a + j)] for i in range(b) for j in range(b)))


def block_diag(G, A, B, a, b):
    n = a + b
    M = [0] * (n * n)
    for i in range(a):
        for j in range(a):
            M[i * n + j] = A[i * a + j]
    for i in range(b):
        for j in range(b):
            M[(a + i) * n + (a + j)] = B[i * b + j]
    return tuple(M)


def harish_chandra_induct(U, a, b, alpha, beta):
    """`harishChandraInduct (a + b) a b rfl α β`, a class function on GL_(a+b)."""
    G = U.groups[a + b]
    return induce(G, G.parabolic(a), lambda p: alpha(blocks(G, p, a, b)[0]) * beta(blocks(G, p, a, b)[1]))


def hcL(U, L, n):
    """`hcL L n` for a list L of pairs (d, class function on GL_d)."""
    s = sum(d for d, _ in L)
    if not L:
        return const_one if n == 0 else zero
    (d, cf), rest = L[0], L[1:]
    if s != n:
        return zero
    return harish_chandra_induct(U, d, n - d, cf, hcL(U, rest, n - d))


def jacquet(G, chi, a, b):
    """`jacquetRestrict n a b rfl χ`, as a function on pairs (m₁ ∈ GL_a, m₂ ∈ GL_b)."""
    Ua = G.unipotent(a)
    N = len(Ua)
    cache = {}

    def J(m):
        if m not in cache:
            M0 = block_diag(G, m[0], m[1], a, b)
            cache[m] = sum((chi(G.mul(M0, u)) for u in Ua), 0j) / N
        return cache[m]
    return J


def double_cosets(G, P, Q):
    """Representatives of the double cosets P \\ G / Q.  A double coset P g Q is a union of right cosets
    P (g q), q ∈ Q, so each new representative g only has to mark the right cosets of the elements g q."""
    # P g Q = ⋃_{q ∈ Q} (P g q) is a union of right cosets P (g q): index the right cosets P x
    cid, r = {}, 0
    for g in G.elems:
        if g not in cid:
            for p in P:
                cid[G.mul(p, g)] = r
            r += 1
    seen, reps = set(), []
    for g in G.elems:
        if cid[g] in seen:
            continue
        reps.append(g)
        for q in Q:
            seen.add(cid[G.mul(g, q)])
    return reps


def pairing_over(G, R, phi, psi):
    """Tau Ceti's pairing restricted to a subgroup R: |R|⁻¹ ∑_{x ∈ R} φ x * ψ x⁻¹."""
    return sum((phi(x) * psi(G.invm(x)) for x in R), 0j) / len(R)


def random_class_function(G, seed):
    """A random class function on G."""
    cls, reps = G.classes()
    rnd = random.Random(seed)
    vals = {r: complex(rnd.uniform(-2, 2), rnd.uniform(-2, 2)) for r in reps}
    return lambda M: vals[reps[cls[M]]]


def random_class_function_on(G, S, seed):
    """A random class function on the subgroup S (constant under conjugation by elements of S)."""
    rnd = random.Random(seed)
    Sset, vals, done = set(S), {}, set()
    for x in S:
        if x in done:
            continue
        v = complex(rnd.uniform(-2, 2), rnd.uniform(-2, 2))
        for h in S:
            c = G.mul(G.mul(h, x), G.invm(h))
            if c not in done:
                done.add(c)
                vals[c] = v
    return vals


# ============================================================================ Green's construction
def invariant_subspaces(G, g):
    F, n = G.F, G.n
    return [(pts, basis) for pts, basis in G.subspaces().items()
            if all(matvec(F, g, n, b) in pts for b in basis)]


def psi_values(G, k):
    """`g ↦ psi (rootPowerSum θ k) (Fin n → F) g` for all g ∈ G."""
    F = G.F
    data = G._cache.get(("mob", ))
    if data is None:
        data = {}
        for g in G.elems:
            inv = invariant_subspaces(G, g)
            cps = {}
            for pts, basis in inv:
                if len(basis) == G.n:
                    cps[pts] = G.charpoly(g)
                else:
                    B = [solve_linear(F, [list(b) for b in basis], list(matvec(F, g, G.n, b))) for b in basis]
                    R = tuple(B[j][i] for i in range(len(basis)) for j in range(len(basis)))
                    cps[pts] = tuple(charpoly(F, R, len(basis)))
            data[g] = (inv, cps)
        G._cache[("mob", )] = data
    whole = G.whole()
    out = {}
    for g, (inv, cps) in data.items():
        val = {}
        for pts, basis in sorted(inv, key=lambda t: len(t[1])):
            v = root_power_sum(F, k, cps[pts])
            for pts2, _ in inv:
                if pts2 < pts and len(pts2) < len(pts):
                    v -= val[pts2]
            val[pts] = v
        out[g] = val[whole]
    return out


def root_power_sum(F, k, P):
    """`rootPowerSum θ k P` for the Teichmüller character θ of F."""
    return complex(sum(m * F.theta_pow(x, k) for x, m in fp_roots(id(F), F, tuple(P))))


def is_regular(q, n, k):
    N = q ** n - 1
    return all((k * q ** i - k) % N != 0 for i in range(1, n))


# ============================================================================ the checks
class Checker:
    def __init__(self, title):
        self.title, self.count, self.fails, self.bad = title, 0, 0, []
        print(f"\n== {title}")

    def check(self, name, cond, info=""):
        self.count += 1
        if cond:
            print(f"ok    {name}  {info}")
        else:
            self.fails += 1
            self.bad.append(name)
            print(f"FAIL  {name}  {info}")

    def close(self, name, val, target, info=""):
        err = abs(val - target)
        self.check(name, err < TOL, f"{info} value={complex(val):.6g} target={complex(target):.6g}")

    def done(self):
        print(f"== {self.title}: {self.count - self.fails}/{self.count} checks passed")
        return self.fails


ONLY_DC = False      # run only the double-coset count check (the cheap item, for the big cases)


def check_group(U, n, C):
    q, F = U.q, U.F
    G = U.groups[n]
    t0 = time.time()
    tag = f"GL_{n}(F_{q})"

    # ---------------------------------------------------------------- 7.5 the double cosets of two parabolics are indexed by matrices
    if n >= 2:
        comps_all = compositions(n)
        for lam, mu in itertools.product(comps_all, comps_all):
            Pl, Pm = parabolic_composition(G, lam), parabolic_composition(G, mu)
            ndc = len(double_cosets(G, Pl, Pm))
            target = count_index_matrices(lam, mu)
            C.check(f"7.5 [{tag}] #{{P_λ\\G/P_μ}} = #{{nonneg. integer matrices with row sums λ, column sums μ}}, λ={lam}, μ={mu}",
                    ndc == target, f"{ndc} vs {target}")
    if ONLY_DC:
        print(f"   ({tag}: {time.time() - t0:.1f}s)")
        return

    # ---------------------------------------------------------------- 3.3
    for a in range(n + 1):
        P, Ua = G.parabolic(a), G.unipotent(a)
        Pset, Uset = set(P), set(Ua)
        C.check(f"3.3 [{tag}] |U_{a}| = q^(a(n-a))", len(Ua) == q ** (a * (n - a)), f"{len(Ua)} vs {q ** (a * (n - a))}")
        C.check(f"3.3 [{tag}] U_{a} ⊆ P_{a} and U_{a} is normal in P_{a}",
                Uset <= Pset and all(G.mul(G.mul(p, u), G.invm(p)) in Uset for p in P for u in Ua))
        C.check(f"3.3 [{tag}] |P_{a}| = q^(a(n-a)) |GL_{a}| |GL_{n - a}|",
                len(P) == q ** (a * (n - a)) * U.groups[a].G * U.groups[n - a].G, f"{len(P)}")
        C.check(f"3.3 [{tag}] P_{a} is a subgroup", all(G.mul(p1, p2) in Pset for p1 in P for p2 in P[:50]))
    if n >= 2:
        e0 = tuple(1 if i == 0 else 0 for i in range(n))
        line_stab = [M for M in G.elems if all(matvec(F, M, n, e0)[i] == 0 for i in range(1, n))]
        C.check(f"3.3 [{tag}] P_1 = stabiliser of the first coordinate line", set(G.parabolic(1)) == set(line_stab))
        hyp_stab = [M for M in G.elems if all(M[(n - 1) * n + j] == 0 for j in range(n - 1))]
        C.check(f"3.3 [{tag}] P_(n-1) = stabiliser of the last coordinate hyperplane",
                set(G.parabolic(n - 1)) == set(hyp_stab))

    # ---------------------------------------------------------------- 1.1, 2.2, 2.3
    irrs = [P for P in monic_polys(F.base, n) if is_irreducible_over(F, q, tuple(P))]
    n_theo = sum(moebius(d) * q ** (n // d) for d in divisors(n)) // n
    C.check(f"1.1 [{tag}] number of monic irreducibles of degree {n}", len(irrs) == n_theo, f"{len(irrs)} vs {n_theo}")
    irrs_unit = [P for P in irrs if P[0] != 0]
    C.check(f"1.1 [{tag}] among them, the ones with nonzero constant term: q - 1 for n = 1, all for n ≥ 2",
            len(irrs_unit) == (q - 1 if n == 1 else len(irrs)), f"{len(irrs_unit)}")
    for a in range(n + 1):
        na = sum(1 for _, b in G.subspaces().items() if len(b) == a)
        C.check(f"2.3 [{tag}] G({n},{a})", na * math.prod(q ** a - q ** i for i in range(a)) == math.prod(q ** n - q ** i for i in range(a)),
                f"{na} subspaces")
    cls, _ = G.classes()
    for P in irrs:
        if P[0] == 0:
            continue
        fibre = [M for M in G.elems if G.charpoly(M) == tuple(P)]
        target = G.G // (q ** n - 1)
        C.check(f"2.2 [{tag}] class with irreducible charpoly (one class of size |G|/(q^n-1))",
                len(fibre) == target and len({cls[M] for M in fibre}) == 1, f"{len(fibre)} vs {target}")
    for a_ in F.base:
        if a_ == 0 or n < 2:
            continue
        J = tuple(a_ if i == j else (1 if j == i + 1 else 0) for i in range(n) for j in range(n))
        fibre = [M for M in G.elems if G.conjugate(M, J)]
        target = G.G // (q ** (n - 1) * (q - 1))
        C.check(f"2.2 [{tag}] class of a single Jordan block J_{n}(a) (size |G|/(q^(n-1)(q-1)))", len(fibre) == target, f"{len(fibre)} vs {target}")

    # ---------------------------------------------------------------- 2.5
    if n >= 2:
        check_ns_torus(U, n, C, tag)

    # ---------------------------------------------------------------- 4.x, 5.x, 6.x
    N = q ** n - 1
    psi, chi = U.green(n)
    by_cp = {}
    for M in G.elems:
        by_cp.setdefault(G.charpoly(M), []).append(M)
    for k in range(N):
        s = lambda P, k=k: root_power_sum(F, k, P)
        ok44 = all(abs(psi[k][M] - s(G.charpoly(M))) <= TOL for M in G.elems if is_irreducible_over(F, q, tuple(G.charpoly(M))))
        C.check(f"4.4 [{tag}] psi_k = rootPowerSum_k (charpoly) on irreducible charpoly, k={k}", ok44)
        C.close(f"4.6 [{tag}] psi_k at the identity, k={k}", psi[k][G.one], math.prod(1 - q ** i for i in range(1, n)))
        ok_irr = ok_mult = ok_split = True
        for cp, Ms in by_cp.items():
            fac = fp_factors(F, q, tuple(cp))
            mass = sum(psi[k][M] for M in Ms)
            if len(fac) == 1:
                f = next(iter(fac))
                target = G.G * s(list(f)) / (q ** n - 1)
                if abs(mass - target) > TOL:
                    if sum(fac.values()) == 1:
                        ok_irr = False
                    else:
                        ok_mult = False
            elif abs(mass) > TOL:
                ok_split = False
        C.check(f"4.5 [{tag}] mass (psi_k) over the fibre of an irreducible f = |G| s(f)/(q^n-1), k={k}", ok_irr)
        C.check(f"4.5 [{tag}] mass (psi_k) over the fibre of f^m, m ≥ 2, = |G| s(f)/(q^n-1), k={k}", ok_mult)
        C.check(f"4.5 [{tag}] mass (psi_k) = 0 when the charpoly has ≥ 2 irreducible factors, k={k}", ok_split)
    for k in range(N):
        for l in range(N):
            val = G.pairing(lambda M, k=k: psi[k][M], lambda M, l=l: root_power_sum(F, l, G.charpoly(M)))
            C.close(f"5.2 [{tag}] <psi_{k}, Psi_{l}> = #{{i < n : k q^i ≡ l}}", val, sum(1 for i in range(n) if (k * q ** i - l) % N == 0))
    if n >= 2:
        C.check(f"5.2 [{tag}] the first draft's |G| * #{{…}} is not the pairing (k = l = 1)",
                abs(G.pairing(lambda M: psi[1][M], lambda M: root_power_sum(F, 1, G.charpoly(M))) - G.G) > 0.5)
    distinct = set()
    for k in range(N):
        if not is_regular(q, n, k):
            continue
        C.close(f"6.1 [{tag}] <chi_{k}, chi_{k}> = 1 (k regular)", G.pairing(lambda M, k=k: chi[k][M], lambda M, k=k: chi[k][M]), 1)
        C.close(f"6.3 [{tag}] chi_{k}(1) = ∏_(i<n) (q^i - 1)", chi[k][G.one], math.prod(q ** i - 1 for i in range(1, n)))
        C.check(f"3.4/6.2 [{tag}] sums of chi_{k} over every U_a vanish, a = 1..n-1",
                all(abs(sum(chi[k][M] for M in G.unipotent(a))) < TOL for a in range(1, n)))
        distinct.add(tuple(round(v.real, 5) + round(v.imag, 5) * 1j for v in (chi[k][M] for M in G.elems)))
    C.check(f"7.11 [{tag}] #distinct chi_k (regular k) = #monic irreducibles of degree n with nonzero constant term",
            len(distinct) == len(irrs_unit), f"{len(distinct)} vs {len(irrs_unit)}")
    if n == 2:
        for k in range(N):
            if not is_regular(q, 2, k):
                continue
            for M in G.elems:
                cp = G.charpoly(M)
                if is_irreducible_over(F, q, cp):
                    z = next(iter(fp_roots(id(F), F, tuple(cp))))[0]
                    C.close(f"6.5 [{tag}] elliptic value of chi_{k}", chi[k][M], -sum(F.theta_pow(F.pow(z, q ** i), k) for i in range(2)))
                elif M[1] == 0 and M[2] == 0 and M[0] == M[3]:
                    C.close(f"6.5 [{tag}] scalar value of chi_{k}", chi[k][M], (q - 1) * F.theta_pow(M[0], k))
                elif len(fp_roots(id(F), F, tuple(cp))) == 1:
                    a = fp_roots(id(F), F, tuple(cp))[0][0]
                    C.close(f"6.5 [{tag}] Jordan value of chi_{k}", chi[k][M], -F.theta_pow(a, k))
                else:
                    C.close(f"6.5 [{tag}] split-regular value of chi_{k}", chi[k][M], 0)
        C.check(f"3.6 [{tag}] chi_k vanishes off the primary elements",
                all(abs(chi[k][M]) < TOL for k in range(N) if is_regular(q, 2, k) for M in G.elems
                    if len(fp_factors(F, q, tuple(G.charpoly(M)))) >= 2))

    # ---------------------------------------------------------------- 7.3
    for a in range(1, n):
        b = n - a
        Ga, Gb = U.groups[a], U.groups[b]
        alpha, beta = random_class_function(Ga, 101 + a), random_class_function(Gb, 202 + b)
        chi_n = random_class_function(G, 303)
        lhs = G.pairing(chi_n, harish_chandra_induct(U, a, b, alpha, beta))
        J = jacquet(G, chi_n, a, b)
        rhs = rhs_old = 0j
        for m1 in Ga.elems:
            for m2 in Gb.elems:
                t = J((m1, m2))
                rhs += t * alpha(Ga.invm(m1)) * beta(Gb.invm(m2))
                rhs_old += t / (alpha(m1) * beta(m2))
        rhs /= Ga.G * Gb.G
        rhs_old /= Ga.G * Gb.G
        C.close(f"7.3 [{tag}] <χ, Ind (α ⊗ β)> = |L|⁻¹ ∑_m J χ (m) α (m₁⁻¹) β (m₂⁻¹), a={a}", lhs, rhs)
        C.check(f"7.3 [{tag}] the form with (α m₁ * β m₂)⁻¹ (complex inverse) is different, a={a}", abs(rhs_old - rhs) > 1e-3,
                f"{rhs_old:.4f} vs {rhs:.4f}")

    # ---------------------------------------------------------------- 7.5 Mackey, arbitrary class functions on two parabolics
    comps = [(a, n - a) for a in range(1, n)]
    for (a, b), (c, d) in itertools.product(comps, comps):
        P, Q = G.parabolic(a), G.parabolic(c)
        fvals, hvals = random_class_function_on(G, P, 11 * a + b), random_class_function_on(G, Q, 17 * c + d)
        lhs = G.pairing(induce(G, P, lambda x: fvals[x]), induce(G, Q, lambda x: hvals[x]))
        Qset, total, nz, sizes = set(Q), 0j, 0, []
        for t in double_cosets(G, P, Q):
            ti = G.invm(t)
            Rt = [p for p in P if G.mul(G.mul(ti, p), t) in Qset]
            # <h^t, f>_(P ∩ tQt⁻¹) with h^t (y) = h (t⁻¹ y t)   (Subgroup.indClassFun_mackey)
            v = pairing_over(G, Rt, lambda x: hvals[G.mul(G.mul(ti, x), t)], lambda x: fvals[x])
            total += v
            nz += abs(v) > TOL
            sizes.append(len(Rt))
        C.close(f"7.5 [{tag}] Mackey, no scalar: <Ind_P f, Ind_Q h> = Σ_t <h^t, f>_(P∩tQt⁻¹), P=({a},{b}), Q=({c},{d})",
                lhs, total, f"{len(sizes)} double cosets ({nz} with nonzero pairing), |P∩tQt⁻¹| = {sorted(set(sizes))}")

    # ---------------------------------------------------------------- 7.5 with cuspidal data; 7.6
    lin = {k: (lambda M, k=k: F.theta_pow(M[0], k)) for k in range(q - 1)}
    if n >= 2:
        cusp = {1: lin}
        for d in range(2, n + 1):
            _, chid = U.green(d)
            cusp[d] = {k: (lambda M, k=k, chid=chid: chid[k][M]) for k in range(q ** d - 1) if is_regular(q, d, k)}

        def label(L):
            return Counter((d, canon_label(U, d, k)) for d, k in L)

        lists = [[(1, k) for k in combo] for combo in itertools.combinations_with_replacement(range(q - 1), n)]
        for d in range(2, n):
            for k in cusp[d]:
                for combo in itertools.combinations_with_replacement(range(q - 1), n - d):
                    lists.append([(d, k)] + [(1, k1) for k1 in combo])
        lists += [[(n, k)] for k in cusp[n]]
        fns = [hcL(U, [(d, cusp[d][k]) for d, k in L], n) for L in lists]
        labels = [label(L) for L in lists]
        bad = bad_special = 0
        for i in range(len(lists)):
            for j in range(i, len(lists)):
                val = G.pairing(fns[i], fns[j])
                if abs(val - bijections(labels[i], labels[j])) > TOL:
                    bad += 1
                if labels[i] == labels[j] and all(m == 1 for m in labels[i].values()):
                    if abs(val - 1) > TOL:
                        bad_special += 1
                        print(f"      (same multiset, nodup, pairing {val:.6g}: {lists[i]} vs {lists[j]})")
                elif labels[i] != labels[j]:
                    if abs(val) > TOL:
                        bad_special += 1
                        print(f"      (different multisets, pairing {val:.6g}: {lists[i]} vs {lists[j]})")
        C.check(f"7.5 [{tag}] <hcL L, hcL L'> = number of degree-preserving bijections of the multisets, over all pairs of {len(lists)} cuspidal lists",
                bad == 0, f"{bad} failures")
        C.check(f"7.5 [{tag}] = 1 for the same multiset without repetition and = 0 for different multisets", bad_special == 0, f"{bad_special} failures")
        # hcL L n = Ind_{P_λ} (⊗ of the entries), λ the composition of the degrees of L (induction in stages)
        ok_stage = True
        for i, L in enumerate(lists):
            lam = tuple(d for d, _ in L)
            Pl = parabolic_composition(G, lam)
            def infl(p, L=L):
                # diagonal blocks of p for the composition of L
                v, off = 1 + 0j, 0
                for d, k in L:
                    blk = tuple(p[(off + r) * n + off + c] for r in range(d) for c in range(d))
                    v *= cusp[d][k](blk)
                    off += d
                return v
            g = induce(G, Pl, infl)            # built once per list
            if any(abs(fns[i](M) - g(M)) > TOL for M in G.elems):
                ok_stage = False
        C.check(f"7.1 [{tag}] hcL L n = Ind_(P_λ) (α₁ ⊗ … ⊗ α_r), λ = composition of the degrees of L ({len(lists)} lists)", ok_stage)
        # Mackey term by term: each double coset contributes 0 or 1; the number of contributing ones is
        # the number of degree-preserving bijections matching the entries
        dc_cache = {}
        def terms(L, Lp):
            lam, mu = tuple(d for d, _ in L), tuple(d for d, _ in Lp)
            key = (lam, mu)
            if key not in dc_cache:
                Pl, Pm = parabolic_composition(G, lam), parabolic_composition(G, mu)
                Pmset = set(Pm)
                dc_cache[key] = [(t, [p for p in Pl if G.mul(G.mul(G.invm(t), p), t) in Pmset])
                                 for t in double_cosets(G, Pl, Pm)]
            def inflate(L, p):
                v, off = 1 + 0j, 0
                for d, k in L:
                    blk = tuple(p[(off + r) * n + off + c] for r in range(d) for c in range(d))
                    v *= cusp[d][k](blk)
                    off += d
                return v
            out = []
            for t, Rt in dc_cache[key]:
                ti = G.invm(t)
                out.append(pairing_over(G, Rt, lambda x: inflate(Lp, G.mul(G.mul(ti, x), t)), lambda x: inflate(L, x)))
            return out
        bad_terms = 0
        pairs_to_test = [(i, i) for i in range(len(lists))]
        pairs_to_test += [(i, j) for i in range(len(lists)) for j in range(len(lists)) if i < j and
                          (lists[i][0][0] != lists[j][0][0] or canon_label(U, n, 0) is None)][:12]
        for i, j in pairs_to_test:
            ts = terms(lists[i], lists[j])
            if any(abs(v - round(v.real)) > TOL or abs(v.imag) > TOL for v in ts):
                bad_terms += 1
            if sum(1 for v in ts if abs(v) > TOL) != bijections(labels[i], labels[j]):
                bad_terms += 1
        C.check(f"7.5 [{tag}] Mackey term by term: every double coset contributes 0 or 1, and the contributing ones are the matching bijections ({len(pairs_to_test)} pairs)", bad_terms == 0, f"{bad_terms} failures")
        # transitivity: the order of the list does not matter
        if len(lists) > 1 and n >= 3 and len(cusp[2]) and q > 2:
            L1 = [(2, next(iter(cusp[2]))), (1, 1)]
            L2 = L1[::-1]
            f1, f2 = hcL(U, [(d, cusp[d][k]) for d, k in L1], n), hcL(U, [(d, cusp[d][k]) for d, k in L2], n)
            C.check(f"7.1 [{tag}] hcL of a list and of its reversal are the same class function", all(abs(f1(M) - f2(M)) < TOL for M in G.elems))
        if n == 2:
            check_gl2_table(U, G, cusp, lin, fns, labels, C, tag)
    print(f"   ({tag}: {time.time() - t0:.1f}s)")


def compositions(n):
    if n == 0:
        return [()]
    out = []
    for i in range(1, n + 1):
        for rest in compositions(n - i):
            out.append((i,) + rest)
    return out


def parabolic_composition(G, comp):
    """The parabolic subgroup with block sizes `comp` (block upper triangular for that composition)."""
    F, n = G.F, G.n
    blk = []
    for i, c in enumerate(comp):
        blk += [i] * c

    def pred(M):
        return all(M[i * n + j] == 0 for i in range(n) for j in range(n) if blk[i] > blk[j])
    return [M for M in G.elems if pred(M)]


def count_index_matrices(lam, mu):
    """Number of nonnegative integer matrices with row sums lam and column sums mu."""
    cols = len(mu)

    def rows_with_sum(total, caps):
        if cols == 1:
            if 0 <= total <= caps[0]:
                yield (total,)
            return

        def rec(j, rem, acc):
            if j == cols - 1:
                if 0 <= rem <= caps[j]:
                    yield tuple(acc + [rem])
                return
            for x in range(0, min(rem, caps[j]) + 1):
                yield from rec(j + 1, rem - x, acc + [x])
        yield from rec(0, total, [])

    def rec(i, cols_left):
        if i == len(lam) - 1:
            return 1 if all(x >= 0 for x in cols_left) and sum(cols_left) == lam[i] else 0
        return sum(rec(i + 1, [c - x for c, x in zip(cols_left, row)]) for row in rows_with_sum(lam[i], cols_left))
    return rec(0, list(mu))


def canon_label(U, d, k):
    """Frobenius-orbit representative of the index k: Green characters of GL_d agree on the orbit."""
    N = U.q ** d - 1
    return min((k * U.q ** i) % N for i in range(d))


def bijections(ci, cj):
    if ci != cj:
        return 0
    r = 1
    for _, m in ci.items():
        r *= math.factorial(m)
    return r


def check_ns_torus(U, n, C, tag):
    """2.5: K = F_{q^n} in the big field; two bases give conjugate embeddings; scalars; elliptic elements."""
    F, q = U.F, U.q
    G = U.groups[n]
    k = round(math.log(q, F.p))
    K = F.subfield(k * n)
    e = []
    for x in F.base:
        if independent_digits(F, e + [x]):
            e.append(x)
    b1 = independent_over(F, K, e, n)
    b2 = independent_over(F, K, e, n, skip=len(b1))
    if len(b2) != n or b2 == b1:
        b2 = [b1[-1]] + b1[:-1]

    def embedding(basis):
        def emb(u):
            cols = [coords_over(F, basis, F.mul[u][v], e) for v in basis]
            return tuple(cols[j][i] for i in range(n) for j in range(n))
        return emb
    e1, e2 = embedding(b1), embedding(b2)
    Qm = tuple(coords_over(F, b1, v, e)[i] for i in range(n) for v in b2)
    Qi = matinv(F, Qm, n)
    C.check(f"2.5 [{tag}] two bases give conjugate embeddings of the non-split torus Kˣ → GL_n(F_q)",
            all(G.mul(G.mul(Qm, e1(u)), Qi) == e2(u) for u in K if u) or all(G.mul(G.mul(Qi, e1(u)), Qm) == e2(u) for u in K if u))
    C.check(f"2.5 [{tag}] F_qˣ goes to the scalar matrices", all(e1(u) == tuple(u if i == j else 0 for i in range(n) for j in range(n)) for u in F.base if u))
    C.check(f"2.5 [{tag}] the embedding is injective and multiplicative",
            len({e1(u) for u in K if u}) == len(K) - 1 and all(G.mul(e1(u), e1(v)) == e1(F.mul[u][v]) for u in K[1:6] for v in K[1:6] if u and v))
    ok_ell = ok_orbit = True
    for u in K:
        if u == 0 or u in F.base:
            continue
        M = e1(u)
        cp = G.charpoly(M)
        if not is_irreducible_over(F, q, cp) or len(fp_roots(id(F), F, cp)) != n:
            ok_ell = False
        if not G.conjugate(M, e1(F.pow(u, q))):
            ok_orbit = False
    C.check(f"2.5 [{tag}] torus elements outside F_qˣ are elliptic (charpoly = minpoly, irreducible of degree n)", ok_ell)
    C.check(f"2.5 [{tag}] e(u) and e(u^q) are conjugate", ok_orbit)


def independent_digits(F, xs):
    _, piv = rref(F, [F.digs[x] for x in xs], F.m)
    return len(piv) == len(xs)


def independent_over(F, K, e, n, skip=0):
    basis, cnt = [], 0
    for v in K:
        if v == 0:
            continue
        if cnt < skip:
            cnt += 1
            continue
        if over_base_independent(F, basis + [v], e):
            basis.append(v)
        if len(basis) == n:
            break
    return basis


def over_base_independent(F, vs, e):
    rows = [F.digs[F.mul[x][v]] for v in vs for x in e]
    _, piv = rref(F, rows, F.m)
    return len(piv) == len(rows)


def coords_over(F, basis, v, e):
    """Coordinates in F_q of v in the F_q-basis `basis` (e is an F_p-basis of F_q)."""
    n = len(basis)
    rows = [[F.digs[F.mul[x][b]][d] for d in range(F.m)] for b in basis for x in e]   # kn unknowns
    # the system: ∑_{i,j} x_ij (e_j b_i) = v, over F_p:  m equations
    A = [[rows[t][d] for t in range(len(rows))] + [F.digs[v][d]] for d in range(F.m)]
    A, piv = rref_int(A, F.p)
    for r in range(len(piv), len(A)):
        if A[r][-1]:
            raise ValueError("not in the span")
    x = [0] * len(rows)
    for i, c in enumerate(piv):
        x[c] = A[i][-1]
    out = []
    for i in range(n):
        ci = 0
        for j, ej in enumerate(e):
            if x[i * len(e) + j]:
                ci = F.add[ci][F.mul[x[i * len(e) + j]][ej]]
        out.append(ci)
    return tuple(out)


def rref_int(A, p):
    A = [r[:] for r in A]
    nr, nc = len(A), len(A[0]) - 1
    piv_cols, r = [], 0
    for c in range(nc):
        piv = next((i for i in range(r, nr) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        icc = pow(A[r][c], -1, p)
        A[r] = [(x * icc) % p for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(nc + 1)]
        piv_cols.append(c)
        r += 1
        if r == nr:
            break
    return A, piv_cols


def check_gl2_table(U, G, cusp, lin, fns, labels, C, tag):
    """7.6 for n = 2: the character table is orthonormal and each row has a cuspidal support."""
    q, F = U.q, U.F
    N = q * q - 1
    theta_det = lambda M, k: F.theta_pow(det(F, M, 2), k)
    rows = {("lin", k): (lambda M, k=k: theta_det(M, k)) for k in lin}
    for k in lin:
        rows[("St", k)] = (lambda M, k=k: theta_det(M, k) * steinberg(F, q, G, M))
    for i, L in enumerate(labels):
        items = list(L.elements())
        if len(items) == 2 and all(d == 1 for d, _ in items):
            k1, k2 = (kk for _, kk in items)
            if k1 != k2:
                rows[("ps", frozenset((k1, k2)))] = fns[i]
        elif len(items) == 1 and items[0][0] == 2:
            rows[("cusp", canon_label(U, 2, items[0][1]))] = fns[i]
    ok_ps = True
    for key, f in rows.items():
        if key[0] != "ps":
            continue
        k1, k2 = tuple(key[1])
        for M in G.elems:
            cp = G.charpoly(M)
            if is_irreducible_over(F, q, cp):
                target = 0
            elif M[1] == 0 and M[2] == 0 and M[0] == M[3]:
                target = (q + 1) * F.theta_pow(M[0], k1 + k2)
            elif len(fp_roots(id(F), F, cp)) == 1:
                target = F.theta_pow(fp_roots(id(F), F, cp)[0][0], k1 + k2)
            else:
                a, b = fp_roots(id(F), F, cp)[0][0], fp_roots(id(F), F, cp)[1][0]
                target = F.theta_pow(a, k1) * F.theta_pow(b, k2) + F.theta_pow(b, k1) * F.theta_pow(a, k2)
            if abs(f(M) - target) > TOL:
                ok_ps = False
    C.check(f"7.x [{tag}] hcL of two linear characters = Ind_B(χ₁ ⊗ χ₂) with its textbook values (principal series)", ok_ps)
    keys = list(rows)
    C.check(f"7.6 [{tag}] the GL₂ table (linear, Steinberg twists, principal series, cuspidal) has q² - 1 rows", len(keys) == N, f"{len(keys)} vs {N}")
    C.check(f"7.6 [{tag}] … one row per conjugacy class", len(keys) == len(G.classes()[1]))
    ok = True
    for i, ki in enumerate(keys):
        for kj in keys[i:]:
            if abs(G.pairing(rows[ki], rows[kj]) - (1 if ki == kj else 0)) > TOL:
                ok = False
    C.check(f"7.6 [{tag}] the GL₂ character table is orthonormal", ok)
    C.check(f"7.6 [{tag}] every irreducible character of GL₂ pairs nontrivially with hcL of a list of cuspidal characters",
            all(max(abs(G.pairing(rows[ki], f)) for f in fns) > TOL for ki in keys))


def steinberg(F, q, G, M):
    cp = G.charpoly(M)
    if is_irreducible_over(F, q, cp):
        return -1
    r = fp_roots(id(F), F, cp)
    if len(r) == 2:
        return 1
    return q if (M[1] == 0 and M[2] == 0) else 0


if __name__ == "__main__":
    cases = sys.argv[1:] or ["gl2_2", "gl2_3", "gl2_4", "gl2_5", "gl3_2"]
    total = 0
    for case in cases:
        ONLY_DC = case.endswith(":dc")            # only the double-coset count check
        globals()["ONLY_DC"] = ONLY_DC
        case = case.replace(":dc", "")
        kind, qs = case.split("_")
        n, q = int(kind[2:]), int(qs)
        t0 = time.time()
        U = Universe(q, n)
        print(f"\n### {case}: F_q inside F_{{{U.q}^{math.lcm(*range(1, max(n, 1) + 1))}}} ({U.F.Q} elements); "
              f"|GL_{n}| = {U.groups[n].G}; set up in {time.time() - t0:.1f}s")
        C = Checker(case)
        for d in range(1, n + 1):
            check_group(U, d, C)
        total += C.done()
    print(f"\nTOTAL failures: {total}")
    sys.exit(1 if total else 0)
