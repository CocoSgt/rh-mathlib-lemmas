# Roadmap: cuspidal characters of general linear groups over finite fields

**Summary.** Over a finite field `F` with `q` elements, the characteristic polynomial identifies the
`F`-rational semisimple conjugacy classes of the algebraic group `GLₙ` (those with squarefree
polynomial are the classes of semisimple elements of the group `GLₙ(F)` of invertible `n × n`
matrices) with the monic polynomials of degree `n` with nonzero constant term; there are `qⁿ - qⁿ⁻¹`
of them. This roadmap
builds the character theory of these groups up to the classification of their cuspidal characters,
which is due to J. A. Green.

A character of `GLₙ(F)` is cuspidal when it sums to zero over the unipotent radical of every
standard parabolic subgroup. Such a character vanishes at every invertible matrix whose
characteristic polynomial has two distinct irreducible factors, and it is determined by its values
at the matrices with irreducible characteristic polynomial. Green's theorem, the first headline, reads: for an
extension `K` of `F` of degree `n`, the characters `θ` of the group `Kˣ` whose conjugates
`θ^{q^i}`, `0 < i < n`, all differ from `θ` (the *regular* characters) are in bijection with the
cuspidal characters of `GLₙ(F)`. The cuspidal character `χ_θ` has degree `∏_{i = 1}^{n-1} (q^i - 1)`;
at a matrix `g` with irreducible characteristic polynomial it takes the value
`(-1)^{n-1} ∑_{i < n} θ(z^{q^i})`, for every root `z ∈ Kˣ` of that polynomial; and
`χ_θ = χ_θ'` exactly when `θ' = θ^{q^i}` for some `i < n`. The second headline follows:
`GLₙ(F)` has `(1/n) ∑_{d ∣ n} μ(d) q^{n/d}` cuspidal characters, as many as there are monic
irreducible polynomials of degree `n` over `F`, and these polynomials, the *prime labels*,
parametrize the cuspidal characters. For example `GL₂(F)` has `q(q - 1)/2` cuspidal characters,
all of degree `q - 1`, and `GL₃(𝔽₂)`, a group of order `168`, has two cuspidal characters, both of
degree `3`.

The third headline is the existence and uniqueness of the *cuspidal support*: every irreducible
character of `GLₙ(F)` occurs in the Harish–Chandra induction of a multiset of cuspidal characters
of smaller general linear groups, of total degree `n`, and the multiset is unique.

The proof follows Green's construction. To a character `θ` of the multiplicative group of the
algebraic closure of `F` one attaches the root-power-sums `P ↦ ∑_{P(α) = 0} θ(α)^k` of
polynomials; they are additive over products. From an additive function `s` on polynomials, Möbius
inversion over the lattice of invariant subspaces of a vector space produces a class function `ψₛ`
on its endomorphisms whose sums over the unipotent radical of every parabolic subgroup are zero,
and which agrees with `s` of the characteristic polynomial on the endomorphisms with irreducible
characteristic polynomial. For `s` a
root-power-sum, the restriction of `(-1)^{n-1} ψₛ` to `GLₙ(F)` is a virtual character, and it has
norm `1` when `k` is regular; so it is an irreducible character, and it is cuspidal because its
sums over the unipotent radicals vanish. Surjectivity is a count. Harish–Chandra induction from
a standard parabolic subgroup is adjoint, under the pairing of class functions, to the average over
the unipotent radical (the Jacquet restriction). By the Mackey formula the inductions of two
different multisets of cuspidal characters are orthogonal. Each such induction has a *generic*
irreducible constituent, on which a Whittaker functional does not vanish, and there are at most
`qⁿ - qⁿ⁻¹` generic irreducible characters. So there are at most `qⁿ - qⁿ⁻¹` multisets of cuspidal
characters of total degree `n`, and comparing this with the multisets assembled from the cuspidal
characters already constructed closes the classification.

The roadmap builds on the character theory of finite groups of
[RepresentationTheory.CharacterTheory](../RepresentationTheory/CharacterTheory/README.md):
class functions, their bilinear pairing, virtual characters and the norm-one test. Its table of
`GL₂(𝔽_q)` is the case `n = 2` here and supplies a Check. The roadmap feeds the depth-zero block
of the representation theory of `GLₙ` over a local field with residue field `F`, whose cuspidal
representations of `GLₙ(F)` it describes; [SmoothRepresentationsOfLocalGroups](../SmoothRepresentationsOfLocalGroups/README.md)
touches that block only in rank one. It is also the finite-field input to the series of roadmaps
outlined under *Roadmap for a roadmap* below.

Layer 1 treats polynomials and root-power-sums, Layer 2 endomorphisms and their characteristic
polynomials, Layer 3 class functions, constant terms and cuspidality, Layer 4 Green's Möbius transform, Layer 5 the
virtual characters obtained from it, Layer 6 the cuspidal characters attached to regular
characters, Layer 7 Harish–Chandra induction, the Jacquet restriction, the cuspidal support, the
generic constituents, Green's theorem and the count of cuspidal characters, Layer 8 the uniqueness
of the cuspidal support and the prime labels.
[`Suggested.lean`](Suggested.lean) states the headline theorems in Lean; it is not the roadmap.

## How to read the build

Layers 1 and 2 are combinatorics and linear algebra over `F`: counts, fibres, subspaces. Layer 3
fixes the vocabulary for class functions on `GLₙ(F)`, the parabolic subgroups and cuspidality; its
support and separation statements (3.6, 3.7) use the primitivity of Layer 4. Layers 4 and 5 are
Green's construction, which connects Layers 1 and 2 to Layer 3. Layer 6 combines Layers 3, 4 and 5
into the cuspidal characters. Layer 7 is the induction theory of the matrix group — Harish–Chandra
induction, its adjoint, the cuspidal support, the generic constituents — and the count that
completes Green's theorem. Layer 8 proves the uniqueness of the cuspidal support and restates the
classification by prime labels. The numbers of the statements are those of `Suggested.lean`.

## Conventions

- **The field.** `F` is a finite field, `q = Nat.card F`, `n ≥ 1`, and `GL (Fin n) F` is Mathlib's
  group of invertible `n × n` matrices (an abbreviation for `(Matrix (Fin n) (Fin n) F)ˣ`). For a
  group element `g`, `(g : Matrix (Fin n) (Fin n) F)` is the matrix. A degree-`n` extension of `F`
  is a field `K` with `Algebra F K` and `Module.finrank F K = n`; any two are `F`-isomorphic and no
  statement depends on the choice.
- **Teichmüller characters.** A multiplicative map `θ : AlgebraicClosure F →* ℂ` that is injective
  off `0` (1.2). It exists and is not unique. Replacing `θ` by `θ ∘ (·^q)` replaces the index `k` of
  every root-power-sum below by `kq`, and no statement of the roadmap depends on the choice.
- **Regular characters.** `IsRegular F n θ`, for `θ : Kˣ →* ℂˣ`: `θ^{q^i} ≠ θ^{q^j}` whenever
  `i ≠ j` in `range n`. Through a Teichmüller character `θ₀` and an `F`-embedding
  `ι : K → AlgebraicClosure F`, every character of `Kˣ` is `u ↦ θ₀ (ι u)^k` for one residue `k`
  modulo `qⁿ - 1`, and it is regular exactly when `k q^i ≢ k [MOD qⁿ - 1]` for `0 < i < n`.
- **Root-power-sums.** `rootPowerSum θ k P = ∑_{P(α) = 0} θ(α)^k`, the roots taken in the
  algebraic closure with multiplicity. A function `s : F[X] → ℂ` is *additive* when
  `s (P * Q) = s P + s Q` for monic `P, Q`.
- **Characters.** A character of a group `G` is a function `G → ℂ`. `IsIrreducibleCharacter n χ`
  says that `χ` is the character of a simple object of `FDRep ℂ (GL (Fin n) F)`; in Tau Ceti this is
  membership in `TauCeti.irreducibleCharacters ℂ G`. A *virtual character* is an element of
  `TauCeti.virtualCharacters ℂ G`, a difference of two characters. The pairing `glPairing n φ ψ` is
  `(Nat.card G)⁻¹ ∑ g, φ g * conj (ψ g)`. On class functions it is `TauCeti.ClassFunction.characterPairing`
  (`|G|⁻¹ ∑ g, φ g * ψ g⁻¹`), because `ψ g⁻¹ = conj (ψ g)` for virtual characters
  (`TauCeti.conj_apply_of_mem_virtualCharacters`); it is bilinear, symmetric and nondegenerate, and
  `⟨χ, χ'⟩` is `1` when `χ = χ'` is irreducible and `0` on two distinct irreducible characters.
- **Cuspidal characters.** `unipotentRadical F n a` is the set `Uₐ` of invertible matrices that
  agree with the identity matrix in their first `a` columns; it has `q^{a(n-a)}` elements and is the
  unipotent radical of the standard parabolic subgroup `parabolic F n a` of block upper triangular
  matrices with block sizes `a`, `n - a`. `IsCuspidalCharacter n χ`: `χ` is irreducible and
  `∑_{u ∈ Uₐ} χ u = 0` for every `0 < a < n`. An invertible matrix is *elliptic* when its
  characteristic polynomial is irreducible, and *primary* when its characteristic polynomial is a
  power of an irreducible polynomial.
- **Harish–Chandra induction and Jacquet restriction.** For `a + b = n` and functions `α`, `β` on
  `GL (Fin a) F`, `GL (Fin b) F`, `harishChandraInduct n a b h α β x` is the induced class function
  `|Pₐ|⁻¹ ∑_{y, y⁻¹ x y ∈ Pₐ} α (A) * β (B)`, where `A`, `B` are the diagonal blocks of `y⁻¹ x y`.
  Its adjoint under the pairing is the Jacquet restriction
  `jacquetRestrict n a b h χ m = |Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ (m * u)`, for a block-diagonal matrix `m` with
  diagonal blocks `m.1, m.2` (Frobenius reciprocity, 7.3). A *list* `L` of degree-tagged functions
  has the iterated induction `hcL L n` along the standard parabolic subgroup of the block sizes of
  the list; it is `0` unless the degrees sum to `n`.
- **Finite sums.** Every sum of the roadmap is finite: over a finite group or subgroup, the
  endomorphisms or subspaces of a finite vector space, or the divisors of `n`.

## Layer 1: monic polynomials, Teichmüller characters, and root-power-sums

### 1.1 Counts

Let `N_q(n)` be the number of monic irreducible polynomials of degree `n` over `F`.

- `card_monicIrreducible`: for `n ≥ 1`, `n * N_q(n) = ∑_{d ∣ n} μ(d) * q^{n/d}`, with `μ` the
  Möbius function `ArithmeticFunction.moebius`.
- The monic polynomials of degree `n` number `qⁿ`; those with nonzero constant term number
  `qⁿ - qⁿ⁻¹`. For `n ≥ 2`, a monic irreducible of degree `n` has nonzero constant term.
- Each monic irreducible of degree `n` has `n` distinct roots in `AlgebraicClosure F`, forming
  one orbit of `α ↦ α^q`; `α ↦ minpoly F α` is `n`-to-`1` from the elements of degree `n` onto the
  monic irreducibles of degree `n`.

Route. Every monic polynomial is the product of the monic irreducibles in
`UniqueFactorizationMonoid.normalizedFactors`; counting multisets of total degree `n`,
`qⁿ = ∑_{d ∣ n} d * N_q(d)`. Möbius inversion over the divisibility order and
`∑_{d ∣ n} μ(d) = 0` for `n > 1` give the formula. The roots of a monic irreducible of degree `n`
are the roots of its splitting field, generated by one root and permuted transitively by the
Frobenius.

**Checks.**
- `N_q(1) = q`; `N_q(2) = q(q - 1)/2`, since `X² + aX + b` is irreducible iff `a² ≠ 4b`;
  `N₂(3) = 2` (`X³ + X + 1` and `X³ + X² + 1`); `N₂(6) = 9`; `N₃(2) = 3`.
- `qⁿ - qⁿ⁻¹` is the number of monic polynomials `Xⁿ + c_{n-1}Xⁿ⁻¹ + … + c₀` with `c₀ ≠ 0`.
- `X²` and `X² + X` are monic of degree `2` with zero constant term; among monic polynomials of
  degree `n` exactly `qⁿ⁻¹` have zero constant term.

*Needs:* Mathlib `UniqueFactorizationMonoid.normalizedFactors` and unique factorization,
`ArithmeticFunction.moebius`, `Nat.divisors`, `Polynomial.roots`, `minpoly`.

### 1.2 Teichmüller characters

Prove `exists_teichmullerChar`: there is `θ : AlgebraicClosure F →* ℂ` with `θ x = θ y → x = y`
for all `x, y ≠ 0`.

Route. The algebraic closure of `F` is the union over `n` of the splitting fields
`GaloisField`, each with `q^{n!}` elements and multiplicative group cyclic of order `q^{n!} - 1`,
and `q^{(n+1)!} - 1 = (q^{n!} - 1) * mₙ` for an integer `mₙ`. Choose generators `gₙ` of these groups
with `g_{n+1}^{mₙ} = gₙ`, and roots of unity `ζₙ ∈ ℂ` of order `q^{n!} - 1` with
`ζ_{n+1}^{mₙ} = ζₙ` (`ℂˣ` contains every root of unity); put `θ (gₙ^k) = ζₙ^k`.

**Checks.**
- `θ 1 = 1`; `θ` is injective on each `𝔽_{q^{n!}}ˣ`; `θ x` is a root of unity of order dividing
  `q^{n!} - 1` for `x ∈ 𝔽_{q^{n!}}`.
- `θ ∘ (·^q)` is another Teichmüller character.

*Needs:* Mathlib `GaloisField`, the cyclicity of `Gal(L/K)` for finite fields
(`Mathlib/FieldTheory/Finite/Basic.lean`), `IsPrimitiveRoot`.

### 1.3 Regular characters of `Kˣ`

Fix `K` of degree `n` over `F`, a Teichmüller character `θ₀` and an `F`-embedding
`ι : K → AlgebraicClosure F`.

- Every character `θ : Kˣ →* ℂˣ` is `u ↦ θ₀ (ι u)^k` for exactly one residue `k` modulo `qⁿ - 1`.
- `θ` is regular iff `k q^i ≢ k [MOD qⁿ - 1]` for `0 < i < n`. Composing `ι` with a power of the
  Frobenius, or replacing `θ₀` by `θ₀ ∘ (·^q)`, replaces `k` by `k q^j`.
- The number of Frobenius orbits of regular characters, for the action `θ ↦ θ^q`, is `N_q(n)`.

Route. `Kˣ` is cyclic of order `qⁿ - 1`, so a character is determined by the image of a generator.
The residues with `k q^d ≡ k` for a given `d ∣ n` are the multiples of `(qⁿ - 1)/(q^d - 1)`,
`q^d - 1` of them, because `gcd(q^d - 1, qⁿ - 1) = q^{gcd(d,n)} - 1`. Möbius inversion over the
divisors of `n` counts the residues whose stabilizer is trivial,
`∑_{d ∣ n} μ(n/d) q^d`; an orbit of that action is regular and has `n` elements, and the orbit
count is `N_q(n)` by 1.1.

**Checks.** `q = 2`, `n = 3`: `Kˣ ≅ ℤ/7`, the Frobenius is `k ↦ 2k`, the orbits are `{0}`,
`{1, 2, 4}` and `{3, 6, 5}`; two are regular and `N₂(3) = 2`.

*Needs:* 1.1; Mathlib on cyclic groups, `ZMod`.

### 1.4 Root-power-sums

- `rootPowerSum_add`: `rootPowerSum θ k` is additive over products of monic polynomials.
- `rootPowerSum_one_sub_pow`: `rootPowerSum θ k ((X - 1)^j) = j`.
- If `α` has degree `n` over `F`, `rootPowerSum θ k (minpoly F α) = ∑_{i < n} θ(α^{q^i})^k`.
- *Orthogonality on roots of unity.* For residues `k, l`:
  `∑_{α ∈ AlgebraicClosure F, α^{qⁿ - 1} = 1} θ(α)^k * conj (θ(α)^l)` equals `qⁿ - 1` if
  `k ≡ l [MOD qⁿ - 1]` and `0` otherwise.

Route. The roots of a product; the only root of `(X - 1)^j`; the roots of a minimal polynomial form
one Frobenius orbit (1.1); the last point is the orthogonality of the characters of a finite cyclic
group of order `qⁿ - 1`, since `θ` is injective on it.

**Checks.** `rootPowerSum θ k (X - a) = θ(a)^k`; `rootPowerSum θ 0 P = P.natDegree` for monic `P`
with nonzero constant term; `rootPowerSum θ k P` depends only on `P` and `k` modulo `q^{P.natDegree} - 1`.

*Needs:* 1.1–1.3; Mathlib `Polynomial.roots`, `IsPrimitiveRoot`; Tau Ceti's character orthogonality
for finite abelian groups.

### Examples

`F = 𝔽₂`, `K = 𝔽₈`: for a root `α` of `X³ + X + 1`,
`rootPowerSum θ₀ k (X³ + X + 1) = θ₀(α)^k + θ₀(α²)^k + θ₀(α⁴)^k`, and this is the same for
`k ∈ {1, 2, 4}` after the reindexing of 1.3.

### Dependencies

Mathlib, and Tau Ceti's character orthogonality for finite abelian groups. No other layer.

## Layer 2: endomorphisms of a finite vector space and their characteristic polynomials

Throughout, `V` is a finite-dimensional `F`-vector space; `LinearMap.charpoly` is the
characteristic polynomial of an endomorphism.

### 2.1 Masses

Define `mass φ P` as the sum of `φ g` over the endomorphisms `g` of `V` with `LinearMap.charpoly g = P`.
It is linear in `φ`, for fixed `P`.

### 2.2 Elliptic classes

Prove `mass_one_irreducible`: for a monic irreducible `f` of degree `d ≥ 1` with nonzero constant
term, the endomorphisms of `Fin d → F` with characteristic polynomial `f` are invertible, form one
orbit under conjugation by `GL (Fin d) F`, and number `|GL (Fin d) F| / (q^d - 1)`.

Prove further: for monic irreducible `f` of degree `d` and `m ≥ 1`, the invertible matrices with
characteristic polynomial `f^m` *and* minimal polynomial `f^m` form one orbit, of size
`|GL (Fin (d * m)) F| / (q^{d(m-1)} * (q^d - 1))`.

Route. A matrix with characteristic polynomial `f` makes `V` a vector space over the field
`F[X]/(f)`, with `q^d` elements, and its centralizer in `GL(V)` is that field's multiplicative
group, of order `q^d - 1` (`Module.AEval'`). A matrix with minimal polynomial `f^m` is cyclic, and
its centralizer is the group of units of `F[X]/(f^m)`, of order `q^{d(m-1)}(q^d - 1)`.

**Checks.** `GL₂(𝔽₂)` has order `6`, and its class of elements with characteristic polynomial
`X² + X + 1` has `6/3 = 2` elements, the two elements of order `3`.

*Needs:* 1.1; Mathlib `LinearMap.charpoly`, `Matrix.card_GL_field`, `Module.AEval'`, `Quotient` of
`F[X]`.

### 2.3 Subspaces

Prove `card_submodules`: the number `G(n, a)` of subspaces of rank `a` of `Fin n → F` satisfies
`G(n, a) * ∏_{i < a} (q^a - q^i) = ∏_{i < a} (qⁿ - q^i)`.

Route. Count the `a`-tuples of linearly independent vectors in two ways: as spanning `a`-tuples of a
rank-`a` subspace, there are `∏_{i < a} (q^a - q^i)` of them per subspace; in total
`∏_{i < a} (qⁿ - q^i)`.

**Checks.** `a = 0`: both products are empty and `G(n, 0) = 1`. `a = 1`: `G(n, 1) = (qⁿ - 1)/(q - 1)`.
`a = n`: `G(n, n) = 1`.

*Needs:* Mathlib `Submodule`, `LinearIndependent`, `Module.finrank`.

### 2.4 Cyclic vectors and the density of a characteristic polynomial

For an endomorphism `g` of `V`, a *cyclic vector* is a vector that lies in no proper `g`-invariant
subspace.

- *Cyclic vectors.* `∑_W #{cyclic vectors of g restricted to W} = q^{dim V}`, over the
  `g`-invariant subspaces `W` of `V`, the zero subspace included (its zero vector is cyclic).
- *The number of cyclic pairs.* For monic `D` of degree `d`,
  `∑_{g : charpoly g = D} #{cyclic vectors of g} = |GL (Fin d) F|`, the sum over endomorphisms of
  `Fin d → F`.
- *Density.* For monic `P`, let `μ(P) = mass 1 P / |GL (Fin P.natDegree) F|`. Then `μ(1) = 1` and
  `q^{P.natDegree} * μ(P) = ∑_{D ∣ P} μ(D)`, over the monic divisors of `P`.

Route. For the first point, group the vectors by the invariant subspace they generate. For the
second, a cyclic vector `v` for `g` identifies `V` with `F[X]/(charpoly g)`, sending `X` to `g` and
`1` to `v`; so for each monic `D` the pairs `(g, v)` are in bijection with the cyclic
`F[X]/(D)`-module structures on `V`, and the count of the source (Provenance) evaluates their
number as `|GL (Fin d) F|`. For the third, sum the second point over the monic polynomials of a
given degree and compare with the number of endomorphisms.

**Checks.** `μ(f) = 1/(q - 1)` for `f = X - a` of degree `1`, since the endomorphism is `a` itself
and `|GL (Fin 1) F| = q - 1`; `μ` is not multiplicative.

*Needs:* 2.1–2.3; Mathlib `Module.AEval'`, `Polynomial` divisibility.

### Examples

`n = 2`: the `q² - q` monic polynomials of degree `2` with nonzero constant term are the classes of
`GL₂(F)`; the `q(q - 1)/2` irreducible ones are the elliptic classes, each of size `q² - q`.

### Dependencies

Layer 1; Mathlib only otherwise.

## Layer 3: class functions on `GLₙ(F)`, constant terms, and cuspidal characters

### 3.1 The pairing

`glPairing n` is the pairing of the Conventions. On class functions it is
`TauCeti.ClassFunction.characterPairing`, nondegenerate because `Nat.card (GL (Fin n) F) ≠ 0` in
`ℂ`; `⟨χ, χ'⟩` is `1` if `χ = χ'` is irreducible and `0` on two distinct irreducible characters
(Mathlib `FDRep.char_orthonormal`).

### 3.2 Characters

`IsIrreducibleCharacter n χ` is membership in `TauCeti.irreducibleCharacters ℂ (GL (Fin n) F)`.
A virtual character of norm `1` is an irreducible character or the negative of one
(`TauCeti.exists_eq_irreducibleCharacter_or_neg`), and it is an irreducible character when
moreover it is a nonnegative combination of characters
(`TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`).

### 3.3 Parabolic subgroups, their unipotent radicals, and the Levi subgroups

`parabolic F n a` is the subgroup `Pₐ` of block upper triangular matrices with block sizes `a`,
`n - a`; `unipotentRadical F n a` is its unipotent radical `Uₐ`; `toGL n M` is the matrix `M` read
in `GL (Fin n) F` (the value `1` occurs only for a non-invertible `M`); `blockDiag n a b h m` is the
block-diagonal matrix with diagonal blocks `m.1`, `m.2`, for `a + b = n`. Prove: `Uₐ` is normal in
`Pₐ` and `Pₐ` is the semidirect product of `Uₐ` with the subgroup `Lₐ` of block-diagonal matrices;
`|Uₐ| = q^{a(n-a)}`; `blockDiag` is a unit, and `m ↦ toGL n (blockDiag n a b h m)` is an injective
homomorphism `GL (Fin a) F × GL (Fin b) F →* GL (Fin n) F` with image `Lₐ`; the characteristic
polynomial of the product of a block-diagonal matrix and an element of `Uₐ` is the product of the
characteristic polynomials of its blocks.

Route. Matrix computation; the last point by the block-triangular determinant formula.

### 3.4 Cuspidal characters

`IsCuspidalCharacter n χ` (Conventions): `χ` is irreducible and `∑_{u ∈ Uₐ} χ u = 0` for every
`0 < a < n`.

### 3.5 Constant terms

Prove `cuspidal_iff_constant_terms`: for a function `χ` on `GL (Fin n) F`, `χ` is a cuspidal
character if and only if it is irreducible and `∑_{u ∈ Uₐ} χ (m * u) = 0` for every `0 < a < n`
and every block-diagonal matrix `m` with blocks of sizes `a`, `n - a`.

Route. For `0 < a < n` and a representation with character `χ`, the operator
`|Uₐ|⁻¹ ∑_{u ∈ Uₐ} u` is the projection onto the subspace of vectors fixed by `Uₐ`, it commutes
with `Lₐ`, and `m ↦ |Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ (m * u)` is the character of `Lₐ` on that subspace. Its value
at the identity is `|Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ u`. So the sums over `Uₐ` vanish when that character is `0`,
and the character of a representation is `0` when its value at the identity is `0`.

### 3.6 Support of a cuspidal character

Prove `cuspidal_vanish_off_primary`: if `χ` is cuspidal and the characteristic polynomial of the
invertible matrix `x` is not a power of an irreducible polynomial, then `χ x = 0`.

Route. Extend `χ` by `0` to the non-invertible endomorphisms of `Fin n → F`. By 3.5 the sums of the
extension over the unipotent radicals `Uₐ` vanish, so the extension is a primitive class function
in the sense of 4.7; a primitive class function vanishes at every endomorphism whose characteristic
polynomial has two distinct irreducible factors (4.7).

### 3.7 Separation on the elliptic elements

Prove `cuspidal_eq_of_eq_on_elliptic`: two cuspidal characters that agree at every invertible
matrix with irreducible characteristic polynomial are equal.

Route. Both extensions by zero are primitive (as in 3.6) and agree on the invertible endomorphisms
with irreducible characteristic polynomial; 4.7 shows that a primitive class function is determined
by its values there.

### Examples

The cuspidal characters of `GL₂(F)` are the `q(q - 1)/2` characters of degree `q - 1` of Tau Ceti's
table. With `λ` the central character and `z` a root of the characteristic polynomial of an elliptic
matrix, they vanish at the split semisimple classes, take the value `(q - 1) λ(s)` at the scalar
matrix `s` and the value `-λ(s)` at the classes `s * u₀` with `u₀` a nontrivial element of `U₁`
(because `∑_{u ∈ U₁} χ (s * u) = χ(s) + (q - 1) χ(s u₀) = 0`), and the value `-θ(z) - θ(z^q)` at
an elliptic matrix (6.3). So a cuspidal character does not vanish off the elliptic elements: the
scalar classes and the classes `s * u₀` are primary, and it vanishes exactly off the classes whose
characteristic polynomial has two distinct irreducible factors.

### Dependencies

Tau Ceti's character theory (Exact supplier contracts) and its `GL₂` table. 4.7 is used in the
routes of 3.6 and 3.7; it is proved in Layer 4 from the definitions of that layer.

## Layer 4: Green's Möbius transform on the lattice of invariant subspaces

### 4.1 Definition

`psi s V g` is defined by recursion on `Module.finrank F V`:
`psi s V g = s (charpoly g) - ∑_{W invariant, W ≠ ⊤} psi s W (g restricted to W)`, the sum over
the proper `g`-invariant subspaces of `V`.

### 4.2 The inversion identity

Prove `charpoly_eq_sum_psi`: for every endomorphism `g`,
`s (charpoly g) = ∑_{W invariant} psi s W (g restricted to W)`, over all invariant subspaces
including `V`.

Route. Induction on the dimension, by the recursion of 4.1.

### 4.3 Class function

Prove `psi_conj`: `psi s V (e.conj g) = psi s V g` for every `e : V ≃ₗ[F] V`. So `psi s V`
restricted to the invertible endomorphisms is a class function on `GL(V)`. It is *not* a function of
the characteristic polynomial alone: for `s = natDegree` and `n = 2` it is `1 - q` at the identity and
`1` at a Jordan block, which have the same characteristic polynomial.

Route. `LinearEquiv.charpoly_conj`; `e` permutes the invariant subspaces of `g` and commutes with
restriction to them.

**Checks.** `V = 0`: `psi s V 0 = s 1`. `s = 0`: `psi s = 0`.

### 4.4 Value on elliptic endomorphisms

Prove `psi_of_irreducible`: if `LinearMap.charpoly g` is irreducible then
`psi s V g = s (charpoly g)`.

Route. An endomorphism with irreducible characteristic polynomial has no nonzero proper invariant
subspace.

### 4.5 The mass formula

Prove `mass_psi`: for `s` additive, `n ≥ 1`, `f` monic irreducible with `f.natDegree * m = n` and
`m ≥ 1`, `mass (psi s (Fin n → F)) (f^m) = |GL (Fin n) F| * s f / (qⁿ - 1)`. Prove also that the
mass of `psi s` over the fibre of a monic `P` of degree `n` with at least two distinct monic
irreducible factors is `0`.

Route. For `m = 1` this is 2.2 with 4.4. In general, sum 4.2 over the fibre of `P`: the left side is
`mass 1 P * s P`; on the right, group the terms by the characteristic polynomial of the restriction
of `g` to `W`, which divides `P`, and solve for `mass (psi s) P` by induction on the number of
irreducible factors of `P`, using 2.4.

### 4.6 Value at the identity

Prove `psi_one`: if `s ((X - 1)^j) = j` for every `j`, then
`psi s (Fin n → F) 1 = ∏_{i = 1}^{n-1} (1 - q^i)`.

Route. The invariant subspaces of the identity are all the subspaces; induction on `n` with 2.3.

**Checks.** `n = 1`: the empty product `1`. `n = 2`, `s = natDegree`: `2 - (q + 1) = 1 - q`.

### 4.7 Primitivity

A function `φ` on `Module.End F V` is *primitive* when for every subspace `A` with `0 ≠ A ≠ V` and
every endomorphism `g` preserving `A`, `∑_{h ∈ nilRad A} φ (g + h) = 0`, where `nilRad A` is the set
of endomorphisms with image in `A` that vanish on `A`.

- For `s` additive, `psi s V` is primitive.
- A primitive class function vanishes at every endomorphism whose characteristic polynomial is not
  a power of an irreducible. A primitive class function that vanishes at every endomorphism with
  characteristic polynomial `f^m` and `f(g) = 0` (an `f`-nilpotent endomorphism) vanishes on the
  whole fibre of `f^m`. Two primitive class functions that agree on the invertible endomorphisms
  with irreducible characteristic polynomial are equal.
- For `φ` primitive and `s` additive,
  `∑_{g invertible} φ g * conj (psi s V g) = ∑_{g invertible} φ g * conj (s (charpoly g))`.

Route. Sum the recursion of 4.1 over `nilRad A`, using `charpoly (g + h) = charpoly g` for
`h ∈ nilRad A`. For the second point, `f(g) = 0` on the kernel of a suitable power of `f(g)`, and
the fibre of `f^m` is a single orbit on each of which the two sides of the statement are equal, by
4.3; see the source statements named in Provenance. For the third, group the invertible `g` by their
invariant subspaces and use 4.7's first point inductively.

**Checks.** `n = 2`, `s = natDegree`: `psi s V` is `2` at the endomorphisms with irreducible
characteristic polynomial, `1 - q` at the identity, `1` at a Jordan block and `0` at a matrix with
two distinct eigenvalues; its sum over `U₁` is `(1 - q) + (q - 1) * 1 = 0`.

*Needs for the layer:* Layers 1 and 2; Mathlib `LinearMap.charpoly`, `LinearEquiv.charpoly_conj`,
`Submodule.finrank_lt`, `Module.AEval'`.

### Examples

`psi (rootPowerSum θ k)` on `Fin 2 → F`: it is `rootPowerSum θ k (P)` on the fibre of an
irreducible `P` (4.4); `1 - q` at the identity (4.6); `1` at a Jordan block with characteristic
polynomial `(X - a)²`, which has one invariant line; `0` at a matrix with two distinct eigenvalues,
which has two.

### Dependencies

Layers 1 and 2; Mathlib only otherwise.

## Layer 5: Frobenius torus characters

### 5.1 Virtual characters

Prove `rootPowerSum_virtualCharacter`: for a Teichmüller character `θ` and all `n, k`, the function
`g ↦ rootPowerSum θ k (charpoly g)` on `GL (Fin n) F` is a virtual character.

Route, by induction on `n`. The class function induced from the non-split torus `T ≅ Kˣ`, `K` of
degree `n`, with its character `θ ∘ ι` powered to `k`, agrees with `rootPowerSum θ k ∘ charpoly` on
the elliptic classes and vanishes elsewhere (2.2 and 1.4). Off the elliptic set, `rootPowerSum θ k`
of a polynomial is the sum of its values on the irreducible factors (1.4), so the difference is
supported on the classes that meet a proper Levi subgroup, and there it is a sum of class functions
induced from the Levi subgroups, each the function of 5.1 for a smaller `GLₘ(F)`.

### 5.2 The pairing formula

Prove `pairing_psi_rootPowerSum`: for a Teichmüller character `θ`, `n ≥ 1` and residues `k, l`,
`⟨ψₖ, Ψ_l⟩ = |GL (Fin n) F| * #{i < n : k q^i ≡ l [MOD qⁿ - 1]}`, where `Ψ_l` is
`rootPowerSum θ l ∘ charpoly` and `ψₖ` the function `g ↦ psi (rootPowerSum θ k) (Fin n → F) (mulVecLin g)`
of `GL (Fin n) F`.

Route. `ψₖ` is primitive (4.7) and equal to `rootPowerSum θ k (charpoly g)` on the elliptic
elements (4.4 and 4.3); by 4.7 its pairing against `Ψ_l` equals that of the function
`g ↦ rootPowerSum θ k (charpoly g)` against `Ψ_l`, summed over the invertible `g`; group by the
monic polynomial `P = charpoly g`, using 2.2 for the size of a fibre and 1.1 to pass to a sum over
the elements `α` with `α^{qⁿ - 1} = 1`; the orthogonality of 1.4 evaluates it.

**Checks.** `l = k`, `k` regular: `|GL (Fin n) F|`. `l = 0`:
`#{i < n : qⁿ - 1 ∣ k q^i}` times `|GL (Fin n) F|`, which is `0` for `k` regular and `n > 1`.

### 5.3 The Möbius transform of a root-power-sum is a virtual character

Prove `psi_rootPowerSum_virtualCharacter`: for a Teichmüller character `θ` and all `n, k`, the
function `g ↦ psi (rootPowerSum θ k) (Fin n → F) (mulVecLin g)` on `GL (Fin n) F` is a virtual
character.

Route, by induction on `n`. Expand the recursion of 4.1 over the chains of invariant subspaces:
on the invertible endomorphisms, `psi s` is an alternating sum over the complete flags of invariant
subspaces of class functions induced from the Levi subgroups of the flags (the class function
induced from a subgroup in the sense of character theory, Tau Ceti's
`TauCeti/RepresentationTheory/Induction/ClassFunction.lean`), each the product of the functions of
5.1 on the graded pieces of the flag. An induced character is a character, and the functions on the
graded pieces are virtual characters by 5.1 and the induction hypothesis.

### Examples

`F = 𝔽₂`, `n = 3`, `k = 1`: `Ψ₁` is a virtual character of `GL₃(𝔽₂)` with `Ψ₁(1) = 3`, and
`ψ₁ = χ₁` (the sign is `+1`) is a cuspidal character of degree `3` (6.2).

### Dependencies

Layers 1–4; Tau Ceti's induced class functions. Nothing from Layers 6–8.

## Layer 6: cuspidal characters from regular characters

Fix `n ≥ 1` and a Teichmüller character `θ`, and let `χₖ` be the function
`g ↦ (-1)^{n-1} * psi (rootPowerSum θ k) (Fin n → F) (mulVecLin g)` on `GL (Fin n) F`.

### 6.1 Self-pairing

Prove `self_pairing_psi_rootPowerSum`: if `k q^i ≢ k [MOD qⁿ - 1]` for `0 < i < n`, then
`⟨χₖ, χₖ⟩ = 1`.

Route. 5.2 with `l = k`; the sign squares to `1`.

### 6.2 Irreducible and cuspidal

Prove `cuspidal_of_self_pairing`: under the hypothesis of 6.1, `χₖ` is a cuspidal character.

Route. `χₖ` is a virtual character (5.3, up to the sign). It is irreducible or the negative of an
irreducible character (3.2 and 6.1); its value at `1` is
`(-1)^{n-1} ∏_{i = 1}^{n-1} (1 - q^i) = ∏_{i = 1}^{n-1} (q^i - 1) > 0` (4.6 and 1.4), so it is an
irreducible character. Its sums over the unipotent radicals `Uₐ` vanish, because `psi s` is
primitive (4.7), so it is cuspidal (3.4).

### 6.3 The character of a regular character

Prove `cuspidalCharacter_of_regular`: for `K` of degree `n` and a regular `θ' : Kˣ →* ℂˣ`, there is
a cuspidal character `χ` of `GL (Fin n) F` with `χ 1 = ∏_{i = 1}^{n-1} (q^i - 1)` and
`χ g = (-1)^{n-1} ∑_{i < n} θ'(z^{q^i})` for every `g` with irreducible characteristic polynomial
and every root `z ∈ Kˣ` of it in `K`.

Route. Write `θ' = u ↦ θ(ι u)^k` (1.3). Then `k` is regular, and `χ := χₖ` has the stated values by
4.4 and 1.4; the roots of the characteristic polynomial of `g` in `K` form one Frobenius orbit, so
the value does not depend on the root.

### 6.4 Injectivity up to Frobenius conjugacy

Prove: for regular characters `θ, θ'` of `Kˣ`, the characters `χ, χ'` of 6.3 are equal if
`θ' = θ^{q^i}` for some `i < n`, and only then.

Route. If `θ' = θ^{q^i}`, the two values at an elliptic `g` are equal by 1.4, and then the
characters are equal by the separation on the elliptic elements (3.7). Conversely, if `χ = χ'`, then
`⟨χ, Ψ_{k'}⟩ = ⟨χ', Ψ_{k'}⟩` is `|GL (Fin n) F|` by 6.1 and 5.2, so `#{i < n : k q^i ≡ k'} > 0`.

*Needs for the layer:* Layers 3–5; Tau Ceti's norm-one test
(`TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`) is what 6.2 uses.

### Examples

`F = 𝔽₂`, `n = 3`: `χ₁(1) = (2 - 1)(4 - 1) = 3`; `χ₁ = χ₂ = χ₄` (the residues `2`, `4` are in the
Frobenius orbit of `1`) and `χ₃ = χ₆ = χ₅` is the other cuspidal character of `GL₃(𝔽₂)`.

### Dependencies

Layers 3–5. Nothing from Layer 7.

## Layer 7: Harish–Chandra induction, cuspidal support, generic constituents, and Green's theorem

### 7.1 Harish–Chandra induction

`toGL`, `parabolic`, `unipotentRadical` and `blockDiag` are defined in 3.3. This layer adds:

- (a) `levi n a b h x`: the two diagonal blocks of `x`, for block sizes `a`, `b` with `a + b = n`,
  each read in its general linear group through `toGL`.
- (b) `harishChandraInduct n a b h α β`: the induced class function of the Conventions.
- (c) `hcL L n`: the induction along a list, by recursion on the list: `hcL [] 0 = 1`, `hcL [] n = 0`
  for `n ≠ 0`, and `hcL (p :: L) n` is `harishChandraInduct n p.1 (sum of the degrees of L) _ p.2
  (hcL L (sum of the degrees of L))` when the degrees sum to `n`, and `0` otherwise.

The API to prove: `harishChandraInduct n a b h α β` is a class function of its last argument and
linear in `(α, β)`; it is the character of an induced representation when `α, β` are characters; and
the *transitivity*: for lists `L₁, L₂` of total degrees `a`, `b`,
`hcL (L₁ ++ L₂) (a + b) = harishChandraInduct (a + b) a b rfl (hcL L₁ a) (hcL L₂ b)`, so that `hcL`
depends on the list only through the multiset of its entries.

### 7.2 The Jacquet restriction

`jacquetRestrict n a b h χ m = |Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ (toGL n (blockDiag n a b h m) * u)`, the average of
`χ` over the coset of the unipotent radical through the image in `GL (Fin n) F` of the element `m`
of the Levi subgroup `Lₐ` (3.3): the constant term of 3.5, as a function on `Lₐ`.

### 7.3 Frobenius reciprocity

Prove `jacquet_frobenius`: for every function `χ` on `GL (Fin n) F` and all `α, β`,
`⟨χ, harishChandraInduct n a b h α β⟩ = |Lₐ|⁻¹ ∑_{m ∈ Lₐ} jacquetRestrict n a b h χ m * conj (α m.1 * β m.2)`.

Route. Expand the pairing and substitute `y⁻¹ x y` for `x`; as `χ` is constant on conjugacy classes
the sum over `y` collapses, and `Pₐ = Lₐ ⋉ Uₐ` (3.3).

### 7.4 Induction of characters is a character

Prove `hcL_character`: if every entry of `L` is an irreducible character, `hcL L n` is the character
of a representation of `GL (Fin n) F`.

Route. 7.1 (b) is the character of an induced representation; compose by the transitivity of 7.1.

### 7.5 The Mackey formula

Prove `pairing_hcL`: for lists `L, L'` of cuspidal characters, each of total degree `n`,
`⟨hcL L n, hcL L' n⟩ = 0` if `L` and `L'` are not the same multiset, and `= 1` if `L` has no
repeated entry and `L` and `L'` are the same multiset.

Route. The Mackey formula for the restriction of an induced class function to a subgroup, applied to
the two parabolic subgroups, indexes the double cosets by the permutations of the blocks, and leaves
the bijections between the two multisets of degree-tagged cuspidal characters that respect the
degrees; a cuspidal character paired with a different cuspidal character of the same degree is `0`,
and the self-pairing of a cuspidal character is `1`. In general the pairing is the number of such
bijections, which takes the two values stated.

### 7.6 Existence of the cuspidal support

Prove `exists_cuspidal_support`: for every irreducible character `χ` of `GL (Fin n) F` there is a
list `L` of cuspidal characters with `(L.map Sigma.fst).sum = n` and `⟨χ, hcL L n⟩ ≠ 0`.

Route. Induction on `n`. If `χ` is cuspidal take `L = [χ]`, since `⟨χ, χ⟩ = 1`. Otherwise, by 3.5
some constant term of `χ` is not identically zero; that constant term is the character of the
`Uₐ`-invariant subspace of a representation with character `χ`, so some irreducible character `τ`
of `Lₐ` has nonzero pairing with `jacquetRestrict n a (n - a) rfl χ`. As `Lₐ` is a direct product, `τ`
is a product `τ₁ ⊗ τ₂` of irreducible characters of `GL (Fin a) F` and `GL (Fin (n - a) F)`, to
which the induction hypothesis gives lists `L₁, L₂` of cuspidal characters with
`⟨τ₁, hcL L₁ a⟩ ≠ 0` and `⟨τ₂, hcL L₂ (n - a)⟩ ≠ 0`. The Jacquet restriction of `χ` is a genuine
character of `Lₐ` (3.5), hence paired nonnegatively with every character; so
`⟨jacquetRestrict … χ, hcL L₁ a ⊗ hcL L₂ (n - a)⟩ ≥ ⟨jacquetRestrict … χ, τ₁ ⊗ τ₂⟩ > 0`. By 7.3 and
the transitivity of 7.1, `⟨χ, hcL (L₁ ++ L₂) n⟩ > 0`.

### 7.7 The Whittaker functional and the generic constituents

- (a) `upperUnitriangular n`: the set `U` of upper unitriangular matrices, the unipotent radical of
  the standard Borel subgroup, of order `q^{n(n-1)/2}`.
- (b) `superdiagonalSum hn M`: the sum of the entries `M i (i + 1)`, `i < n - 1`, of a matrix.
- (c) `whittakerFunctional ψ hn f = ∑_{u ∈ U} ψ (superdiagonalSum hn u) * f u`, for an additive
  character `ψ : AddChar F ℂ`. An irreducible character is *generic* for `ψ` when this is not `0`.
- (d) Prove `exists_generic_constituent`: for `ψ ≠ 1` and a list `L` of cuspidal characters of total
  degree `n ≥ 1`, there is an irreducible character `ρ` of `GL (Fin n) F` that is generic for `ψ`
  and has `⟨ρ, hcL L n⟩ ≠ 0`.

Route. A cuspidal character is generic (`wh ψ ρ ≠ 0` for every `ψ ≠ 1`), and the Whittaker functional
of `hcL L n` is not `0`: the Jacquet module of an induced representation along the Borel subgroup has
a filtration whose graded pieces are inductions from the parabolic subgroup of the block sizes of
`L` (the geometric lemma), and the functional is computed on the generic graded pieces. As
`hcL L n` is a nonnegative combination of irreducible characters (7.4), one of them is generic and
has nonzero multiplicity.

### 7.8 The number of generic irreducible characters

Prove `card_generic_irreducibles_le`: for `ψ ≠ 1` and `n ≥ 1`, there are at most `qⁿ - qⁿ⁻¹`
irreducible characters of `GL (Fin n) F` that are generic for `ψ`.

Route. A generic irreducible character is the generic constituent of exactly one multiset of cuspidal
characters (7.5 and 7.6), and a multiset with a repeated cuspidal character has no generic
constituent: both are read off the filtration of the Jacquet module along the Borel subgroup used in
7.7. So the generic irreducible characters are at most as many as the multisets of pairwise distinct
cuspidal characters of total degree `n`, which are at most the multisets of prime labels of total
degree `n`, that is the monic polynomials of degree `n` with nonzero constant term: `qⁿ - qⁿ⁻¹`
(1.1). The two facts about the filtration are the content of this section; they are stated here as
one target with 7.7 (d).

### 7.9 The counting lemma

Prove `card_cuspidal_multisets_le`: every `S : Finset (Multiset …)` of multisets of cuspidal
characters, each of total degree `n`, has at most `qⁿ - qⁿ⁻¹` elements.

Route. By 7.5 and 7.7 (d), distinct multisets have generic constituents that are distinct (a common
constituent would pair the two inductions), and by 7.8 there are at most `qⁿ - qⁿ⁻¹` generic
irreducible characters.

### 7.10 Green's theorem

Prove `green_cuspidal_characters`: for every `K` of degree `n` there is a map `τ` from the
characters of `Kˣ` to the functions on `GL (Fin n) F` with (i) at a regular `θ`, `τ θ` is a cuspidal
character of degree `∏_{i = 1}^{n-1} (q^i - 1)` whose value at an invertible matrix `g` with
irreducible characteristic polynomial is `(-1)^{n-1} ∑_{i < n} θ (z^{q^i})` for every root `z ∈ Kˣ`;
(ii) for regular `θ, θ'`, `τ θ = τ θ'` iff `θ' = θ^{q^i}` for some `i < n`; (iii) every cuspidal
character is `τ θ` for a regular `θ`.

Route. (i) is 6.3, (ii) is 6.4. For (iii), let `χ` be cuspidal. For each degree `e ≤ n` the
construction of 6.3 attaches to every monic irreducible `P` of degree `e` with nonzero constant term
a cuspidal character `ρ_P` of `GL (Fin e) F`, and `P ↦ ρ_P` is injective by 6.4. The set `S`
consisting of the multiset `{χ}` and of the multisets `{ρ_Q : Q ∣ f}` (the monic irreducible factors
with multiplicity of a monic `f` of degree `n` with nonzero constant term) consists of multisets of
cuspidal characters of total degree `n`. If `χ` is none of the `ρ_P` of degree `n`, these are
`1 + (qⁿ - qⁿ⁻¹)` distinct multisets, by unique factorization (1.1): a contradiction with 7.9.

### 7.11 The number of cuspidal characters

Prove `card_cuspidalCharacters`: the number of cuspidal characters of `GL (Fin n) F` equals the
number of monic irreducible polynomials of degree `n` with nonzero constant term, which is `N_q(n)`
for `n ≥ 2` and `q - 1` for `n = 1`.

Route. 7.10 makes the regular Frobenius orbits of characters of `Kˣ` correspond bijectively to the
cuspidal characters; 1.3 counts these orbits as `N_q(n)`, and 1.1 as prime labels.

### Examples

`GL₂(F)`: the multisets of cuspidal characters of total degree `2` are the `q(q - 1)/2` singletons
`{ρ}` with `ρ` cuspidal and the `q(q - 1)/2` pairs `{χ₁, χ₂}` of linear characters with repetition
(two linear characters among `q - 1`, unordered, with repetition): `q² - q` in all, the number of
monic polynomials of degree `2` with nonzero constant term, so 7.9 is an equality. For `{χ, χ}` the
two constituents are the twist of the trivial character and the twist `χ ∘ det * St` of the Steinberg
character; the latter is the generic one of 7.7 (d): `∑_{u ∈ U} ψ (u₁₂) * St(u) = q`, since `St` is
`0` at the nontrivial elements of `U` and `q` at the identity. `GL₁(F)`: the `q - 1` characters of
`Fˣ` are all cuspidal, all generic (`U` is trivial), and correspond to the `q - 1` prime labels
`X - a`, `a ≠ 0`.

### Dependencies

Layers 3–6; Tau Ceti's Mackey theory and induced class functions (Exact supplier contracts).

## Layer 8: uniqueness of the cuspidal support, and labels

### 8.1 Uniqueness of the cuspidal support

Prove `cuspidal_support_unique`: if `L` and `L'` are lists of cuspidal characters, each of total
degree `n`, both paired nontrivially with the same irreducible character `χ`, then `L` and `L'` are
the same multiset.

Route. 7.4 and 7.5: the two inductions are characters with a common constituent `χ`, so their
pairing is at least the product of the multiplicities of `χ`, a positive integer; by 7.5 the two
lists are the same multiset.

### 8.2 Prime labels

Prove `green_prime_labels`: for a Teichmüller character `θ` there is a family `τ P` of cuspidal
characters, indexed by the monic irreducible polynomials `P` of degree `n` with nonzero constant
term, with `τ P 1 = ∏_{i = 1}^{n-1} (q^i - 1)`, with `τ P = τ Q` only for `P = Q`, with every
cuspidal character some `τ P`, and with value `(-1)^{n-1} ∑_{i < n} θ (z^{q^i})` at a matrix `g` with
`Matrix.charpoly g = P`, for every root `z` of `P` in the algebraic closure.

Route. A prime label `P` determines the Frobenius orbit of its roots and, through 1.2 and 1.3, a
Frobenius orbit of regular characters of `Kˣ`; 6.4 shows that the cuspidal character of 6.3 attached
to any character of the orbit is the same. Compose with 7.10.

### Examples

`GL₂(F)`: the cuspidal supports are `{χ₁, χ₂}` (principal series, `χ₁ ≠ χ₂`), `{χ, χ}` (the two
constituents of the induction of `χ ⊗ χ` for a linear character `χ`: the twist of the Steinberg
character and the twist of the trivial character), and `{ρ}` (cuspidal). The prime labels of degree
`2` are the `q(q - 1)/2` irreducible quadratics with nonzero constant term.

### Dependencies

Layers 1 and 6–7.

## Downstream consumers

- **Depth-zero supercuspidal representations.** Over a local field `E` with residue field `F`, a
  cuspidal representation of `GLₙ(F)` inflates to `GLₙ(O_E)` and induces compactly to a
  depth-zero supercuspidal representation of `GLₙ(E)`; this roadmap supplies the characters on the
  finite-field side. [SmoothRepresentationsOfLocalGroups](../SmoothRepresentationsOfLocalGroups/README.md)
  treats Bushnell–Kutzko types in depth zero for `n = 2` (around lines 3493–3542) and
  [SmoothRepresentationsOfLocalGroupsPartII](../SmoothRepresentationsOfLocalGroupsPartII/README.md)
  §4.8 takes the depth-zero supercuspidals of `PGL₂(ℚ_p)` as an example; neither states the
  construction for general `n`, and it is not a target here.
- **The planned series** (Roadmap for a roadmap): R2 uses the prime labels of 8.2.
- **Zelevinsky's classification and Deligne–Lusztig theory** are not planned here (Scope).

## Scope and ownership

### Owned here

- the counts of Layer 1, the Teichmüller characters, the regular characters of `Kˣ` and their
  Frobenius orbits, the root-power-sums and their orthogonality;
- masses, the sizes of the elliptic classes and of the classes with given characteristic and
  minimal polynomial, the count of subspaces, cyclic vectors and the density recursion (Layer 2);
- the vocabulary for `GLₙ(F)`: `glPairing`, `IsIrreducibleCharacter`, `unipotentRadical`,
  `IsCuspidalCharacter`, `parabolic`, `levi`, `toGL`, `harishChandraInduct`, `hcL`, `blockDiag`,
  `jacquetRestrict`, with their API (Layers 3 and 7);
- Green's Möbius transform `psi` and its properties (Layer 4);
- the virtual characters `rootPowerSum θ k ∘ charpoly` and the pairing formula (Layer 5);
- the cuspidal character of a regular character, its injectivity up to Frobenius conjugacy,
  Green's theorem and the count of cuspidal characters (Layers 6 and 7);
- the existence and uniqueness of the cuspidal support of an irreducible character, and the
  parametrization of the cuspidal characters by prime labels (7.6, 8.1 and 8.2).

### Consumed, not redefined

- class functions, their bilinear pairing, virtual characters, the enumeration of the irreducible
  characters and the norm-one test: [RepresentationTheory.CharacterTheory](../RepresentationTheory/CharacterTheory/README.md)
  Layers 0–3, as Tau Ceti realizes them (`TauCeti.ClassFunction`, `TauCeti.ClassFunction.characterPairing`,
  `TauCeti.virtualCharacters`, `TauCeti.irreducibleCharacters`, `TauCeti.irreducibleCharacter`);
- the table of `GL₂(𝔽_q)`: the same roadmap's Layer 9, as realized in
  `TauCeti/RepresentationTheory/CharacterTable/GL2/`, which is a Check for `n = 2` (the Examples of
  Layer 3) and the instance `n = 2` of 7.10 and 8.2;
- Mackey theory, Frobenius reciprocity and induced class functions:
  [RepresentationTheory.InductionRestriction](../RepresentationTheory/InductionRestriction/README.md),
  as realized in `TauCeti/RepresentationTheory/Induction/`, consumed in 7.3 and 7.5;
- the conjugacy classes of `GL₂(𝔽_q)`: Tau Ceti's
  `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`, the case `n = 2` of the
  classification of matrices by their elementary divisors used in 2.2 and 2.4.

### Not owned here

- **The table of `GL₂(𝔽_q)`**: Layer 9 of
  [RepresentationTheory.CharacterTheory](../RepresentationTheory/CharacterTheory/README.md) owns
  it; that the cuspidal characters of 6.3 at `n = 2` are Tau Ceti's `TauCeti.GL2Cuspidal`, up to
  `θ ↦ θ^q`, is a Check of this roadmap, not a target.
- **Zelevinsky's classification of the irreducible characters of `GLₙ(F)` by multisegments**: 7.6
  and 8.1 give the cuspidal support, not the segment data, and 7.5 gives the pairing of two
  inductions, not the constitution of one; the generic constituent and its uniqueness are not
  pursued.
- **Deligne–Lusztig theory, character sheaves, Hall–Littlewood polynomials**: not planned; see the
  statement in [RepresentationTheory.CharacterTheory](../RepresentationTheory/CharacterTheory/README.md)
  that the Deligne–Lusztig theory of which the cuspidal series of `GL₂` is a special case is not
  planned there either.
- **Smooth representation theory of `GLₙ` over a local field**: Bernstein–Zelevinsky derivatives and
  the segment classification belong to
  [SmoothRepresentationsOfLocalGroups](../SmoothRepresentationsOfLocalGroups/README.md); the
  depth-zero construction is a consumer, not a target.
- **Finite groups of Lie type other than `GLₙ`**: the cuspidal characters of the other classical
  groups and of the exceptional groups, and their tables, are outside; the only finite groups of
  Lie type of which this roadmap treats characters are the `GLₙ(F)`.

## Exact supplier contracts

### From Mathlib

- `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean`: `Matrix.card_GL_field`
  (`Nat.card (GL (Fin n) 𝔽) = ∏ i, (q ^ n - q ^ i)`) and the notation `GL`.
- `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`: `Matrix.charpoly`;
  `Mathlib/LinearAlgebra/Charpoly/Basic.lean`: `LinearMap.charpoly`;
  `Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean`: `Matrix.mulVecLin`, `charpoly_mulVecLin`,
  `LinearEquiv.charpoly_conj`.
- `Mathlib/Algebra/Polynomial/Roots.lean`: `Polynomial.roots`;
  `Mathlib/FieldTheory/AlgebraicClosure.lean`: `AlgebraicClosure`;
  `Mathlib/RingTheory/Polynomial/Basic.lean` (and `Content.lean`): `Polynomial.aeval`,
  `Polynomial.map`.
- `Mathlib/FieldTheory/Finite/Basic.lean`: the cyclicity of `Gal(L/K)` for finite fields;
  `Mathlib/FieldTheory/Finite/GaloisField.lean`: `GaloisField`.
- `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`: `Submodule.finrank_lt`.
- `Mathlib/RepresentationTheory/Character.lean`: `Representation.character`,
  `FDRep.char_orthonormal`; `Mathlib/RepresentationTheory/FDRep.lean`: `FDRep`,
  `FDRep.character`; `Mathlib/CategoryTheory/Simple.lean`: `CategoryTheory.Simple`.
- `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`: `ArithmeticFunction.moebius`.
- `Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean`:
  `UniqueFactorizationMonoid.normalizedFactors`.
- `ConjClasses`, `Module.AEval'`, `Matrix.of`, `finCongr`: their defining modules.

### From Tau Ceti

- `TauCeti/RepresentationTheory/CharacterTable/ClassFunction.lean`: `TauCeti.ClassFunction`,
  `TauCeti.ClassFunction.ofCharacter`, `TauCeti.ClassFunction.equivConjClasses`.
- `TauCeti/RepresentationTheory/CharacterTable/Pairing.lean`:
  `TauCeti.ClassFunction.characterPairing` (`LinearMap.BilinForm k (ClassFunction k G)`),
  `TauCeti.ClassFunction.characterPairing_apply` (`= |G|⁻¹ ∑ g, f₁ g * f₂ g⁻¹`).
- `TauCeti/RepresentationTheory/CharacterTable/VirtualCharacter.lean`:
  `TauCeti.virtualCharacters`, `TauCeti.character_mem_virtualCharacters`,
  `TauCeti.conj_apply_of_mem_virtualCharacters`,
  `TauCeti.exists_eq_irreducibleCharacter_or_neg`,
  `TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one`,
  `TauCeti.exists_simple_character_eq_of_characterPairing_self_eq_one`.
- `TauCeti/RepresentationTheory/CharacterTable/Table.lean`: `TauCeti.irreducibleCharacters`,
  `TauCeti.irreducibleCharacter`.
- `TauCeti/RepresentationTheory/CharacterTable/GL2/Cuspidal/Basic.lean` and `Irreducible.lean`:
  `TauCeti.GL2CuspidalVirtualCharacter`, `TauCeti.GL2CuspidalVirtualCharacter_apply_jordanGL`,
  `TauCeti.GL2Cuspidal`, `TauCeti.finrank_GL2Cuspidal`, `TauCeti.simple_GL2Cuspidal`.
- `TauCeti/RepresentationTheory/Induction/ClassFunction.lean` and the `Mackey/` directory:
  induced class functions and the Mackey formula (the exact declarations are named by the
  InductionRestriction roadmap's own supplier contract; this roadmap consumes them as that roadmap
  states them).
- `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`: the classes of `GL₂`.
- `TauCeti/GroupTheory/FiniteAbelian/CharacterOrthogonality.lean`: character orthogonality for
  finite abelian groups (1.4).

### From TauCetiRoadmap.RepresentationTheory.CharacterTheory

- Layer 0: `TauCeti.ClassFunction` and its pairing (as above), the identification of the pairing
  with the raw sum of `char_orthonormal`.
- Layer 3.5: virtual characters and their lattice structure, used in 3.2, 5.1 and 6.2.
- Layer 9 (§9.1, §9.2): the classes, principal series, Steinberg character and cuspidal characters
  of `GL₂(𝔽_q)`, as realized in the library; a Check for `n = 2`.

### From TauCetiRoadmap.RepresentationTheory.InductionRestriction

- Induced class functions and Frobenius reciprocity; the Mackey decomposition and its
  irreducibility criterion: consumed in 7.3 and 7.5, as realized in
  `TauCeti/RepresentationTheory/Induction/`.

## Roadmap for a roadmap (not work to attempt now)

This section is motivation for future roadmaps. **Contributors must not attempt it**: nothing in it
is a target of this roadmap, and nothing in it may be cited as a target in a pull request.

The plan is a series of roadmaps bringing the main line of the Alpöge–Claude proof of the Riemann
hypothesis into Tau Ceti, layer by layer. The series starts here, with Green's classification,
which is the only part of the main line that is proved from Mathlib alone in the source
formalization. The remaining layers follow in dependency order, with the roadmaps each would
consume; none of these dependencies is a target here.

- **R2. Depth-zero local Langlands for `GLₙ`, and Green's labels.** The dictionary between cuspidal
  representations of `GLₙ(F)`, regular characters of `Kˣ` and irreducible polynomials, and its
  transfer to depth-zero supercuspidal representations of `GLₙ(E)` and to elliptic Weil–Deligne
  representations. Suppliers: `SmoothRepresentationsOfLocalGroups` (Bernstein decomposition,
  Bushnell–Kutzko types; the local Langlands correspondence of `GLₙ` is a supplied convention
  there, §SR.5.2), `ArithmeticGaloisRepresentations` (Weil–Deligne representations, Layer 2).
- **R3. Galois representations attached to automorphic representations by theta lifts.** The
  statement `Row0b` of the source: to a regular algebraic polarized cuspidal automorphic
  representation of a unitary group over a CM field is attached an ℓ-adic Galois representation with
  prescribed Hodge–Tate weights, satisfying local–global compatibility. This must be coordinated
  with `AutomorphicGaloisRepresentationsPartII`, which states the same conclusion by the
  cohomological route (AG2.0, AG2.1a, AG2.3, AG2.5); the theta-lift route would reach the same goal
  by another road.
- **R4. The automorphic window.** The statement `VWin` of the source: a bound on the total ℓ-adic
  length of the Galois cohomology groups of the layers of the cyclotomic tower, a weakened form of
  Vandiver's conjecture obtained by killing classes by twisting. Suppliers: `IntegralIwasawaTheory`
  (Layer 7: the cyclotomic `ℤₚ`-extension, class number growth, `VandiverCondition`),
  `SelmerIwasawaCohomology` (§0.6–0.9, §3.7, §4.16–4.21), `ArithmeticKTheory` (§7.5: the K-groups of
  `ℤ` and Vandiver), `CyclotomicClassGroupsAndStickelberger`.
- **R5. Theta-lift chains and the analytic hypotheses.** The package `HypsAlt … DefiniteSideCondition`
  of the source: iterated theta lifts between totally definite unitary groups, the positivity of a
  determinant and the bootstrap that follows it, periods (Bessel periods, the see-saw), covolumes
  and masses (Siegel mass, Chowla–Selberg, Bost's slope inequality), class number formulas, lattice
  point counts, twisted period integrals. Suppliers: `MetaplecticAutomorphicForms` (Layer 6: Weil
  representation, Howe duality, see-saw, global theta lifts, Rallis, Siegel–Weil),
  `GanGrossPrasadUnitaryGroups` (Bessel models, Jacquet–Rallis, the relative trace formula),
  `AutomorphicLFunctionsAndLocalFactorsPartII` (the doubling method),
  `ArakelovGeometryAndAbelianHeights` (Faltings heights, Bost's lower bound),
  `ComplexMultiplicationAndExplicitReciprocityPartII` (Chowla–Selberg, averaged Colmez),
  `GeometryOfNumbersAndQuadraticArithmetic` (hermitian lattices), `PELModuli` and
  `PotentialAutomorphyInfrastructurePartII` (unitary PEL data, definite unitary groups).
- **R6. The explicit formula and zero-freeness.** The smoothed explicit formula for Dirichlet
  `L`-functions (kernel `(1 - t)₊`) with Landau's theorem; the reduction of the generalized Riemann
  hypothesis to a Chebyshev-type bound for twisted von Mangoldt sums; and the supply of every
  primitive Dirichlet character by a class field of an imaginary quadratic field (primes in short
  intervals, Linnik's theorem). Suppliers: `ZerosOfLFunctions` (Layer 8: the Weil formula; Layer 9:
  GRH as a divisor statement), `QuasiRiemannHypothesis` (§1.1 zero-free half-planes, §5.5 primitive
  to all characters, §11.1 the zero strip), `AnalyticNumberTheoryPartI` (§1.3–1.9: the explicit
  formula), `AnalyticNumberTheoryPartIII` (§8.3 Landau's lemma, §10.2 the transfer theorem). For
  primes in short intervals in imaginary quadratic fields and unconditional Linnik no roadmap
  exists today (only explicit versions in `ExplicitPrimeCounting` Layer 7, and Linnik under GRH in
  §6.5 there); that input would be work of R6 or of a roadmap of its own.
- **From `EveryCharacter` to `RiemannHypothesis`.** Nothing to do: `QuasiRiemannHypothesis` §1.1,
  §5.5, §11.1 and `ZerosOfLFunctions` Layer 9 already state every step.
- **What has no roadmap at all:** a weakened Vandiver obtained by twisting; Behrend's theorem on the
  class numbers of the layers of the cyclotomic tower; iterated theta lifts between totally definite
  unitary groups; the Siegel mass formula for hermitian lattices; Bost's slope inequality as a
  target; Chowla–Selberg periods; Guinand's form of the explicit formula and the definite-sign
  determinant argument; the existence of the local Langlands correspondence for a general reductive
  group.

The source formalization is cited under Provenance. Its release carries no licence text, so nothing
may be copied from it before its author has been consulted.

## Provenance (secondary)

This section is secondary: it maps the statements of this roadmap to an existing formalization and
prescribes nothing. The Lean project of Levent Alpöge (with Claude), *Riemann hypothesis in Lean*
(<https://alpo.ge/>; mirror <https://github.com/CocoSgt/riemann-hypothesis-lean>), contains, at the
release of 2026-11-20, proofs of the statements below; paths are relative to `source/src/` of that
release and the names are the names of the files, which state one declaration each. Coordinate with
the author before porting any of it: the release carries no licence file. `CharacterTheory` stands
for `Development/AbelianVarietyTheory/Proofs/CharacterTheory/` and `InertiaEigenvalues` for
`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`.

| § | Content | Files |
| --- | --- | --- |
| 1.1 | counts of monic polynomials; prime labels and regular character orbits | `InertiaEigenvalues/NcardMonicNatDegreeCoeffZeroNeZero.lean`, `MonicIrreducibleInjectRegularCharacterOrbits.lean` |
| 1.2 | the Teichmüller character | `CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean` |
| 1.4 | root-power-sums and their orthogonality | `CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean`, `FrobeniusTorusMinpolyDegreeRootPowerSum.lean`, `RootPowerSumCharacterAdditiveAndXSubOnePow.lean` |
| 2.2–2.4 | subspaces, cyclic vectors, densities | `CharacterTheory/CardSubspacesMulGeneralLinearGroupCard.lean`, `CardSubspacesOfFinrankMulCardBases.lean`, `FinsumCardCyclicVectorsInvariantSubspaces.lean`, `EndomorphismMassOfCharpolyCardCyclicVectors.lean`, `CharpolyEndomorphismDensityGLRecursion.lean` |
| 3.3–3.5, 4.7 | the group `GLₙ(𝔽_q)`, cuspidal characters, primitivity | `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean`; `CharacterTheory/FinsumUnipotentRadicalEqZero.lean`, `IsPrimitiveExtendZeroOfSumUnipotentRadical.lean`, `EqZeroOfNotPrimary.lean`, `PrimitiveEndClassFunctionEqZeroOfPrimary.lean`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean` |
| 4.1–4.6 | `psi`, the Möbius transform | `Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean`; `CharacterTheory/CharpolyEqFinsumPsi.lean`, `InvariantSubspaceMobiusInverseCharpolyLinearEquiv.lean`, `…CharpolyOfIrreducible.lean`, `…OneProdIco.lean`, `FinsumMobiusInverseCharpolyInvariantLe.lean`, `EndomorphismMassMobiusInverseMonicEq.lean`, `IsPrimitiveEndClassFunctionInvariantSubspaceMobius.lean`, `InvertibleEndomorphismInnerProductPrimitiveMobius.lean` |
| 5.1–5.2 | virtual characters and the pairing formula | `CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGL.lean`, `InvertibleEndInnerProductRootPowerSumEqTorusSum.lean`, `InnerProductRootPowerSumEqOfFrobeniusModEq.lean`, `InvertibleEndInnerProductRootPowerSumMobius.lean` |
| 6.1–6.3 | cuspidal characters of regular characters | `CharacterTheory/IsCharacterCuspidalRootSumRegular.lean`; `Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean`; `InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean`, `GreenCuspidalCharsByRegularCharsProof.lean` |
| 7.1–7.9 | Harish–Chandra induction, the Mackey formula, generic constituents, the count | `LabelDatum.lean` (above); `InertiaEigenvalues/CharacterPairingHarishChandraCuspidalMackey.lean`, `ExistsGenericConstituentHarishChandraCuspidal.lean`, `ExistsCuspidalListHarishChandraPairingNeZero.lean`, `NcardGenericIrreducibleCharactersGLnLe.lean`, `CardCuspidalMultisetsTotalDegreeLe.lean` |
| 7.10–8.2 | Green's theorem and the labels | `LabelDatum.lean` (`GlobalTheory.GLq.Green`); `InertiaEigenvalues/CuspidalCharExistsOfGreen.lean`, `CuspidalCharacterLabelUniqueGLn.lean`, `HarishChandraSeriesLabelExistsUniqueGLn.lean` |

In the source, the existence of the cuspidal support (7.6) is proved through *generic*
constituents (a Whittaker functional nonzero on the induction) rather than through the Jacquet
restriction; both routes are available.

## References

- J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. **80**
  (1955), 402–447: the cuspidal characters and their values, the parametrization by polynomials.
- A. V. Zelevinsky, *Representations of finite classical groups: a Hopf algebra approach*, Lecture
  Notes in Mathematics **869**, Springer-Verlag, 1981: cuspidal representations, Harish–Chandra
  induction and its Hopf-algebra structure, the multisegment classification of `GLₙ`.
- I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford Mathematical
  Monographs, Oxford University Press, 1995: Chapter IV, Green's functions of `GLₙ(𝔽_q)` and its
  character table.
- F. Digne and J.-M. Michel, *Representations of finite groups of Lie type*, 2nd ed., London
  Mathematical Society Student Texts **95**, Cambridge University Press, 2020: the Deligne–Lusztig
  characters and their values (Green's theorem as the case of `GLₙ`).
- P. Deligne and G. Lusztig, *Representations of reductive groups over finite fields*, Ann. of Math.
  (2) **103** (1976), 103–161.
- R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS **25** (1965),
  49–80; *The representations of GL(3,q), GL(4,q), PGL(3,q), and PGL(4,q)*, Canad. J. Math. **3**
  (1951), 225–235.
- G. W. Mackey, *On induced representations of groups*, Amer. J. Math. **73** (1951), 576–592.
- C. W. Curtis and I. Reiner, *Methods of representation theory, with applications to finite groups
  and orders*, Vol. II, Wiley, 1987: Harish–Chandra induction for finite groups with a
  `BN`-pair.
- Attributed in prose without a locator: C. F. Gauss, *Disquisitiones Arithmeticae* (the number of
  monic irreducible polynomials of given degree over a finite field).
