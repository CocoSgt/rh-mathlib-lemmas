import Mathlib

/-!
# Cuspidal characters of general linear groups over finite fields: target signatures

**This file is not the roadmap.** The roadmap is `README.md`. This file states the roadmap's
headline theorems against the pinned Mathlib, each with `sorry`, together with the few definitions
they need; every definition has a real body. The README's remaining steps, API lists and Checks
are not restated, and `Suggested.lean` is read as suggested forms, never as an exhaustive
checklist.

Everything is stated for a finite field `F` with `q = Nat.card F` elements and the group
`GL (Fin n) F` of invertible `n × n` matrices. A character is here a function to `ℂ`:
`IsIrreducibleCharacter` says that it is the character of a simple finite-dimensional complex
representation, and `IsCuspidalCharacter` that in addition it sums to zero over the unipotent
radical of every standard parabolic subgroup; such a character vanishes off the elements whose
characteristic polynomial is a power of an irreducible, and it is determined by its values on the
elements with irreducible characteristic polynomial. In the roadmap these are read through Tau Ceti's
`TauCeti.ClassFunction`, `TauCeti.virtualCharacters` and `TauCeti.irreducibleCharacters`; those
modules cannot be imported here, so bare functions are used and the pairing `glPairing` is
written out (it is `TauCeti.ClassFunction.characterPairing` on `ℂ`).

The construction behind the headline is Green's. For a multiplicative map `θ` from the algebraic
closure of `F` to `ℂ` and an integer `k`, the `k`-th root-power-sum of a polynomial `P` is
`∑_{P(α) = 0} θ α ^ k`. From an additive function `s` on monic polynomials one forms `ψ` on the
endomorphisms of a finite-dimensional `F`-vector space `V` by Möbius inversion over the lattice of
invariant subspaces, `psi s V g = s (charpoly g) - ∑_{W ⫋ V} psi s W (g on W)`. Green's theorem
says: for an extension `K` of `F` of degree `n`, the characters `θ` of `Kˣ` whose conjugates
`θ ^ q ^ i`, `i < n`, are pairwise distinct are in bijection with the cuspidal characters of
`GL (Fin n) F`, by `θ ↦ (-1) ^ (n - 1) • ψ (rootPowerSum θ 1)`.
-/

noncomputable section

open Polynomial

open scoped Classical

namespace TauCetiRoadmap.CharactersOfGLnOverFiniteFields

variable {F : Type} [Field F] [Fintype F]

/-! ## Layer 1: monic polynomials, the Teichmüller character, and root-power-sums -/

/-- 1.1 The number of monic irreducible polynomials of degree `n ≥ 1` over `F` is
`(1/n) ∑_{d ∣ n} μ (d) q ^ (n / d)`, with `q = Nat.card F` and `μ` the Möbius function. -/
theorem card_monicIrreducible (n : ℕ) (hn : 0 < n) :
    (n : ℤ) * (Nat.card {P : F[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = n} : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((Nat.card F : ℤ) ^ (n / d)) := by
  sorry

/-- 1.2 A Teichmüller character of the algebraic closure: a multiplicative map to `ℂ` that is
injective off `0`. -/
theorem exists_teichmullerChar : ∃ θ : AlgebraicClosure F →* ℂ,
    ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  sorry

/-- 1.3 A character `θ` of `Kˣ`, for `K` an extension of `F` of degree `n`, is *regular* when its
conjugates `θ ^ q ^ i`, `i < n`, are pairwise distinct. -/
def IsRegular (F : Type) [Field F] [Fintype F] (n : ℕ) {K : Type} [Field K] [Algebra F K]
    (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → θ ^ (Nat.card F ^ i) = θ ^ (Nat.card F ^ j) → i = j

/-- 1.4 The `k`-th root-power-sum of a polynomial `P` over `F`: the sum of `θ α ^ k` over the
roots `α` of `P` in the algebraic closure, with multiplicity. -/
def rootPowerSum (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X]) : ℂ :=
  ((P.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).sum

/-- 1.4 Root-power-sums are additive over products. -/
theorem rootPowerSum_add (θ : AlgebraicClosure F →* ℂ) (k : ℕ) {P Q : F[X]} (hP : P.Monic)
    (hQ : Q.Monic) :
    rootPowerSum θ k (P * Q) = rootPowerSum θ k P + rootPowerSum θ k Q := by
  sorry

/-- 1.4 The `k`-th root-power-sum of `(X - 1) ^ j` is `j`, for every `k`. -/
theorem rootPowerSum_one_sub_pow (θ : AlgebraicClosure F →* ℂ) (k j : ℕ) :
    rootPowerSum θ k ((X - C (1 : F)) ^ j) = j := by
  sorry

/-! ## Layer 2: endomorphisms of a finite vector space and their characteristic polynomials -/

/-- 2.1 The mass of a function `φ` on the endomorphisms of `V` over the fibre of the
characteristic polynomial at `P`: the sum of `φ g` over all `g` with `charpoly g = P`. -/
def mass {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | LinearMap.charpoly g = P}, φ g

/-- 2.2 For a monic irreducible `f` of degree `d ≥ 1` with nonzero constant term, the endomorphisms
of `Fin d → F` with characteristic polynomial `f` are the invertible ones, they form one
conjugacy class under `GL (Fin d) F`, and there are `|GL (Fin d) F| / (q ^ d - 1)` of them. -/
theorem mass_one_irreducible (f : F[X]) (hf : Irreducible f) (hfM : f.Monic) (hf0 : f.coeff 0 ≠ 0) :
    mass (fun _ : Module.End F (Fin f.natDegree → F) => 1) f =
      (Nat.card (GL (Fin f.natDegree) F) : ℂ) / ((Nat.card F : ℂ) ^ f.natDegree - 1) := by
  sorry

/-- 2.3 The number of subspaces of rank `a` of a rank-`n` space is the Gaussian binomial
coefficient: the left product is `(q ^ a - q ^ i)` times that number, the right one is over
`q ^ n`. -/
theorem card_submodules (n a : ℕ) :
    Nat.card {W : Submodule F (Fin n → F) // Module.finrank F W = a} *
      ∏ i ∈ Finset.range a, ((Nat.card F : ℕ) ^ a - (Nat.card F : ℕ) ^ i) =
        ∏ i ∈ Finset.range a, ((Nat.card F : ℕ) ^ n - (Nat.card F : ℕ) ^ i) := by
  sorry

/-! ## Layer 3: class functions on `GL (Fin n) F`, constant terms, and cuspidal characters -/

/-- 3.1 The pairing of two functions on `GL (Fin n) F`: the average of `φ x * conj (ψ x)`. -/
def glPairing (n : ℕ) (φ ψ : GL (Fin n) F → ℂ) : ℂ :=
  (Nat.card (GL (Fin n) F) : ℂ)⁻¹ * ∑ x, φ x * (starRingEnd ℂ) (ψ x)

/-- 3.2 `χ` is the character of a simple finite-dimensional complex representation. -/
def IsIrreducibleCharacter (n : ℕ) (χ : GL (Fin n) F → ℂ) : Prop :=
  ∃ V : FDRep ℂ (GL (Fin n) F), CategoryTheory.Simple V ∧ ∀ x, V.character x = χ x

/-- 3.3 The unipotent radical of the standard parabolic subgroup with blocks `a`, `n - a`: the
invertible matrices that agree with the identity in their first `a` columns. -/
def unipotentRadical (F : Type) [Field F] [Fintype F] (n a : ℕ) : Finset (GL (Fin n) F) :=
  Finset.univ.filter fun u : GL (Fin n) F =>
    ∀ i j : Fin n, (j : ℕ) < a → (u : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0

/-- 3.3 The standard parabolic subgroup with blocks `a`, `n - a`: the block upper triangular
matrices. -/
def parabolic (F : Type) [Field F] [Fintype F] (n a : ℕ) : Finset (GL (Fin n) F) :=
  Finset.univ.filter fun x : GL (Fin n) F =>
    ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (x : Matrix (Fin n) (Fin n) F) i j = 0

/-- 3.3a The matrix `M` read inside `GL (Fin n) F`; the junk value `1` occurs only when `M` is
not invertible. -/
def toGL (n : ℕ) (M : Matrix (Fin n) (Fin n) F) : GL (Fin n) F :=
  if h : IsUnit M then h.unit else 1

/-- 3.3b The block-diagonal matrix with diagonal blocks `m.1` and `m.2`, for block sizes `a`, `b`
with `a + b = n`; it is the image in matrices of an element of the Levi subgroup `Lₐ`. -/
def blockDiag (n a b : ℕ) (h : a + b = n) (m : GL (Fin a) F × GL (Fin b) F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < a then
      if hj : (j : ℕ) < a then (m.1 : Matrix (Fin a) (Fin a) F) ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else
      if hj : a ≤ (j : ℕ) then
        (m.2 : Matrix (Fin b) (Fin b) F) ⟨i - a, by omega⟩ ⟨j - a, by omega⟩
      else 0

/-- 3.4 A cuspidal character: an irreducible character whose sum over the unipotent radical of
every standard parabolic subgroup is zero. -/
def IsCuspidalCharacter (n : ℕ) (χ : GL (Fin n) F → ℂ) : Prop :=
  IsIrreducibleCharacter n χ ∧
    ∀ a : ℕ, 0 < a → a < n → ∑ u ∈ unipotentRadical F n a, χ u = 0

/-- 3.5 For an irreducible character, the sums over the unipotent radicals vanish as soon as the
sums over the cosets of every unipotent radical do: the definition of cuspidal is equivalent to
the vanishing of every constant term. -/
theorem cuspidal_iff_constant_terms (n : ℕ) (χ : GL (Fin n) F → ℂ) :
    IsCuspidalCharacter n χ ↔ IsIrreducibleCharacter n χ ∧
      ∀ (a b : ℕ) (h : a + b = n), 0 < a → a < n →
        ∀ m : GL (Fin a) F × GL (Fin b) F,
          ∑ u ∈ unipotentRadical F n a, χ (toGL n (blockDiag n a b h m) * u) = 0 := by
  sorry

/-- 3.6 A cuspidal character vanishes at every invertible matrix whose characteristic polynomial
has at least two distinct monic irreducible factors (is not a power of an irreducible). -/
theorem cuspidal_vanish_off_primary (n : ℕ) (χ : GL (Fin n) F → ℂ) (hχ : IsCuspidalCharacter n χ)
    (x : GL (Fin n) F) (hx : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = f ^ m) : χ x = 0 := by
  sorry

/-- 3.7 Two cuspidal characters that agree at the invertible matrices with irreducible
characteristic polynomial are equal. -/
theorem cuspidal_eq_of_eq_on_elliptic (n : ℕ) (χ χ' : GL (Fin n) F → ℂ)
    (hχ : IsCuspidalCharacter n χ) (hχ' : IsCuspidalCharacter n χ')
    (h : ∀ x : GL (Fin n) F, Irreducible (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)) →
      χ x = χ' x) : χ = χ' := by
  sorry

/-! ## Layer 4: Green's Möbius transform on the lattice of invariant subspaces -/

/-- 4.1 `psi s V g` is defined from a function `s` on `F[X]` by Möbius inversion over the
`g`-invariant subspaces of `V`. -/
def psi (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : ℂ :=
  s (LinearMap.charpoly g) -
    ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
  termination_by Module.finrank F V
  decreasing_by
    exact Submodule.finrank_lt (by simpa using W.2.1)

/-- 4.2 The inversion identity: `s (charpoly g)` is the sum of `psi` over all invariant subspaces. -/
theorem charpoly_eq_sum_psi (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) :
    s (LinearMap.charpoly g) =
      ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  sorry

/-- 4.3 `psi` is a class function: it is invariant under conjugation by a linear automorphism. -/
theorem psi_conj (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : V ≃ₗ[F] V) (g : Module.End F V) : psi s V (e.conj g) = psi s V g := by
  sorry

/-- 4.4 At an endomorphism with irreducible characteristic polynomial, `psi s` is `s` of the
characteristic polynomial. -/
theorem psi_of_irreducible (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g)) :
    psi s V g = s (LinearMap.charpoly g) := by
  sorry

/-- 4.5 The mass formula. Let `s` be additive over products of monic polynomials, `n ≥ 1`, and
let `f` be monic irreducible with `m ≥ 1` and `f.natDegree * m = n`. The mass of `psi s` over
the fibre of `f ^ m` is `|GL (Fin n) F| * s f / (q ^ n - 1)`; over the fibre of a monic `P` of
degree `n` with at least two distinct irreducible factors the mass of `psi s` is `0` (4.2 and
additivity, see the README). -/
theorem mass_psi (s : F[X] → ℂ) (hs : ∀ P Q : F[X], P.Monic → Q.Monic → s (P * Q) = s P + s Q)
    {n : ℕ} (hn : 0 < n) {f : F[X]} {m : ℕ} (hf : Irreducible f) (hm : 0 < m) (hfM : f.Monic)
    (hfn : f.natDegree * m = n) :
    mass (psi s (Fin n → F)) (f ^ m) =
      (Nat.card (GL (Fin n) F) : ℂ) * s f / ((Nat.card F : ℂ) ^ n - 1) := by
  sorry

/-- 4.6 At the identity, `psi s` is `∏_{i = 1}^{n - 1} (1 - q ^ i)` whenever `s ((X - 1) ^ j) = j`
for every `j`. -/
theorem psi_one (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C (1 : F)) ^ j) = j) {n : ℕ} (hn : 0 < n) :
    psi s (Fin n → F) 1 = ∏ i ∈ Finset.Ico 1 n, (1 - (Nat.card F : ℂ) ^ i) := by
  sorry

/-! ## Layer 5: Frobenius torus characters -/

/-- 5.1 For a Teichmüller character `θ`, the class function `rootPowerSum θ k` of the
characteristic polynomial on `GL (Fin n) F` is a virtual character. -/
theorem rootPowerSum_virtualCharacter (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    ∃ V W : FDRep ℂ (GL (Fin n) F), ∀ x : GL (Fin n) F,
      rootPowerSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)) =
        V.character x - W.character x := by
  sorry

/-- 5.2 The pairing of `psi` of the `k`-th root-power-sum with the `l`-th root-power-sum of the
characteristic polynomial is `|GL (Fin n) F|` times the number of indices `i < n` with
`k * q ^ i ≡ l [MOD q ^ n - 1]`. -/
theorem pairing_psi_rootPowerSum (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k l : ℕ) :
    glPairing n (fun x : GL (Fin n) F => psi (rootPowerSum θ k) (Fin n → F) (Matrix.mulVecLin x))
      (fun x : GL (Fin n) F => rootPowerSum θ l (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))) =
        (Nat.card (GL (Fin n) F) : ℂ) *
          ((Finset.range n).filter fun i => k * (Nat.card F ^ i) ≡ l [MOD Nat.card F ^ n - 1]).card := by
  sorry

/-- 5.3 The Möbius transform of a root-power-sum, restricted to `GL (Fin n) F`, is a virtual
character. -/
theorem psi_rootPowerSum_virtualCharacter (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    ∃ V W : FDRep ℂ (GL (Fin n) F), ∀ x : GL (Fin n) F,
      psi (rootPowerSum θ k) (Fin n → F) (Matrix.mulVecLin x) = V.character x - W.character x := by
  sorry

/-! ## Layer 6: cuspidal characters from regular characters -/

/-- 6.1 The construction behind 6.3: for a Teichmüller character `θ`, the function
`(-1) ^ (n - 1) * psi (rootPowerSum θ k)` on `GL (Fin n) F` has pairing `1` with itself as soon
as `k` is regular in the sense that `k * q ^ i ≢ k [MOD q ^ n - 1]` for `0 < i < n`, and it is a
cuspidal character then. -/
theorem self_pairing_psi_rootPowerSum (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : ∀ i : ℕ, 0 < i → i < n → ¬ k * (Nat.card F ^ i) ≡ k [MOD Nat.card F ^ n - 1]) :
    glPairing n (fun x : GL (Fin n) F => (-1 : ℂ) ^ (n - 1) *
        psi (rootPowerSum θ k) (Fin n → F) (Matrix.mulVecLin x))
      (fun x : GL (Fin n) F => (-1 : ℂ) ^ (n - 1) *
        psi (rootPowerSum θ k) (Fin n → F) (Matrix.mulVecLin x)) = 1 :=
  sorry

/-- 6.2 Under the hypothesis of 6.1 the function there is a cuspidal character. -/
theorem cuspidal_of_self_pairing (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : ∀ i : ℕ, 0 < i → i < n → ¬ k * (Nat.card F ^ i) ≡ k [MOD Nat.card F ^ n - 1]) :
    IsCuspidalCharacter n fun x : GL (Fin n) F => (-1 : ℂ) ^ (n - 1) *
      psi (rootPowerSum θ k) (Fin n → F) (Matrix.mulVecLin x) :=
  sorry

/-- 6.3 To a regular character `θ` of `Kˣ`, with `K` of degree `n` over `F`, corresponds a
cuspidal character of `GL (Fin n) F` of degree `∏_{i = 1}^{n-1} (q ^ i - 1)`, whose value at an
invertible matrix `g` with irreducible characteristic polynomial is
`(-1) ^ (n - 1) ∑_{i < n} θ (z ^ q ^ i)` for every root `z ∈ Kˣ` of that polynomial. -/
theorem cuspidalCharacter_of_regular (n : ℕ) (hn : 0 < n) (K : Type) [Field K] [Algebra F K]
    (hK : Module.finrank F K = n) (θ : Kˣ →* ℂˣ) (hθ : IsRegular F n θ) :
    ∃ χ : GL (Fin n) F → ℂ, IsCuspidalCharacter n χ ∧
      χ 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
      ∀ g : GL (Fin n) F, Irreducible (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) →
        ∀ z : Kˣ, aeval (z : K) (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) = 0 →
          χ g = (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, ((θ (z ^ (Nat.card F ^ i)) : ℂˣ) : ℂ) := by
  sorry

/-! ## Layer 7: Harish–Chandra induction, cuspidal support, generic constituents, and Green's theorem -/

/-- 7.1a The two diagonal blocks of a matrix, for block sizes `a`, `b` with `a + b = n`, each read
in its general linear group through `toGL`. -/
def levi (n a b : ℕ) (h : a + b = n) (x : Matrix (Fin n) (Fin n) F) : GL (Fin a) F × GL (Fin b) F :=
  (toGL a (Matrix.of fun i j => x (finCongr h (Fin.castAdd b i)) (finCongr h (Fin.castAdd b j))),
   toGL b (Matrix.of fun i j => x (finCongr h (Fin.natAdd a i)) (finCongr h (Fin.natAdd a j))))

/-- 7.1b Harish–Chandra induction of a pair of class functions from `GL (Fin a) F × GL (Fin b) F`:
the usual induced class function from the standard parabolic subgroup. -/
def harishChandraInduct (n a b : ℕ) (h : a + b = n) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F) : ℂ :=
  ((parabolic F n a).card : ℂ)⁻¹ *
    ∑ y ∈ Finset.univ.filter fun y : GL (Fin n) F => (y⁻¹ * x * y) ∈ parabolic F n a,
      α (levi n a b h (y⁻¹ * x * y : Matrix (Fin n) (Fin n) F)).1 *
        β (levi n a b h (y⁻¹ * x * y : Matrix (Fin n) (Fin n) F)).2

/-- 7.1c Harish–Chandra induction along a list of degree-tagged class functions: the head is
induced against the induction of the tail. The result is `0` unless the degrees sum to `n`. -/
def hcL : (L : List (Σ d : ℕ, GL (Fin d) F → ℂ)) → (n : ℕ) → GL (Fin n) F → ℂ
  | [], 0 => fun _ => 1
  | [], _ => fun _ => 0
  | p :: L, n => fun x =>
      if h : p.1 + (L.map Sigma.fst).sum = n then
        harishChandraInduct n p.1 ((L.map Sigma.fst).sum) h p.2 (hcL L (L.map Sigma.fst).sum) x
      else 0

/-- 7.2 The Jacquet restriction of a function on `GL (Fin n) F` to `GL (Fin a) F × GL (Fin b) F`:
the average over the unipotent radical of the standard parabolic subgroup (the block-diagonal
matrix is that of 3.3b). -/
def jacquetRestrict (n a b : ℕ) (h : a + b = n) (χ : GL (Fin n) F → ℂ)
    (m : GL (Fin a) F × GL (Fin b) F) : ℂ :=
  ((unipotentRadical F n a).card : ℂ)⁻¹ *
    ∑ u ∈ unipotentRadical F n a, χ (toGL n (blockDiag n a b h m) * u)

/-- 7.3 Frobenius reciprocity for the Jacquet restriction against Harish–Chandra induction. -/
theorem jacquet_frobenius (n a b : ℕ) (h : a + b = n) (χ : GL (Fin n) F → ℂ)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    glPairing n χ (harishChandraInduct n a b h α β) =
      ((Nat.card (GL (Fin a) F) * Nat.card (GL (Fin b) F) : ℕ) : ℂ)⁻¹ *
        ∑ m : GL (Fin a) F × GL (Fin b) F,
          jacquetRestrict n a b h χ m * (starRingEnd ℂ) (α m.1 * β m.2) := by
  sorry

/-- 7.4 The Harish–Chandra induction of a list of characters is the character of a
representation. -/
theorem hcL_character (L : List (Σ d : ℕ, GL (Fin d) F → ℂ))
    (hL : ∀ p ∈ L, IsIrreducibleCharacter p.1 p.2) (n : ℕ) :
    ∃ V : FDRep ℂ (GL (Fin n) F), ∀ x, V.character x = hcL L n x := by
  sorry

/-- 7.5 The Mackey formula for the pairing of two cuspidally induced functions: it is zero unless
the two lists are the same multiset, and it is one when the first list has no repetitions and
the two lists are the same multiset. -/
theorem pairing_hcL (L L' : List (Σ d : ℕ, GL (Fin d) F → ℂ))
    (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2) (hL' : ∀ p ∈ L', IsCuspidalCharacter p.1 p.2)
    {n : ℕ} (hn : (L.map Sigma.fst).sum = n) (hn' : (L'.map Sigma.fst).sum = n) :
    ((L : Multiset (Σ d : ℕ, GL (Fin d) F → ℂ)) ≠ L' → glPairing n (hcL L n) (hcL L' n) = 0) ∧
      (L.Nodup → (L : Multiset (Σ d : ℕ, GL (Fin d) F → ℂ)) = L' →
        glPairing n (hcL L n) (hcL L' n) = 1) := by
  sorry

/-- 7.6 Every irreducible character of `GL (Fin n) F` has a cuspidal support: a list of cuspidal
characters of total degree `n` whose Harish–Chandra induction contains it. -/
theorem exists_cuspidal_support (n : ℕ) (χ : GL (Fin n) F → ℂ) (hχ : IsIrreducibleCharacter n χ) :
    ∃ L : List (Σ d : ℕ, GL (Fin d) F → ℂ),
      (∀ p ∈ L, IsCuspidalCharacter p.1 p.2) ∧ (L.map Sigma.fst).sum = n ∧
      glPairing n χ (hcL L n) ≠ 0 := by
  sorry

/-- 7.7a The upper unitriangular matrices: the unipotent radical of the standard Borel subgroup. -/
def upperUnitriangular (n : ℕ) : Finset (GL (Fin n) F) :=
  Finset.univ.filter fun u : GL (Fin n) F =>
    ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → (u : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0

/-- 7.7b The sum of the entries on the first superdiagonal of a matrix. -/
def superdiagonalSum {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin (n - 1), M (finCongr (by omega) (Fin.castAdd 1 i)) (finCongr (by omega) (Fin.succ i))

/-- 7.7c The Whittaker functional of a function on `GL (Fin n) F`, for an additive character `ψ` of
`F`: the sum of `ψ (superdiagonal sum) * f` over the upper unitriangular matrices. -/
def whittakerFunctional (ψ : AddChar F ℂ) {n : ℕ} (hn : 0 < n) (f : GL (Fin n) F → ℂ) : ℂ :=
  ∑ u ∈ upperUnitriangular n, ψ (superdiagonalSum hn (u : Matrix (Fin n) (Fin n) F)) * f u

/-- 7.7d Every cuspidally induced function has a *generic* irreducible constituent: one on which
the Whittaker functional does not vanish. -/
theorem exists_generic_constituent (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (L : List (Σ d : ℕ, GL (Fin d) F → ℂ))
    {n : ℕ} (hn : (L.map Sigma.fst).sum = n) (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2)
    (hn' : 0 < n) :
    ∃ ρ : GL (Fin n) F → ℂ, IsIrreducibleCharacter n ρ ∧ whittakerFunctional ψ hn' ρ ≠ 0 ∧
      glPairing n ρ (hcL L n) ≠ 0 := by
  sorry

/-- 7.8 There are at most `q ^ n - q ^ (n - 1)` generic irreducible characters: irreducible
characters on which the Whittaker functional does not vanish. -/
theorem card_generic_irreducibles_le (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    Nat.card {ρ : GL (Fin n) F → ℂ // IsIrreducibleCharacter n ρ ∧ whittakerFunctional ψ hn ρ ≠ 0} ≤
      (Nat.card F) ^ n - (Nat.card F) ^ (n - 1) := by
  sorry

/-- 7.9 Any set of multisets of cuspidal characters, all of total degree `n`, has at most
`q ^ n - q ^ (n - 1)` elements. -/
theorem card_cuspidal_multisets_le (n : ℕ) (hn : 0 < n)
    (S : Finset (Multiset (Σ d : ℕ, GL (Fin d) F → ℂ)))
    (hS : ∀ M ∈ S, (M.map Sigma.fst).sum = n ∧ ∀ p ∈ M, IsCuspidalCharacter p.1 p.2) :
    S.card ≤ (Nat.card F) ^ n - (Nat.card F) ^ (n - 1) := by
  sorry

/-- 7.10 **Green's theorem.** For every extension `K` of `F` of degree `n` there is a map `τ` from
the characters of `Kˣ` to the functions on `GL (Fin n) F` such that: (i) at a regular `θ` it is a
cuspidal character of degree `∏_{i = 1}^{n-1} (q ^ i - 1)`, with the value
`(-1) ^ (n - 1) ∑_{i < n} θ (z ^ q ^ i)` at every matrix with irreducible characteristic
polynomial and every root `z ∈ Kˣ` of it; (ii) two regular characters have the same image exactly
when they are conjugate under `θ ↦ θ ^ q ^ i`; (iii) every cuspidal character is the image of a
regular character. -/
theorem green_cuspidal_characters (n : ℕ) (hn : 0 < n) (K : Type) [Field K] [Algebra F K]
    (hK : Module.finrank F K = n) :
    ∃ τ : (Kˣ →* ℂˣ) → (GL (Fin n) F → ℂ),
      (∀ θ : Kˣ →* ℂˣ, IsRegular F n θ →
        IsCuspidalCharacter n (τ θ) ∧
          τ θ 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
          ∀ g : GL (Fin n) F,
            Irreducible (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) →
            ∀ z : Kˣ, aeval (z : K) (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) = 0 →
              τ θ g = (-1) ^ (n - 1) *
                ∑ i ∈ Finset.range n, ((θ (z ^ (Nat.card F ^ i)) : ℂˣ) : ℂ)) ∧
      (∀ θ θ' : Kˣ →* ℂˣ, IsRegular F n θ → IsRegular F n θ' →
        (τ θ = τ θ' ↔ ∃ i < n, θ' = θ ^ (Nat.card F ^ i))) ∧
      ∀ χ : GL (Fin n) F → ℂ, IsCuspidalCharacter n χ → ∃ θ : Kˣ →* ℂˣ, IsRegular F n θ ∧ χ = τ θ := by
  sorry

/-- 7.11 The number of cuspidal characters of `GL (Fin n) F` is the number of monic irreducible
polynomials of degree `n` over `F` with nonzero constant term: `(1/n) ∑_{d ∣ n} μ (d) q ^ (n / d)`
by 1.1 (for `n ≥ 2` every irreducible polynomial of degree `n` has nonzero constant term). -/
theorem card_cuspidalCharacters (n : ℕ) (hn : 0 < n) :
    Nat.card {χ : GL (Fin n) F → ℂ // IsCuspidalCharacter n χ} =
      Nat.card {P : F[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0} := by
  sorry

/-! ## Layer 8: uniqueness of the cuspidal support, and labels -/

/-- 8.1 The cuspidal support is unique up to reordering the list. -/
theorem cuspidal_support_unique (n : ℕ) (χ : GL (Fin n) F → ℂ) (hχ : IsIrreducibleCharacter n χ)
    (L L' : List (Σ d : ℕ, GL (Fin d) F → ℂ))
    (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2) (hL' : ∀ p ∈ L', IsCuspidalCharacter p.1 p.2)
    (hLn : (L.map Sigma.fst).sum = n) (hL'n : (L'.map Sigma.fst).sum = n)
    (hχL : glPairing n χ (hcL L n) ≠ 0) (hχL' : glPairing n χ (hcL L' n) ≠ 0) :
    (L : Multiset (Σ d : ℕ, GL (Fin d) F → ℂ)) = L' := by
  sorry

/-- 8.2 **Green's parametrization by prime labels.** There is a family `τ P` of cuspidal
characters indexed by the monic irreducible polynomials `P` of degree `n` with nonzero constant
term: distinct labels give distinct characters, every cuspidal character is one of them, and at a
matrix with characteristic polynomial `P` the value is `(-1) ^ (n - 1) ∑_{i < n} θ₀ (z ^ q ^ i)`
for every root `z` of `P`, for a Teichmüller character `θ₀`. -/
theorem green_prime_labels (n : ℕ) (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∃ τ : F[X] → (GL (Fin n) F → ℂ),
      (∀ P : F[X], P.Monic → Irreducible P → P.natDegree = n → P.coeff 0 ≠ 0 →
        IsCuspidalCharacter n (τ P) ∧
          τ P 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
          ∀ g : GL (Fin n) F, Matrix.charpoly (g : Matrix (Fin n) (Fin n) F) = P →
            ∀ z : AlgebraicClosure F, aeval z (P.map (algebraMap F (AlgebraicClosure F))) = 0 →
              τ P g = (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, θ (z ^ (Nat.card F ^ i))) ∧
      (∀ P Q : F[X], P.Monic → Irreducible P → P.natDegree = n → Q.Monic → Irreducible Q →
        Q.natDegree = n → τ P = τ Q → P = Q) ∧
      ∀ χ : GL (Fin n) F → ℂ, IsCuspidalCharacter n χ →
        ∃ P : F[X], P.Monic ∧ Irreducible P ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0 ∧ χ = τ P := by
  sorry

end TauCetiRoadmap.CharactersOfGLnOverFiniteFields
