module

public import Mathlib
public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Irreducible
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Cuspidal characters of general linear groups over finite fields: target signatures

**This file is not the roadmap.** The roadmap is `README.md`. This file states the roadmap's
headline theorems against the pinned Mathlib and Tau Ceti, each with `sorry`, together with the few
definitions they need; every definition has a real body (a few call a `sorry` theorem from this
file, the class-function property of the function they bundle). The README's remaining steps, API
lists and Checks are not restated, and `Suggested.lean` is read as suggested forms, never as an
exhaustive checklist.

Everything is stated for a finite field `F` with `q = Nat.card F` elements and the group
`GL (Fin n) F` of invertible `n × n` matrices. A character of `GL (Fin n) F` is a Tau Ceti class
function, an element of `TauCeti.ClassFunction ℂ (GL (Fin n) F)`, read as a function `g ↦ χ g`
through `χ.1`. An irreducible character is a class function whose underlying function lies in
`TauCeti.irreducibleCharacters`, a virtual character one lying in `TauCeti.virtualCharacters`, and
the pairing of class functions is `TauCeti.ClassFunction.characterPairing`; none of these is
restated here. `IsCuspidalCharacter n χ` says that `χ` is an irreducible character whose sums over
the unipotent radical of every standard parabolic subgroup vanish; such a character vanishes off
the elements whose characteristic polynomial is a power of an irreducible, and it is determined by
its values on the elements with irreducible characteristic polynomial.

The construction behind the headline is Green's. For a multiplicative map `θ` from the algebraic
closure of `F` to `ℂ` and an integer `k`, the `k`-th root-power-sum of a polynomial `P` is
`∑_{P(α) = 0} θ α ^ k`. From an additive function `s` on monic polynomials one forms `ψ` on the
endomorphisms of a finite-dimensional `F`-vector space `V` by Möbius inversion over the lattice of
invariant subspaces, `psi s V g = s (charpoly g) - ∑_{W ⫋ V} psi s W (g on W)`. Green's theorem
says: for an extension `K` of `F` of degree `n`, the characters `θ` of `Kˣ` whose Frobenius
conjugates `θ ∘ (· ^ q ^ i)`, `i < n`, are pairwise distinct are in bijection with the cuspidal
characters of `GL (Fin n) F`, by `θ ↦ (-1) ^ (n - 1) • ψ (rootPowerSum θ 1)`.
-/

noncomputable section

open Polynomial

open scoped Classical

namespace TauCetiRoadmap.CharactersOfGLnOverFiniteFields

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

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
Frobenius conjugates `θ ∘ (· ^ q ^ i)`, `i < n`, are pairwise distinct. The conjugate is spelled
`θ.comp (powMonoidHom (q ^ i))`, as in Tau Ceti's `GL₂` files; it is also the pointwise power
`θ ^ (q ^ i)`, since `θ (u ^ m) = θ u ^ m`. -/
def IsRegular (F : Type) [Field F] [Fintype F] (n : ℕ) {K : Type} [Field K] [Algebra F K]
    (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j : ℕ, i < n → j < n →
    θ.comp (powMonoidHom (Nat.card F ^ i)) = θ.comp (powMonoidHom (Nat.card F ^ j)) → i = j

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

/-- 1.4 *Orthogonality on roots of unity.* For an extension `K` of `F` of degree `n`, an
`F`-embedding `ι` of `K` into the algebraic closure and residues `k, l`, the sum of
`θ (ι u) ^ k * conj (θ (ι u) ^ l)` over `u ∈ Kˣ` is `q ^ n - 1` if `k ≡ l [MOD q ^ n - 1]` and `0`
otherwise. -/
theorem rootPowerSum_orthogonality (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k l : ℕ)
    {K : Type} [Field K] [Algebra F K] [Fintype K] (hK : Module.finrank F K = n)
    (ι : K →ₐ[F] AlgebraicClosure F) :
    ∑ u : Kˣ, (θ (ι u)) ^ k * (starRingEnd ℂ) ((θ (ι u)) ^ l) =
      if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
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

/-! ## Layer 3: class functions on `GL (Fin n) F`, the parabolic subgroups, and cuspidal characters -/

/-- 3.3a The matrix `M` read inside `GL (Fin n) F`; the junk value `1` occurs only when `M` is
not invertible. -/
def toGL (n : ℕ) (M : Matrix (Fin n) (Fin n) F) : GL (Fin n) F :=
  if h : IsUnit M then h.unit else 1

/-- 3.3 The standard parabolic subgroup with blocks `a`, `n - a`: the invertible matrices that are
block upper triangular for the block index taking the value `1` on the last `n - a` indices and
`0` on the first `a` (Mathlib's `Matrix.BlockTriangular`), i.e. the block upper triangular
matrices with block sizes `a`, `n - a`. -/
def parabolic (F : Type) [Field F] [Fintype F] (n a : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {x | (x : Matrix (Fin n) (Fin n) F).BlockTriangular
    fun i => if a ≤ (i : ℕ) then 1 else 0}
  one_mem' := by
    show ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular _
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular _
    rw [Units.val_mul]
    exact hx.mul hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular _
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

/-- Membership in the standard parabolic subgroup, in matrix entries: the entries below the
diagonal blocks vanish. -/
theorem mem_parabolic_iff (n a : ℕ) {x : GL (Fin n) F} :
    x ∈ parabolic F n a ↔ ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) →
      (x : Matrix (Fin n) (Fin n) F) i j = 0 := by
  constructor
  · intro h i j hj hia
    have h' : (x : Matrix (Fin n) (Fin n) F).BlockTriangular
        (fun i => if a ≤ (i : ℕ) then 1 else 0) := h
    refine h' ?_
    show (if a ≤ (j : ℕ) then 1 else 0) < (if a ≤ (i : ℕ) then 1 else 0)
    rw [ite_eq_right (not_le.mpr hj), ite_eq_left hia]
    exact Nat.zero_lt_one
  · intro h
    show (x : Matrix (Fin n) (Fin n) F).BlockTriangular (fun i => if a ≤ (i : ℕ) then 1 else 0)
    intro i j hb
    dsimp only at hb
    by_cases hj : a ≤ (j : ℕ)
    · rw [ite_eq_left hj] at hb
      split at hb <;> omega
    · rw [ite_eq_right hj] at hb
      split at hb
      · exact h i j (lt_of_not_ge hj) ‹a ≤ (i : ℕ)›
      · omega

/-- 3.3 The unipotent radical of the standard parabolic subgroup with blocks `a`, `n - a`: the
invertible matrices that agree with the identity in their first `a` columns. -/
def unipotentRadical (F : Type) [Field F] [Fintype F] (n a : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {u | ∀ i j : Fin n, (j : ℕ) < a →
    (u : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0}
  one_mem' := by
    intro i j _
    rw [Units.val_one]
    exact Matrix.one_apply
  mul_mem' := by
    intro u v hu hv i j hj
    simp only [Units.val_mul, Matrix.mul_apply, hv _ j hj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hu i j hj
  inv_mem' := by
    intro u hu i j hj
    have h := congrArg (fun g : GL (Fin n) F => ((g : Matrix (Fin n) (Fin n) F)) i j)
      (inv_mul_cancel u)
    simp only [Units.val_mul, Units.val_one, Matrix.one_apply, Matrix.mul_apply, hu _ j hj, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h

/-- 3.3 The unipotent radical `Uₐ` is contained in the parabolic subgroup `Pₐ`. -/
theorem unipotentRadical_le_parabolic (n a : ℕ) : unipotentRadical F n a ≤ parabolic F n a := by
  intro u hu
  have hu' : ∀ i j : Fin n, (j : ℕ) < a →
      ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0 := hu
  rw [mem_parabolic_iff]
  intro i j hj hia
  rw [hu' i j hj]
  have hne : ¬ (i = j) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_eq_val] at this
    omega
  split
  · exact absurd ‹i = j› hne
  · rfl

/-- 3.3b The block-diagonal matrix with diagonal blocks `m.1` and `m.2`, for block sizes `a`, `b`
with `a + b = n`; it is the matrix of an element of the Levi subgroup `Lₐ`. -/
def blockDiag (n a b : ℕ) (h : a + b = n) (m : GL (Fin a) F × GL (Fin b) F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < a then
      if hj : (j : ℕ) < a then (m.1 : Matrix (Fin a) (Fin a) F) ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else
      if hj : a ≤ (j : ℕ) then
        (m.2 : Matrix (Fin b) (Fin b) F) ⟨i - a, by omega⟩ ⟨j - a, by omega⟩
      else 0

/-- 3.4 A cuspidal character of `GL (Fin n) F`: an irreducible character (its underlying function
lies in `TauCeti.irreducibleCharacters`) whose sum over the unipotent radical `Uₐ` of every
standard parabolic subgroup is zero. -/
def IsCuspidalCharacter (n : ℕ) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F)) : Prop :=
  (χ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F) ∧
    ∀ a : ℕ, 0 < a → a < n → ∑ u : unipotentRadical F n a, χ.1 u = 0

/-- 3.5 For an irreducible character, the sums over the unipotent radicals vanish as soon as the
sums over the cosets of every unipotent radical do: the definition of cuspidal is equivalent to
the vanishing of every constant term. -/
theorem cuspidal_iff_constant_terms (n : ℕ) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F)) :
    IsCuspidalCharacter n χ ↔ ((χ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F)) ∧
      ∀ (a b : ℕ) (h : a + b = n), 0 < a → a < n →
        ∀ m : GL (Fin a) F × GL (Fin b) F,
          ∑ u : unipotentRadical F n a, χ.1 (toGL n (blockDiag n a b h m) * u) = 0 := by
  sorry

/-- 3.6 A cuspidal character vanishes at every invertible matrix whose characteristic polynomial
has at least two distinct monic irreducible factors (is not a power of an irreducible). -/
theorem cuspidal_vanish_off_primary (n : ℕ) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F))
    (hχ : IsCuspidalCharacter n χ)
    (x : GL (Fin n) F) (hx : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = f ^ m) : χ.1 x = 0 := by
  sorry

/-- 3.7 Two cuspidal characters that agree at the invertible matrices with irreducible
characteristic polynomial are equal. -/
theorem cuspidal_eq_of_eq_on_elliptic (n : ℕ) (χ χ' : TauCeti.ClassFunction ℂ (GL (Fin n) F))
    (hχ : IsCuspidalCharacter n χ) (hχ' : IsCuspidalCharacter n χ')
    (h : ∀ x : GL (Fin n) F, Irreducible (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)) →
      χ.1 x = χ'.1 x) : χ = χ' := by
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

/-- 4.3 On the group `GL (Fin n) F`, `g ↦ psi s (Fin n → F) (mulVecLin g)` is a class function. -/
theorem psi_classFunction (s : F[X] → ℂ) (n : ℕ) :
    (fun x : GL (Fin n) F => psi s (Fin n → F) (Matrix.mulVecLin x)) ∈
      TauCeti.ClassFunction ℂ (GL (Fin n) F) := by
  sorry

/-- 4.3 The class function of `psi s` on `GL (Fin n) F`. -/
def psiClassFunction (s : F[X] → ℂ) (n : ℕ) : TauCeti.ClassFunction ℂ (GL (Fin n) F) :=
  ⟨fun x => psi s (Fin n → F) (Matrix.mulVecLin x), psi_classFunction s n⟩

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

/-- 5.1 The class function `g ↦ rootPowerSum θ k (charpoly g)` of `GL (Fin n) F`: a class function
because the characteristic polynomial is constant on conjugacy classes. -/
def rootPowerSumClassFunction (θ : AlgebraicClosure F →* ℂ) (n k : ℕ) :
    TauCeti.ClassFunction ℂ (GL (Fin n) F) :=
  ⟨fun x => rootPowerSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F)),
    TauCeti.ClassFunction.mem_iff.2 fun g h => by
      apply congrArg (rootPowerSum θ k)
      simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]⟩

/-- 5.1 For a Teichmüller character `θ`, the class function `rootPowerSum θ k` of the
characteristic polynomial on `GL (Fin n) F` is a virtual character. -/
theorem rootPowerSum_virtualCharacter (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    (rootPowerSumClassFunction θ n k : GL (Fin n) F → ℂ) ∈ TauCeti.virtualCharacters ℂ (GL (Fin n) F) := by
  sorry

/-- 5.2 The pairing formula. The pairing of `psi` of the `k`-th root-power-sum with the `l`-th
root-power-sum of the characteristic polynomial is the number of indices `i < n` with
`k * q ^ i ≡ l [MOD q ^ n - 1]` (the pairing is normalized by `|GL (Fin n) F|`; with the plain sum
over the group it is `|GL (Fin n) F|` times that number). -/
theorem pairing_psi_rootPowerSum (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k l : ℕ) :
    TauCeti.ClassFunction.characterPairing (psiClassFunction (rootPowerSum θ k) n)
      (rootPowerSumClassFunction θ n l) =
        ((Finset.range n).filter fun i => k * (Nat.card F ^ i) ≡ l [MOD Nat.card F ^ n - 1]).card := by
  sorry

/-- 5.3 The Möbius transform of a root-power-sum, restricted to `GL (Fin n) F`, is a virtual
character. -/
theorem psi_rootPowerSum_virtualCharacter (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n k : ℕ) :
    (psiClassFunction (rootPowerSum θ k) n : GL (Fin n) F → ℂ) ∈
      TauCeti.virtualCharacters ℂ (GL (Fin n) F) := by
  sorry

/-! ## Layer 6: cuspidal characters from regular characters -/

/-- The class function `χₖ = (-1) ^ (n - 1) • psi (rootPowerSum θ k)` of `GL (Fin n) F`, the
function that, for a Teichmüller character `θ` and a regular index `k`, is a cuspidal character
(6.2). -/
def chiK (θ : AlgebraicClosure F →* ℂ) (n k : ℕ) : TauCeti.ClassFunction ℂ (GL (Fin n) F) :=
  (-1 : ℂ) ^ (n - 1) • psiClassFunction (rootPowerSum θ k) n

/-- 6.1 The construction behind 6.3: for a Teichmüller character `θ`, the class function
`chiK θ n k` has pairing `1` with itself as soon as `k` is regular in the sense that
`k * q ^ i ≢ k [MOD q ^ n - 1]` for `0 < i < n`, and it is a cuspidal character then. -/
theorem self_pairing_psi_rootPowerSum (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : ∀ i : ℕ, 0 < i → i < n → ¬ k * (Nat.card F ^ i) ≡ k [MOD Nat.card F ^ n - 1]) :
    TauCeti.ClassFunction.characterPairing (chiK θ n k) (chiK θ n k) = 1 :=
  sorry

/-- 6.2 Under the hypothesis of 6.1 the class function `chiK θ n k` is a cuspidal character. -/
theorem cuspidal_of_self_pairing (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n)
    (k : ℕ) (hk : ∀ i : ℕ, 0 < i → i < n → ¬ k * (Nat.card F ^ i) ≡ k [MOD Nat.card F ^ n - 1]) :
    IsCuspidalCharacter n (chiK θ n k) :=
  sorry

/-- 6.3 To a regular character `θ` of `Kˣ`, with `K` of degree `n` over `F`, corresponds a
cuspidal character of `GL (Fin n) F` of degree `∏_{i = 1}^{n-1} (q ^ i - 1)`, whose value at an
invertible matrix `g` with irreducible characteristic polynomial is
`(-1) ^ (n - 1) ∑_{i < n} θ (z ^ q ^ i)` for every root `z ∈ Kˣ` of that polynomial. -/
theorem cuspidalCharacter_of_regular (n : ℕ) (hn : 0 < n) (K : Type) [Field K] [Algebra F K]
    (hK : Module.finrank F K = n) (θ : Kˣ →* ℂˣ) (hθ : IsRegular F n θ) :
    ∃ χ : TauCeti.ClassFunction ℂ (GL (Fin n) F), IsCuspidalCharacter n χ ∧
      χ.1 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
      ∀ g : GL (Fin n) F, Irreducible (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) →
        ∀ z : Kˣ, aeval (z : K) (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) = 0 →
          χ.1 g = (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, ((θ (z ^ (Nat.card F ^ i)) : ℂˣ) : ℂ) := by
  sorry

/-- 6.5 *Check, the case `n = 2`.* For a quadratic extension `K` of `F` and a character `θ` of
`Kˣ` that is not fixed by the Frobenius twist (`θ.comp (powMonoidHom (Fintype.card F)) ≠ θ`, i.e.
`θ ^ q ≠ θ`: it is regular in the sense of 1.3), the character of Tau Ceti's `TauCeti.GL2Cuspidal`
is a cuspidal character in the sense of this roadmap, and it is the one that 6.3 attaches to `θ`:
its value at the elliptic matrix `TauCeti.GL2NonSplitTorusHom F K u`, for `u ∈ Kˣ` outside `Fˣ`,
is `- ∑_{i < 2} θ (u ^ q ^ i)`. -/
theorem gl2Cuspidal_character (K : Type) [Field K] [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (θ : Kˣ →* ℂˣ) (hθ : θ.comp (powMonoidHom (Fintype.card F)) ≠ θ) :
    IsCuspidalCharacter 2 (TauCeti.ClassFunction.ofFDRep (TauCeti.GL2Cuspidal θ hθ)) ∧
      ∀ u : Kˣ, (u : K) ∉ Set.range (algebraMap F K) →
        (TauCeti.GL2Cuspidal θ hθ).character (TauCeti.GL2NonSplitTorusHom F K u) =
          -∑ i ∈ Finset.range 2, ((θ (u ^ (Fintype.card F ^ i)) : ℂˣ) : ℂ) := by
  sorry

/-! ## Layer 7: Harish–Chandra induction, cuspidal support, generic constituents, and Green's theorem -/

/-- 7.1a The Levi projection: the two diagonal blocks of a matrix, for block sizes `a`, `b` with
`a + b = n`, each read in its general linear group through `toGL` (the junk value `1` occurs only
for a block that is not invertible). -/
def levi (n a b : ℕ) (h : a + b = n) (x : Matrix (Fin n) (Fin n) F) : GL (Fin a) F × GL (Fin b) F :=
  (toGL a (Matrix.of fun i j => x (finCongr h (Fin.castAdd b i)) (finCongr h (Fin.castAdd b j))),
   toGL b (Matrix.of fun i j => x (finCongr h (Fin.natAdd a i)) (finCongr h (Fin.natAdd a j))))

/-- 7.1b Inflation to the parabolic subgroup `Pₐ` of a pair of class functions on its two Levi
blocks is a class function on `Pₐ`: conjugating within `Pₐ` conjugates each diagonal block. -/
theorem leviInflate_mem_classFunction (n a b : ℕ) (h : a + b = n)
    (α : TauCeti.ClassFunction ℂ (GL (Fin a) F)) (β : TauCeti.ClassFunction ℂ (GL (Fin b) F)) :
    (fun p : parabolic F n a =>
      α.1 (levi n a b h ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).1 *
        β.1 (levi n a b h ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).2) ∈
      TauCeti.ClassFunction ℂ (parabolic F n a) := by
  sorry

/-- 7.1b Inflation to the parabolic subgroup `Pₐ` of a pair of class functions on its two Levi
blocks: the class function `p ↦ α (Aₚ) * β (Bₚ)`, where `Aₚ`, `Bₚ` are the diagonal blocks of `p`
(the junk value of `levi` occurs only outside `Pₐ`). -/
def leviInflate (n a b : ℕ) (h : a + b = n) (α : TauCeti.ClassFunction ℂ (GL (Fin a) F))
    (β : TauCeti.ClassFunction ℂ (GL (Fin b) F)) : TauCeti.ClassFunction ℂ (parabolic F n a) :=
  ⟨fun p =>
    α.1 (levi n a b h ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).1 *
      β.1 (levi n a b h ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).2,
    leviInflate_mem_classFunction n a b h α β⟩

/-- 7.1b Harish–Chandra induction of a pair of class functions from `GL (Fin a) F × GL (Fin b) F`:
the induced class function (Tau Ceti's `Subgroup.indClassFunction`) from the standard parabolic
subgroup `Pₐ` of the inflation to `Pₐ` of `α` and `β`. By `Subgroup.indClassFun_eq_natCard_inv_mul_sum`
it is the class function `|Pₐ|⁻¹ ∑_{y, y⁻¹ x y ∈ Pₐ} α (A) * β (B)` of the README, `A`, `B` being the
diagonal blocks of `y⁻¹ x y`. -/
def harishChandraInduct (n a b : ℕ) (h : a + b = n) (α : TauCeti.ClassFunction ℂ (GL (Fin a) F))
    (β : TauCeti.ClassFunction ℂ (GL (Fin b) F)) : TauCeti.ClassFunction ℂ (GL (Fin n) F) :=
  Subgroup.indClassFunction (parabolic F n a) (leviInflate n a b h α β)

/-- 7.1c Harish–Chandra induction along a list of degree-tagged class functions: the head is
induced against the induction of the tail. The result is `0` unless the degrees sum to `n`. -/
def hcL : (L : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F))) → (n : ℕ) →
    TauCeti.ClassFunction ℂ (GL (Fin n) F)
  | [], 0 => ⟨fun _ => 1, TauCeti.ClassFunction.mem_iff.2 fun _ _ => rfl⟩
  | [], _ => 0
  | p :: L, n =>
      if h : p.1 + (L.map Sigma.fst).sum = n then
        harishChandraInduct n p.1 ((L.map Sigma.fst).sum) h p.2 (hcL L (L.map Sigma.fst).sum)
      else 0

/-- 7.2 The Jacquet restriction is a class function on `GL (Fin a) F × GL (Fin b) F`: the
block-diagonal matrix is a homomorphism, and the unipotent radical is normalized by the Levi
subgroup. -/
theorem jacquetRestrict_mem_classFunction (n a b : ℕ) (h : a + b = n)
    (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F)) :
    (fun m : GL (Fin a) F × GL (Fin b) F => (Nat.card (unipotentRadical F n a) : ℂ)⁻¹ *
      ∑ u : unipotentRadical F n a, χ.1 (toGL n (blockDiag n a b h m) * u)) ∈
      TauCeti.ClassFunction ℂ (GL (Fin a) F × GL (Fin b) F) := by
  sorry

/-- 7.2 The Jacquet restriction of a class function of `GL (Fin n) F` to the Levi subgroup
`GL (Fin a) F × GL (Fin b) F`: the class function
`m ↦ |Uₐ|⁻¹ ∑_{u ∈ Uₐ} χ (m * u)`, the average of `χ` over the coset of the unipotent radical
through the image in `GL (Fin n) F` of the element `m` of the Levi subgroup. -/
def jacquetRestrict (n a b : ℕ) (h : a + b = n) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F)) :
    TauCeti.ClassFunction ℂ (GL (Fin a) F × GL (Fin b) F) :=
  ⟨fun m => (Nat.card (unipotentRadical F n a) : ℂ)⁻¹ *
      ∑ u : unipotentRadical F n a, χ.1 (toGL n (blockDiag n a b h m) * u),
    jacquetRestrict_mem_classFunction n a b h χ⟩

/-- 7.3 Frobenius reciprocity for the Jacquet restriction against Harish–Chandra induction. -/
theorem jacquet_frobenius (n a b : ℕ) (h : a + b = n) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F))
    (α : TauCeti.ClassFunction ℂ (GL (Fin a) F)) (β : TauCeti.ClassFunction ℂ (GL (Fin b) F)) :
    TauCeti.ClassFunction.characterPairing χ (harishChandraInduct n a b h α β) =
      ((Nat.card (GL (Fin a) F) * Nat.card (GL (Fin b) F) : ℕ) : ℂ)⁻¹ *
        ∑ m : GL (Fin a) F × GL (Fin b) F,
          (jacquetRestrict n a b h χ).1 m * (α.1 m.1 * β.1 m.2)⁻¹ := by
  sorry

/-- 7.4 The Harish–Chandra induction of a list of irreducible characters is the character of a
representation. -/
theorem hcL_character (L : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)))
    (hL : ∀ p ∈ L, (p.2 : GL (Fin p.1) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin p.1) F))
    (n : ℕ) :
    ∃ V : FDRep ℂ (GL (Fin n) F), (hcL L n : GL (Fin n) F → ℂ) = V.character := by
  sorry

/-- 7.5 The Mackey formula for the pairing of two cuspidally induced class functions: it is zero
unless the two lists are the same multiset, and it is one when the first list has no repetitions
and the two lists are the same multiset. -/
theorem pairing_hcL (L L' : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)))
    (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2) (hL' : ∀ p ∈ L', IsCuspidalCharacter p.1 p.2)
    {n : ℕ} (hn : (L.map Sigma.fst).sum = n) (hn' : (L'.map Sigma.fst).sum = n) :
    ((L : Multiset (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F))) ≠ L' →
        TauCeti.ClassFunction.characterPairing (hcL L n) (hcL L' n) = 0) ∧
      (L.Nodup → (L : Multiset (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F))) = L' →
        TauCeti.ClassFunction.characterPairing (hcL L n) (hcL L' n) = 1) := by
  sorry

/-- 7.6 Every irreducible character of `GL (Fin n) F` has a cuspidal support: a list of cuspidal
characters of total degree `n` whose Harish–Chandra induction contains it. -/
theorem exists_cuspidal_support (n : ℕ) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F))
    (hχ : (χ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F)) :
    ∃ L : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)),
      (∀ p ∈ L, IsCuspidalCharacter p.1 p.2) ∧ (L.map Sigma.fst).sum = n ∧
      TauCeti.ClassFunction.characterPairing χ (hcL L n) ≠ 0 := by
  sorry

/-- 7.7b The sum of the entries on the first superdiagonal of a matrix. -/
def superdiagonalSum {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin (n - 1), M (finCongr (by omega) (Fin.castAdd 1 i)) (finCongr (by omega) (Fin.succ i))

/-- 7.7c The Whittaker functional of a class function of `GL (Fin n) F`, for an additive character
`ψ` of `F`: the sum of `ψ (superdiagonal sum) * f` over the upper unitriangular matrices, Tau
Ceti's subgroup `TauCeti.upperUnitriangularGroup`. -/
def whittakerFunctional (ψ : AddChar F ℂ) {n : ℕ} (hn : 0 < n)
    (f : TauCeti.ClassFunction ℂ (GL (Fin n) F)) : ℂ :=
  ∑ u : TauCeti.upperUnitriangularGroup (Fin n) F,
    ψ (superdiagonalSum hn ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * f.1 u

/-- 7.7d Every cuspidally induced class function has a *generic* irreducible constituent: one on
which the Whittaker functional does not vanish. -/
theorem exists_generic_constituent (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (L : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)))
    {n : ℕ} (hn : (L.map Sigma.fst).sum = n) (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2)
    (hn' : 0 < n) :
    ∃ ρ : TauCeti.ClassFunction ℂ (GL (Fin n) F),
      (ρ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F) ∧
      whittakerFunctional ψ hn' ρ ≠ 0 ∧
      TauCeti.ClassFunction.characterPairing ρ (hcL L n) ≠ 0 := by
  sorry

/-- 7.8 There are at most `q ^ n - q ^ (n - 1)` generic irreducible characters: irreducible
characters on which the Whittaker functional does not vanish. -/
theorem card_generic_irreducibles_le (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    Nat.card {ρ : TauCeti.ClassFunction ℂ (GL (Fin n) F) //
      (ρ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F) ∧
        whittakerFunctional ψ hn ρ ≠ 0} ≤
      Nat.card F ^ n - Nat.card F ^ (n - 1) := by
  sorry

/-- 7.9 Any set of multisets of cuspidal class functions, all of total degree `n`, has at most
`q ^ n - q ^ (n - 1)` elements. -/
theorem card_cuspidal_multisets_le (n : ℕ) (hn : 0 < n)
    (S : Finset (Multiset (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F))))
    (hS : ∀ M ∈ S, (M.map Sigma.fst).sum = n ∧ ∀ p ∈ M, IsCuspidalCharacter p.1 p.2) :
    S.card ≤ Nat.card F ^ n - Nat.card F ^ (n - 1) := by
  sorry

/-- 7.10 **Green's theorem.** For every extension `K` of `F` of degree `n` there is a map `τ` from
the characters of `Kˣ` to the class functions of `GL (Fin n) F` such that: (i) at a regular `θ`
it is a cuspidal character of degree `∏_{i = 1}^{n-1} (q ^ i - 1)`, with the value
`(-1) ^ (n - 1) ∑_{i < n} θ (z ^ q ^ i)` at every matrix with irreducible characteristic
polynomial and every root `z ∈ Kˣ` of it; (ii) two regular characters have the same image exactly
when they are conjugate under `θ ↦ θ ∘ (· ^ q ^ i)`; (iii) every cuspidal character is the image
of a regular character. -/
theorem green_cuspidal_characters (n : ℕ) (hn : 0 < n) (K : Type) [Field K] [Algebra F K]
    (hK : Module.finrank F K = n) :
    ∃ τ : (Kˣ →* ℂˣ) → TauCeti.ClassFunction ℂ (GL (Fin n) F),
      (∀ θ : Kˣ →* ℂˣ, IsRegular F n θ →
        IsCuspidalCharacter n (τ θ) ∧
          (τ θ).1 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
          ∀ g : GL (Fin n) F,
            Irreducible (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) →
            ∀ z : Kˣ, aeval (z : K) (Matrix.charpoly (g : Matrix (Fin n) (Fin n) F)) = 0 →
              (τ θ).1 g = (-1) ^ (n - 1) *
                ∑ i ∈ Finset.range n, ((θ (z ^ (Nat.card F ^ i)) : ℂˣ) : ℂ)) ∧
      (∀ θ θ' : Kˣ →* ℂˣ, IsRegular F n θ → IsRegular F n θ' →
        (τ θ = τ θ' ↔ ∃ i < n, θ' = θ.comp (powMonoidHom (Nat.card F ^ i)))) ∧
      ∀ χ : TauCeti.ClassFunction ℂ (GL (Fin n) F), IsCuspidalCharacter n χ →
        ∃ θ : Kˣ →* ℂˣ, IsRegular F n θ ∧ χ = τ θ := by
  sorry

/-- 7.11 The number of cuspidal characters of `GL (Fin n) F` is the number of monic irreducible
polynomials of degree `n` over `F` with nonzero constant term: `(1/n) ∑_{d ∣ n} μ (d) q ^ (n / d)`
by 1.1 (for `n ≥ 2` every irreducible polynomial of degree `n` has nonzero constant term). -/
theorem card_cuspidalCharacters (n : ℕ) (hn : 0 < n) :
    Nat.card {χ : TauCeti.ClassFunction ℂ (GL (Fin n) F) // IsCuspidalCharacter n χ} =
      Nat.card {P : F[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0} := by
  sorry

/-! ## Layer 8: uniqueness of the cuspidal support, and labels -/

/-- 8.1 The cuspidal support is unique up to reordering the list. -/
theorem cuspidal_support_unique (n : ℕ) (χ : TauCeti.ClassFunction ℂ (GL (Fin n) F))
    (hχ : (χ : GL (Fin n) F → ℂ) ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F))
    (L L' : List (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)))
    (hL : ∀ p ∈ L, IsCuspidalCharacter p.1 p.2) (hL' : ∀ p ∈ L', IsCuspidalCharacter p.1 p.2)
    (hLn : (L.map Sigma.fst).sum = n) (hL'n : (L'.map Sigma.fst).sum = n)
    (hχL : TauCeti.ClassFunction.characterPairing χ (hcL L n) ≠ 0)
    (hχL' : TauCeti.ClassFunction.characterPairing χ (hcL L' n) ≠ 0) :
    (L : Multiset (Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F))) = L' := by
  sorry

/-- 8.2 **Green's parametrization by prime labels.** There is a family `τ P` of cuspidal
characters indexed by the monic irreducible polynomials `P` of degree `n` with nonzero constant
term: distinct labels give distinct characters, every cuspidal character is one of them, and at a
matrix with characteristic polynomial `P` the value is `(-1) ^ (n - 1) ∑_{i < n} θ₀ (z ^ q ^ i)`
for every root `z` of `P`, for a Teichmüller character `θ₀`. -/
theorem green_prime_labels (n : ℕ) (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) :
    ∃ τ : F[X] → TauCeti.ClassFunction ℂ (GL (Fin n) F),
      (∀ P : F[X], P.Monic → Irreducible P → P.natDegree = n → P.coeff 0 ≠ 0 →
        IsCuspidalCharacter n (τ P) ∧
          (τ P).1 1 = ∏ i ∈ Finset.Ico 1 n, ((Nat.card F : ℂ) ^ i - 1) ∧
          ∀ g : GL (Fin n) F, Matrix.charpoly (g : Matrix (Fin n) (Fin n) F) = P →
            ∀ z : AlgebraicClosure F, aeval z (P.map (algebraMap F (AlgebraicClosure F))) = 0 →
              (τ P).1 g = (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, θ (z ^ (Nat.card F ^ i))) ∧
      (∀ P Q : F[X], P.Monic → Irreducible P → P.natDegree = n → Q.Monic → Irreducible Q →
        Q.natDegree = n → τ P = τ Q → P = Q) ∧
      ∀ χ : TauCeti.ClassFunction ℂ (GL (Fin n) F), IsCuspidalCharacter n χ →
        ∃ P : F[X], P.Monic ∧ Irreducible P ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0 ∧ χ = τ P := by
  sorry

end TauCetiRoadmap.CharactersOfGLnOverFiniteFields
