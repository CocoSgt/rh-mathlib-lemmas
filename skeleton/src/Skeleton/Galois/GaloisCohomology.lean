/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, shared base: continuous group cohomology `H¹` of a
topological group with coefficients in a discrete module, and the "Galois cohomology
data" `LData` whose `Sha`-length `shaLen` bounds the window hypothesis `VVle`
(see `Skeleton/Window/VWin.lean`).

Source (all Mathlib-only, statements and proofs):
  * `ReciprocityTheory.Gal.Z1`, `d0`, `B1`, `mem_coboundaries1`, `H1`, `restrictCocycles1`, `resH1`:
      source/src/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean:36-154
  * `ReciprocityTheory.Gal.Sha1`:
      source/src/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean:168
  * `ReciprocityTheory.Gal.locFam`, `continuous_locFam`:
      source/src/ReciprocityTheory/Hypotheses/GalCoh.lean:132-138
  * `Formalism.GaloisCohomology.ZlSub`, `QZ`, `QZ.mk`, `scalRep`, `scalRep_apply`, `Above`,
    `LData`, `qzTw`, `zlTw`, `Sha`, `shaLen`:
      source/src/Formalism/GaloisCohomology/Statement.lean:13-78
-/
import Skeleton.Galois.Places

noncomputable section

open NumberField IsDedekindDomain Representation

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section Cochain

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)

/-- Continuous 1-cocycles. -/
def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩

/-- The coboundary map. -/
def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id

/-- Continuous 1-coboundaries. -/
def B1 : Submodule R (G → M) := LinearMap.range (d0 rho)

omit [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] in
theorem mem_coboundaries1 (f : G → M) : f ∈ B1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, funext fun g => (hm g).symm⟩

/-- Continuous first cohomology. -/
abbrev H1 := Z1 rho ⧸ (B1 rho).comap (Z1 rho).subtype

section Restriction

variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))

omit [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] in
/-- Restriction of cocycles along the family `phi`. -/
def restrictCocycles1 (i : I) : Z1 rho →ₗ[R] Z1 (rho.comp (phi i)) where
  toFun f := ⟨f.1 ∘ phi i, f.2.1.comp (hphi i), fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction on `H¹` along `phi i`. -/
def resH1 (i : I) : H1 rho →ₗ[R] H1 (rho.comp (phi i)) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi i) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hf
    exact (mem_coboundaries1 _ _).2 ⟨m, fun h => hm (phi i h)⟩

/-- The "Selmer"/Sha subgroup: classes trivial at every place `i`. -/
def Sha1 : Submodule R (H1 rho) :=
  ⨅ i, LinearMap.ker (resH1 rho phi hphi i)

end Restriction

end Cochain

section Global

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

/-- The family of local Galois groups at the places of `S`, mapping to `GS Ω S`. -/
def locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) :
    ∀ v : S, Dec (F := F) (Av v) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  fun v => locHom _ (Av v)

omit [NumberField F] [IsAlgClosure F Ω] in
theorem continuous_locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) (v : S) : Continuous (locFam S Av v) :=
  continuous_locHom _ _

end Global

end ReciprocityTheory.Gal

namespace Formalism.GaloisCohomology

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

section Coeff

variable (l : ℕ) [Fact l.Prime]

/-- `ℤ_[l]` seen as a submodule of `ℚ_[l]`. -/
abbrev ZlSub : Submodule ℤ_[l] ℚ_[l] := LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l])

/-- `ℚ_[l] / ℤ_[l]` with the discrete topology. -/
def QZ : Type := ℚ_[l] ⧸ ZlSub l

instance : AddCommGroup (QZ l) := inferInstanceAs (AddCommGroup (ℚ_[l] ⧸ ZlSub l))
instance : Module ℤ_[l] (QZ l) := inferInstanceAs (Module ℤ_[l] (ℚ_[l] ⧸ ZlSub l))
instance : TopologicalSpace (QZ l) := ⊥
instance : DiscreteTopology (QZ l) := ⟨rfl⟩
instance : IsTopologicalAddGroup (QZ l) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- In the source this instance is found through `ReciprocityTheory.Gal.continuousConstSMul_quotient`
(ContinuousConstSMulQuotient.lean:189, a quotient-module instance); for a discrete module it is
immediate, and stating it directly avoids the quotient topology. -/
instance continuousConstSMul_QZ : ContinuousConstSMul ℤ_[l] (QZ l) :=
  ⟨fun c => (continuous_of_discreteTopology : Continuous (fun x : QZ l => c • x))⟩

/-- The class of `x : ℚ_[l]` in `QZ l`. -/
def QZ.mk (x : ℚ_[l]) : QZ l := Submodule.Quotient.mk (p := ZlSub l) x

end Coeff

/-- Scalar multiplication by a character, as a representation. -/
def scalRep {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*) [AddCommGroup M]
    [Module R M] (ψ : Γ →* Rˣ) : Representation R Γ M where
  toFun g := ((ψ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, mul_smul, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.mul_apply, map_smul]
    first | rfl | exact smul_comm _ _ _

@[simp] theorem scalRep_apply {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] (M : Type*)
    [AddCommGroup M] [Module R M] (ψ : Γ →* Rˣ) (g : Γ) (m : M) :
    scalRep M ψ g m = ((ψ g : Rˣ) : R) • m := rfl

section Field

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]

variable (F) in
/-- The finite places of `F` above `l`. -/
def Above : Set (HeightOneSpectrum (𝓞 F)) := {v | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}

variable (F Ω) in

/-- Galois-cohomology data at `l`: the set `S` of places above `l`, a place `A v` of `Ω` over
each `v ∈ S`, and a character `chi` of `GS Ω S` lifting the cyclotomic character.
Original: `Formalism/GaloisCohomology/Statement.lean:54` (`variable (F Ω) in`). -/
structure LData where

  S : Finset (HeightOneSpectrum (𝓞 F))
  hS : (S : Set (HeightOneSpectrum (𝓞 F))) = Above F l

  A : S → ValuationSubring Ω
  hA : ∀ v, IsPlaceOver (A v) v.1

  chi : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* ℤ_[l]ˣ
  hchi : chi.comp (toGS Ω _) = cycZ F Ω l

variable {l}

/-- Twist of the trivial `QZ l`-representation by `chi ^ (-e)`. -/
def qzTw (D : LData F Ω l) (e : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (QZ l) :=
  scalRep (QZ l) (D.chi ^ (-e))

/-- Twist of the trivial `ℤ_[l]`-representation by `chi ^ n`. -/
def zlTw (D : LData F Ω l) (n : ℤ) :
    Representation ℤ_[l] (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) ℤ_[l] :=
  scalRep ℤ_[l] (D.chi ^ n)

/-- The Sha subgroup (classes vanishing at every place of `S`) of `H¹(qzTw D e)`. -/
def Sha (D : LData F Ω l) (e : ℤ) : Submodule ℤ_[l] (H1 (qzTw D e)) :=
  Sha1 (qzTw D e) (locFam D.S D.A) (continuous_locFam D.S D.A)

/-- Its length.  `VVle` (in `Skeleton/Window/VWin.lean`) bounds these lengths. -/
def shaLen (D : LData F Ω l) (e : ℤ) : ℕ∞ := Module.length ℤ_[l] (Sha D e)

end Field

end Formalism.GaloisCohomology

end
