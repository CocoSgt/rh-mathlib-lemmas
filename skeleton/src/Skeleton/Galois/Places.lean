/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, shared base: places of a number field inside an algebraic
closure, the absolute Galois group `G F Ω`, decomposition / inertia, the subgroup
`NS` ("no inertia outside `S`") and the quotient `GS` used by the Galois cohomology
data (`Skeleton/Galois/GaloisCohomology.lean`) and by `VWin`
(`Skeleton/Window/VWin.lean`).

Source (all Mathlib-only, statements and proofs):
  * `Formalism.ConjugateSelfDual.G`, `Qbar`, `cyc`, `IsPlaceOver`, `normV`, `Inertia`, `IsFrob`:
      source/src/Formalism/ConjugateSelfDual/Statement.lean:6-32
  * `ReciprocityTheory.Gal.Dec`, `mem_Dec`, `apply_mem_iff_of_mem_Dec`, `valuation_lt_one_iff'`,
    `valuation_apply_lt_one_iff`, `mul_inv_apply`, `Ine`, `mem_Ine`, `Ine_le_Dec`:
      source/src/ReciprocityTheory/GaloisValuations/Global.lean:15-66
  * `ReciprocityTheory.Gal.cycZ`, `NS`, `normal_NS`, `isClosed_NS`, `GS`, `toGS`,
    `continuous_toGS`, `locHom`, `continuous_locHom`:
      source/src/ReciprocityTheory/GaloisValuations/Global.lean:90-153
-/
import Mathlib

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace Formalism.ConjugateSelfDual

/-- The automorphism group of `Ω` over `F` (the "absolute Galois group" when `Ω` is
an algebraic closure of `F`). -/
abbrev G (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] := Ω ≃ₐ[F] Ω

/-- A fixed algebraic closure of `ℚ_[l]` (the coefficients of the `l`-adic Galois
representations).  Mathlib name: `PadicAlgCl`. -/
abbrev Qbar (l : ℕ) [Fact l.Prime] := PadicAlgCl l

/-- The `l`-adic cyclotomic character of `Ω` over `F`, with values in `(Qbar l)ˣ`. -/
def cyc (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    G F Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter (Ω) l).comp
      (MulSemiringAction.toRingAut (G F Ω) (Ω)))

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- The valuation subring `A` of `Ω` lies over the finite place `v` of `F`. -/
def IsPlaceOver (A : ValuationSubring (Ω)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ x : 𝓞 F, A.valuation (algebraMap F (Ω) (x : F)) < 1 ↔ x ∈ v.asIdeal

/-- The norm (residue field degree) of a finite place. -/
def normV (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

/-- The inertia group at the place `A`. -/
def Inertia (A : ValuationSubring (Ω)) : Set (G F Ω) :=
  {σ | σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x) < 1}

/-- The Frobenius condition at `A` (for residue degree `q`). -/
def IsFrob (A : ValuationSubring (Ω)) (q : ℕ) (σ : G F Ω) : Prop :=
  σ ∈ A.decompositionSubgroup F ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1

end places

end Formalism.ConjugateSelfDual

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- The decomposition group at `A`. -/
def Dec (A : ValuationSubring (Ω)) : Subgroup (G F Ω) := A.decompositionSubgroup F

omit [NumberField F] in
theorem mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Dec (F := F) A ↔ σ • A = A := Iff.rfl

omit [NumberField F] in
theorem apply_mem_iff_of_mem_Dec {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (x : Ω) : σ x ∈ A ↔ x ∈ A := by
  have h := mem_Dec.mp hσ
  have key : σ • x ∈ σ • A ↔ x ∈ A := ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h] at key
  exact key

theorem valuation_lt_one_iff' (A : ValuationSubring (Ω)) (y : Ω) :
    A.valuation y < 1 ↔ y ∈ A ∧ (y = 0 ∨ y⁻¹ ∉ A) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, not_le,
      Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
    simp only [hy, false_or]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩

omit [NumberField F] in
theorem valuation_apply_lt_one_iff {A : ValuationSubring (Ω)} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) (y : Ω) :
    A.valuation (σ y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', (map_inv₀ σ y).symm, apply_mem_iff_of_mem_Dec hσ,
    apply_mem_iff_of_mem_Dec hσ, EmbeddingLike.map_eq_zero_iff]

omit [NumberField F] in
theorem mul_inv_apply {σ : G F Ω} (x : Ω) : σ ((σ⁻¹ : G F Ω) x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- The inertia group at `A`, as a subgroup of the decomposition group. -/
def Ine (A : ValuationSubring (Ω)) : Subgroup (G F Ω) where
  carrier := Inertia (F := F) A
  one_mem' := ⟨(Dec (F := F) A).one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, hσ'⟩ ⟨hτ, hτ'⟩
    refine ⟨(Dec (F := F) A).mul_mem hσ hτ, fun x hx => ?_⟩
    have e : (σ * τ) x - x = σ (τ x - x) + (σ x - x) := by
      simp [AlgEquiv.mul_apply, map_sub]
    rw [e]
    exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσ _).mpr (hτ' x hx)) (hσ' x hx)
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨(Dec (F := F) A).inv_mem hσ, fun x hx => ?_⟩
    have hy : A.valuation ((σ⁻¹ : G F Ω) x) ≤ 1 := by
      rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hσ, mul_inv_apply]
      exact (A.valuation_le_one_iff x).mp hx
    have e : (σ⁻¹ : G F Ω) x - x = -(σ ((σ⁻¹ : G F Ω) x) - (σ⁻¹ : G F Ω) x) := by
      rw [mul_inv_apply]; ring
    rw [e, Valuation.map_neg]
    exact hσ' _ hy

omit [NumberField F] in
theorem mem_Ine {A : ValuationSubring (Ω)} {σ : G F Ω} :
    σ ∈ Ine (F := F) A ↔ σ ∈ Inertia (F := F) A := Iff.rfl

omit [NumberField F] in
theorem Ine_le_Dec (A : ValuationSubring (Ω)) : Ine (F := F) A ≤ Dec (F := F) A := fun _ h => (mem_Ine.mp h).1

variable (F Ω) in
/-- The `l`-adic cyclotomic character with values in `ℤ_[l]ˣ`. -/
def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

variable (Ω) in
/-- The closed normal subgroup generated by the inertia groups at places *not* in `S`. -/
def NS : Subgroup (G F Ω) :=
  (Subgroup.normalClosure
    (⋃ v ∈ Sᶜ, ⋃ A ∈ {A : ValuationSubring (Ω) | IsPlaceOver A v}, Inertia (F := F) A)
    ).topologicalClosure

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

variable (Ω) in
omit [NumberField F] in
theorem isClosed_NS : IsClosed (NS Ω S : Set (G F Ω)) := Subgroup.isClosed_topologicalClosure _

variable (Ω) in
/-- The Galois group "unramified outside `S`". -/
abbrev GS := G F Ω ⧸ NS Ω S

variable (Ω) in
def toGS : G F Ω →* GS Ω S := QuotientGroup.mk' (NS Ω S)

variable (Ω) in
omit [NumberField F] in
theorem continuous_toGS : Continuous (toGS Ω S) := by
  unfold toGS
  exact continuous_quot_mk

/-- The local Galois group at `A` maps to `GS Ω S`. -/
def locHom (A : ValuationSubring (Ω)) : Dec (F := F) A →* GS Ω S :=
  (toGS Ω S).comp (Dec (F := F) A).subtype

omit [NumberField F] in
theorem continuous_locHom (A : ValuationSubring (Ω)) :
    Continuous (locHom S A) := (continuous_toGS Ω S).comp continuous_subtype_val

end unram

end ReciprocityTheory.Gal

end
