/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Galois layer (1/2): the statement of `Row0b`
("mainline layer-2 output: every regular algebraic polarized cuspidal automorphic
representation of `GL_a(𝔸_E)` over a CM field `E` has an `l`-adic Galois representation
with prescribed Hodge–Tate weights, crystalline/de Rham/pluriharmonic behaviour and
the expected local behaviour away from `l`").

What is compiled here: the two Mathlib-only definitions `IsQp` and `IsQpBig` of the
statement.  The rest of `Row0b` (structures `AwayB`, `AboveB`, `PropsB`) is **not yet
portable**: its atoms are the automorphic-representation and p-adic Hodge theory
definitions of `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/*`
and `Formalism/SharpRestriction/LevelLetterCocycles/DataN{,Loc}.lean`.  The verbatim
statements are kept below as comments, so that this file is the exact interface that a
future port of the atoms must satisfy (see SKELETON-lower.md §3 for the chain depths).

Source:
  * `IsQp`        source/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjAlt.lean:16
  * `IsQpBig`     …/WeightsConjBis.lean:15-20
  * `RecNotion`, `Tor`, `Sqf`, `Away`   …/WeightsConjAlt.lean:16-40
  * `AwayB`, `AboveB`, `PropsB`, `Row0b`, `Row0.row0b`  …/WeightsConjBis.lean:26-86
  * `UpperTheory.One.M.Row`, `UpperTheory.V.Z.Win.RowT` (= `Row0b fun h rc => IsRecT h rc`)
        …/UnitarySphericalFixing/SatakeParameters/RecT.lean:6,
        …/ModularityArgument/AutomorphyLifting/WeakOfAtt.lean:47

Verbatim statements (WeightsConjBis.lean:26-73, with the `open`s of the source file):

    structure AwayB (x y : WD h) : Prop where
      dim : x.lpDim = y.lpDim
      tor : Tor y → y.mono0 → x = y
      tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 →
        x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

    structure AboveB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
        (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
        (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
      crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ →
        IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
      nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc →
        ((IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) →
        (rc (algNorm σ)).mono0 →
        IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
        AwayB (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

    structure PropsB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
        (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
      cont : Continuous r
      ss : IsSSRep r
      away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))
      weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
        ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
      weights_conj : ∀ τ : E →+* Qbar l,
        HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
      above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveB Rc π ι r HT P h Bw hj

    def Row0b : Prop :=
      ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
        (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
        ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg →
          GlobalTheory.ContraPair.PolarizedPair π χ →
          ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsB Rc π ι r wt HT

(`Rc : UpperTheory.GalStar.RecNotion` is a `variable` of the section; `RecNotion` is
`∀ {E Ω} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), (IrrGL (w.adicCompletion E) → WD h) → Prop`,
WeightsConjAlt.lean:16-18.  The mainline instantiates it with `fun h rc => IsRecT h rc`.)
-/
import Mathlib
import Skeleton.Galois.Places

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.GalStar

open Formalism.ConjugateSelfDual

/-- The finite place `w` has residue field `𝔽_g` for some prime `g` (so `E_w ≅ ℚ_g`). -/
def IsQp {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i

/-- Same, with the side condition `n = 1 ∨ 16 n² < g` (the "big residue characteristic"
hypothesis of the `tame0`/`nice` fields of `AwayB`/`AboveB`). -/
def IsQpBig {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i ∧ (n = 1 ∨ 16 * n ^ 2 < g)

theorem IsQpBig.isQp {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} (k : IsQpBig w n) : IsQp w := by
  obtain ⟨g, p, i, c, -⟩ := k
  exact ⟨g, p, i, c⟩

end UpperTheory.GalStar

end
