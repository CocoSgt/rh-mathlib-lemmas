/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Galois layer (2/2): the statement of `IsRecT` / `RecTExists`
("mainline layer-2 output: for every number field `E`, place `w` and algebraic closure
data `(Ω, A)`, there exists a *reciprocity map* `rc` assigning to every irreducible smooth
representation of `GL_n(E_w)` a Weil–Deligne representation, satisfying the list `LawsT`
of local Langlands axioms (dimension, behaviour on characters, Langlands quotient,
cuspidal ⇒ irreducible, twisting, central character, duality, injectivity, depth,
and the type law at depth zero).")

`IsRecT` is **not yet portable**: its atoms are the smooth representation theory of
`GL_n` over a local field (`IrrGL`, `IrrRep`, `IrrCl`, `Segment`, `IsL`, `segSum`,
`parInd`, …), the Weil–Deligne API (`WD`, `Weil`, `lpTw`, `lpChar`, `lpDual`, `eig`, …)
and the local reciprocity data (`IsLocalArtin`, `IsRegularChar`, `TameGen.Inflates`).
See SKELETON-lower.md §3 for the chain depths (150 statement-level definitions, longest
chain 14; 148 definitions + 20 lemmas once bodies are included).

What is compiled here: a *schematic* form `RecTExistsSchematic`
in which the type `R` of reciprocity maps and the predicate `T` ("satisfies the reciprocity
laws") are parameters; the source definitions are the instances `R := fun E Ω A w h =>
(IrrGL (w.adicCompletion E) → WD h)` and `T := IsRecT`.

Source (verbatim, source/src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:20-85;
a duplicate lives in Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/RecTExists.lean):

    def GoodCusp (y : IrrGL k) : Prop :=
      y.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) ∧
        ∃ (y₀ : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), GlobalTheory.PRep.fixed y₀.rep (GlobalTheory.SplitWeil.KOne k (Fin y₀.1)) ≠ ⊥ ∧ y = y₀.tw χ hχ)

    def Good (x : IrrGL k) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, GoodCusp y

    def Toral (x : IrrGL k) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, y.1 = 1

    def TypeLaw (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
      ∀ (E' : Type) [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E' Ω]
        (g : ℕ) [Fact g.Prime] (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
        ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
        ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
        ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
        ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
          RingHom.ker red = w'.asIdeal →
        ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
        ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
          (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
            τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
        ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
          GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
          (rc (cls σ)).mono0 ∧
          ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
            Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
            (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
              ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

    structure LawsT (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
        (rc : IrrGL (w.adicCompletion E) → WD h) : Prop where
      dim : ∀ x, (rc x).lpDim = x.1
      one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
      langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
        IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l
      cusp : ∀ x, x.IsCusp → IsIrrWD (rc x)
      nu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s
      absCentral : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
        ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
      twist : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))
      central : ∀ (x : IrrGL (w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
        ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)
      dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
        Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual
      inj : ∀ x y, Good y → rc x = rc y → x = y
      depth : ∀ x, Good x → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)
      type : TypeLaw h rc

    def IsRecT (rc : IrrGL (w.adicCompletion E) → WD h) : Prop := ∃ a ha, LawsT (h := h) a ha rc

    def RecTExists : Prop :=
      ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
        (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ rc, IsRecT h rc

    def RecTUnique : Prop :=
      ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
        (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc rc' : IrrGL (w.adicCompletion E) → WD h),
        IsRecT h rc → IsRecT h rc' → ∀ x, Good x → rc x = rc' x

(`Gn`, `Mt`, `IsCusp` are ported in `Skeleton/Window/Green.lean`; `Ine`, `normV`, `IsPlaceOver`
in `Skeleton/Galois/Places.lean`.)  The mainline theorem is
`UpperTheory.Zero.LLC.recTExists : RecTExists` (Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20).
-/
import Mathlib
import Skeleton.Galois.Places

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Zero.LLC

open Formalism.ConjugateSelfDual

/-- The type of "reciprocity maps" at `(E, Ω, A, w, h)`, as an abstract parameter:
in the source this is `fun E Ω A w h => (IrrGL (w.adicCompletion E) → WD h)`. -/
abbrev RecMapType :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → Type

/-- The predicate "the reciprocity map `rc` satisfies the local Langlands laws", as an
abstract parameter; in the source this is `fun E Ω A w h rc => IsRecT h rc`. -/
abbrev RecLawPred (R : RecMapType) :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), R E Ω A w h → Prop

/-- **Schematic `RecTExists`** (IsRecTOfIsRec.lean:78): for every `(E, Ω, A, w, h)` there is a
reciprocity map satisfying the laws.  `RecTExists = RecTExistsSchematic R T` for the
instantiations above. -/
def RecTExistsSchematic (R : RecMapType) (T : RecLawPred R) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ rc, T E Ω A w h rc

end UpperTheory.Zero.LLC

end
