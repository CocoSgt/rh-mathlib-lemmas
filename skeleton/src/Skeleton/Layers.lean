/-
Copyright (c) 2026 Levent Alpöge (with Claude). The propositions assembled here are the main-line
intermediate statements of the Alpöge–Claude Lean formalization of the Riemann Hypothesis
(released 2026-11-20 at https://alpo.ge/); they were copied into `skeleton/` by the three
"step 6" sessions (see SKELETON.md). All mathematical credit belongs to Levent Alpöge and Claude.

# The five layers of the main line, as one entry point

`SKELETON.md` explains the layers; this file only fixes them as definitions and collects the
links between them that are proved in this library (Mathlib-only).  Everything here is either
*stated in full* from Mathlib concepts (`Layer3`, `Layer4`, `Layer5`, and the `VWin` / `Green`
components of `Layer2`), or kept *abstract* because its statement needs hundreds of project
definitions (`Layer1`, and the analytic hypothesis `HypsSat` of `Layer2`).

| layer | original name (`source/src`)                                              | status            |
|-------|---------------------------------------------------------------------------|-------------------|
| `Layer1` | `UpperTheory.GalStar.Row0b (fun h rc => IsRecT h rc)` + `UpperTheory.Zero.LLC.RecTExists` | abstract (`Row`, `RecTExists`) |
| `Layer2` | `UpperTheory.Top.VWin`, `GlobalTheory.GLq.Green`, `Nonempty (Hyps … DRS)` | `VWin`, `Green` stated in full (`Skeleton/Window/`); `Hyps` abstract |
| `Layer3` | `Formalism.HC.ZeroFreeAll`                                                | stated in full (`Skeleton/Window/PChar.lean`) |
| `Layer4` | `UpperTheory.EveryCharacter`                                              | stated in full (`Skeleton/Top/EveryCharacter.lean`) |
| `Layer5` | `RiemannHypothesis` (Mathlib's own definition)                            | Mathlib           |

Which links are proved: `Layer3 → Layer4` (`imprimitive`), `Layer4 → Layer5` (`rh_of_every`,
and `riemannHypothesis_of_everyCharacter`, `critLine`, `Claim.strip/zeta` in `Skeleton/Top/`).
`Layer2 → Layer3` is `plugWin` (not Mathlib-only; `plugWinStatement`), `Layer1 → Layer2` /
`Layer1 → Layer4` go through `automorphic_window_of_inputs`, base change and
`every_character_of_literature_of_vWin` (not Mathlib-only; hypotheses of
`UpperTheory.FinalTheorems.everyCharacter_of_row_of`).
-/
import Skeleton.Top.MainTheorems
import Skeleton.Galois.Mainline

noncomputable section

namespace Skeleton

/-- **Layer 5** — the target, Mathlib's own `RiemannHypothesis`. -/
def Layer5 : Prop := RiemannHypothesis

/-- **Layer 4** — `UpperTheory.EveryCharacter` (`CharacterBoxes/EveryCharacter.lean:13`):
no Dirichlet `L`-function vanishes on `re s > 1/2` (except the pole of the principal character). -/
def Layer4 : Prop := EveryCharacter

/-- **Layer 3** — `Formalism.HC.ZeroFreeAll` (`TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`):
every *primitive* Dirichlet `L`-function is nonvanishing on `re s > 1/2`
(`Skeleton/Window/PChar.lean`, original namespace). -/
def Layer3 : Prop := Formalism.HC.ZeroFreeAll

/-- **Layer 2** — the inputs of `plugWin`: the automorphic window `UpperTheory.Top.VWin`
(`CharacterBoxes/ExistsPageN.lean:49`), `GlobalTheory.GLq.Green`
(`NonGaloisDescent/LabelDatum.lean:108`) — both stated in full in `Skeleton/Window/` — and the
analytic hypothesis `Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)`
(`Definitions/GlobalTwisting/APerTw.lean:23`), which is not portable and is kept abstract. -/
def Layer2 (HypsSat : Prop) : Prop := UpperTheory.Top.VWin ∧ GlobalTheory.GLq.Green ∧ HypsSat

/-- **Layer 1** — the Galois-representation input of the main line,
`UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)`
(`Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`) together with the
local-Langlands existence statement `UpperTheory.Zero.LLC.RecTExists`
(`Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`).  Neither statement can be written from
Mathlib concepts in a reasonable size (hundreds of project definitions), so both are abstract. -/
def Layer1 (Row RecTExists : Prop) : Prop := Row ∧ RecTExists

/-! ### Bridging the two namespaces used in `skeleton/`

`Skeleton/Top/` re-names the upper statements into the `Skeleton` namespace, `Skeleton/Window/`
and `Skeleton/Galois/` keep the original namespaces.  The two copies are the same propositions. -/

/-- `Skeleton.EveryCharacter` (Top) and `UpperTheory.EveryCharacter` (Window) are the same
definition, copied verbatim from `CharacterBoxes/EveryCharacter.lean:13`. -/
theorem everyCharacter_same : Skeleton.EveryCharacter = UpperTheory.EveryCharacter := rfl

/-- `Skeleton.ZeroFreeAll` (Top, with `Skeleton.PChar`) and `Formalism.HC.ZeroFreeAll`
(Window, with `Formalism.HC.PChar`) are the same statement up to the packaging of a primitive
character. -/
theorem zeroFreeAll_iff_formalism : Skeleton.ZeroFreeAll ↔ Formalism.HC.ZeroFreeAll := by
  constructor
  · intro h ψ _
    exact h ⟨ψ.N, ψ.χ, ψ.prim⟩ trivial
  · intro h ψ _
    exact h ⟨ψ.N, ψ.χ, ψ.prim⟩ trivial

theorem zeroFreeAll_iff_formalism' : Formalism.HC.ZeroFreeAll ↔ Skeleton.ZeroFreeAll :=
  zeroFreeAll_iff_formalism.symm

/-- The two copies of `imprimitive` (`CharacterBoxes/Imprimitive.lean:5`) agree. -/
theorem imprimitive_same (h : Skeleton.ZeroFreeAll) :
    Skeleton.imprimitive h = UpperTheory.Top.imprimitive (zeroFreeAll_iff_formalism.mp h) := rfl

/-! ### The links that are proved from Mathlib only -/

/-- **`Layer3 → Layer4`**: original `UpperTheory.Top.imprimitive`
(`CharacterBoxes/Imprimitive.lean:5`; an imprimitive `L`-function is its primitive model times
nonvanishing Euler factors). -/
theorem layer4_of_layer3 : Layer3 → Layer4 := UpperTheory.Top.imprimitive

/-- **`Layer4 → Layer5`**: original `Formalism.VW.rh_of_every`
(`Formalism/GammaFactorNonvanishing/CritLine.lean:29`, via `rh_of_right`, `RhOfRight.lean:5`). -/
theorem layer5_of_layer4 : Layer4 → Layer5 := Skeleton.rh_of_every

/-- `Layer4 → Layer5` by the second route of the original development
(`UpperTheory.riemannHypothesis_of_everyCharacter`, `CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215`). -/
theorem layer5_of_layer4' : Layer4 → Layer5 := Skeleton.riemannHypothesis_of_everyCharacter

/-- **`Layer2 → Layer3`** is `plugWin` (`CharacterBoxes/EveryCharacter.lean:8`), the one link
that is not Mathlib-only; with it as a hypothesis the layer step follows. -/
theorem layer3_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer3 := fun ⟨hV, hG, hH⟩ => hW hG hV hH

/-- **`Layer2 → Layer4`**: original `plugAll` (`CharacterBoxes/EveryCharacter.lean:16`) =
`imprimitive ∘ plugWin`; Mathlib-only modulo `plugWin`. -/
theorem layer4_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer4 := fun h => UpperTheory.Top.plugAll_of_plugWin hW h.2.1 h.1 h.2.2

/-- **`Layer1 → Layer4`** along the route that `Main.lean` actually uses
(`UpperTheory.FinalTheorems.everyCharacter_of_row`, `CharacterBoxes/MainConclusion.lean:7`):
modulo the automorphic-window theorem with base change and the literature theorem
`every_character_of_literature_of_vWin` (`EveryCharacterOfLiteratureOfVWin.lean:810`), which
are the hypotheses of `UpperTheory.FinalTheorems.everyCharacter_of_row_of`. -/
theorem layer4_of_layer1 {Row RecTExists : Prop} {BaseChangeIsobaricN : Prop}
    (hmk : Row → UpperTheory.LiteratureTheorems.OpenImageCondition Row)
    (bc : BaseChangeIsobaricN)
    (haw : ∀ (_O : UpperTheory.LiteratureTheorems.OpenImageCondition Row),
      BaseChangeIsobaricN → Row → UpperTheory.Top.VWin)
    (hlit : ∀ (_O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements Row RecTExists),
      UpperTheory.Top.VWin → UpperTheory.EveryCharacter) :
    Layer1 Row RecTExists → Layer4 := fun ⟨h, hrec⟩ =>
  UpperTheory.FinalTheorems.everyCharacter_of_row_of hlit
    (UpperTheory.One.vwin_of_row_of hmk bc haw) hrec h

/-- **`Layer2 → Layer5`**: everything from the `plugWin` inputs down to the Riemann Hypothesis
is Mathlib-only once `plugWin` is given. -/
theorem layer5_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer5 := layer5_of_layer4 ∘ layer4_of_layer2 hW

/-- The five theorems of `Main.lean` and the four statements of `Statements.lean`, from
`Layer2` modulo `plugWin` (original `Supplements/Kernels/MainTheorems.lean` + `Main.lean`). -/
theorem mainOfLayer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat →
    RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
      PrimitiveDirichletLZerosOnLine ∧ RiemannHypothesis :=
  fun h => Skeleton.mainOfPlugWin
    (fun hG hV hH => zeroFreeAll_iff_formalism.mpr (layer3_of_layer2 hW ⟨hV, hG, hH⟩)) h.2.1 h.1 h.2.2

end Skeleton
