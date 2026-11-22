/-
Copyright (c) 2026 Levent Alpöge (with Claude). The propositions assembled here are the main-line
intermediate statements of the Alpöge–Claude Lean formalization of the Riemann Hypothesis
(released 2026-11-20 at https://alpo.ge/); they were copied into `skeleton/` by the "step 6"
sessions (see SKELETON.md). All mathematical credit belongs to Levent Alpöge and Claude.

# The five layers of the main line, as one entry point

`SKELETON.md` explains the layers; this file only fixes them as definitions and collects the
links between them that are proved in this library (Mathlib-only).  The main line, walked the
way `Main.lean` walks it (file:line in `source/src`):

```
Layer 1   Row0b IsRecT  +  RecTExists                    Galois representations, local Langlands
   │  vwin_of_row (CharacterBoxes/MainConclusion.lean:7-8)          ⟹ VWin            (window)
Layer 2   VWin ∧ Green ∧ Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)
   │  zero_free_all_of_green_v_win (ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12)   ⟹ ZeroFreeAll
Layer 3   Formalism.HC.ZeroFreeAll
   │  imprimitive (CharacterBoxes/Imprimitive.lean:5)                                  ⟹ EveryCharacter
Layer 4   UpperTheory.EveryCharacter
   │  rh_of_every (Formalism/GammaFactorNonvanishing/CritLine.lean:29, RhOfRight.lean:5)
   │  riemannHypothesis_of_everyCharacter (CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215)
Layer 5   RiemannHypothesis   (+ critLine, Claim.strip / Claim.zeta)
```

The parallel version `plugWin` / `plugAll` (`CharacterBoxes/EveryCharacter.lean:8`, `:16`, hypothesis
`Nonempty (Hyps (…) DRS)`) has the same shape and is *not* on this route; both share the last step
`zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`).

Everything here is either *stated in full* from Mathlib concepts (`Layer3`, `Layer4`, `Layer5`, and
the `VWin` / `Green` components of `Layer2`), or kept *abstract* because its statement needs hundreds
of project definitions (`Layer1`, and the analytic hypothesis `HypsSat` of `Layer2`).

| layer | original name (`source/src`)                                              | status            |
|-------|---------------------------------------------------------------------------|-------------------|
| `Layer1` | `UpperTheory.GalStar.Row0b (fun h rc => IsRecT h rc)` + `UpperTheory.Zero.LLC.RecTExists` | abstract (`Row`, `RecTExists`) |
| `Layer2` | `UpperTheory.Top.VWin`, `GlobalTheory.GLq.Green`, `Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)` | `VWin`, `Green` stated in full (`Skeleton/Window/`); the analytic hypothesis abstract |
| `Layer3` | `Formalism.HC.ZeroFreeAll`                                                | stated in full (`Skeleton/PChar.lean`) |
| `Layer4` | `UpperTheory.EveryCharacter`                                              | stated in full (`Skeleton/PChar.lean`) |
| `Layer5` | `RiemannHypothesis` (Mathlib's own definition)                            | Mathlib           |

Which links are proved: `Layer3 → Layer4` (`imprimitive`), `Layer4 → Layer5` (`rh_of_every`,
and `riemannHypothesis_of_everyCharacter`, `critLine`, `Claim.strip/zeta` in `Skeleton/Top/`).
`Layer2 → Layer3` is `zero_free_all_of_green_v_win` / `plugWin` (not Mathlib-only; `plugWinStatement`
as a hypothesis), `Layer1 → Layer2` / `Layer1 → Layer4` go through `automorphic_window_of_inputs`,
base change and `every_character_of_literature_of_vWin` (not Mathlib-only; hypotheses of
`UpperTheory.FinalTheorems.everyCharacter_of_row_of`).
-/
import Skeleton.Top.MainTheorems
import Skeleton.Galois.Mainline

noncomputable section

namespace Skeleton

/-- **Layer 5** — the target, Mathlib's own `RiemannHypothesis`. -/
def Layer5 : Prop := RiemannHypothesis

/-- **Layer 4** — `UpperTheory.EveryCharacter` (`CharacterBoxes/EveryCharacter.lean:13`, in
`Skeleton/PChar.lean`): no Dirichlet `L`-function vanishes on `re s > 1/2` (except the pole of
the principal character). -/
def Layer4 : Prop := UpperTheory.EveryCharacter

/-- **Layer 3** — `Formalism.HC.ZeroFreeAll` (`TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`,
in `Skeleton/PChar.lean`): every *primitive* Dirichlet `L`-function is nonvanishing on `re s > 1/2`. -/
def Layer3 : Prop := Formalism.HC.ZeroFreeAll

/-- **Layer 2** — the inputs of `zero_free_all_of_green_v_win` / `plugWin`: the automorphic window
`UpperTheory.Top.VWin` (`CharacterBoxes/ExistsPageN.lean:49`, `Skeleton/Window/VWin.lean`), the
analytic input `GlobalTheory.GLq.Green` (`NonGaloisDescent/LabelDatum.lean:108`,
`Skeleton/Window/Green.lean`) — both stated in full — and the analytic hypothesis.  On the main
line the latter is `Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)`
(`ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22`, `DefiniteSideCondition.lean:25`; the parallel
`plugWin` uses `Nonempty (Hyps (…) DRS)`, `Definitions/GlobalTwisting/APerTw.lean:23`, `DRS.lean:21`);
it is not portable and is kept abstract as `HypsSat`. -/
def Layer2 (HypsSat : Prop) : Prop := UpperTheory.Top.VWin ∧ GlobalTheory.GLq.Green ∧ HypsSat

/-- **Layer 1** — the Galois-representation input of the main line,
`UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)`
(`Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`) together with the
local-Langlands existence statement `UpperTheory.Zero.LLC.RecTExists`
(`Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`).  Neither statement can be written from
Mathlib concepts in a reasonable size (hundreds of project definitions), so both are abstract
(what can be ported of them is in `Skeleton/Galois/Row0b.lean` and `Skeleton/Galois/IsRecT.lean`). -/
def Layer1 (Row RecTExists : Prop) : Prop := Row ∧ RecTExists

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

/-- **`Layer3 → Layer5`**: "if every primitive Dirichlet `L`-function is nonvanishing on `re s > 1/2`,
then the Riemann Hypothesis holds" — the composition of the two Mathlib-only links. -/
theorem layer5_of_layer3 : Layer3 → Layer5 := layer5_of_layer4 ∘ layer4_of_layer3

/-- From `Layer4` one gets the five theorems of `Main.lean` and the four propositions of
`Statements.lean` (`Supplements/Kernels/MainTheorems.lean` + `Main.lean`, original). -/
theorem mainOfLayer4 (h : Layer4) :
    RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
      PrimitiveDirichletLZerosOnLine ∧ RiemannHypothesis :=
  ⟨riemannZeta_eq_zero_re h, LFunction_ne_zero_of_half_lt_re h, LFunction_eq_zero_re h,
    LFunction_eq_zero_re_of_isPrimitive h, riemannHypothesis h⟩

/-! ### `Layer2 → Layer3`: the link that is *not* proved here -/

/-- **`Layer2 → Layer3`** is the link `UpperTheory.Top.zero_free_all_of_green_v_win`
(`ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`; parallel version `UpperTheory.Top.plugWin`,
`CharacterBoxes/EveryCharacter.lean:8`), the one link of the main line that is not Mathlib-only.
With it as a hypothesis (`UpperTheory.Top.plugWinStatement HypsSat`, `Skeleton/Window/PlugAll.lean`)
the layer step follows. -/
theorem layer3_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer3 := fun ⟨hV, hG, hH⟩ => hW hG hV hH

/-- **`Layer2 → Layer4`**: original `every_character_of_green_v_win` (`TopPlug.lean:16`) / `plugAll`
(`CharacterBoxes/EveryCharacter.lean:16`) = `imprimitive ∘` the link; Mathlib-only modulo the link. -/
theorem layer4_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer4 := fun h => UpperTheory.Top.plugAll_of_plugWin hW h.2.1 h.1 h.2.2

/-- **`Layer2 → Layer5`**: everything from the inputs of the link down to the Riemann Hypothesis
is Mathlib-only once the link is given. -/
theorem layer5_of_layer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat → Layer5 := layer5_of_layer4 ∘ layer4_of_layer2 hW

/-- The five theorems of `Main.lean` and the four statements of `Statements.lean`, from
`Layer2` modulo the link (original `Supplements/Kernels/MainTheorems.lean` + `Main.lean`). -/
theorem mainOfLayer2 {HypsSat : Prop} (hW : UpperTheory.Top.plugWinStatement HypsSat) :
    Layer2 HypsSat →
    RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
      PrimitiveDirichletLZerosOnLine ∧ RiemannHypothesis :=
  fun h => Skeleton.mainOfPlugWin (fun hG hV hH => hW hG hV hH) h.2.1 h.1 h.2.2

/-! ### `Layer1 → Layer4`: assembly modulo the deep theorems -/

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

/-- **`Layer1 → Layer5`**: same, composed with the Mathlib-only `Layer4 → Layer5`. -/
theorem layer5_of_layer1 {Row RecTExists : Prop} {BaseChangeIsobaricN : Prop}
    (hmk : Row → UpperTheory.LiteratureTheorems.OpenImageCondition Row)
    (bc : BaseChangeIsobaricN)
    (haw : ∀ (_O : UpperTheory.LiteratureTheorems.OpenImageCondition Row),
      BaseChangeIsobaricN → Row → UpperTheory.Top.VWin)
    (hlit : ∀ (_O : UpperTheory.LiteratureTheorems.OpenLiteratureStatements Row RecTExists),
      UpperTheory.Top.VWin → UpperTheory.EveryCharacter) :
    Layer1 Row RecTExists → Layer5 := layer5_of_layer4 ∘ layer4_of_layer1 hmk bc haw hlit

end Skeleton
