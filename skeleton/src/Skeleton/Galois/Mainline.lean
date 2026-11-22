/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Galois layer glue: how `Row0b` + `RecTExists` are *assembled* into
`VWin` and then `EveryCharacter`.  Since `Row0b`/`IsRecT` (Galois/Row0b.lean, Galois/IsRecT.lean)
and `PositivityTheory.Rg.BcN.BaseChangeIsobaricN` are not portable yet, `Row`, `RecTExists`
and `BaseChangeIsobaricN` are abstract `Prop`s here; the three deep theorems are hypotheses:

  * `UpperTheory.Zero.LLC.recTExists : RecTExists`
        Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20
  * `UpperTheory.One.vwin_of_row (h : Row) : VWin :=
        automorphic_window_of_inputs (OpenImageCondition.mk h) baseChangeN h`
        AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4
    (with `automorphic_window_of_inputs (O : OpenImageCondition) (bc : BaseChangeIsobaricN) (gal : RowT) : VWin`,
        …/DenseThresholdCases/TopMainZj.lean:71, and `baseChangeN : BaseChangeIsobaricN`,
        Foundations/BaseChangeIdentities/DefiniteNHolds.lean:5)
  * `every_character_of_literature_of_vWin (O : OpenLiteratureStatements) (hV : VWin) : EveryCharacter`
        ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810

and the source assemblies are

    theorem everyCharacter_of_row (h : Row) : EveryCharacter :=
      every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)       -- MainConclusion.lean:7
    def UpperTheory.One.M.Row : Prop := Row0b fun h rc => IsRecT h rc                 -- SatakeParameters/RecT.lean:6
    def UpperTheory.V.Z.Win.RowT : Prop := Row0b fun h rc => IsRecT h rc              -- AutomorphyLifting/WeakOfAtt.lean:47

    structure OpenImageCondition : Prop where
      galoisRepOfPolarizedPairLit : UpperTheory.V.Z.Win.RowT                        -- …/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207
    structure OpenLiteratureStatements : Prop where
      caraianiLocalGlobalDual : UpperTheory.One.M.Row
      localLanglandsExists : UpperTheory.Zero.LLC.RecTExists
      galoisRepOfPolarizedPairLit : UpperTheory.One.M.Row                          -- EveryCharacterOfLiteratureOfVWin.lean:215

Below, `OpenImageCondition RowT` and `OpenLiteratureStatements Row RecTExists` are these two
structures with `RowT`/`Row`/`RecTExists` as parameters (they are definitionally the same
proposition once `Row := Row0b fun h rc => IsRecT h rc`).
-/
import Mathlib
import Skeleton.PChar
import Skeleton.Window.VWin
import Skeleton.Window.Green
import Skeleton.Window.PlugAll

noncomputable section

namespace UpperTheory.LiteratureTheorems

/-- Source: TemperedProductOfSquareIntegrable.lean:207, with `RowT` as a parameter. -/
structure OpenImageCondition (RowT : Prop) : Prop where
  galoisRepOfPolarizedPairLit : RowT

/-- Source: EveryCharacterOfLiteratureOfVWin.lean:215, with `Row`, `RecTExists` as parameters. -/
structure OpenLiteratureStatements (Row RecTExists : Prop) : Prop where
  caraianiLocalGlobalDual : Row
  localLanglandsExists : RecTExists
  galoisRepOfPolarizedPairLit : Row

end UpperTheory.LiteratureTheorems

namespace UpperTheory.One

/-- **Provable glue (assembly of `vwin_of_row`)**: from a way of turning a `Row`-hypothesis into an
`OpenImageCondition` (source: `OpenImageCondition.mk h`), a base-change statement, and the
deep theorem `automorphic_window_of_inputs`, one gets `Row → VWin`. -/
theorem vwin_of_row_of {Row : Prop} {BaseChangeIsobaricN : Prop}
    (hmk : Row → UpperTheory.LiteratureTheorems.OpenImageCondition Row)
    (bc : BaseChangeIsobaricN)
    (haw : ∀ (_ : UpperTheory.LiteratureTheorems.OpenImageCondition Row),
      BaseChangeIsobaricN → Row → UpperTheory.Top.VWin)
    (h : Row) : UpperTheory.Top.VWin :=
  haw (hmk h) bc h

end UpperTheory.One

namespace UpperTheory.FinalTheorems

/-- **Provable glue (assembly of `everyCharacter_of_row`, MainConclusion.lean:7)**:
`vwin_of_row` + `recTExists` + the literature theorem give `Row → EveryCharacter`. -/
theorem everyCharacter_of_row_of {Row RecTExists : Prop}
    (hlit : ∀ (_ : UpperTheory.LiteratureTheorems.OpenLiteratureStatements Row RecTExists),
      UpperTheory.Top.VWin → UpperTheory.EveryCharacter)
    (hvwin : Row → UpperTheory.Top.VWin) (hrec : RecTExists) (h : Row) : UpperTheory.EveryCharacter :=
  hlit ⟨h, hrec, h⟩ (hvwin h)

/-- **The whole lower mainline, modulo the deep theorems.**  If
`Row` (i.e. `Row0b fun h rc => IsRecT h rc`) holds, the automorphic window theorem
`automorphic_window_of_inputs` and base change hold, `Green` and the analytic hypothesis
`HypsSat` hold, and the link `Green + VWin + HypsSat → ZeroFreeAll` holds — then `EveryCharacter`.
On the route of `Main.lean` this is `everyCharacter_of_row` → `every_character_of_literature_of_vWin`
→ `every_character_of_theta_integrals_local_matching` → `every_character_of_green_v_win`
(= `imprimitive ∘ zero_free_all_of_green_v_win`, `TopPlug.lean:12-18`), with the analytic core that
discharges `HypsAlt … DefiniteSideCondition` and the deep inputs isolated as named hypotheses
(`everyCharacter_of_row_of` keeps the literature-package route; this theorem uses the `plugWin`-shaped
route, on which `Main.lean` is via `zero_free_all_of_green_v_win`).  Combined with the upper skeleton
(`EveryCharacter → RiemannHypothesis`, `Skeleton/Top/`) this gives RH modulo these hypotheses. -/
theorem everyCharacter_of_row_and_inputs {Row BaseChangeIsobaricN HypsSat : Prop}
    (hmk : Row → UpperTheory.LiteratureTheorems.OpenImageCondition Row)
    (bc : BaseChangeIsobaricN)
    (haw : ∀ (_ : UpperTheory.LiteratureTheorems.OpenImageCondition Row),
      BaseChangeIsobaricN → Row → UpperTheory.Top.VWin)
    (hW : UpperTheory.Top.plugWinStatement HypsSat)
    (hG : GlobalTheory.GLq.Green) (hH : HypsSat) (h : Row) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.plugAll_of_plugWin hW hG (UpperTheory.One.vwin_of_row_of hmk bc haw h) hH

end UpperTheory.FinalTheorems

end
