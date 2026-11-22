/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Window layer (4/4): the analytic hypothesis and the glue `plugAll`.

The link `Green + VWin + Hyps → ZeroFreeAll` of the main line.  On the route that `Main.lean`
actually takes it is (source/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-18):

  theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
      (h : Nonempty (GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) GlobalTheory.Fc.DefiniteSideCondition)) :
      Formalism.HC.ZeroFreeAll :=
    h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
      (GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)
      fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
  theorem UpperTheory.Top.every_character_of_green_v_win … : UpperTheory.EveryCharacter :=
    UpperTheory.Top.imprimitive (zero_free_all_of_green_v_win hG hV h)

The parallel version is `UpperTheory.Top.plugWin` / `plugAll` (`CharacterBoxes/EveryCharacter.lean:8-18`, hypothesis
`Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)`, through `shape_of … (shapeWin hG) …`); `Main.lean`
does not pass through it (its only user is `FockModels/EveryCharacterE.lean:67-70`).  Both share the final step
`UpperTheory.Top.zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`), so the *shape* of the link is the same.

The analytic hypothesis is **not portable** (not even at statement level in a reasonable size): `HypsAlt` / `Hyps` are
`Type 1` structures with 40+ fields, each a global analytic hypothesis on families of lattices / automorphic forms
(`ThirdPlaceSeries/Hyps.lean:22`; `source/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23-92`),
and `DefiniteSideCondition` (`ThirdPlaceSeries/DefiniteSideCondition.lean:25`) / `DRS` (`…/GlobalTwisting/DRS.lean:21-31`)
are concrete such data; `Closed` is `Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159` and `LinkN` is
`Formalism/SharpRestriction/GlobalTheoremInputs.lean:45`.  In the source this hypothesis is discharged by the analytic core
(`UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`, `ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44`,
and the `GlobalTheory.Fc.*` machinery — the bulk of the library), i.e. it is an output of the analytic-core layer.
Here it is abstracted as a `Prop` parameter `HypsSat`.

The proof of the link itself needs `zeroFreeAll_of_topG`, `shape_closed_link_n_of_green` (parallel: `shape_of`, `shapeWin`),
`forall_goal_of_shape_of_hyps` and `supplyChi`, and is not Mathlib-only.
-/
import Mathlib
import Skeleton.PChar
import Skeleton.Top.PlugWin
import Skeleton.Window.VWin
import Skeleton.Window.Green

noncomputable section

namespace UpperTheory.Top

/-- The statement of the link `Green + VWin + Hyps → ZeroFreeAll` (`TopPlug.lean:12` on the main line;
the parallel `plugWin`, `EveryCharacter.lean:8`) with the non-portable analytic hypothesis — on the
main line `Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)` —
replaced by an abstract `Prop`.  This is `Skeleton.PlugWin` instantiated with the skeleton's own `Green` and `VWin`. -/
def plugWinStatement (HypsSat : Prop) : Prop :=
  Skeleton.PlugWin GlobalTheory.GLq.Green UpperTheory.Top.VWin HypsSat

/-- **Provable glue:** assembling `plugAll` / `every_character_of_green_v_win` from the link; the only
non-Mathlib step is the link itself (the `imprimitive` step is proved in `Skeleton/PChar.lean`). -/
theorem plugAll_of_plugWin {HypsSat : Prop} (hW : plugWinStatement HypsSat)
    (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin) (h : HypsSat) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (hW hG hV h)

end UpperTheory.Top

end
