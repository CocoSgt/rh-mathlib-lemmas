/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Window layer (4/4): `Hyps` and the glue `plugAll`.

`UpperTheory.Top.plugAll (hG : Green) (hV : VWin) (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) :
UpperTheory.EveryCharacter := imprimitive (plugWin hG hV h)`
(source/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:16-18).

`Hyps` is **not portable** (not even at statement level in a reasonable size): it is the
`Type 1` structure `GlobalTheory.Fc.Hyps` with 40+ fields, each a global analytic
hypothesis on families of lattices / automorphic forms
(source/src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean:23-92), and
`DRS : R1.DefT` is a concrete such hypothesis (…/GlobalTwisting/DRS.lean:21-31); `Closed` is
Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159 and `LinkN` is
Formalism/SharpRestriction/GlobalTheoremInputs.lean:45.  In the source this hypothesis is
discharged by the analytic core (`GlobalTheory.Fc.*`, the bulk of the library), i.e. it is
the *mainline layer-4 output*.  Here it is abstracted as a `Prop` parameter `HypsSat`.

The proof of `plugWin` itself needs `zeroFreeAll_of_topG`, `shape_of`, `shapeWin`, `supplyChi`
(CharacterBoxes/ZeroFreeAllOfTopG.lean:26, AbelianVarietyTheory/Proofs/GlobalInterpolation/ShapeOf.lean:14,
CharacterBoxes/ShapeWin.lean:27, CharacterBoxes/SupplyChi.lean:8) and is not Mathlib-only.
-/
import Mathlib
import Skeleton.Window.PChar
import Skeleton.Window.VWin
import Skeleton.Window.Green

noncomputable section

namespace UpperTheory.Top

open Formalism.HC

/-- The statement of `UpperTheory.Top.plugWin` (EveryCharacter.lean:8) with the
non-portable hypothesis `Nonempty (Hyps … DRS)` replaced by an abstract `Prop`.
This is the missing step between the three layer-4/3 inputs and `ZeroFreeAll`. -/
def plugWinStatement (HypsSat : Prop) : Prop :=
  GlobalTheory.GLq.Green → UpperTheory.Top.VWin → HypsSat → ZeroFreeAll

/-- **Provable glue:** assembling `plugAll` from `plugWin`; the only non-Mathlib step of
`plugAll` is `plugWin` itself (the `imprimitive` step is proved in `Skeleton/Window/PChar.lean`). -/
theorem plugAll_of_plugWin {HypsSat : Prop} (hW : plugWinStatement HypsSat)
    (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin) (h : HypsSat) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (hW hG hV h)

end UpperTheory.Top

end
