/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original statement in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Abstracted into the "main-line skeleton" (skeleton/); all mathematical credit belongs to
Levent Alpöge and Claude.

# The one link of the main line that cannot be reproduced from Mathlib alone:
`Green + VWin + (analytic hypothesis) → ZeroFreeAll`

On the route that `Main.lean` actually takes, this link is `UpperTheory.Top.zero_free_all_of_green_v_win`
(`Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`):

```
theorem UpperTheory.Top.zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (GlobalTheory.Fc.HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) GlobalTheory.Fc.DefiniteSideCondition)) :
    Formalism.HC.ZeroFreeAll :=
  h.elim fun h => UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
    (GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)
    fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
```

and `UpperTheory.Top.every_character_of_green_v_win` (`TopPlug.lean:16`) is `imprimitive` applied to it.
The parallel version `UpperTheory.Top.plugWin` / `plugAll` (`CharacterBoxes/EveryCharacter.lean:8`, `:16`,
with hypothesis `Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)`, proved through
`shape_of … (shapeWin hG) …`) is **not** used by `Main.lean` (its only user is
`FockModels/EveryCharacterE.lean:67–70`); both reduce to `UpperTheory.Top.zeroFreeAll_of_topG`
(`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`).

The three inputs and all intermediate statements are defined deep inside the project's own formalism
(see SKELETON-top.md §3 for the full list of definitions and their depth):
* `GlobalTheory.GLq.Green` — `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`
  (stated in full in `Skeleton/Window/Green.lean`)
* `UpperTheory.Top.VWin` — `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`
  (stated in full in `Skeleton/Window/VWin.lean`)
* `HypsAlt`, `DefiniteSideCondition` — `ThirdPlaceSeries/Hyps.lean:22`, `…/DefiniteSideCondition.lean:25`
  (parallel version: `Hyps`, `DRS`, `Closed`, `LinkN` — `Definitions/GlobalTwisting/APerTw.lean:23`,
  `…/GlobalTwisting/DRS.lean:21`, `Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159`,
  `…/GlobalTheoremInputs.lean:45`)
* `TopG` — `CharacterBoxes/ZeroFreeAllOfTopG.lean:12`; `TopShape` — `…/GlobalTwisting/TopShape.lean:17`.

The analytic hypothesis cannot be unfolded into Mathlib definitions, so here the three inputs are kept as
*opaque propositions* `Green VWin Hyps : Prop` and the link is stated as `PlugWin`.  With the original
development available, `Skeleton.PlugWin Green VWin Hyps` is proved by
`fun hG hV h => UpperTheory.Top.zero_free_all_of_green_v_win hG hV h` (or `… plugWin hG hV h`).
Everything *after* this link is Mathlib-only and is proved in this directory:
`PlugWin → EveryCharacter → RiemannHypothesis` (and the four statements of `Statements.lean`), see
`Skeleton/Top/MainTheorems.lean`.  The concrete instantiation with the skeleton's own `Green` and `VWin`
is `UpperTheory.Top.plugWinStatement` (`Skeleton/Window/PlugAll.lean`).
-/
import Skeleton.PChar

namespace Skeleton

/-- The link `Green + VWin + Hyps → ZeroFreeAll` with its three inputs as opaque propositions.
On the main line this is `UpperTheory.Top.zero_free_all_of_green_v_win` (`TopPlug.lean:12`) with
`Hyps := Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)`; the parallel
`UpperTheory.Top.plugWin` (`EveryCharacter.lean:8`) has `Hyps := Nonempty (Hyps (…) DRS)`.
Not proved here (see the file header). -/
def PlugWin (Green VWin Hyps : Prop) : Prop := Green → VWin → Hyps → Formalism.HC.ZeroFreeAll

/-- Original: `UpperTheory.Top.every_character_of_green_v_win` (`TopPlug.lean:16`) and the parallel
`UpperTheory.Top.plugAll` (`EveryCharacter.lean:16`): `Green → VWin → Hyps → EveryCharacter`, via `imprimitive`. -/
theorem everyCharacter_of_plugWin {Green VWin Hyps : Prop} (hW : PlugWin Green VWin Hyps)
    (hG : Green) (hV : VWin) (h : Hyps) : UpperTheory.EveryCharacter :=
  UpperTheory.Top.imprimitive (hW hG hV h)

end Skeleton
