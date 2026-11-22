/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original statement in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Abstracted into the "main-line skeleton" (skeleton/); all mathematical credit belongs to
Levent Alpöge and Claude.

# The one link of the main line that cannot be reproduced from Mathlib alone:
`Green + VWin + Hyps → ZeroFreeAll`

The original theorem is

```
theorem UpperTheory.Top.plugWin (hG : GlobalTheory.GLq.Green) (hV : UpperTheory.Top.VWin)
    (h : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)) : Formalism.HC.ZeroFreeAll
```
(`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8`), proved in one line as
`zeroFreeAll_of_topG (la := 3/2) (shape_of _ _ _ _ (shapeWin hG) trivial trivial h)
(fun ψ => supplyChi ψ (hV ψ))`, and `plugAll : Green → VWin → Hyps → EveryCharacter` (`:16`)
is `imprimitive (plugWin …)`.

Its three hypotheses and all intermediate statements are defined deep inside the project's
own formalism (see `SKELETON-top.md` for the full list of definitions and their depth):
* `GlobalTheory.GLq.Green` — `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`
* `UpperTheory.Top.VWin` — `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`
* `Hyps`, `DRS`, `Closed`, `LinkN` — `Definitions/GlobalTwisting/APerTw.lean:23`, `…/DRS.lean:21`,
  `Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159`, `…/GlobalTheoremInputs.lean:45`
* `TopG` — `CharacterBoxes/ZeroFreeAllOfTopG.lean:12`; `TopShape` — `…/GlobalTwisting/TopShape.lean:17`.

None of these can be unfolded into Mathlib definitions, so here the three inputs are kept as
*opaque propositions* `Green VWin Hyps : Prop` and the link is stated as `PlugWin`.  With the
original development available, `Skeleton.PlugWin Green VWin Hyps` is proved by
`fun hG hV h => UpperTheory.Top.plugWin hG hV h`.  Everything *after* this link is Mathlib-only
and is proved in this directory: `PlugWin → EveryCharacter → RiemannHypothesis` (and the four
statements of `Statements.lean`), see `Skeleton/Top/MainTheorems.lean`.
-/
import Skeleton.Top.Imprimitive

namespace Skeleton

/-- The link `UpperTheory.Top.plugWin` (`EveryCharacter.lean:8`) with its three inputs
`Green`, `VWin`, `Hyps` (the last one being `Nonempty (Hyps … DRS)`) as opaque propositions:
they imply `ZeroFreeAll`. -/
def PlugWin (Green VWin Hyps : Prop) : Prop := Green → VWin → Hyps → ZeroFreeAll

/-- Original: `UpperTheory.Top.plugAll`, `EveryCharacter.lean:16`:
`Green → VWin → Hyps → EveryCharacter`, via `imprimitive`. -/
theorem everyCharacter_of_plugWin {Green VWin Hyps : Prop} (hW : PlugWin Green VWin Hyps)
    (hG : Green) (hV : VWin) (h : Hyps) : EveryCharacter :=
  imprimitive (hW hG hV h)

end Skeleton
