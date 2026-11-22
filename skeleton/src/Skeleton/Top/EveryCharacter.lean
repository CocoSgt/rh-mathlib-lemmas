/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original definition in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# `EveryCharacter`: the top analytic input of the main line

The proposition that no Dirichlet `L`-function vanishes in the open right half plane
`re s > 1/2` (away from the pole `s = 1` of the principal character). In the original
development this is the *last* layer before the Riemann Hypothesis: `Formalism.VW.rh_of_every`
(`Skeleton/Top/CritLine.lean`) derives RH from it, and it is itself derived from
`Green + VWin + Hyps` via `plugWin`/`imprimitive` (`Skeleton/Top/PlugWin.lean`).

Only Mathlib concepts occur (`DirichletCharacter.LFunction`); the lemma `everyCharacter_iff`
additionally imports `Skeleton/Top/Statements.lean`.

Original location (file:line, in `source/src`):
`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`
  :13 `UpperTheory.EveryCharacter` (this file),
  :8 `UpperTheory.Top.plugWin`, :16 `UpperTheory.Top.plugAll` (→ `Skeleton/Top/PlugWin.lean`).
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Skeleton.Top.Statements

namespace Skeleton

/-- Every Dirichlet `L`-function (any level `N ≠ 0`, any character `χ`) is nonvanishing on
`re s > 1/2`, except possibly at the pole `s = 1` when `χ` is principal.
Original: `UpperTheory.EveryCharacter`, `CharacterBoxes/EveryCharacter.lean:13`. -/
def EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
    DirichletCharacter.LFunction χ s ≠ 0

/-- `EveryCharacter` is literally the statement `DirichletLNonvanishingRightOfHalf` of
`source/src/Statements.lean:6`. -/
theorem everyCharacter_iff : DirichletLNonvanishingRightOfHalf ↔ EveryCharacter := Iff.rfl

end Skeleton
