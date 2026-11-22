/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original definitions in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# The three "claims": half-plane nonvanishing, strip statement, and the zeta statement

`Claim.HalfPlane` is definitionally `UpperTheory.EveryCharacter` (`Skeleton/PChar.lean`);
`Claim.Strip` is definitionally `Skeleton.DirichletLZerosOnLine`; `Claim.Zeta` is definitionally
`RiemannHypothesis` and `Skeleton.RiemannZetaZerosOnLine`. The implications
`HalfPlane → Strip` and `HalfPlane → Zeta` are proved in `Skeleton/Top/ClaimStrip.lean`.

Only Mathlib concepts occur; the `*_iff` bookkeeping lemmas additionally import
`Skeleton/Top/Statements.lean`.  `Skeleton.everyCharacter_iff` (formerly in
`Skeleton/Top/EveryCharacter.lean`) records that the statement
`DirichletLNonvanishingRightOfHalf` of `source/src/Statements.lean:6` *is* `UpperTheory.EveryCharacter`.

Original location (file:line, in `source/src`):
`Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean`
  :3 `Claim.HalfPlane`, :6 `Claim.Strip`, :9 `Claim.Zeta`.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Skeleton.PChar
import Skeleton.Top.Statements

namespace Skeleton.Claim

/-- All Dirichlet `L`-functions are nonvanishing on `re s > 1/2` (away from `s = 1` for the
principal character). Original: `Claim.HalfPlane`, `CharacterBoxes/HalfPlane.lean:3`. -/
def HalfPlane : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
    DirichletCharacter.LFunction χ s ≠ 0

/-- Every zero of a Dirichlet `L`-function in the open critical strip lies on the critical
line. Original: `Claim.Strip`, `CharacterBoxes/HalfPlane.lean:6`. -/
def Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 →
    DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Every nontrivial zero of `riemannZeta` lies on the critical line.
Original: `Claim.Zeta`, `CharacterBoxes/HalfPlane.lean:9`. -/
def Zeta : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

/-- `Claim.HalfPlane` is literally `UpperTheory.EveryCharacter`
(original `CharacterBoxes/EveryCharacter.lean:13`, in `Skeleton/PChar.lean`). -/
theorem halfPlane_iff : HalfPlane ↔ UpperTheory.EveryCharacter := Iff.rfl

/-- `Skeleton.DirichletLNonvanishingRightOfHalf` (`Statements.lean:6`) is literally
`UpperTheory.EveryCharacter`. -/
theorem everyCharacter_iff : Skeleton.DirichletLNonvanishingRightOfHalf ↔ UpperTheory.EveryCharacter := Iff.rfl

/-- `Claim.Strip` is literally `Skeleton.DirichletLZerosOnLine` (`Statements.lean:10`). -/
theorem strip_iff : Strip ↔ Skeleton.DirichletLZerosOnLine := Iff.rfl

/-- `Claim.Zeta` is literally `Skeleton.RiemannZetaZerosOnLine` (`Statements.lean:3`). -/
theorem zeta_iff_statements : Zeta ↔ Skeleton.RiemannZetaZerosOnLine := Iff.rfl

end Skeleton.Claim
