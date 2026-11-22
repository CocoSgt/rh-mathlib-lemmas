/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original statements in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# The four top-level statements

Verbatim copies (same names, now in namespace `Skeleton`) of the four propositions in
`source/src/Statements.lean:3-16`. They are the targets of the five theorems of
`source/src/Main.lean`; see `Skeleton/Top/MainTheorems.lean` for the conditional versions
"EveryCharacter → each statement".

Only Mathlib concepts occur: `riemannZeta`, `DirichletCharacter.LFunction`,
`DirichletCharacter.IsPrimitive`.

Original location (file:line, in `source/src`):
`Statements.lean` :3 `RiemannZetaZerosOnLine`, :6 `DirichletLNonvanishingRightOfHalf`,
:10 `DirichletLZerosOnLine`, :14 `PrimitiveDirichletLZerosOnLine`.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace Skeleton

/-- All nontrivial zeros of the Riemann zeta function lie on the critical line:
`riemannZeta s = 0` with `s ≠ 1` and `s` not a trivial zero `-2(n+1)` forces `re s = 1/2`.
Original: `RiemannZetaZerosOnLine`, `Statements.lean:3`. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- No Dirichlet `L`-function (any level, any character) vanishes in the open right
half plane `re s > 1/2`, except at the pole `s = 1` of the principal character.
Original: `DirichletLNonvanishingRightOfHalf`, `Statements.lean:6` (this is literally
`Skeleton.EveryCharacter`, see `Skeleton.everyCharacter_iff`). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- All zeros of all Dirichlet `L`-functions inside the critical strip lie on the
critical line. Original: `DirichletLZerosOnLine`, `Statements.lean:10`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- All zeros of primitive Dirichlet `L`-functions inside the critical strip lie on
the critical line (the usual GRH for Dirichlet `L`-functions).
Original: `PrimitiveDirichletLZerosOnLine`, `Statements.lean:14`. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

end Skeleton
