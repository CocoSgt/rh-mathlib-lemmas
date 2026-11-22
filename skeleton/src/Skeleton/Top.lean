/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original statements and proofs in the
Alpöge–Claude Lean formalization of the Riemann Hypothesis (released 2026-11-20 at
https://alpo.ge/). Reproduced in the "main-line skeleton" (skeleton/); all mathematical
credit belongs to Levent Alpöge and Claude.

# Upper layer of the main-line skeleton

Everything in this directory depends on Mathlib only (no other part of the original
development).  See `SKELETON-top.md` at the repository root for the file-by-file table.

The propositions `EveryCharacter`, `ZeroFreeAll` (with `PChar`) and the proved link
`ZeroFreeAll → EveryCharacter` (`imprimitive`) live in the shared file `Skeleton/PChar.lean`
(original namespaces), which everything here imports.

* `Statements`, `HalfPlane`: `Claim.HalfPlane/Strip/Zeta`, the four statements of `Statements.lean`,
  and the `Iff.rfl` bookkeeping (`everyCharacter_iff`, `halfPlane_iff`, …).
* `RhOfRight`, `CritLine`, `ClaimStrip`, `RiemannHypothesisOfEveryCharacter`:
  the proved links `EveryCharacter → RiemannHypothesis` (twice), `EveryCharacter → GRH for
  primitive characters`, `HalfPlane → Strip/Zeta`.
* `PlugWin`: the link `Green + VWin + Hyps → ZeroFreeAll`, stated with opaque inputs (the
  only link of the main line that is *not* reproduced), and `PlugWin → EveryCharacter`.
* `MainTheorems`: the five theorems of `Main.lean`, conditional on `EveryCharacter`, and
  the whole chain below `PlugWin`.
-/
import Skeleton.PChar
import Skeleton.Top.Statements
import Skeleton.Top.HalfPlane
import Skeleton.Top.RhOfRight
import Skeleton.Top.CritLine
import Skeleton.Top.ClaimStrip
import Skeleton.Top.RiemannHypothesisOfEveryCharacter
import Skeleton.Top.PlugWin
import Skeleton.Top.MainTheorems
