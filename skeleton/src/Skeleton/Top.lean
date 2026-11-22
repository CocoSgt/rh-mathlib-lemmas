/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original statements and proofs in the
Alpöge–Claude Lean formalization of the Riemann Hypothesis (released 2026-11-20 at
https://alpo.ge/). Reproduced in the "main-line skeleton" (skeleton/); all mathematical
credit belongs to Levent Alpöge and Claude.

# Upper layer of the main-line skeleton

Everything in this directory depends on Mathlib only (no other part of the original
development).  See `SKELETON-top.md` at the repository root for the file-by-file table.

* `Statements`, `EveryCharacter`, `HalfPlane`, `ZeroFreeAll`: the propositions
  (`EveryCharacter`, `Claim.HalfPlane/Strip/Zeta`, `ZeroFreeAll` with `PChar`, and the
  four statements of `Statements.lean`).
* `RhOfRight`, `CritLine`, `ClaimStrip`, `RiemannHypothesisOfEveryCharacter`, `Imprimitive`:
  the proved links `EveryCharacter → RiemannHypothesis` (twice), `EveryCharacter → GRH for
  primitive characters`, `HalfPlane → Strip/Zeta`, `ZeroFreeAll → EveryCharacter`.
* `PlugWin`: the link `Green + VWin + Hyps → ZeroFreeAll`, stated with opaque inputs (the
  only link of the main line that is *not* reproduced), and `PlugWin → EveryCharacter`.
* `MainTheorems`: the five theorems of `Main.lean`, conditional on `EveryCharacter`, and
  the whole chain below `PlugWin`.
-/
import Skeleton.Top.Statements
import Skeleton.Top.EveryCharacter
import Skeleton.Top.HalfPlane
import Skeleton.Top.ZeroFreeAll
import Skeleton.Top.RhOfRight
import Skeleton.Top.CritLine
import Skeleton.Top.ClaimStrip
import Skeleton.Top.RiemannHypothesisOfEveryCharacter
import Skeleton.Top.Imprimitive
import Skeleton.Top.PlugWin
import Skeleton.Top.MainTheorems
