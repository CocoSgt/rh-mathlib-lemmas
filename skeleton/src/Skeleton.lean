/-
Copyright (c) 2026 Levent Alpöge (with Claude). Everything in this library is copied from the
Alpöge–Claude Lean formalization of the Riemann Hypothesis (released 2026-11-20 at
https://alpo.ge/ ; mirror https://github.com/CocoSgt/riemann-hypothesis-lean ). All mathematical
credit belongs to Levent Alpöge and Claude. Extraction, cleaning and compilation checks were done
by GLM 5.4 via DeepSeek Harness. The source release carries no license file (REPORT.md §5.6).

# Main-line skeleton of the Riemann Hypothesis proof

Every module of this library depends on Mathlib only (pinned at the same commit as `source/`).
See `SKELETON.md` at the repository root.

* `Skeleton.PChar` — the shared bottom (original namespaces): `PChar`, `ZeroFreeAll`,
  `EveryCharacter`, and the proved link `imprimitive : ZeroFreeAll → EveryCharacter`.
* `Skeleton.Layers` — the five layers as one entry point (`Layer1` … `Layer5`) and the links
  between them that are proved here.
* `Skeleton.Top.*` — the four statements of `Statements.lean`, `Claim.*`, and the proved links
  `EveryCharacter → RiemannHypothesis` (twice) and `EveryCharacter → GRH` (`critLine`),
  `HalfPlane → Strip/Zeta`; `PlugWin` (the one link that is not reproduced, with opaque inputs);
  `Main.lean` conditional on `EveryCharacter` (namespace `Skeleton`).
* `Skeleton.Window.*`, `Skeleton.Galois.*` — the *full* statements of `UpperTheory.Top.VWin` and
  `GlobalTheory.GLq.Green` with their definition cones, and the assemblies of the lower links
  (`plugWinStatement`, `vwin_of_row`, `everyCharacter_of_row`) with the deep theorems as hypotheses.
-/
import Skeleton.PChar
import Skeleton.Top
import Skeleton.Window.VWin
import Skeleton.Window.Green
import Skeleton.Window.PlugAll
import Skeleton.Galois.Places
import Skeleton.Galois.GaloisCohomology
import Skeleton.Galois.Row0b
import Skeleton.Galois.IsRecT
import Skeleton.Galois.Mainline
import Skeleton.Layers
