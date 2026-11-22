/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proofs in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).

# Pilot: general-purpose lemmas extracted from the Alpöge–Claude RH formalization

Each file below is a self-contained, Mathlib-only extraction of one source file of the
formalization (the original file:line is recorded in the file header). See `../REPORT.md`
for the candidate table and the Mathlib-availability audit.
-/
import RhLemmas.Analysis.InnerProductSpace.CompactSelfAdjoint
import RhLemmas.Analysis.Matrix.Deriv
import RhLemmas.Analysis.Matrix.PosDef.Det
import RhLemmas.Analysis.Matrix.PosDef.Open
import RhLemmas.Analysis.SpecialFunctions.BernsteinIntegral
import RhLemmas.Analysis.SpecialFunctions.Complex.ExpFiber
import RhLemmas.Analysis.SpecialFunctions.Tent
import RhLemmas.Geometry.Convex.Cone.DualFinite
import RhLemmas.LinearAlgebra.Matrix.Det
import RhLemmas.LinearAlgebra.Matrix.LDU
import RhLemmas.LinearAlgebra.Matrix.Similarity
import RhLemmas.RingTheory.RegularLocalRing.Domain
import RhLemmas.Topology.Algebra.InfiniteSum.Fiberwise
