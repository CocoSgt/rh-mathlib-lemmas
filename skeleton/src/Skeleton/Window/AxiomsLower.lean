/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton: `#print axioms` for every definition and theorem of
`skeleton/src/Skeleton/{Galois,Window}/*.lean` (except this file).  The table produced on
2026-11-23 00:49 CST is in SKELETON-lower.md §6: 42 declarations, all with at most
`propext, Classical.choice, Quot.sound`, no `sorryAx`.
-/
import Skeleton.Galois.Places
import Skeleton.Galois.GaloisCohomology
import Skeleton.Galois.Row0b
import Skeleton.Galois.IsRecT
import Skeleton.Galois.Mainline
import Skeleton.Window.PChar
import Skeleton.Window.VWin
import Skeleton.Window.Green
import Skeleton.Window.PlugAll

-- propositions (defs)
#print axioms Formalism.HC.PChar
#print axioms Formalism.HC.ZeroFreeAll
#print axioms UpperTheory.EveryCharacter
#print axioms UpperTheory.Top.VWin
#print axioms GlobalTheory.GLq.Green
#print axioms UpperTheory.Top.plugWinStatement
#print axioms UpperTheory.Zero.LLC.RecTExistsSchematic
#print axioms UpperTheory.GalStar.IsQpBig
#print axioms UpperTheory.LiteratureTheorems.OpenImageCondition
#print axioms UpperTheory.LiteratureTheorems.OpenLiteratureStatements

-- theorems: Window/PChar.lean
#print axioms Formalism.HC.PChar.inv_inv
#print axioms Formalism.HC.PChar.of_self
#print axioms Formalism.HC.PChar.of_one
#print axioms Formalism.HC.PChar.of_inv
#print axioms Formalism.HC.zeroFreeOn_of_levels
#print axioms Formalism.HC.Level.mem_ofSub
#print axioms Formalism.HC.Level.mem_cyc
#print axioms Formalism.HC.zeroFreeOn_of_cyc
#print axioms UpperTheory.Top.imprimitive
-- Galois/Places.lean
#print axioms ReciprocityTheory.Gal.mem_Dec
#print axioms ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec
#print axioms ReciprocityTheory.Gal.valuation_lt_one_iff'
#print axioms ReciprocityTheory.Gal.valuation_apply_lt_one_iff
#print axioms ReciprocityTheory.Gal.mul_inv_apply
#print axioms ReciprocityTheory.Gal.mem_Ine
#print axioms ReciprocityTheory.Gal.Ine_le_Dec
#print axioms ReciprocityTheory.Gal.normal_NS
#print axioms ReciprocityTheory.Gal.isClosed_NS
#print axioms ReciprocityTheory.Gal.continuous_toGS
#print axioms ReciprocityTheory.Gal.continuous_locHom
-- Galois/GaloisCohomology.lean
#print axioms ReciprocityTheory.Gal.mem_coboundaries1
#print axioms ReciprocityTheory.Gal.continuous_locFam
#print axioms Formalism.GaloisCohomology.scalRep_apply
#print axioms GlobalTheory.GLq.hcL_cons
#print axioms GlobalTheory.GLq.hcL_nil
-- Galois/Row0b.lean
#print axioms UpperTheory.GalStar.IsQpBig.isQp
-- Window/VWin.lean
#print axioms UpperTheory.Top.VVle.mono
#print axioms UpperTheory.Top.exists_pageN
-- Window/PlugAll.lean, Galois/Mainline.lean
#print axioms UpperTheory.Top.plugAll_of_plugWin
#print axioms UpperTheory.One.vwin_of_row_of
#print axioms UpperTheory.FinalTheorems.everyCharacter_of_row_of
#print axioms UpperTheory.FinalTheorems.everyCharacter_of_row_and_inputs
