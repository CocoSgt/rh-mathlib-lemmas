/-
Axiom audit for every declaration of `Skeleton/Top` (run `lake env lean src/Skeleton/Top/Axioms.lean`;
the output is collected in `axioms.txt` next to this file).  This file is not imported by
anything.  Expected: each line reads `'…' does not depend on any axioms` or
`'…' depends on axioms: [propext, Classical.choice, Quot.sound]`; in particular no
`sorryAx`.
-/
import Skeleton.Top

-- Statements.lean
#print axioms Skeleton.RiemannZetaZerosOnLine
#print axioms Skeleton.DirichletLNonvanishingRightOfHalf
#print axioms Skeleton.DirichletLZerosOnLine
#print axioms Skeleton.PrimitiveDirichletLZerosOnLine

-- EveryCharacter.lean
#print axioms Skeleton.EveryCharacter
#print axioms Skeleton.everyCharacter_iff

-- HalfPlane.lean
#print axioms Skeleton.Claim.HalfPlane
#print axioms Skeleton.Claim.Strip
#print axioms Skeleton.Claim.Zeta
#print axioms Skeleton.Claim.halfPlane_iff
#print axioms Skeleton.Claim.strip_iff
#print axioms Skeleton.Claim.zeta_iff_statements

-- ZeroFreeAll.lean
#print axioms Skeleton.PChar.one
#print axioms Skeleton.PChar.inv
#print axioms Skeleton.PChar.of
#print axioms Skeleton.PChar.inv_inv
#print axioms Skeleton.ZeroFreeAll
#print axioms Skeleton.PChar.of_self
#print axioms Skeleton.PChar.of_one
#print axioms Skeleton.PChar.of_inv
#print axioms Skeleton.zeroFreeAll_iff

-- RhOfRight.lean
#print axioms Skeleton.rh_of_right

-- CritLine.lean
#print axioms Skeleton.gammaFactor_ne_zero
#print axioms Skeleton.critLine
#print axioms Skeleton.rh_of_every

-- ClaimStrip.lean
#print axioms Skeleton.Claim.factor_ne_zero
#print axioms Skeleton.Claim.prim_zero
#print axioms Skeleton.Claim.gamma_ne_zero
#print axioms Skeleton.Claim.prim_reflect
#print axioms Skeleton.Claim.strip
#print axioms Skeleton.Claim.zeta
#print axioms Skeleton.Claim.zeta_iff

-- RiemannHypothesisOfEveryCharacter.lean
#print axioms Skeleton.zeta_ne_zero_of_everyCharacter
#print axioms Skeleton.riemannHypothesis_of_everyCharacter

-- Imprimitive.lean
#print axioms Skeleton.imprimitive

-- PlugWin.lean
#print axioms Skeleton.PlugWin
#print axioms Skeleton.everyCharacter_of_plugWin

-- MainTheorems.lean
#print axioms Skeleton.rhOfAll
#print axioms Skeleton.critAll
#print axioms Skeleton.claimAll
#print axioms Skeleton.riemannHypothesis
#print axioms Skeleton.riemannZeta_eq_zero_re
#print axioms Skeleton.LFunction_ne_zero_of_half_lt_re
#print axioms Skeleton.LFunction_eq_zero_re
#print axioms Skeleton.LFunction_eq_zero_re_of_isPrimitive
#print axioms Skeleton.riemannHypothesis_of_plugWin
#print axioms Skeleton.mainOfPlugWin
