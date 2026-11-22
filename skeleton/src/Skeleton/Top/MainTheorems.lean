/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Reproduced (conditional on `EveryCharacter`) in the "main-line skeleton" (skeleton/);
all mathematical credit belongs to Levent Alpöge and Claude.

# The final theorems of the development, conditional on `EveryCharacter`

In the original, `Supplements/Kernels/MainTheorems.lean` plugs the proved
`allChi : UpperTheory.EveryCharacter` into the glue lemmas and `Main.lean` states the five
final theorems.  Here `UpperTheory.EveryCharacter` is an (unproved) proposition, so the same five
theorems are proved *from* a hypothesis `allChi : UpperTheory.EveryCharacter`; together with
`Skeleton/Top/PlugWin.lean` this shows that the chain

  `Green + VWin + Hyps  ⟹[zero_free_all_of_green_v_win / plugWin, NOT reproduced]  ZeroFreeAll
   ⟹[imprimitive]  EveryCharacter
   ⟹[rh_of_every / critLine / Claim.strip / Claim.zeta]  RH, GRH(primitive), Strip, Zeta`

is Mathlib-only below that link (the link itself is `UpperTheory.Top.zero_free_all_of_green_v_win`,
`TopPlug.lean:12`, on the route `Main.lean` takes).

Original location (file:line, in `source/src`):
`Supplements/Kernels/MainTheorems.lean` :7 `allChi`, :9 `rhOfAll`, :11 `critAll`, :15 `claimAll`;
`Main.lean` :4 `riemannHypothesis`, :6 `riemannZeta_eq_zero_re`, :8 `LFunction_ne_zero_of_half_lt_re`,
:10 `LFunction_eq_zero_re`, :12 `LFunction_eq_zero_re_of_isPrimitive`.
-/
import Skeleton.Top.Statements
import Skeleton.Top.ClaimStrip
import Skeleton.Top.CritLine
import Skeleton.Top.RiemannHypothesisOfEveryCharacter
import Skeleton.Top.PlugWin

open Complex DirichletCharacter

namespace Skeleton

/-- Original: `rhOfAll`, `Supplements/Kernels/MainTheorems.lean:9`. -/
theorem rhOfAll (allChi : UpperTheory.EveryCharacter) : RiemannHypothesis := rh_of_every allChi

/-- Original: `critAll`, `Supplements/Kernels/MainTheorems.lean:11`. -/
theorem critAll (allChi : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : LFunction χ s = 0) : s.re = 1 / 2 :=
  critLine allChi N χ hχ s h0 h1 hz

/-- Original: `claimAll`, `Supplements/Kernels/MainTheorems.lean:15`. -/
theorem claimAll (allChi : UpperTheory.EveryCharacter) : Claim.HalfPlane ∧ Claim.Strip ∧ Claim.Zeta :=
  ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩

/-- Original: `Main.lean:4`. -/
theorem riemannHypothesis (allChi : UpperTheory.EveryCharacter) : RiemannHypothesis := rhOfAll allChi

/-- Original: `Main.lean:6`. -/
theorem riemannZeta_eq_zero_re (allChi : UpperTheory.EveryCharacter) : RiemannZetaZerosOnLine := rhOfAll allChi

/-- Original: `Main.lean:8`. -/
theorem LFunction_ne_zero_of_half_lt_re (allChi : UpperTheory.EveryCharacter) :
    DirichletLNonvanishingRightOfHalf := allChi

/-- Original: `Main.lean:10`. -/
theorem LFunction_eq_zero_re (allChi : UpperTheory.EveryCharacter) : DirichletLZerosOnLine :=
  (claimAll allChi).2.1

/-- Original: `Main.lean:12`. -/
theorem LFunction_eq_zero_re_of_isPrimitive (allChi : UpperTheory.EveryCharacter) :
    PrimitiveDirichletLZerosOnLine := critAll allChi

/-- The whole main line below the `Green + VWin + Hyps → ZeroFreeAll` link: `Green + VWin + Hyps`
imply the Riemann Hypothesis once `PlugWin Green VWin Hyps` is available (in the original development
this is `Main.lean:4` applied to `UpperTheory.FinalTheorems.everyCharacter`, whose proof runs through
`every_character_of_green_v_win` for the proved `Green`, `VWin`, `Nonempty (HypsAlt … DefiniteSideCondition)`). -/
theorem riemannHypothesis_of_plugWin {Green VWin Hyps : Prop} (hW : PlugWin Green VWin Hyps)
    (hG : Green) (hV : VWin) (h : Hyps) : RiemannHypothesis :=
  rhOfAll (everyCharacter_of_plugWin hW hG hV h)

/-- Likewise for the four statements of `Statements.lean`. -/
theorem mainOfPlugWin {Green VWin Hyps : Prop} (hW : PlugWin Green VWin Hyps) (hG : Green)
    (hV : VWin) (h : Hyps) :
    RiemannZetaZerosOnLine ∧ DirichletLNonvanishingRightOfHalf ∧ DirichletLZerosOnLine ∧
      PrimitiveDirichletLZerosOnLine ∧ RiemannHypothesis := by
  have allChi := everyCharacter_of_plugWin hW hG hV h
  exact ⟨riemannZeta_eq_zero_re allChi, LFunction_ne_zero_of_half_lt_re allChi,
    LFunction_eq_zero_re allChi, LFunction_eq_zero_re_of_isPrimitive allChi, riemannHypothesis allChi⟩

end Skeleton
