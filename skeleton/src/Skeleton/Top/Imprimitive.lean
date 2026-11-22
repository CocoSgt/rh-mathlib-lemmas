/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# `ZeroFreeAll → EveryCharacter`: from primitive characters to all characters

An arbitrary `χ` is `changeLevel` of its primitive model, and
`L(χ, s) = L(χ.primitiveCharacter, s) · ∏_{p ∣ N / conductor} (1 - χ'(p) p^(-s))`
(`DirichletCharacter.LFunction_changeLevel`); the Euler factors do not vanish for
`0 < re s`, so a zero-free half plane for primitive `L`-functions gives one for all.

Dependencies: Mathlib only, plus `Skeleton.ZeroFreeAll` / `Skeleton.PChar`
(`Skeleton/Top/ZeroFreeAll.lean`) and `Skeleton.EveryCharacter` (`Skeleton/Top/EveryCharacter.lean`).

Original location (file:line, in `source/src`):
`Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean` :5 `UpperTheory.Top.imprimitive`.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Skeleton.Top.EveryCharacter
import Skeleton.Top.ZeroFreeAll

namespace Skeleton

/-- If every primitive Dirichlet `L`-function is nonvanishing on `re s > 1/2`, then so is
every Dirichlet `L`-function. Original: `UpperTheory.Top.imprimitive`, `Imprimitive.lean:5`. -/
theorem imprimitive (h : ZeroFreeAll) : EveryCharacter := by
  intro N _ χ s hs hχs
  haveI : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  intro h0
  have key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
  have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
  have hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by simpa using h2
  rw [key, norm_one] at hn
  exact lt_irrefl _ hn

end Skeleton
