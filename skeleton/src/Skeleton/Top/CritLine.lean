/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# From `EveryCharacter` to the Riemann Hypothesis and to GRH for primitive characters

* `gammaFactor_ne_zero`: `DirichletCharacter.gammaFactor χ s ≠ 0` for `0 < re s`.
* `critLine`: if all Dirichlet `L`-functions are nonvanishing on `re s > 1/2`, then every
  zero of a *primitive* `L`-function in the open strip has `re s = 1/2` (reflect with the
  functional equation `completedLFunction_one_sub` when `re s < 1/2`).
* `rh_of_every`: `EveryCharacter → RiemannHypothesis` (take the level-`1` character, for which
  `LFunction = riemannZeta`, and apply `Skeleton.rh_of_right`).

Dependencies: Mathlib only, plus `Skeleton.rh_of_right` (`Skeleton/Top/RhOfRight.lean`).

Original location (file:line, in `source/src`):
`Formalism/GammaFactorNonvanishing/CritLine.lean`
  :6 `Formalism.VW.gammaFactor_ne_zero`, :11 `Formalism.VW.critLine`, :29 `Formalism.VW.rh_of_every`.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Skeleton.Top.EveryCharacter
import Skeleton.Top.RhOfRight

open Complex DirichletCharacter

namespace Skeleton

/-- Original: `Formalism.VW.gammaFactor_ne_zero`, `CritLine.lean:6`. -/
theorem gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

/-- If every Dirichlet `L`-function is nonvanishing on `re s > 1/2`, then every zero of a
primitive `L`-function in the open critical strip lies on the critical line (GRH for
Dirichlet `L`-functions, zeros version).
Original: `Formalism.VW.critLine`, `CritLine.lean:11`. -/
theorem critLine (h : EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) :
    s.re = 1 / 2 := by
  have hs0 : s ≠ 0 := fun e => by simp [e] at h0
  have hs1 : s ≠ 1 := fun e => by simp [e] at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : χ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ
    have hc : completedLFunction χ s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)] at hz
      exact (div_eq_zero_iff.1 hz).resolve_right (gammaFactor_ne_zero χ h0)
    have hfe := hinv.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    have h2 : (1 - s) ≠ 0 := sub_ne_zero.2 hs1.symm
    refine h N χ⁻¹ (1 - s) (by rw [sub_re, one_re]; linarith) (Or.inr fun e => hs0 (by linear_combination -e)) ?_
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h2), hfe, zero_div]
  · exact h N χ s hgt (Or.inr hs1) hz

/-- Every Dirichlet `L`-function nonvanishing on `re s > 1/2` implies the Riemann
Hypothesis. Original: `Formalism.VW.rh_of_every`, `CritLine.lean:29`. -/
theorem rh_of_every (h : EveryCharacter) : RiemannHypothesis :=
  rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this

end Skeleton
