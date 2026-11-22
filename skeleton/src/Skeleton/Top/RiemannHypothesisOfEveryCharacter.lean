/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# A second, shorter route from `EveryCharacter` to the Riemann Hypothesis

Using Mathlib's functional equation `completedRiemannZeta_one_sub` directly (instead of the
unfolded form `riemannZeta_one_sub` used in `Skeleton.rh_of_right`).

In the original file this proof sits under 209 internal imports that it does not use; the
only dependencies are Mathlib and `UpperTheory.EveryCharacter` (`Skeleton/PChar.lean`).

Original location (file:line, in `source/src`):
`Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean`
  :211 `UpperTheory.zeta_ne_zero_of_everyCharacter`, :215 `UpperTheory.riemannHypothesis_of_everyCharacter`.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Skeleton.PChar

open Complex

namespace Skeleton

/-- Original: `UpperTheory.zeta_ne_zero_of_everyCharacter`, `RiemannHypothesisOfEveryCharacter.lean:211`. -/
theorem zeta_ne_zero_of_everyCharacter (h : UpperTheory.EveryCharacter) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := fun s hs h1 => by
  have := h 1 1 s hs (Or.inr h1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- `EveryCharacter` implies the Riemann Hypothesis (second proof).
Original: `UpperTheory.riemannHypothesis_of_everyCharacter`,
`RiemannHypothesisOfEveryCharacter.lean:215`. -/
theorem riemannHypothesis_of_everyCharacter (h : UpperTheory.EveryCharacter) : RiemannHypothesis := by
  intro s hs hn h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
    have h1s : (1 - s) ≠ 1 := fun e => hs0 (by simpa using e)
    have hz : riemannZeta (1 - s) ≠ 0 := zeta_ne_zero_of_everyCharacter h (1 - s) (by simp; linarith) h1s
    have hc : completedRiemannZeta s = completedRiemannZeta (1 - s) := (completedRiemannZeta_one_sub s).symm
    have h1s0 : (1 - s) ≠ 0 := fun e => h1 (by linear_combination -e)
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · exact hz (by rw [riemannZeta_def_of_ne_zero h1s0, ← hc, hs, zero_div])
    · obtain ⟨n, hn'⟩ := Complex.Gammaℝ_eq_zero_iff.1 hs
      rcases n with _ | n
      · exact hs0 (by simpa using hn')
      · exact hn ⟨n, by rw [hn']; push_cast; ring⟩
  · exact zeta_ne_zero_of_everyCharacter h s hgt h1 hs

end Skeleton
