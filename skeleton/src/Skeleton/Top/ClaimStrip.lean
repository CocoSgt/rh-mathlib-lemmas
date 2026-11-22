/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# From half-plane nonvanishing to the "strip" and "zeta" claims

* `factor_ne_zero`: `1 - ψ p p^(-s) ≠ 0` for `0 < re s` and a prime `p` (Euler factors never vanish).
* `prim_zero`: a zero of `L(χ, s)` in the open strip is a zero of the primitive model.
* `prim_reflect`: via the functional equation, a strip-zero `s` of a primitive `L`-function
  gives the strip-zero `1 - s` of the inverse character.
* `strip`: `HalfPlane → Strip`: for `re s < 1/2` reflect, for `re s > 1/2` there is no zero.
* `zeta`: `HalfPlane → Zeta`: the level-`1` case of `strip`; `re s ≤ 0` is excluded by the
  functional equation `completedRiemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re`.

Dependencies: Mathlib only (`DirichletCharacter.LFunction_changeLevel`,
`completedLFunction_one_sub`, `riemannZeta_def_of_ne_zero`, …).

Original location (file:line, in `source/src`):
`Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`
  :7 `factor_ne_zero`, :23 `prim_zero`, :35 `gamma_ne_zero`, :42 `prim_reflect`,
  :59 `strip`, :75 `zeta`, :102 `zeta_iff`.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Skeleton.Top.HalfPlane

open Complex

namespace Skeleton.Claim

/-- Original: `Claim.factor_ne_zero`, `ClaimStrip.lean:7`. -/
theorem factor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) (p : ℕ)
    (hp : p.Prime) : (1 : ℂ) - ψ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : ψ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hn : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by
          gcongr; exact ψ.norm_le_one _
      _ < 1 := by rw [one_mul]; exact hpow
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/-- Original: `Claim.prim_zero`, `ClaimStrip.lean:23`. -/
theorem prim_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have key := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter, h] at key
  rcases mul_eq_zero.mp key.symm with h' | h'
  · exact h'
  · obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp h'
    exact absurd hp0 (factor_ne_zero _ hs0 p (Nat.prime_of_mem_primeFactors hp))

/-- Original: `Claim.gamma_ne_zero`, `ClaimStrip.lean:35`. -/
theorem gamma_ne_zero {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) {t : ℂ} (ht : 0 < t.re) :
    DirichletCharacter.gammaFactor φ t ≠ 0 := by
  rcases φ.even_or_odd with hφ | hφ
  · rw [hφ.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos ht
  · rw [hφ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

/-- Original: `Claim.prim_reflect`, `ClaimStrip.lean:42`. -/
theorem prim_reflect {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (h : DirichletCharacter.LFunction ψ s = 0) :
    DirichletCharacter.LFunction ψ⁻¹ (1 - s) = 0 := by
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  have ht0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have ht0' : 1 - s ≠ 0 := fun e => by rw [e, Complex.zero_re] at ht0; exact lt_irrefl _ ht0
  have hc : DirichletCharacter.completedLFunction ψ s = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ s (Or.inl hs0'),
      div_eq_zero_iff] at h
    exact h.resolve_right (gamma_ne_zero ψ hs0)
  have hψ' : (ψ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hψ
  have fe := hψ'.completedLFunction_one_sub s
  rw [inv_inv, hc, mul_zero] at fe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor ψ⁻¹ (1 - s) (Or.inl ht0'), fe,
    zero_div]

/-- Half-plane nonvanishing implies the critical-line statement for all Dirichlet
`L`-functions. Original: `Claim.strip`, `ClaimStrip.lean:59`. -/
theorem strip (h : HalfPlane) : Strip := by
  unfold HalfPlane at h
  intro N _ χ s hs0 hs1 hz
  have hs : s ≠ 1 := fun e => by rw [e, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hs0' : s ≠ 0 := fun e => by rw [e, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := prim_zero χ hs0 hs1 hz
    have hr := prim_reflect χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hs0 hs1 hp
    have ht : (1 : ℂ) - s ≠ 1 := fun e => hs0' (sub_eq_self.mp e)
    exact h χ.conductor χ.primitiveCharacter⁻¹ (1 - s)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (Or.inr ht) hr
  · exact heq
  · exact absurd hz (h N χ s hgt (Or.inr hs))

/-- Half-plane nonvanishing for all Dirichlet `L`-functions implies the Riemann Hypothesis
in its "all nontrivial zeros on the critical line" form.
Original: `Claim.zeta`, `ClaimStrip.lean:75`. -/
theorem zeta (h : HalfPlane) : Zeta := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
  rcases lt_or_ge 0 s.re with hpos | hnpos
  · rcases lt_or_ge s.re 1 with hlt1 | hge1
    · have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
        rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
      exact strip h 1 1 s hpos hlt1 hL
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
  · exfalso
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have := congrArg Complex.re e
      rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'

/-- Original: `Claim.zeta_iff`, `ClaimStrip.lean:102`: the "zeta claim" is literally
Mathlib's `RiemannHypothesis`. -/
theorem zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl

end Skeleton.Claim
