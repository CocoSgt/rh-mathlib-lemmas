/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

Integral of the Bernstein basis polynomials: `∫ t in (0..1), t ^ i * (1 - t) ^ j = i! j! / (i + j + 1)!`
(the Beta integral at natural numbers), proved directly by integration by parts, and the
corollary that every Bernstein basis polynomial of degree `D` has integral `1 / (D + 1)`.

Original location (file:line, in `source/src`):
`ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean`
  :78 `betaNatInt`, :80 `bI_zero`, :90 `bI_succ`, :117 `bI_closed`, :140 `integral_bernstein`.
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set Polynomial

/-- `∫ t in (0..1), t ^ i * (1 - t) ^ j` for natural numbers `i`, `j` (an elementary
version of the Beta integral). -/
noncomputable def Real.betaNatInt (i j : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ i * (1 - t) ^ j

theorem Real.betaNatInt_zero (j : ℕ) : ((j : ℝ) + 1) * Real.betaNatInt 0 j = 1 := by
  unfold Real.betaNatInt
  simp only [pow_zero, one_mul]
  have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ j) (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  rw [h, integral_pow]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  simp
  field_simp

theorem Real.betaNatInt_succ (i j : ℕ) :
    ((j : ℝ) + 1) * Real.betaNatInt (i + 1) j = ((i : ℝ) + 1) * Real.betaNatInt i (j + 1) := by
  unfold Real.betaNatInt
  have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ (i + 1)) (((i : ℝ) + 1) * x ^ i) x := by
    intro x _
    simpa using hasDerivAt_pow (i + 1) x
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => -(1 - x) ^ (j + 1)) (((j : ℝ) + 1) * (1 - x) ^ j) x := by
    intro x _
    have h2 := (((hasDerivAt_id x).const_sub 1).pow (j + 1)).neg
    refine h2.congr_deriv ?_
    simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have e1 : ∫ x in (0 : ℝ)..1, ((j : ℝ) + 1) * (x ^ (i + 1) * (1 - x) ^ j) =
      ∫ x in (0 : ℝ)..1, x ^ (i + 1) * (((j : ℝ) + 1) * (1 - x) ^ j) := by
    congr 1; funext x; ring
  have e2 : ∫ x in (0 : ℝ)..1, ((i : ℝ) + 1) * (x ^ i * (1 - x) ^ (j + 1)) =
      -∫ x in (0 : ℝ)..1, ((i : ℝ) + 1) * x ^ i * (-(1 - x) ^ (j + 1)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, e1, e2, hparts]
  simp

/-- The Beta integral at natural arguments: `∫ t in (0..1), t ^ i * (1 - t) ^ j = i! j! / (i + j + 1)!`. -/
theorem Real.betaNatInt_eq_inv_mul_choose (i j : ℕ) :
    ((i : ℝ) + j + 1) * ((i + j).choose i : ℝ) * Real.betaNatInt i j = 1 := by
  induction i generalizing j with
  | zero => simpa using Real.betaNatInt_zero j
  | succ i ih =>
    have h1 := Real.betaNatInt_succ i j
    have h2 := ih (j + 1)
    have e3 : i + (j + 1) = i + j + 1 := by omega
    rw [e3] at h2
    push_cast at h2
    have h3 : ((i + j + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) =
        ((i + j + 1).choose i : ℝ) * ((j : ℝ) + 1) := by
      have := Nat.choose_succ_right_eq (i + j + 1) i
      have e : i + j + 1 - i = j + 1 := by omega
      rw [e] at this
      exact_mod_cast this
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have e2 : i + 1 + j = i + j + 1 := by omega
    rw [e2]
    push_cast
    apply mul_right_cancel₀ hj
    linear_combination ((i : ℝ) + j + 2) * ((i + j + 1).choose (i + 1) : ℝ) * h1 +
      ((i : ℝ) + j + 2) * Real.betaNatInt i (j + 1) * h3 + ((j : ℝ) + 1) * h2

/-- Every Bernstein basis polynomial of degree `D` integrates to `1 / (D + 1)` on `[0, 1]`. -/
theorem Real.integral_bernsteinPolynomial (D i : ℕ) (hi : i ≤ D) :
    ∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ D i).eval t = 1 / (D + 1 : ℝ) := by
  have h := Real.betaNatInt_eq_inv_mul_choose i (D - i)
  have e : i + (D - i) = D := by omega
  rw [e] at h
  have hcast : ((i : ℝ) + ((D - i : ℕ) : ℝ) + 1) = (D : ℝ) + 1 := by
    rw [Nat.cast_sub hi]; ring
  rw [hcast] at h
  unfold Real.betaNatInt at h
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_natCast,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_sub]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, eq_div_iff hD]
  linear_combination h
