/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

Derivative of the determinant along a differentiable path of matrices.

* `Matrix.hasDerivAt_det`: if every entry of `G : ℝ → Matrix (Fin r) (Fin r) ℂ` has
  derivative `G' i j` at `t`, then `s ↦ (G s).det` has derivative
  `Matrix.trace ((G t).adjugate * G')` at `t` (Jacobi's formula).
* `Matrix.hasDerivAt_log_det_re`: when `G t` is positive definite, `s ↦ log (re (G s).det)`
  has derivative `re (trace ((G t)⁻¹ * G'))`.

Original location (file:line, in `source/src`):
`ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean`
  :8 `trace_adjugate_mul_eq_sum_perm` (kept private), :31 `hasDerivAt_det`,
  :57 `hasDerivAt_log_det`.  (The `first | … | …` alternatives in the original proof
  were version-compatibility fallbacks; the branch that applies to this Mathlib is kept.)
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Matrix

open scoped ComplexOrder

private theorem trace_adjugate_mul_eq_sum_perm {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i := by
  have hcol : ∀ i, (A.adjugate * B) i i = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) *
      ((∏ j ∈ Finset.univ.erase i, A (σ j) j) • B (σ i) i) := by
    intro i
    have h1 : (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
      rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), smul_eq_mul, mul_comm]
    congr 1
    all_goals first
      | refine Finset.prod_congr rfl fun j hj => ?_
        simp [Finset.ne_of_mem_erase hj]
      | simp
  simp only [Matrix.trace, Matrix.diag, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]

/-- **Jacobi's formula**: the derivative of `s ↦ (G s).det` at `t` is the trace of
`(G t).adjugate * G'`, where `G' i j` is the derivative of the `(i, j)` entry. -/
theorem Matrix.hasDerivAt_det {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by
  rw [trace_adjugate_mul_eq_sum_perm]
  have hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j := by
    funext s; exact Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      HasDerivAt (fun s => (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j)
        ((Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t :=
    fun σ _ => (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _
  exact HasDerivAt.fun_sum hσ

/-- Derivative of `s ↦ log (re ((G s).det))` at a point where `G t` is positive definite:
it is `re (trace ((G t)⁻¹ * G'))`. -/
theorem Matrix.hasDerivAt_log_det_re {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hpos : (G t).PosDef) :
    HasDerivAt (fun s => Real.log (G s).det.re) ((G t)⁻¹ * G').trace.re t := by
  have hd := Matrix.hasDerivAt_det G G' t hG
  have hre : HasDerivAt (fun s => (G s).det.re) ((G t).adjugate * G').trace.re t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa [Function.comp_def] using this
  have hre0 : 0 < (G t).det.re ∧ (G t).det.im = 0 := by
    obtain ⟨h1, h2⟩ := Complex.lt_def.1 hpos.det_pos
    simpa using ⟨h1, h2.symm⟩
  have hlog := hre.log hre0.1.ne'
  convert hlog using 1
  have hdet : (G t).det = (((G t).det.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre0.2])
  rw [Matrix.inv_def, Matrix.smul_mul, Matrix.trace_smul, Ring.inverse_eq_inv', smul_eq_mul, hdet,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  simp only [Complex.ofReal_re]
  ring
