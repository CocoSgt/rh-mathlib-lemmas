/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

# Positive definiteness is an open condition along a continuous family

`Matrix.PosDef.eventually`: if `A : X → Matrix (Fin m) (Fin m) ℂ` has continuous entries,
`A x` is Hermitian for all `x`, and `A x₀` is positive definite, then `A x` is positive
definite for all `x` near `x₀`. (Equivalently, `PosDef` is open in the space of Hermitian
matrices.)

Original location (file:line, in `source/src`):
`Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean` :7 `quadForm_real_smul` (private),
:15 `re_quad_pos` (private), :20 `posDef_of_re` (private), :25 `goal1` (the theorem).
-/
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open Filter Topology

open scoped ComplexOrder

private theorem quadForm_real_smul {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (r : ℝ) :
    star ((r : ℂ) • v) ⬝ᵥ (M.mulVec ((r : ℂ) • v)) = ((r ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ M.mulVec v) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

private theorem re_quad_pos {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) {y : Fin m → ℂ}
    (hy : y ≠ 0) : 0 < (star y ⬝ᵥ M.mulVec y).re :=
  (Complex.pos_iff.mp (h.dotProduct_mulVec_pos hy)).1

private theorem posDef_of_re {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hH : M.IsHermitian)
    (h : ∀ v : Fin m → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ M.mulVec v).re) : M.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv =>
    Complex.pos_iff.mpr ⟨h v hv, (hH.im_star_dotProduct_mulVec_self v).symm⟩

/-- Positive definiteness is an open condition: a continuous family of Hermitian matrices that is
positive definite at `x₀` is positive definite near `x₀`. -/
theorem Matrix.PosDef.eventually {X : Type*} [TopologicalSpace X] {m : ℕ}
    (A : X → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) {x0 : X} (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  have hAc : Continuous A := continuous_pi fun i => continuous_pi fun j => hA i j
  set K : Set (Fin m → ℂ) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  have hq : Continuous fun p : X × (Fin m → ℂ) => star p.2 ⬝ᵥ (A p.1).mulVec p.2 :=
    (continuous_snd.star).dotProduct ((hAc.comp continuous_fst).matrix_mulVec continuous_snd)
  have key : ∀ᶠ x in 𝓝 x0, ∀ y ∈ K, 0 < (star y ⬝ᵥ (A x).mulVec y).re := by
    refine hKc.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp [hK] at hy
    have hpos : 0 < (star y ⬝ᵥ (A x0).mulVec y).re := re_quad_pos h0 hy0
    have hev := (continuousAt_const (x := (x0, y))).eventually_lt
      ((Complex.continuous_re.comp hq).continuousAt (x := (x0, y))) hpos
    filter_upwards [hev] with z hz using hz
  filter_upwards [key] with x hx
  refine posDef_of_re (hH x) fun v hv => ?_
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := by
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne']
  have h1 := hx _ hw
  rw [quadForm_real_smul, Complex.re_ofReal_mul] at h1
  exact pos_of_mul_pos_right h1 (by positivity)
