/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

Determinant miscellanea.

* `Matrix.det_mul_eq_sum_over_functions`: the Cauchy–Binet formula
  `det (A * B) = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * det (B.submatrix f id)`
  (functions `f` that are not injective contribute `0`).
* `LinearMap.det_mulLeft_matrix`, `LinearMap.det_mulRight_matrix`: the determinant of
  left/right multiplication by `A` on the space of `n × n` matrices is `(det A) ^ n`;
  `LinearMap.det_restrictScalars_mulLeft`: its determinant as a real operator is
  `‖det A‖ ^ 2 ^ n` for complex `A`.
* `Equiv.Perm.eq_one_of_forall_le`: a permutation `π` with `π x ≤ x` for all `x` is the identity.

Original locations (file:line, in `source/src`):
  `Lemmata/GeneralBFact/Imports.lean` :8 `Bl.general_b_fact.goal1` (Cauchy–Binet);
  `GroundTheory/AutomorphicForms/RealGroupsHaar.lean` :12 `vecLinearEquiv`, :20
  `det_mulLeft_matrix`, :33 `det_mulRight_matrix`, :256 `det_restrictScalars_mulLeft`,
  :261 `det_restrictScalars_mulRight`;
  `GroundTheory/AutomorphicForms/FiniteBruhat.lean` :83 `perm_eq_one_of_forall_le`.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.RingTheory.Complex

open Finset Matrix

open scoped Kronecker

/-- Cauchy–Binet: `det (A * B)` for `A : Fin i → Fin N`, `B : Fin N → Fin i`, as a sum over
all functions `Fin i → Fin N` (non-injective `f` give a zero `submatrix` determinant). -/
theorem Matrix.det_mul_eq_sum_over_functions {R : Type*} [CommRing R] {i N : ℕ}
    (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  classical
  have h1 : (A * B : Matrix (Fin i) (Fin i) R) = fun a => ∑ k, A a k • B k := by
    funext a j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : (A * B).det =
      (detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap
        (fun a => ∑ k, A a k • B k) := by
    rw [Matrix.det, h1]
    rfl
  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

section DetMul

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The `𝕜`-linear equivalence between `n × n` matrices and functions `n × n → 𝕜`
reading a matrix column by column. -/
private def Matrix.vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜) where
  toFun := vec
  invFun v := of fun i j => v (j, i)
  map_add' := vec_add
  map_smul' := vec_smul
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl

/-- Left multiplication by `A` on the space of `n × n` matrices has determinant `(det A) ^ #n`. -/
theorem LinearMap.det_mulLeft_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulLeft 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (Matrix.vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulLeft 𝕜 A ∘ₗ (Matrix.vecLinearEquiv (n := n)).symm.toLinearMap = toLin' (1 ⊗ₖ A) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulLeft_apply, toLin'_apply]
    show vec (A * Matrix.vecLinearEquiv.symm v) = _
    rw [vec_mul_eq_mulVec]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulLeft 𝕜 A) Matrix.vecLinearEquiv, h, LinearMap.det_toLin',
    det_kronecker, det_one, one_pow, one_mul]

/-- Right multiplication by `A` on the space of `n × n` matrices has determinant `(det A) ^ #n`. -/
theorem LinearMap.det_mulRight_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulRight 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (Matrix.vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulRight 𝕜 A ∘ₗ (Matrix.vecLinearEquiv (n := n)).symm.toLinearMap =
        toLin' (A ⊗ₖ (1 : Matrix n n 𝕜))ᵀ := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulRight_apply, toLin'_apply]
    show vec (Matrix.vecLinearEquiv.symm v * A) = _
    rw [vec_mul_eq_vecMul, mulVec_transpose]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulRight 𝕜 A) Matrix.vecLinearEquiv, h, LinearMap.det_toLin',
    det_transpose, det_kronecker, det_one, one_pow, mul_one]

/-- Left multiplication by a complex matrix, viewed as a real operator, has determinant
`‖det A‖ ^ 2 ^ n`. -/
theorem LinearMap.det_restrictScalars_mulLeft (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_mulLeft_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

/-- Right multiplication by a complex matrix, viewed as a real operator, has determinant
`‖det A‖ ^ 2 ^ n`. -/
theorem LinearMap.det_restrictScalars_mulRight (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulRight ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_mulRight_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

end DetMul

/-- A permutation of `Fin n` that does not increase any index is the identity. -/
theorem Equiv.Perm.eq_one_of_forall_le {n : ℕ} (π : Equiv.Perm (Fin n)) (h : ∀ x, π x ≤ x) :
    π = 1 := by
  have hsum : ∑ x, ((π x : Fin n) : ℕ) = ∑ x : Fin n, (x : ℕ) :=
    Equiv.sum_comp π (fun x : Fin n => (x : ℕ))
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun x _ => Fin.le_iff_val_le_val.mp (h x))).mp hsum
  exact Equiv.ext fun x => by simpa using Fin.ext (heq x (Finset.mem_univ _))
