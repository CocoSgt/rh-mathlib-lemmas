/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

Determinant inequalities for positive (semi)definite complex matrices.

* Minkowski: `Matrix.PosDef.det_re_mono` — `G ≤ H` in the Loewner order implies
  `Re (det G) ≤ Re (det H)`.
* Fischer: `Matrix.PosDef.det_re_le_det_re_mul_det_re_fromBlocks` — for a positive
  definite block matrix, `Re (det M) ≤ Re (det A) * Re (det D)`.
* Hadamard: `Matrix.PosDef.det_re_le_prod_diag_re` — `Re (det D) ≤ ∏ Re D i i`.

Original location (file:line, in `source/src`):
`ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean`
  :12 `gramSt_det_one_add_eq`, :30 `gramSt_det_re_le_of_sub`, :68 `gramSt_fischer`,
  :104 `gramSt_fin_blocks`, :119 `gramSt_hadamard`, :143 `det_re_le_mul_prod_diag`.
(The file also contains two restatements of existing Mathlib lemmas, :134 :139, which
are dropped here.)
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

open Matrix

open scoped ComplexOrder MatrixOrder

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of `1 + Q` for a positive semidefinite `Q` is the product of
`1 + λ` over the eigenvalues `λ` of `Q`. -/
theorem Matrix.PosSemidef.det_one_add_eq_prod {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
  set U := hQ.isHermitian.eigenvectorUnitary with hU
  have h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U
      (1 + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) := by
    rw [map_add, map_one, ← hQ.isHermitian.spectral_theorem]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) : Matrix ι ι ℂ) =
      diagonal fun i => ((1 + hQ.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod,
    mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul, Unitary.mul_star_self_of_mem U.2, det_one,
    mul_one]

/-- **Minkowski's determinant inequality**: if `G` is positive definite and `H - G` is
positive semidefinite, then `Re (det G) ≤ Re (det H)`. -/
theorem Matrix.PosDef.det_re_mono {G H : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGH : (H - G).PosSemidef) : G.det.re ≤ H.det.re := by
  set S := CFC.sqrt G with hSdef
  have hS0 : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSh : Sᴴ = S := hS0.1
  have hdetG : G.det = S.det * S.det := by rw [← hSS, det_mul]
  have hGpos := hG.det_pos
  have hSdet : S.det ≠ 0 := fun h => by rw [hdetG, h, zero_mul] at hGpos; exact lt_irrefl _ hGpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hQ : (S⁻¹ * (H - G) * (S⁻¹)ᴴ).PosSemidef := hGH.mul_mul_conjTranspose_same _
  have hinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have h2 : S * (S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S = H - G := by
    rw [hinvh, show S * (S⁻¹ * (H - G) * S⁻¹) * S = (S * S⁻¹) * (H - G) * (S⁻¹ * S) by
      simp only [Matrix.mul_assoc]]
    rw [mul_nonsing_inv S hSu, nonsing_inv_mul S hSu, Matrix.one_mul, Matrix.mul_one]
  have hH : H = S * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hSS, h2]; abel
  have hdetH : H.det = G.det * (1 + S⁻¹ * (H - G) * (S⁻¹)ᴴ).det := by
    conv_lhs => rw [hH]
    rw [det_mul, det_mul, hdetG]; ring
  rw [hdetH, hQ.det_one_add_eq_prod]
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hGpos
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h1 : (1 : ℝ) ≤ ∏ i, (1 + hQ.isHermitian.eigenvalues i) := by
    calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
      _ ≤ ∏ i, (1 + hQ.isHermitian.eigenvalues i) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hQ.eigenvalues_nonneg i])
  nlinarith

end Spectral

section Blocks

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- **Fischer's inequality**: for a positive definite block matrix `M = [[A, B], [Bᴴ, D]]`,
`Re (det M) ≤ Re (det A) * Re (det D)`. -/
theorem Matrix.PosDef.det_re_le_det_re_mul_det_re_fromBlocks
    {A : Matrix m m ℂ} {B : Matrix m k ℂ} {C : Matrix k m ℂ} {D : Matrix k k ℂ}
    (h : (fromBlocks A B C D).PosDef) :
    (fromBlocks A B C D).det.re ≤ A.det.re * D.det.re := by
  have hA : A.PosDef := by
    have := h.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
    have e : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by ext; simp
    rwa [e] at this
  have hD : D.PosDef := by
    have := h.submatrix (e := (Sum.inr : k → m ⊕ k)) Sum.inr_injective
    have e : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by ext; simp
    rwa [e] at this
  have hC : C = Bᴴ := ((isHermitian_fromBlocks_iff.mp h.isHermitian).2.1).symm
  subst hC
  have : Invertible A := hA.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef :=
    (PosDef.fromBlocks₁₁ B D hA).mp h.posSemidef
  have hdet : (fromBlocks A B Bᴴ D).det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hSne : (D - Bᴴ * A⁻¹ * B).det ≠ 0 := by
    intro h0
    have := h.det_pos
    rw [hdet, h0, mul_zero] at this
    exact lt_irrefl _ this
  have hSd : (D - Bᴴ * A⁻¹ * B).PosDef := hS.posDef_iff_det_ne_zero.mpr hSne
  have hdiff : (D - (D - Bᴴ * A⁻¹ * B)).PosSemidef := by
    rw [sub_sub_cancel]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same B
  have hmono := hSd.det_re_mono hdiff
  obtain ⟨hAre, hAim⟩ := Complex.pos_iff.mp hA.det_pos
  rw [hdet, Complex.mul_re, ← hAim, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hAre.le

/-- Block version of Fischer's inequality for a matrix indexed by `Fin (a + b)`. -/
theorem Matrix.PosDef.det_re_le_submatrix_det_re_mul_submatrix_det_re {a b : ℕ}
    {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).det.re := by
  have hE : M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (M.submatrix (Fin.castAdd b) (Fin.natAdd a))
        (M.submatrix (Fin.natAdd a) (Fin.castAdd b))
        (M.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp
  have hP : (M.submatrix finSumFinEquiv finSumFinEquiv).PosDef :=
    hM.submatrix finSumFinEquiv.injective
  rw [hE] at hP
  have := hP.det_re_le_det_re_mul_det_re_fromBlocks
  rwa [← hE, det_submatrix_equiv_self] at this

/-- **Hadamard's determinant inequality** for positive definite complex matrices:
`Re (det D) ≤ ∏ j, Re (D j j)`. -/
theorem Matrix.PosDef.det_re_le_prod_diag_re {k : ℕ} {D : Matrix (Fin k) (Fin k) ℂ}
    (hD : D.PosDef) :
    D.det.re ≤ ∏ j : Fin k, (D j j).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hD.det_re_le_submatrix_det_re_mul_submatrix_det_re (a := k) (b := 1)
    have h2 := ih (hD.submatrix (Fin.castAdd_injective k 1))
    have h3 : (D.submatrix (Fin.natAdd k) (Fin.natAdd k : Fin 1 → Fin (k + 1))).det =
        D (Fin.last k) (Fin.last k) := by
      rw [det_unique]; rfl
    have h4 : 0 ≤ (D (Fin.last k) (Fin.last k)).re := (Complex.pos_iff.mp hD.diag_pos).1.le
    rw [h3] at h1
    rw [Fin.prod_univ_castSucc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)

/-- Hadamard's inequality for an arbitrary split of the index set: the determinant is
at most the determinant of the leading block times the product of the remaining
diagonal entries. -/
theorem Matrix.PosDef.det_re_le_submatrix_det_re_mul_prod_diag_re {a b : ℕ}
    {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ} (hM : M.PosDef) :
    M.det.re ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re *
      ∏ j : Fin b, (M (Fin.natAdd a j) (Fin.natAdd a j)).re := by
  have h1 := hM.det_re_le_submatrix_det_re_mul_submatrix_det_re
  have h2 := (hM.submatrix (e := Fin.natAdd a) (Fin.natAdd_injective b a)).det_re_le_prod_diag_re
  have h0 : 0 ≤ (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).det.re :=
    (Complex.pos_iff.mp (hM.submatrix (Fin.castAdd_injective a b)).det_pos).1.le
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)

end Blocks
