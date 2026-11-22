/-
Axiom audit for every public theorem of the pilot (`lake env lean Axioms.lean`).
Expected: each line reads `'…' does not depend on any axioms` or
`'…' depends on axioms: [propext, Classical.choice, Quot.sound]`.
-/
import RhLemmas

-- Analysis/InnerProductSpace/CompactSelfAdjoint.lean
#print axioms Orthonormal.finite_setOf_mem_of_finiteDimensional
#print axioms exists_hilbertBasis_subset_iUnion
#print axioms IsCompactOperator.zero_mem_spectrum
#print axioms LinearMap.IsSymmetric.exists_real_of_hasEigenvalue
#print axioms IsCompactOperator.finite_eigenvalues_norm_ge
#print axioms IsCompactOperator.countable_eigenvalues
#print axioms IsCompactOperator.finite_spectrum_norm_ge
#print axioms IsCompactOperator.countable_spectrum
#print axioms IsCompactOperator.spectrum_subset_range_ofReal
#print axioms IsCompactOperator.eventually_notMem_spectrum
#print axioms exists_hilbertBasis_eigenvectors
#print axioms exists_hilbertBasis_eigenvectors_hasSum
#print axioms orthogonal_iSup_iInf_eigenspaces_eq_bot
#print axioms exists_hilbertBasis_common_eigenvectors
-- Analysis/Matrix/Deriv.lean
#print axioms Matrix.hasDerivAt_det
#print axioms Matrix.hasDerivAt_log_det_re
-- Analysis/Matrix/PosDef/Det.lean
#print axioms Matrix.PosSemidef.det_one_add_eq_prod
#print axioms Matrix.PosDef.det_re_mono
#print axioms Matrix.PosDef.det_re_le_det_re_mul_det_re_fromBlocks
#print axioms Matrix.PosDef.det_re_le_submatrix_det_re_mul_submatrix_det_re
#print axioms Matrix.PosDef.det_re_le_prod_diag_re
#print axioms Matrix.PosDef.det_re_le_submatrix_det_re_mul_prod_diag_re
-- Analysis/Matrix/PosDef/Open.lean
#print axioms Matrix.PosDef.eventually
-- Analysis/SpecialFunctions/BernsteinIntegral.lean
#print axioms Real.betaNatInt_zero
#print axioms Real.betaNatInt_succ
#print axioms Real.betaNatInt_eq_inv_mul_choose
#print axioms Real.integral_bernsteinPolynomial
-- Analysis/SpecialFunctions/Complex/ExpFiber.lean
#print axioms Complex.isDiscrete_exp_fiber
#print axioms Complex.exists_norm_le_of_tendsto_exp
#print axioms Complex.eventually_norm_le_of_tendsto_exp
-- Analysis/SpecialFunctions/Tent.lean
#print axioms Real.tent_nonneg
#print axioms Real.tent_le_one
#print axioms Real.tent_of_abs_le
#print axioms Real.tent_of_one_le_abs
#print axioms Real.abs_tent_sub_tent_le
#print axioms Real.abs_lt_one_of_tent_ne_zero
#print axioms Real.tent_add_int_eq_zero_of_notMem
#print axioms Real.sum_tent_add_int_pair
#print axioms Finset.abs_prod_sub_prod_le
#print axioms Real.tentProd_nonneg
#print axioms Real.tentProd_le_one
#print axioms Real.abs_lt_one_of_tentProd_ne_zero
#print axioms Real.abs_tentProd_sub_tentProd_le
#print axioms Real.tentProd_add_int_eq_zero_of_notMem
#print axioms Real.sum_tentProd_add_int_piFinset
#print axioms Real.hasSum_tentProd_add_int
-- Geometry/Convex/Cone/DualFinite.lean
#print axioms PointedCone.mem_hull_insert
#print axioms PointedCone.exists_of_mem_hull_image
#print axioms PointedCone.nonneg_of_mem_hull
#print axioms PointedCone.exists_dual_neg_of_not_mem_hull
#print axioms PointedCone.exists_dual_neg_of_not_mem_hull_finset
#print axioms PointedCone.exists_dual_neg_of_not_mem
#print axioms PointedCone.mem_iff_forall_dual
#print axioms PointedCone.fg_top
#print axioms PointedCone.hull_inf_halfspace
#print axioms PointedCone.fg_inf_halfspace
#print axioms PointedCone.fg_dual_finset
#print axioms PointedCone.fg_dual
#print axioms PointedCone.dual_dual_flip_of_fg
#print axioms PointedCone.fg_iff_dualFG
-- LinearAlgebra/Matrix/Det.lean
#print axioms Matrix.det_mul_eq_sum_over_functions
#print axioms LinearMap.det_mulLeft_matrix
#print axioms LinearMap.det_mulRight_matrix
#print axioms LinearMap.det_restrictScalars_mulLeft
#print axioms LinearMap.det_restrictScalars_mulRight
#print axioms Equiv.Perm.eq_one_of_forall_le
-- LinearAlgebra/Matrix/LDU.lean
#print axioms Matrix.exists_ldu_decomposition
-- LinearAlgebra/Matrix/Similarity.lean
#print axioms MatrixSimilarity.continuous_charpoly_coeff_of_fintype
#print axioms MatrixSimilarity.continuous_charpoly_coeff
#print axioms MatrixSimilarity.charpoly_smul_eq_zero
#print axioms MatrixSimilarity.exists_cyclic_decomposition
#print axioms MatrixSimilarity.exists_isSymm_of_form
#print axioms MatrixSimilarity.exists_isSymm_mul_eq_transpose_mul
#print axioms MatrixSimilarity.exists_conj_of_equiv
#print axioms MatrixSimilarity.finite_monic_dvd
#print axioms MatrixSimilarity.exists_countable_conj_charpoly
-- RingTheory/RegularLocalRing/Domain.lean
#print axioms Ideal.spanFinrank_span_finset_le
#print axioms Module.Basis.exists_repr_ne_zero
#print axioms Module.Basis.span_insert_image_erase_eq_top
#print axioms IsLocalRing.quotient_span_singleton
#print axioms IsRegularLocalRing.spanFinrank_quotient_eq_and_ringKrullDim_add_one
#print axioms IsRegularLocalRing.quotient_span_singleton
#print axioms IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one
#print axioms IsLocalRing.isDomain_of_maximalIdeal_eq_bot
#print axioms IsLocalRing.maximalIdeal_eq_bot_of_le_sq
#print axioms IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes
#print axioms IsRegularLocalRing.isDomain
-- Topology/Algebra/InfiniteSum/Fiberwise.lean
#print axioms summable_and_tsum_le_of_fiber_le
#print axioms tsum_ge_mul_tsum_of_ncard_fiber_ge
