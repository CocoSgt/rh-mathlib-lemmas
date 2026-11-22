#!/usr/bin/env python3
"""Search the pinned Mathlib source for each candidate (same name + synonyms).
Usage: mathlib_check.py  → writes analysis/mathlib_checks.txt
Each entry: (id, [regex patterns restricted to declaration lines]).
"""
import os, re, subprocess, textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
MATHLIB = os.path.normpath(os.path.join(HERE, '..', 'extracted', '.lake', 'packages', 'mathlib', 'Mathlib'))
RG = '/Users/admin/.kimi-code/bin/rg'
DECL = r'^\s*(public\s+)?(theorem|lemma|def|abbrev|instance|alias|class|structure)\s'

CHECKS = [
    ('C01 det_mono (PosDef/PSD determinant monotonicity)', r'''det_mono\b|det_monotone|det_le_det|re_det_le|PosSemidef.*det.*le|det.*PosSemidef.*le'''),
    ('C02 gramSt_hadamard (Hadamard determinant inequality, PosDef)', r'''hadamard.*(det|inequal)|(det|inequal).*hadamard|det_le_prod_diag|det_le_diagonal|det_le_prod.*diag|PosDef.*det_le|le_posDef_det|PosDef.*le.*det|fischer|fromBlocks.*det.*(le|≤)|det.*fromBlocks.*le'''),
    ('C04 hasDerivAt_det (derivative of det along a path)', r'''[Hh]asDerivAt.*\bdet\b|\bdet\b.*[Hh]asDerivAt|deriv_det|det_deriv|HasFDerivAt.*det\b|fderiv.*\bdet\b'''),
    ('C05 Cauchy–Binet (det (A*B) = Σ over injections)', r'''[Cc]auchy.?[Bb]inet|det_mul_submatrix|submatrix.*det_mul|det_mul_eq_sum|sum_submatrix.*det'''),
    ('C06 matrix similar to its transpose', r'''similar.*transpose|transpose.*similar|isTransposition|transpose.*conj|Matrix\.transpose.*GL|eq_transpose_mul|mul_eq_transpose'''),
    ('C07 det (mulLeft A) = det A ^ n', r'''det_mulLeft|det_mulRight|mulLeft.*\.det|mulRight.*\.det|LinearMap\.det\s*\(.*mul(Left|Right)'''),
    ('C08 IsRegularLocalRing.isDomain', r'''RegularLocalRing.*(isDomain|IsDomain|domain)|isDomain.*RegularLocalRing'''),
    ('C09 quotient of regular local ring by regular element is regular local, dim +1', r'''RegularLocalRing.*quotient|quotient.*RegularLocalRing|ringKrullDim.*(quotient|⧸).*span|spanFinrank.*quotient'''),
    ('C10 maximalIdeal ≤ m² → m = ⊥ (Nakayama form)', r'''maximalIdeal.*(eq_bot|le.*sq|le.*\^ 2)|eq_bot_of_eq_ideal_smul|maximalIdeal_sq'''),
    ('C11 Krull dim: P ≤ Q, x ∈ Q∖P → dim(R/Q)+1 ≤ dim(R/P)', r'''ringKrullDim.*(quotient|⧸).*le|le.*ringKrullDim.*(quotient|⧸)|Ideal.*ringKrullDim_le|ringKrullDim_le_quotient|Quotient.*ringKrullDim'''),
    ('C12 minimal prime p, q prime ≤ p → p ≤ q', r'''minimalPrimes.*(le|prime)|le_of_le_of_mem_minimalPrimes|isPrime_of_mem_minimalPrimes'''),
    ('C13 Module.length additivity for quotient', r'''Module\.length_eq_add_of_exact|Module\.length_quotient|length_add_length'''),
    ('C14 length (R/(t^k)) = k in a DVR', r'''length_quotient_pow|length.*(span.*\^|pow_maximalIdeal)|Module\.length.*Irreducible'''),
    ('C15 spectral theorem: compact self-adjoint ⟹ Hilbert basis of eigenvectors', r'''hilbertBasis.*eigen|eigen.*hilbertBasis|HilbertBasis.*eigen|spectral.*(compact|self)|compact.*spectral|exists_hilbertBasis_eigenvectors|eigenvectorBasis.*(compact|IsCompactOperator)|(eigenvalue|spectrum).*(Finite|Countable)|(Finite|Countable).*(eigenvalue|spectrum)|finite_eigenvalues|countable_eigenvalues|finite_spectrum|countable_spectrum'''),
    ('C17 0 ∈ spectrum of compact operator on infinite-dim space', r'''zero_mem_spectrum|zero.*spectrum.*compact|compact.*zero.*spectrum'''),
    ('C18 eigenspace of a continuous linear map is closed', r'''isClosed_eigenspace|IsClosed.*eigenspace|eigenspace.*IsClosed|continuous_eigenspace|eigenspace.*continuous'''),
    ('C19 finite_setOf_mem_of_orthonormal', r'''orthonormal.*[Ff]inite|[Ff]inite.*orthonormal|finite_coe_iff.*linearIndependent|LinearIndependent.*finite_of_isNoetherian'''),
    ('C20 C^∞ + Cauchy bounds on iterated FDeriv ⟹ analytic', r'''analytic.*iteratedFDeriv|iteratedFDeriv.*analytic|ContDiff.*analyticAt_of|analyticAt_of.*ContDiff|norm_iteratedFDeriv_le|AnalyticAt.*norm_iteratedFDeriv|Cauchy.*(estimate|inequal).*deriv|analytic.*of.*bound.*(deriv|iterat)|[Cc]ontinuous.*charpoly|charpoly.*[Cc]ontinuous|continuous_charpoly'''),
    ('C22 perm with ∀ x, π x ≤ x is identity', r'''perm.*eq_one|Equiv\.Perm.*eq_one|eq_one_of_forall_le'''),
    ('C23 |∏a − ∏b| ≤ Σ|a−b| for entries in unit disk', r'''abs_prod_sub_prod|prod_sub_prod|abs.*prod.*sub.*prod'''),
    ('C24 fibre_sum_le (sum over fibers with bounded cardinality)', r'''fibre_sum|fiber_sum|sum_fiber|Summable.*ncard|ncard.*Summable|tsum.*ncard|ncard.*tsum'''),
    ('C25 power-sum bounds n^{k+1} ≤ (k+1)Σa^k ≤ n^{k+1}+(k+1)n^k', r'''sum_pow.*le|le.*sum_pow|sum_rpow_le|sum_pow_bounds|pow_succ_lower|pow_succ_upper|sum_bounds'''),
    ('C26 Σ log(1+t) ≤ N log(1+Σt/N) (concavity)', r'''sum_log_le|log_sum_le|sum_log.*card|card.*log.*sum|concav.*log.*sum|Real\.log.*sum.*le'''),
    ('C27 ∫₀¹ C(D,i) t^i (1−t)^{D−i} = 1/(D+1)', r'''integral_bernstein|bernstein.*integral|integral.*bernstein|integral_pow_mul.*pow|integral_pow.*one_sub|integral.*choose.*(pow|\^)'''),
    ('C28 mean value on circle: 2π‖g 0‖² ≤ ∫‖g(se^{iθ})‖²', r'''mean.*circle|circle.*mean|circleIntegral.*norm|norm.*circleIntegral|pgds_circle|circle_mean|Integral.*circle.*norm_sq|norm_sq.*circle'''),
    ('C29 polar coordinates on disk in ℂ', r'''polarCoord|polar_coord|Complex\.polar|integral.*polar|polar.*integral|ball.*polar|polar.*ball'''),
    ('C30 isDiscrete {w | exp w = c}', r'''isDiscrete.*exp|exp.*isDiscrete|IsDiscrete.*exp|exp.*IsDiscrete|discrete.*fiber.*exp|fiber.*exp.*discrete'''),
    ('C31 bdd_of_exp_tendsto (exp(f) → L≠0 ⟹ f locally bounded)', r'''bdd.*exp.*tendsto|exp.*tendsto.*bdd|bounded.*exp.*tendsto|tendsto.*exp.*bounded'''),
    ('C32 Lp (p=2) norm squared = ∫‖f‖²', r'''Lp.*norm_sq|norm_sq.*Lp|Lp.*two_norm|lp.*norm_sq|norm_sq_eq_integral|integral.*norm_sq.*Lp|Lp_two_norm_sq'''),
    ('C33 GL(n) is a Lie group', r'''lieGroup_GL|GL.*LieGroup|LieGroup.*GL|Matrix.*GL.*LieGroup|lieGroup.*matrix|Units.*LieGroup|GL.*lie_group'''),
    ('C34 compact open subgroup in locally compact totally disconnected group', r'''compactOpen|compact_open|CompactOpen|exists.*compact.*[Oo]pen.*[Ss]ubgroup|IsCompact.*OpenSubgroup|OpenSubgroup.*IsCompact'''),
    ('C35 relIndex finite for compact open subgroup', r'''relIndex.*(ne_zero|pos|finite)|index.*(ne_zero|pos).*[Oo]pen|IsOpen.*index|index.*IsOpen|relIndex_ne_zero_of_isCompact'''),
    ('C36 sum over α/s of right-t-invariant function = index • sum over α/t', r'''sum_quotient|quotient.*sum.*index|index.*sum.*quotient|relIndex.*sum'''),
    ('C37 Hilbert–Schmidt: Σ‖Tbᵢ‖² = Σ‖T†cⱼ‖²', r'''[Hh]ilbert.?[Ss]chmidt|enorm_sq_eq_tsum|tsum.*adjoint.*sq|hsNorm|HilbertSchmidt'''),
    ('C38 cyclic vector when charpoly separable', r'''cyclic|exists_cyclic|LinearIndependent.*pow.*charpoly|charpoly.*Separable.*LinearIndependent'''),
    ('C39 symmetric polynomials: adjoin = symmetricSubalgebra', r'''symmetricSubalgebra|adjoin_eq_symmetric|symmetric.*adjoin|IsSymmetric.*adjoin'''),
    ('C40 sl2 ladder: J(R^j t) = (κ+2j) R^j t', r'''ladder|R_pow_apply|L_pow|sl2|J_pow_apply|raising.*lowering|Lowering.*Raising'''),
    ('C41 Farkas / Weyl–Minkowski for finitely generated cones', r'''[Ff]arkas|exists_dual_neg|dual_dual|Weyl.*Minkowski|Minkowski.*Weyl|fg_iff_dualFG|dual.*FG|FG.*dual|PointedCone.*(FG|dual)'''),
    ('C42 Krull domain: mem range iff locally principal at height one primes (x ∈ frac A)', r'''mem_range_of_forall_height_one|mem_range.*height|height_one.*mem_range|IsKrullDomain.*mem_range|krull.*mem_range|IsDomain.*mem_range.*height'''),
    ('C43 height_eq_one_of_isAssociatedPrime', r'''height_eq_one|IsAssociatedPrime.*height|associated.*height'''),
    ('C44 semisimple module W, simple S with same annihilator ⟹ Hom(W,S) ≠ 0', r'''semisimple.*simple.*[Hh]om|Simple.*Semisimple|IsSemisimpleModule.*IsSimpleModule|exists.*ne_zero.*Hom.*[Ss]imple'''),
    ('C45 AlgEquiv orbit of integral element is finite: ∃ n≠0, σⁿ y = y', r'''AlgEquiv.*IsIntegral|IsIntegral.*AlgEquiv|exists_pow.*AlgEquiv|AlgEquiv.*pow.*(fixed|eq)|integral.*fixed.*pow|finite.*orbit.*integral'''),
    ('C46 involution τ on field k: θ − τθ ≠ 0 ⟹ card k = (card fixed)²', r'''involution.*card|card.*involution|card.*fixed.*sq|sq.*card.*fixed|RingHom.*card.*(sq|2)|QuotientCardPow|card_eq_card_fixed'''),
    ('C47 Multiset: s ≤ map f t → ∃ u ≤ t, map f u = s', r'''Multiset.*(le_map|exists.*map.*le|map_eq.*le)|exists_le_map|le_map'''),
    ('C48 p ∈ P prime ideal, n ∈ P → ∃ prime p ∣ n, p ∈ P', r'''IsPrime.*(exists.*Prime|prime.*dvd|mem.*dvd)|exists_prime.*dvd.*mem|Prime.*mem.*dvd|prime_of_mem.*ideal|Ideal.*exists_mem_prime_dvd|exists_mem_prime_dvd|exists_mem_isPrime_dvd'''),
    ('C49 base-B digit uniqueness: Σ cₘ Bᵐ = 0, |cₘ|<B → c = 0', r'''ofDigits|digits.*eq_zero|eq_zero.*digits|ZMod.*digits|ofDigits_eq_zero|Int.*digits.*zero'''),
    ('C50 LDU uniqueness (unit triangular N, invertible U)', r'''[Ll][Dd][Uu]|BlockTriangular.*det|unitriangular.*unique|triangular.*unique|exists.*unique.*triangular'''),
    ('C51 continuous hom ℝ→ℂ with ‖f‖=1 is exp(ib·)', r'''Continuous.*(MonoidHom|OneHom).*exp|exp.*Continuous.*(MonoidHom|hom)|monoidHom.*(Real|exp)|toCircle.*Continuous|Continuous.*toCircle|ContinuousAddMonoidHom.*(Real|circle)|exists.*exp.*mul.*I|Real.*Continuous.*(hom|Equiv).*Circle|Continuous.*chars?\b.*(exp|Circle)|norm_sub_pow|pow_sub.*norm|norm.*pow.*sub.*le|sub_pow.*norm_le|norm_sub_pow_le'''),
    ('C53 monic integral-poly root in ultrametric field has ‖x‖ ≤ 1', r'''norm.*root.*le_one|root.*norm_le|norm_le_one.*root|IsRoot.*norm.*le|norm.*IsRoot.*le|Polynomial.*norm_le_one|eval.*zero.*norm.*le|norm_eval_eq_zero|isRoot.*norm_le_one'''),
    ('C54 linear indep. of simultaneous eigenvectors with distinct characters', r'''[Ll]inearIndependent.*(char|character|eigen)|[Ll]inearIndependent_of_.*(distinct|ne)|eigen.*[Ll]inearIndependent|[Ll]inearIndependent.*eigenvector|Dedekind|Artin.*(indep|linear)|iSupIndep.*eigenspace|eigenspace.*iSupIndep|independent.*eigenspace|disjoint.*eigenspace.*ne'''),
    ('C56 maxGenEigenspace (AB) ⊇ maxGenEigenspace A ⊓ maxGenEigenspace B (commute)', r'''maxGenEigenspace.*(mul|commute|prod)|mul.*maxGenEigenspace|mapsTo_maxGenEigenspace_of_comm'''),
    ('C57 a − C(eval p a) ∈ span {X i − C(p i)}', r'''span_range_X_sub_C|ker_eval|X_sub_C|eval.*ker.*span|span.*X.*sub.*C|aeval.*quotient.*eval'''),
    ('C58 PosDef is open along continuous family of Hermitian matrices', r'''PosDef.*(IsOpen|open|Continuous|eventually|Eventually)|isOpen.*PosDef|PosDef.*nhds|posDef.*isOpen|eventually.*posDef|PosDef.*eventually'''),
    ('C59 semisimple (simple) module: W semisimple, S simple, Ann W ⊆ Ann S ⟹ Hom ≠ 0 (variant)', r'''IsSemisimpleModule.*[Hh]om|exists.*LinearMap.*IsSimpleModule|annihilator.*[Ss]imple'''),
    ('C60 trace of matrix stabilizing an 𝓞-lattice is an algebraic integer', r'''trace.*IsIntegral|IsIntegral.*trace|isIntegral.*trace|Matrix\.trace.*(Integral|integral)|charpoly.*Integral.*eigen|IsIntegral.*eigenvalue'''),
    ('C61 change of basis over a subring (P Q = 1)', r'''exists.*(Matrix|matrix).*(basis|Basis).*(subring|range)|Basis.*exists.*(eq|mul).*1|change.*basis.*subring|Basis.*toMatrix.*IsUnit|isUnit.*toMatrix.*Basis'''),
    ('C62 clearing denominators: z ∈ span_K L (L an R-lattice, R domain with frac field K) → ∃ d ≠ 0, d • z ∈ L', r'''span.*exists.*(mul_mem|smul_mem|mem.*ne_zero)|exists.*(mul_mem|smul_mem).*span|Submodule.*exists.*mem.*span.*(mul|smul)|FractionField.*span.*(mem|exists)|exists_mem_span.*mul|span_eq_top.*exists.*(mul|smul)_mem|IsFractionRing.*span.*(ne_zero|mem)|exists_mem_of_mem_span|Submodule\.span.*(exists.*mul_mem)|exists_mul_mem_span|mem_span.*exists_mul_mem'''),
    ('C63 weak approximation on Dedekind domain with prescribed bounds', r'''weak_approx|approximation.*Dedekind|Dedekind.*approximation|exists.*approximation|IsDedekindDomain.*exists.*(valuation|approx)|HeightOneSpectrum.*exists|approximation.*valuation|exists_ideal.*eq|Chevalley|independent.*valuation'''),
    ('C64 length of cokernel of injective endomorphism of free DVR module = addVal det', r'''length.*(coker|range|det)|det.*length|Module\.length.*LinearMap\.(det|range)|addVal.*det|length_quotient.*det|LinearMap\.det.*addVal|length.*addVal'''),
    ('C65 complement of a submodule above a complemented one over a PID', r'''IsCompl.*exists|exists.*IsCompl|IsCompl.*(PID|IsPrincipalIdealRing)|IsPrincipalIdealRing.*IsCompl|exists_compl|compl.*exists.*PID|Submodule.*IsCompl.*exists'''),
    ('C66 LDU-type decomposition over local ring (unit diagonal, ideals U, L)', r'''exists.*(triangular|Triangular).*[Ll]ocal|IsLocalRing.*(triangular|LDU|decomp)|unit.*diagonal.*(U|ideal).*lower|Iwasawa|Gauss.*decompos.*local|exists.*mul.*diag.*mul.*[Ll]ocal'''),
    ('C67 polynomial divisibility from pointwise growth bound', r'''dvd.*norm.*eval|eval.*norm.*dvd|dvd_of.*eval.*(le|bound)|growth.*dvd|dvd.*growth|eq_zero.*of.*norm.*eval.*le|Polynomial.*dvd.*of.*forall.*norm|norm_le.*dvd|dvd_of_forall.*norm|degree.*dvd_of.*bound|Polynomial.*eq_zero_of.*le.*eval|le_of_eval|eval.*le.*dvd|dvd_of_norm_le'''),
    ('C68 Cauchy estimate: ‖fderiv f y‖ ≤ C/R on a ball', r'''[Cc]auchy.*estimate|norm_fderiv_le|fderiv.*norm.*le.*(ball|closedBall)|norm_le.*fderiv|Cauchy.*inequal|le_norm_fderiv|norm_fderiv.*ball|ball.*norm_fderiv|bound.*fderiv|fderiv.*bound.*ball|norm_fderiv_le_of|cauchyBound|Cauchy.*bound|le_of_forall.*norm.*ball.*fderiv|norm_deriv_le_of|deriv.*norm.*le.*ball|CauchyIntegral.*deriv.*norm|norm_le_closed_ball.*fderiv|fderiv.*le.*div|norm_le_div|norm_fderiv.*div|norm.*fderiv.*(div|M.*R)'''),
    ('C69 det (A t) derivative at 0 = trace A′ when A 0 = 1', r'''det.*HasDerivAt.*trace|HasDerivAt.*det.*trace|trace.*HasDerivAt.*det|deriv.*det.*one|det.*deriv.*one|HasDerivAt.*det.*(trace|adjugate)'''),
    ('C70 x² = x + c (c ∈ ℤ) ⟹ x integral', r'''IsIntegral.*sq|sq.*IsIntegral|isIntegral.*of.*eq.*add.*cast|isIntegral_of_sub_mem_span|isIntegral.*root.*Monic.*deg|eq_add_pow|Integral.*quadratic.*root|IsIntegral.*Quadratic|quadratic.*IsIntegral|IsIntegral.*root.*eq'''),
    ('C71 IsUnit a, m ∈ 𝔪 → IsUnit (a − m)', r'''isUnit.*sub.*maximal|isUnit_one_sub|one_sub.*isUnit|isUnit_of_sub_mem|maximal.*isUnit.*sub|isUnit.*isUnit.*sub|isUnit_sub_of|isUnit_of_mem_maximal.*sub|isUnit_add_of_mem_maximal|isUnit_of_isUnit_sub|isUnit.*jacobson|jacobson.*isUnit|isUnit.*add.*jacobson|isUnit_of_mem_jacobson|isUnit_one_sub_mem|IsLocalRing.*isUnit.*(sub|add)'''),
    ('C72 augmented algebra, nilpotent augmentation ideal: IsUnit(aug a) → IsUnit a', r'''IsUnit.*aeval|isUnit.*aug|aug.*isUnit|IsNilpotent.*ker.*(IsUnit|isUnit)|isUnit.*of.*isUnit.*map.*nil|isUnit_of_isUnit_map|IsUnit.*IsNilpotent|isUnit.*IsLocalRing.*ker|AlgHom.*(isUnit|IsUnit)|isUnit.*AlgHom.*ker|LocalRing.*AlgHom.*(isUnit|aug|unit)|isUnit_of_isUnit_.*map|IsUnit.*of.*IsUnit.*map'''),
    ('C73 padicValNat of multiset product', r'''padicValNat.*(prod|multiset)|Prime.*padicValNat.*(prod|multiset)|padicValNat_prod|padicVal.*multiset'''),
    ('C74 IsRegularLocalRing quotient_span_singleton (regular local quotient by non-square-degenerate element)', r'''RegularLocalRing.*span_singleton|span_singleton.*RegularLocalRing|isRegularLocalRing_quotient|RegularLocalRing.*IsLocalRing.*quotient|quotient_span_singleton'''),
    ('C75 exp(2πi x) = 1 ↔ x ∈ ℤ', r'''exp_eq_one_iff|exp.*eq_one.*int|Complex\.exp.*Int'''),
    ('C76 charpoly root gives eigenvector', r'''hasEigenvector_iff|HasEigenvalue.*isRoot|isRoot.*HasEigenvalue|charpoly.*HasEigenvalue|Module\.End\.hasEigenvalue_iff_isRoot|aeval.*eigen'''),
    ('C77 matrix ↔ 𝔸 module stability under polynomial (aeval)', r'''aeval.*mem.*invariant|Submodule.*aeval.*mem|invariant.*aeval|aeval.*mapsTo|mapsTo.*aeval|Submodule\.map_aeval|Module\.End.*aeval.*mem'''),
    ('C78 sum (cₘ Bᵐ) uniqueness base B', r'''ofDigits|digits|eq_zero_of.*sum.*pow|sum.*pow.*eq_zero'''),
    ('C79 (Fin n) filter antitone: θ ≤ f j ↔ j < card {i | θ ≤ f i}', r'''antitone.*card.*filter|card.*filter.*antitone|filter.*card.*lt|lt_card_filter|card_filter.*lt|Antitone.*filter.*card|Fin.*filter.*(lt|card).*(antiton|Antiton)'''),
    ('C80 finite index / index of subgroup via surjection with coset fibers', r'''index_eq_card|index.*Nat\.card|Nat\.card.*index|index.*surjective|surjective.*index|index_eq_of_surjective|exists.*index.*surj|index.*comap.*eq|ker.*index.*card'''),
    ('C81 tsum over group = tsum over quotient × subgroup (ℝ≥0∞)', r'''tsum.*quotient|quotient.*tsum|tsum_eq_tsum_quotient|tsum.*coset|coset.*tsum|tsum_comp_quotient|QuotientGroup.*tsum|tsum.*QuotientGroup|MeasurableEquiv.*tsum|tsum.*subtype.*prod'''),
    ('C82 ∫ ξ, 𝓕f ξ • g ξ = ∫ x, φ x • 𝓕 g x (Fourier swap)', r'''[Ff]ourier.*(integral|swap|swap)|integral.*fourier.*(smul|mul)|∫.*𝓕.*∫.*𝓕|integral_fourier|fourier_integral|integral_mul_fourier|fourier.*integral.*mul'''),
    ('C83 norm_sq convex combination: ‖a z + b w‖² ≤ a‖z‖² + b‖w‖²', r'''norm_sq.*convex|convex.*norm_sq|norm_sq.*comb|norm_sq.*add.*smul|sq_norm.*convex|convexOn.*norm|\bnorm_sq\b.*\ble\b.*smul|norm_sq.*lincomb|norm_sq_smul_add|norm_add_smul.*sq|norm_sq.*weighted|weighted.*norm_sq'''),
    ('C84 x² + txy + my² = e solvable over finite field when t² ≠ 4m', r'''Quadratic.*finite|finite.*[Qq]uadratic|exists.*sq.*add.*mul.*sq|Finset.*sq.*sum.*card|quad.*solvable|sum_sq|sq.*sq.*exists|card.*sq|sq.*card|QuadraticForm.*Finite|IsSq.*finite|Finite.*IsSquare|finite.*sum.*square'''),
    ('C85 ℤ-lattice: bounded set ∩ L finite', r'''IsZLattice|ZLattice|zLattice|lattice.*[Ff]inite.*(bounded|IsBounded)|[Ff]inite.*lattice.*bounded|DiscreteTopology.*Finite|bounded.*DiscreteTopology.*Finite|IsBounded.*Finite.*Submodule|Submodule.*DiscreteTopology.*Finite|finite.*discrete.*bounded|bounded_inter|Finite.*inter.*Discrete'''),
    ('C86 measure(S)/covol ≤ #(S ∩ L) for symmetric convex S', r'''measure.*(lattice|Lattice|ncard)|ncard.*measure|covol.*ncard|IsZLattice.*measure|measureReal.*(ncard|card)|IsAddHaarMeasure.*(lattice|ncard)|Blichfeldt|Minkowski.*(convex|lattice)|lattice.*convex.*measure'''),
    ('C03 gramSt_fischer (Fischer inequality)', r'''fischer|fromBlocks.*det.*le|det.*fromBlocks.*le|fromBlocks.*PosDef.*det'''),
    ('C16 compact self-adjoint: eigenvalues |μ|≥ε finite / spectrum countable', r'''finite_eigenvalues|countable_eigenvalues|finite_spectrum|countable_spectrum|(eigenvalue|spectrum).*(Finite|Countable)|(Finite|Countable).*(eigenvalue|spectrum)'''),
    ('C21 charpoly coefficients continuous', r'''[Cc]ontinuous.*charpoly|charpoly.*[Cc]ontinuous|continuous_charpoly'''),
    ('C52 ultrametric: ‖x‖,‖y‖≤1 → ‖xⁿ−yⁿ‖ ≤ ‖x−y‖', r'''norm_sub_pow|pow_sub.*norm|norm.*pow.*sub.*le|sub_pow.*norm_le|norm_sub_pow_le'''),
    ('C55 iSupIndep of eigenspaces for distinct characters', r'''iSupIndep.*eigenspace|eigenspace.*iSupIndep|independent.*eigenspace|disjoint.*eigenspace.*ne'''),
]

def run(pattern):
    cmd = [RG, '-n', '--no-heading', '-t', 'lean', '-e', DECL + r'.*(' + pattern + r')', '.']
    try:
        out = subprocess.run(cmd, cwd=MATHLIB, capture_output=True, text=True, timeout=120).stdout
    except subprocess.TimeoutExpired:
        return ['<timeout>']
    lines = [l for l in out.split('\n') if l and not l.startswith('Archive/')]
    return lines[:12]

with open(os.path.join(HERE, 'mathlib_checks.txt'), 'w') as fh:
    for cid, pats in CHECKS:
        fh.write(f'\n=== {cid}\n')
        if not pats:
            continue
        seen = set()
        res = run(pats)
        if not res:
            fh.write('    (no matches)\n')
        for l in res:
            if l not in seen:
                seen.add(l); fh.write(f'    {l}\n')
print('done')
