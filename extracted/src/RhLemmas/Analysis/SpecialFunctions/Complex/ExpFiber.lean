/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

Two elementary complex-analysis lemmas.

* `Complex.isDiscrete_exp_fiber`: the fiber `exp ⁻¹' {c}` is a discrete set (it is the
  coset `log c + 2πi·ℤ`, or empty).
* `Complex.exists_norm_le_of_tendsto_exp`: if `f` is continuous on `(a, b)` and
  `exp (f s)` tends to a nonzero limit as `s → a⁺`, then `f` is bounded on `(a, t]`
  for every `t ∈ (a, b)`: near `a`, `f` takes values in a discrete coset of `2πi·ℤ`, so
  it is locally constant plus a bounded logarithm. (This is the obstruction to "winding"
  that gives the name `NoWind` in the original file.)
* `Complex.eventually_norm_le_of_tendsto_exp`: the eventual form near `a`.

Original location (file:line, in `source/src`):
`ReciprocityTheory/Chebotarev/NoWind.lean` :7 `isDiscrete_exp_fiber`,
:31 `bounded_of_tendsto_exp` (stated there for the interval `Ioc 1 2`; generalised here
to `Ioc a b`), :89 `bdd_of_exp_tendsto` (stated for `𝓝[>] 1`; generalised to `𝓝[>] a`).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue

open Filter Topology Set Complex

/-- The fiber of `Complex.exp` over any point is discrete. -/
theorem Complex.isDiscrete_exp_fiber (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext w
  simp only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwc⟩
    have hexp : Complex.exp w = Complex.exp y := hwc.trans hy.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hn
    have hd : dist w y = |(n : ℝ)| * (2 * Real.pi) := by
      rw [dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have := Real.pi_gt_three
    nlinarith
  · rintro rfl
    exact ⟨Metric.mem_ball_self one_pos, hy⟩

/-- If `f` is continuous on `(a, b)` and `exp ∘ f` has a nonzero limit at `a⁺`, then `f` is
bounded on `(a, t]` for any `t ∈ (a, b)`. -/
theorem Complex.exists_norm_le_of_tendsto_exp {f : ℝ → ℂ} {a b t : ℝ} (_hab : a < b)
    (hat : a < t) (htb : t ≤ b) (hf : ContinuousOn f (Ioc a b)) {L : ℂ} (hL : L ≠ 0)
    (hlim : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] a) (𝓝 L)) :
    ∃ C, ∀ s ∈ Ioc a t, ‖f s‖ ≤ C := by
  have hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)
  have hlim' : Tendsto (fun s => Complex.exp (f s) / L) (𝓝[>] a) (𝓝 1) := by
    simpa [div_self hL] using hlim.div_const L
  have hev := hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1' : a < u := hu1
  set t' : ℝ := min ((a + u) / 2) t with ht'
  have ht'1 : a < t' := lt_min (by linarith) hat
  have ht'u : t' < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht't : t' ≤ t := min_le_right _ _
  have hSsub : Ioc a t' ⊆ Ioc a b := Ioc_subset_Ioc_right (ht't.trans htb)
  have hball : ∀ s ∈ Ioc a t', Complex.exp (f s) / L ∈ Metric.closedBall (1 : ℂ) (1 / 2) :=
    fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 ht'u⟩
  set g : ℝ → ℂ := fun s => f s - Complex.log (Complex.exp (f s) / L) with hg
  have hgc : ContinuousOn g (Ioc a t') := by
    intro s hs
    have h1 : ContinuousWithinAt f (Ioc a t') s := (hf s (hSsub hs)).mono hSsub
    have h2 : ContinuousWithinAt (fun s => Complex.exp (f s) / L) (Ioc a t') s :=
      (Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L
    have h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (f s) / L)) (Ioc a t') s :=
      (continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt
        (f := fun s => Complex.exp (f s) / L) h2
    exact h1.sub h3
  have hmaps : MapsTo g (Ioc a t') {w : ℂ | Complex.exp w = L} := by
    intro s _
    have hne : Complex.exp (f s) / L ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hL
    simp only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, -, hc⟩ :=
    isPreconnected_Ioc.eqOn_const_of_mapsTo (Complex.isDiscrete_exp_fiber L) hgc hmaps
      ⟨Complex.log L, Complex.exp_log hL⟩
  have hcc : ContinuousOn f (Icc t' b) :=
    hf.mono ((Icc_subset_Ioc_iff (a₁ := t') (b₁ := b) (ht't.trans htb)).mpr ⟨ht'1, le_rfl⟩)
  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc t' b)).exists_bound_of_continuousOn hcc
  refine ⟨max (‖c‖ + B) C2, fun s hs => ?_⟩
  rcases le_or_gt s t' with hst | hst
  · have hs' : s ∈ Ioc a t' := ⟨hs.1, hst⟩
    have hgs : g s = c := hc hs'
    have hL' : f s = c + Complex.log (Complex.exp (f s) / L) := by
      rw [← hgs, hg]; ring
    calc ‖f s‖ = ‖c + Complex.log (Complex.exp (f s) / L)‖ := by rw [← hL']
      _ ≤ ‖c‖ + ‖Complex.log (Complex.exp (f s) / L)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + B := by gcongr; exact hB _ (hball s hs')
      _ ≤ _ := le_max_left _ _
  · exact (hC2 s ⟨hst.le, hs.2.trans htb⟩).trans (le_max_right _ _)

/-- If `f` is continuous on `(a, ∞)` and `exp ∘ f` has a nonzero limit at `a⁺`, then `f` is
eventually bounded at `a⁺`. -/
theorem Complex.eventually_norm_le_of_tendsto_exp {f : ℝ → ℂ} {a : ℝ}
    (hf : ContinuousOn f (Ioi a)) {L : ℂ} (hL : L ≠ 0)
    (h : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] a) (𝓝 L)) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] a, ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := Complex.exists_norm_le_of_tendsto_exp (a := a) (b := a + 1) (t := a + 1 / 2)
    (by linarith) (by linarith) (by linarith) (hf.mono Ioc_subset_Ioi_self)
    hL h
  refine ⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT (by linarith)) hC⟩
