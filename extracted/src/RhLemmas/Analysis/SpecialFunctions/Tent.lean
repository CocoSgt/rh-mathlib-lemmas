/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original proof in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Extracted, renamed and documented here as part of the "rh-mathlib-lemmas" pilot; all
mathematical credit belongs to Levent Alpöge and Claude.

# The tent function and its integer translates

`Real.tent t = max 0 (1 - |t|)` is `1`-Lipschitz, supported in `[-1, 1]`, and its translates by
integers form a partition of unity of `ℝ`: `∑' n : ℤ, tent (t + n) = 1`. The product
`Real.tentProd y = ∏ i, tent (y i)` gives a partition of unity for `ι → ℤ` acting on `ι → ℝ`
(`Real.hasSum_tentProd_add_int`). Also `Finset.abs_prod_sub_prod_le`:
`|∏ a i - ∏ b i| ≤ ∑ |a i - b i|` for families in the unit disk.

Original location (file:line, in `source/src`):
`ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean`
  :7 `tent`, :9 `tent_nonneg`, :11 `tent_le_one`, :14 `tent_of_abs_le`, :17 `tent_of_one_le_abs`,
  :20 `abs_tent_sub_tent_le`, :26 `abs_lt_one_of_tent_ne_zero`, :30 `tent_add_int_eq_zero_of_notMem`,
  :36 `sum_tent_add_int_pair`, :59 `abs_prod_sub_prod_le_sum_abs_sub`, :84 `Tent`, :86 `Tent_nonneg`,
  :88 `Tent_le_one`, :91 `abs_lt_one_of_Tent_ne_zero`, :94 `abs_Tent_sub_Tent_le`,
  :101 `Tent_add_int_eq_zero_of_notMem`, :109 `sum_Tent_add_int_piFinset`, :116 `hasSum_Tent_add_int`.
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

noncomputable section
/-- The Real.tent function `Real.tent t = max 0 (1 - |t|)`: a continuous partition of unity for the
action of `ℤ` on `ℝ` by translations (`Real.hasSum_tent_add_int`). -/
noncomputable def Real.tent (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- The Real.tent function is nonnegative. -/
theorem Real.tent_nonneg (t : ℝ) : 0 ≤ Real.tent t := le_max_left _ _

/-- The Real.tent function is at most `1`. -/
theorem Real.tent_le_one (t : ℝ) : Real.tent t ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg t])

/-- On `[-1, 1]` the Real.tent function is `1 - |t|`. -/
theorem Real.tent_of_abs_le {t : ℝ} (h : |t| ≤ 1) : Real.tent t = 1 - |t| :=
  max_eq_right (by linarith)

/-- Outside `(-1, 1)` the Real.tent function vanishes. -/
theorem Real.tent_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : Real.tent t = 0 :=
  max_eq_left (by linarith)

/-- The Real.tent function is `1`-Lipschitz. -/
theorem Real.abs_tent_sub_tent_le (s t : ℝ) : |Real.tent s - Real.tent t| ≤ |s - t| := by
  unfold Real.tent
  calc |max 0 (1 - |s|) - max 0 (1 - |t|)| ≤ |(1 - |s|) - (1 - |t|)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |(|t| - |s|)| := by ring_nf
    _ ≤ |t - s| := abs_abs_sub_abs_le_abs_sub t s
    _ = |s - t| := abs_sub_comm t s

/-- The Real.tent function is nonzero only on `(-1, 1)`. -/
theorem Real.abs_lt_one_of_tent_ne_zero {t : ℝ} (h : Real.tent t ≠ 0) : |t| < 1 := by
  by_contra h'
  exact h (tent_of_one_le_abs (not_lt.mp h'))

/-- `Real.tent (t + n)` vanishes unless `n ∈ {-⌊t⌋, -⌊t⌋ - 1}`. -/
theorem Real.tent_add_int_eq_zero_of_notMem (t : ℝ) {n : ℤ} (hn : n ∉ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ)) :
    Real.tent (t + n) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  apply tent_of_one_le_abs
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hn.1 with h | h
  · have : n ≤ -⌊t⌋ - 2 := by omega
    have : (n : ℝ) ≤ -⌊t⌋ - 2 := by exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith
  · have : (n : ℝ) ≥ -⌊t⌋ + 1 := by exact_mod_cast (show n ≥ -⌊t⌋ + 1 by omega)
    rw [abs_of_nonneg (by linarith)]; linarith

/-- The two nonzero translates of the Real.tent function at `t` sum to `1`. -/
theorem Real.sum_tent_add_int_pair (t : ℝ) :
    ∑ n ∈ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ), Real.tent (t + n) = 1 := by
  have hne : (-⌊t⌋ : ℤ) ≠ -⌊t⌋ - 1 := by omega
  rw [Finset.sum_pair hne]
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  push_cast
  rw [tent_of_abs_le, tent_of_abs_le]
  · rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith


/-- For families with `|a i| ≤ 1` and `|b i| ≤ 1`,
`|∏ a i - ∏ b i| ≤ ∑ |a i - b i|`. -/
theorem Finset.abs_prod_sub_prod_le {κ : Type*} (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hP : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (mem_insert_of_mem hi))
    have ih' := ih (fun i hi => ha i (mem_insert_of_mem hi)) (fun i hi => hb i (mem_insert_of_mem hi))
    have haj := ha j (mem_insert_self j s)
    have hsum : 0 ≤ ∑ i ∈ s, |a i - b i| := sum_nonneg fun i _ => abs_nonneg _
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
      _ ≤ |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 :=
        add_le_add (mul_le_mul haj ih' (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

variable {ι : Type*} [Fintype ι]

/-- Product of Real.tent functions, a partition of unity for `ι → ℤ` acting on `ι → ℝ`. -/
noncomputable def Real.tentProd (y : ι → ℝ) : ℝ := ∏ i, Real.tent (y i)

/-- `tentProd` is nonnegative. -/
theorem Real.tentProd_nonneg (y : ι → ℝ) : 0 ≤ Real.tentProd y := prod_nonneg fun _ _ => tent_nonneg _

/-- `tentProd` is at most `1`. -/
theorem Real.tentProd_le_one (y : ι → ℝ) : Real.tentProd y ≤ 1 :=
  prod_le_one (fun _ _ => tent_nonneg _) (fun _ _ => tent_le_one _)

/-- `tentProd y ≠ 0` forces `|y i| < 1` for all `i`. -/
theorem Real.abs_lt_one_of_tentProd_ne_zero {y : ι → ℝ} (h : Real.tentProd y ≠ 0) (i : ι) : |y i| < 1 :=
  abs_lt_one_of_tent_ne_zero fun h' => h (prod_eq_zero (mem_univ i) h')

/-- `tentProd` is `1`-Lipschitz in the `ℓ¹` norm. -/
theorem Real.abs_tentProd_sub_tentProd_le (y y' : ι → ℝ) : |Real.tentProd y - Real.tentProd y'| ≤ ∑ i, |y i - y' i| := by
  unfold Real.tentProd
  refine (Finset.abs_prod_sub_prod_le univ _ _ (fun i _ => ?_) (fun i _ => ?_)).trans
    (sum_le_sum fun i _ => abs_tent_sub_tent_le (y i) (y' i))
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _

/-- `tentProd (y + n)` vanishes unless `n` ranges over
`{-⌊y i⌋, -⌊y i⌋ - 1}` at every `i`. -/
theorem Real.tentProd_add_int_eq_zero_of_notMem [DecidableEq ι] (y : ι → ℝ) {n : ι → ℤ}
    (hn : n ∉ Fintype.piFinset fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) :
    Real.tentProd (fun i => y i + n i) = 0 := by
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact prod_eq_zero (mem_univ i) (tent_add_int_eq_zero_of_notMem (y i) hi)

/-- The finitely many nonzero translates of `tentProd` by integer vectors sum to `1`. -/
theorem Real.sum_tentProd_add_int_piFinset [DecidableEq ι] (y : ι → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Real.tentProd (fun i => y i + n i) = 1 := by
  classical
  show ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), ∏ i, Real.tent (y i + n i) = 1
  rw [← Finset.prod_univ_sum (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) (fun i n => Real.tent (y i + n))]
  exact prod_eq_one fun i _ => sum_tent_add_int_pair (y i)

/-- **Partition of unity**: `∑' n : ι → ℤ, tentProd (y + n) = 1`. -/
theorem Real.hasSum_tentProd_add_int (y : ι → ℝ) : HasSum (fun n : ι → ℤ => Real.tentProd (fun i => y i + n i)) 1 := by
  classical
  have h : HasSum (fun n : ι → ℤ => Real.tentProd (fun i => y i + n i))
      (∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Real.tentProd (fun i => y i + n i)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => Real.tentProd_add_int_eq_zero_of_notMem y hn
  rwa [Real.sum_tentProd_add_int_piFinset] at h

end
