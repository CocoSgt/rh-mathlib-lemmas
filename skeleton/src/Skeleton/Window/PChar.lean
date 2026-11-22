/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Window layer (1/4): primitive Dirichlet characters, the
"zero-free" propositions and `EveryCharacter`.

Source: Alpöge's Lean formalisation of the Riemann hypothesis (2026-11-20),
https://github.com/CocoSgt/riemann-hypothesis-lean  (`source/` mirror in this repo).

  * `Formalism.HC.PChar`, `KSet`, `Level` and the zero-free propositions:
      source/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean:7-45
      source/src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:11-43
  * `UpperTheory.EveryCharacter`, `UpperTheory.Top.plugWin`, `plugAll`:
      source/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8-18
  * `UpperTheory.Top.imprimitive`:
      source/src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5-35
  * glue lemmas `PChar.of_self`, `of_one`, `of_inv`, `zeroFreeOn_of_levels`,
    `Level.ofSub`, `mem_ofSub`, `cyc`, `mem_cyc`, `zeroFreeOn_of_cyc`:
      ExplicitFormulaErrorOfHostConditions.lean:45-127

Everything in this file only uses Mathlib (statement *and* proofs).
The pieces of `Level` that are not on the mainline (`Gm`, `ChebyshevGrowthImpliesZeroFree`,
which need `Formalism.Gz` and `An.gChi`) are not ported.
-/
import Mathlib

noncomputable section

open NumberField

namespace Formalism.HC

/-- A primitive Dirichlet character, remembered together with its (primitive) level.
`prim` says the level is the conductor. -/
structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

/-- The value of `ψ` at a natural number, as a complex number. -/
def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

/-- The trivial character (at level 1). -/
def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

/-- The inverse of a primitive character (level unchanged: the level is the conductor). -/
def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

theorem inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _

/-- The primitive character underlying an arbitrary Dirichlet character. -/
def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

/-- A character taking only real values. -/
def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

end PChar

/-- A finite set of primitive characters containing 1 and closed under inverse,
together with (at most) one distinguished odd real character. -/
structure KSet where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT

  psK : Option PChar
  psK_spec : ∀ ψ, psK = some ψ → ψ ∈ KEPT ∧ ψ.χ.Odd ∧ ψ.IsReal

/-- `ZeroFreeAbove ψ θ`: `L(s, ψ)` has no zero with `Re s > θ`. -/
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

/-- All characters in a class `Q` are zero-free right of 1/2. -/
def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

/-- The even characters are zero-free right of 1/2. -/
def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even

/-- **Mainline layer-3 output (analytic half):** every primitive Dirichlet character has
no zero right of the critical line. This is what `Green + VWin + Hyps` produce (`plugWin`). -/
def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

/-- A level: a `KSet` with an order `o`. -/
structure Level extends KSet where
  o : ℕ

namespace Level

variable (Λ : Level)

/-- All kept characters are zero-free above `θ`. -/
def ZeroFreeAbove (θ : ℝ) : Prop := ∀ ψ ∈ Λ.KEPT, ψ.ZeroFreeAbove θ

/-- The zero-freeness at the critical line, for a level. -/
def ZeroFreeLevel : Prop := Λ.ZeroFreeAbove (1 / 2)

/-- All kept characters are even. -/
def IsEven : Prop := ∀ ψ ∈ Λ.KEPT, ψ.χ.Even

open Classical in
/-- The non-trivial kept characters. -/
def Nt : Finset PChar := Λ.KEPT.erase PChar.one

end Level

theorem zeroFreeOn_of_levels {Q : PChar → Prop} (h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel) : ZeroFreeOn Q := by
  intro ψ hψ
  obtain ⟨Λ, h1, h2⟩ := h ψ hψ
  exact h2 ψ h1

private theorem pchar_mk_eq_of_changeLevel_eq_self_of_primitive {N d : ℕ} [NeZero N] [NeZero d] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ d) (hd : d ∣ N) (hc : DirichletCharacter.changeLevel hd ψ = χ)
    (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive) (he : d = N) :
    PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

theorem PChar.of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  have : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_self_of_primitive ψ.χ ψ.χ.primitiveCharacter ψ.χ.conductor_dvd_level
    ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive ψ.prim ψ.prim

private theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive)
    (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  have : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one

private theorem pchar_mk_eq_of_changeLevel_eq_of_level_eq {M d e : ℕ} [NeZero M] [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d) (φ : DirichletCharacter ℂ e)
    (hd : d ∣ M) (he' : e ∣ M) (hde : d = e) (hψ : DirichletCharacter.changeLevel hd ψ = χ)
    (hφ : DirichletCharacter.changeLevel he' φ = χ) (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) :
    PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl

private theorem conductor_inv_dvd_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor ∣ χ.conductor := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹,
    by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]⟩

private theorem conductor_inv_eq_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor = χ.conductor := by
  apply Nat.dvd_antisymm (conductor_inv_dvd_conductor χ)
  simpa using conductor_inv_dvd_conductor χ⁻¹

theorem PChar.of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : PChar.of χ⁻¹ = (PChar.of χ).inv := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_of_level_eq χ⁻¹ χ⁻¹.primitiveCharacter χ.primitiveCharacter⁻¹ χ⁻¹.conductor_dvd_level
    χ.conductor_dvd_level (conductor_inv_eq_conductor χ) χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _

open Classical in
/-- The level generated by a subgroup of Dirichlet characters at a fixed level `M`. -/
def Level.ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem := Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  inv_mem := by
    intro ψ h
    obtain ⟨χ, h1, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨χ⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.inv_mem (Finset.mem_filter.1 h1).2⟩, PChar.of_inv χ⟩
  psK := none
  psK_spec := fun _ h => by cases h
  o := Nat.card Ξ

theorem Level.mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by
  classical
  simp [Level.ofSub]

/-- The cyclic level generated by a single primitive character. -/
def Level.cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)

theorem Level.mem_cyc (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT :=
  (Level.mem_ofSub _ _).2 ⟨ψ.χ, Subgroup.mem_zpowers _, ψ.of_self⟩

/-- Zero-freeness for every cyclic level gives zero-freeness for all characters. -/
theorem zeroFreeOn_of_cyc {Q : PChar → Prop} (h : ∀ ψ, Q ψ → (Level.cyc ψ).ZeroFreeLevel) : ZeroFreeOn Q :=
  zeroFreeOn_of_levels fun ψ hψ => ⟨_, Level.mem_cyc ψ, h ψ hψ⟩

end Formalism.HC

namespace UpperTheory

open Formalism.HC

/-- **Mainline layer-3 output:** every Dirichlet character `χ` (not nec. primitive) has
`L(s, χ) ≠ 0` for `Re s > 1/2`, except for the trivial character at `s = 1`.
This is the hypothesis consumed by `UpperTheory.riemannHypothesis_of_everyCharacter`
(upper skeleton, `Skeleton/Top/`). -/
def EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

namespace Top

/-- **Provable glue (Window layer, bottom):** zero-freeness for all primitive characters
implies it for all Dirichlet characters, via `LFunction_changeLevel`.
Source: CharacterBoxes/Imprimitive.lean:5. -/
theorem imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  have : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  refine mul_ne_zero hL (Finset.prod_ne_zero_iff.mpr fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  intro h0
  have key : χ.primitiveCharacter p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h0
  have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp'.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp'.one_lt) (by linarith)
  have hn : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by simpa using h2
  rw [key, norm_one] at hn
  exact lt_irrefl _ hn

end Top

end UpperTheory

end
