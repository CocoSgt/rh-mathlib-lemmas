/-
Copyright (c) 2026 Levent Alpöge (with Claude). Original definitions in the Alpöge–Claude
Lean formalization of the Riemann Hypothesis (released 2026-11-20 at https://alpo.ge/).
Copied verbatim into the "main-line skeleton" (skeleton/); all mathematical credit
belongs to Levent Alpöge and Claude.

# `ZeroFreeAll`: zero-free half planes for primitive characters

`ZeroFreeAll` is the output of the analytic core of the development (`plugWin`) and the
input of `imprimitive` (`Skeleton/Top/Imprimitive.lean`), which turns it into
`Skeleton.EveryCharacter`. It is phrased with the development's own packaging `PChar` of a
*primitive* Dirichlet character together with its (primitive) level; `PChar` only refers to
Mathlib's `DirichletCharacter`, so the whole statement is Mathlib-only.
`zeroFreeAll_iff` below restates it without `PChar`.

Original location (file:line, in `source/src`):
`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean`
  :7 `Formalism.HC.PChar`, :17 `PChar.val`, :19 `PChar.one`, :21 `PChar.inv`,
  :26 `PChar.inv_inv`, :32 `PChar.of`, :35 `PChar.IsReal`
  (:39 `Formalism.HC.KSet` and the later structures are not needed by any top-layer statement).
`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean`
  :11 `PChar.ZeroFreeAbove`, :14 `ZeroFreeOn`, :16 `ZeroFreeEven`, :18 `Formalism.HC.ZeroFreeAll`,
  :50, :64, :75 the three private lemmas, :59 `PChar.of_self`, :70 `PChar.of_one`,
  :85, :91 `conductor_inv_{dvd,eq}_conductor`, :96 `PChar.of_inv`.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.Conductor

noncomputable section

namespace Skeleton

/-- A primitive Dirichlet character packaged with its (primitive) level.
Original: `Formalism.HC.PChar`, `PrimePairSizeCondition.lean:7`. -/
structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

/-- The value of the character at a natural number.
Original: `Formalism.HC.PChar.val`, `PrimePairSizeCondition.lean:17`. -/
def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

/-- The primitive character `1` of level `1`.
Original: `Formalism.HC.PChar.one`, `PrimePairSizeCondition.lean:19`. -/
def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

/-- The inverse of a primitive character (at the same level).
Original: `Formalism.HC.PChar.inv`, `PrimePairSizeCondition.lean:21`. -/
def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

/-- Original: `Formalism.HC.PChar.inv_inv`, `PrimePairSizeCondition.lean:26`. -/
theorem inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _

/-- The primitive character associated to an arbitrary Dirichlet character (its
primitive model, at its conductor).
Original: `Formalism.HC.PChar.of`, `PrimePairSizeCondition.lean:32`. -/
def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

/-- Whether the character is real-valued.
Original: `Formalism.HC.PChar.IsReal`, `PrimePairSizeCondition.lean:35`. -/
def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

end PChar

/-- The `L`-function of `ψ` has no zero in the open right half plane `θ < re s`.
Original: `Formalism.HC.PChar.ZeroFreeAbove`, `ExplicitFormulaErrorOfHostConditions.lean:11`. -/
def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

/-- Every primitive character satisfying `Q` has no zero in `re s > 1/2`.
Original: `Formalism.HC.ZeroFreeOn`, `ExplicitFormulaErrorOfHostConditions.lean:14`. -/
def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

/-- The same, restricted to even characters.
Original: `Formalism.HC.ZeroFreeEven`, `ExplicitFormulaErrorOfHostConditions.lean:16`. -/
def ZeroFreeEven : Prop := ZeroFreeOn fun ψ => ψ.χ.Even

/-- Every primitive Dirichlet `L`-function is nonvanishing on `re s > 1/2`.
Original: `Formalism.HC.ZeroFreeAll`, `ExplicitFormulaErrorOfHostConditions.lean:18`. -/
def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True

/-- Original: the private `pchar_mk_eq_of_changeLevel_eq_self_of_primitive`,
`ExplicitFormulaErrorOfHostConditions.lean:50`. -/
private theorem pchar_mk_eq_of_changeLevel_eq_self_of_primitive {N d : ℕ} [NeZero N] [NeZero d]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ d) (hd : d ∣ N)
    (hc : DirichletCharacter.changeLevel hd ψ = χ) (h1 : ψ.IsPrimitive) (h2 : χ.IsPrimitive)
    (he : d = N) : PChar.mk d ψ h1 = PChar.mk N χ h2 := by
  subst he
  rw [DirichletCharacter.changeLevel_self] at hc
  subst hc
  rfl

/-- Original: `Formalism.HC.PChar.of_self`, `ExplicitFormulaErrorOfHostConditions.lean:59`. -/
theorem PChar.of_self (ψ : PChar) : PChar.of ψ.χ = ψ := by
  haveI : NeZero ψ.χ.conductor := ⟨ψ.χ.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_self_of_primitive ψ.χ ψ.χ.primitiveCharacter
    ψ.χ.conductor_dvd_level ψ.χ.changeLevel_primitiveCharacter ψ.χ.primitiveCharacter_isPrimitive
    ψ.prim ψ.prim

/-- Original: the private `pchar_mk_eq_one_of_level_eq_one`,
`ExplicitFormulaErrorOfHostConditions.lean:64`. -/
private theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d)
    (h : ψ.IsPrimitive) (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

/-- Original: `Formalism.HC.PChar.of_one`, `ExplicitFormulaErrorOfHostConditions.lean:70`. -/
theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  haveI : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one

/-- Original: the private `pchar_mk_eq_of_changeLevel_eq_of_level_eq`,
`ExplicitFormulaErrorOfHostConditions.lean:75`. -/
private theorem pchar_mk_eq_of_changeLevel_eq_of_level_eq {M d e : ℕ} [NeZero M] [NeZero d]
    [NeZero e] (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d)
    (φ : DirichletCharacter ℂ e) (hd : d ∣ M) (he' : e ∣ M) (hde : d = e)
    (hψ : DirichletCharacter.changeLevel hd ψ = χ) (hφ : DirichletCharacter.changeLevel he' φ = χ)
    (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) : PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl

/-- Original: the private `conductor_inv_dvd_conductor`,
`ExplicitFormulaErrorOfHostConditions.lean:85`. -/
private theorem conductor_inv_dvd_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor ∣ χ.conductor := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹,
    by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]⟩

/-- Original: the private `conductor_inv_eq_conductor`,
`ExplicitFormulaErrorOfHostConditions.lean:91`. -/
private theorem conductor_inv_eq_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor = χ.conductor := by
  apply Nat.dvd_antisymm (conductor_inv_dvd_conductor χ)
  simpa using conductor_inv_dvd_conductor χ⁻¹

/-- Original: `Formalism.HC.PChar.of_inv`, `ExplicitFormulaErrorOfHostConditions.lean:96`. -/
theorem PChar.of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    PChar.of χ⁻¹ = (PChar.of χ).inv := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  haveI : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_of_level_eq χ⁻¹ χ⁻¹.primitiveCharacter
    χ.primitiveCharacter⁻¹ χ⁻¹.conductor_dvd_level χ.conductor_dvd_level (conductor_inv_eq_conductor χ)
    χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _

/-- `ZeroFreeAll` without the packaging `PChar`: every *primitive* Dirichlet `L`-function is
nonvanishing on `re s > 1/2` (new; not in the original development). -/
theorem zeroFreeAll_iff :
    ZeroFreeAll ↔ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), χ.IsPrimitive →
      1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0 :=
  ⟨fun h N _ χ s hχ hs => h (@PChar.mk N inferInstance χ hχ) trivial s hs,
   fun h ψ _ s hs => h ψ.N ψ.χ s ψ.prim hs⟩

end Skeleton
