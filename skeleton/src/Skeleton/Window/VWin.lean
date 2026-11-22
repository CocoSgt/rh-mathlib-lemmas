/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Window layer (2/4): the automorphic window hypothesis `VWin`
("mainline layer-3 input, produced from `Row0b` by `vwin_of_row`").

Source (verbatim except for one `@`-application in `VVle`: `shaLen` here takes instance arguments
`[Field E] [Field Ω] [Algebra E Ω]` only, so `@shaLen E Ω _ _ _ (l : ℕ) ⟨l.2⟩ …` has three `_` where
the source has five — the source's `shaLen` also carries the unused `[NumberField E] [IsAlgClosure E Ω]`.
All Mathlib-only once `PChar` and the Galois cohomology data of
`Skeleton/Galois/GaloisCohomology.lean` are in place):
  * `UpperTheory.Top.VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin`,
    `VVle.mono`, `exists_pageN`:
      source/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12-77

Definition chain (statement level, see SKELETON-lower.md): `VWin → VWinAt → {PageN, WinPair, VAt}
→ {IsChiField, VVle} → {shaLen, PChar} → Sha/qzTw → {LData, scalRep, locFam, Sha1, ...} → ... →
Mathlib; 32 definitions, 2 Mathlib-only lemmas, longest chain 12.
-/
import Mathlib
import Skeleton.Galois.GaloisCohomology
import Skeleton.Window.PChar

noncomputable section

open NumberField

namespace UpperTheory.Top

open Formalism.HC

/-- A bound on the `l`-adic Sha lengths at the places of `E` (for `e < t`) and on their
logarithmic sum. -/
def VVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → Formalism.GaloisCohomology.shaLen (ld p) (e : ℤ) ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes,
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t,
          ((@Formalism.GaloisCohomology.shaLen E Ω _ _ _ (l : ℕ) ⟨l.2⟩ (@ld (l : ℕ) ⟨l.2⟩) (e : ℤ)).toNat : ℝ) ≤ B

/-- `E` admits an embedding into `ℚ(ζ_N)` such that the Galois action on the image is
controlled by `ψ`, with congruence conditions modulo `2^(e+2)`, `q`, `d`. -/
def IsChiField (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ),
    2 ^ (e + 2) ∣ N ∧ ψ.N ∣ N ∧ q ∣ N ∧ d ∣ N ∧ IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔
        (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1)

/-- A pair of auxiliary primes `(q, d)` of size about `Y^(ε/5)`, `Y^(ε/5)·log²Y`. -/
structure WinPair (eps Y : ℝ) (q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  q_lo : Y ^ (eps / 5) / 2 < Real.log q
  q_up : Real.log q ≤ Y ^ (eps / 5)
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_lo : Y ^ (eps / 5) * Real.log Y ^ 2 / 2 < Real.log d
  d_up : Real.log d ≤ Y ^ (eps / 5) * Real.log Y ^ 2
  d_q : q ∣ d + 1
  d_small : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → p ∣ d + 1

/-- `2^e` is comparable to `x^(2+8ε)`. -/
def PageN (eps x : ℝ) (e : ℕ) : Prop := x ^ (2 + 8 * eps) ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)

/-- The Sha-length bound `VVle` for every field `E` that is a `ψ`-character field. -/
def VAt (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → VVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

/-- The window estimate: for every small `ε`, every page-number function `e`, there are
`J` and `X0` such that for all large `X`, for all `Y ∈ [X^(1/J), X²]`, the Sha bounds hold
for all `x ∈ [Y, Y²]` and all auxiliary prime pairs of size `Y^(ε/5)`. -/
def VWinAt (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
    ∃ J : ℝ, 1 ≤ J ∧ ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → VAt ψ eps Ct q d (e x) x

/-- **Mainline layer-3 input (automorphic window):** the window estimate for every
primitive Dirichlet character, with exponent `Ct = 401`.
This is what `Row0b` produces through `vwin_of_row` (`Skeleton/Galois/EveryCharacterOfRow.lean`)
and what `plugWin` consumes (`Skeleton/Window/PlugAll.lean`). -/
def VWin : Prop := ∀ ψ : PChar, VWinAt ψ 401

theorem VVle.mono {E : Type} [Field E] [NumberField E] {t t' : ℕ} {B B' : ℝ} (h : VVle E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVle E t' B' := by
  intro Ω _ _ _ ld
  obtain ⟨h1, h2⟩ := h Ω ld
  refine ⟨fun p _ e he1 he2 => h1 p e he1 (lt_of_lt_of_le he2 ht), fun S => ?_⟩
  refine le_trans ?_ (le_trans (h2 S) hB)
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_Ico] at he ⊢
    omega
  · intro e _ _
    positivity

theorem exists_pageN (eps : ℝ) (he : 0 < eps) : ∃ e : ℝ → ℕ, ∀ x ≥ (1 : ℝ), PageN eps x (e x) := by
  have : ∀ x : ℝ, ∃ e : ℕ, x ≥ 1 → PageN eps x e := by
    intro x
    by_cases hx : x ≥ 1
    · have h1 : (1 : ℝ) ≤ x ^ (2 + 8 * eps) := Real.one_le_rpow hx (by linarith)
      obtain ⟨n, a, b⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine ⟨n + 1, fun _ => ⟨b.le, ?_⟩⟩
      rw [pow_succ]; linarith
    · exact ⟨0, fun h => absurd h hx⟩
  choose e he using this
  exact ⟨e, he⟩

end UpperTheory.Top

end
