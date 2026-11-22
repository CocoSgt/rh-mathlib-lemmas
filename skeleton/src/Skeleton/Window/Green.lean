/-
Author of the underlying formalisation: Levent Alpöge (with Claude).
The source release carries no license file; redistribution terms are to be
confirmed with the author (see REPORT.md §5.6).  Skeleton files extracted by
GLM 5.4 via DeepSeek Harness.

Lower mainline skeleton, Window layer (3/4): the analytic input `Green`
("Green's characters of `GL_n(𝔽_g)` exist and are unique up to labelling"),
one of the two hypotheses consumed by `plugWin`.

Source (verbatim; all Mathlib-only):
  * `GlobalTheory.GLq.Gn … Green`:
      source/src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:11-112
  * `Formalism.CyclotomicNorms.Fbar`, `rootsBar`:
      source/src/Formalism/CyclotomicNorms/StatementT.lean:14-17
  * `Formalism.MainNotions.ArithmeticCylinders.entN`, `IsUniUp`, `eDat`, `eU`:
      source/src/Formalism/SharpRestriction/LevelLetterCocycles/ArithmeticCylinders.lean:292-307
  (`ESerTie`, LabelDatum.lean:114, depends on `Formalism.BasicNotions.D7` and is not on the
  mainline; not ported.)

Definition chain: `Green → IsCuspOf → {IsCusp, thetaOf, LabelDatum} → {res, hc, hcT, hcL, IsIrr,
rootsBar, Fbar} → {entN, eU, eDat, FDRep.character} → Mathlib; 15 definitions, longest chain 5.
-/
import Mathlib

noncomputable section

open Polynomial NumberField

namespace Formalism.CyclotomicNorms

/-- A fixed algebraic closure of `𝔽_g = ZMod g`. -/
abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)

/-- The multiset of roots in `Fbar g` of a polynomial over `ZMod g`. -/
def rootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (Fbar g) :=
  (f.map (algebraMap (ZMod g) (Fbar g))).roots

end Formalism.CyclotomicNorms

namespace Formalism.MainNotions.ArithmeticCylinders

/-- Entry `(a, b)` of an `N × N` matrix, read as 0 outside the index range. -/
def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- Upper unitriangular matrices. -/
def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

/-- The averaging element of `ℂ[GL_n(𝔽_g)]` over the matrices satisfying `P`, with
coefficients `ψ₀(φ(u))⁻¹`. -/
def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹

/-- The averaging element over the upper unitriangular matrices, for the character
`ψ₀(Σ u_{i,i+1})`. -/
def eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N IsUniUp (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

end Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

/-- `GL_n(𝔽_g)`. -/
abbrev Gn (g n : ℕ) : Type := GL (Fin n) (ZMod g)

/-- `M_n(𝔽_g)`. -/
abbrev Mt (g n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod g)

/-- A class function on `G`. -/
def IsClass {G : Type} [Group G] (χ : G → ℂ) : Prop := ∀ x y : G, χ (y * x * y⁻¹) = χ x

/-- `χ` is the character of a finite-dimensional representation. -/
def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop := ∃ V : FDRep ℂ G, ∀ x, V.character x = χ x

/-- `χ` is the character of an irreducible finite-dimensional representation. -/
def IsIrr {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ ∀ x, V.character x = χ x

/-- Inner product of class functions. -/
def ip {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, α x * β x⁻¹

/-- Trace of `a ∈ ℂ[G]` against `χ`. -/
def tr {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) : ℂ := ∑ x, a.coeff x * χ x

/-- The central idempotent of `χ` (for `χ` irreducible). -/
def zOf {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ x, MonoidAlgebra.single x (χ 1 / (Fintype.card G : ℂ) * χ x⁻¹)

variable {g : ℕ} [Fact g.Prime]

/-- Top-left `a × a` block, padded with zeros. -/
def tl (a : ℕ) {n : ℕ} (M : Mt g n) : Mt g a := fun i j => entN M i j

/-- Bottom-right `b × b` block, read off below/right of index `a`. -/
def br (a b : ℕ) {n : ℕ} (M : Mt g n) : Mt g b := fun i j => entN M (a + i) (a + j)

/-- Parabolic structure: lower-left `a × (n-a)` block vanishes. -/
def InPar (a : ℕ) {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

/-- The `GL` element of a block matrix when invertible, else 1. -/
def toG {n : ℕ} (M : Mt g n) : Gn g n := if h : IsUnit M then h.unit else 1

/-- Hecke-type averaging: conjugation average over parabolic cosets, evaluated on a
pair of blocks. -/
def hcT (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InPar a ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      Φ (toG (tl a ((y⁻¹ * x * y : Gn g n) : Mt g n))) (toG (br a b ((y⁻¹ * x * y : Gn g n) : Mt g n))) else 0

/-- Product version of `hcT`. -/
def hc (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := hcT a b (fun x y => α x * β y) n

/-- Jacquet module value: average of `χ` over matrices with given diagonal blocks. -/
def res (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g a → Gn g b → ℂ := fun h₁ h₂ =>
  ((g : ℂ) ^ (a * b))⁻¹ * ∑ x : Gn g n,
    if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b) then χ x else 0

/-- A pair (degree, class function on `GL_deg`). -/
abbrev Pc (g : ℕ) : Type := Σ d : ℕ, Gn g d → ℂ

/-- Total degree of a list of such pairs. -/
def degL (L : List (Pc g)) : ℕ := (L.map fun p => p.1).sum

/-- Iterated Hecke averaging along a list. -/
def hcL (L : List (Pc g)) : (n : ℕ) → Gn g n → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → Gn g n → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (degL L) p.2 (ih (degL L)) n) L

theorem hcL_nil (n : ℕ) : hcL ([] : List (Pc g)) n = fun _ => 1 := rfl

theorem hcL_cons (p : Pc g) (L : List (Pc g)) (n : ℕ) :
    hcL (p :: L) n = hc p.1 (degL L) p.2 (hcL L (degL L)) n := rfl

/-- Cuspidal class function on `GL_d(𝔽_g)`: irreducible and trivial on every Jacquet module. -/
def IsCusp {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  0 < d ∧ IsIrr χ ∧ ∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0

/-- Whittaker value of `χ`. -/
def wh (ψ₀ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) : ℂ := tr (eU g n ψ₀) χ

/-- Derivative of `χ` along the Whittaker character, as a function on `GL_m`. -/
def der (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g m → ℂ := fun h =>
  wh ψ₀ (res m (n - m) χ h)

/-- Gauss sum of a unipotent matrix (conjugation average of `ψ₀` on the superdiagonal). -/
def gg (ψ₀ : AddChar (ZMod g) ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if IsUniUp ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ψ₀ (∑ i ∈ Finset.range (n - 1), entN ((y⁻¹ * x * y : Gn g n) : Mt g n) i (i + 1)) else 0

/-- Kummer-type averaging element with a vanishing column condition. -/
def eJ' (g N : ℕ) [NeZero g] (k : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, a < k → entN M a k = 0)
    (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

/-- Labelling data for the irreducible characters of `GL_d(𝔽_g)`: an injective "Teichmüller"
lift `Fbar g → ℂˣ` and a compatible system of generators of `𝔽_{g^d}ˣ`. -/
structure LabelDatum (g : ℕ) [Fact g.Prime] where
  teich : Formalism.CyclotomicNorms.Fbar g →* ℂ
  teich_inj : ∀ x y, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y
  gen : ℕ → Formalism.CyclotomicNorms.Fbar g
  gen_order : ∀ d, 0 < d → orderOf (gen d) = g ^ d - 1
  gen_norm : ∀ d e, 0 < d → 0 < e → gen (d * e) ^ ((g ^ (d * e) - 1) / (g ^ d - 1)) = gen d

/-- The "theta" value `Σ_i teich(x)^{g^i}`-type constant attached to a root `z` of a prime
polynomial over `𝔽_g` (Green's character value at a regular elliptic element). -/
def thetaOf (L : LabelDatum g) (d : ℕ) (x z : Formalism.CyclotomicNorms.Fbar g) : ℂ :=
  if h : ∃ n : ℕ, z = L.gen d ^ n then L.teich x ^ h.choose else 0

/-- A monic irreducible polynomial of degree `d` with non-zero constant term. -/
def IsPrimeLab (d : ℕ) (P : (ZMod g)[X]) : Prop := P.Monic ∧ Irreducible P ∧ P.coeff 0 ≠ 0 ∧ P.natDegree = d

/-- `χ` is the cuspidal character labelled by the prime polynomial `P`: its values at
regular elements are given by `thetaOf` at the roots of `P`. -/
def IsCuspOf (L : LabelDatum g) (P : (ZMod g)[X]) {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  IsPrimeLab d P ∧ IsCusp χ ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly →
    ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly,
      χ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, thetaOf L d x (z ^ (g ^ i))

/-- `χ` has a label: it is a constituent of the Hecke averaging along `f`'s factorisation. -/
def HasLabel (L : LabelDatum g) {n : ℕ} (χ : Gn g n → ℂ) (f : (ZMod g)[X]) : Prop :=
  ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
    f = (Q.map Prod.fst).prod ∧ ip χ (hcL (Q.map Prod.snd) n) ≠ 0

/-- The "Serre" element: sum of the idempotents of the irreducible characters with label `f`. -/
def eSerC (L : LabelDatum g) (n : ℕ) (f : (ZMod g)[X]) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ᶠ χ ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}, zOf χ

/-- A weight ratio extracted from `eSerC`. -/
def wtC (L : LabelDatum g) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) (f : (ZMod g)[X]) : ℝ :=
  ((a * eSerC L n f).coeff 1).re / (a.coeff 1).re

/-- **Mainline layer-4 input (analytic):** for every `d ≥ 1` there is a labelling `τ` of the
prime polynomials of degree `d` by cuspidal characters of `GL_d(𝔽_g)`, with the prescribed
value at the identity, injective, and surjective onto the cuspidal characters.
This is the "Green's characters exist" hypothesis consumed by `plugWin`. -/
def Green : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (d : ℕ), 0 < d → ∃ τ : (ZMod g)[X] → Gn g d → ℂ,
    (∀ P, IsPrimeLab d P → IsCuspOf L P (τ P) ∧ τ P 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) ∧
    (∀ P P', IsPrimeLab d P → IsPrimeLab d P' → τ P = τ P' → P = P') ∧
    ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ P, IsPrimeLab d P ∧ χ = τ P

end GlobalTheory.GLq

end
