# ROADMAP-PR — 给 De Song 的三段草稿（TASK.md 第 7 步 f）

> 三段都是**草稿**，由 De Song 本人改写后再发。按 Tau Ceti 的规矩（`TauCetiRoadmap/CONTRIBUTING.md`）：路线图 PR 的说明里要写明用了哪个模型；Nobody should post a roadmap or a review comment they have not read carefully themselves。下文凡是写"De Song 做了什么"的地方，都是**留给他确认或改写**的，我没有替他读过。
>
> 三段都用英文（PR、Zulip 帖、邮件的受众都读英文）。2026-11-23 由 GLM 5.4 通过 DeepSeek Harness 起草。

## 用法

| 段 | 发到哪里 | 发之前要做的 |
|---|---|---|
| ① | `TauCetiProject/TauCetiRoadmap` 的 PR：只动新目录 `TauCetiRoadmap/CharactersOfGLnOverFiniteFields/`（`README.md`、`Suggested.lean`、`metadata.toml`），**不要**手工改根 `README.md` 的路线图列表、两个 issue 模板和根 `TauCetiRoadmap.lean`（它们由 bot 生成）；PR 开好后在自己的 PR 下评论一行 `awaiting-review` | 通读 `README.md` 与 `ROADMAP-REVIEW.md` §6；按 TauCetiRoadmap 自己的 pin 重新 `lake env lean Suggested.lean`；跑 `python3 .github/scripts/check_roadmap_topics.py`；把 ① 里"Human review"一段改成实际做过的事 |
| ② | Lean Zulip，Tau Ceti 频道（`#Tau Ceti`），建议在 "Getting started: roadmaps" 话题或新开一个话题 | 先发 ③ 的邮件，或者至少决定好是否先联系 Alpöge；Zulip 帖子里不要替他表态 |
| ③ | 给 Levent Alpöge 的邮件（alpo.ge 上的联系方式） | 用 De Song 自己的名义与邮箱；附件可带 `ROADMAP-SURVEY.md` 的英文摘要（现在是中文，需要翻译或删去） |

---

## ① 路线图 PR 的说明

> 标题：`Roadmap: cuspidal characters of general linear groups over finite fields`

This PR adds one new roadmap, `TauCetiRoadmap/CharactersOfGLnOverFiniteFields/`, with its `README.md`, `Suggested.lean` and `metadata.toml` (`math.RT`). It touches nothing else; the roadmap list, the issue templates and `TauCetiRoadmap.lean` are left to the sync bot.

**What the roadmap builds.** The character theory of `GLₙ(F)` over a finite field `F`, up to Green's classification of the cuspidal characters (J. A. Green, Trans. AMS 80 (1955)): for a degree-`n` extension `K` of `F`, the characters of `Kˣ` whose conjugates under `θ ↦ θ^q` are pairwise distinct are in bijection with the cuspidal characters of `GLₙ(F)`, of degree `∏_{i<n}(q^i − 1)`, with the value `(-1)^{n-1} ∑_{i<n} θ(z^{q^i})` on elements with irreducible characteristic polynomial; consequently there are `(1/n) ∑_{d∣n} μ(d) q^{n/d}` cuspidal characters, indexed by the monic irreducible polynomials of degree `n`. The route is Green's: root-power-sums of polynomials, Möbius inversion over the lattice of invariant subspaces, the virtual characters so obtained, and a count through Harish–Chandra induction, its adjoint and the Mackey formula. Along the way: the counts of monic irreducibles, of subspaces and of cyclic vectors; the pairing of class functions on `GLₙ(F)`; the Jacquet restriction and Frobenius reciprocity; the existence and uniqueness of the cuspidal support of an irreducible character.

**Why this roadmap, and why now.** It builds on [RepresentationTheory.CharacterTheory](../RepresentationTheory/CharacterTheory/README.md) (class functions, the pairing, virtual characters, the norm-one test) and consumes its `GL₂(𝔽_q)` table as the case `n = 2`; it says explicitly what it does not do (Zelevinsky's classification, Deligne–Lusztig theory, smooth representation theory). It is meant as the first of a series bringing the main line of the Alpöge–Claude formalization of the Riemann hypothesis (<https://alpo.ge/>, 2026-11-20) into Tau Ceti layer by layer: Green's classification is the finite-field input of that proof (its statement is `GlobalTheory.GLq.Green` in the source), and the only part of the main line whose statement *and* proof depend on Mathlib alone. The remaining layers are outlined in a section marked *Roadmap for a roadmap (not work to attempt now)*, with the existing roadmaps each would consume; nothing in it is a target.

**Relation to existing roadmaps.** No existing roadmap states Green's classification for general `n`; `RepresentationTheory/CharacterTheory` Layer 9 has `GL₂(𝔽_q)` only and says the Deligne–Lusztig theory is not planned there. The top of the Alpöge–Claude main line (zero-free half-planes, GRH for Dirichlet `L`-functions, the bridge to `RiemannHypothesis`) is already owned by `QuasiRiemannHypothesis` §1.1, §5.5, §11.1 and `ZerosOfLFunctions` Layer 9, so this series does not restate it.

**`Suggested.lean`.** It compiles with `lake env lean` against Mathlib master (`leanprover/lean4:v4.37.0-rc1`) with no errors; the only output is the expected `declaration uses 'sorry'` warnings (31 theorems; every `def` has a real body). It imports Mathlib only; the Tau Ceti interfaces it should use (`TauCeti.ClassFunction.characterPairing`, `TauCeti.virtualCharacters`, `TauCeti.irreducibleCharacters`, the `GL₂` table, induced class functions and Mackey theory) are named in the markdown.

**Self-review.** A self-review by the drafting model against the four aspects of CONTRIBUTING.md and the *Writing a roadmap* checklist is available on request (in Chinese); its main caveats: (1) the choice of Green's classification as the first roadmap of the series is a judgement call; (2) the routes of §7.7(d) (every cuspidal induction has a generic constituent) and §7.8 (at most `qⁿ − qⁿ⁻¹` generic irreducible characters) are only sketched, and I would particularly welcome review of those; (3) the bibliographic details of the references were not checked online.

**Human review.** [To be completed by De Song: which parts of the README and `Suggested.lean` were read and checked by hand; which subject-matter experts, if any, were consulted.]

**AI assistance.** Drafted by **GLM 5.4** through **DeepSeek Harness**, directed by De Song. The model read the rules of the three Tau Ceti repositories and the neighbouring roadmaps, surveyed the library and the roadmaps for overlap, read the relevant parts of the Alpöge–Claude formalization, and wrote from the standard accounts of Green's theorem (Green, Zelevinsky, Macdonald, Digne–Michel); it wrote `README.md`, `Suggested.lean` and `metadata.toml`, compiled `Suggested.lean`, and wrote the self-review. The mathematical content is Green's; the Lean statements are suggested forms, not taken from any existing code.

**Attribution and licence.** The mathematics follows Green (1955), Zelevinsky (1981), Macdonald (1995) and Digne–Michel (2020), cited in the README. The *Provenance* section maps the statements to the Alpöge–Claude formalization as a cited source only; that release carries no licence file, and the README says that nothing may be ported from it before its author has been consulted. The author is being contacted separately.

## ② Zulip 帖子（Tau Ceti 频道）

> Topic: Getting started: roadmaps (or: **A roadmap series for the Alpöge–Claude proof**)

Hi all — I'd like to gauge reaction before opening a roadmap PR.

**The plan.** The Alpöge–Claude formalization of RH (alpo.ge, 2026-11-20; ~17.4M lines of Lean on top of Mathlib) is one connected block: the main line runs from Galois representations attached to automorphic representations via theta lifts, through an automorphic-window statement and a large package of analytic hypotheses, to "every primitive Dirichlet `L`-function is nonvanishing on `Re s > 1/2`", and from there to `RiemannHypothesis`. I'd like to bring the reusable parts into Tau Ceti as a **series of roadmaps**, one layer each, so that the intermediate statements become citable from a library.

**What exists already, and what does not.** The last step (zero-free half-planes, GRH for Dirichlet `L`-functions, the bridge to Mathlib's `RiemannHypothesis`) is covered by `QuasiRiemannHypothesis` and `ZerosOfLFunctions`. The first-layer statement (Galois representations attached to regular algebraic cuspidal representations on unitary groups) is already a goal of `AutomorphicGaloisRepresentationsPartII`, by the cohomological route; the proof I'd port reaches it by theta lifts, so that layer needs coordination before any roadmap is written. The analytic core (theta-lift chains, the determinant positivity, periods and masses) has suppliers in `MetaplecticAutomorphicForms`, `GanGrossPrasadUnitaryGroups`, `ArakelovGeometryAndAbelianHeights` and others, but no roadmap states its goals. A few inputs have no roadmap at all (a weakened Vandiver obtained by twisting, iterated theta lifts between definite unitary groups, the hermitian Siegel mass formula, Bost's slope inequality, primes of an imaginary quadratic field in short intervals).

**The first roadmap.** The one part of the main line that is proved from Mathlib alone, and that Tau Ceti does not have, is its finite-field input: Green's classification of the cuspidal characters of `GLₙ(𝔽_q)` (`GlobalTheory.GLq.Green` in the source). I have drafted a roadmap for it — the class-function theory of `GLₙ(𝔽_q)` up to Green's theorem and the count of cuspidal characters, consuming `RepresentationTheory/CharacterTheory` and its `GL₂(𝔽_q)` table — with a `Suggested.lean` that compiles against Mathlib master with only `sorry` warnings, and a section marked as a roadmap-for-a-roadmap for the remaining layers. I'll open the PR once I've read it through myself.

**Two questions.**
1. Is this the right way to contribute the reusable parts of that proof — a series of roadmaps, starting from the finite-field end — or would you rather see the layers in a different order (e.g. the statement layer first)?
2. The original release has **no licence file**. The roadmap cites it as a source and does not port any code; I'm writing to Levent Alpöge to ask how he'd like his work to be used and under what licence. If anyone here has discussed this with him already, or has thoughts on how Tau Ceti should treat material from that release, please say so.

Drafts (roadmap, survey, self-review) are available; the PR description will say which models were used.

---

## 三段都没写的（留给 De Song 决定）

- 没有提 `CocoSgt/rh-mathlib-lemmas` 仓库与三个 Mathlib PR 的链接：②③ 里提"three small pull requests"就够，是否给链接由你定。
- 没有替 De Song 承诺任何时间表或"我会亲自维护这个系列"。
- ② 里的"working with the GLM model"与 ① 的 AI 说明一致；如果你在发之前改用了别的模型，两处都要改。
