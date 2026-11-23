# 要加进 TauCetiRoadmap `RepresentationTheory/README.md` 的两段（不是整份文件）

> 这不是一份 README。这是路线图 `CharactersOfGLnOverFiniteFields` 作为 `RepresentationTheory` 的子路线图归位时，要加进 TauCetiRoadmap 现有的 `TauCetiRoadmap/RepresentationTheory/README.md` 的两段文字，写法照该文件已有的条目。父 README 是这次 PR 唯一动到的别人的文件：只加这两段，别的行不改。2026-11-23 由 GLM 5.4 通过 DeepSeek Harness 起草；下面的文字与在 TauCetiRoadmap 本地副本里实际加进去的逐行相同。

## 1. 在 "The roadmaps" 列表里加一条

放在 *Induction, restriction, and Mackey theory*（`InductionRestriction`）那条之后、*Induction theorems in Grothendieck groups of modular representations*（`ModularInduction`）那条之前：

```markdown
- [**Cuspidal characters of general linear groups over finite fields**](CharactersOfGLnOverFiniteFields/README.md)
  - the character theory of `GLₙ(𝔽_q)`: the standard parabolic subgroups and their unipotent
  radicals, Green's Möbius transform on the lattice of invariant subspaces, the virtual characters
  it produces, Harish–Chandra induction and the Jacquet restriction, the cuspidal support, and
  Green's classification of the cuspidal characters by the regular characters of the degree-`n`
  extension of the field and by prime labels.
```

## 2. 在 "How they depend on one another" 里加一条

放在 *Induction/restriction and Schur-Weyl feed character theory.* 那条之后、*Root systems → Lie highest weight → classical groups.* 那条之前：

```markdown
- **Character theory and induction feed the finite general linear groups.** CharactersOfGLnOverFiniteFields
  consumes CharacterTheory's class functions, pairing, virtual characters and norm-one test, and its
  `GL₂(𝔽_q)` table as the case `n = 2`, and InductionRestriction's induced class functions,
  Frobenius reciprocity and Mackey decomposition (Harish–Chandra induction from a standard parabolic
  subgroup is their induced class function). Its output, Green's classification of the cuspidal
  characters of `GLₙ(𝔽_q)`, is the finite-field input to the depth-zero block of the representation
  theory of `GLₙ` over a local field, which this family does not pursue (the
  [smooth representations of local groups](../SmoothRepresentationsOfLocalGroups/README.md) roadmap
  touches that block in rank one only).
```

## 3. 不改的地方

- 顶层 `TauCetiRoadmap/README.md` 的路线图列表、两个 issue 模板和根 `TauCetiRoadmap.lean` 由 bot 生成，没有写过这条路线图，不动。
- `RepresentationTheory/README.md` 的 "Scope and boundaries" 一节不动：普通特征标的归属（CharacterTheory）与这条路线图不冲突，边界写在子路线图自己的 "Not owned here" 里。
- 子路线图不带 `metadata.toml`，沿用父路线图的 topic（`math.RT`，见 `.github/scripts/check_roadmap_topics.py` 开头的说明）。
