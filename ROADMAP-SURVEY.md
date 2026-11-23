# ROADMAP-SURVEY — Alpöge–Claude 证明主线的调研与范围选择（TASK.md 第 7 步 a、b）

> **功劳与署名**：证明的全部数学属于 **Levent Alpöge（与 Claude 合作）**，2026-11-20 发布于 <https://alpo.ge/>，原样镜像见 `source/`（<https://github.com/CocoSgt/riemann-hypothesis-lean>）。本文只做阅读、转述与选范围，没有新的数学。调研与起草由 **GLM 5.4 通过 DeepSeek Harness** 完成（其中 5 个子代理各写了一份笔记，见 §1.2）。原发布没有 license 文件（REPORT.md §5.6）。
>
> 本文用中文；路线图正文（`roadmap/CharactersOfGLnOverFiniteFields/README.md`）用英文。标「确定」的是逐行读过陈述的；标「很可能」「猜测」的请按 §6 处理。

## 0. 结论

1. **主线五层**（SKELETON.md §1，逐行核对过）：L1 Galois 表示（`Row0b`、`RecTExists`）→ L2 自守窗口 `VWin` + `Green` + 解析假设 `HypsAlt … DefiniteSideCondition` 非空 → L3 `ZeroFreeAll`（每个**本原** Dirichlet L 函数在 Re s > 1/2 无零点）→ L4 `EveryCharacter`（**所有** Dirichlet L 函数）→ L5 `RiemannHypothesis`（Mathlib 的定义）。L2 → L3 那一环在源码里是 `zero_free_all_of_green_v_win`（`ThirdPlaceSeries/TopPlug.lean:12`）= `imprimitive` 之后接 `zeroFreeAll_of_topG`：由 Green 得到「形状」定理 `TopG`，由 `VWin` 供给每个本原特征的主机（`supplyChi`），再用 Dirichlet L 函数的磨光显式公式 + Landau 定理得到零点自由。
2. **哪些是新的**（§3）：L3 以上的衔接、显式公式与 Landau、Green 分类、LLC、Siegel–Weil、倍乘法等都是教科书或已发表定理；**新的是把 `Green + VWin + Hyps` 变成 `ZeroFreeAll` 的整条解析链**（θ 提升链、定号行列式、bootstrap、Iwasawa 塔上"用扭曲消去"的弱化 Vandiver、周期与体积计算），它占证明的绝大部分，而且其陈述要几千个自定义定义。
3. **Tau Ceti 覆盖**（§4）：顶层衔接已被 `QuasiRiemannHypothesis`（§1.1、§5.5、§11.1）和 `ZerosOfLFunctions`（Layer 9）覆盖；L1 的结论有上同调路线的路线图 `AutomorphicGaloisRepresentationsPartII`（库里未实现）；L2 的各种文献输入在 `MetaplecticAutomorphicForms`、`GanGrossPrasadUnitaryGroups`、`IntegralIwasawaTheory`、`ArakelovGeometryAndAbelianHeights` 等里有目标，但几乎都没有实现；解析核心（`Hyps`、`TopG`、`supplyChi`）没有对应目标。**`Green`（Green 1955 对 GL_n(𝔽_q) 尖特征标的分类）在 Tau Ceti 没有目标**，库里只有 GL₂(𝔽_q) 的特征标表。
4. **选定的范围**（§5）：第一份路线图做 **GL_n(𝔽_q) 的类函数与 Green 的尖特征标分类**（`roadmap/CharactersOfGLnOverFiniteFields/`）。它是主线上唯一同时满足「陈述与证明只依赖 Mathlib」「Tau Ceti 没有」「可复用」的一块；其余各层写成明确标注的 roadmap-for-a-roadmap。

## 1. 读了什么

### 1.1 规则与格式

| 文件 | 读到的要点 |
|---|---|
| `TauCeti/README.md`（全文，重点 Collaboration） | Tau Ceti 是 AI 写代码、人写路线图、AI 按 rubric 对抗审稿的库；前沿成果有人登记意向就让路，基础材料不等；依赖 Mathlib master、不往 Mathlib 推东西；Apache 许可 |
| `TauCeti/AGENTS.md`（全文） | 新数学必须对应路线图的具名目标；库代码禁 `set_option`、禁 `maxHeartbeats`；不留兼容别名；每个 PR 一行 `Roadmap: <Area>`；不许 agent 自己开 TauCetiRoadmap 的 PR/issue |
| `TauCeti/COORDINATION.md`（全文） | 代理之间的分支写入、claim、合并规则（本次都用不到：我们不在 Tau Ceti 的任何仓库写东西） |
| `TauCetiRoadmap/README.md`（全文） | **Writing a roadmap**：Build the library、No gaps、每条无歧义、边界清楚、不写 optional/deferred/later、路线图要 timeless、可复用；**Working with Mathlib**：用 Mathlib 的词汇、尊重 Mathlib 的设计、但不等它、不往它推；**Porting existing work**：写数学不写代码结构、先与作者协调、改进而不是照抄、逐文件对照放在次要的 provenance 一节；**Laying out the README**：`**Summary.**` 开头、`## Conventions`、`## Layer k`、Scope and ownership、Exact supplier contracts、References；**Prototyping**：`Suggested.lean` 开头写标准说明、诚实用 `sorry`、不用 `Prop` 字段或 `def _ : Prop := sorry`；**Filing**：`metadata.toml` 的 arXiv 主类 |
| `TauCetiRoadmap/CONTRIBUTING.md`（全文） | 审路线图四方面；**AI 辅助要在 PR 说明里写明用了哪个模型**；PR 只动自己目录；不要尾部拖一个欠规格的大扩展，要写就明确标成 roadmap-for-a-roadmap；找领域专家 |
| `TauCetiReview/rubrics/{README,_common,scope,attribution,correctness}.md`（全文） | 这是审**实现 PR** 的规则：PR 必须引用路线图文件和目标；不得出现占位（`True` 型字段）、不得有未被使用的谓词（新 `Prop` 必须有消费它的定理或非平凡见证）；代码里要注明形式与非形式来源；路线图本身不能只在 PR 说明里署名 |
| 相邻路线图 | `WeilPositivityAndLiCriterion`（605 行全读）：Summary→Conventions→Layer（Define/Prove/Route/Checks/Needs/Examples/Dependencies）→Scope→Exact supplier contracts（From Mathlib / From Tau Ceti / From TauCetiRoadmap.X）→References；`QuasiRiemannHypothesis`（概述、Layer 1、5、11、Downstream consumers、Owned here）：层内每个引理都有带常数的陈述和 route；`ZerosOfLFunctions`（概述、Layer 9、Provenance、Scope）；`LFunctions`、`AnalyticNumberTheoryPartIII` 的结构；`RepresentationTheory` 索引（它是一族子路线图）；`RepresentationTheory/CharacterTheory`（Conventions、Layer 0、Layer 9 的 GL₂(𝔽_q)）；`CFSGStatement`（"只陈述不证明"的路线图先例） |

### 1.2 调研笔记（`.run/step7-roadmap/`，不入库）

- `survey-S2.md`（642 行）：`PChar`/`KSet`/`Level`、`TopG`/`supplyChi`/`HostExW`、`VVle`/`IsChiField`/`WinPair`、`ShortNorm`/`SmallOne`、磨光显式公式与 Landau、CharacterBoxes 其余文件。
- `survey-S3.md`（182 行）：`GlobalTheory.Published.*` 文献包（主 bundle `HypothesesUE` 71 字段，其中 63 条是文献命题）、`OpenLiteratureStatements`（3 个开放输入）、短区间素数。
- `survey-T2.md`（423 行）：自守/Langlands 侧 12 个主题与现有路线图的对照（带 README 行号与实现状态）。
- `survey-T3.md`（244 行）：算术核心 8 个主题的对照；其中 U6 明确回答了 Green 分类在 Tau Ceti 没有目标。
- 两个源码调研子代理（L1 与 VWin 的定义链；顶层衔接）中途失败，这两部分由本会话自己读（`skeleton/src/Skeleton/Top/*`、`PChar.lean`、`LabelDatum.lean`、`Hyps.lean`、`DefiniteSideCondition.lean`、`TopPlug.lean`、`ZeroFreeAllOfTopG.lean`、`SupplyChi.lean`、`Supply.lean`、`CharacterTheory/*Statement.lean`、`InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean` 等）。作者的四页说明取自 <https://alpo.ge/remark.pdf>（存为 `remark.txt`）。

## 2. 主线每一层是什么数学

记号：`q` 素数或素数幂，`χ` Dirichlet 特征，`L(s, χ) = DirichletCharacter.LFunction χ s`（Mathlib）。

### 2.1 L5：黎曼猜想

- **命题**：Mathlib 的 `RiemannHypothesis`（`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`：ζ 的每个非平凡零点实部为 1/2）与 `Statements.lean` 的另外三条：ζ 的零点在临界线上、每个 Dirichlet L 函数在 Re s > 1/2 非零、Dirichlet L 函数在临界带内的零点在临界线上（`PrimitiveDirichletLZerosOnLine` 只对本原特征）。**确定**
- **衔接**（`Main.lean:4-12`、`Supplements/Kernels/MainTheorems.lean`）：`rh_of_right`（ζ 在 Re s > 1/2 非零 ⇒ RH，`Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`）、`rh_of_every` 与 `critLine`（`CritLine.lean:6-32`）、`riemannHypothesis_of_everyCharacter`（`CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:211-215`）、`Claim.strip/zeta`（`CharacterBoxes/ClaimStrip.lean`）。数学内容：由函数方程与 Γ 因子非零，临界带内的零点关于 `ρ ↦ 1 − ρ̄` 对称，所以「右侧无零点」⇔「全部在临界线上」。**确定**

### 2.2 L4：所有 Dirichlet L 函数在右半平面非零

- **命题**：`UpperTheory.EveryCharacter`（`CharacterBoxes/EveryCharacter.lean:13`）：对任意模数 N 与特征 χ，Re s > 1/2 且（χ ≠ 1 或 s ≠ 1）时 `L(s, χ) ≠ 0`。**确定**
- **衔接**：`imprimitive`（`CharacterBoxes/Imprimitive.lean:5`）：非本原特征的本原化 χ₀ 满足 `L(s, χ) = L(s, χ₀) · ∏_{p | N, p ∤ N₀} (1 − χ₀(p) p^{−s})`（Mathlib `DirichletCharacter.LFunction_changeLevel`），右边的有限乘积在 Re s > 0 时非零。**确定**

### 2.3 L3：每个本原 Dirichlet L 函数在 Re s > 1/2 无零点

- **命题**：`Formalism.HC.ZeroFreeAll`（`TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`）= 对每个 `PChar`（本原特征连同其导子，`PrimePairSizeCondition.lean:7-11`）有 `PChar.ZeroFreeAbove (1/2)`。由函数方程，这就是 **Dirichlet L 函数的 GRH**。**确定**
- **包装**：`KSet`（含 1、对逆封闭的有限个本原特征，外加至多一个奇实特征 `psK`）、`Level`（`KSet` + 阶 `o`）、`Level.cyc ψ`（单个特征生成的循环子群）、`zeroFreeOn_of_cyc`（逐循环子群归并）。`psK` 与 `Level.Gm`/`ChebyshevGrowthImpliesZeroFree` 的形状指向 Landau 例外实零点的隔离与「Chebyshev 型上界 ⇒ 零点自由区域」（Landau/Ingham）。**陈述确定；含义很可能**

### 2.4 L2 → L3：`zero_free_all_of_green_v_win`（证明的解析出口）

`UpperTheory.Top.zero_free_all_of_green_v_win (hG : Green) (hV : VWin) (h : Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DefiniteSideCondition)) : ZeroFreeAll`（`ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12-15`）。它分三路（`survey-S2.md` 条目 2、3）：

1. **形状**：`shape_closed_link_n_of_green : Green → TopShapeAlt True True (Closed LinkN) TopG`（`ThirdPlaceSeries/TopShape.lean:33`），再由 `forall_goal_of_shape_of_hyps` 从 `HypsAlt` 非空拆包得到 `TopG`（`CharacterBoxes/ZeroFreeAllOfTopG.lean:12`）。`TopG` 说：对任意"要求" `G : FReq`，只要每个尺度上都能用参数一致有界的**主机**（host：导子 + Artin 映射 + 特征集）实现它，且相应的族类里每个族满足假设 V，那么这个族类是"连通"的：类里有族，其整个窗口被 Weil 型**链**（theta 提升链）绑定，误差常数一致。`TopShape` 是带约 60 个前提的蕴含式，`shape_of` 是纯拆包引理。**陈述确定；正性（定号行列式）藏在哪里没读到**
2. **供给**：`supplyChi : ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req`（`CharacterBoxes/SupplyChi.lean:8`）：对每个本原特征 ψ，在假设 V 的窗口版本下，每个尺度上都有主机携带 ψ 的循环 level，且满足显式公式误差条件 `EAtH`（`TT` 是 `x^{−1+ε}`-近似设计、逐点界 `‖g_χ(x)‖ ≤ x^{1/2+ε}`、`‖L'/L(1,χ)‖ ≤ 4 log x`）。`supplyOfAdmOf`（`ShortNorms/supplyOfAdmOf.lean:13`）用 `VWinAt` 与均方界（`MeanSquareBounds/pairEx`）造出素数对 `(q, d)`（`q ≡ 3 (8)`、`d ≡ 7 (16)`、`q | d+1`、所有小素数整除 `d+1`）与**特征域** `IsChiField ψ e q d E`（ℚ(ζ_N) 的全实子域，含分圆 ℤ₂-扩张的第 e 层、ker ψ 的域与 ℚ(√d)），用到的解析输入是**短区间中的素数**（`ShortNorm`：`[X, X(1+h)]` 中素数个数 ≥ c′hX/((4dM²)^A log X)，h ≥ exp(−c√log X)；完整陈述 `Proofs/GlobalInterpolation/NormPrimesImagQuadShortIntervalLowerBound.lean:98`：虚二次域 ℚ(√−d) 中范数在短区间里、≡ 1 (mod M) 的素元）与 **Linnik 型** `SmallOne`。**陈述确定；"虚二次域范数素数"很可能**
3. **显式公式**：`zeroFreeAll_of_topG`（`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`）用 `zeroFreeOn_of_tiedWin_cyc`（`TotientGaloisClasses/TopWin.lean:90`）：`EAtH` 型条件 + 链绑定 ⇒ Chebyshev 不等式 `Λ.Gm x ≤ x^{1/2 + (e_D + e_L + 7)ε}`（`TopDefs.lean` 的 `ChebyshevInequalityForFamily`）⇒（`Landau.lean`、`Formalism/ZetaNonvanishing/ZetaLandau`）`Re s > 1/2 + cε` 零点自由 ⇒ 令 ε → 0。显式公式本身是 **Dirichlet L 函数的磨光版**（`TotientGaloisClasses/Analytic.lean:14-24`）：`G(y) = Σ_{n ≤ y} Λ(n)(y/n − 1)₊ − y(log y − 1 − γ)`，`g_χ(y) = Σ_{n ≤ y} Λ(n)χ(n)(y/n − 1)₊ + y L′(1,χ)/L(1,χ)`，核 `(1 − t)₊` 的 Mellin 变换是 `1/(s(s+1))`，零点 ρ 贡献 `y^ρ/(ρ(ρ−1))`。**确定**

所以 L2 → L3 的数学是：**用自守/算术几何的方法对一族 twisted von Mangoldt 和证明平方根品质的 Chebyshev 型上界，再用显式公式 + Landau 得到零点自由**。

### 2.5 L2 的三个输入

**(a) `GlobalTheory.GLq.Green`**（`Definitions/NonGaloisDescent/LabelDatum.lean:108-112`）：对每个素数幂 g、标签数据 L、d > 0，存在从 `(ZMod g)[X]` 到 `GL_d(ZMod g) → ℂ` 的映射 τ，使得每个 d 次**素标签**（首一不可约、常数项非零）P 给出一个尖特征标 `τ P`（`IsCuspOf L P`：尖、不可约，且在特征多项式不可约的元素 y 上 `τ P y = (−1)^{d−1} Σ_i θ_x(z^{g^i})`，x 取遍 P 的根、z 取遍 y 的特征多项式的根），`τ P 1 = ∏_{i=1}^{d−1}(g^i − 1)`；τ 在素标签上单射；每个尖特征标都是某个 `τ P`。这就是 **J. A. Green 1955 对 GL_n(𝔽_q) 尖特征标的分类**（`Gn g d = GL (Fin d) (ZMod g)`，`IsCusp χ`：不可约且对每个 0 < a < d，沿单幂根 `U_a` 的和为 0）。**确定**（陈述逐行读过；源码里 `Published.GreenRegularCharacters` 是等价形式，证明在 `Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:137`）。
证明路线（源码 `Proofs/CharacterTheory/` 103 条陈述 + `InertiaEigenvalues` 的 Green 部分，几乎只 import Mathlib）：对代数闭包上的 Teichmüller 特征 θ 与 k 定义根幂和 `rootSum θ k P = Σ_{P(α)=0} θ(α)^k`（可加）；对 End(V) 上的 `g` 用**不变子空间格上的 Möbius 反演**定义 `ψ s V g = s(charpoly g) − Σ_{W ⫋ V} ψ s W (g|_W)`；证明 ψ 是类函数、是"本原"的（沿抛物子群幂根的和为 0）、在不可约特征多项式上等于 s、质量公式 `mass (ψ s) P = |GL_n| · Λ_s(P)/(q^n − 1)`；`rootSum θ k ∘ charpoly` 是虚拟特征标，与 ψ 的配对 = `|GL_n| · #{i < n : k q^i ≡ l}`；本原类函数在根幂和上的展开系数是整数；k 正则时 `(−1)^{n−1} ψ (rootSum θ k)` 的自配对为 1，因而是不可约尖特征标；满射性用 **Harish–Chandra 诱导**：尖特征标的 list 的诱导 `hcL` 是真特征标，Mackey 配对公式（不同的多重集配对为 0，无重复时为 1），广义（Whittaker 泛函非零）成分互不相同且个数 ≤ 共轭类数 `q^n − q^{n−1}`，于是尖特征标的多重集个数 ≤ `q^n − q^{n−1}`，再把「所有 d 次首一多项式 → 标签」的映射与之比较得到矛盾式的计数。**确定**

**(b) `UpperTheory.Top.VWin`**（`CharacterBoxes/ExistsPageN.lean:49`，`skeleton/src/Skeleton/Window/VWin.lean` 是 Mathlib-only 版本）：对每个本原特征 ψ，`VWinAt ψ 401`：对每个 `ε ∈ (0, 1/52)`、每个 `2^{e(x)} ≈ x^{2+8ε}` 的 e，存在 J ≥ 1 与 X₀，使得对一切 X ≥ X₀ 与每对满足 `WinPair ε (X^{1/J}) q d` 的 `(q, d)`，存在 `Y ∈ [X^{1/J}, X^{1/2}]`，对一切 `x ∈ [Y, Y²]` 与每个**特征域** `E`（`IsChiField ψ e q d E`）有 `VVle E ⌊x^{401}⌋ √(exp(x^ε))`。`VVle E t B`：对每个代数闭包 Ω 与每个素数处的局部数据，(i) 对所有 ℓ 与 `1 ≤ e < t`，Galois 上同调群（`Formalism.GaloisCohomology.shaLen`，取值 ℕ∞）有限；(ii) 对任意有限素数集 S，`Σ_{ℓ∈S} (log ℓ) · Σ_{1 ≤ e < t} shaLen ℓ e ≤ B`。结合作者说明第 17 条（"the classes in H¹(…, ℚ_ℓ/ℤ_ℓ(−e)) that we couldn't kill by twisting, fight for a significant weakening of Vandiver"），这是 **Iwasawa 塔上 ℓ 进 Galois 上同调群（类群 ℓ 部分 / Kummer 理论）总长的界**，V 很可能指 Vandiver。**陈述确定；数学含义很可能；`shaLen` 的定义未读**

**(c) `HypsAlt … DefiniteSideCondition` 非空**（`ThirdPlaceSeries/Hyps.lean:22-90`，40 个字段；`DefiniteSideCondition.lean:25`）：对一族（`FamClass`）带 CM/酉数据的算术几何对象，要求：有界的实现实、类数公式（`StandardLattice.ClassNumberFormula₂`）、genus 质量（`GenusMassVolumes.VolSigIndep`、`GenusMassAt D 2`、`MassRatioUnderVolume`）、格点计数（`CountAllPointsClass`）、扭曲周期与点积分的可容许性（`TwistedPeriodAdmissible`、`TwistedPointIntegral`、`PeriodClassSumWeyl`）、谱的行正性（`RowsPos`、`TheoremSSelected`）、衰减（`WuDecayOfGap`）、以及沿族"最终成立"的主假设 `Closed 𝒞 (fun Fm _ => LinkN Fm)`。非空性由 `nonempty_hyps_definite_side_of_closed_bound`（`SiegelEisensteinSecondTermHypotheses.lean:44`，主线最大的单块：证明锥 ≈ 44 万条声明）从文献包推出；`every_character_of_theta_integrals_local_matching`（同文件 `:69`）再用它。**陈述确定；各字段含义只按名字转述**

### 2.6 L1：Galois 表示与局部 Langlands

- **`UpperTheory.GalStar.Row0b (fun h rc => IsRecT h rc)`**（`Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`）：对 CM 域上每个正则代数、极化、本质平方可积的尖表示 π（`CuspSub`/`CG`/`PolarizedPair` 等）附带一个 ℓ 进 Galois 表示 r（带权 `wt`、Hodge–Tate 权重 `HT`），满足一组局部–整体相容条件 `PropsB`/`AboveB`（用 Weil–Deligne 表示 `WD`、p 进 Hodge 数据 `LocBridge`/`LocAinf`/`PeriodData` 表述），并且局部上满足与 `IsRecT` 相容的递归规律。**很可能**（`survey-S1` 未返回；依据 SKELETON-lower.md 的定义链与 REPORT §1.3）
- **`UpperTheory.Zero.LLC.RecTExists`**（`Foundations/LocalLanglands/IsRecTOfIsRec.lean:78`，`LocalCentralUnits/RecTExists.lean:20`）：对每个 `(E, Ω, A, w)` 存在满足 `IsRecT h rc` 的局部 Langlands 型递归映射（`LawsT` 的 `langlands`/`dual`/`depth` 字段用到 Bernstein–Zelevinsky 的段与抛物诱导 `SmGL.*`）。**很可能**
- **衔接**：`galoisLocalGlobalStrong_recParameter := galoisRepresentations_of_thetaLift TP.K.tLiftK`（`IntegralStructures/RowSrc.lean:6`）：**经 θ 提升**构造 Galois 表示；`vwin_of_row := automorphic_window_of_inputs (OpenImageCondition.mk h) baseChangeN h`（`VwinOfRow.lean:4` → `TopMainZj.lean:71`）：由 `Row0b` 推出自守窗口 `VWin`（用基变换 `baseChangeN`）；`every_character_of_row := every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)`（`CharacterBoxes/MainConclusion.lean:7-11`）。**确定**（陈述）
- **开放输入**：`OpenImageCondition`（`…/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207`）只有 1 个字段 `galoisRepOfPolarizedPairLit : UpperTheory.V.Z.Win.RowT`；`OpenLiteratureStatements`（`ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215`）只有 3 个字段：`caraianiLocalGlobalDual`、`localLanglandsExists : RecTExists`、`galoisRepOfPolarizedPairLit`；`every_character_of_literature_of_vWin (O) (hV : VWin) : EveryCharacter`（`:810`）= `every_character_of_theta_integrals_local_matching (published_results_eigen O) (published_results_first O) (theta_integrals_agree_and_local_matching_of_literature O)`。**确定**

### 2.7 文献包

`GlobalTheory.Published.*` 共 493 个陈述文件（`PublishedTheorems/` 21 个子目录），主 bundle `HypothesesUE`（`Definitions/Divisors/HypothesisBundleConversions.lean:56`）71 字段，其中 63 条文献命题，分六组（`survey-S3.md` §2 逐条给了 file:line）：(1) GL_n(𝔽_q)/深度零：Green、Bernstein–Zelevinsky（余极小核、泛型酉对偶、多项式环、有限性、几何引理）；(2) GL 自守谱：Speh 分类、Jacquet–Shalika 刚性与界、Flath、尖形式快速衰减、尖谱迹类；(3) ℓ 进 Galois 表示与局部–整体：Clozel、极化尖表示的 Galois 表示、base change（Labesse）、Bhatt–Scholze、Hecke 特征标的 ℓ 进实现、局部 Tate 对偶与 Euler 特征；(4) 类域论：Artin 互反、Weber、Chebotarev；(5) 酉群/θ/Siegel–Weil：Siegel–Weil、正则化首项、倍乘法（Lapid–Rallis、Yamana）、Howe 对偶、Labesse–Waldspurger、Bessel 唯一性、SU 强逼近；(6) 实群（Harish–Chandra）：解析性、特征标、Langlands 分类、离散序列、形式度、Dixmier–Malliavin、Schur 正交。部分命题在库内有证明（`globalArtinReciprocity`、`greenCuspidal`、`greenRegularCharacters`、`harishChandraModules`），其余以假设 bundle 的形式进入。**确定（清单）；"哪些已被 discharge"未核实**

## 3. 整体策略与哪一步是新的

作者的四页说明（`remark.txt`）给出的线索（**全部是作者自己的简述，我只把它与代码结构对照，没有核实证明**）：

- **Stepanov 的后代**：函数域上 Stepanov 的证明靠"带重数的除子"；数域上没有重数，相当于"对整数求导"。新的做法是**链式 θ 提升** `U(X₀) → U(X₁) → ⋯ → U(X_m)`（全定酉群之间），`π ↦ π ⊞ μ_j[t]`，用 m 次提升模拟重数；对长度 X 的 von Mangoldt 和取 `m ≈ √X`。对应源码：`ThirdPlaceSeries`、`ChainTied`、`eDiv`/`eLoss`（每次提升的"代价"）。
- **定号行列式**：`W(1_S) ≥ 0` 由行列式得到，解释成"重数 1 的 Stepanov"，再 bootstrap：`W·1_{(0,1]} + (∼X^η)·1_{(0,1/X]} ≥ 0` 给出 `> 1 − η`。对应：`RowsPos`、`TheoremSSelected`、`Separation…`（?）。
- **Guinand–Weil 的符号、方差检验函数技巧**：对应 `MeanSquareBounds/`（twisted von Mangoldt 和的均方界，`survey-S2.md` 条目 4）。
- **Iwasawa 塔**（类比 `𝔽_q^n/𝔽_q` 上的抽屉原理）、"用 Behrend 选塔"、**弱化 Vandiver**（ twisting 消不去的 H¹ 类）、Bost 斜率不等式、Chowla–Selberg/Weyl/Siegel 质量、周期是 Bessel 周期（Rallis、see-saw）、相对迹公式、`GL₅` 的六重覆盖、整结构的"gcd"、协体积与 θ 级数的指数、提升之间的同余。对应：`VWin`/`VVle`/`IsChiField`、`HypsAlt` 的各类字段、`HypothesesUE` 的文献输入。

**教科书 / 已发表**（按上面的对照）：L3 以上的全部衔接与显式公式、Landau、de la Vallée Poussin；Green 分类；LLC（GL_n：Harris–Taylor、Scholze）；Clozel；base change；Siegel–Weil、倍乘法、Howe、Jacquet–Shalika、Labesse–Waldspurger、Harish–Chandra、Dixmier–Malliavin、Flath、Bhatt–Scholze；Artin 互反、Chebotarev、Tate 局部对偶；短区间素数、Linnik；类数公式、Siegel 质量公式；Faltings/Colmez 高度、Chowla–Selberg、Bost；奇点消解、Moriwaki、Poincaré–Lelong、L² ∂̄；ℤ 的 K 群（Lichtenbaum–Quillen 一线）。

**这份证明独有的新路线**：把上面这些拼成 `Green + VWin + Hyps ⇒ ZeroFreeAll` 的整条链（§2.4–2.5），尤其是 θ 提升链的重数模拟、定号行列式与 bootstrap、塔上"用扭曲消去"的弱化 Vandiver、以及 `Row0b` 经 θ 提升构造 Galois 表示。这部分没有任何教科书对应，陈述需要几千个自定义定义（`HypsAlt` 陈述锥 2,853–7,034 条，`TopG` 约 1,380 条）。

## 4. 每层的覆盖情况

「实现」一列来自各路线图目录有没有 `STATUS.md`（没有就是一行都没落地；T2/T3 的核对）。

| 层 / 材料 | 教科书还是新 | Tau Ceti 路线图（文件、目标） | 库内实现 | Mathlib |
|---|---|---|---|---|
| L5 RH、L4/L3 的陈述与衔接 `rh_of_right`、`imprimitive`、`critLine` | 教科书 | `QuasiRiemannHypothesis` §1.1（`ZeroFreeRightOf σ f`，含 Dirichlet L 函数的读法）、§5.5（本原 ⇒ 所有 Dirichlet 特征，用 `LFunction_changeLevel`）、§11.1（零点带；θ = 1/2 即 GRH）；`ZerosOfLFunctions` Layer 9（GRH 的除子陈述 ≡ `RiemannHypothesis`）；`LFunctions` Layer 4（Dirichlet L 函数与因子分解）；等价形式在 `WeilPositivityAndLiCriterion` | 未实现（ZerosOfLFunctions Layer 9 未动） | 有：`RiemannHypothesis`、`DirichletCharacter.LFunction`、`LFunction_changeLevel`、`IsPrimitive.completedLFunction_one_sub`、`riemannZeta_ne_zero_of_one_le_re` |
| L3 `PChar`/`Level`、`ChebyshevGrowthImpliesZeroFree` | 教科书 | 同上（QuasiRH 的零点自由判别）；Landau 型引理：`AnalyticNumberTheoryPartIII` §8.3、§10.2 | 部分 | 无 `PChar` 这种包装（本原特征用 `χ.IsPrimitive`/`primitiveCharacter`） |
| L2→L3 磨光显式公式、Landau | 教科书 | `ZerosOfLFunctions` Layer 8（§8.4 Weil 公式）、`AnalyticNumberTheoryPartI` §1.3–1.9（Weil 显式公式、零密度）；`TotientGaloisClasses/Analytic.lean` 的 `(y/n − 1)₊` 核没有具名目标 | 未开始 | 部分（`riemannZeta` 的函数方程、`DirichletCharacter.LFunctionFunctionalEquation`） |
| L2→L3 `TopG`/`shape`/`supplyChi`/`EAtH`/`HostExW`/近似设计 | **新** | 无 | 无 | 无 |
| L2 `Green`（GL_n(𝔽_q) 尖特征标） | 教科书（Green 1955） | **无**（只有 `RepresentationTheory/CharacterTheory` Layer 9 的 GL₂(𝔽_q)：§9.1 类、主级数、Steinberg、尖；§9.2 特征值与表；并明说 Deligne–Lusztig "not planned in this roadmap"） | GL₂：`TauCeti/RepresentationTheory/CharacterTable/GL2/*`（`GL2CuspidalVirtualCharacter`、`GL2Steinberg`、`GL2PrincipalSeries`、`Classification.lean`） | 有 `Matrix.card_GL_field`、`GaloisField`、`Representation.character`；没有 Green 定理、n 次首一不可约多项式个数的公式、子空间计数 |
| L2 `VWin`（Iwasawa 塔上的 Galois 上同调） | **新**（弱化 Vandiver） | 间接：`IntegralIwasawaTheory` Layer 7（`VandiverCondition`、`vandiver_propagation`）、`CyclotomicClassGroupsAndStickelberger` §6.4、`ArithmeticKTheory` §7.5（ℤ 的 K 群 ↔ Vandiver）、`SelmerIwasawaCohomology` §0.6–0.9、§3.7（twisting）、§4.16–4.21 | 只有 Iwasawa 代数上的模论与分圆塔；无 Vandiver、无 K 群 | 无 |
| L2 `HypsAlt` 的各字段（类数公式、genus 质量、格点计数、扭曲周期） | 文献 | `ImaginaryQuadraticClassNumber` H1.4/H2.2（已实现）、`GeometryOfNumbersAndQuadraticArithmetic` §2.7、§3.1–3.3.5（hermitian 格；Siegel 质量只对二次 ℤ-格）、`ArakelovGeometryAndAbelianHeights`(+II)（Faltings 高度、Moriwaki）、`ComplexMultiplicationAndExplicitReciprocityPartII` §0.2、§4.6、Layer 9（Chowla–Selberg 只到 g = 1、平均 Colmez） | 部分（类数公式、ℤ-格的 θ 级数 `ThetaSeries` 已完成） | 无 |
| `supplyChi` 用到的短区间素数、Linnik | 文献 | `ExplicitPrimeCounting` Layer 7（显式版）；Linnik 只在 GRH 下（§6.5）；无条件 Linnik、变模数的短区间素数：**无** | 无 | 无 |
| θ 提升、Weil 表示、Siegel–Weil、倍乘法、Rallis、GGP、Jacquet–Rallis | 文献 | `MetaplecticAutomorphicForms`（Layer 6：Weil 表示 L460、Howe L704、see-saw L714、`globalThetaLift` L1324、Rallis L1672、Siegel–Weil L1511–1597）、`AutomorphicLFunctionsAndLocalFactorsPartII`（倍乘法）、`GanGrossPrasadUnitaryGroups` §1.1、GGP.8、Jacquet–Rallis L1159、RTF L610；**全定酉群之间的迭代 θ 提升：无** | 无 | 无 |
| 酉群、PEL、CM 模空间 | 文献 | `PELModuli` M0.22–M0.24、M3.1、M5.5；`PotentialAutomorphyInfrastructurePartII` Layer 3 + `CompletedCohomologyAndLocalGlobalCompatibility` §0.7；`JacobianChallenge`(+II) | 部分（只有 hermitian 形式、矩阵 U(p,q)） | 无 |
| L1 `Row0b`（极化尖表示的 Galois 表示） | 文献（但**证明走 θ 提升**） | `AutomorphicGaloisRepresentationsPartII`（AG2.0 权重与极化、AG2.1a 紧酉簇上同调、AG2.3 定酉群 + patching、AG2.5 Hodge–Tate 数与局部比较）：同一结论的**上同调路线**；`PotentialAutomorphyInfrastructure`(+II)；酉群 ↔ GL_n 的 base change 只在 `EndoscopicTransferAndUnitaryTraceComparison` §6.27/6.29/13.1 条件性地出现 | 无（只有 `TauCeti.DominantWeight.hodgeMultiset`） | 无 |
| L1 `IsRecT`/`RecTExists`（LLC 的存在性） | 文献 | `SmoothRepresentationsOfLocalGroups`（SR.0 部分；Bernstein 分解 L2308、BZ 导子 L3315、segment 分类 L4471–4540；**GL_n 的 LLC 只是约定** §SR.5.2 L4361）、`ArithmeticGaloisRepresentations` Layer 2（Weil–Deligne）、`GL2AutomorphicRepresentationsAndTransfer` R16.0.1、`EndoscopicTransferAndUnitaryTraceComparison` Layer 10；"RecTExists 型存在陈述"**无** | 只有 `Representation.IsSmooth`、局部 Weil 群 | 无 Weil–Deligne |
| p 进 Hodge | 文献 | `PadicHodgeTheory`、`PadicPeriodRings`、`FiniteFlatGroupsAndIntegralPadicHodgeTheory`、`PrismaticCohomologyPartIII` §7.22–7.24 | 无 | 无 |
| 实群、离散序列、Harish–Chandra | 文献 | `RealSemisimpleLieGroups`、`LieGroupsPartII`、`SmoothRepresentationsOfLocalGroupsPartII`、`RepresentationTheory/LieGroups` | 部分 | 无 |
| 定号行列式、均方界（"variance test function trick"）、Guinand | **新** | 无（`WeilPositivityAndLiCriterion` Layer 5 是 ζ 的 Weil 二次型） | 无 | 无 |
| 奇点消解、Poincaré–Lelong、L² ∂̄ | 文献 | `ResolutionOfSingularitiesCharacteristicZero`、`ComplexComparisonPartII` C5.4、`ComplexKahlerGeometry` K2/K5、`HeightsRationalPointsAndObstructions` §5.17c | 部分 | 无 |
| Bost 斜率不等式、一般酉群的 Siegel 质量/体积、Chowla–Selberg 周期 | 文献 | 只作为证明路线出现，**无具名目标** | 无 | 无 |

（行号见 `survey-T2.md`、`survey-T3.md`；QuasiRH 与 ZerosOfLFunctions 的节号见 `tauceti-ref/TauCetiRoadmap/TauCetiRoadmap/QuasiRiemannHypothesis/README.md` 第 128–176、898–931、2054–2095 行与 `ZerosOfLFunctions/README.md` 第 2442–2500 行。）

## 5. 选范围（b）

### 5.1 标准

照 Tau Ceti 的规矩：最低一层落在 Mathlib 或 Tau Ceti 已有材料上（No gaps）；与已有路线图不重叠，要用的写成 supplier；Build the library；范围明确；可复用；整条主线太大时写成一组路线图的第一份，其余用一节明确标成 roadmap-for-a-roadmap。

### 5.2 候选

| 候选 | 最低一层 | 与现有路线图 | 结论 |
|---|---|---|---|
| **A. 顶层衔接**（`PChar`/`ZeroFreeAll`/`EveryCharacter`/`imprimitive`/`rh_of_*`/`critLine`，16 条声明） | Mathlib | **全部重叠**：QuasiRH §1.1（零点自由半平面谓词）、§5.5（本原 ⇒ 所有）、§11.1（零点带，θ = 1/2 即 GRH）；ZerosOfLFunctions Layer 9（≡ `RiemannHypothesis`） | 不选 |
| **B. 主线的"陈述层"**（把 `VWin`、`Green`、`ZeroFreeAll`、`EveryCharacter`、RH 都写成 Prop，衔接作目标） | `VWin` 的陈述 32 条定义可以落到 Mathlib（`skeleton/Window/VWin.lean` 已编译），但 `HypsAlt`/`TopG`/`IsRecT`/`Row0b` 要几百到几千条自定义定义 | A 的重叠；另 `VWin` 作为 `Prop` 没有消费它的定理也没有见证（correctness rubric 的 unexercised predicate）；`zero_free_all_of_green_v_win` 作为目标是 8.5 万条声明的飞跃 | 不选 |
| **C. `Green`：GL_n(𝔽_q) 的类函数与尖特征标分类** | Mathlib（有限域、多项式、`Module.End`、`LinearMap.charpoly`、`GL`、`FDRep`）+ Tau Ceti 的特征标论（`ClassFunction`、`virtualCharacters`、GL₂ 表） | 不重叠：Tau Ceti 没有 n ≥ 3 的 Green 分类，CharacterTheory 明说不做 Deligne–Lusztig | **选** |
| **D. L2 → L3 的解析部分**（`TopG`、`supplyChi`、`EAtH`、短区间素数） | "主机/帧/尺度"的定义链上千条；短区间素数是独立的解析数论结果 | 短区间素数、Linnik 无条件版没有目标（可以单独立项） | 现在不选 |
| **E. L1**（`Row0b`、`RecTExists`） | Weil–Deligne、p 进 Hodge、自守表示、光滑表示，库里一行都没有 | 同一结论已有 `AutomorphicGaloisRepresentationsPartII`（上同调路线）；按 θ 提升再写一份会同目标重复 | 现在不选 |

### 5.3 为什么是 C

1. **它在主线上**：`GlobalTheory.GLq.Green` 是 `zero_free_all_of_green_v_win` 的三个输入之一（§2.4），在解析核心里通过深度零的局部 Langlands 与"好 Fourier 系数"被反复使用（`HypothesisBundleConversions.lean:87` 的 `greenRegularCharacters` 字段，`OpenFirstParametersOfPublishedUE.lean:52-54`）。
2. **没有缺口**：陈述只用 Mathlib（`skeleton/Window/Green.lean` 16 条定义 / 35 行，`analysis/extract_cone.py` 自动抽出即编译通过）；源码的证明（`Proofs/CharacterTheory/` 129 个证明文件 10,344 行 + `InertiaEigenvalues` 里的 Green 与 Harish–Chandra 部分）除两条小定义文件外只 import Mathlib。SKELETON.md 说它"极小（≈ 50–64 条）"指的是 `green_of_regular` 这一步；整个 `GreenRegularCharacters` 的证明要大得多，但同样只依赖 Mathlib。
3. **可复用**：Green 的分类是有限群李型表示论（Zelevinsky 分类、Deligne–Lusztig 理论、特征标层）的入口；Tau Ceti 现有的 GL₂(𝔽_q) 表是它的 n = 2 特例，路线图里可以写成一致性检验。
4. **是已发表的数学**：J. A. Green, *The characters of the finite general linear groups*, Trans. AMS 80 (1955)；Macdonald《Symmetric functions and Hall polynomials》；Zelevinsky。与 Alpöge 证明的关系只在 provenance 一节（源码有完整形式化可以对照）。

### 5.4 这份路线图里有什么、没有什么

- **有**（8 层）：首一多项式与 Teichmüller 特征、根幂和；End(V) 的特征多项式纤维与质量、子空间计数；`GL_n(𝔽_q)` 上的类函数、配对、单幂根、常项、尖性的两种刻画；Green 的 Möbius 变换；Frobenius 环面特征（根幂和）的虚拟特征标性质与配对；正则特征给出尖特征标；Harish–Chandra 诱导、Jacquet 限制与 Frobenius 互反、Mackey 配对、共轭类数、Green 定理与尖特征标个数；尖支撑的唯一性与素标签形式。
- **没有**（都写进 Scope 的 Not owned here，各有去处）：GL₂(𝔽_q) 的显式表（`RepresentationTheory/CharacterTheory` Layer 9 已有）；Zelevinsky 的完整分类（多重集 ↔ 不可约特征标、generic 成分的唯一性只做到尖支撑这一步）；Deligne–Lusztig 理论、特征标层、Hall–Littlewood；`GL_n` 光滑表示的 BZ 分类（`SmoothRepresentationsOfLocalGroups`）；一般有限群的特征标论（`RepresentationTheory/CharacterTheory`）。
- **其余主线**（roadmap-for-a-roadmap 一节，README 里明写"不要照着做"）：R2 深度零局部 Langlands 与 Green 标签（需要 `SmoothRepresentationsOfLocalGroups`）；R3 Galois 表示的 θ 提升构造（与 `AutomorphicGaloisRepresentationsPartII` 同目标，必须先和它的作者协调）；R4 自守窗口（Iwasawa 塔上的 Galois 上同调，弱化 Vandiver；suppliers：`IntegralIwasawaTheory`、`SelmerIwasawaCohomology`、`ArithmeticKTheory`）；R5 θ 提升链与解析假设（suppliers：`MetaplecticAutomorphicForms`、`GanGrossPrasadUnitaryGroups`、`ArakelovGeometryAndAbelianHeights`…）；R6 显式公式与零点自由（suppliers：`ZerosOfLFunctions`、`QuasiRiemannHypothesis`）。

## 6. 待人工确认

1. **范围**：第一份路线图选 Green 分类而不是主线的别处，是我的判断（§5.2）；De Song 可能更想先要"陈述层"或 L2 → L3 的显式公式部分。
2. **作者说明与代码的对应**（§3）：θ 提升链、定号行列式、bootstrap、弱化 Vandiver 等说法都来自四页说明，我只在命名（`ChainTied`、`RowsPos`、`VVle`、`LinkN`…）上做了类比，没有读证明。
3. `HypsAlt` 40 个字段（§2.5(c)）只按名字转述；`shaLen`、`LinkN`、`TopG` 里"正性"的确切位置没有读到。
4. `Row0b`/`IsRecT`/`RecTExists` 的数学内容是「很可能」（负责这一部分的子代理中途失败）。
5. `GlobalTheory.Published.*` 里哪些已在库内被 discharge、哪些仍是假设，没有核实（§2.7）。
6. Green 证明里满射性的计数路线（§2.5(a)）：Mackey 配对、广义成分、类数这三步的陈述我是照源码的陈述写的，route 是我按经典 Harish–Chandra/Zelevinsky 的做法补的，细节以 `ROADMAP-REVIEW.md` 的自审为准。
7. Tau Ceti 路线图的「实现」状态只按有无 `STATUS.md` 判断，没有逐条核对 `STATUS.md` 的内容。
