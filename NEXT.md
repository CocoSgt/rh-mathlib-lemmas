# NEXT — 后续阶段计划

> 目标：把 Alpöge–Claude 黎曼猜想形式化（`source/`，175,187 文件 / 17.4M 行）里的通用数学结果拆成可独立引用、可逐条并入 Mathlib 的单元。本文件接在 `REPORT.md` 之后，给出顺序、分块、前置补基础和工作量估计。所有估计以"一个人 + Lean 经验"计，按试点的实际速度（一条机器化陈述改写 + 编译 5–15 分钟；一个 150–400 行文件整理 0.5–2 小时）外推。

## 0. 先做基础设施（1–2 周）

| 事项 | 产出 | 说明 |
|---|---|---|
| 去重 | `analysis/dedup.py`：对 `leaf_theorems.jsonl` 的陈述文本做规范化后聚类 | 已知重复：`RegGensA` = `MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne`；"清除分母" 20+ 变体；`det_mono` 两份。去重后 `Lemmata` 的 142 条叶子定理估计剩 ~90 条 |
| import 最小化脚本 | `analysis/minimize_imports.sh`：从 `import Mathlib` 出发，按报错逐步加子模块 | 试点里每个文件手试 2–4 轮；Mathlib 这个版本启用了 `module`/`public import`，很多想当然的文件名不存在（§4.3）。可以借用 Mathlib 自己的 `scripts/minimize_imports.lean`（需确认在 `0df444a3` 下可用） |
| 陈述改写规范 | `CONVENTIONS.md`：`goal1` → 名字、`Eq.{1}`/`DFunLike.coe` → 记法、`@` 全展开 → 隐式、`first \| …` 固定分支、`set_option` 清零、命名空间选择表 | 试点已给出 13 个样例文件 |
| 公理检查进 CI | `extracted/Axioms.lean` 改成 `#guard_msgs` 形式或用 `lean4checker` 回放 | 现在 `axioms.txt` 是手工保存的输出 |
| 授权 | 与 Levent Alpöge 确认 license 与并入 Mathlib 的许可 | 原始发布没有 license 文件（镜像 README 明说）；并入前必须解决 |
| 机器 | 整理工作每个 `lean` 进程 ~5.7 GB（import Mathlib）；`lake build -K jobs=4` 可接受；**不要**尝试 `lake build` 整个 `source/` | TASK 已说明需要 ~100 GB 内存 |

## 1. 把试点 13 个文件变成 Mathlib PR（3–5 周）

按"越小越通用越先"排序，每个 PR 独立可合并：

| 批 | 文件（`extracted/src/RhLemmas/…`） | 目标 Mathlib 位置 | 预计 | 备注 |
|---|---|---|---|---|
| 1a | `Analysis/Matrix/PosDef/Det.lean` | `Mathlib/Analysis/Matrix/PosDef.lean`（或新 `PosDef/Det.lean`） | 2 天 | Minkowski/Fischer/Hadamard；Mathlib `PosDef` API 的自然延伸 |
| 1b | `LinearAlgebra/Matrix/Det.lean` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`（Cauchy–Binet）、`Mathlib/LinearAlgebra/Determinant.lean`（det mulLeft）、`Data/Fin/Basic`（perm） | 2 天 | 可能被要求拆成 3 个 PR |
| 1c | `Analysis/Matrix/Deriv.lean` + `Analysis/Matrix/PosDef/Open.lean` | `Mathlib/Analysis/Matrix.lean` | 2 天 | Jacobi 公式 + PosDef 开性 |
| 1d | `Analysis/SpecialFunctions/BernsteinIntegral.lean` | `Mathlib/Analysis/SpecialFunctions/Bernstein.lean` | 1 天 | 也可挂到 `RingTheory/Polynomial/Bernstein.lean` |
| 1e | `Analysis/SpecialFunctions/Complex/ExpFiber.lean` | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` 附近 | 1 天 | 推广后的陈述 |
| 1f | `Analysis/SpecialFunctions/Tent.lean` | 新文件 `Mathlib/Analysis/SpecialFunctions/Tent.lean`（或 `Topology/PartitionOfUnity`） | 2 天 | 命名需要讨论（`tent`/`tentProd`） |
| 1g | `Topology/Algebra/InfiniteSum/Fiberwise.lean` | `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean` 附近 | 1 天 | |
| 1h | `LinearAlgebra/Matrix/LDU.lean` | `Mathlib/LinearAlgebra/Matrix/…`（新） | 2 天 | 陈述较长，可能被要求拆分 |
| 1i | `Geometry/Convex/Cone/DualFinite.lean` | `Mathlib/Geometry/Convex/Cone/DualFinite.lean`（扩展） | 1 周 | Farkas/Weyl–Minkowski；维护者可能希望与 `Analysis/Convex/Cone/Dual.lean` 的拓扑版统一命名 |
| 1j | `RingTheory/RegularLocalRing/Domain.lean` | `Mathlib/RingTheory/RegularLocalRing/…`（新文件） | 1–2 周 | 直接补 Defs.lean 的 TODO；`instIsDomain` 实例需要讨论；Mathlib master 上 `KrullDimension/Regular.lean` 可能已有新进展，需 rebase |
| 1k | `Analysis/InnerProductSpace/CompactSelfAdjoint.lean` | `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` 之后的新文件 | 1–2 周 | 补 Spectrum.lean 的 TODO；14 条定理；证明已 Mathlib 风格 |
| 1l | `LinearAlgebra/Matrix/Similarity.lean` | `Mathlib/LinearAlgebra/Matrix/Charpoly/…`、`LinearAlgebra/Matrix/…` | 2 周 | 46 条声明、500 行，需要拆成 Frobenius 标准形 / 转置相似 / 连续性 / 共轭类 4 个 PR |

总计约 25–40 个工作日。每条 PR 前都要：重命名核对（与 Mathlib 现有命名风格一致）、docstring、`lake build`（Mathlib CI 会跑 lint：`docBlame`、`lineLength` 等）、`#print axioms`。

## 2. `Lemmata/` 库全量处理（4–6 周）

167 文件、9.2k 行，145 个叶子文件（Mathlib-only），去重后约 90 条定理。按主题分成约 8 个 Mathlib PR：

| 主题 | 文件（`Lemmata/…`） | 条数 | 目标 |
|---|---|---:|---|
| 线性代数/矩阵 | `GeneralBFact*`（Cauchy–Binet、LDU 唯一性、广义特征空间、特征向量无关、过渡矩阵）、`DetMonotoneStarMulSelf`、`DetNormLeProdRows`、`PosDefOfRealQuadratic`、`PowMulVecEigen*`、`SimultaneousEigenvectors`、`GeneralBFactSecondLast`（B 进制唯一性） | ~20 | `Mathlib/LinearAlgebra/*` |
| 交换代数 | `FirstBlockLemmaB`（Krull 维数）、`FirstBlockLemmaG/I/K`（IsUnit）、`DiscreteValuationQuotients`（DVR 余核长度）、`ComplementLifts`、`Cancellation`（弱逼近）、`ClearingDenominators`、`Denominators`、`NatMulIsIntegral`、`IntegerMulIntegral`、`GeneralBFact*(清除分母变体 20+)`、`AddValuationProducts`、`FirstBlockLemmaL`、`B1962s`（ℤ_p[X] 无挠） | ~35（去重后 ~15） | `Mathlib/RingTheory/*`、`Mathlib/NumberTheory/NumberField/*` |
| p-adic/数论 | `PadicNatCastNorm`、`FirstBlockLemmaC/D/F`（PadicAlgCl 范数）、`GeneralBFactUpper/RightExtra/LeftTer/Third`（超度量不等式）、`MiscLemmasN`、`FiberEquations`、`GeneralBFactLeftTail` | ~12 | `Mathlib/NumberTheory/PAdic/*`、`Analysis/Normed/*` |
| 分析 | `CofiniteContinuousBounds`（增长界 ⇒ 整除）、`GeneralBFactBisForm`（Cauchy 估计）、`FunctionAtZero`/`GeneralBFactLeftVariant`/`ThirdFurther`（连续同态 ⇒ exp）、`CofiniteContinuousBounds`、`GeneralBFactJ`（全纯零点唯一性）、`MultivariateIntegrals`、`PeriodicFunctions`、`IterateZero`、`CurryModusPonens`（Fubini）、`GeneralBFactThirdBisForm`（Fubini） | ~12 | `Mathlib/Analysis/*` |
| 拓扑/群 | `GeneralBFactLeftRest`（指标）、`MiscLemmasI`（线性无关基变换）、`GeneralBFactRightRest`（Multiset map）、`GeneralBFactSecondTer`（filter 计数）、`GeneralBFactRightFurther` | ~6 | 多数已在 Mathlib（§2.3），只需核对 |

剩余 22 个带 `Imports.lean` 的目录是给大型证明用的聚合器，不单独处理；其中 `GeneralBFactLeftAltForm.MQ`、`DualWeylPullback`、`PlaneOverMembership`、`TwistedIdempotents` 等的陈述引用 Formalism 结构，属于阶段 4/5。

## 3. 其它库里的通用叶子文件（6–10 周）

按"通用性 × 可读性"排序（数量来自 `analysis/leaf_theorems.jsonl`：GroundTheory 851、ReciprocityTheory 611、Formalism 1,223、CompanionTheory 107、PositivityTheory 18、Development 9,003 条 Mathlib-only 叶子定理）：

| 优先 | 子库 | 代表文件 | 内容 | 估计 |
|---|---|---|---|---|
| A | `GroundTheory.AutomorphicForms`（219 条叶子定理） | `RealGroupsHaar.lean`（Haar 测度在 GL(n) 左乘下的变换、`det_restrictScalars`）、`RealGroupsLie.lean`（`GL` 李群、指数映射）、`LocallyProfinite.lean`、`GeometricLemma{Average,Orbit}.lean`、`HilbertSchmidt.lean`、`PartialDifferential/{AnalyticHypoSeries,Sobolev}.lean`、`DixmierMalliavinLine{Kernel,Limit}.lean`、`GL2/{GJGlobalEntire,GJLaurentIdeal,GJGlobalRank,GJGlobalUnfoldCount}.lean`、`GL2Classical/*`、`FiniteBruhat.lean`、`HarishChandraCentre/Symmetric.lean`、`RestrictedHaarProduct.lean`、`ArchimedeanWhittaker/*`、`DefiniteClassNumber/Reduction.lean`、`QuadraticConj.lean`、`StableConjCyclic.lean` | 李群、Haar、Sobolev、Hilbert–Schmidt、Mellin、Godement–Jacquet、Whittaker ODE | 10–15 个 PR，3–4 周 |
| B | `ReciprocityTheory.GeometryOfNumbers`（32）、`CommutativeAlgebra`（34）、`Chebotarev`（30）、`GroupCohomology`（15）、`NeutralLocalFields`（15）、`DualLattices`（41）、`SemistableReduction`（43）、`AnalyticForms`（48） | GramSt、LogDetSt、DiscSt、SimplexSumSt、WeakMatSt、CohenMacaulay、NoWind、SplitF、AbsProd…、NormCongr、CyclotomicIrreducible…、MemZpowersQuot、TendstoPrimeIdealZetaSumUniv | 行列式不等式、正则局部环、Chebotarev 的代数部分、格、算术 | 8–12 个 PR，3–4 周 |
| C | `GroundTheory.{LocalFields,GlobalFields,TateCohomology,ProfiniteCohomology,Brauer,PowerSubgroups,FunctionField,IdeleRoots}`（31+128+34+49+14+14+2 条） | `LocalFields/…`、`GlobalFields/…` | 局部域、整体域、Tate 上同调、Brauer | 需要先看哪些是 Mathlib `LocalField`/`TateCohomology` 已有的；估计 5–8 个 PR，3 周 |
| D | `GroundTheory.ArithmeticGeometry`（51）、`PAdicHodge`（92）、`HeightsAndTheta`（217） | `SchemeCohomology/*`（正则局部环商、层上同调）、`ToricVarieties/*`、`KrullDomain.lean`、`ModularCurves/WeierstrassCharts.lean`、`PAdicHodge/*`（tilt、untilt）、θ 函数 | p-adic Hodge 在 Mathlib 几乎没有；θ 函数 Mathlib 有一部分 | 需要先补定义（见阶段 4），3–4 周 |
| E | `Formalism.{MahlerMeasure,SuccessiveMinima,HarderNarasimhan,HermitianLattices,LatticeSlopes,SmithDeterminants,GaloisIrreducibility,LogVandermondeBounds,ZeroFreeRegion,LandauZeroFreeBounds,…}` | 1,223 条叶子定理 | Mahler 测度、逐次极小、Harder–Narasimhan、Galois 不可约性、零点自由区域 | 很多是数论专门结果，Mathlib 已有 Mahler 测度的一部分；先做 `ZeroFreeRegion`/`LandauZeroFreeBounds`（解析数论）和 `SuccessiveMinima`/`HarderNarasimhan`（几何） |
| F | `Development.*`（9,003 条） | 抽样看主要是自守表示、θ 提升、迹公式的技术引理；通用比例低，但 `Development.AutomorphicArithmetic.CommutativeAlgebra`（432 文件）、`ResidueCharacters`、`DedekindLFunctions`、`CyclotomicBounds` 等值得单独扫一遍 | | 先用 `dump_leaf.py` 按关键词筛 |

## 4. 需要先往 Mathlib 补"基础定义"的块（与 2–3 并行，每块 2–6 周）

这些块在源里有完整理论，但 Mathlib 缺少底层定义，直接抽定理进不去，要先提"定义 + 基本引理"的 PR：

| 块 | 源位置 | Mathlib 缺的东西 | 建议 |
|---|---|---|---|
| 局部 profinite 群 | `GroundTheory.AutomorphicForms/LocallyProfinite.lean`、`RestrictedHaarProduct.lean` | `LocallyProfiniteSpace` 类、紧开子群的存在、限直积 `Πʳ i, [G i, C i]`、限直积上的 Haar 测度与 Euler 积分 | 先提 `Topology/Algebra/Group/LocallyProfinite.lean`（定义 + `exists_compactOpen_subgroup` + `hasBasis_nhds_compactOpenSubgroup`），再提限直积 |
| Hilbert–Schmidt / 紧算子谱 | `HilbertSchmidt.lean`、`CompactSelfAdjoint.lean` | Mathlib 有 `IsCompactOperator`、`IsSelfAdjoint`，无 `HilbertSchmidt` 算子、无谱定理基形式 | 谱定理（1k）先行；Hilbert–Schmidt 看需求 |
| Sobolev 空间（Bessel 位势） | `PartialDifferential/Sobolev.lean` | Mathlib 没有 `MemSobolev`/`besselPotential`（源文件里是自定义的，需要核对） | 先确认定义是否与 Mathlib 的 `SobolevSpace`（若已存在）兼容 |
| GL(n) 上的 Haar 测度 / 李群结构 | `RealGroupsHaar.lean`、`RealGroupsLie.lean` | 实例可由 `UnitsOfNormedAlgebra` 得到，但 Haar 测度的显式密度 `‖det g‖^{-n}` 是新的 | 1–2 个 PR |
| Mellin 变换 | `GL2/GJGlobalEntire.lean` | Mathlib 有 `mellin`/`MellinConvergent`（2025 新加），但没有对称延拓定理 `exists_entire_of_symm` | 核对 Mathlib `MellinTransform` 文件后补 |
| 局部 Langlands / Galois 表示 | `Development.AutomorphicArithmetic.Foundations.{LocalLanglands,GaloisRepresentations}` | Mathlib 没有 `(φ, N)`-模、Weil–Deligne 表示、Galois 表示的 Hodge–Tate 权重等；这是最大的一块基础缺口 | 不在第一阶段；等 Mathlib 的 Langlands 方向（`Mathlib/NumberTheory/LSeries`、`RepresentationTheory`）成熟 |
| p-adic Hodge（tilt/untilt、Breuil–Kisin） | `GroundTheory.PAdicHodge` | Mathlib 完全没有 | 单独立项 |
| Étale 上同调 / 奇点消解 | `Development.EtaleCohomology`（1,398 文件）、`ResolutionOfSingularities`（499 文件） | Mathlib 完全没有（有 `Scheme`、`Cohomology` 基础） | 单独立项；先做 `EtaleCohomology.TateTwists`、`KummerTheory` 这类能用现有 `Scheme` 讲的部分 |
| 阿贝尔簇 / 模空间 | `Development.AbelianVarietyTheory.Definitions.*`（2,190 文件） | Mathlib 没有 AbelianVariety | 单独立项 |

## 5. 哪些块可以"整体并入"（不做逐条改写，直接作为独立库维护）

考虑到 Development ↔ Formalism ↔ GroundTheory 之间的循环 import（§1.4），**按库整体迁移到 Mathlib 不可行**；但可以先在本仓库里重组成一个分层的独立库 `AlpoClaude`，让外部能按层 import：

```
AlpoClaude.Basic        ← Lemmata 叶子 + GroundTheory 通用叶子 + ReciprocityTheory 通用叶子（阶段 2–3 的产物，Mathlib-only）
AlpoClaude.Analytic     ← Formalism.{SharpRestriction, HermitianCurvature, LocalToGlobal, PeriodIntegrals, GL3MeanSquares, …} + PositivityTheory + CompanionTheory
AlpoClaude.Arithmetic   ← Development.{WeilBound, AutomorphicSpectrum, EtaleCohomology, ResolutionOfSingularities} + GroundTheory.{HeightsAndTheta, PAdicHodge, ArithmeticGeometry}
AlpoClaude.Abelian      ← Development.AbelianVarietyTheory（8.1M 行，保持原样）
AlpoClaude.Top          ← Development.AutomorphicArithmetic.{Foundations, ThetaCorrespondence, AutomorphicVarieties, CharacterBoxes} + Formalism.VW + Supplements + Statements + Main
```

分层的目的是把"只有最顶层需要的"和"所有人都需要的"分开；每层内部保持原文件不动（避免 17M 行的重排风险），只在顶层加 `import` 聚合文件。这个重组本身不改数学，只是 `lakefile` + 聚合文件，但它需要**整库编译一次**来验证分层无环——这需要 ~100 GB 内存的机器，不在本机做。可行的替代：用 `analysis/closure.py` 精确计算每层的 import 闭包，只在文本层面证明无环，再在 CI 机器上编译。

### 5.1 最顶层 glue：4 条"条件定理"可以现在就并入 Mathlib

下面这些定理的**陈述和证明只用 Mathlib**（已读证明，并在只 import Mathlib 的环境里实测编译，见 REPORT §3.1），只是因为文件 import 了上游聚合文件才"看起来"依赖全库：

| 定理 | 位置 | 陈述 |
|---|---|---|
| `UpperTheory.riemannHypothesis_of_everyCharacter` | Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215 | (∀ N χ s, 1/2 < Re s → L(χ,s) ≠ 0) → `RiemannHypothesis` |
| `Formalism.VW.rh_of_every` | Formalism/GammaFactorNonvanishing/CritLine.lean:29 | 同上（直接走 ζ 函数方程） |
| `Formalism.VW.critLine` | 同上:11 | (∀ χ, Re s > 1/2 非零) → 本原 Dirichlet L 函数的带内零点在 Re s = 1/2 |
| `Claim.strip`, `Claim.zeta` | CharacterBoxes/ClaimStrip.lean:59,75 | 半平面非零 ⇒ 带内零点在线上 / ζ 的 RH；`Claim.zeta_iff : Zeta ↔ RiemannHypothesis := Iff.rfl` |

它们是"所有 Dirichlet L 函数在 Re s > 1/2 非零 ⇒ RH"这一经典推导的形式化，Mathlib 的 `RiemannHypothesis` 定义旁边正缺这些。做成一个 PR（约 150 行，依赖 0*）。需要把 `UpperTheory.EveryCharacter` 这个 def 换成 Mathlib 风格的陈述（它就是 `Statements.lean` 里 `DirichletLNonvanishingRightOfHalf` 的复制，可以直接用那个名字）。

## 6. 时间线与里程碑

| 阶段 | 内容 | 工时 | 里程碑 |
|---|---|---|---|
| 0 | 基础设施 + 授权 | 1–2 周 | 去重后的候选清单；import 最小化脚本可用；授权确认 |
| 1 | 试点 13 文件 → Mathlib PR | 5–6 周（含 review 往返按 2 倍计） | 至少 6 个 PR 合并（谱定理、正则局部环、PosDef 行列式不等式、Farkas、Cauchy–Binet、Jacobi） |
| 1' | 顶层 glue 4 条 | 3 天 | "EveryCharacter ⇒ RH" 进 Mathlib |
| 2 | `Lemmata/` 全量 | 4–6 周 | 去重后 ~90 条，8 个 PR |
| 3 | 其它库通用叶子（A–F） | 8–12 周 | 30–40 个 PR |
| 4 | 补基础定义（locally profinite、Haar on GL(n)、Hilbert–Schmidt、Mellin…） | 与 2–3 并行，每块 2–6 周 | 每块一个"定义 + 基本引理"PR |
| 5 | 分层独立库 `AlpoClaude`（文本层无环 + 远程机器整库编译） | 4–8 周（含等待机器） | 四层 `import` 闭包无环；CI 机器上 `lake build AlpoClaude.Top` 通过；`#print axioms riemannHypothesis` 三公理 |

总计约 6–9 个月一个人的工作量；其中一半是 Mathlib review 往返而不是写证明。

## 7. 风险

1. **授权**：没有 license，一切对 Mathlib 的 PR 都要等 Alpöge 确认。
2. **Mathlib 漂移**：固定版 `0df444a3` 之后 Mathlib 在 `RegularLocalRing`、`Spectrum`、`MellinTransform` 上都在快速发展，阶段 1j/1k rebase 时可能撞车（已经有同名结果）。
3. **陈述质量**：源文件很多陈述是机器展开形式，改写时容易悄悄改变语义；每条改写都要和原陈述做 `example : 新 ↔ 原 := Iff.rfl` 式核对（试点没做这一步，建议在阶段 0 加上）。
4. **内存**：任何涉及 Development/Formalism 大文件的验证都需要大机器；本机只能做 Mathlib-only 的叶子文件。
5. **重复副本**：不改写就去重会漏；先用文本聚类，再人工确认。
