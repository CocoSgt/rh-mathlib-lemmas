# REPORT — 把黎曼猜想 Lean 证明拆成可复用引理：第一阶段报告

> 功劳与署名：证明的全部数学与 Lean 代码属于 **Levent Alpöge（与 Claude 合作）**。本报告及 `extracted/` 里抽出的每一条引理都来自 `source/`（alpo.ge 发布、CocoSgt 镜像的 2026-11-20 版），我们只做了查找、整理、改写与编译验证，没有新的数学。
>
> 环境：Lean `v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，macOS arm64，10 核 / 32 GB。Lake 5.0.0 没有 `-j` 选项，并发用 `lake build -K jobs=4`（或环境变量 `LAKE_JOBS`）控制。

## 0. 摘要

- **结构**：175,187 个文件 / 17,374,215 行，`Main` 的传递 import 闭包覆盖 99.8% 的文件（174,764 个），整个库是一个连通的整体；顶层库之间 import 大量互相交叉（Development ↔ Formalism 6 万多条边、GroundTheory ↔ ReciprocityTheory 互相引用），**不能按目录当"层"来拆**。真正的分层在"命题"层面：`Row0b`(Galois 表示) → `VWin`(自守窗口) + `Green` + `Hyps` 非空 → `ZeroFreeAll` → `EveryCharacter` → `RiemannHypothesis`（§1.3）。
- **可拆出来的东西**：只 import Mathlib 的"叶子文件"有 5,927 个，里面有 11,955 条非 private 定理的陈述只用 Mathlib 概念（§1.1 表）。`Lemmata/`（167 文件，9.2k 行）是作者自己的通用工具箱，145 个叶子文件全部 Mathlib-only。此外 GroundTheory.AutomorphicForms、ReciprocityTheory.{GeometryOfNumbers,CommutativeAlgebra,Chebotarev,...}、Formalism.{MahlerMeasure,SuccessiveMinima,...} 里也有大量通用结果。
- **候选表**：§2 列了 52 条（含主线 glue 4 条），逐条到固定版 Mathlib 源码里搜过同名/同义声明（搜索脚本与结果在 `analysis/mathlib_check.py`、`analysis/mathlib_checks.txt`）；另有 15 条 Mathlib 已有、不必并入的记在 §2.3。52 条里 23 条（标 ★）已做进试点。
- **试点**：`extracted/` 是一个独立 Lake 项目（pin 同一版 Mathlib），13 个文件、89 条公开定理，全部 `lake build -K jobs=4` 通过，`#print axioms` 只依赖 `propext, Classical.choice, Quot.sound`（§3）。原文件在摘出前都先原样编译过一遍（每条引理的内部依赖锥 = 0，§2 表中"依赖"列）。
- **最重要的发现**：(1) 几块可以"整体并入"的通用文件：紧自伴算子谱定理（368 行）、正则局部环是整环（388 行）、半正定矩阵行列式不等式（Hadamard/Fischer/Minkowski，153 行）、代数 Farkas 引理 / Weyl–Minkowski（235 行）——这些在 Mathlib 里都缺；(2) 真正阻碍复用的是 import 列表"聚合式"写法：一个文件往往 import 上百个模块但证明只用其中几个，所以**依赖锥必须靠单独编译来量，不能看 import 列表**（§1.4）。
- **GitHub（步骤 5，§3.5）**：全部交付物在 https://github.com/CocoSgt/rh-mathlib-lemmas ；mathlib4 fork 在 https://github.com/CocoSgt/mathlib4 ；第一批 3 个 PR 已开：[#46339](https://github.com/leanprover-community/mathlib4/pull/46339)（PosDef 行列式不等式）、[#46340](https://github.com/leanprover-community/mathlib4/pull/46340)（Jacobi 公式）、[#46341](https://github.com/leanprover-community/mathlib4/pull/46341)（Cauchy–Binet），CI 状态见 PROGRESS.md。

---

## 1. 结构图

数据来源：`analysis/scan_imports.py`（每个文件的行数、import 列表 → `analysis/imports.jsonl`）、`analysis/index_decls.py`（每条声明的种类/文件/行号/private → `analysis/decls.jsonl`）、`analysis/leaf_statements.py`（叶子文件定理的陈述文本，并检查是否引用同文件 `def` → `analysis/leaf_theorems.jsonl`）、`analysis/closure.py`（传递闭包）。全部脚本只读 `source/`。

### 1.1 各库规模

"叶子文件"= 只 import Mathlib（及 Batteries/Lean 等标准依赖）、不 import 本项目任何模块的文件。"陈述只用 Mathlib 概念"= 叶子文件里的非 private 定理，且陈述文本里没有引用同文件定义的 `def/structure/abbrev/instance`（这是充分条件：文件只 import Mathlib，所以陈述里出现的每个名字都是 Mathlib 的）。

| 库 | 文件数 | 行数 | 叶子文件 | 非 private 定理/引理 | 叶子文件中非 private 定理 | 其中陈述只用 Mathlib 概念 |
|---|---:|---:|---:|---:|---:|---:|
| Development | 141,928 | 12,232,663 | 4,265 | 507,827 | 15,241 | 9,003 |
| Formalism | 18,254 | 3,200,748 | 766 | 156,162 | 2,514 | 1,223 |
| GroundTheory | 8,507 | 1,119,138 | 448 | 53,876 | 2,688 | 851 |
| ReciprocityTheory | 3,845 | 563,016 | 256 | 25,425 | 1,104 | 611 |
| CompanionTheory | 2,027 | 194,218 | 35 | 9,357 | 208 | 107 |
| PositivityTheory | 449 | 55,130 | 6 | 2,595 | 27 | 18 |
| Lemmata | 167 | 9,232 | 145 | 164 | 142 | 142 |
| Supplements + Statements + Main + BuildAid | 10 | 70 | 6 | 9 | 0 | 0 |
| **合计** | **175,187** | **17,374,215** | **5,927** | **755,415** | **21,924** | **11,955** |

声明总数 1,054,991：theorem 782,528、lemma 34,510、def 212,275、abbrev 13,090、structure 8,286、instance 4,138、inductive 121、class 43。

### 1.2 各库讲什么、互相怎么 import

下面"讲什么"主要根据目录名、文件名和抽样读的定理陈述判断；**目录名与内容不一定一致**（例如 `Development.AbelianVarietyTheory` 里绝大部分是自守表示/θ级数/迹公式的材料，见 §5 待人工确认）。

#### Development（141,928 文件 / 12.2M 行，占 70%）

| 二级目录 | 文件 | 行 | 内容（按目录名） |
|---|---:|---:|---|
| `AbelianVarietyTheory` | 99,187 | 8,102,723 | 按 `Definitions.* / Proofs.* / PublishedTheorems.* / Statements.* / BlockTheory.* / Counterexamples.*` 组织；主题：Divisors、InertiaEigenvalues、IwasawaDecomposition、TwistedOperators、FlagMeasures、DecoratedLatticeProofs、SatakeParameters、ModuliProofs、DegenerationProofs、JetHarmonics、GlobalInterpolation、UniformizationProofs、UnitaryExistence、SiegelThetaTransformation、CuspFormEvaluations、ThetaShiftProofs、HeightProofs、UnramifiedDepth、AdelicLatticeProofs、CubicalLineBundles、ThetaLawProofs、CoherentCohomologyProofs、GaloisGeometry、LatticeFrames、TorusHaarMeasure、ToricGeometry、TwistedInnerProducts、CovolumeBounds、FormalGroupCharts、CharacterTheory、ShimuraVarieties、CrystallinePeriods… |
| `AutomorphicArithmetic` | 18,431 | 1,776,375 | AutomorphicVarieties（ModularityArgument、SmallClassNumbers、HeightAndVanishing…）、Foundations（LocalLanglands、GaloisRepresentations、BaseChangeIdentities）、ThetaCorrespondence（ThetaPairLifts）、CharacterBoxes（**最终 glue：UpperTheory.EveryCharacter 的推导**）、IntegralCasts、CommutativeAlgebra、DivisorFrames、CyclotomicBounds、WhittakerHecke、LocalEmbeddings、TwistedTraces、DedekindLFunctions、MeanSquareBounds、PrimeDiscriminants、WeightCongruences… |
| `AutomorphicSpectrum` | 15,147 | 1,195,844 | `Proofs / Definitions / Statements / PublishedTheorems` 四段式；自守谱（Shintani 公式、离散谱等） |
| `WeilBound` | 7,051 | 848,547 | CoreStatements（含 SiegelWeilFormula / EisensteinMeromorphy / AutomorphicKernels）、RepresentationTheoryGL、ThetaLifts |
| `ResolutionOfSingularities` | 499 | 140,709 | EmbeddedResolution、Foundations |
| `EtaleCohomology` | 1,398 | 104,525 | EtaleSheaves、CohomologicalPurity、TateTwists、KummerTheory、EtaleTrace、DivisorCycles、WeilConjectures |
| `DiscreteGroups` | 215 | 23,703 | GlobalIrreducibility、PiInvariants |

`Development` 对外 import：→ Formalism 41,859 条、→ ReciprocityTheory 38,051、→ GroundTheory 7,532、→ CompanionTheory 1,875、→ PositivityTheory 1,057。它是 import 图里"最上层"同时也是最大的库，但 `Formalism` 也反向 import `Development` 236 条、`GroundTheory` 反向 57 条——顶层库之间没有无环的分层。

#### Formalism（18,254 文件 / 3.2M 行，100 多个子库）

证明的"形式化主干"：把解析输入写成命题并证明。最大的几块：

| 二级目录 | 文件 | 行 | 内容 |
|---|---:|---:|---|
| `LocalToGlobal` | 5,501 | 955,843 | SiegelLatticeTheory、Columns、IndefiniteReal、TorsionIntegrality、GlobalTheory、KernelLattices、ProjectiveLattices、CharacterGerms、Divisibility、GroupLattices、InertKernelTheory、PairingIndexBounds、ExponentGrids、NumberFieldFamilies… |
| `SharpRestriction` | 3,093 | 709,436 | GrowthBounds、LevelLetterCocycles、CuspSpanNormBounds、GlobalSchurBounds、GenusPolyhedralBounds、RamificationFrobenius、ValuationFrobeniusEpsilon、InertJacobiLevels… |
| `PeriodIntegrals` | 4,350 | 451,856 | UnitaryGroupMassFormula（3,615 文件）等 |
| `HermitianCurvature` | 1,922 | 460,802 | HermitianCurvatureProofs（1,854 文件） |
| `GL3MeanSquares` | 440 | 78,320 | GL(3) 均方界 |
| `ThetaLogCoordinates` | 292 | 54,555 | θ 函数对数坐标 |
| `WachLatticeTwists` | 262 | 38,367 | Wach 模、 twists |
| `LocalRingCardinality` | 173 | 35,348 | 局部环基数计数 |
| 其余 ~90 个 | 3,021 | ~400k | MahlerMeasure、HarderNarasimhan、SuccessiveMinima、HermitianLattices、LatticeSlopes、LandauZeroFreeBounds、ZeroFreeRegion、ZetaNonvanishing（含 `Statement*`：零点自由区域定理的顶层陈述）、GaloisIrreducibility、CyclotomicNorms、TameInertiaTowers、FrobeniusOrbits、CMTypeGalois、DirichletDensity、ArtinHasse、SmithDeterminants、GaussJetBounds、EllipticTorsion、FormalGroupWitt/Log、PadicSubsetSums、ResultantValuation、WachModuleLifts、EisensteinCokernelLengths、GradedWeylDivisibility、PieriBlockIdeals、SatakeDualWeyl、GelfandTransference、MirabolicMackeyTheory、RealPlaceAnalysis、FormalDegreeBessel、DoubleCosetMeasures、LogVandermondeBounds、QuotientMetricDivisors、PairingDivisors、ThetaLiftIndependence、LatticeTheta、CorankShare、LogFactorial*、IncomingBounds、TruncatedSeriesCounting、WindowSums、CoboundaryTransfers、FrobeniusContraction、GaussValuationBounds、JumpKernelCokernel、DivisorInequality、MeanHeightDescent、MonomialMeanResidues、NormUnitaryBounds、RankGapBounds、SizeWindowBrackets、AdmissibleDesigns、PolynomialDimension、SubspaceCounting、GrowthSums、DegreeFormula、MoebiusJetDuality、… |

`Formalism` 对外 import：→ ReciprocityTheory 348、→ Lemmata 118、→ Development 236。被 Development（41,859）、CompanionTheory（762）、GroundTheory（10）、ReciprocityTheory（266）、Lemmata（634）、PositivityTheory（8）import。

#### GroundTheory（8,507 文件 / 1.1M 行）

| 二级目录 | 文件 | 行 | 内容 |
|---|---:|---:|---|
| `HeightsAndTheta` | 6,410 | 641,322 | 高度函数、θ 函数 |
| `AutomorphicForms` | 542 | 150,005 | **通用数学很多**：CompactSelfAdjoint（紧自伴算子谱定理）、RealGroupsHaar（GL(n) 上的 Haar 测度、det(mulLeft)）、RealGroupsLie（GL(n) 是李群）、ContragredientTranspose（矩阵与转置相似、charpoly 系数连续、循环分解）、HilbertSchmidt、LocallyProfinite、PartialDifferential（Sobolev、C^∞+Cauchy 界 ⇒ 解析）、ArchimedeanWhittaker（Whittaker 方程的 Wronskian 唯一性）、GL2（Mellin 变换解析延拓、Godement–Jacquet）、GeometricLemma*、RestrictedHaarProduct（限直积上的 Haar 测度与 Euler 积）、HarishChandraCentre（对称多项式）… |
| `ProfiniteCohomology` | 450 | 84,902 | 上同调、Tate 上同调 |
| `GlobalFields` | 384 | 72,305 | 整体域、Frobenius、不变量 |
| `PAdicHodge` | 226 | 64,317 | p-adic Hodge（tilt、untilt、Breuil–Kisin 类） |
| `ArithmeticGeometry` | 218 | 45,046 | AbelianVarieties、ModularCurves、SchemeCohomology（正则局部环商、层上同调）、ToricVarieties（**Farkas / Weyl–Minkowski**）、IwasawaModules、KrullDomain |
| `LocalFields` | 159 | 40,767 | 局部域：tame 子扩张、分歧、赋值 |
| `TateCohomology` | 56 | 8,755 | Tate 上同调 |
| `Brauer` | 20 | 4,723 | Brauer 群 |
| `FunctionField`、`IdeleRoots`、`PowerSubgroups` | 42 | 6,996 | 函数域、理想元根、幂子群 |

`GroundTheory` 对外 import：→ ReciprocityTheory 1,161、→ Development 57、→ Formalism 10。

#### ReciprocityTheory（3,845 文件 / 563k 行）

| 二级目录 | 文件 | 行 | 内容 |
|---|---:|---:|---|
| `ReductiveGroups` | 2,799 | 409,976 | 约化群：DiscreteSeries、Casimir 代数、Bochner 不等式… |
| `L2DbarEstimates` | 227 | 33,734 | L² ∂̄ 估计（Levi 形式、Bergman 核、多次数调和） |
| `AnalyticForms` | 192 | 36,680 | 解析形式 |
| `SemistableReduction` | 119 | 14,578 | 半稳定约化 |
| `DualLattices` | 183 | 24,554 | 对偶格、Smith 标准形 |
| `ClassFieldTheory` | 91 | 11,830 | 类域论 |
| `GroupCohomology` | 56 | 8,227 | 群上同调；procyclic 稠密子群、模长度 |
| `Chebotarev` | 47 | 4,382 | Chebotarev：CrossRes/CrossFrobE/CrossLift/CrossFix/CrossGal、NormCongr、LatSum、SplitF、**NoWind（exp 纤维离散 ⇒ 局部有界）**、CyclotomicIrreducibleOfForallIsUnramifiedAt |
| `GeometryOfNumbers` | 39 | 5,256 | **通用线性代数/分析**：LatticeCovolumes（GramSt：Hadamard/Fischer/Minkowski 行列式不等式；CountZSt：格点计数）、PluriharmonicAnalysis（LogDetSt：**行列式求导**、Bernstein 积分；DiscSt：圆均值/极坐标）、AsymptoticSequences（幂和估计）、MatrixArithmetic（log 凹性） |
| `CommutativeAlgebra` | 26 | 3,014 | CohenMacaulay（**正则局部环是整环**、商掉正则元仍是正则局部环） |
| 其余 | 86 | ~14k | NeutralLocalFields、ResidueCardinality、GaloisValuations、ReducedBases、ThetaQuasiPeriods、AdeleApproximation、BurnsideSurjectivity、AdicCompleteness、GeneralLinearIntegers、ThetaSummability |

`ReciprocityTheory` 对外 import：→ Formalism 266、→ Lemmata 50。被 Development（38,051）、GroundTheory（1,161）、CompanionTheory（154）、Formalism（348）、PositivityTheory（2）import。

#### CompanionTheory（2,027 文件 / 194k 行）

`SpectralGeometry`（LocalGlobalProofs、CountingDefinitions）、`AutomorphicTheory`（PieriRules、BesselWaveGrids、ProductFormulaTheory、ZuckermanCommutation、ThetaDilations、SchurLimitBounds…）、`HarishChandraModules`（KFiniteAnalyticVectors、BesselParameterIntegrals、LowKTypeMultiplicity）、`RealGroups`（DiscreteSeries、FormalDegrees、GeneralUnitaryRepresentations、BaseChange）、`ThickeningEstimates`。伴生（companion）表示的局部-整体理论。对外 import：→ Development 1,437、→ Formalism 762、→ ReciprocityTheory 154、→ GroundTheory 65。

#### PositivityTheory（449 文件 / 55k 行）

`AutomorphicForms.PublishedInputs`（445 文件，"已发表定理的输入"）、`PublishedTheorems.{UnitKilling,TowerLemmas,WeilRepresentations}`、`Representations.BoundaryCones`。自守形式的正性（θ 核的正性、Weil 表示）。对外 import：→ Development 632、→ GroundTheory 111。

#### Lemmata（167 文件 / 9.2k 行）

作者的通用工具箱，**一个目录一条引理**（`Lemmata/<Topic>/<Decl>.lean`），145 个叶子文件只 import Mathlib，22 个带 `Imports.lean` 的目录是给大型证明用的"import 聚合器"（一个文件 import 上百个 Formalism 模块）。主题：LDU 分解（局部环上）、清除分母（数域格）、离散赋值环商的长度、特征向量线性无关、行列式单调、正定连续族、p-adic 赋值、多项式整除、Mellin/Fourier 小引理、Cauchy–Binet、群指标…（§2 表里 C50–C84 多数来自这里）。

#### Supplements / Statements / Main / BuildAid

`Statements.lean`（16 行，只 import Mathlib）：四个顶层命题 `RiemannZetaZerosOnLine`、`DirichletLNonvanishingRightOfHalf`、`DirichletLZerosOnLine`、`PrimitiveDirichletLZerosOnLine`。`Supplements/Kernels/MainTheorems.lean`（16 行）：把 `allChi`、`rhOfAll`、`critAll`、`claimAll` 接到 Mathlib 的 `RiemannHypothesis` 与 `Statements` 的四个命题上。`Main.lean`：5 条定理。`BuildAid/*.lean`：5 个 `run_cmd`，只往 Lean 的 library-suggestion deny list 里加命名空间，没有数学。

### 1.3 主线：从 Main.lean 往下追

```
Main.lean
└─ Supplements.Kernels.MainTheorems.lean
   ├─ rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
   │    Formalism/GammaFactorNonvanishing/CritLine.lean:29
   │    证明只用 Mathlib 的 ζ 函数方程（completedRiemannZeta_one_sub、riemannZeta_ne_zero_of_one_le_re）
   ├─ critAll := Formalism.VW.critLine allChi …      (同文件 :11，Dirichlet L 函数的函数方程)
   ├─ allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter
   │    Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10
   │    everyCharacter := everyCharacter_of_row Gal.Int.galoisLocalGlobalStrong_recParameter
   │    everyCharacter_of_row (h : Row0b recT) :=
   │        every_character_of_literature_of_vWin ⟨h, LLC.recTExists, h⟩ (One.vwin_of_row h)
   │        ├─ LiteratureTheorems.every_character_of_literature_of_vWin
   │        │    ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810（810 行）
   │        ├─ Zero.LLC.recTExists        Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20
   │        │    （局部 Langlands 递归的存在性：每个 (E,Ω,A,w) 都有 IsRecT h rc）
   │        ├─ One.vwin_of_row h           AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4
   │        │    := Join.automorphic_window_of_inputs (OpenImageCondition.mk h) (BaseChangeIdentities.baseChangeN h)
   │        │    → UpperTheory.Top.VWin（CharacterBoxes/ExistsPageN.lean:49：PageN/WinPair 窗口估计）
   │        └─ h : GalStar.Row0b IsRecT    Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69
   │             （CM 域上每个正则代数极化尖表示 π 都附带 Galois 表示 r、权 wt、HT，满足 PropsB…）
   │             := Gal.Int.galoisRepresentations_of_thetaLift TP.K.tLiftK
   │                Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6
   └─ claimAll := ⟨allChi, Claim.strip allChi, Claim.zeta allChi⟩
        CharacterBoxes/ClaimStrip.lean:59,75（半平面非零 ⇒ 临界带零点在临界线上 / ζ 的 RH；只用 Mathlib 的 LFunction_changeLevel、gammaFactor）
```

`EveryCharacter`（CharacterBoxes/EveryCharacter.lean:13，陈述只用 Mathlib 的 `DirichletCharacter.LFunction`）本身由 `plugAll`（:16）推出：

```
EveryCharacter ⟸ imprimitive (plugWin hG hV h)
  hG : GlobalTheory.GLq.Green          （解析输入："Green 函数"假设，来自 Formalism 的 Green/shape 定理）
  hV : UpperTheory.Top.VWin            （自守窗口，来自上面的 vwin_of_row）
  h  : Nonempty (Hyps (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) DRS)   （"假设可满足"）
  ⟹ Formalism.HC.ZeroFreeAll（Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18）
  ⟹ EveryCharacter（imprimitive：由本原特征 + LFunction_changeLevel 推到所有特征）
```

所以从命题依赖看，库分为五层：

1. **顶层 glue（Mathlib-only 命题）**：`EveryCharacter → RiemannHypothesis`（`Formalism.VW.rh_of_every`、`UpperTheory.riemannHypothesis_of_everyCharacter`、`Claim.strip/zeta`、`Formalism.VW.critLine`）。这几条定理陈述里只有 Mathlib 的 `riemannZeta`、`DirichletCharacter.LFunction`、`gammaFactor`、`completedRiemannZeta`，证明也只用 Mathlib 引理，**本身就是 Mathlib 候选**（"所有 Dirichlet L 函数在 Re s > 1/2 非零 ⇒ RH"）。
2. **Galois 表示层**（Development/AutomorphicArithmetic/Foundations/{GaloisRepresentations,LocalLanglands}）：从 θ 提升构造 Galois 表示，满足 `Row0b` 与局部 Langlands 相容性 `IsRecT`。
3. **自守窗口层**（AutomorphicVarieties/ModularityArgument、ThetaCorrespondence、CharacterBoxes）：`Row0b + recTExists → VWin → EveryCharacter`。
4. **解析核心层**（Formalism.LocalToGlobal / SharpRestriction / HermitianCurvature / PeriodIntegrals、ReciprocityTheory、CompanionTheory、PositivityTheory）：证明 `Green`、`Hyps` 非空、`Closed/LinkN` 等解析输入——库的主体。
5. **基础层**（GroundTheory、Development.AbelianVarietyTheory/Definitions、EtaleCohomology、ResolutionOfSingularities、Lemmata）：高度/θ 函数、上同调、p-adic Hodge、局部域、类域论、交换代数、通用引理。

### 1.4 对后续拆分有直接影响的观察

1. **import 图 ≠ 依赖锥**。几乎所有文件都 `import Mathlib`（整库），再 import 一长串"上游聚合文件"。一个 30 行的证明常常 import 100+ 个内部模块（例如 `Lemmata/GeneralBFactLeftAltForm/MQ.lean` 236 行、import 60 个模块）。真实依赖锥只有把证明单独放到只 import Mathlib 的环境里编译才能量出来。本次对 16 个候选文件做了这件事（§3.1），全部内部依赖为 0。
2. **顶层库之间有环**（Development ↔ Formalism、GroundTheory ↔ ReciprocityTheory、Lemmata ↔ Formalism），所以不能"按库整体迁移"；但**叶子文件可以**：5,927 个叶子文件是天然的无内部依赖单元。
3. **同一结果有重复副本**：`ReciprocityTheory/CommutativeAlgebra/MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne.lean` 与 `CohenMacaulay/RegGensA.lean` 内容完全相同（同样的 17 条定理，行号不同）；`Lemmata` 里"清除分母"一条引理有 20 多个变体文件（`GeneralBFactSecondAlt/SecondBisAlt/ThirdAlt/ThirdSide/ThirdTail/ThirdTer/…`，陈述几乎一样）。整理时要先去重。
4. **文件粒度极细**：平均一个文件 99 行、1 条声明； Development.AbelianVarietyTheory.Proofs.DivisorProofs 一个目录就有 42,424 个文件。"整体并入"的单位应该是目录/主题，而不是文件。
5. **陈述写法机器化**：`Lemmata` 里很多 `theorem goal1` 用 `Eq.{1}`、`DFunLike.coe.{…}` 等完全展开的形式，需要改写成 Mathlib 风格的可读陈述（§3 做了示范）。

---

## 2. 候选引理表

### 2.1 方法

1. **找"只用 Mathlib 概念"的陈述**：叶子文件（只 import Mathlib，5,927 个）里的非 private 定理，陈述文本不引用同文件 `def/structure/abbrev/instance` 的，共 11,955 条（`analysis/leaf_statements.py`，充分条件）。非叶子文件里也有只用 Mathlib 概念的引理（例如 `Lemmata/DetMonotoneStarMulSelf/OneLeReReDetOneAdd.lean` 里的 private `det_mono`），靠人工读文件补充。
2. **依赖锥**：对叶子文件，内部依赖恒为 0；对非叶子文件，import 列表严重高估（§1.4）。本次对 16 个候选文件做了"只 import Mathlib 原样编译"的实测（§3.1），全部通过，依赖 0。
3. **Mathlib 核实**：固定版 `extracted/.lake/packages/mathlib/Mathlib`（commit `0df444a3`）。`analysis/mathlib_check.py` 对 86 组候选各用 5–15 个同名/同义正则搜声明行（结果 `analysis/mathlib_checks.txt`），再对关键项（`RegularLocalRing`、`InnerProductSpace/Spectrum`、`Convex/Cone/Dual*`、`KrullDimension/Regular`、`Eigenspace/*`、`JointEigenspace`）人工读源码确认。
4. **优先级**：线性代数 / 分析 / 凸几何 / 交换代数 / 拓扑群 等通用领域优先；纯自守表示、θ 函数、迹公式相关的不列入（它们本身就是要单独讨论的"块"）。

表内列："依赖"= 证明需要的本项目内部声明数（叶子文件 = 0；"0*" = 文件 import 很多但证明只用 Mathlib，已实测）；"Mathlib"= `无` / `已有：名字` / `部分：说明`；难度 1（几行）– 5（数百行、需重构）。★ = 已做进试点（§3）。

### 2.2 候选表（52 条）

| # | 名字（源 → 建议） | 文件:行（`source/src/`） | 命题一句话 | 依赖 | Mathlib | 为什么值得并入 | 难度 |
|---|---|---|---|---|---|---|---|
| 1★ | `gramSt_det_re_le_of_sub` → `Matrix.PosDef.det_re_mono` | ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean:30 | G 正定、H−G 半正定 ⇒ Re det G ≤ Re det H（Minkowski） | 0 | 无（只有 `posDef_iff_det_ne_zero`） | 凸几何、格、统计、矩阵分析；Mathlib 的 `PosDef` API 缺单调性 | 2 |
| 2★ | `gramSt_hadamard` → `Matrix.PosDef.det_re_le_prod_diag_re` | 同上:119 | Hadamard 行列式不等式 Re det D ≤ ∏ Re D ii | 0 | 无 | 经典、通用 | 2 |
| 3★ | `gramSt_fischer` → `…fromBlocks` | 同上:68 | Fischer 不等式：分块正定阵 det ≤ det A · det D | 0 | 无 | 经典、通用 | 2 |
| 4★ | `hasDerivAt_det` → `Matrix.hasDerivAt_det` | ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean:31 | Jacobi 公式：det 沿路径的导数 = tr(adj(G t)·G′) | 0 | 无（只有多项式导数版 `derivative_det_one_add_X_smul`） | Liouville 公式、矩阵分析 | 2 |
| 5★ | `hasDerivAt_log_det` → `Matrix.hasDerivAt_log_det_re` | 同上:57 | log det 的导数 = Re tr(G⁻¹ G′)（正定族） | 0 | 无 | 信息几何、优化 | 2 |
| 6 | `Bl.b110.goal1` | Lemmata/B110/ExistsMoved.lean:18 | A 0 = 1 且各项可导 ⇒ det∘A 在 0 处导数 = trace A′ | 0 | 无（同 #4 系列） | #4 的特例，短 | 1 |
| 7★ | `Bl.general_b_fact.goal1` → `Matrix.det_mul_eq_sum_over_functions` | Lemmata/GeneralBFact/Imports.lean:8 | Cauchy–Binet：det(AB) = Σ_f ∏ A a (f a) · det(B.submatrix f id) | 0 | 无 | 组合、概率、格 | 2 |
| 8★ | `det_mulLeft_matrix`, `det_mulRight_matrix` | GroundTheory/AutomorphicForms/RealGroupsHaar.lean:20,33 | det(左/右乘 A 作用于 n×n 矩阵空间) = (det A)^n | 0 | Mathlib 的 `LinearMap.det_mulLeft` 是 R 作为 R-模的版本，矩阵版无 | Haar 测度、李群、行列式论 | 2 |
| 9★ | `det_restrictScalars_mulLeft/Right` | 同上:256,261 | 复矩阵左乘视为实算子 det = (‖det A‖²)^n | 0 | 无 | 同上 | 2 |
| 10★ | `perm_eq_one_of_forall_le` → `Equiv.Perm.eq_one_of_forall_le` | GroundTheory/AutomorphicForms/FiniteBruhat.lean:83 | 置换 π 满足 ∀x, π x ≤ x ⇒ π = 1 | 0 | 无 | 组合小引理 | 1 |
| 11★ | `exists_isSymm_mul_eq_transpose_mul` | GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean:372 | 任意方阵与转置相似，且相似矩阵可取对称可逆 S（S A = Aᵀ S） | 0 | 无 | 经典线性代数；"对称相似"版本更强 | 3 |
| 12★ | `exists_cyclic_decomposition` | 同上:220 | Frobenius/rational 标准形存在：F^n ≅ ⨁ F[X]/(q i)，q i ∣ charpoly | 0 | 无（Mathlib 只有 PID 上模分解 `Module.equiv_directSum_of_isTorsion`） | 线性代数核心 | 3 |
| 13★ | `continuous_charpoly_coeff` | 同上:183,200 | A ↦ charpoly.coeff k 连续（拓扑域） | 0 | 无 | 亦含 `ContCoeff` API | 2 |
| 14★ | `finite_monic_dvd` | 同上:459 | 非零多项式的首一因子只有有限个 | 0 | 无 | UFD 基础 | 1 |
| 15★ | `exists_countable_conj_charpoly` | 同上:474 | 给定 charpoly 的 GL(n,F) 共轭类可数 | 0 | 无 | 代数（需 #11–14） | 3 |
| 16★ | `Bl.SecondBlockLemmaB.goal1` → `Matrix.exists_ldu_decomposition` | Lemmata/MiscLemmasA/Imports.lean:5 | 局部环上带理想约束的 LDU 型分解（单位对角） | 0 | 无 | 代数 K 理论、群表示 | 2 |
| 17★ | `Bl.PosDefOfRealQuadratic.goal1` → `Matrix.PosDef.eventually` | Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean:25 | 连续 Hermite 矩阵族在正定点附近保持正定 | 0 | 无 | 优化、矩阵分析 | 2 |
| 18 | `Bl.DetMonotoneStarMulSelf.det_mono`（private） | Lemmata/DetMonotoneStarMulSelf/OneLeReDetOneAdd.lean:40 | 同 #1（重复副本） | 0 | — | 去重即可 | — |
| 19 | `Bl.general_b_fact_left_last.goal1` | Lemmata/GeneralBFactLeftLast/Pz.lean:14 | 交换算子 A B：A 的 a-广义特征空间 ∩ B 的 b-广义特征空间 ⊆ AB 的 ab-广义特征空间 | 0 | 部分：`mapsTo_maxGenEigenspace_of_comm`（无乘积版） | 线性代数 | 2 |
| 20 | `Bl.general_b_fact_extra.goal1` | Lemmata/GeneralBFactExtra/Imports.lean:5 | 一族算子的不同特征值的同时特征向量线性无关（Dedekind–Artin 型） | 0 | 无（未找到 `LinearIndependent` of distinct chars） | 表示论 | 2 |
| 21 | `Bl.general_b_fact_second_ter_form.goal1` | Lemmata/GeneralBFactSecondTerForm/Imports.lean:45 | 不同特征值向量 χ 的公共特征空间族 `iSupIndep` | 0 | 无 | 表示论 | 2 |
| 22 | `Bl.general_b_fact_left_more.goal1` | Lemmata/GeneralBFactLeftMore/Imports.lean:9 | a − C(eval p a) ∈ span {X i − C (p i)} | 0 | 无 | 交换代数、代数几何 | 2 |
| 23 | `Bl.GeneralBFactThirdBis.goal1` | Lemmata/GeneralBFactThirdBis/Imports.lean:7 | 稳定 𝓞_E-格的矩阵 trace 是代数整数 | 0 | 变体：`Algebra.isIntegral_trace` 是域扩张版 | 数论、格 | 2 |
| 24 | `Bl.GeneralBFactThirdAltForm.goal1` | Lemmata/GeneralBFactThirdAltForm/Imports.lean:5 | 子环上同一模的两组基，过渡矩阵 P Q = 1 | 0 | 无 | 数论、格 | 2 |
| 25 | `Bl.GeneralBFactForm.goal1` | Lemmata/GeneralBFactForm/Imports.lean:5 | LDU（块三角）分解唯一性 | 0 | 无 | 代数 | 3 |
| 26 | `Bl.GeneralBFactRightVersion.goal1` | Lemmata/GeneralBFactRightVersion/Imports.lean:5 | 代数整元在 E-自同构下轨道有限：∃ n ≠ 0, σⁿ y = y | 0 | 无（有 `AlgEquiv.isIntegral_iff`） | 数论 | 2 |
| 27 | `Bl.GeneralBFactSecondVersion.goal1` | Lemmata/GeneralBFactSecondVersion/Imports.lean:5 | W 半单、S 单、Ann W ⊆ Ann S ⇒ Hom(W,S) ≠ 0 | 0 | 部分：`linearEquiv_of_ne_zero` 给后半 | 模表示论 | 2 |
| 28 | `Bl.FirstBlockLemmaB.goal1` | Lemmata/FirstBlockLemmaB/Imports.lean:7 | P ≤ Q 素理想、x ∈ Q∖P ⇒ dim(R/Q)+1 ≤ dim(R/P) | 0 | 部分：`ringKrullDim_quotient_le`, `Ideal.height_le_ringKrullDim_quotient_add_one` | 交换代数 | 2 |
| 29 | `Bl.DiscreteValuationQuotients.goal1` | Lemmata/DiscreteValuationQuotients/LenQuotSpan.lean:32 | DVR 上自由模单自同态余核长度 = addVal(det) | 0 | 变体：`length_quotient_pow_maximalIdeal` | 交换代数、格 | 3 |
| 30 | `Bl.VolumeRatioCancellation.goal1` | Lemmata/Cancellation/EnnrealVolumeRatioStepCancel.lean:12 | Dedekind 整环：有限个位素上带赋值上界的弱逼近 | 0 | 无直接版本（需复核 `IsDedekindDomain` 逼近 API） | 数论 | 3 |
| 31 | `Bl.ComplementLifts.goal1` | Lemmata/ComplementLifts/ComplLift.lean:29 | PID 上包含已补子模的子模仍有补 | 0 | 部分：除环版 `Submodule.exists_isCompl` | 模论 | 2 |
| 32 | `Bl.DenominatorsAlt.goal1` / `Bl.IntegerMulIntegral.goal1` | Lemmata/Denominators/Denom.lean:25；Lemmata/IntegerMulIntegral/IntMulIntegral.lean:11 | z ∈ span_K L（L 为 𝓞_E-格）⇒ ∃ d ≠ 0, d • z ∈ L | 0 | 无直接版本 | 数论、格（源里有 20+ 重复变体，需合并） | 2 |
| 33 | `Bl.FirstBlockLemmaL.goal1` | Lemmata/FirstBlockLemmaL/Imports.lean:5 | padicValNat ℓ (∏ s) = ∑ padicValNat ℓ（多重集） | 0 | 无 | 数论 | 1 |
| 34 | `Bl.FirstBlockLemmaK.goal1` | Lemmata/FirstBlockLemmaK/Imports.lean:5 | 增广理想幂零的增广代数：IsUnit(aug a) ⇒ IsUnit a | 0 | 无（有 `isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub`，需比对） | 环论 | 2 |
| 35 | `Bl.FirstBlockLemmaE.goal1` | Lemmata/FirstBlockLemmaE/Imports.lean:5 | x² = x + c（c ∈ ℤ）⇒ x 是代数整数 | 0 | 无 | 初等数论 | 1 |
| 36 | `Bl.FirstBlockLemmaG/I.goal1` | Lemmata/FirstBlockLemmaG,FirstBlockLemmaI/Imports.lean:5 | IsUnit a, m ∈ 𝔪 ⇒ IsUnit(a−m)；z ∈ Jac(0) ⇒ IsUnit(u+z) | 0 | 可由 `isUnit_one_sub_self_of_mem_nonunits`, `isUnit_of_sub_one_mem_jacobson_bot` 1–3 行推出 | 不必单独并入 | 1 |
| 37★ | `IsRegularLocalRing.isDomain`（+ `quotient_span_singleton`, `ringKrullDim_quotient_span_singleton_add_one`, `exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes`） | ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean:378, 276, 284, 239 | 正则局部环是整环；商掉 𝔪∖𝔪² 中元仍正则局部、维数减一；素避引理 | 0 | **无**（`RegularLocalRing/Defs.lean` 明写 TODO；`KrullDimension/Regular.lean` 有 Krull 维数版商公式） | Mathlib 正在发展的方向，直接补 TODO | 4 |
| 38 | `maximalIdeal_eq_bot_of_le_sq` | 同上:231 | Noether 局部环 𝔪 ≤ 𝔪² ⇒ 𝔪 = 0 | 0 | 可由 `maximalIdeal_sq_lt_maximalIdeal` 2 行推出 | 不必单独并入 | 1 |
| 39★ | `CompactSelfAdjoint.*`（14 条：`exists_hilbertBasis_eigenvectors`, `…_hasSum`, `exists_hilbertBasis_common_eigenvectors`, `finite_eigenvalues_norm_ge`, `countable_spectrum`, `zero_mem_spectrum`, …） | GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean:13–339 | 紧自伴算子谱定理（Hilbert 基形式、展开形式、交换族共同特征基） | 0 | **无**（`InnerProductSpace/Spectrum.lean` 只到"特征空间余补为 0、特征空间有限维"，明写 TODO） | 泛函分析核心；可整体并入 | 4 |
| 40★ | `isDiscrete_exp_fiber`, `bdd_of_exp_tendsto` | ReciprocityTheory/Chebotarev/NoWind.lean:7,89 | exp 纤维离散；exp(f s) → L≠0 ⇒ f 局部有界 | 0 | 无 | 复分析 | 2 |
| 41★ | `integral_bernstein` | ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean:140 | ∫₀¹ C(D,i) t^i(1−t)^{D−i} = 1/(D+1)（Bernstein 基积分） | 0 | 无 | 逼近论；可挂到 `SpecialFunctions/Bernstein.lean` | 2 |
| 42★ | `tent`, `Tent`, `hasSum_Tent_add_int`, `abs_prod_sub_prod_le_sum_abs_sub` | ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean:7–116 | tent 函数是 1-Lipschitz 单位分解 ∑ₙ tent(t+n) = 1；乘积版；|∏a−∏b| ≤ Σ|a−b| | 0 | 无 | 调和分析、解析数论 | 2 |
| 43★ | `fibre_sum_le`, `fibre_sum_ge` | ReciprocityTheory/Chebotarev/SplitF.lean:7,35 | 纤维基数一致有界/一致大时，Σ f 与 Σ h 的比较 | 0 | 部分：`tsum_fiberwise`（ℝ≥0∞ 版） | 求和法 | 2 |
| 44★ | `Toric.*`（14 条：`exists_dual_neg_of_not_mem`, `fg_inf_halfspace`, `fg_dual`, `dual_dual_flip_of_fg`, `fg_iff_dualFG`…） | GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean:12–219 | 有限生成锥的代数 Farkas 引理与 Weyl–Minkowski 定理 | 0 | 部分：Mathlib 有闭锥的 `ProperCone.hyperplane_separation` 和 `DualFG` API，无代数 Farkas / `FG ↔ DualFG` | 线性规划、环面几何、数论 | 3 |
| 45 | `analyticAt_of_norm_iteratedFDeriv_le` | GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean:47 | C^∞ 且迭代 FDeriv 有 Cauchy 型界 ⇒ 解析 | 0 | **无**（正向 `AnalyticAt ⇒ 界` 已有） | 分析 | 3 |
| 46 | `sum_bounds` | ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean:33 | n^{k+1} ≤ (k+1)Σ_{a≤n} a^k ≤ n^{k+1}+(k+1)n^k | 0 | 无 | 初等不等式 | 1 |
| 47 | `wma_sum_log_le` | ReciprocityTheory/GeometryOfNumbers/MatrixArithmetic/WeakMatSt.lean:5 | Σ log(1+t σ) ≤ N log(1+(Σt)/N) | 0 | 无 | 初等不等式（Jensen 型） | 1 |
| 48 | `Bl.general_b_fact_bis_form.goal1` | Lemmata/GeneralBFactBisForm/Imports.lean:7 | 球上全纯、模 ≤ C ⇒ ‖fderiv f y‖ ≤ C/R（Cauchy 估计） | 0 | 未找到（需复核 `Complex.cauchyIntegral*` API） | 复分析 | 2 |
| 49 | `UpperTheory.riemannHypothesis_of_everyCharacter` | Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215 | (∀N χ s, Re s > 1/2 ⇒ L(χ,s) ≠ 0) ⇒ `RiemannHypothesis`（Mathlib 的定义） | 0*（文件 import 50 个模块，证明只用 Mathlib；已实测，见 §3.1） | 无 | 解析数论；Mathlib 的 `RiemannHypothesis` 旁正缺"GRH ⇒ RH"的推导 | 2 |
| 50 | `Formalism.VW.rh_of_right` + `Formalism.VW.rh_of_every` | Formalism/GammaFactorNonvanishing/RhOfRight.lean:5; CritLine.lean:29 | (ζ 在 Re s > 1/2 非零) ⇒ `RiemannHypothesis`；再由 L(1,s) = ζ(s) 归结 | 0*（`rh_of_right` 62 行，实测通过） | 无 | 同上；ζ 函数方程 + Gamma 非零 + cos 零点的标准推导 | 2 |
| 51 | `Formalism.VW.critLine`, `Formalism.VW.gammaFactor_ne_zero` | Formalism/GammaFactorNonvanishing/CritLine.lean:11,6 | (所有 Dirichlet L 函数在 Re s > 1/2 非零) ⇒ 本原 L 函数带内零点在 Re s = 1/2（GRH） | 0*（实测通过） | 无（`DirichletCharacter.gammaFactor` 非零性 Mathlib 没有） | 同上 | 2 |
| 52 | `Claim.strip`, `Claim.zeta`, `Claim.zeta_iff`, `Claim.prim_zero`, `Claim.prim_reflect` | Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59,75,102,23,42 | 半平面非零 ⇒ 带内零点在线上；⇒ ζ 的 RH；本原化与反射引理 | 0*（依赖 `HalfPlane.lean` 只 import Mathlib；`Factor`/`gammaFactor` 引理为 Mathlib 概念） | 无（`LFunction_changeLevel`、`completedLFunction_one_sub` 已有，组合是新的） | 同上 | 2 |

### 2.3 Mathlib 里已有的（不并入，记名字）

| 源 | 位置 | Mathlib 对应 |
|---|---|---|
| `len_sub_add_quot` | ReciprocityTheory/GroupCohomology/RankLenA.lean:26 | `Module.length_eq_add_of_exact`, `Module.length_quotient` |
| `len_quot_pow` | 同上:54 | `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`（变体） |
| `isClosed_eigenspace`, `hasEigenvalue_of_mem_spectrum` | GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean:21,151 | `ContinuousLinearMap.isClosed_eigenspace`, `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` |
| `finite_setOf_mem_of_orthonormal` | 同上:13 | `LinearIndependent.finite_of_isNoetherian`（2 行推论） |
| `exists_norm_iteratedFDeriv_le_of_analyticAt` | PartialDifferential/AnalyticHypoSeries.lean:240 | `AnalyticAt.norm_iteratedFDeriv_le`（`Analysis/Calculus/FDeriv/Analytic.lean:793`） |
| `lieGroup_GL` | GroundTheory/AutomorphicForms/RealGroupsLie.lean:174 | `LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ`（`Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean`），取 `V = Matrix n n 𝕜` 即得 |
| `Bl.GeneralBFactRightSide.goal1` | Lemmata/GeneralBFactRightSide/Imports.lean:7 | `Complex.exp_eq_one_iff` |
| `Bl.general_b_fact_right_bis.goal1` | Lemmata/GeneralBFactRightBis/Imports.lean:7 | `Module.End.hasEigenvalue_of_isRoot`, `hasEigenvector_iff` |
| `Bl.GeneralBFactLeftForm.goal1` | Lemmata/GeneralBFactLeftForm/Imports.lean:8 | `Finset.lt_card_filter_univ_iff_apply_of_imp` |
| `Bl.GeneralBFactLeftRest.goal1` | Lemmata/GeneralBFactLeftRest/Imports.lean:7 | `Subgroup.index_ker`, `Subgroup.index_eq_card` |
| `integral_fourier_mul_eq` | GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean:10 | `integral_fourier_smul_eq`（Schwartz 版；源是可积函数版，属变体） |
| `pgds_integral_ball_polar` | ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/DiscSt.lean:17 | `Complex.polarCoord`, `integral_comp_polarCoord_symm`（可推出） |
| `Lp_two_norm_sq_eq_integral` | GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean:336 | `L2Space`：`inner_self_eq_norm_sq_to_K` 等（疑似，需核对陈述） |
| `Bl.general_b_fact_right_variant.goal1` | Lemmata/GeneralBFactRightVariant/Imports.lean:7 | `Ideal.IsPrime.prod_mem_iff_exists_mem` + `Nat.prod_primeFactors` 可推出 |
| `isGalois_cyclotomicField`, `classGroup_mulEquiv_mk0` 等 | ReciprocityTheory/Chebotarev/CrossGal.lean:21; NeutralLocalFields/…/HilbertClassFieldA.lean:17,42 | `IsCyclotomicExtension` / `ClassGroup` API（疑似，需核对） |

---

## 3. 试点

### 3.1 源文件原样编译（依赖锥实测）

把 16 个候选源文件原样复制到 `extracted/scratch/src/`，用 `lake env lean` 在只 import Mathlib 的环境里编译（每个文件一个进程，峰值内存 ≈ 5.7 GB，所以最多两个并行）：

| 源文件（`source/src/`） | 行数 | 结果 | 用时 |
|---|---:|---|---:|
| ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean | 153 | 通过 | 14 s |
| ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean | 154 | 通过 | 37 s |
| GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean（含 `set_option maxSynthPendingDepth 1`） | 368 | 通过 | 101 s |
| ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean | 388 | 通过 | 18 s |
| ReciprocityTheory/Chebotarev/NoWind.lean | 95 | 通过 | 116 s |
| ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean | 125 | 通过 | 31 s |
| ReciprocityTheory/Chebotarev/SplitF.lean | 86 | 通过 | 19 s |
| Lemmata/GeneralBFact/Imports.lean | 25 | 通过 | 24 s |
| GroundTheory/AutomorphicForms/FiniteBruhat.lean | 358 | 通过 | 17 s |
| GroundTheory/AutomorphicForms/RealGroupsHaar.lean | 367 | 通过 | 18 s |
| GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean | 509 | 通过 | 19 s |
| Lemmata/MiscLemmasA/Imports.lean | 160 | 通过 | 39 s |
| Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean | 83 | 通过 | 40 s |
| ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean | 115 | 通过 | 14 s |
| ReciprocityTheory/GeometryOfNumbers/MatrixArithmetic/WeakMatSt.lean | 27 | 通过 | 25 s |
| GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean | 235 | 通过 | 59 s |

结论：**16 个文件的内部依赖锥都是 0**（用时差异主要来自首次读 Mathlib olean 的磁盘缓存，以及 `import Mathlib` 整库的装载时间）。

另外对主线 glue 做了同样的事：把 `UpperTheory.EveryCharacter` 的定义内联（它本来就是 Mathlib-only 的 def），`Formalism.VW.rh_of_right`（62 行）原样编译通过（104 s），`RiemannHypothesisOfEveryCharacter.lean` 去掉 50 个内部 import 后编译通过（279 s），`CritLine.lean` 中 `critLine`/`rh_of_every` 的证明在 `rh_of_right` 作为 `sorry` 占位的情况下通过（17 s，说明这两条只用 Mathlib + `rh_of_right`）；`ClaimStrip.lean` 的唯一内部依赖 `HalfPlane.lean` 只有 `import Mathlib` 和 3 个 def。所以候选表 #49–52 的"0*"是实测结论。

### 3.2 整理后的试点项目 `extracted/`

Lake 项目 `rhlemmas`，lean-toolchain `v4.33.1`，Mathlib pin 与 `source/lakefile.toml` 相同（`0df444a3…`），依赖 revision 直接复制自 `source/lake-manifest.json`。`lake exe cache get` 20 分钟（Mathlib 7.1 GB）。构建：`lake build -K jobs=4` 通过（3,450 jobs，44 s）。

整理原则：每个文件开头写明出处与原文件行号；只 import 需要的 Mathlib 子模块（不再 `import Mathlib`，单文件编译 5–50 s）；去掉 `set_option`、`first | … | …` 版本兼容分支；机器化陈述（`goal1`、`Eq.{1}`、`abelian₂`）改写为可读陈述；按 Mathlib 命名放到合适的命名空间（`Matrix.`、`Matrix.PosDef.`、`IsCompactOperator.`、`IsRegularLocalRing.`、`PointedCone.`、`LinearMap.`、`Real.`、`Complex.`…）；删掉与 Mathlib 重复的引理（`isClosed_eigenspace`, `hasEigenvalue_of_mem_spectrum`, `posDef_det_re_pos`, `det_re_le_of_sub_posSemidef`）。

| 试点文件（`extracted/src/RhLemmas/…`） | 来源文件（行号） | 内容 | 定理数 | 行数（源→新） | 备注 |
|---|---|---|---:|---|---|
| `Analysis/Matrix/PosDef/Det.lean` | GramSt.lean (:12–143) | Minkowski/Fischer/Hadamard 行列式不等式、`det_one_add_eq_prod` | 6 | 153→165 | 删 2 条重复陈述；去掉 `try rw` |
| `Analysis/Matrix/Deriv.lean` | LogDetSt.lean (:8–57) | Jacobi 行列式求导、log det 求导 | 2（+1 private） | 50→90 | `first` 分支固定为 `fun_finsetProd`/`fun_sum` |
| `Analysis/SpecialFunctions/BernsteinIntegral.lean` | LogDetSt.lean (:78–152) | Beta 积分自然数版、Bernstein 基积分 = 1/(D+1) | 4（+1 def） | 75→105 | 最终定理用 `bernsteinPolynomial` 陈述 |
| `Analysis/SpecialFunctions/Complex/ExpFiber.lean` | NoWind.lean (:7–93) | exp 纤维离散；exp(f)→L≠0 ⇒ f 有界 | 3 | 95→130 | **推广**：区间 `Ioc 1 2` → `Ioc a b`，`𝓝[>] 1` → `𝓝[>] a` |
| `Analysis/InnerProductSpace/CompactSelfAdjoint.lean` | CompactSelfAdjoint.lean (:13–364) | 紧自伴算子谱定理（单算子 + 交换族） | 14 | 368→400 | 去掉 `maxSynthPendingDepth`；删 2 条与 Mathlib 重复的 |
| `RingTheory/RegularLocalRing/Domain.lean` | RegGensA.lean (:11–384) | 正则局部环是整环（+ 商、素避、Nakayama 引理、实例） | 12（+4 private, 1 instance） | 388→370 | 通用引理用 `_root_` 放到 `Ideal.`/`Module.Basis.`/`IsLocalRing.` |
| `Geometry/Convex/Cone/DualFinite.lean` | ExistsDualNegOfNotMemHullFinset.lean (:12–231) | 代数 Farkas、`fg_inf_halfspace`、Weyl–Minkowski、`FG ↔ DualFG` | 14 | 235→270 | 命名空间 → `PointedCone`；证明未改 |
| `Analysis/SpecialFunctions/Tent.lean` | AbsProdSubProdLeSumAbsSub.lean (:7–121) | tent 函数、`tentProd` 单位分解、`|∏a−∏b| ≤ Σ|a−b|` | 18 | 125→150 | `tent`→`Real.tent`，`Tent`→`Real.tentProd` |
| `Topology/Algebra/InfiniteSum/Fiberwise.lean` | SplitF.lean (:7–84) | 纤维求和可和性比较 | 2 | 86→75 | 删掉未用的 `S.Finite` 假设 |
| `LinearAlgebra/Matrix/Det.lean` | GeneralBFact/Imports.lean:8；RealGroupsHaar.lean:12–48,256–264；FiniteBruhat.lean:83 | Cauchy–Binet、det(mulLeft/mulRight)、实化 det、置换引理 | 6 | —→110 | 三个文件合成一个 |
| `LinearAlgebra/Matrix/Similarity.lean` | MatrixSimilarity.lean (:13–509) | Frobenius 标准形、与转置相似、charpoly 系数连续、首一因子有限、共轭类可数 | 46（含 API） | 509→540 | 命名空间 → `MatrixSimilarity`；证明未改 |
| `LinearAlgebra/Matrix/LDU.lean` | MiscLemmasA/Imports.lean:5 | 局部环上 LDU 分解 | 1 | 160→75 | `goal1` 改写为可读陈述 |
| `Analysis/Matrix/PosDef/Open.lean` | QuadFormRealSmul.lean (:7–81) | 正定是开条件 | 1（+3 private） | 83→75 | `goal1` 的全展开陈述改写 |
| `RhLemmas.lean`（根） | — | 汇总 import + 出处说明 | — | 20 | |

合计 13 个文件、2,850 行、**89 条公开定理**。

### 3.3 公理检查

`extracted/Axioms.lean`（在库外，`lake env lean Axioms.lean`）对 89 条公开定理逐条 `#print axioms`，输出保存在 `extracted/axioms.txt`：89 条全部是

```
'…' depends on axioms: [propext, Classical.choice, Quot.sound]
```

没有 `sorryAx`，没有其它公理（`lake build` 本身也保证了无 `sorry`）。

### 3.4 试点里做的改写（举例）

- `Bl.PosDefOfRealQuadratic.goal1` 原陈述是 30 行 `@Matrix.IsHermitian.{0, 0} Complex (Fin m) (@InvolutiveStar.toStar …)` 的全展开形式；改为
  ```lean
  theorem Matrix.PosDef.eventually {X : Type*} [TopologicalSpace X] {m : ℕ}
      (A : X → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ i j, Continuous fun x => A x i j)
      (hH : ∀ x, (A x).IsHermitian) {x0 : X} (h0 : (A x0).PosDef) :
      ∀ᶠ x in 𝓝 x0, (A x).PosDef
  ```
- `bounded_of_tendsto_exp` 原来只对区间 `Ioc 1 2` 陈述（`abelian₂`、`L1` 是自动命名）；推广为任意 `Ioc a b`，并把最终结论拆成 `Complex.exists_norm_le_of_tendsto_exp`（有界）和 `Complex.eventually_norm_le_of_tendsto_exp`（最终有界）。
- `Real.integral_bernstein` 用 Mathlib 已有的 `Polynomial.bernsteinPolynomial` 陈述：`∫ t in (0..1), (bernsteinPolynomial ℝ D i).eval t = 1 / (D + 1)`。
- `CompactSelfAdjoint.lean` 开头的 `set_option maxSynthPendingDepth 1` 去掉后照常编译。

### 3.5 移植到 Mathlib master 与第一批 PR（步骤 5）

- **fork**：https://github.com/CocoSgt/mathlib4（基线 upstream/master `a495318f`，toolchain `v4.37.0-rc1`，比钉住的 `0df444a3` 新 2696 个提交）。
- **选了 3 条最干净、最通用的试点**，先在 master 源码里核实不存在（master 只有 `PosDef.det_pos`、`PosSemidef.det_nonneg`、`derivative_det_one_add_X_smul`、`det_mul`），再移植、推广、过 Mathlib 的 linter（`lake build --wfail`、`lake exe lint-style`、`lake exe mk_all --check`）：
  1. `Analysis/Matrix/PosDef/Det.lean` → `Mathlib/Analysis/Matrix/Order.lean`：Minkowski / Fischer / Hadamard 行列式不等式，6 条定理，从 ℂ 推广到 `RCLike 𝕜`（master 的 PosDef 理论已经是 `RCLike` 的；`CFC.sqrt` 和 Loewner 序都在这个文件里，所以放这里而不是 `PosDef.lean`——后者被 `Order.lean` import，不能反向）。
  2. `Analysis/Matrix/Deriv.lean` → 新文件 `Mathlib/Analysis/Matrix/Deriv.lean`：Jacobi 公式 `hasDerivAt_det` + `hasDerivAt_log_det_re`，推广到任意有限指标集、任意赋范交换 `𝕜`-代数 / `RCLike`。
  3. `LinearAlgebra/Matrix/Det.lean` 里的 Cauchy–Binet → `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`：`det_mul_eq_sum_over_functions`，推广到任意指标集。
- **移植时遇到的变化**（08-21 → 11-21 的 Mathlib）：(a) `ComplexOrder` 的 `≤` 现在要求虚部相等（`z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`），所以陈述用 `RCLike.re`；(b) 类型变量 `𝕜` 上不能用 `.re` 这种字段记法（"Field projection operates on types of the form C ..."），要写 `RCLike.re`；(c) `Finset.prod_le_prod` 现在要 `[MulLeftMono]`（ℝ 没有），改用 `Finset.prod_le_prod₀`；(d) 数字投影 `.2` 被 linter 禁止，用 `.property`；(e) `unusedSectionVars` / `unusedDecidableInType` linter 要求 `omit [DecidableEq n] in`；(f) 新文件要 `lake exe mk_all` 更新 `Mathlib.lean`。
- **PR**（都由 GLM 5.4 通过 DeepSeek Harness 开，说明里写了原文件:行号、镜像链接、出处和 license 提醒；提交信息带 `Co-authored-by: Levent Alpöge <alpoge@fas.harvard.edu>`，文件头 Authors 加 Levent Alpöge）：

| PR | 内容 | CI |
|---|---|---|
| [#46339](https://github.com/leanprover-community/mathlib4/pull/46339) | `feat(Analysis/Matrix/Order): add Minkowski, Fischer and Hadamard determinant inequalities` | 见 PROGRESS.md 最后一行 |
| [#46340](https://github.com/leanprover-community/mathlib4/pull/46340) | `feat(Analysis/Matrix/Deriv): add Jacobi's formula for the derivative of the determinant` | 同上 |
| [#46341](https://github.com/leanprover-community/mathlib4/pull/46341) | `feat(LinearAlgebra/Matrix/Determinant): add the Cauchy–Binet formula as a sum over functions` | 同上 |

- 没有放进第一批但已经整理好、可以直接移植的：Bernstein 基积分、`det_mulLeft/mulRight`（矩阵空间上左/右乘的行列式）、`Equiv.Perm.eq_one_of_forall_le`、tent 函数单位分解、紧自伴谱定理、正则局部环是整环、Farkas / Weyl–Minkowski（后三个较大，需要拆分并与 master 的新进展比对）。

---

## 4. 遇到的问题

1. **Lake 版本**：这台机器的 Lake 5.0.0 没有 `-j`/`--jobs`，并发要用 `-K jobs=4`（环境变量 `LAKE_JOBS` 未见效）。TASK 里的"`lake build -j 4`"在 REPORT/NEXT 里都按 `-K jobs=4` 写。
2. **内存**：任何 `import Mathlib` 的文件，单个 `lean` 进程峰值 ≈ 5.7 GB；`lake build` 时 Mathlib 的 3,400 多个 olean 只是校验不重编，所以整体很快（44 s）。整理后的文件只 import 子模块，单个 5–50 s。
3. **Mathlib 这个版本启用了新的 module 系统**（`module` / `public import` / `public section`），而且很多"想当然"的文件名不存在（`Mathlib/Analysis/Matrix.lean`、`Mathlib/Analysis/SpecialFunctions/Complex/Exp.lean`、`Mathlib/Data/Set/Ncard.lean`、`Mathlib/Topology/Algebra/InfiniteSum/BigOperators.lean` 都没有），每个文件都要试 2–4 轮才能把 import 收敛到最小集。这对后续批量抽取是个工程量：建议写一个"从全库 import 出发逐步删"的脚本（见 NEXT.md 阶段 0）。
4. **import 列表 ≠ 依赖锥**：这是对拆分最重要的发现。举例子：`Lemmata/GeneralBFactLeftAltForm/MQ.lean`（236 行）import 60 个内部模块，`Formalism/GammaFactorNonvanishing/CritLine.lean` import 2 个聚合文件（传递闭包覆盖半个库），但两者的证明都只用 Mathlib。候选表里"依赖 0*"的条目都是实测出来的。
5. **重复副本多**：`RegGensA.lean` 与 `MaximalIdealSquares/RingKrullDimQuotientSpanSingletonAddOne.lean` 完全相同（17 条定理）；`Lemmata` 里"清除分母"有 20 多个变体文件；`gramSt_det_re_le_of_sub` 与 `DetMonotoneStarMulSelf.det_mono` 是同一条。整理前要先去重（`analysis/leaf_theorems.jsonl` 里按陈述文本聚类即可）。
6. **陈述机器化**：`Lemmata` 里大量 `theorem goal1 : ∀ …, Eq.{1} (DFunLike.coe.{…} …)`，变量名 `abelian₂`、`inst✝`、`L1`，需要逐条改写（试点改了 5 条，每条 5–15 分钟）。
7. **版本兼容分支**：源文件里大量 `first | exact A | exact B | simpa using C` 是为了跨 Mathlib 版本编译，整理时要固定到一个分支（试点固定了 4 处：`HasDerivAt.fun_finsetProd`/`fun_sum`、`simp` 参数）。
8. **`#print axioms` 只能在库外跑**（它是命令不是定理），所以做成 `Axioms.lean` 脚本 + 保存的输出；若想在 CI 里强制，可用 `lean4checker` 或在脚本里 `#guard_msgs` 匹配输出。
9. **实例风险**：`IsRegularLocalRing.instIsDomain`（priority 100）是源文件给的实例，Mathlib 里 `IsRegularLocalRing` 的实例（PID ⇒ 正则局部环）需要 `IsDomain`，可能形成实例搜索环；是否保留需 Mathlib 维护者判断（§5）。
10. **网络**：`lake exe cache get` 20 分钟，Mathlib 7.1 GB，磁盘 65 GB 剩余；后续如果要编译更多原文件，`scratch/` 的做法（一次一个、5.7 GB）是可行的，但不能 `lake build` 整个 `source/`。

---

## 5. 待人工确认

1. **各库的"数学内容"描述**（§1.2）主要来自目录名和抽样定理陈述，源文件几乎没有 module docstring；特别是 `Development.AbelianVarietyTheory`（8.1M 行）的子目录名（DivisorProofs、InertiaEigenvalues、IwasawaDecomposition、TwistedOperators、FlagMeasures…）更像自守表示/迹公式的材料而非阿贝尔簇理论，需要读过证明的人确认。
2. **`IsRegularLocalRing.instIsDomain` 实例**是否适合进 Mathlib（priority、与 `IsRegularLocalRing` 其它实例的相互依赖）。
3. **Mathlib 已有性**里标"疑似/需复核"的几条：Cauchy 估计（#48：`‖fderiv f y‖ ≤ C/R`，Mathlib 可能藏在 `Complex.cauchyIntegral*` 里）、`Lp_two_norm_sq_eq_integral`、Dedekind 整环弱逼近（#30）、`isGalois_cyclotomicField`、`ClassGroup` 相关引理。本报告按"搜索词未命中"记为未找到，不等价于"确定没有"。
4. **#28（Krull 维数商不等式）**和 **#29（DVR 余核长度）**可能从 Mathlib 现有结果几行推出，归入"变体/可推出"还是"新结果"需人工判断。
5. **推广是否忠实**：`Complex.exists_norm_le_of_tendsto_exp` 把区间从 `Ioc 1 2` 推广到 `Ioc a b`、`Real.integral_bernstein` 改用 `bernsteinPolynomial` 陈述、`tsum_ge_mul_tsum_of_ncard_fiber_ge` 删掉了未用的 `S.Finite`——数学上都是等价或更一般的，但若要回馈 Mathlib 需维护者确认陈述形式。
6. **源头说明**：原代码没有 license 文件（镜像 README 也说明"published without a stated license"）；并入 Mathlib 前需要 Alpöge 明确授权。
