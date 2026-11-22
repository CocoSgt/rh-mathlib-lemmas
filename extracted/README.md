# extracted — 试点项目：从 Alpöge–Claude 黎曼猜想形式化里抽出的通用引理

> 所有数学与证明来自 **Levent Alpöge（与 Claude）** 的 Lean 形式化（https://alpo.ge/，2026-11-20）。
> 这里只是查找、改写、补 docstring、编译验证；每个文件头都写了原文件与行号。

## 构建

```bash
cd extracted
lake exe cache get          # 首次：约 20 分钟，Mathlib 7.1 GB
lake build -K jobs=4        # Lake 5.0.0 没有 -j；用 -K jobs=N 控制并发
lake env lean Axioms.lean   # 对 89 条公开定理做 #print axioms（输出见 axioms.txt）
```

- Lean `v4.33.1`，Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`（与 `source/` 相同，依赖 revision 复制自 `source/lake-manifest.json`）。
- 每个文件只 import 需要的 Mathlib 子模块（单文件 `lake env lean <file>` 5–50 s）。

## 文件与出处

| 文件 | 内容 | 原文件（`source/src/`） |
|---|---|---|
| `RhLemmas/Analysis/Matrix/PosDef/Det.lean` | Minkowski / Fischer / Hadamard 行列式不等式 | `ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/GramSt.lean` |
| `RhLemmas/Analysis/Matrix/Deriv.lean` | Jacobi 行列式求导、log det 求导 | `ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/LogDetSt.lean` |
| `RhLemmas/Analysis/Matrix/PosDef/Open.lean` | 正定是开条件 | `Lemmata/PosDefOfRealQuadratic/QuadFormRealSmul.lean` |
| `RhLemmas/Analysis/SpecialFunctions/BernsteinIntegral.lean` | Beta 积分（自然数）、Bernstein 基积分 | `…/PluriharmonicAnalysis/LogDetSt.lean` |
| `RhLemmas/Analysis/SpecialFunctions/Complex/ExpFiber.lean` | exp 纤维离散、exp(f)→L≠0 ⇒ f 局部有界 | `ReciprocityTheory/Chebotarev/NoWind.lean` |
| `RhLemmas/Analysis/SpecialFunctions/Tent.lean` | tent 函数单位分解 | `ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean` |
| `RhLemmas/Analysis/InnerProductSpace/CompactSelfAdjoint.lean` | 紧自伴算子谱定理 | `GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean` |
| `RhLemmas/Geometry/Convex/Cone/DualFinite.lean` | 代数 Farkas、Weyl–Minkowski | `GroundTheory/ArithmeticGeometry/ToricVarieties/ExistsDualNegOfNotMemHullFinset.lean` |
| `RhLemmas/LinearAlgebra/Matrix/Det.lean` | Cauchy–Binet、det(左/右乘)、置换引理 | `Lemmata/GeneralBFact/Imports.lean`，`GroundTheory/AutomorphicForms/{RealGroupsHaar,FiniteBruhat}.lean` |
| `RhLemmas/LinearAlgebra/Matrix/Similarity.lean` | Frobenius 标准形、与转置相似、charpoly 系数连续 | `GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean` |
| `RhLemmas/LinearAlgebra/Matrix/LDU.lean` | 局部环上 LDU 分解 | `Lemmata/MiscLemmasA/Imports.lean` |
| `RhLemmas/RingTheory/RegularLocalRing/Domain.lean` | 正则局部环是整环 | `ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean` |
| `RhLemmas/Topology/Algebra/InfiniteSum/Fiberwise.lean` | 纤维求和可和性 | `ReciprocityTheory/Chebotarev/SplitF.lean` |

`scratch/` 是原样复制后只 import Mathlib 编译的 16 个候选源文件 + 4 个 glue 文件的编译日志（`compile_summary.txt`），用于证明依赖锥为 0。

详见 `../REPORT.md`（结构图、候选表、试点结果）与 `../NEXT.md`（后续计划）。
