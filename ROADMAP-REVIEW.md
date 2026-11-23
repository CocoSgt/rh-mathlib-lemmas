# ROADMAP-REVIEW — 对路线图草稿 `roadmap/CharactersOfGLnOverFiniteFields/` 的自审（TASK.md 第 7 步 e）

> 这是**作者的自审**（GLM 5.4 通过 DeepSeek Harness），不是另一位贡献者的审稿。按 `TauCetiRoadmap/CONTRIBUTING.md`「Reviewing a roadmap」的四个方面各审一遍，再对照 `TauCetiRoadmap/README.md`「Writing a roadmap」的清单逐条核对；每条写清查了什么、没查什么。拿不准的数学列在 §6「待人工确认」。自审过程中**改掉了三处我自己写错的陈述**，记在 §1.3，请重点看。

## 0. 审的对象

- `roadmap/CharactersOfGLnOverFiniteFields/README.md`（1023 行）、`Suggested.lean`（461 行）、`metadata.toml`（`topic = "math.RT"`）。
- 编译：`source .run/env.sh && cd mathlib4 && lake env lean <绝对路径>/Suggested.lean`，mathlib4 在分支 `posdef-det-inequalities`（Lean v4.37.0-rc1，未切分支、未改文件）：**exit 0，0 个 error，31 条 `declaration uses 'sorry'` 警告**（31 条定理的证明都是 `sorry`；全部 `def` 都有真实定义体，包括 `psi` 的良基递归）。日志 `.run/step7-roadmap/lean-final.log`（前面的迭代在 `lean1.log` … `lean9.log`）。

## 1. 方面一：包含什么（是不是 Tau Ceti 想要的数学）

**查了什么。**
- 范围的选择过程与候选比较写在 `ROADMAP-SURVEY.md` §5：A 顶层衔接（与 QuasiRH/ZerosOfLFunctions 重叠）、B 陈述层（`VWin` 是未被使用的谓词）、**C Green 分类（选）**、D L2→L3 解析部分（最低一级远高于已形式化）、E L1（与 AG-II 同目标）。选 C 的理由：主线上唯一"陈述与证明只依赖 Mathlib"的一块，Tau Ceti 没有，可复用。
- 与 Tau Ceti 的重叠：用 grep 核对过 (i) `RepresentationTheory/CharacterTheory` Layer 9 只有 GL₂(𝔽_q)，并明说 Deligne–Lusztig "neither is planned in this roadmap"（README 第 1533–1534 行）；(ii) TauCeti 库里 `RepresentationTheory/CharacterTable/GL2/*`（`GL2CuspidalVirtualCharacter`、`GL2Steinberg`、`GL2PrincipalSeries`、`Classification.lean`）；(iii) 全部路线图里没有 "Green's parametrization/cuspidal characters of GL_n(F_q)"（`survey-T3.md` U6）。所以不重叠，GL₂ 表写成 supplier 与 Check。
- 是否值得做：Green 定理是有限群李型表示论的经典入口（Zelevinsky、Deligne–Lusztig 的前置），Mathlib 没有（grep：没有 n 次首一不可约多项式个数的公式，没有子空间计数公式，没有 Green 定理）。

**没查什么。** 没有请领域专家判断"这块数学该不该进 Tau Ceti、该做多深"；没有核对 `SmoothRepresentationsOfLocalGroups` 是否真的会用它（Downstream consumers 一节写的是"供给深度零超尖表示的有限域一侧"，那两个路线图只在秩一的例子里碰到深度零）。范围是 `Suggested.lean` 之外由我定的，**De Song 可能更想先要别的部分**（见 §6.1）。

## 2. 方面二：怎么做（层与接口是否表达预期的数学、是否接到已有的库）

**查了什么。**
- **接口能否在 pin 上写出来**：`Suggested.lean` 整个文件编译通过。为此改了三处 Mathlib master 的 API 名：`ArithmeticFunction.moebius`（不是 `Möbius`）、`starRingEnd ℂ`（master 没有 `Complex.conj`）、`GL (Fin n) F` 是 `Matrix.GeneralLinearGroup` 的记号（即 `(Matrix …)ˣ`，但需要 `[Fintype F]` 才有 `Fintype` 实例）。所有定理陈述都按 `Suggested.lean` 的定义写成 Lean，不是只在 markdown 里说。
- **定义名**：`glPairing`、`IsIrreducibleCharacter`、`virtualCharacters` 在 README 里明确对应 Tau Ceti 的 `TauCeti.ClassFunction.characterPairing`、`TauCeti.irreducibleCharacters`、`TauCeti.virtualCharacters`（grep 核对过这些声明存在：`RepresentationTheory/CharacterTable/{Pairing,Table,VirtualCharacter}.lean`）；`Matrix.charpoly`、`LinearMap.charpoly`、`Matrix.card_GL_field`、`charpoly_mulVecLin`、`LinearEquiv.charpoly_conj`、`Submodule.finrank_lt`、`ArithmeticFunction.moebius`、`UniqueFactorizationMonoid.normalizedFactors`、`FDRep.char_orthonormal`、`IsCyclic Gal(L/K)`（`Mathlib/FieldTheory/Finite/Basic.lean:409`）都 grep 到了定义处。
- **层间依赖没有前向引用**：1 → 2 → 3（3.6、3.7 用 4.7）→ 4 → 5 → 6 → 7（7.6 用 3.5、7.3；7.9 用 7.5、7.7、7.8）→ 8。3.6/3.7 的 route 引用 4.7，README 的 Dependencies 一节写明了。
- **满射性的计数**：我最初的 route（"不同多重集的诱导正交 ⇒ 多重集个数 ≤ 共轭类数"）**不成立**：GL₂(F) 有 `q² − 1` 个共轭类（数量级大于 `q² − q`），这个界不够关掉 Green 定理的归纳。改成源码的做法：generic 成分（Whittaker 泛函非零）存在 + generic 不可约特征标至多 `qⁿ − qⁿ⁻¹` 个。**这两步（7.7(d)、7.8）的 route 我只写了大纲，见 §6.3。**

**没查什么。** 没有逐条核对 Tau Ceti 里 `TauCeti/RepresentationTheory/Induction/ClassFunction.lean` 与 `Mackey/` 的具体声明名（README 的 supplier contract 只写到模块，并注明"以 InductionRestriction 路线图的 contract 为准"）；没有核对 `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean` 里到底有什么（只在 GL2/Classification.lean 的 import 里见到它）；没有读 `SmoothRepresentationsOfLocalGroups` 全文来确认深度零的节号（只 grep 到第 3493、3542 行与 PartII §4.8）。

## 3. 方面三：Tau Ceti 格式

**查了什么（对照 Writing a roadmap 与 Laying out the README）。**
- 标题 `# Roadmap: …`；概述以 `**Summary.**` 开头，用普通数学语言陈述三条 headline 及其实际假设，说明它建在 `RepresentationTheory.CharacterTheory` 上、供给深度零一侧与 roadmap-for-a-roadmap 的系列，末尾有一段逐层导读；概述里没有 Lean 名字、行号。随后是 `## How to read the build`、`## Conventions`、`## Layer 1…8`（按搭建顺序）、`## Downstream consumers`、`## Scope and ownership`（Owned here / Consumed, not redefined / Not owned here）、`## Exact supplier contracts`（`### From Mathlib`、`### From Tau Ceti`、`### From TauCetiRoadmap.RepresentationTheory.CharacterTheory`、`### From TauCetiRoadmap.RepresentationTheory.InductionRestriction`）、`## Roadmap for a roadmap (not work to attempt now)`、`## Provenance (secondary)`、`## References`。
- **Build the library**：每层都有定义的 API（1.1–1.4 的计数、2.2–2.4 的类尺寸与密度、3.3 的抛物结构、4.2–4.7 的 ψ 的性质、7.1 的传递性、7.5 的 Mackey），不是只奔定理。
- **No gaps**：最低一级（多项式、有限维向量空间、特征多项式、`GL`、`FDRep`）全在 Mathlib；Tau Ceti 的部分写成 supplier；每条的 route 只引用本路线图更早的节或 supplier。
- **无歧义**：每条陈述都在 `Suggested.lean` 里有对应的 Lean 陈述（README 的编号与 `Suggested.lean` 的编号逐条对上；2.4、4.7、5.3、6.4、7.1 的 API 只有 markdown 陈述）。
- **范围明确**：grep 过 optional / deferred / for later / TODO / placeholder / upstream，都没有；Not owned here 列了 GL₂ 表、Zelevinsky 分类、Deligne–Lusztig、光滑表示、其它李型有限群。
- **timeless**：正文没有提 PR、审稿或争论；Alpöge–Claude 的对照只在 Provenance（标明 secondary）与 Roadmap-for-a-roadmap 里；license 问题只写在那里。
- **roadmap-for-a-roadmap**：标题明写 "(not work to attempt now)"，首段写明"Contributors must not attempt it… nothing in it may be cited as a target"。
- **Prototyping**：`Suggested.lean` 开头是标准说明（"This file is not the roadmap…"），没有 `Prop` 型字段或 `def _ : Prop := sorry`；不能 import 的 Tau Ceti 接口写在 markdown 里。
- **Filing**：`metadata.toml` = `topic = "math.RT"`（Green 1955 的论文归 math.RT）。
- **Porting existing work**：README 写的是数学，没有照搬源码的命名（`PChar`、`Gn`、`hcT`、`IsPrimeLab` 等都没出现）；逐文件对照在 Provenance。

**没查什么。** 没有跑 `python3 .github/scripts/check_roadmap_topics.py`（不编译、不跑 Tau Ceti 仓库的脚本）；没有对照 `WeilPositivityAndLiCriterion` 那种"Route + **Checks.** + *Needs:* + ### Examples + ### Dependencies"逐层检查每层是否都齐全（Layer 1–8 每层都有 Examples 与 Dependencies，Checks 放在我觉得有价值的小节）。Summary 的篇幅比多数已合并路线图长。

## 4. 方面四：反复细查（数学错误、缺口、一致性）

**查了什么。**
- **每个 Check 手算过**：`N_q(1) = q`、`N_q(2) = q(q−1)/2`、`N₂(3) = 2`、`N₂(6) = (64−8−4+2)/6 = 9`、`N₃(2) = 3`；GL₂(𝔽₂) 阶 6、椭圆类大小 2；ψ(deg) 在 n = 2 的四个值（2、1−q、1、0）与 `Σ_{U₁} = 0`；GL₂ 尖特征标在数量矩阵 `(q−1)λ(s)`、Jordan 类 `−λ(s)`、椭圆 `−θ(z)−θ(z^q)`；`Σ_{u∈U} ψ(u₁₂)·St(u) = q`；`n = 2` 的多重集计数 `q(q−1)/2 + (q−1)q/2 = q² − q`；GL₃(𝔽₂) 阶 168、两个 3 次尖特征标、Frobenius 轨道 {3,6,5}；1.3 里 `k qᵈ ≡ k` 的解恰有 `q^d − 1` 个；2.2 一般类的中心化子阶 `q^{d(m−1)}(q^d−1)`；2.4 的 `μ(X−a) = 1/(q−1)`。
- **我改掉的三处错误**（都是初稿写错、自查时发现的）：
  1. 初稿写"尖特征标 ⟺ 不可约且在特征多项式可约的元素上为 0"。**错**：GL₂ 的尖特征标在数量矩阵上取 `(q−1)λ(s)`，在 Jordan 元素上取 `−λ(s)`，都非零。改成：尖特征标在"特征多项式有两个不同不可约因子"的元素上为 0（3.6），且由椭圆元素上的值决定（3.7）；常项的消失与对单幂根求和的消失等价（3.5）。
  2. 初稿写"ψ 只依赖特征多项式"。**错**：恒等元与 Jordan 块有相同的特征多项式 `(X−a)²`，但 ψ(deg) 分别是 `1−q` 与 `1`。改成只陈述共轭不变（4.3）。
  3. 初稿有"`GLₙ(F)` 的共轭类数是 `qⁿ − qⁿ⁻¹`"。**错**：GL₂(F) 有 `q² − 1` 个类。删掉了这条（`Suggested.lean` 里的 `card_classes` 也删了），满射性改走 generic 成分的路线。
- **编译**：三次结构性改动（Layer 7/8 重排、`toGL`/`parabolic`/`blockDiag` 提前到 3.3）后都重新编译到 exit 0。
- **引用一致性**：README 的节号在重排后逐处改过（grep `7\.|8\.` 核对）；Summary、How to read the build、Scope、Provenance 里的节号已同步。

**没查什么。** 没有逐行通读 README 全文做文字校对（写得很赶，可能有句子不通顺或残留的措辞问题）；没有核对 References 里的卷号页码（见 §6.5）；没有核对 Roadmap for a roadmap 里引用的其它路线图的节号与行号（来自 `survey-T2.md`、`survey-T3.md`，我只抽查了 SmoothRepresentationsOfLocalGroups 的两处）；`Suggested.lean` 的 31 条陈述只保证了"能写出来"，没有验证它们的真实性（它们对应源码里有证明的陈述，但我没有逐条与源码对拍）。

## 5. 对照 Writing a roadmap 的清单

| 条目 | 结论 |
|---|---|
| Build the library, don't race to the theorem | 有 API；2.4、4.7、7.1 的部分 API 只在 markdown |
| No gaps | 最低一级 Mathlib；**7.7(d)、7.8 的 route 是大纲**（§6.3） |
| Every item unambiguous | 都有 Lean 陈述或精确的数学陈述 |
| Clear boundaries | Scope 三小节；与 CharacterTheory Layer 9 的边界写明 |
| Be definite about scope | 没有 optional/deferred/later；roadmap-for-a-roadmap 明确标出 |
| Roadmaps are timeless | 正文不提 PR/审稿；Alpöge–Claude 只在 Provenance/R4R |
| Aim for reusable | 子空间计数、根幂和、HC 诱导、Jacquet 限制都可独立复用 |
| Use Mathlib's vocabulary | `Matrix.charpoly`、`LinearMap.charpoly`、`GL`、`ConjClasses`、`FDRep`；`GL` 在 master 是 `GeneralLinearGroup` 的记号 |
| Defer to Mathlib / never wait / never push | 没有往 Mathlib 推的东西；Mathlib 没有的（Green 定理、计数）在这里建 |
| Specify the mathematics, not your existing code | 源码命名全部没有进入 README |
| Coordinate first | Provenance 与 R4R 末尾写明"release 没有 license 文件，先与作者协商" |
| Checks are sanity checks | 每条都手算；有一条（2.4 的 μ）自查时改正 |
| Import existing Tau Ceti APIs | `Suggested.lean` 只 import Mathlib（按任务要求）；Tau Ceti 接口写在 markdown |
| Pin conventions | Conventions 一节 9 条 |
| Give it an arXiv topic | `math.RT` |

## 6. 待人工确认

1. **范围**（最重要）：第一份路线图选 Green 分类而不是主线的别处，是我的判断。理由与其它候选见 `ROADMAP-SURVEY.md` §5。请 De Song 决定是否接受这个起点；如果不接受，`Suggested.lean` 与 README 的结构可以整体套到别的范围上。
2. **7.7(d)「每个尖诱导都有 generic 成分」与 7.8「generic 不可约特征标至多 `qⁿ − qⁿ⁻¹` 个」**：陈述照源码（`exists_generic_constituent_harishChandra_cuspidal`、`ncard_generic_irreducible_characters_GLn_le`）的意思写的，但 route 只有大纲。我自己核对过的只有：GL₂ 的 `{χ, χ}` 的 generic 成分是 Steinberg 扭曲（`Σ_{u∈U} ψ(u₁₂)St(u) = q`），`{ρ,ρ}` 的情形按 Zelevinsky 应有一个 generic 成分；「带重复的尖特征标的多重集没有 generic 成分」我**没有**把握（初稿写过又删了）。请熟悉 Green/Zelevinsky 证明的人补这两条 route，或者换成源码里的 Parseval 型论证（`ParsevalBoundIntegerVectorSmallFourierSupport`、`SeparationNumericalIneqCuspidalGL`、`NoNormEightOfFourierVanishingOrderFifteen`、`NoNormTwelveOrderSixtythree`，含 `(q,n) = (2,4)`、`(2,6)` 两个例外情形的数值引理）。
3. **5.1、5.3（根幂和与 ψ 是虚拟特征标）的 route**：按"对 n 归纳 + 完全旗标上的交错和"写的，没有逐条对照源码（`RootPowerSumCharpolyMemVirtualCharactersGL`）。
4. **4.7 的三条 primitivity 陈述、4.5 的质量公式、2.4 的三条计数**：陈述照源码（`CharacterTheory/*Statement.lean`）转写，route 是我按经典做法补的，细节未核。
5. **References 的卷号页码**没有联网核对（Green 1955 Trans. AMS 80 402–447；Zelevinsky 1981 LNM 869；Macdonald 1995 Ch. IV；Digne–Michel 2020 LMSST 95；Deligne–Lusztig 1976 Ann. Math. 103 103–161；Steinberg 1965 IHÉS 25 49–80 与 1951 Canad. J. Math. 3 225–235；Mackey 1951 AJM 73 576–592；Curtis–Reiner 1987）。Macdonald 的章节、Digne–Michel 的章节没有写具体节号。
6. **Downstream consumers 里对 `SmoothRepresentationsOfLocalGroups`(+PartII) 的描述**（"只在秩一里碰到深度零"）来自 grep，没有通读。
7. **Provenance 表**用的是源码的**文件名**（每文件一条声明），没有写定理名，因为源码的定理名大小写混用（`GlobalTheory.T.exists_teichmullerMap_algebraicClosure_finiteField`、`…T.frobeniusTorusCharacterOrthogonality`），怕抄错；需要时按文件名去找。
8. `Suggested.lean` 的 `IsRegular`、`unipotentRadical`、`parabolic` 把 `F` 写成显式参数（否则实例推断卡住），与 Tau Ceti 的写法可能不一致；`hcL` 的定义里对次数不加总为 `n` 的 list 返回 `0`（junk 值），README 的 Conventions 写明了。
