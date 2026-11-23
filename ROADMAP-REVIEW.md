# ROADMAP-REVIEW — 对路线图草稿 `roadmap/CharactersOfGLnOverFiniteFields/` 的自审（TASK.md 第 7 步 e；§7 是第 8 步的增补）

> 这是**作者的自审**（GLM 5.4 通过 DeepSeek Harness），不是另一位贡献者的审稿。按 `TauCetiRoadmap/CONTRIBUTING.md`「Reviewing a roadmap」的四个方面各审一遍，再对照 `TauCetiRoadmap/README.md`「Writing a roadmap」的清单逐条核对；每条写清查了什么、没查什么。拿不准的数学列在 §6「待人工确认」。自审过程中**改掉了三处我自己写错的陈述**，记在 §1.3，请重点看。

## 0. 审的对象

> §0–§6 审的是第 7 步的稿子（只 import Mathlib、在 mathlib4 master 上 `lake env lean`）。第 8 步把它改成用 Tau Ceti 自己的声明、在 TauCetiRoadmap 的环境里编译，改动与新增的自审写在 §7；§0–§6 里的编译数字（v4.37.0-rc1、31 条 sorry）是第 7 步时的状态。

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

## 7. 第 8 步改了什么（按 Tau Ceti 自己的环境改一轮）

### 7.1 换掉的自定义声明 → Tau Ceti 声明

名字都在 `tauceti-build/TauCetiRoadmap/.lake/packages/TauCeti/`（TauCeti `2fd255d99`）的源码里 grep 核实过（索引在 `.run/step8-tauceti/decls.txt`，脚本 `chk.sh`），文件路径以 `TauCeti/` 开头。

| 第 7 步稿里自己写的 | 现在 | Tau Ceti 里的声明（文件） |
|---|---|---|
| `glPairing n φ ψ = |G|⁻¹ ∑ φ * conj ψ`（任意函数上的配对） | `TauCeti.ClassFunction.characterPairing φ ψ` | `TauCeti/RepresentationTheory/CharacterTable/Pairing.lean`：`characterPairing`、`characterPairing_apply`（`|G|⁻¹ ∑ g, f₁ g * f₂ g⁻¹`）、`characterPairing_symm`、`characterPairing_nondegenerate`、`characterPairing_ofFDRep_orthonormal`、`characterPairing_ofFDRep_self`、`characterPairing_ofFDRep_eq_zero` |
| `IsIrreducibleCharacter n χ`（`∃ V : FDRep, Simple V ∧ …`） | `χ.1 ∈ TauCeti.irreducibleCharacters ℂ (GL (Fin n) F)` | `CharacterTable/Table.lean`：`irreducibleCharacters`、`mem_irreducibleCharacters_iff`、`character_mem_irreducibleCharacters`、`irreducibleCharacter` |
| 虚拟特征标 `∃ V W : FDRep ℂ G, ∀ x, f x = V.character x - W.character x` | `f ∈ TauCeti.virtualCharacters ℂ G` | `CharacterTable/VirtualCharacter.lean`：`virtualCharacters`、`mem_virtualCharacters_iff_exists_eq_character_sub_character`（与原来的写法等价）、`virtualCharacters_le_classFunction`、`conj_apply_of_mem_virtualCharacters`、`exists_eq_irreducibleCharacter_or_neg`、`mem_irreducibleCharacters_of_characterPairing_self_eq_one`、`exists_simple_character_eq_of_characterPairing_self_eq_one` |
| `upperUnitriangular n : Finset (GL (Fin n) F)` | `TauCeti.upperUnitriangularGroup (Fin n) F`（子群，求和写成 `∑ u : TauCeti.upperUnitriangularGroup (Fin n) F`） | `LinearAlgebra/Matrix/GeneralLinearGroup/UpperUnitriangular/Basic.lean` |
| Harish–Chandra 诱导：`|Pₐ|⁻¹ ∑_{y, y⁻¹xy ∈ Pₐ} α (A) * β (B)`（自己写的余弦和） | `Subgroup.indClassFunction (parabolic F n a) (leviInflate n a b h α β)` | `RepresentationTheory/Induction/ClassFunction.lean`：`Subgroup.indClassFun`、`indClassFunction`、`indClassFun_apply`、`indClassFun_eq_natCard_inv_mul_sum`（对类函数就是原来那个公式）；`Induction/VirtualCharacter.lean`：`indClassFun_mem_virtualCharacters`；`Induction/FrobeniusReciprocity.lean`：`characterPairing_ind`、`frobenius_reciprocity_classFunction`（7.3 的 route 用）；`Induction/Mackey/Basic.lean`：`mackeySubgroup`、`mackeyClassFun`、`indClassFun_mackey`（7.5 的 route 用） |
| GL₂ 尖特征标（第 7 步只在 README 里提了名字） | 新增 Check `gl2Cuspidal_character`，直接引用 `TauCeti.ClassFunction.ofFDRep (TauCeti.GL2Cuspidal θ hθ)` 与 `TauCeti.GL2NonSplitTorusHom F K u` | `CharacterTable/GL2/Cuspidal/Irreducible.lean`：`GL2Cuspidal`、`character_GL2Cuspidal`、`finrank_GL2Cuspidal`、`simple_GL2Cuspidal`、`GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`；`Cuspidal/Basic.lean`：`GL2CuspidalVirtualCharacter` 及四个取值；`GeneralLinearGroup/NonSplitTorus.lean`：`GL2NonSplitTorusHom` |
| Mathlib 侧的佐证（`Module.AEval'`） | `Module.AEval`（pin 的 Mathlib `1b1ccf4b` 里已没有 `AEVal'`） | `Mathlib/Algebra/Polynomial/Module/AEval.lean` |

只进 README、不进 `Suggested.lean` 签名但写进 supplier contract 的 Tau Ceti 声明：`TauCeti.FiniteField.orbit_eq_rootSet_minpoly`、`natCard_orbit_eq_natDegree_minpoly`、`mem_orbit_iff_minpoly_eq`、`exists_monic_irreducible_natDegree_eq`（1.1）；`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite`（1.4）；`TauCeti.upperTriangularGroup`、`GL2Borel`、`lineStabilizer`、`hyperplaneStabilizer`、`exists_mem_doubleCoset_permutationGL`（3.3 的 Checks、7.5）；`GL2NonSplitTorus.natCard_eq`、`natCard_GL_fin_two`、`ncard_carrier_mk_of_forall_mul_self_ne`、`natCard_centralizer_diagGL`、`natCard_centralizer_jordanGL`、`exists_isConj_normalForm`、`card_conjClasses_GL2`（2.2、2.5 的 `n = 2`）。

### 7.2 仍然自己定义的部分，和原因

| 定义 | 为什么不换成 Tau Ceti 的 |
|---|---|
| `parabolic F n a`、`unipotentRadical F n a`（一般分块 `a`, `n - a`） | Tau Ceti 只有上三角子群 `upperTriangularGroup`、`GL2Borel`，以及两条极大抛物 `lineStabilizer`、`hyperplaneStabilizer`（分块 `(1, n - 1)`、`(n - 1, 1)`）。现在定义成 `Subgroup (GL (Fin n) F)`，`parabolic` 用 Mathlib 的 `Matrix.BlockTriangular`（证明与 Tau Ceti 自己定义 `upperTriangularGroup` 的写法相同），`mem_parabolic_iff` 给出矩阵元素的写法，`unipotentRadical_le_parabolic` 有真实证明；与 Tau Ceti 那三个子群的一致性写成 3.3 的 Checks |
| `toGL`、`blockDiag`、`levi`、`leviInflate`、`hcL`、`jacquetRestrict`、`superdiagonalSum`、`whittakerFunctional` | Tau Ceti 里没有一般的 Levi 投影、列表上的迭代 Harish–Chandra 诱导、Jacquet 限制、Whittaker 泛函（GL₂ 的诱导是 `GL2EllipticInduction` 等具体表示，不是一般定义）。诱导这一步本身已经换成 `Subgroup.indClassFunction`，自己定义的只有从抛物子群到 Levi 的提升和沿列表的迭代 |
| `IsCuspidalCharacter`、`IsRegular` | Tau Ceti 没有这两个谓词（`GL2CuspidalVirtualCharacter` 是具体的构造，不是"尖"的定义）。不可约性这一半已经是 `irreducibleCharacters` 的成员资格 |
| `psi`、`mass`、`rootPowerSum`、`rootPowerSumClassFunction`、`psiClassFunction`、`chiK` | Green 的构造本身，Tau Ceti 与 Mathlib 都没有 |

`rootPowerSumClassFunction`、`psiClassFunction`、`leviInflate`、`jacquetRestrict` 是把本路线图的函数打包成 `TauCeti.ClassFunction` 的包装：打包要的类函数性单独写成定理（`psi_classFunction`、`leviInflate_mem_classFunction`、`jacquetRestrict_mem_classFunction`，都是 sorry；`rootPowerSumClassFunction` 的类函数性用 Mathlib 的 `Matrix.charpoly_units_conj` 当场证出）。

### 7.3 连带改动

- **载体**：`GLₙ(F)` 上的函数一律改成 `TauCeti.ClassFunction ℂ (GL (Fin n) F)`（Tau Ceti 的配对、诱导、`GL2Cuspidal` 都定义在这个载体上，`TauCeti.ClassFunction` 在 module 系统下不暴露定义，别的模块只能经 `TauCeti.ClassFunction.mem_iff` 造元素）。列表元素类型相应变成 `Σ d : ℕ, TauCeti.ClassFunction ℂ (GL (Fin d) F)`。
- **`IsRegular` 与 7.10 (ii)**：Frobenius 共轭写成 `θ.comp (powMonoidHom (q ^ i))`（Tau Ceti GL₂ 文件的写法，`powMonoidHom` 是 Mathlib 的），与原来的逐点幂 `θ ^ (q ^ i)` 相等（`θ (u ^ m) = θ u ^ m`）。
- **`[DecidableEq F]`**：加到变量行，使各处的 `Fintype (GL (Fin n) F)` 实例一致（Tau Ceti 的配对定理也带 `[DecidableEq F]`）。
- **新增**：1.4 的 `rootPowerSum_orthogonality`（在 `Kˣ` 上，经一个 `F`-嵌入；源码 `frobeniusTorus_character_orthogonality` 是在代数闭包的 `qⁿ - 1` 次单位根上求有限和）；README 新增 2.5 非分裂环面 `nsTorus`（5.1 的 route 原先说"从非分裂环面诱导的类函数"，但这个对象没有被定义，是 No gaps 上的一个洞）；6.5 Check `gl2Cuspidal_character`。
- **`hcL` 的 junk 值**保持原稿的约定（次数不加总为 `n` 时为 `0`），与源码不同，写在 Provenance 里。

### 7.4 核对源码时改正的错误（都是第 7 步稿子里的）

1. **5.2 多了一个因子**。原稿写 `⟨ψₖ, Ψ_l⟩ = |GL (Fin n) F| * #{i < n : k q^i ≡ l}`，取自源码 `ipGL_psi_rootSum`；但源码的 `ipGL φ φ' = ∑ᶠ g, φ g * star (φ' g)` 是**未归一化**的群上求和，而配对是 `|G|⁻¹ ∑`（源码自己的 `ip` 也是归一化的）。归一化之后是 `#{i < n : …}`，没有 `|GL|`。原稿因此还与 6.1（`⟨χₖ, χₖ⟩ = 1`）自相矛盾；用 `q = 3, n = 2, k = l = 1` 手算了一遍：`∑_g |Ψ₁(g)|² = 96 = 2·48`，`∑_g ψ₁(g) conj(Ψ₁(g)) = 48`，与改后的公式一致。README 5.2 的 Checks 同步改了（`l = k, k` 正则：`1`）。
2. **7.3 的假设不足**。原稿对任意函数 `χ, α, β` 陈述 `⟨χ, Ind(α ⊗ β)⟩ = |Lₐ|⁻¹ ∑_m jacquet(χ)(m) * conj (α m.1 * β m.2)`，这是错的：`Subgroup.indClassFun` 对非类函数依赖代表元的选取，求和坍缩那一步要 `χ` 是类函数，`conj` 那一步要 `α, β` 是虚拟特征标。现在 `χ, α, β` 都是类函数，右边写成 `(α m.1 * β m.2)⁻¹`，README 注明对特征标它就是复共轭。7.1 的 API 里"是最后一个变量的类函数"也相应改成"按构造就是类函数"。
3. `Module.AEval'` 在 pin 的 Mathlib 里不存在，改成 `Module.AEval`。
4. README 7.5 的 route 原先说"把双陪集按块的置换分类"却没有任何地方说出这是 Bruhat 分解；现在引 Tau Ceti 的 `exists_mem_doubleCoset_permutationGL`，并说明两个诱导经投射公式都化成从 Borel 子群的诱导。

另记一笔（不是错误）：源码的 cuspidality、HC 诱导、Whittaker 泛函和 7.6–7.10、8.2 都只对素域 `ZMod g` 陈述，路线图对一切有限域陈述；写在 Provenance 里。

### 7.5 编译（第 8 步 b）

在 `tauceti-build/TauCetiRoadmap`（工具链 `leanprover/lean4:v4.36.0-rc2`，TauCeti `2fd255d9`，Mathlib `1b1ccf4b`）里，`source ../../.run/env.sh` 后带 `.run/build-tauceti.sh` 同样的 `LAKE_CONFIG`、`LAKE_CACHE_DIR`，`lake build TauCetiRoadmap.CharactersOfGLnOverFiniteFields.Suggested`：**exit 0，Build completed successfully (18510 jobs)，0 error，36 条警告，全部是 `declaration uses 'sorry'`**（日志 `.run/step8-tauceti/build2.log`）。38 条定理里 36 条 sorry（`mem_parabolic_iff`、`unipotentRadical_le_parabolic` 有真实证明），19 个 `def` 都有真实定义体（打包类函数的 `psiClassFunction`、`leviInflate`、`jacquetRestrict` 三个 def 调用本文件里 sorry 的类函数性定理；`rootPowerSumClassFunction` 的类函数性是当场证的）。第 7 步时的 "consider adding `module`" 警告因为加了 `module` 头而消失；没有其它警告（deprecated 名字 `if_pos`/`if_neg`/`if_true` 在试编译时出现过，已换成 `ite_eq_left`/`ite_eq_right`/`ite_true`）。`python3 .github/scripts/check_roadmap_topics.py`：`Roadmap topics valid (532 roadmaps)`。没有改副本里别的路线图、lakefile、manifest、根 `TauCetiRoadmap.lean`。

### 7.6 查了什么、没查什么

**查了。** 上面每个 Tau Ceti 声明名都在源码里 grep 到定义处（或 `#check` 过）；用到的 Mathlib 名字（`Matrix.BlockTriangular`、`blockTriangular_inv_of_blockTriangular`、`charpoly_units_conj`、`twoBlockTriangular_det`、`powMonoidHom`、`Module.AEval`、`Algebra.IsQuadraticExtension`、`normalizedFactors` 的路径）在 pin 的 Mathlib 里 grep 过；5.2、4.5、4.6、1.4、7.6–7.9 的定量陈述逐条对过源码的 Statement 文件（`EndomorphismMassMobiusInverseMonicEq`、`InvariantSubspaceMobiusInverseOneProdIco`、`FrobeniusTorusCharacterOrthogonality`、`NcardGenericIrreducibleCharactersGLnLe`、`CardCuspidalMultisetsTotalDegreeLe`、`ExistsGenericConstituentHarishChandraCuspidal`、`ExistsCuspidalListHarishChandraPairingNeZero`、`RootPowerSumCharpolyMemVirtualCharactersGL`、`GreenRegularCharacters`），只发现 5.2 的归一化问题；`parabolic`/`unipotentRadical` 的子群结构证明和 `mem_parabolic_iff` 是编译器验证的；`GL2Cuspidal` 的假设形（`θ.comp (powMonoidHom (Fintype.card F)) ≠ θ`）照抄。

**没查。** 3.3 的三个 Checks（`parabolic F 2 1 = TauCeti.GL2Borel F`、`parabolic F n 1 = TauCeti.lineStabilizer F 0`、`parabolic F n (n - 1) = TauCeti.hyperplaneStabilizer F` 末指标）与 2.5 的 Check（`GL2NonSplitTorus.natCard_eq`）是按两边的定义读出来认为相等的，没有在 Lean 里证；`Subgroup.indClassFunction` 对类函数等于原来那个 `|Pₐ|⁻¹ ∑_y` 公式依据的是 `indClassFun_eq_natCard_inv_mul_sum` 的陈述，没有自己重新推导；7.5 里"两个诱导经投射公式化成从 Borel 子群的诱导"与"每个匹配的置换贡献 1"只是口头论证，标量因子如何抵消没有算清（见 §7.7 第 4 条）；`rootPowerSum_orthogonality` 与源码的 `{α | α ^ (qⁿ - 1) = 1}` 版本等价（`ι (Kˣ)` 恰是这些单位根）没有证；README 全文没有重新通读，只看了改过的段落。

### 7.7 第 8 步新增的待人工确认

1. **目录位置**：草稿在 `TauCetiRoadmap/CharactersOfGLnOverFiniteFields/`（顶层路线图，`metadata.toml` = `math.RT`），而相邻的表示论路线图都是 `TauCetiRoadmap/RepresentationTheory/` 这个路线图下的子路线图（子路线图不带 `metadata.toml`）。放哪里由 De Song 定；移动的话要改 README 里的相对链接。
2. **对一切有限域陈述**：7.6–7.10、8.2 在源码里只对 `ZMod g`（`g` 素数）证明。路线图把它们写成任意有限域 `F`，数学上没有疑问（证明不依赖域是素域），但这是对源稿的推广，请确认接受。
3. **3.3、2.5 的 Checks** 没有编译验证（见上"没查"）。
4. **7.5 的 route** 里的标量：`Ind_B^G (Res_B ψ) = [P : B] · Ind_P^G ψ`，两个诱导化到 Borel 子群后 Mackey 公式给出的 `∑_w ⟨φ, φ'^w⟩_B` 与"匹配置换的个数"之间的因子关系我没有算清楚；结论（不同多重集给 `0`、无重复的同一多重集给 `1`）是标准事实，但 route 的叙述可能需要熟悉 Mackey 公式的人改写。
5. **`[DecidableEq F]`**：这是沿用 Tau Ceti 配对定理的习惯，不是数学内容；如果审稿人不喜欢可以去掉（语句换成 `classical` 推出的实例）。
6. **`hcL` 的 junk 值**（次数不加总为 `n` 时返回 `0`）与源码不同，见 Provenance。

