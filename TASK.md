# 任务：把黎曼猜想证明拆成可复用的引理，为并入 Mathlib 做第一步

## 背景

2026-11-20，Levent Alpöge（和 Claude 合作）发布了一份黎曼猜想及 Dirichlet L 函数 GRH 的 Lean 证明：175,187 个 `.lean` 文件，约 1740 万行，只依赖 Mathlib。11-21 Lean FRO 和 Mathlib Initiative 发了联合声明，确认证明正确：只用到 propext、Classical.choice、Quot.sound 三条标准公理，几套独立内核都接受。

问题在于它是一个整块。后人想引用其中某条中间结果，只能 import 整个 1740 万行的库。要让这份工作能被别人接着用，得把里面通用的数学结果拆出来，按 Mathlib 的标准整理好，最终逐条并入 Mathlib。

这次只做第一阶段：摸清结构、挑出候选、做几条试点，交一份能指导后续工作的报告。

## 材料

- `source/`：证明的完整副本（原样镜像，lean-toolchain `leanprover/lean4:v4.33.1`，Mathlib 固定在 `0df444a360eaa60ab8c11dca51a86af692955474`）。先读 `source/README.md`，再读 `source/src/Main.lean`、`source/src/Statements.lean`、`source/src/Supplements/Kernels/MainTheorems.lean`
- 这台机器已经装好 elan 和 `leanprover--lean4---v4.33.1`
- 机器只有 32 GB 内存、10 核、硬盘剩余约 88 GB。**整库编译要约 100 GB 内存，不要尝试编译整个 source/**。只编译你抽出来的小文件

## 要做的事

1. **画结构图**：`source/src/` 下各个库（Development、Formalism、GroundTheory、ReciprocityTheory、CompanionTheory、PositivityTheory、Lemmata……）各自讲什么数学、互相怎么 import、规模多大。从 Main.lean 往下追主线：最后那几条定理依赖哪几层
2. **挑候选引理**：找出满足这几条的定理或引理
   - 命题只用到 Mathlib 里已有的概念（不依赖本项目自定义的结构）
   - Mathlib 在这个固定版本里还没有（去 Mathlib 源码里搜同名、同义的结果核实；有现成的就记下对应名字）
   - 依赖锥小：证明它需要的本项目内部引理不多
   - 对数论、复分析、调和分析之外的人也有用的优先
   列一张表：名字、文件:行号、命题一句话说明、依赖多少个内部声明、Mathlib 里有没有、为什么值得并入、预计难度
3. **做试点**：从表里挑 5–10 条最合适的，抽到 `extracted/` 下的一个独立 Lake 项目里（依赖同一版 Mathlib，用 `lake exe cache get` 拉缓存）
   - 按 Mathlib 风格整理：命名规范、加 docstring、去掉 `maxHeartbeats` 之类的临时设置、证明尽量缩短
   - 每条都要编译通过，并用 `#print axioms` 确认只依赖三条标准公理
   - 原证明里对应的位置在注释里写清楚（文件:行号）
4. **写后续计划**：按什么顺序拆、哪些块可以整体并入、哪些要先往 Mathlib 补基础定义、大致工作量
5. **提交到 GitHub**（你自己完成，用本机已登录的 `gh`，账号 CocoSgt）
   - 建公开仓库 `CocoSgt/rh-mathlib-lemmas`，推上 REPORT.md、NEXT.md、PROGRESS.md、extracted/（不推 source/ 副本，README 里链接原镜像 https://github.com/CocoSgt/riemann-hypothesis-lean）
   - fork `leanprover-community/mathlib4` 到 CocoSgt，从**最新的 master** 拉分支。试点钉的是旧版 Mathlib，提交前要移植到最新版，在 fork 里编译通过（只编译改动的文件和依赖它的少数文件，用 `lake exe cache get` 拉缓存，`-j 4`），并跑 Mathlib 的风格检查
   - 给 mathlib4 开 PR：一个 PR 只放一两条相关引理，放进 Mathlib 现有目录里该在的文件，不新建「黎曼猜想」目录。第一批最多 3 个 PR，挑最干净、最通用的
   - 每个 PR 的说明写清：内容来自 Levent Alpöge 2026-11-20 发布的黎曼猜想 Lean 形式化（附原文件:行号和镜像链接），由 GLM 5.4 通过 DeepSeek Harness 抽取、整理、提交；提交信息里加 `Co-authored-by: Levent Alpöge`（拿不到他的邮箱就只在说明里写）
   - 开完 PR 等 CI：失败就修，修到通过或确认是 Mathlib 那边的问题为止。PR 链接和 CI 结果记进 PROGRESS.md 和 REPORT.md

6. **主线骨架**（第一批 PR 开完、CI 跑完之后做）。这才是本项目的主要目标：让后人能单独引用证明主线上的中间结论，不用 import 整份证明。只有 32 GB 内存、硬盘约 60 GB，不整库编译，按下面的办法做：
   - **每层的命题单独成文件**：主线五层（Row0b Galois 表示 → VWin 自守窗口 + Green + Hyps → ZeroFreeAll → EveryCharacter → RiemannHypothesis），每层的结论写成一个只 import Mathlib 的命题文件（`def LayerN : Prop := …`，用到的本项目定义一并搬过来，搬不动的记下原因）。放在新目录 `skeleton/`，独立 Lake 项目，同一版 Mathlib
   - **层与层之间的推出关系单独证明**：`LayerN → LayerN+1` 这类衔接定理，凡是能在只 import Mathlib + 命题文件的环境下证出来的（上一轮已实测 `rh_of_right`、`RiemannHypothesisOfEveryCharacter`、`CritLine` 可以），都放进 `skeleton/` 编译通过、`#print axioms` 核对。结果是一条"只要第 1 层成立，就推出黎曼猜想"的链，每一环都能单独引用
   - **静态依赖图**：不编译，从源码文本解析每条主线定理的证明里引用了哪些声明（上一轮的 `analysis/decls.jsonl` 可复用），算出每层结论的近似依赖锥（文件数、行数），找出依赖锥最小的那几层和最大的瓶颈。输出 `analysis/mainline_graph.*` 和一张主线依赖图（Mermaid 写进 `SKELETON.md`）
   - **挑一层真抽出来**：选依赖锥最小、最低的一层，把它的证明连同依赖锥抽进 `skeleton/` 编译通过（一次编译一个文件，单进程约 6 GB，最多两个并行）。抽不动就在 SKELETON.md 写清卡在哪、要多少文件
   - 交付 `SKELETON.md`（主线每层说明、依赖锥大小、哪些已能单独引用、哪些还不能及原因）；`skeleton/` 推到 `CocoSgt/rh-mathlib-lemmas`。这一步不往 Mathlib 开 PR

7. **起草一份 Tau Ceti 路线图**（只起草，不在 Tau Ceti 的任何仓库开 PR、issue、评论、intention 或 claim）
   - 背景：Mathlib 审稿人 vihdzp 在 #46341 建议，用 LLM 拆出来的引理更适合先落到 Tau Ceti。Tau Ceti 是 Lean FRO 和 Mathlib Initiative 孵化的 AI 数学库：人写路线图，AI 写代码，AI 按 rubric 对抗式审稿。新数学必须挂在某份路线图的目标上，路线图是人负责的（可以用 AI 起草，要在 PR 说明里写明用了哪个模型），所以这一步你起草，De Song 审改后由他本人提交
   - 已查到：三个 Mathlib PR 的内容 Tau Ceti 已经有了（`TauCeti/Analysis/Matrix/MinkowskiDeterminant.lean`、`TauCeti/Analysis/Matrix/PosSemidef/Determinant.lean`、`TauCeti/Analysis/Calculus/Deriv/Matrix.lean`、`TauCeti/LinearAlgebra/Matrix/Compound.lean`），边缘引理不用再搬。路线图要做的是证明主线
   - 参考材料在 `tauceti-ref/`（三个仓库的浅克隆，只读）。动笔前读完：`TauCeti/README.md`（尤其 Collaboration 一节：前沿成果和基础材料怎么分）、`TauCeti/AGENTS.md`、`TauCeti/COORDINATION.md`；`TauCetiRoadmap/README.md` 的 Writing a roadmap、Working with Mathlib、Porting existing work、Laying out the README、Prototyping、Filing a roadmap 各节，`TauCetiRoadmap/CONTRIBUTING.md`、`TauCetiRoadmap/AGENTS.md`；`TauCetiReview/rubrics/` 下的 attribution、scope、correctness。再读相邻的已有路线图：`ZerosOfLFunctions`、`LFunctions`、`QuasiRiemannHypothesis`、`AnalyticNumberTheoryPart{I,II,III}`，以及和第 1、2 层相关的（Galois 表示、局部 Langlands、自守形式、theta 对应一类，用 `ls tauceti-ref/TauCetiRoadmap/TauCetiRoadmap` 找）
   - **a. 调研**（写 `ROADMAP-SURVEY.md`）：用普通数学语言说清主线每一层是什么数学（Row0b、RecTExists、VWin、Green、`HypsAlt … DefiniteSideCondition`、ZeroFreeAll……），证明的整体策略是什么、哪一步是新的；每一层里哪些是教科书级的基础材料、哪些是这份证明独有的新路线；哪些 Tau Ceti 已有的路线图或库文件已经覆盖了（写清是哪个文件、哪个目标），哪些 Mathlib 已有
   - **b. 选范围**：定一份路线图的范围，理由写进 SURVEY。标准照 Tau Ceti 的规矩：最低一层能落到 Mathlib 或 Tau Ceti 已有的材料上（No gaps）；和已有路线图不重叠，要用的就写成 supplier 依赖；Build the library；范围明确，不写 optional/deferred/later；可复用。整条主线太大时，可以写成一组路线图里的第一份，其余用一节明确标成 roadmap-for-a-roadmap
   - **c. 起草**：放在 `roadmap/<AreaName>/`，英文，格式完全照 Laying out the README：`# Roadmap: …` 标题、`**Summary.**` 开头的概述、`## Conventions`、按搭建顺序的 `## Layer k: …`、`## Scope and ownership`、`## Exact supplier contracts`（每个 supplier 一个 `### From …`）、`## References`；Alpöge 证明的逐文件对照放在明显次要的 provenance 一节。另加 `metadata.toml`（arXiv 主类）和 `Suggested.lean`（开头写标准说明，诚实用 `sorry`，只 import Mathlib；必须 import Tau Ceti 模块的接口就写在 markdown 里，不编译）。用的定义名先去 `mathlib4/` 和 `tauceti-ref/TauCeti/` 里查有没有现成的，有就用 Mathlib 的叫法。路线图写的是数学本身，不照抄原代码的结构和命名
   - **d. 编译 `Suggested.lean`**：用 `mathlib4/` 这份 master 克隆（Lean v4.37.0-rc1，和 Tau Ceti 现在的工具链一致）：`source .run/env.sh && cd mathlib4 && lake env lean <文件的绝对路径>`，只允许出现 `declaration uses 'sorry'` 警告。（11-23 起硬盘已扩容，这条限制由第 8 步取代）
   - **e. 自审**（写 `ROADMAP-REVIEW.md`）：按 CONTRIBUTING.md 里审路线图的四个方面（包含什么、怎么做、Tau Ceti 格式、逐条细查）各审一遍，再对照 Writing a roadmap 的清单逐条核对；每条写清查了什么、没查什么。数学判断拿不准的列进「待人工确认」
   - **f. 给 De Song 的草稿**（写 `ROADMAP-PR.md`，三段，都是草稿，由他本人改写后发）：① 路线图 PR 的说明（含 AI 使用说明：GLM 5.4 通过 DeepSeek Harness 做了哪些事）；② 一条 Zulip 帖子，在 Tau Ceti 频道说明想把 Alpöge 证明的主线整理成路线图、原发布没有许可证、想先和作者及社区商量；③ 一封给 Levent Alpöge 的英文短信，请他同意把他的工作作为路线图的引用来源、并问许可证
   - 完成后在 PROGRESS.md 记一行，`git commit` 到本仓库，**先不 push**，等 De Song 审过再说

8. **路线图按 Tau Ceti 自己的环境改一轮**（仍然只在本地改，不 push，Tau Ceti 上什么都不发）
   - 背景：硬盘已扩到约 240 GB，第 7 步 d 里“只 import Mathlib、不 lake build TauCetiRoadmap”的限制取消。`tauceti-build/TauCetiRoadmap/` 是 TauCetiRoadmap 的本地副本，已按它 CI 的方式拉好缓存（工具链 v4.36.0-rc2，TauCeti 2fd255d9，Mathlib 1b1ccf4b），我们的草稿已复制在 `TauCetiRoadmap/CharactersOfGLnOverFiniteFields/`，现状 `lake build` 通过、31 条 sorry 警告。TauCeti 源码在 `tauceti-build/TauCetiRoadmap/.lake/packages/TauCeti/`
   - **a. `Suggested.lean` 改用 Tau Ceti 的声明**：TauCetiRoadmap 的 lakefile 要求目标签名直接用 Tau Ceti 已有的声明，不要用 Mathlib 重新写一遍。相邻路线图都是 `module` 开头、`import Mathlib` 再 `import TauCeti.…`。先读 `TauCeti/RepresentationTheory/CharacterTable/`（ClassFunction、Pairing、VirtualCharacter、Table、GL2/…）和相关的 Chevalley/有限群文件，凡是我们自己写的类函数、配对、不可约特征标、GL₂ 尖特征标等，Tau Ceti 有现成的就换成它的，名字逐个在源码里 grep 核实；确实没有的才在本文件定义，并在 README 的 Scope and ownership 里写成 Owned。README 的 `Exact supplier contracts` 里 `### From Tau Ceti` 一节同步改成真实的声明名和文件路径
   - **b. 编译**：在 `tauceti-build/TauCetiRoadmap` 里用 `source ../../.run/env.sh` 后，带上 `.run/build-tauceti.sh` 里同样的 `LAKE_CONFIG`、`LAKE_CACHE_DIR`，跑 `lake build TauCetiRoadmap.CharactersOfGLnOverFiniteFields.Suggested`，只允许 `declaration uses 'sorry'` 警告。再跑 `python3 .github/scripts/check_roadmap_topics.py`。不要改这个副本里别的路线图，不要改 lakefile、manifest、根文件 `TauCetiRoadmap.lean`
   - **c. 同步回本仓库**：改好的三个文件复制回 `roadmap/CharactersOfGLnOverFiniteFields/`
   - **d. 改 `ROADMAP-PR.md`**：① 里的编译说明改成实际编译环境（TauCetiRoadmap 当前 manifest：Lean v4.36.0-rc2、TauCeti 2fd255d9、Mathlib 1b1ccf4b）。③ 给 Alpöge 的信：删掉“Nothing of your code has been redistributed so far”，如实写现状：GitHub 上 `CocoSgt/riemann-hypothesis-lean` 有一份他发布的原样镜像，`CocoSgt/rh-mathlib-lemmas` 里有从中抽出的代码（`extracted/`，13 个文件）和 `skeleton/` 里照录的命题，三个 Mathlib PR 用了其中的矩阵引理；问他是否同意、要不要撤下或加许可。删掉“I'm De Song, a mathematician working with AI tools on formalization”和“a small group of us”，自我介绍处留 `[De Song：一句自我介绍]` 占位。②（Zulip）里有同类说法的也照此改
   - **e. 自审补一节**：`ROADMAP-REVIEW.md` 加一节“第 8 步改了什么”，列出换掉的自定义声明 → Tau Ceti 声明对照表，以及仍然自己定义的部分和原因
   - 完成后在 PROGRESS.md 记一行，把这一步的改动和之前没提交的 `ROADMAP-SURVEY.md`、`.gitignore` 一起 `git commit`，**先不 push**。`tauceti-build/` 已在 .gitignore 里，不提交

## 交付

- `REPORT.md`：结构图、候选表（至少 30 条）、试点结果、遇到的问题
- `extracted/`：能 `lake build` 通过的试点项目
- `NEXT.md`：后续阶段计划
- `PROGRESS.md`：边做边记，每完成一步写一行（时间、做了什么、下一步），中途断了也能接着做
- GitHub：`CocoSgt/rh-mathlib-lemmas` 仓库，和第一批 mathlib4 PR（链接写进 REPORT.md）

## 规矩

- `STORY.md` 不是给你的，不读不改不提交
- `source/` 只读，任何改动都放在 `extracted/` 或别的新目录里
- 提交身份统一用 `Beyond the AGI Bar <beyond@agi.bar>`（两个仓库的本地 git config 已设好，别改回去，也别用 --author 覆盖）。rh-mathlib-lemmas 的第一个提交已改写为 e007519，PROGRESS.md 里的 f00ddab 指的就是它
- GitHub 上的操作只做第 5 步写的这些：自己的仓库、mathlib4 的 fork 和 PR。别人的仓库只读，不 force-push 别人的分支，不在别人的 issue/PR 里评论。审稿人在 PR 里提意见，可以照着改代码、推提交；**但不许在 GitHub 上发任何评论或回复**（Mathlib 规定 GitHub/Zulip 上的交流必须是人自己写的，不许用 LLM），回复的草稿写进 REPORT.md 交给 De Song 本人改写后发
- Tau Ceti 的仓库（TauCeti、TauCetiRoadmap、TauCetiReview 等）只读：不开 PR、issue，不评论，不登记 intention，不 claim，不跑 `tauceti` worker
- `lake build` 加 `-j 4` 左右，别把内存吃满（这台机器上还有别的任务在跑 Lean）
- 功劳归 Levent Alpöge 和 Claude；抽出来的每个文件开头写明出处
- 拿不准的数学判断，写进 REPORT.md 的「待人工确认」一节，别硬下结论
