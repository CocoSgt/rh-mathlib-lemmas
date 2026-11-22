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
- GitHub 上的操作只做第 5 步写的这些：自己的仓库、mathlib4 的 fork 和 PR。别人的仓库只读，不 force-push 别人的分支，不在别人的 issue/PR 里评论。审稿人在你的 PR 里提意见，可以回复、照着改
- `lake build` 加 `-j 4` 左右，别把内存吃满（这台机器上还有别的任务在跑 Lean）
- 功劳归 Levent Alpöge 和 Claude；抽出来的每个文件开头写明出处
- 拿不准的数学判断，写进 REPORT.md 的「待人工确认」一节，别硬下结论
