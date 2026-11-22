# SKELETON-top — 主线骨架 · 上层（`skeleton/src/Skeleton/Top/`）

> **汇总会话注（2026-11-23 02:30，合并后）**：本文件作为附录 A 原样保留，但 `skeleton/` 已经合并：`Top/ZeroFreeAll.lean`、`Top/EveryCharacter.lean`、`Top/Imprimitive.lean` 里与 `Window/PChar.lean` 重复的 `PChar`、`ZeroFreeAll`、`EveryCharacter`、`imprimitive` 只保留一份，在 **`skeleton/src/Skeleton/PChar.lean`**（源命名空间 `Formalism.HC` / `UpperTheory`）；本文 §1 表里的 `Skeleton.PChar`、`Skeleton.ZeroFreeAll`、`Skeleton.EveryCharacter`、`Skeleton.imprimitive`、`Skeleton.everyCharacter_iff` 等名字已不存在，对照见 `SKELETON.md` 附录 D。§3 的"陈述依赖锥"数字（`Green` 118、`VWin` 1,292、`Hyps` 3,844 …）是本文的口径，与其它口径的差异见 `SKELETON.md` §3.1、§3.5。另：`Main.lean` 实际走的是 `TopPlug.lean` 的 `zero_free_all_of_green_v_win`（`HypsAlt … DefiniteSideCondition`），不是本文 §3 写的 `plugWin`（`Hyps … DRS`），两者形状相同、在 `zeroFreeAll_of_topG` 汇合，见 `SKELETON.md` §1.1。

> 功劳与署名：所有数学与 Lean 证明属于 **Levent Alpöge（与 Claude）**（2026-11-20 发布，https://alpo.ge/ ，镜像 https://github.com/CocoSgt/riemann-hypothesis-lean ）。本目录只是把主线顶层的命题与衔接定理原样搬到只依赖 Mathlib 的文件里、补 docstring、编译验证；抽取、整理、编译由 GLM 5.4 通过 DeepSeek Harness 完成。原发布没有 license 文件（见 REPORT.md §5.6）。
>
> 环境：Lean `v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（与 `source/` 相同），`skeleton/` 独立 Lake 项目，`.lake/packages` 指向 `extracted/.lake/packages`（缓存已就绪）。

## 0. 结论（一眼版）

- 主线五层里，**最后两层（`ZeroFreeAll → EveryCharacter → RiemannHypothesis`）以及 `Main.lean` 的五条定理、`Statements.lean` 的四条命题，现在都能在只 import Mathlib 的环境里单独引用**：`skeleton/src/Skeleton/Top/`，13 个模块，47 条公开声明，全部编译通过，`#print axioms` 全部只有 `propext, Classical.choice, Quot.sound`（`Top/axioms.txt`）。
- 这一段的入口是 `Skeleton.EveryCharacter`（= `Statements.lean:6` 的 `DirichletLNonvanishingRightOfHalf`，`Iff.rfl`）。从它出发：
  `Skeleton.rh_of_every` / `Skeleton.riemannHypothesis_of_everyCharacter` → `RiemannHypothesis`；`Skeleton.critLine` → 本原特征的 GRH（`PrimitiveDirichletLZerosOnLine`）；`Skeleton.Claim.strip` → `DirichletLZerosOnLine`；`Skeleton.Claim.zeta` → `RiemannZetaZerosOnLine`。`Skeleton.MainTheorems` 里把它们装成 `Main.lean` 那五条定理的条件版（以 `allChi : EveryCharacter` 为假设）。
- **唯一搬不动的一环是 `plugWin`（`Green + VWin + Hyps 非空 → ZeroFreeAll`）**：它的三个假设和中间命题（`TopG`、`HostExW`、`GChi`、`FamP`、`Hyps`、`DRS`、`TopShape`…）都是本项目自己的深层定义，陈述层面的依赖锥最小 118 条声明 / 49 个文件（`Green`），最大 3,844 条 / 1,103 个文件 / 25 万行（`Hyps`）。所以写成 `Skeleton.PlugWin Green VWin Hyps : Prop := Green → VWin → Hyps → ZeroFreeAll`（三个输入作为不透明命题），而 **`PlugWin → EveryCharacter → RH + 四条命题** 这一整段都在这里证出来了（`Skeleton.everyCharacter_of_plugWin`、`Skeleton.riemannHypothesis_of_plugWin`、`Skeleton.mainOfPlugWin`）。也就是说：主线从 `Green + VWin + Hyps` 到黎曼猜想，只剩 `plugWin` 这一环没有 Mathlib-only 的版本。
- 命名空间：本目录所有声明放在 `Skeleton.*` 下（`Skeleton.EveryCharacter`、`Skeleton.Claim.*`、`Skeleton.PChar`、`Skeleton.ZeroFreeAll` …），名字与原开发一一对应（见 §1 表），docstring 里写了原全名与 `文件:行号`。与 `Skeleton/Window/PChar.lean`（下层会话，用原命名空间 `Formalism.HC.*` / `UpperTheory.*` 搬了同一批 `PChar` / `ZeroFreeAll` / `EveryCharacter` / `imprimitive`）**内容重叠但命名空间不同，不会冲突**；汇总会话二选一即可（见 §5）。

## 1. 文件与定理

"编译"一列：`lake build -K jobs=1 Skeleton.Top.Axioms` 通过（每个模块 11–24 s）；"公理"一列：全部为 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`（`Top/axioms.txt`）。"依赖"指除 Mathlib 外的依赖（都只 import Mathlib 的子模块 + 本目录里更底下的文件）。

| 文件（`Top/`） | 声明（本目录） | 原位置（`source/src/`） | 内容 | 依赖 | 编译 |
|---|---|---|---|---|---|
| `Statements.lean` | `Skeleton.RiemannZetaZerosOnLine` | `Statements.lean:3` | ζ 的非平凡零点在临界线上 | Mathlib (`LSeries.RiemannZeta`, `DirichletContinuation`) | ✓ |
| | `Skeleton.DirichletLNonvanishingRightOfHalf` | `Statements.lean:6` | 所有 Dirichlet L 在 Re s > 1/2 非零（= EveryCharacter） | 同上 | ✓ |
| | `Skeleton.DirichletLZerosOnLine` | `Statements.lean:10` | 所有 Dirichlet L 的带内零点在临界线上 | 同上 | ✓ |
| | `Skeleton.PrimitiveDirichletLZerosOnLine` | `Statements.lean:14` | 本原 Dirichlet L 的 GRH（零点版） | 同上 | ✓ |
| `EveryCharacter.lean` | `Skeleton.EveryCharacter` | `CharacterBoxes/EveryCharacter.lean:13` | 主线倒数第二层的命题 | Mathlib | ✓ |
| | `Skeleton.everyCharacter_iff`（新） | — | `DirichletLNonvanishingRightOfHalf ↔ EveryCharacter := Iff.rfl` | `Statements` | ✓ |
| `HalfPlane.lean` | `Skeleton.Claim.HalfPlane` / `Strip` / `Zeta` | `CharacterBoxes/HalfPlane.lean:3 / :6 / :9` | 三条"claim" | Mathlib | ✓ |
| | `Skeleton.Claim.halfPlane_iff` / `strip_iff` / `zeta_iff_statements`（新） | — | 分别 `Iff.rfl` 于 `EveryCharacter` / `DirichletLZerosOnLine` / `RiemannZetaZerosOnLine` | `Statements`, `EveryCharacter` | ✓ |
| `ZeroFreeAll.lean` | `Skeleton.PChar`（structure） | `TotientGaloisClasses/PrimePairSizeCondition.lean:7` | 本原 Dirichlet 特征 + 其（本原）模数 | Mathlib | ✓ |
| | `Skeleton.PChar.val / one / inv / inv_inv / of / IsReal` | 同上 `:17 :19 :21 :26 :32 :35` | 基本接口 | Mathlib | ✓ |
| | `Skeleton.PChar.ZeroFreeAbove`、`Skeleton.ZeroFreeOn`、`ZeroFreeEven`、`Skeleton.ZeroFreeAll` | `TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:11 :14 :16 :18` | "本原 L 函数在 Re s > 1/2 无零点" | Mathlib | ✓ |
| | `Skeleton.PChar.of_self / of_one / of_inv`（+ 5 条 private 引理） | 同上 `:59 :70 :96`（private `:50 :64 :75 :85 :91`） | `PChar.of` 的 API | Mathlib (`RingTheory.Conductor`) | ✓ |
| | `Skeleton.zeroFreeAll_iff`（新） | — | 不用 `PChar` 的等价陈述：对本原 χ，L(χ,s) ≠ 0 | Mathlib | ✓ |
| `RhOfRight.lean` | `Skeleton.rh_of_right` | `Formalism/GammaFactorNonvanishing/RhOfRight.lean:5` | ζ 在 Re s > 1/2 非零 ⇒ `RiemannHypothesis`（函数方程 + Gamma/cos 非零） | Mathlib (`RiemannZeta`, `Nonvanishing`) | ✓ |
| `CritLine.lean` | `Skeleton.gammaFactor_ne_zero` | `…/CritLine.lean:6` | `gammaFactor χ s ≠ 0`（Re s > 0） | Mathlib, `EveryCharacter`, `RhOfRight`（同文件 import） | ✓ |
| | `Skeleton.critLine` | `…/CritLine.lean:11` | EveryCharacter ⇒ 本原 L 的带内零点在 Re s = 1/2 | Mathlib, `EveryCharacter` | ✓ |
| | `Skeleton.rh_of_every` | `…/CritLine.lean:29` | **EveryCharacter ⇒ `RiemannHypothesis`**（取模 1 的特征，L = ζ，用 `rh_of_right`） | Mathlib, `RhOfRight` | ✓ |
| `ClaimStrip.lean` | `Skeleton.Claim.factor_ne_zero` | `CharacterBoxes/ClaimStrip.lean:7` | Euler 因子 `1 − ψ(p) p^{-s} ≠ 0` | Mathlib | ✓ |
| | `Skeleton.Claim.prim_zero` | `:23` | L(χ,s) = 0 ⇒ 本原模型也为零 | Mathlib | ✓ |
| | `Skeleton.Claim.gamma_ne_zero` | `:35` | `gammaFactor ≠ 0` | Mathlib | ✓ |
| | `Skeleton.Claim.prim_reflect` | `:42` | 本原 L 在 s 为零 ⇒ 逆特征在 1 − s 为零（函数方程） | Mathlib | ✓ |
| | `Skeleton.Claim.strip` | `:59` | **HalfPlane ⇒ Strip** | Mathlib, `HalfPlane` | ✓ |
| | `Skeleton.Claim.zeta` | `:75` | **HalfPlane ⇒ Zeta**（`riemannZeta` 版） | Mathlib, `HalfPlane` | ✓ |
| | `Skeleton.Claim.zeta_iff` | `:102` | `Zeta ↔ RiemannHypothesis := Iff.rfl` | 同上 | ✓ |
| `RiemannHypothesisOfEveryCharacter.lean` | `Skeleton.zeta_ne_zero_of_everyCharacter` | `CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:211` | EveryCharacter ⇒ ζ 在 Re s > 1/2 非零 | Mathlib, `EveryCharacter` | ✓ |
| | `Skeleton.riemannHypothesis_of_everyCharacter` | `:215` | **EveryCharacter ⇒ `RiemannHypothesis`**（第二条路线：直接用 `completedRiemannZeta_one_sub`；原文件 209 行内部 import 全部不需要） | 同上 | ✓ |
| `Imprimitive.lean` | `Skeleton.imprimitive` | `CharacterBoxes/Imprimitive.lean:5` | **ZeroFreeAll ⇒ EveryCharacter**（`LFunction_changeLevel` + Euler 因子非零） | Mathlib, `EveryCharacter`, `ZeroFreeAll` | ✓ |
| `PlugWin.lean` | `Skeleton.PlugWin`（def） | `CharacterBoxes/EveryCharacter.lean:8`（陈述） | `PlugWin Green VWin Hyps := Green → VWin → Hyps → ZeroFreeAll`，三个输入不透明（**未证明**，见 §3） | `Imprimitive`（仅为下一行） | ✓（命题） |
| | `Skeleton.everyCharacter_of_plugWin` | `CharacterBoxes/EveryCharacter.lean:16`（`plugAll`） | **PlugWin Green VWin Hyps ⇒ Green → VWin → Hyps → EveryCharacter** | Mathlib, `Imprimitive` | ✓ |
| `MainTheorems.lean` | `Skeleton.rhOfAll`、`critAll`、`claimAll` | `Supplements/Kernels/MainTheorems.lean:9 :11 :15` | 原来把已证的 `allChi` 代入；这里以 `allChi : EveryCharacter` 为假设 | 上面各文件 | ✓ |
| | `Skeleton.riemannHypothesis`、`riemannZeta_eq_zero_re`、`LFunction_ne_zero_of_half_lt_re`、`LFunction_eq_zero_re`、`LFunction_eq_zero_re_of_isPrimitive` | `Main.lean:4 :6 :8 :10 :12` | `Main.lean` 的五条定理，条件版（假设 `allChi`） | 同上 | ✓ |
| | `Skeleton.riemannHypothesis_of_plugWin`（新） | — | `PlugWin Green VWin Hyps → Green → VWin → Hyps → RiemannHypothesis`（plugWin 以下的整条链） | 同上, `PlugWin` | ✓ |
| | `Skeleton.mainOfPlugWin`（新） | — | 同上，一次给出 `Statements` 四条 + RH | 同上 | ✓ |
| `Top.lean`（在 `Skeleton/` 下，本目录的根） | — | — | 只做 import 汇总 | 全部 | ✓ |
| `Axioms.lean` / `axioms.txt` | — | — | 对 47 条声明逐条 `#print axioms`；不被任何文件 import | `Skeleton.Top` | ✓ |

没有搬进来的原文件内容：`ExplicitFormulaErrorOfHostConditions.lean` 里 `Level`、`KSet`、`HType`、`Frame`、`EAtH` 等（主线顶层任何陈述都不需要；`Level.*` 的那部分下层会话放在 `Skeleton/Window/PChar.lean`）。

## 2. 主线衔接链（本目录覆盖的部分）

```mermaid
flowchart LR
  G["Green"] --> PW
  V["VWin"] --> PW
  H["Hyps 非空"] --> PW
  PW["plugWin<br/>EveryCharacter.lean:8<br/>【未复现：Skeleton.PlugWin，以 G/V/H 为不透明假设】"] -->|✓ 命题| ZFA["ZeroFreeAll<br/>Skeleton.ZeroFreeAll"]
  ZFA -->|✓ imprimitive| EC["EveryCharacter<br/>Skeleton.EveryCharacter"]
  EC -->|✓ rh_of_every| RH["RiemannHypothesis"]
  EC -->|✓ riemannHypothesis_of_everyCharacter| RH
  EC -->|✓ critLine| GRH["PrimitiveDirichletLZerosOnLine"]
  EC -->|✓ Claim.strip| ST["DirichletLZerosOnLine"]
  EC -->|✓ Claim.zeta| ZS["RiemannZetaZerosOnLine"]
  EC -. Iff.rfl .- DNP["DirichletLNonvanishingRightOfHalf"]
  RH -. Iff.rfl .- ZS
```

打 ✓ 的边都在本目录编译通过、公理核对；虚线是 `Iff.rfl`。唯一实线未证的是 `plugWin`。

## 3. `plugWin` 这一环卡在哪

原证明（`CharacterBoxes/EveryCharacter.lean:8–11`，只有 3 行）：

```
plugWin hG hV h := zeroFreeAll_of_topG (la := 3/2) (by norm_num)
  (GlobalTheory.Fc.shape_of _ _ _ _ (UpperTheory.Top.shapeWin hG) trivial trivial h)
  fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ)
```

拆开是四块，每块的**陈述**就依赖大量项目内定义（下表；数字是对陈述做静态名字解析后得到的"陈述依赖锥"——只追定义的陈述、不追证明体，用 Lean 的命名空间/`open` 规则解析标识符，方法见附录）：

| 原声明 | 文件:行号 | 陈述依赖锥：内部声明数 | 文件数 | 这些文件的总行数 | 最深链 | 内容 |
|---|---|---:|---:|---:|---:|---|
| `UpperTheory.Top.plugWin` | `CharacterBoxes/EveryCharacter.lean:8` | 3,881 | 1,103 | 255,448 | 14 | 定理本身 |
| `GlobalTheory.GLq.Green` | `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108` | 118 | 49 | 10,629 | 11 | GL_n(𝔽_g) 的 Green 特征存在唯一（`LabelDatum`、`Fbar`、`IsCuspOf`…） |
| `UpperTheory.Top.VWin` | `CharacterBoxes/ExistsPageN.lean:49` | 1,292 | 477 | 113,109 | 34 | 自守窗口（`VWinAt → WinPair/PageN/VAt → IsChiField/VVle → shaLen/LData…`） |
| `GlobalTheory.Fc.Hyps`（structure，`Type 1`） | `Definitions/GlobalTwisting/APerTw.lean:23` | 3,844 | 1,103 | 254,143 | 13 | 75 个字段的解析假设包（`RawSel`、`Duty`、`TuSize`、`ServT`…） |
| `GlobalTheory.Fc.DRS` | `Definitions/GlobalTwisting/DRS.lean:21` | 3,219 | 982 | 220,639 | 15 | `R1.DefT` 型的"divisibility"条件 |
| `Formalism.MainNotions.Closed` | `Formalism/SharpRestriction/ParamsHeightRankConstant.lean:159` | 1,569 | 549 | 128,229 | 16 | `Closed 𝒞 P`（族上的一致成立） |
| `Formalism.MainNotions.LinkN` | `Formalism/SharpRestriction/GlobalTheoremInputs.lean:45` | 1,559 | 545 | 127,264 | 16 | LinkN 条件 |
| `UpperTheory.Top.TopG` | `CharacterBoxes/ZeroFreeAllOfTopG.lean:12` | 1,703 | 590 | 137,093 | 16 | `∀ la G, 1 < la → HostExW la G.req → … → FamilyClassConnected (G.cls la)` |
| `UpperTheory.Top.zeroFreeAll_of_topG` | 同上 `:26` | 1,715 | 594 | 137,869 | 17 | `TopG + (∀ ψ, HostExW la (GChi ψ).req) → ZeroFreeAll`（证明用 `zeroFreeOn_of_tiedWin_cyc`：1,357 条 / 500 文件） |
| `UpperTheory.Top.shapeWin` | `CharacterBoxes/ShapeWin.lean:27` | — | — | — | — | `Green → TopShape True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) TopG`（陈述同 `TopShape`：3,894 条 / 1,119 文件） |
| `GlobalTheory.Fc.shape_of` | `Proofs/GlobalInterpolation/ShapeOf.lean:14` | 3,920 | 1,125 | 260,640 | 14 | `TopShape V NR N G → V → NR → N (D3 3 𝒜) → G` |
| `UpperTheory.Top.supplyChi` | `CharacterBoxes/SupplyChi.lean:8` | 1,372 | 492 | 115,971 | 19 | `∀ ψ, VWinAt ψ 401 → HostExW (3/2) (GChi ψ).req` |
| `UpperTheory.Top.FReq`、`GChi` | `CharacterBoxes/Supply.lean:10 :42` | 1,281 / 1,283 | 472 / 473 | 112,324 / 112,456 | 17 / 18 | `FReq := ∀ Scale Frame HostAx …, Prop`，`GChi ψ := fun s _ H TT t => EAtH (Level.cyc ψ) … ∧ VVle …` |
| `GlobalTheory.EX.HostExW` | `Definitions/GlobalTwisting/ThinScalesIffHostBound.lean:120` | 1,357 | 484 | 115,076 | 18 | host 的存在性条件 |

结论：

1. 这一环**不是**"几条定义搬过来就能证"的情形。最小的 `Green`（118 条 / 49 文件）下层会话已经搬进 `Skeleton/Window/Green.lean`；`VWin` 也在 `Skeleton/Window/VWin.lean`（需要 `Skeleton/Galois/GaloisCohomology.lean` 里的 `shaLen`/`LData`）。但 `Hyps`（3,844 条 / 1,103 文件，`Type 1` 结构）、`DRS`、`TopG`、`TopShape`、`HostExW`、`FamP/FamCore` 都在 Formalism/Development 的解析核心里，陈述就带着 `D7`（1,279 条 / 471 文件）、`FamP`（1,554 条 / 544 文件）这样的东西，没法在只 import Mathlib 的文件里写出来。
2. 所以 `plugWin` 在 `Top/PlugWin.lean` 里写成 `Skeleton.PlugWin (Green VWin Hyps : Prop) : Prop := Green → VWin → Hyps → ZeroFreeAll`。有了原开发，一行 `fun hG hV h => UpperTheory.Top.plugWin hG hV h` 就能证明它（三个参数恰好一一对应）。待下层把 `Green`/`VWin`/`Hyps` 的命题定下来之后，实例化 `Skeleton.PlugWin Skeleton.Window.Green Skeleton.Window.VWin (Nonempty Hyps)` 即可。
3. 原证明里**唯一能单独拎出来、只用 Mathlib 的部分**（`imprimitive`）已经证了；`plugAll`（`EveryCharacter.lean:16`）就是 `imprimitive ∘ plugWin`，这里相应地是 `everyCharacter_of_plugWin`。

## 4. 编译与公理检查

```bash
cd skeleton
lake build -K jobs=1 Skeleton.Top.Axioms      # 13 个模块，单进程，每个 11–24 s（Mathlib 缓存已就绪）
lake env lean src/Skeleton/Top/Axioms.lean    # 47 条 #print axioms，输出见 src/Skeleton/Top/axioms.txt
```

- 47 条声明全部 `'…' depends on axioms: [propext, Classical.choice, Quot.sound]`，没有 `sorryAx`，没有其它公理。
- 每个文件只 import 需要的 Mathlib 子模块（`Mathlib.NumberTheory.LSeries.{RiemannZeta,DirichletContinuation,Nonvanishing}`、`Mathlib.RingTheory.Conductor`），按 Mathlib 的 `linter.minImports` 收窄。注意：`import Mathlib` 整库在这台机器当前负载下单文件要 3.5–18 分钟（内存紧、页缓存放不下 6.5 GB 的 olean），收窄后 11–24 s。
- 原文件里 `haveI : NeZero …` 的写法保留（`linter.style.haveILetI` 会给一个 warning，但那里确实需要注册实例）。
- 证明体全部照抄原文（只改命名空间、`Skeleton.EveryCharacter` 等替换），没有改动数学内容。新加的只有 `*_iff`（`Iff.rfl`）、`zeroFreeAll_iff`、`PlugWin`、`everyCharacter_of_plugWin`、`riemannHypothesis_of_plugWin`、`mainOfPlugWin`。

## 5. 给汇总会话的说明

1. **与 `Skeleton/Window/PChar.lean` 的重叠**：下层会话用原命名空间搬了 `Formalism.HC.PChar`/`ZeroFreeAll`/`Level`、`UpperTheory.EveryCharacter`、`UpperTheory.Top.imprimitive`；本目录用 `Skeleton.*` 搬了其中 `PChar`、`ZeroFree*`、`EveryCharacter`、`imprimitive`。两套命名空间不同，可以同时 import；若要合并，建议保留一套定义，另一边改成 `abbrev`/别名（例如 `abbrev Skeleton.EveryCharacter := UpperTheory.EveryCharacter` 之类，需要 `Iff.rfl` 的那几条相应改写）。我没有 import `Skeleton.Window.*`，以保证本目录不随下层文件的改动而变化。
2. `Skeleton/Top.lean`（模块根，在 `Skeleton/` 目录下）是本部分的汇总 import；`Skeleton.lean` 总根留给汇总会话。
3. `Skeleton/Top/Axioms.lean` 在 lib 的 glob（`Skeleton.+`）之内，`lake build` 会编译它并把 47 行 `#print axioms` 作为 info 打出来；不想看的话从目标里去掉即可，它不被任何文件 import。
4. 这几条 glue 本身就是 Mathlib 候选（REPORT.md §2 #49–52）。如果以后往 Mathlib 提，建议名字：`riemannHypothesis_of_zeta_ne_zero_right`（`rh_of_right`）、`riemannHypothesis_of_dirichletLFunction_ne_zero`（`rh_of_every`）、`DirichletCharacter.IsPrimitive.re_eq_half_of_LFunction_eq_zero`（`critLine`）、`DirichletCharacter.LFunction_ne_zero_of_primitive`（`imprimitive`）；`Statements` 的四个 `def` 不必进 Mathlib（它们是本项目的目标命题）。

## 附录：陈述依赖锥的算法

脚本 `top_closure2.py`（临时放在 `/tmp/sk-top/`，没有进仓库；如需保留请移到 `analysis/`）。输入 `analysis/decls.jsonl`（声明 → 文件、行号）和 `analysis/imports.jsonl`（文件行数）：

1. 取声明的**陈述文本**：theorem/lemma/instance 截到证明体之前的 `:=`；`def … : Prop := …` 与 `abbrev … := …` 取整个右端（它们的"陈述"就是右端）；structure/class 取整块。
2. 按 Lean 的规则解析文本里的每个标识符：先当全名；再依次试当前命名空间栈的各前缀（长的优先）；再试该行生效的 `open`（最近的优先；`open … in` 只作用于下一条声明）；最后允许唯一的"点分后缀"匹配。只在 `decls.jsonl` 里有同名声明时才算项目内引用。
3. 对命中的声明递归（不进证明体），BFS 层数就是"最深链"；文件数、行数按 `imports.jsonl` 统计。

这是近似（会把同命名空间里的短名偶然匹配上、`open` 的解析是近似的），但数量级可信：`Green` 118 / `VWin` 1,292 / `TopG` 1,703 / `Hyps` 3,844 条声明，分别对应 49 / 477 / 590 / 1,103 个文件。
