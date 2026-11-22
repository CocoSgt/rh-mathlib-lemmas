# skeleton/ — 主线骨架（TASK.md 第 6 步）

黎曼猜想 Lean 证明（Levent Alpöge 与 Claude，2026-11-20 发布，https://alpo.ge/ ；镜像
https://github.com/CocoSgt/riemann-hypothesis-lean ）主线中间结论的"骨架"：每一层的命题写成只依赖
Mathlib 的文件，能证的层间衔接在这里证出来并做公理检查。所有数学与证明属于 Levent Alpöge（与 Claude）；
这里只做了查找、搬运、整理与编译验证（GLM 5.4 通过 DeepSeek Harness）。原发布没有 license 文件
（REPORT.md §5.6）。说明文档：仓库根目录的 `SKELETON.md`（一页结论、实际路径、依赖锥、可引用清单）。

主线五层（`Main.lean` 实际走的路径，见 `SKELETON.md` §1）：

```
Row0b + RecTExists  ⟹ vwin_of_row ⟹  VWin  ∧  Green  ∧  Nonempty (HypsAlt … DefiniteSideCondition)
   ⟹ zero_free_all_of_green_v_win ⟹  ZeroFreeAll  ⟹ imprimitive ⟹  EveryCharacter  ⟹  RiemannHypothesis
```

骨架里已证（Mathlib-only）：`imprimitive`、`EveryCharacter → RiemannHypothesis`（两条路线）、`critLine`、`Claim.strip/zeta`、`Main.lean` 的条件版；
未证、以假设出现：`zero_free_all_of_green_v_win`（`plugWinStatement`）、`vwin_of_row` 与文献定理（拼接定理的假设）。

## 环境

- Lean `leanprover/lean4:v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（与 `source/` 相同）。
- `lean-toolchain` 在 `~/.elan`（不在工作区 `.elan/`，那里只有 4.37.0-rc1）：`export PATH=$HOME/.elan/bin:$PATH`。
- `.lake/packages` 是指向 `../extracted/.lake/packages` 的符号链接（同一版 Mathlib，缓存已就绪，不重复占 7 GB）。
- 机器 32 GB：一个 `import Mathlib` 的 `lean` 进程约 6 GB，`lake build` 用 `-K jobs=1`，同一时间只跑一个 lean 进程。

```bash
cd skeleton
export PATH=$HOME/.elan/bin:$PATH
lake build -K jobs=1 Skeleton              # 整个骨架：22 个模块，单进程；Mathlib 缓存已就绪时约 2.5 分钟
python3 make_axioms.py                     # 生成 Axioms.lean 与 src/Skeleton/Top/Axioms.lean（新增文件后重跑）
lake env lean Axioms.lean > axioms.txt     # 全库 144 条公开声明的 #print axioms
python3 make_axioms.py --check axioms.txt  # 校验：只有 [propext, Classical.choice, Quot.sound] 的子集，无 sorryAx
lake env lean src/Skeleton/Top/Axioms.lean > src/Skeleton/Top/axioms.txt   # Top/ 的 36 条
```

## 结构

命名规则：从源里搬来的命题与衔接**保留源命名空间与名字**（`Formalism.HC.*`、`UpperTheory.*`、`GlobalTheory.*`、`ReciprocityTheory.*` …），只在骨架里才有的东西（`Statements` 的副本、`Claim.*`、`PlugWin`、条件版 `Main` 定理、`LayerN`）放在 `Skeleton` 命名空间。

| 模块 | 内容 | 命名空间 |
|---|---|---|
| `src/Skeleton.lean` | 总根（只 import） | — |
| `src/Skeleton/PChar.lean` | **共享底座（唯一一份）**：`PChar`、`KSet`、`Level`、`ZeroFreeAll`、`EveryCharacter`，衔接 `imprimitive : ZeroFreeAll → EveryCharacter`，`zeroFreeAll_iff`；只 import 4 个 Mathlib 子模块（单文件 10 s） | `Formalism.HC`、`UpperTheory` |
| `src/Skeleton/Layers.lean` | 五层 `Layer1…Layer5` 与已证的衔接（入口）：`layer4_of_layer3`、`layer5_of_layer4`（两条路线）、`layer5_of_layer3`、`mainOfLayer4`、`layer3_of_layer2`、`layer4_of_layer2`、`layer5_of_layer2`、`mainOfLayer2`、`layer4_of_layer1`、`layer5_of_layer1` | `Skeleton` |
| `src/Skeleton/Top/` | `Statements` 四条命题、`Claim.*`；`rh_of_right`、`rh_of_every`、`riemannHypothesis_of_everyCharacter`、`critLine`、`Claim.strip/zeta`；`PlugWin`（未证的衔接，以不透明命题为参数）；`Main.lean` 五条定理的条件版 | `Skeleton` |
| `src/Skeleton/Window/` | `VWin` 的完整陈述（`VWin.lean`）、`Green` 的完整陈述（`Green.lean`）、衔接的陈述 `plugWinStatement` 与拼接 `plugAll_of_plugWin`（`PlugAll.lean`） | `UpperTheory.Top`、`GlobalTheory.GLq`、`Formalism.CyclotomicNorms` … |
| `src/Skeleton/Galois/` | 位与 Galois 群（`Places.lean`）、Galois 上同调（`GaloisCohomology.lean`，`VWin` 的 `VVle` 所需）、`Row0b`/`IsRecT` 的可搬部分与原陈述注释（`Row0b.lean`、`IsRecT.lean`）、`vwin_of_row`/`everyCharacter_of_row` 的拼接（`Mainline.lean`） | `Formalism.ConjugateSelfDual`、`ReciprocityTheory.Gal`、`Formalism.GaloisCohomology`、`UpperTheory` |
| `Axioms.lean`（根，不属库）、`src/Skeleton/Top/Axioms.lean`、`src/Skeleton/Window/AxiomsLower.lean` | `#print axioms` 脚本（前两个由 `make_axioms.py` 生成）；输出在 `axioms.txt`、`src/Skeleton/Top/axioms.txt` | — |

历史：2026-11-23 之前 `Top/` 与 `Window/PChar.lean` 各有一份 `PChar`/`ZeroFreeAll`/`EveryCharacter`/`imprimitive`，合并后只保留 `PChar.lean` 这一份（对照表见 `SKELETON.md` 附录 D）。
