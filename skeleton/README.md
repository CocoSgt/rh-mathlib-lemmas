# skeleton/ — 主线骨架（TASK.md 第 6 步）

黎曼猜想 Lean 证明（Levent Alpöge 与 Claude，2026-11-20 发布，https://alpo.ge/ ；镜像
https://github.com/CocoSgt/riemann-hypothesis-lean ）主线中间结论的"骨架"：每一层的命题写成只依赖
Mathlib 的文件，能证的层间衔接在这里证出来并做公理检查。所有数学与证明属于 Levent Alpöge（与 Claude）；
这里只做了查找、搬运、整理与编译验证（GLM 5.4 通过 DeepSeek Harness）。原发布没有 license 文件
（REPORT.md §5.6）。说明文档：仓库根目录的 `SKELETON.md`。

## 环境

- Lean `leanprover/lean4:v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`（与 `source/` 相同）。
- `lean-toolchain` 在 `~/.elan`（不在工作区 `.elan/`，那里只有 4.37.0-rc1）：`export PATH=$HOME/.elan/bin:$PATH`。
- `.lake/packages` 是指向 `../extracted/.lake/packages` 的符号链接（同一版 Mathlib，缓存已就绪，不重复占 7 GB）。
- 机器 32 GB：一个 `import Mathlib` 的 `lean` 进程约 6 GB，`lake build` 用 `-K jobs=1`（最多 2）。

```bash
cd skeleton
export PATH=$HOME/.elan/bin:$PATH
lake build -K jobs=1 Skeleton              # 整个骨架（Top/Window/Galois/Layers）
lake env lean Axioms.lean > axioms.txt     # 对所有公开定理做 #print axioms（Axioms.lean 由 make_axioms.py 生成）
python3 make_axioms.py                     # 重新生成 Axioms.lean（新增文件后）
```

## 结构

| 模块 | 内容 | 命名空间 |
|---|---|---|
| `src/Skeleton.lean` | 总根（只 import） | — |
| `src/Skeleton/Layers.lean` | 五层 `Layer1…Layer5` 与已证的衔接（入口） | `Skeleton` |
| `src/Skeleton/Top/` | `EveryCharacter`、`ZeroFreeAll`、`Statements` 四条命题；`rh_of_right`、`rh_of_every`、`critLine`、`Claim.strip/zeta`、`riemannHypothesis_of_everyCharacter`、`imprimitive`；`PlugWin`（未证，以不透明命题为参数）；`Main.lean` 五条定理的条件版 | `Skeleton` |
| `src/Skeleton/Window/` | `PChar`/`ZeroFreeAll`/`EveryCharacter`/`imprimitive`（原命名空间）、`VWin` 的完整陈述、`Green` 的完整陈述、`plugAll` 的拼接 | `Formalism.HC`、`UpperTheory`、`GlobalTheory.GLq` |
| `src/Skeleton/Galois/` | 位与 Galois 群、Galois 上同调（`VWin` 的 `VVle` 所需）、`Row0b`/`IsRecT` 的可搬部分与说明、`vwin_of_row`/`everyCharacter_of_row` 的拼接 | `Formalism.ConjugateSelfDual`、`ReciprocityTheory.Gal`、`UpperTheory` |
| `Top/Axioms.lean`、`Axioms.lean`（根） | `#print axioms` 汇总 | — |
