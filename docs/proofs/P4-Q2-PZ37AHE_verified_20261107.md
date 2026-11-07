# P4-Q2-PZ37AHE 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。元Wilson作用・centered physical source・元kernel・floor・Haar法則・AGP/AGUの既存Type値証拠・Lean/mathlib pin・公開rootは不変更。旧正式証明記録は上書きしない。

## Exact-source CI・Git tree・独立receipt

| 項目 | 確定 |
| --- | --- |
| [AHE定理PR #6430](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6430) | **MERGED** |
| exact-source HEAD | `90bbea93dad9aafa640ec5651833658f50a35fb1` |
| test-merge SHA | `6b737f013e5c093339fb6ca1eb8f09cb23ed2857` |
| squash SHA | `048d6b38a577201bb231147c6c4981789c4da5e8` |
| source/test-merge/squash 共通 Git tree | `0c978fd763c57fe7c91d9a995732a3d1ee43732b` |
| [Exact-source CI #42321226504](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42321226504) | workflow completed / **SUCCESS** |
| Changed Lean job | `128245991469` completed / SUCCESS |
| 依存閉包 | **11,366 / 11,366 SUCCESS** |
| AHE新規定理の公理監査 | **16件**：`propext`・`Classical.choice`・`Quot.sound` のみ |
| sorryAx／変更Lean warning／error | **なし／0／0** |
| 独立completion receipt | job `128247469541` completed / **SUCCESS** |
| 変更 | 新規Lean1ファイル・386行、既存Lean変更／削除0 |

GitHub MCPから `lean-fast-check-log` の実物を回収し、`Build completed successfully (11366 jobs).`、新規16宣言の `#print axioms`、変更Lean warning/error 0/0、sorryAxなしをログ全文で確認した。既存依存Leanの非fatal linter warningと変更対象AHEの警告は混同しない。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。文書専用PRではStrict Leanを実行しない。別のGovernance/Strict Lean workflowが走ったとは主張しない。

## CLOSED — 元AGP真正signed-Haar有理表の厳密中心・不確実性分解

元AGP/AGI表の真正セル数を有限 `n`、下端／上端の元セル係数を `a_i^-, a_i^+`、真のHaar質量を包含する元の有理区間を `[l_i,u_i]` とする。真正AGPでは `l_i≤u_i` が同じ元Haar測度の有界性から形式証明される。正負の係数にかかわらず

```text
mid_i = (l_i+u_i)/2 ; err_i = (u_i-l_i)/2 >= 0
min(a_i^-*l_i, a_i^-*u_i) = a_i^-*mid_i - |a_i^-|*err_i
max(a_i^+*l_i, a_i^+*u_i) = a_i^+*mid_i + |a_i^+|*err_i
```

が `ℚ` 上の厳密恒等式である。したがって、元AGP表を一切書き換えずに

```text
originalTable.lower = Σ_i a_i^-*mid_i - Σ_i |a_i^-|*err_i
originalTable.upper = Σ_i a_i^+*mid_i + Σ_i |a_i^+|*err_i
```

をLean4で証明。両 `err` 合計は非負。真正有理表の正符号は `lowerMoment > lowerError`、負符号は `upperMoment + upperError < 0` と正確に同値である。半幅や絶対値の取り方を変更して符号を捏造していない。

## CLOSED — 固定H真正表のBoolean checkerとAHDへの接続

`p4Q2PZ37AHE_originalPositiveCheck` / `originalNegativeCheck` は元の `AGP_originalTable H d B b m n hn` をそのまま評価する有理演算のBoolで、実表の元Haar区間整合性を検証する証拠 `d` を保持する。Boolが`true`なら、既証明 `AGP_originalTransfer_bounds` により同じ真正 `t_H(B)` の厳密正／負符号を形式的に導く。

`original24PositiveCheck` / `original24NegativeCheck` は、既存 `AGP_original24Data H`（元AFQ/AGD 24中心・真正product-Haarセル質量区間）に具体的に特殊化し、その符号判定が`true`なら物理transferにも同符号であることを証明した。ただし**実際に`true`を返す固定H／B／m／nは示していない**。

AHDの任意精度定理を用いて、同じ元AGU precision-indexed 真正Haar表に対して

```text
(∃ R eps m n, finePositiveCheck = true) ↔ t_H(B) > 0
(∃ R eps m n, fineNegativeCheck = true) ↔ t_H(B) < 0
(∃ positive OR negative accepting fine checker) ↔ t_H(B) ≠ 0
```

を既証明AHC/AHDの仮定範囲（固定H、AGL有理座標の右境界）で形式証明した。AGUの格子選択は証明を伴う `Classical.choice` であり、大体積真正Haar表の実数値計算が済んだことは意味しない。

## OPEN — 実際の元物理非零符号の有限証人

AHEの新規16定理は **有理判定式の厳密性・真正Haarへの健全性・条件付き完全性**を確定する。一方、実際の固定Hと元Wilson作用・元centered source・真正Haarセル質量について上の厳密不等式を満たす元AGP有限有理データは**未構成**である。

**NEXT — AHF:** 真の有限セル・境界・m,n・質量有理区間の**明示的な構成・評価**と、実際に checker=true を与える符号証人（存在しなければ零／区間交差の obstruction）を探索する。古典選択Typeと実行可能な有限データは区別する。two-sign shell、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップ、非有理境界拡張は引き続き未証明。

[AHE Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/048d6b38a577201bb231147c6c4981789c4da5e8/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTrueHaarMidpointSignBudgetV5_PZ37AHE.lean)。本記録は追加の歴史記録であり、AHD以前の記録を削除・上書きしない。
