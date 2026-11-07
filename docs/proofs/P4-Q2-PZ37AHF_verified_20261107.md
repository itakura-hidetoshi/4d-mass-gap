# P4-Q2-PZ37AHF 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。`main` は文書ミラー。元Wilson作用・centered source・kernel・floor・Haar測度・既存Type値証拠・公開root・固定Lean/mathlibを変更しない。

## 検証済み正本

| 項目 | 確認結果 |
| --- | --- |
| [AHF定理PR #6433](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6433) | MERGED |
| AHE継承基点 | `fa74c962bdd0ba126ad686436bdabda6eb3e3556` |
| 最終exact-source HEAD | `37ab3c3883a78c2076407b8e22a6fa8ef3469c22` |
| test-merge SHA | `7796a3d294ea567a5eebaefbe7452c59cee96ed4` |
| theorem squash SHA | `86b19fa57650ac9f7771a2d37c659d55837c0033` |
| source/test-merge/squash共通Git tree | `201b10c2058662efaf3b46c5a066426831103857` |
| [Exact-source CI #42324945920](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42324945920) | workflow completed / SUCCESS |
| Changed Lean job | `128257946776` completed / SUCCESS |
| Lean依存閉包 | **11,367 / 11,367 SUCCESS** |
| 新規定理公理依存 | **20宣言**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt | job `128259580055` completed / SUCCESS |
| 変更 | 新規Lean1件・451追加行、既存Lean変更・削除0 |

GitHub MCPから最終 `lean-fast-check-log` artifact `13554956951` の実物を回収し、`Build completed successfully (11367 jobs).`、全20件の公理依存、変更ファイルの警告・エラー0、ログ内sorryAxなしを検査した。初回失敗ログとは区別する。独立Strict Lean/Governance workflowが実行されたとは主張しない。固定Leanは `v4.30.0-rc2`、mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## CLOSED — 元AGPセル半径による符号障害

`p_H` は元空間plaquetteリスト長、`delta = 1 - originalFloorInterval.lower`、`M_H = p_H * delta / 4` は元AGN transferRadius。元floor包含から `delta >= 0`。元AGPのsource適応係数は

```text
L_i = 6*delta + 13*beta_upper*|source_i| >= 6*delta.
```

元セルの認証半径 `r_i` に対して、任意の有理 `k` について

```text
r_i >= k*p_H/24  ==>  originalCellBudget_i >= k*M_H
```

を形式証明した。`delta` で除算せず、`delta=0` の場合も扱う。元のkernel、source、符号付きmin/maxを別のモデルへ置換しない。

### p_H/24 — 両符号の棄却

全セルの認証半径が `r_i >= p_H/24` なら、元AGPの各セル下端・上端は0をまたぐ。真正Haar質量の上端が非負であることから、元のsigned min/max和も0をまたぎ、AHEの正・負Boolean checkerはともに `false` となる。

Haar質量の有理下端が負になることも許し、上下端ベクトルが総和1という偽の仮定は加えていない。

### p_H/12 — 大域区間への完全な退化

全セルの認証半径が `r_i >= p_H/12` なら、元AGP clippedセル区間は厳密に `[-M_H,M_H]`。真のHaar質量の総和1から有理上端質量の総和が1以上であることを導き、元raw表が `[-M_H,M_H]` を包含すると証明した。したがって、元AGN global区間とのtighten-only交差は厳密にglobal区間そのものとなる。

## CLOSED — literal original24での全体積・全次数の棄却

元空間の各頂点には空間方向が3個、増加方向対も3個あるため、元plaquette数と元正向き空間リンク数の一致を証明した。

```text
p_H = card(PeriodicHypercubicEvenSpatialSliceLink H).
```

既存 `p4Q2PZ37AGP_original24Data H` が持つ認証半径は、その元定義のまま

```text
r_i = (4/5)*p_H >= p_H/12.
```

よって、**すべてのH、AGL有理座標証拠を持つ元右境界B、結合近似次数m、Taylor次数n>0**について

```text
AHE_original24PositiveCheck H B b m n hn = false
AHE_original24NegativeCheck H B b m n hn = false
original24 tightened interval = [-M_H,M_H]  (上下端の厳密一致)
```

が成立する。同じ真正セル・同じ認証半径・同じAGP評価式を保持する限り、質量区間を任意の別の正しいHaar包含区間へ改善しても両checkerの棄却は変わらない。

これは24中心そのものに対するあらゆる可能な鋭い評価を否定する定理ではない。**literal original24の既存認証半径と元AGP評価式**についての障害であり、元物理transferが0という主張でもない。

## CLOSED — 受理に必要な細分条件

一般の元AGPデータで正または負checkerが受理されるなら

```text
exists i, r_i < p_H/24.
```

元AGU precision-indexedデータで全セル半径がRなら、受理から `R < p_H/24` が従う。いずれも**必要条件であって十分条件ではない**。少なくとも一セルの条件を全セルの条件に読み替えない。

## 初回CIと修正理由

初回CI `42324080216` では `count_eq_links` の個数比較だけが失敗した。元plaquetteリストの `Subtype.fintype` と、import経由のAAX2頂点Fintypeが異なり、同じ型の個数であっても定義上同じ式にならなかった。

固定mathlibの `Nat.card_congr` と、まさに異なるFintype実装を揃えるための `Fintype.card_eq_nat_card` を使用し、証明の2行だけ修正した。定理文・仮定・型・元の列挙・物理定義は不変更。修正版の全20宣言を最終CIで再検証し、初回失敗に由来するsorryAx依存が残っていないことを確認した。

## OPEN / NEXT — AHG

固定24中心の既存半径を維持して、Taylor次数・結合精度・Haar質量精度だけを増やす経路は除外できる。次は上記必要条件を満たす細かい真正セルと元物理有限データ、または同じ元source/kernelに対するより鋭い評価から、実際の正・負符号証人を構成する。

AHEの条件付き完全性は元AGUの任意精度格子族全体についての結果であり、AHFによる固定original24の棄却と矛盾しない。実際の非零signed-transfer証人、二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップは本結果では未証明のまま保持する。

[A H F Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/86b19fa57650ac9f7771a2d37c659d55837c0033/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2Original24SignObstructionV5_PZ37AHF.lean)。本記録は新規ファイルとして追加する。今回はREADME・ROADMAPを更新せず、両ブランチそれぞれの旧本文と過去の正式記録をそのまま保持する。文書専用PRでStrict Leanは起動しない。
