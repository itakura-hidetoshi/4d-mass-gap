# P4-Q2-PZ37AGQ 正式証明記録（2026-11-06 JST）

著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean正本は `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラー。

## 正本・CI同一性

| 項目 | 確認結果 |
| --- | --- |
| 定理PR | [#6390](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6390) MERGED |
| 検証source | `237127ece19ba654a32cc6500dda4e6a8a5cdd31` |
| 定理squash | `1c19b6396248e74cce912204b68a59532e5ed514` |
| test-merge | `30024c215ef56cf6397ab0c57dc61eb5c98d2dbf` |
| 共通Git tree | `35dc6e3f41c2648339b07268c260db686959142d` |
| exact-source CI | [#42178646756](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42178646756) completed/SUCCESS |
| Changed Lean job | `127762857299` completed/SUCCESS、Lean step17 SUCCESS |
| 独立completion receipt | `127765120135` completed/SUCCESS、source commit status SUCCESS |
| 全Lean依存閉包 | **11,352/11,352 SUCCESS** |
| 新規公理依存 | **9宣言**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | なし |
| 変更Lean warning/error | **0/0** |
| 変更規模 | 新規Lean葉1件220行、既存Lean・root・workflow・依存pin変更なし |

固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。元のSU(2)・Wilson作用・固定結合・真のproduct Haar・Perron・source・kernel・transferの定義は不変更。

## 数学的内容

有限体積Hにおける元の真正AGH空間Borel格子を `grid` とし、格子の真のセル質量を `m_i = Measure.real mu_H (grid.cell i)`、格子のセル数を `N=grid.n` とする。任意の正の有理数 `eps` に対し、

`delta = (eps/(N+1))/2 > 0`

をセル数が確定した後に選ぶ。AFNの実数に対する有理密度を真の各Haar質量そのものへ適用し、`q_i : ℚ` と `|m_i-(q_i:ℝ)|<=delta` を得る。その証拠を持つ区間

`lower_i=q_i-delta`, `upper_i=q_i+delta`

はAGＮの真正 `massIntervals` 構造を満たす。さらに

`upper_i-lower_i = 2*delta`

なので、正確な有限和

`sum_i(upper_i-lower_i)=N*(2*delta)=N*eps/(N+1)<=eps`

をLean4形式証明した。質量区間の端点を「真の質量」と誤同一視せず、端点総和が1であるとの不正確な仮定も置かない。真の質量総和1はAGNで別途証明済み。

AGPの真正有理中心・証拠付きセル半径を入力とすると、上記の質量区間を任意精度で自動構成して、同じ元物理signed transferの`verifiedInterval`へ接続した。質量端点を外部から供給する前提を除去したが、構成はAFNの古典的有理選択に依存しており、実際の質量値を計算して出力する有限数値アルゴリズムという主張ではない。任意細分の有理中心被覆の存在も本モジュールでは証明していない。

## Lean4全文修正履歴

初回source `57449ea74a61cf03e86e91da0181e6a4e20fea45` のCI #42177901733では、複数行の`∑ i : Fin grid.n, upper i - lower i`において減算がbinder scope外へ結合し、`autoImplicit=false`のもとで`Unknown identifier i` が4か所発生した。初回の下流未解決ゴール／診断に現れた`sorryAx`は成功証明として採用しない。

証明したい和そのものの意味を明示するため、全4箇所の`upper i - lower i`を被加算項全体の括弧で囲み、`Finset.sum_const_zero`という使われていないsimp引数も除いた。定理文・数学的仮定・精度式を変更せず、最終source `237127ec...` で全9宣言を再検証。Lean再帰深度・heartbeatを緩和して回避する方式は使わない。

## 研究上の境界と次段

真正Haarセルの任意精度の**存在証明**から、大体積の質量表が実行可能・計算済みとは結論しない。新しい細分SU(2)格子で、有理座標中心の証拠、被覆、原Haar質量の実効的な包囲とsource/kernelの細分評価を結びつける必要がある。特に有理点の稠密性を元のSU(2)行列の座標規約へ結ぶ形式証明は別工程。実際の非零signed transfer符号、二閾値殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills質量ギャップはOPEN。

ソース：[AGQ Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1c19b6396248e74cce912204b68a59532e5ed514/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalMassBudgetGridDataV5_PZ37AGQ.lean)。旧AGO／AGPの正式記録・本文は保持する。
