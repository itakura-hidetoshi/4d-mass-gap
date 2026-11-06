# P4-Q2-PZ37AGP 正式証明記録（2026-11-06 JST）

唯一のLean定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。著作権者：板倉英俊（Hidetoshi Itakura）。

## Source and exact-source receipt

- 定理PR：[ #6387 ](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6387) MERGED。
- 検証source：`fc93e5ca42aeef85dce18ed192032c682d2fb235`。
- Squash SHA：`57be141cd5d21158b5981469bb8f09b073f3ea8f`。
- 最終CI：[ #42175738816 ](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42175738816) completed/SUCCESS。Changed Lean job `127753651669`・Lean step completed/SUCCESS、独立completion receipt `127755458108` completed/SUCCESS。
- 完全依存閉包 **11,351/11,351 SUCCESS**、17件の `#print axioms` は `propext`, `Classical.choice`, `Quot.sound` の範囲内、sorryAxなし、変更Lean warning/error 0/0。
- 診断artifact `13483516878` digest `sha256:f045e02617689f5865594a1eb72a89a7a5fb7e822f87faa1f95ac4305f7b7ac4`。
- Source/test-merge `848ec1994f4df3bfa6d8517dcedf86195f1c5303`/squash共通Git tree `2324f41dd6fd7b9c0579cac6967caccc278a3350`。
- 新規Lean 1ファイル394行追加、既存削除0。元SU(2)、Wilson作用、中心化source、Haar/Perron、核、固定結合、transfer、root、workflow、Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` 不変更。

## 数学的結果

同じ元の連続積分代表 `g_B(A)=f_H(A)*(K_H(A,B)-(1+k_H)/2)` について中心C依存の変動評価

`|g_B(A)-g_B(C)| <= [6*(1-k_H)+13*beta0*|f_H(C)|]*D_H(A,C)`

を証明した。AGNの元Wilson Haar平均の厳密計算から `|f_H(C)|<=p_H/2`。したがって一様評価の源振幅項は旧AGGの半分まで改善される。ただし項全体の係数を半減したとの主張ではない。

各真正AGHセルの中心に有理座標証拠があり、セルごとの弦距離半径 `r_i` と真正product-Haar質量の認証有理端点が与えられたとき、中心の元kernel/source有理区間から `eps_i=c_i*r_i` の局所誤差を導いた。既知大域半径 `R_H` でクリップしたセル端点 `max(-R_H,a_i-eps_i)`・`min(R_H,b_i+eps_i)` は、各セルの全点における元の連続被積分関数を包囲する。既存AGIの符号付き `min/max` 集計器とAGNの真のHaar積分定理を、幾何誤差0の表（セル端点へ誤差を織り込んだため）として接続する。元transfer `t_H(B)` のAFV verifiedIntervalが得られ、過去の正しい区間との交差はtighten-onlyとなる。

既存24-center格子も入力できるが、その旧AGI評価器に関するAGOの障害を解消したとは主張しない。新しい細分格子・Haar質量の高精度数値構成は別途必要。非零signed transfer、二閾値殻、体積一様coercivity、Hamiltonian gap、連続体4D mass gapは未証明。

## Lean 4修正

最初のPRコミットのCIでは加法項の順序を整える書換えが失敗した。定理文を変えず、該当箇所を実際の順序に従う明示的な線形不等式で修正した。最終的なsourceで17宣言の公理依存を再監査し、変更warning/error 0/0を確認した。

Leanソース：[AGP 元source-adapted cellwise](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/57be141cd5d21158b5981469bb8f09b073f3ea8f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceAdaptedCellwiseV5_PZ37AGP.lean)。本記録は独立の追補であり過去の正式記録を上書きしない。
