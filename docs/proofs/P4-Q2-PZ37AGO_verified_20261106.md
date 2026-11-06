# P4-Q2-PZ37AGO 正式証明記録

記録日：2026-11-06 JST。著作権者：板倉英俊（Hidetoshi Itakura）。唯一のLean 4正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは文書ミラー。

## 定理・検証状態

- 定理PR：[ #6384 ](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6384) **MERGED**。
- 検証source：`82dc6a7bae92b40fbff48f23ddc778fb1f552e5d`。
- squash / canonical定理HEAD：`c6f0b5b3ed640774f5539813f33c75259224f6ca`。
- exact-source CI：[ #42169865632 ](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42169865632) completed/SUCCESS、Changed Lean job `127734898892` completed/SUCCESS（Lean step17 SUCCESS）、独立receipt `127736380281` completed/SUCCESS。sourceの `chatgpt-ci-receipt/PR Lean Fast Check` SUCCESS。
- **11,350 / 11,350** 依存閉包のビルド成功。新規12 `#print axioms` 対象は `propext`・`Classical.choice`・`Quot.sound` のみ、`sorryAx` なし、変更Lean warning/error **0/0**。
- source・test-merge `9feb90a8673e38e7bfc147ba3f7c1991a2c7c586`・squashの共通Git tree `60763de825d87805002e42445325e4b7121bd315`。
- 新規Lean葉1ファイル377行追加。既存Lean削除・workflow変更・root変更なし。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。

## 数学的内容：AGI signed min/max の一般飽和定理

有理テーブル `d` と半径 `R >= 0` を固定する。すべてのセルiで`0 <= massUpper_i`、`sum_i massUpper_i >= 1`、`sampleLower_i <= R`、`-R <= sampleUpper_i`、全体の幾何予算が `2R <= geometry` なら、セル下端 `sampleLower_i-geometry <= -R`、上端 `sampleUpper_i+geometry >= R` が成立する。従ってAGIの符号を保持した定義

`rawLower = sum_i min(cellLower_i*massLower_i, cellLower_i*massUpper_i)`

`rawUpper = sum_i max(cellUpper_i*massLower_i, cellUpper_i*massUpper_i)`

から `rawLower <= -R`、`rawUpper >= R` をLean 4証明。質量下端が正であること、質量上下端の和が1であること、被積分関数の符号などを仮定しない。Boolの正負判定はいずれもfalseとなる。

これとは独立の真の値に対する区間 `[-R,R]` と交差すると、定義上その全区間が残る。

## 真正モデルへの無条件の特殊化

元の空間正リンク型は「元空間頂点×3方向」、元plaquette型は「元空間頂点×3つの順序付き（厳密順）方向対」である。標準の `Fin 4` と `Nat.card_prod`、`Fintype.card_eq_nat_card` を用いて、元plaquette listの長さ `p_H` と元空間リンク数の一致を示した。これはlocal `Fintype.ofFinite` インスタンスと数値の評価順に依存しない。

AGNの元固定24中心格子は、真のproduct-Haarセル質量を持ち、上端ベクトルの和が1以上である。AGNの厳密中心化とkernel/floor区間から任意の元中心で `|g_B(A)| <= R_H` が成立する。固定元格子の球半径は `(4/5)*p_H`。AGKの `betaUpper(m)>=0`、AGN floor下端 `>=0` を用いて

`R_H=p_H*(1-floorLower_H(m,n))/4 <= p_H/4`

`gamma_H=(6+13*betaUpper(m)*p_H)*(4/5)*p_H >= (24/5)*p_H >= 2R_H`

をすべての有限H、m,n（`n>0`）で導いた。したがって元のcertified raw表の全端点と最終 `p4Q2PZ37AGN_original24TransferInterval` に対し、

`rawLower_H <= -R_H`, `R_H <= rawUpper_H`, `finalLower_H=-R_H`, `finalUpper_H=R_H`

が厳密に成立する。元右境界の各リンクに有理座標証拠がある場合、正負どちらの区間判定にも成功しない。

これは「固定24中心＋現行幾何予算＋現行AGI評価器」の形式的限界である。元のtransfer `t_H(B)` がゼロであるという定理ではなく、他の格子・改善幾何・直接積分の符号判定可能性を排除しない。

## Leanエラー分析と修正

PR初回commit `40f355994c9f34ceeae670aa4f92a0503eb190b8` では一般飽和・真正Haar質量・条件付き元transferの8宣言をLean stepで成功させたが、後続追記のためworkflow全体はcancelledであり成功判定に採用しない。続くcommit `ba7065514bab6a2c9bf401e94d40164484c9ba4b` のCI #42169137984は、数え上げ補題中の `simp [periodicHypercubicEvenSpatialSlicePlaquetteList, Fintype.card_eq_nat_card]` に対し、mathlibの `Nat.card_eq_fintype_card` と双方の書換えが循環して `maximum recursion depth has been reached` となった。

実際の型・import・Lean4固定記法と全変更ファイルを確認し、定理文・仮定は維持したまま、`Finset.length_toList`、`Finset.card_univ`、`Fintype.card_eq_nat_card` の一方向だけを指定する `simp only` に修正。maxRecDepth増大やsorryでの迂回は行っていない。最終commit `82dc6a7bae92b40fbff48f23ddc778fb1f552e5d` を完全な依存閉包と公理監査まで再検証した。

## 未解決と次段

元SU(2)の同一性、元Wilson作用、固定結合、真正空間Haar、Perron、元中心化source、transfer、FF、既存Lean rootは変更していない。任意の境界での非零signed transfer符号、二閾値殻の非空、H一様coercivity、物理Hamiltonian gap、連続体四次元Yang–Mills質量ギャップは未証明。

次段の有効な研究対象は、固定24中心で消せない半径 `4/5` の障害を真正SU(2)細分格子・可検証な細胞Haar質量・局所振動の鋭い上界・モーメントや相関を使った積分恒等式によって改善すること。Taylor/結合次数のみの増大では今回の障害を変えない。

ソース：[AGO Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c6f0b5b3ed640774f5539813f33c75259224f6ca/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixed24SignedGeometryObstructionV5_PZ37AGO.lean)。本書は独立追補であり過去の形式記録を書き換えない。
