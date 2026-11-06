# P4-Q2-PZ37AGZ 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。唯一のLean定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラーであり、異なる既存履歴を維持する。

## Exact-source検証とGit正本

| 項目 | 検証済み値 |
| --- | --- |
| 定理PR | [#6415](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6415) **MERGED** |
| 最終source HEAD | `2c7c0f7fe24a922e79c9d9ab1bac953c795db4b7` |
| test-merge SHA | `1b927405c88057697897b3f3cd6f9cba51e64e8e` |
| 定理squash SHA | `2af5eabd5191417c846ae2f2670c1757d3f68e95` |
| source/test-merge/squash共通Git tree | `a8a5c7c2c75e1bd147840ab2ec2e3f31e4ee5df8` |
| [Exact-source CI #42304072471](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42304072471) | workflow completed/SUCCESS |
| Changed Lean job `128188869200` | completed/SUCCESS |
| Lean dependency closure | **11,361 / 11,361 SUCCESS** |
| 新規宣言公理依存 | **11宣言、`propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 新規Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt `128191376313` | completed/SUCCESS |
| 変更範囲 | 新規Lean1件、304追加行、削除0 |

GitHub Actionsの `lean-fast-check-log` artifact を回収・照合し、末尾の `Build completed successfully (11361 jobs).` と新規11件の `#print axioms` を確認した。依存する従来ファイルには既存の非fatal linter warnings があるが、変更対象AGZ Leanには warning/error がない。固定Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。別workflowのStrict LeanやGovernance実行を主張しない。

## CLOSED — AGK結合区間から真正指数入力幅へ

AGNのglobal floorは真正の組合せ作用量、AGLのone-slab actionは各真正有理座標中心の厳密有理値であり、新たなaction-value oracleは不要である。

非負の真正作用量有理値 \(S\) に対し、AGKで証明済みの元固定結合 \(\beta_0\) の上下端点から指数入力端点を

\[
q^-_m(S)=-\beta_m^{\mathrm{upper}}S,\qquad
q^+_m(S)=-\beta_m^{\mathrm{lower}}S
\]

と定義。AGZで

\[
\boxed{
0\le q^+_m(S)-q^-_m(S)
=S(\beta_m^{\mathrm{upper}}-\beta_m^{\mathrm{lower}})
\le S\,\frac5{768}\left(\frac1{25}\right)^m
}
\]

を形式証明した。AGMによって元one-slab actionの非負性は自動取得され、floor側もAGNの真正global combinatorial action budgetで処理する。これは**指数入力幅**の収束率であり、Taylor指数出力区間幅そのものの収束を意味しない。

## CLOSED — 元AGM kernelと元AGN floorを生のAGK/AGJ Taylor幅へ接続

既存AGM `originalRationalKernelInterval` は、厳密AGL作用量、AGK固定結合区間、AGJのrational scaled Taylor constructionおよびAGM自動整数scaleから構成される。`originalClippedKernelInterval` はその**同じ真正Wilson kernel**の区間を [0,1] と交差したものである。したがって各真正中心 \(C_i\) に対し

\[
\boxed{\Delta K_i^{\rm clipped}\le \Delta K_i^{\rm rawTaylor}}
\]

を証明した。AGN元global floorもAGJ/AGK raw intervalと [0,1] の同一物理値に対する交差であるため

\[
\boxed{\Delta F^{\rm clipped}\le\Delta F^{\rm rawTaylor}}
\]

が成り立つ。生の両幅の非負性も、`verifiedInterval`の元の実数値包含関係から証明した。「Taylor幅」は結合区間幅を含む**有限有理数端点の差**であり、Taylor打切り残差だけを意味しない。

## CLOSED — 同一AGU真正格子上の有限最大とsigned transfer

AGYの**同じ**AGU precisionGridDataについて、各真正中心のraw Taylor kernel幅を `Finset.sup'` でまとめ、

\[
\Delta K_{\rm max}^{\rm clipped}
\le \Delta K_{\rm max}^{\rm rawTaylor}
\]

を証明。既証明の元signed transfer、中心化source、元Haar、Borel細胞、AGV/AGU radius・mass precisionは維持したまま、

\[
\boxed{
\operatorname{width}(I_H)
\le \frac{p_H}{2}
\left(\Delta K_{\rm max}^{\rm rawTaylor}
+\frac{\Delta F^{\rm rawTaylor}}{2}\right)
+2L_H(m)R+2M_H(m,n)\varepsilon
}
\]

をLean4で証明した。AGZの `p4Q2PZ37AGZ_transferWidth_of_rationalChecks` は、`DeltaKmax_rawTaylor ≤ etaK`・`DeltaF_rawTaylor ≤ etaF` という**有限有理数チェック証拠が与えられた場合**、上界を `etaK`・`etaF` で置換する定理である。実際に任意の精度でチェックが成立することは仮定も証明もしていない。

## OPEN — 次の数学的障害

AGKの `tail(m)→0` は既証明だが、AGJ Taylor出力端点の幅について、指数入力幅・正有理scale・Taylor次数・元作用量の有界性を合わせた明示的かつ一様な収束率はなお未証明。したがってAGZだけでは `DeltaKmax_rawTaylor→0`、`DeltaF_rawTaylor→0`、元signed transfer非零符号、H一様coercivity、two-threshold shell、Hamiltonian gap、連続体4D Yang–Mills mass gapを導けない。古典選択された大体積Haarグリッドの数値表も未評価。

**NEXT — AHA:** pinned mathlibでAGJ `expLower/Upper` の有理多項式差と `taylorError` の評価を接続し、AGK結合幅から生のkernel/floor出力幅へ一様精度保証を組み立てる。元物理値・measure・source・定理root・pinsは変更しない。

[AGZ Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/2af5eabd5191417c846ae2f2670c1757d3f68e95/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTaylorWidthBridgeV5_PZ37AGZ.lean)。
