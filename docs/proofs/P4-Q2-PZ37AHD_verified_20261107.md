# P4-Q2-PZ37AHD 正式証明記録（2026-11-07 JST）

著作権：板倉英俊（Hidetoshi Itakura）。Lean定理の唯一の正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラー。元物理定義・Haar測度・Type値証拠履歴・公開root・固定Lean/mathlibを変更しない。

## Exact-source CI・Git正本

| 項目 | 確定検証結果 |
| --- | --- |
| 定理PR | [#6427](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6427) **MERGED** |
| 最終exact-source HEAD | `dac657f2068a54bef2c22a8d7bdc5531a79f3628` |
| test-merge SHA | `c82a0b7aaf5fda0396672cf5f7fc76c06812de91` |
| 定理squash SHA | `9e9730d808d2e4e774ae950e1b0c2f64a9a5ceb5` |
| source/test-merge/squash 共通Git tree | `c7a7f3c76072b0549fd3571948338ec07eaeee5d` |
| [Exact-source CI #42318237854](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42318237854) | workflow completed / **SUCCESS** |
| Changed Lean job `128236119062` | completed / SUCCESS |
| Lean依存閉包 | **11,365 / 11,365 SUCCESS** |
| 新規定理公理依存 | **14宣言：`propext`・`Classical.choice`・`Quot.sound` のみ** |
| sorryAx / 変更Lean warning / error | **なし / 0 / 0** |
| 独立completion receipt job `128237932327` | completed / SUCCESS |
| 定理変更 | 新規Leanファイル1件・388追加行、既存Lean変更・削除0 |

GitHub MCPで `lean-fast-check-log` artifactを回収し、`Build completed successfully (11365 jobs).`、新規14件の `#print axioms`、変更Lean warning/error 0/0、sorryAxなしを確認した。依存する既存Leanの非fatal linter warningと変更ファイルの診断は区別する。固定Lean `v4.30.0-rc2`・mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を維持。文書PRでStrict Leanの実行は行わない。独立Governance/Strict Lean workflowを実行したという主張はしない。

## CLOSED — AHC任意精度区間の符号判定完全性

既証明AHCは、各固定H・全元AGL有理座標右境界Bに対し、同じ真正 `t_H(B)` を含む元AGU signed-transfer認証区間を、任意の正有理幅 `η` 未満に構成する。これと固定mathlibの `exists_rat_btwn`（実数間の有理数稠密性）から、**実際の正の `t_H(B)` が存在する場合**、それより小さい正有理精度を選び、区間の**有理下端が正**になることをLean4で証明した。負の場合も同様に**有理上端が負**となる。逆方向はAFVの元verifiedInterval包含証明を直接使う。

\[
\boxed{
\begin{aligned}
t_H(B)>0
&\iff \exists R,\varepsilon,m,n:\ I_H^{\rm lower}>0,\\
t_H(B)<0
&\iff \exists R,\varepsilon,m,n:\ I_H^{\rm upper}<0.
\end{aligned}}
\]

ここで `R,eps>0`、`n>0`、`I_H` はAHCと同じ元物理 `p4Q2PZ37AGU_fineOriginalTransferInterval`。真正右境界のAGL有理座標証拠は固定して保持する。したがって

\[
\boxed{t_H(B)\ne0
\iff\exists\text{真正元AGU区間の正または負の符号証明書}}
\]

も形式証明した。これは**実際の非零 `t_H(B)` や具体的表の存在証明ではない**。符号に関する真偽の境界を厳密に特定したもの。

## CLOSED — zeroのobstructionを明示

元AFV verifiedIntervalは上下有理端点に真の実数値を包含する。値がゼロならどの区間も

\[
I_H^{\rm lower}\le0\le I_H^{\rm upper}
\]

を満たす。AHCの任意精度性を使った逆方向と併せ、

\[
\boxed{
t_H(B)=0\iff
\text{あらゆる真正元AGU区間がゼロをまたぐ}
}
\]

をLean4形式化。さらに`0`を含む**幅ゼロ**のAFV認証区間を直接構成し、`width(I)<eta` から `t\ne0` を推論するのは誤りだと形式的に示した。

## CLOSED — 符号証明書は元AGPのsigned Haar有理表へ帰着

AGU最終区間は、**同じ真正元物理signed transfer**を含む

1. 元AGPの本物のBorel/Haarセル・中心区間から組み立てた `originalTable` の生のsigned min/max有理区間
2. 元AGNが元Haar/中心化Wilson sourceから別途証明した対称global区間 `[-M_H(m,n),M_H(m,n)]`

の交差であり、`M_H≥0` はAGVから既証明である。従って対称global区間自身は正負のstrict endpointを与えず、AGU最終区間が正下端／負上端を持つ条件は**AGPの生の有理表の正下端／負上端条件と同値**：

\[
\boxed{
\begin{aligned}
I_H^{\rm lower}>0
&\iff \mathrm{AGPTable}^{\rm lower}>0,\\
I_H^{\rm upper}<0
&\iff \mathrm{AGPTable}^{\rm upper}<0.
\end{aligned}}
\]

これと前段の符号判定完全性を結合し、

\[
\boxed{
t_H(B)\ne0\iff
\exists\text{真正元AGP signed-Haar有理表の正下端または負上端}
}
\]

をLean4で形式証明した。また `t_H(B)=0` は正表・負表のどちらの証明書も存在しないことと同値。**Haar mass endpointsの下端を不当に非負と仮定したり、有理質量和を1で置き換えたりしていない。** 旧AGP/AGI signed min/max・元Haar総質量1・旧source/kernel/floorを一切保持する。

## CLOSED — 型付き符号証明書を別々に保持

`finePositiveCertificate`・`fineNegativeCertificate`、`rawHaarPositiveCertificate`・`rawHaarNegativeCertificate` は個別の`Prop`として保持する。元物理の真値、原Haar積分、有限有理表を別の表現へ置換して同一視しない。存在定理には、AHCの古典選択された元AGU精度付き格子と、有理数稠密性による証人選択が含まれる。格子を具体的に計算・列挙したわけではなく、構成的な数値符号証明書の実例が存在することは**未確認**である。

## OPEN — AHE以降に必要な真正物理証人

AHDは既存任意精度証明から**conditional completeness**を確立したにとどまる。未解決なのは、少なくとも一つの真正有限H・元AGL有理右境界について、原Wilson作用、原中心化sourceと真のHaarセル質量を認証した元AGP `originalTable` の正下端または負上端を実際に**構成・証明**すること。非計算的な古典選択格子では直ちに実用数値計算にならないため、具体的なHでの有限網と真のmass証明書を別途構築する必要がある。非有理右境界への十分な拡張、二符号殻、H一様coercivity、Hamiltonian gap、連続体4D Yang–Mills mass gapもなおOPEN。

**NEXT — AHE:** 新しい物理的非零値を仮定せず、元AGPの`originalTable`を実際に評価・符号判定するための有限有理数データと本物のHaar mass認証の依存関係を特定する。固定Hでの実行可能・再現可能な証明書を優先する。

[AHD Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/9e9730d808d2e4e774ae950e1b0c2f64a9a5ceb5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSignedTransferSignCertificatesV5_PZ37AHD.lean)。
