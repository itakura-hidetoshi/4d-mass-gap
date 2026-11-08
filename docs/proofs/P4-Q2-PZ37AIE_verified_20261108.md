# P4-Q2-PZ37AIE — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：formal/real-hilbert-uniform-coercive-strong-limit。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson one-slab作用、両端halfweight、元ZW signed source、空間積Haar、物理的L2 transfer、型付き履歴、固定Lean/mathlibとworkflowは変更しない。

## 1．Exact-source形式証明台帳

| 項目 | 確定値 |
| --- | --- |
| [AIE定理PR #6508](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6508) | MERGED |
| 継承したcanonical formal HEAD | 3884e75eec91266f270b9f7a506ef0646cc7c164 |
| 最終exact-source HEAD | 7c850988470b6a53b9192b01b8d3e8a4a464f883 |
| 最終test-merge HEAD | a77c0017f42a408e35f5d9617be220594d7513d9 |
| 定理squash／formal HEAD | ce97bd5bd17dbde592921eda89d3e8b1677601f5 |
| source・test-merge・squash共通Git tree | a5472d2ddd4df69df2253bf4ebd4967c20631437 |
| 最終Lean Git blob | 87196f0019b1775b0c4411701408ce8f95cfa969 |
| [最終exact-source CI #42461907660](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42461907660) | completed／SUCCESS |
| Changed Lean job | 128672807435、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| 独立completion receipt job | 128673861461、completed／SUCCESS |
| Receipt実ログ | exact_sha=7c850988470b6a53b9192b01b8d3e8a4a464f883、source_result=success、run=42461907660、attempt=1 |
| Strict Lean依存閉包 | 11,393／11,393 SUCCESS |
| 新規宣言公理監査 | 8／8、標準 propext・Classical.choice・Quot.sound のみ |
| sorryAx | なし |
| 変更Lean warning／error | 0／0 |
| 最終diagnostic artifact | 13609524984、lean-fast-check-log |
| 最終artifact digest | sha256:df7f567fac5c82f475b94cde3d290709b45a8fb50832fc514f16e4448a4f0de4 |
| 新規Leanファイル | 1件・226行、7定理＋1定義 |
| 既存Lean／物理定義変更 | なし |

Leanはv4.30.0-rc2、mathlibは5450b53e5ddc75d46418fabb605edbf36bd0beb6で固定。すべての個別公理出力を完成Leanログの8宣言と照合し、欠落・重複・余剰、sorryAxを認めなかった。source/test-merge/squashの同一treeと最終formalファイルblobの一致をGitHub MCPで独立に読み戻した。failed CIおよび途中warning付きCIを最終成功の根拠にしない。

[Lean4定理全文（検証済みsquash）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ce97bd5bd17dbde592921eda89d3e8b1677601f5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceHaarLaplaceAnticorrelationV5_PZ37AIE.lean)

## 2．対象の authority 境界

本段階で新しく扱う量は、元の周期偶数4次元SU(2) Wilson模型における**元の空間配置積Haar確率測度** \(\mu_H\) と、元ZW signed sourceの既存連続代表 \(f_H\) に対するsource-only Haar–Laplace相関である。

元sourceは既存の定義から

\[
f_H(A)=\frac{W_H(A)-p_H}{2},
\qquad
\int f_H\,d\mu_H=0,\qquad
|f_H(A)|\le \frac{p_H}{2}.
\]

既存AHNの真正二次Haarモーメントは

\[
V_H=\int f_H(A)^2\,d\mu_H(A)>0.
\]

新しいsource-only相関を

\[
\boxed{
L_H(\beta)=\int f_H(A)e^{-\beta f_H(A)}\,d\mu_H(A)
}
\]

と定義する。定義上、ここにはまだ元のcrossing作用は入らない。元のsource、Haar測度、有限格子、物理作用・transferを変更・置換したものではない。

## 3．正負両方のsource値を扱うスカラー不等式

\(\beta\ge0\)、\(c\ge0\)、\(|x|\le c\) に対して、Lean4で次を証明した。

\[
\boxed{
x(e^{-\beta x}-1)\le
-\beta e^{-\beta c}x^2.
}
\]

\(x\ge0\) では、指数関数の接線評価 \(e^{\beta x}\ge1+\beta x\) に正の \(e^{-\beta x}\) を掛け、

\[
x(e^{-\beta x}-1)\le-\beta x^2e^{-\beta x}
\le-\beta x^2e^{-\beta c}
\]

を得る。\(x\le0\) では \(e^{-\beta x}\ge1-\beta x\) を非正の \(x\) で掛け、不等号を反転させる。

\[
x(e^{-\beta x}-1)\le-\beta x^2
\le-\beta x^2e^{-\beta c}.
\]

Leanでは固定mathlibの Real.add_one_le_exp、Real.exp_le_one_iff、Real.exp_le_expと符号付き乗算の不等式を使い、両枝を証明した。条件 \(\beta c\le1\) 等の小ささの仮定はない。\(x=0\)、\(\beta=0\) も含む。

## 4．真正Haar平均ゼロと定量的負性

既存のsource Haar平均零から、実際の積分の恒等式として

\[
\boxed{
L_H(\beta)=
\int f_H(A)\bigl(e^{-\beta f_H(A)}-1\bigr)d\mu_H(A)
}
\]

を証明した。被積分関数は元のcompact配置空間で連続なので、各可積分性は明示的に供給している。

前節のスカラー不等式を \(c=p_H/2\) として点ごとに適用し、積分の単調性を用いることで

\[
\boxed{
L_H(\beta)\le
-\beta e^{-\beta p_H/2}V_H
\quad(\beta\ge0)
}
\]

を形式証明した。

既存の \(V_H>0\)、元の plaquette count \(p_H>0\)、指数の正値から、全有限体積・全正結合について

\[
\boxed{L_H(\beta)<0\quad(\beta>0)}
\]

が従う。元固定結合

\[
\beta_0=\frac{\log(3/2)}{64}>0
\]

への直接の特殊化も証明済みである。指数減衰付きの定量下限を体積一様な下限と解釈しない。

この結果は元のsourceのゼロ平均と真のHaar二次モーメントに基づく**積分後の厳密な符号確定**であり、近似誤差の条件付き符号定理ではない。ただし対象はsource-only相関 \(L_H\) である。

## 5．8宣言・依存関係・固定API

新規宣言をそれぞれ個別の \#print axioms の対象とした。

| No. | 宣言 | 種別 |
|---|---|---|
| 1 | p4Q2PZ37AIE_real_centeredLaplace_quadraticUpper | 定理 |
| 2 | p4Q2PZ37AIE_originalCenteredSourceLaplace | 定義 |
| 3 | p4Q2PZ37AIE_originalCenteredSourceLaplace_integrable | 定理 |
| 4 | p4Q2PZ37AIE_originalCenteredSourceLaplace_eq_centeredDifference | 定理 |
| 5 | p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance | 定理 |
| 6 | p4Q2PZ37AIE_originalCenteredSourceLaplace_neg | 定理 |
| 7 | p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_neg | 定理 |
| 8 | p4Q2PZ37AIE_originalFixedCenteredSourceLaplace_le_negativeVariance | 定理 |

スカラー宣言はMGAP4D.MathlibAnalytic、元模型に依存する宣言はMGAP4D.MathlibAnalytic.GroundStatePosteriorJointのnamespaceにある。

直接importsは次の2件のみ：

- MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalConvexChordQuarticRemainderV5_PZ37AID
- Mathlib.Tactic

新規物理的source、Haar、crossing kernelや仮定は導入していない。前段AHPのsource平均零、AGNのsource絶対値の点ごとの上界、AHNの真正正分散と元の固定結合を使う。元の定義上の積分被積分関数が連続であることから可積分性を示している。

## 6．初回失敗・最終修正の証跡

初回source e6c6be40a08fdae1e1d686219d818351d5f2d451 に対する [CI #42461105332](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42461105332) は Lean stepの1件のtype mismatchでFAILUREとなった。積分の点ごとの目標が \(-(ab)c\)、既証明スカラー補題が \(-(abc)\) の結合形であり、Leanのelaborationが構文上の積の形を同一化しなかった。数学的な主張は同じである。

中間source d06e7aac52965ef20347d0893cf985065b6ba52a は convertとringによる代数正規化で [CI #42461508729](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42461508729) を11,393 jobs成功にした。ただし変更Leanに不要な tactic focus 記法のwarningが1件残った。

最終source 7c850988470b6a53b9192b01b8d3e8a4a464f883 では、証明の論理を変えず不要な記法（tac1 <;> tac2）を通常の逐次タクティクへ修正した。8宣言の型、仮定、定義、imports、元の物理定義、toolchain、workflowに変更はなく、同一HEADに対する完成CI #42461907660 と独立receiptで8宣言すべて標準公理・sorryAxなし・warning/error 0/0を確定した。

## 7．未解決のcrossing Haar平均と次段階AIF

元の物理的完全一スラブtransferは

\[
(T_{H,\beta}f_{0,H})(B)
=\int f_H(A)e^{-\beta(
W_H(A)/2+S_H^{cross}(A,B)+W_H(B)/2)}
\,d\mu_H(A)
\]

である。今回確定した \(L_H(\beta)\) はこれと同一ではない。

次の焦点は、全右境界の元のHaar平均

\[
\int_B e^{\beta W_H(B)/2}(T_{H,\beta}f_{0,H})(B)d\mu_H(B)
\]

を真のFubini積分へ接続し、各元空間リンクのSU(2)左Haar平行移動を使ってcrossing kernelの積分を評価できるかという点である。元のcrossing作用は各リンクの相対SU(2)元のWilson energyの和であり、積Haarによる正確な正規化が期待されるが、**このFubini・crossing相関の独立性・右境界平均の負性は本段階では未形式化**である。

したがって、元固定結合の物理的transferの無条件の符号、負の境界の存在、正負shell、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップはいずれも未証明である。今回のsource-only相関の負性を、それらの証明として扱わない。

本文の正式記録はcanonical formalへの新規appendのみとし、同一Git blobをmainへdocs-onlyで同期する。既存Lean、halfweights、source、Haar、物理transfer、proof history、root、固定toolchainおよびworkflowsを保持する。