# P4-Q2-PZ37AJC — 元の正規化ZW物理源像の全top正準直交射影と定量的障害

2026年11月9日 JST。唯一のLean定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本記録は機械検証された内容と来歴を記述するものであり、文章自体は形式証明ではない。

[Lean定理PR #6581](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6581) ／ [squash後のLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/eda6b204e5bbbae65809aa968957736ad763b62e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceCanonicalTopProjectionV5_PZ37AJC.lean)。

## 1．元の対象と条件

元の完全 SU(2) Wilson one-slab作用、両端halfweight、真正product-Haar確率測度、符号付きZW Gauss-law物理L²源 `f₀,H`、既存の物理transfer `P_H,β` とその**既存物理ノルム**による正規化 `N_H,β`、既存の**全top固有空間** `Top_H,β` を変更しない。全top固有空間と任意に選択した一つのtop固有ベクトルの張る直線は、証明なしに同一視しない。有限体積Hごとに物理Hilbert空間は異なる。

`R_H,β` は元AIGの厳密負領域と同一のHaar可測集合、`m_H,β>0` はAIWの元の余裕を同じ物理作用素ノルムで割った正規化余裕。AJAで形式証明した各有限H・全β>0の正証明書を
\[
C_{H,\beta} := m_{H,\beta}^2\,\operatorname{Measure.real}(\mu_H,R_{H,\beta})>0
\]
と書く。この量はHおよびβに依存する。

## 2．証明された正準分解と定量下界

AJBの任意存在分解に対し、AJCでは既存Mathlibの `Submodule.starProjection` を同一元物理Hilbert空間の**既存全top固有空間**とその直交補へ適用し、指定された正準二成分を構成した。

\[
u_{\mathrm{top}}:=\Pi_{\mathrm{Top}_{H,\beta}}(N_{H,\beta}f_{0,H}),\qquad
u_{\perp}:=\Pi_{(\mathrm{Top}_{H,\beta})^\perp}(N_{H,\beta}f_{0,H}).
\]

元の正規化ZW源像に対して次の恒等式と証明書比較がLean4で成立する。

\[
N_{H,\beta}f_{0,H}=u_{\mathrm{top}}+u_{\perp},\quad
\|N_{H,\beta}f_{0,H}\|_{L^2}^2
=\|u_{\mathrm{top}}\|^2+\|u_\perp\|^2,\quad
0<C_{H,\beta}\le\|u_{\mathrm{top}}\|^2+\|u_\perp\|^2.
\]

さらに**条件付きの厳密な残余下界**
\[
C_{H,\beta}-\|u_{\mathrm{top}}\|^2\le\|u_{\perp}\|^2
\]
を証明した。従って \(\|u_{\mathrm{top}}\|^2<C_{H,\beta}\) が**別に証明された場合のみ** \(u_{\perp}\ne0\) を導く。

## 3．新規宣言と証明境界

新規独立Lean leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceCanonicalTopProjectionV5_PZ37AJC.lean` は186行追加・削除0。**正準射影の定義2件、定理7件、9件の実際の `#print axioms`** を持つ。すべての宣言は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。

| 新規宣言のsuffix | 内容 |
|---|---|
| `p4Q2PZ37AJC_originalNormalizedSourceTopComponent` | 既存全topへの元源像の正準直交射影（定義） |
| `p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent` | 既存全top直交補への正準直交射影（定義） |
| `p4Q2PZ37AJC_originalNormalizedSourceTopComponent_mem` | top成分が全topに属する |
| `p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent_mem` | 直交成分が既存全topの直交補に属する |
| `p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_sum` | 正準両成分の和による元源像の厳密再構成 |
| `p4Q2PZ37AJC_originalNormalizedSource_canonicalProjection_norm_sq` | 元物理Hilbertノルムのピタゴラス恒等式 |
| `p4Q2PZ37AJC_originalHaarCertificate_le_canonicalProjection_norm_sq` | AJAの真正Haar-L²証明書から正準両成分のノルム二乗和への比較 |
| `p4Q2PZ37AJC_originalOrthogonalNorm_sq_ge_certificate_sub_top` | 実top寄与を差し引いた条件付き残余下界 |
| `p4Q2PZ37AJC_originalOrthogonalComponent_ne_zero_of_top_small` | 実top射影ノルムの厳密上界が**別途得られた場合のみ**直交非零 |

直接importは統合済みAJB、既存のtop eigenspace直交分解、固定mathlibの射影API、Mathlib.Tactic。新しい物理対象や元のtop eigenspace定義の置換はない。

## 4．初回CI失敗の構造原因と修正

初回実装source `5192b453d9c5cbf38be4c5b049ec6da65cf65f66` の[CI #42616327394](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42616327394)はFAILUREであり未認証。新規sourceの84、116、119、129、131行でLeanが `No goals to be solved` を報告した。初回の局所 `HasOrthogonalProjection` インスタンス構成では、既存閉部分空間の完全性からの型クラス導出に余分な証明段階があり、既に解決されたgoalに後続tacticを実行していた。

修正では既存閉性定理の `.completeSpace_coe` から**既存全top固有空間のCompleteSpaceインスタンス**を直接供給し、固定Mathlibの正準射影インスタンス生成をそのまま使用した。物理定義、9宣言の数学的条件、固定環境、root、workflowは変更しない。

## 5．最終Exact-sourceと統合後push認証

| 項目 | Exact-source | 統合後push |
|---|---|---|
| CI | [#42617449250](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42617449250) | [#42618394145](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42618394145) |
| イベント・結果 | pull_request／SUCCESS | push／SUCCESS |
| 認証HEAD | `6f16501c87ff57941b9244efd0ef7b6465cf9f9c` | `eda6b204e5bbbae65809aa968957736ad763b62e` |
| Lean依存閉包 | 11,417/11,417 SUCCESS | 11,417/11,417 SUCCESS |
| 公理出力 | 9/9 | 9/9 |
| 新規宣言依存公理 | `propext`、`Classical.choice`、`Quot.sound` のみ | 同左 |
| 変更Lean warning/error | 0/0 | 0/0 |
| 新規 `sorryAx` | なし | なし |
| 独立completion receipt | SUCCESS | SUCCESS |

CI実ログの全9 `#print axioms` と独立receiptを確認。receiptは第二のLean kernelによる再証明ではなく、実行結果の受領記録である。source／squashはともにGit tree `caefa8a12dbe42b122f559fe0a6f198e9a49b237`。最終Lean blobは `0b20f8e9fee8fe383fd0e33802e6590e311acab0`。

## 6．未認証事項と次段AJD

**既存の元ZW正規化源像について、実際の全top射影二乗ノルムが \(C_{H,\beta}\) より小さいとは証明していない。** 正準射影が構成されたことだけで励起成分非零とは言えない。元ZW源そのもののtop直交性、H一様正振幅、真の励起下界、coercivity、Hamiltonian spectral gap、非自明な4次元連続体Yang–Mills構成とmass gapはOPENとする。

次段AJD候補では、同じ元物理Hilbert空間における実際のtop-overlap、元の中心化ZW源とtop固有空間の関係、既存Wilson-Haar内積と正準射影の整合を独立に調べる。上記の不足する不等式は、証明なしに仮定として追加しない。
