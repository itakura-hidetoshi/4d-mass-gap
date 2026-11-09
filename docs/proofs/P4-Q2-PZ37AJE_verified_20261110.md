# P4-Q2-PZ37AJE — 元ZW源の真正全top射影の双対評価と必要障害

2026年11月10日 JST。唯一のLean定理正本は itakura-hidetoshi/4d-mass-gap の formal/real-hilbert-uniform-coercive-strong-limit。本文は検証来歴の記録であり、文章自体は形式証明ではない。

[定理PR #6587](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6587) MERGED。[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/661345cdc4100c06996dbf431a84f4ee96dacb35/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullTopOverlapDualBoundsV5_PZ37AJE.lean)。

## 1．真正対象・条件

既存の完全SU(2) Wilson one-slab、両端halfweight、真正product-Haar確率、有限HごとのGauss-law物理Hilbert空間、符号付き中心化ZW源 f₀,H、正規化物理transfer N_H,β、既存の**全top固有空間** Top_H,β を変更しない。対象はすべての有限H∈ℕ、β>0で、HをまたぐHilbert空間同一視はしない。

前段AJDは真正全top射影 Q_H,β に対して
\[
Q_{H,\beta}(N_{H,\beta}f_{0,H})=Q_{H,\beta}f_{0,H}
\]
を証明済みだが、射影の小ささは未証明である。

## 2．AJEで形式証明された全top双対評価

任意の実数 b≥0 に対して、同じH,βの元ZW源について
\[
\boxed{
\|Q_{H,\beta}f_{0,H}\|\le b
\iff
\forall v\in\mathrm{Top}_{H,\beta},\
|\langle f_{0,H},v\rangle|\le b\|v\|
}
\]
をLean4で証明した。量化されるvは**選択top固有ベクトル1本ではなく、全top部分空間の全ベクトル**。

同じ元の物理Hilbertノルムで
\[
\|Q_{H,\beta}f_{0,H}\|\le\|f_{0,H}\|
\]
も証明。既存の**選択単位top固有ベクトル** Ω_H,β に対して
\[
|\langle f_{0,H},\Omega_{H,\beta}\rangle|
\le \|Q_{H,\beta}f_{0,H}\|
\]
を証明した。これは一つの真正top方向から得られる**必要条件**に過ぎない。選択したΩの張る直線と全topを同一視せず、選択Ωへの小さい内積だけで全top射影の小ささを結論しない。

AJAのH,β依存の真正Haar-L²証明書
\[
C_{H,\beta}:=m_{H,\beta}^2\,\operatorname{Measure.real}(\mu_H,R_{H,\beta})>0
\]
について、次の同値もLean4で証明した。
\[
\boxed{
\|Q_{H,\beta}f_{0,H}\|^2<C_{H,\beta}
\iff
\exists b\ge0,\ b^2<C_{H,\beta}\land
\forall v\in\mathrm{Top}_{H,\beta},\
|\langle f_{0,H},v\rangle|\le b\|v\|
}
\]
**右辺を満たす具体的なbは構成していない。** これは求める物理的評価の必要十分条件の定式化であり、小top条件を無条件で証明したものではない。

## 3．新規Lean宣言の来歴

新規単独leaf MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullTopOverlapDualBoundsV5_PZ37AJE.lean、230行追加・既存削除0。新規9宣言と実際の9回の #print axioms。一般実Hilbert補題5件、真正元ZW対象の定理4件。

| 新規宣言のsuffix | 証明内容 |
| --- | --- |
| realHilbert_starProjection_inner_eq_of_mem | 元源と部分空間ベクトルの内積を正準射影へ接続 |
| realHilbert_starProjection_source_inner_self | 真正射影自己内積とノルム二乗 |
| realHilbert_starProjection_norm_le_source_norm | 正準射影の縮小性 |
| realHilbert_starProjection_inner_bound | 全部分空間ベクトルへのCauchy–Schwarz上界 |
| realHilbert_starProjection_norm_le_iff_uniform_inner_bound | 全ベクトルに対する一様上界の必要十分条件 |
| p4Q2PZ37AJE_originalSource_fullTop_inner_bound | 元ZW源の真正全top内積上界 |
| p4Q2PZ37AJE_originalSourceTop_norm_le_originalSource_norm | 元物理源の真正top射影縮小性 |
| p4Q2PZ37AJE_selectedUnitTop_sourceOverlap_le_fullTop_norm | 既存選択単位top固有ベクトルからの必要検査 |
| p4Q2PZ37AJE_originalSourceTop_small_iff_uniform_overlap_budget | 正のAJA証明書未満の全top一様内積予算との同値 |

既存AJD・固定mathlib射影APIのみを継承し、元物理定義、物理仮定、固定mathlib pin、Lean、root、workflowには変更なし。

## 4．初回CIのLean4 API不一致と修正

初回source dfac553c441096c77abd02671964caa13a6d0110 の[CI #42640480799](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42640480799)はFAILURE。AJE新規leaf 102行で (mul_le_mul_right hp).mp hmul がLean4の関数/定理インターフェースと一致せず、実ログに Invalid field mp と Application type mismatch が出た。初回依存公理出力中のsorryAxはこの未完了の下流証明に由来し、**初回sourceは未認証**である。

修正source 750b0fd38e88e85bc7965ab2ec7386a9abbdd9aa では、正のノルム hp に対して不等式が破れると仮定し、mul_pos と nlinarith で積の符号の矛盾を示した。**定理文・前提・真正物理対象は変更せず**、全9宣言を同じ意味で型検査した。

## 5．実CI・公理・Git認証

| 項目 | 認証済み結果 |
| --- | --- |
| 修正版Exact-source | [#42641688446](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42641688446) — SUCCESS |
| 統合後push | [#42642608623](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42642608623) — SUCCESS |
| 認証source | 750b0fd38e88e85bc7965ab2ec7386a9abbdd9aa |
| squash統合HEAD | 661345cdc4100c06996dbf431a84f4ee96dacb35 |
| 共通source/test-merge/squash Git tree | c4321886c4420c28d3d5e7782dd4974f964a132e |
| Lean依存閉包（統合後実ログ） | 11,419／11,419 SUCCESS |
| 新規宣言の実公理出力 | 9／9、propext・Classical.choice・Quot.sound のみ |
| 新規sorryAx／変更Lean warning／error | なし／0／0 |
| 独立completion receipt | SUCCESS（統合後pushでも確認） |
| 統合後最終Lean Git blob | 032a1e65a48bee50cf6784c6921bb37497416f09 |

全9宣言の実ログの公理出力と、統合後build成功・receiptをGitHub MCPで確認。receiptはCI状態の独立受領書であり、別個のLean kernel再証明を意味しない。固定Lean v4.30.0-rc2、mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6。

## 6．未認証の物理的障害と次段

元ZW源について全top内積の一様評価を**実際に構成**すること、特に \(\|Q_{H,\beta}f_{0,H}\|^2<C_{H,\beta}\) は未証明。元のHaar平均中心化は定数方向への直交性に過ぎず、真の全top eigenspaceとの直交性には昇格できない。選択topベクトル一本の評価と、全topへの上界も混同しない。

真の励起成分の無条件な正量的下界、全H一様coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapはOPEN。次段AJF以降では真正Wilson–Haar内積と既存topベクトル／全topの関係から数値的な証明書を探し、見つからなければobstructionとして保持する。

append-only／tighten-only／overwrite-forbidden／same-root。
