# P4-Q2-PZ37AJI — 真正元Wilson transfer反復の全top射影への幾何収束と厳密AJA予算の有限証人同値性

2026年11月10日 JST。唯一のLean4定理正本は itakura-hidetoshi/4d-mass-gap の formal/real-hilbert-uniform-coercive-strong-limit。本書は機械検証済みソースの来歴記録であって、この文章自体は証明ではない。

[定理PR #6599](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6599) **MERGED**。[squash後の統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0548de742afda7894e6647a65dad2348b5a0ceac/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceFullTopPowerLimitV5_PZ37AJI.lean)。

## 1．元の物理対象・許容条件

有限H∈ℕ、実β>0ごとに、元の完全SU(2) Wilson one-slab、両端halfweight、真正積Haar確率、Gauss-law実物理Hilbert空間を維持する。元の符号付き中心化ZW物理源 f₀,H、元正規化物理transfer S_H,β、その**全**top固定固有空間 F_H,β=ker(S_H,β−I)、真正正準直交射影 Q_H,β、およびその直交補への既存の制限作用素 R_H,β は不変更。

既存物理定理から、S_H,β が対称・正・コンパクト・作用素ノルム1であり、**各固定H,βで** ‖R_H,β‖<1 を使用する。F_H,βの閉性と完備性は既存の定理から得ており、新しい物理仮定を追加しない。top eigenspaceが一次元とも、Haar定数ベクトルがtop固有ベクトルとも仮定していない。Hについての一様縮小率も導入しない。

## 2．9宣言で得られた新たなLean4形式証明

一般実Hilbertの射影分解・固定点性・部分空間の縮小作用素冪を使い、全自然数冪がtopを固定することと、n≥1で
\[
\boxed{
\|S_{H,\beta}^{n}f_{0,H}-Q_{H,\beta}f_{0,H}\|
\le
\|R_{H,\beta}\|^n
\|Q_{H,\beta}^{\perp}f_{0,H}\|
}
\]
を元の真正物理ノルムについて証明。従って
\[
\boxed{
S_{H,\beta}^{n+1}f_{0,H}\xrightarrow[n\to\infty]{L^2_{\rm physical}}
Q_{H,\beta}f_{0,H}.
}
\]
これは**全top空間**の射影への収束であり、選択Ωによる一次元射影への収束とは認定していない。

AJAが既に持つ真正の正Haar-L²証明書
\[
C_{H,\beta}
=m_{H,\beta}^2
\operatorname{Measure.real}\mu_H
\{B:u_{H,\beta}(B)<-m_{H,\beta}\}>0
\]
をそのまま用い、
\[
\boxed{
\|Q_{H,\beta}f_{0,H}\|^2<C_{H,\beta}
\;\Longleftrightarrow\;
\exists\,n\in\mathbb N,\ n>0\ \land\
\|S_{H,\beta}^{n}f_{0,H}\|^2<C_{H,\beta}
}
\]
を形式証明した。左→右は**既証明の全topへの反復収束と開集合の近傍性**から従い、右→左はAJHの射影ノルム上界による。**具体的な有限nは構成していない**し、左辺の厳密不等式自体を証明したわけではない。

さらに既存AJA下界
\[
C_{H,\beta}\le\|S_{H,\beta}f_{0,H}\|^2
\]
から、**n=1は厳密予算を満たせないこと**をLean4で形式証明した。従って有限証人が存在すれば n≥2 が必要である。証人が別途得られた場合に限り、元normalized ZW源の全top直交射影が非零となる。

## 3．新規Lean leaf・宣言一覧

新規ファイル1件：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceFullTopPowerLimitV5_PZ37AJI.lean`。**336行、追加のみ、既存ソース・物理定義・workflow・Lean/mathlib pin・公開root変更なし**。

| 宣言suffix | 形式化内容 |
| --- | --- |
| realHilbert_fixedSubspace_power_fixed_aji | 真正固定部分空間を任意の作用素冪が固定 |
| realHilbert_topOrthogonalRestriction_power_coe_aji | 直交補への制限冪とambient冪の一致 |
| realHilbert_fullTop_power_sub_projection_norm_le_aji | 一般実Hilbertでの全top幾何収束上界 |
| realHilbert_fullTop_power_succ_tendsto_projection_aji | 全topへの強収束 |
| p4Q2PZ37AJI_originalSource_power_sub_fullTop_norm_le | 真正SU2 ZW sourceへの幾何ノルム上界 |
| p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop | 真正元物理sourceの全topへの強収束 |
| p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget | 真正AJA厳密予算と有限反復証人との同値 |
| p4Q2PZ37AJI_no_firstPower_budget | n=1厳密予算の不可能性 |
| p4Q2PZ37AJI_originalOrthogonal_ne_zero_of_exists_transferPower_budget | 有限証人が与えられた場合の条件付き直交成分非零 |

全9宣言について独立した実行時`#print axioms`を設置した。公理は`propext`、`Classical.choice`、`Quot.sound`の標準3公理のみ。新規`sorryAx`なし。

## 4．初回失敗・修正の来歴

初回source `b4b8d748ac8fa80f736af3f18640377b90c4fe7b` に対する [CI #42708843152](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42708843152) は **FAILURE**。全文324行と依存補題、Lean固定環境の実ログを照合した。

- 81行・129行：汎用定理の宣言の型を作る際、`(realHilbertTopEigenspace S).HasOrthogonalProjection` のインスタンスがまだ得られず失敗。固定mathlib `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean` では`CompleteSpace K`から`HasOrthogonalProjection`を構成する実装が存在する。そこで汎用定理の署名に必要な型クラスを明示し、真正topの既存の閉性・完備性のインスタンスを具体的物理対象に与えた。**物理的な追加仮定ではない。**
- 216行：具体的SU2定理で巨大な定義を直接 `exact` に照合させたため、definitional equality検査（`isDefEq`）が3,900,000 heartbeatを使い切った。固定仮定やheartbeat上限は変更せず、元の正規化物理作用素`S`・対称性証明`hS`・全top`F`・制限`R`を明示的な型付き`let`に分解して、局所照合へ変更。
- 初回の`sorryAx`出力はエラーによる不完全な宣言に由来し、証明済みとして採用しない。修正後の実ログに残余`sorryAx`なし。

## 5．Exact-source・定理squashの最終認証

| 対象 | 確認結果 |
| --- | --- |
| 修正版exact-source CI | [#42710645084](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42710645084) completed／SUCCESS |
| Lean依存閉包 | 11,423／11,423 SUCCESS |
| 新規9宣言の実公理監査 | 9／9、標準3公理のみ |
| 新規sorryAx | なし |
| 変更Lean warning/error | 0／0 |
| 独立completion receipt | SUCCESS、exact-source head/runと一致 |
| 認証source | `bfe386d1a9d8a236c9605ea1b9914a2a93f8cfb1` |
| test-merge HEAD | `edbb9c9752befa6dcb32e83bd66042d7aa3d7688` |
| 正式定理squash／formal | `0548de742afda7894e6647a65dad2348b5a0ceac` |
| 3者の共通Git tree | `f2fdd35a8f37ce05a8512a2d28f9d2984fee3539`、一致 |
| 統合後push CI | [#42711612792](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42711612792)、別途完了再観測が必要 |

Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を固定。CIの独立completion receiptは別個のLean kernel証明ではない。

## 6．AJJへ残す障害

今回の同値性は**有限証人探索の完全性**であり、証人があるという存在主張ではない。真正AJA証明書Cを下回る`n≥2`の上界を未構成のまま保持する。選択真空ΩとHaar定数cの偏差`D=1−|⟨Ω,c⟩|²`に必要な上界、追加top残余`E=‖r‖²`が十分小さいこと、真正top eigenspaceの一次元性、無条件の励起sector非零、正のH一様下界、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapも未証明。

次段は、真正Wilson transferの`(I−S)c`残差と既証明の有限体積収縮率から、cの**全top空間への距離**を上から抑える可能性を検証し、選択Ωとの差およびtop多重度の残余を別々に保存する。append-only／tighten-only／overwrite-forbidden／same-root。

## 7．統合後push CIの独立再観測（追記）

[統合後push #42711612792](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42711612792) は **completed／SUCCESS**。真正formal定理squash `0548de742afda7894e6647a65dad2348b5a0ceac` のexact headで **11,423／11,423 Lean依存閉包SUCCESS**、AJI全9宣言の実公理出力は標準3公理のみ、変更Lean warning/error 0/0、新規sorryAxなしを実ログで独立確認した。

「Publish MCP CI completion receipt」も completed／SUCCESS。正式squashの `chatgpt-ci-receipt/PR Lean Fast Check` は `state=success` かつ run #42711612792 を指し、独立した完了記録として照合できた。したがって第5節で保留した統合後push結果は認証済みとなった。receiptを二つ目のLean証明とは扱わない。未構成のn≥2予算証人・無条件非零性・H一様gapは引き続きOPEN。
