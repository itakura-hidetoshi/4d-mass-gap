# P4-Q2-PZ37AJD — 元ZW源の真正全top射影のtransfer不変性と残余障害

2026年11月9日 JST。唯一のLean定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本書は検証来歴の記録であり、文章自体を証明とは扱わない。

[定理PR #6584](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6584) MERGED。 [統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/f646eb48342eac60f5e05acbbea60c5e846a33fb/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOverlapInvarianceV5_PZ37AJD.lean)。

## 1．対象・条件と新たな証明

元のSU(2) Wilson one-slab作用、左右halfweight、真正product-Haar測度、符号付き中心化ZW Gauss-law物理L²源 `f₀,H`、正規化物理transfer `N_H,β`、既存の**全top固有空間** `Top_H,β`、そのH・β依存の物理Hilbert内積を変更しない。すべての有限H∈ℕ・β>0で以下を扱う。既存top eigenspaceは `N_H,β v=v` を満たす真の固定部分空間であり、任意に選択したtopベクトル一本の張る直線とは同一視しない。

新しい唯一の派生定義は、転送**前**の元ZW源の全top直交射影

\[Q_{H,\beta}f_{0,H}:=\Pi_{\mathrm{Top}_{H,\beta}}f_{0,H}.\]

既存normalized transferの対称性とtopベクトルの固定性から、任意の真正topベクトル `v∈Top_H,β` に対し、

\[\langle N_{H,\beta}f_{0,H},v\rangle=\langle f_{0,H},v\rangle,\]

さらにMathlibの正準直交射影の一意性から、

\[\boxed{\Pi_{\mathrm{Top}_{H,\beta}}(N_{H,\beta}f_{0,H})=\Pi_{\mathrm{Top}_{H,\beta}}f_{0,H}}\]

を形式証明した。これはtop射影の**等式**であり、その射影が0であることや小さいことの証明ではない。

## 2．真正Haar-L²証明書との接続

AJCの同じ物理Hilbert空間の正準直交成分 `u_⊥,H,β` と、AJAの正のHaar-L²証明書 `C_H,β := m_H,β² Measure.real μ_H(R_H,β)>0` を変更しない。AJDは

\[\|N_{H,\beta}f_{0,H}\|^2=\|\Pi_{\mathrm{Top}_{H,\beta}}f_{0,H}\|^2+\|u_{\perp,H,\beta}\|^2,\]

\[\boxed{\|u_{\perp,H,\beta}\|^2\ge C_{H,\beta}-\|\Pi_{\mathrm{Top}_{H,\beta}}f_{0,H}\|^2}\]

を得る。特に `‖Π_Top f₀‖²<C_H,β` が**独立に証明される場合だけ** `u_⊥≠0`。現行Leanはその前件を証明していない。

## 3．新規宣言（Lean leaf 206行・新規7宣言）

ファイル：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOverlapInvarianceV5_PZ37AJD.lean`。1つの独立leafのみ新規追加・既存ファイル削除0。依存する定理の仮定や既存物理定義に変更なし。

| 実宣言suffix | 形式化された内容 |
|---|---|
| `realHilbert_symmetric_fixedSubspace_starProjection_eq` | 対称作用素が固定する閉部分空間の射影不変性（一般Hilbert補題） |
| `p4Q2PZ37AJD_originalSourceTopComponent` | 元源の全top正準射影の定義 |
| `p4Q2PZ37AJD_originalNormalizedSource_topInner_eq_source` | 元源像と元源の全topベクトルとの内積一致 |
| `p4Q2PZ37AJD_normalizedSourceTop_eq_originalSourceTop` | 転送前後の正準top射影一致 |
| `p4Q2PZ37AJD_sourceImage_norm_sq_eq_sourceTop_add_orthogonal` | 元源top射影で書いた正準Pythagoras |
| `p4Q2PZ37AJD_originalOrthogonal_norm_sq_ge_certificate_sub_sourceTop` | 元源top寄与を差し引くHaar証明書の残余下界 |
| `p4Q2PZ37AJD_orthogonal_ne_zero_of_originalSourceTop_small` | 厳密top上界が**別途あるときのみ**直交非零 |

## 4．exact-source／統合後pushと来歴

| 検証対象 | 結果 |
|---|---|
| [Exact-source CI #42634322528](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42634322528) | pull_request／SUCCESS、認証source `714aec58d29953b631010cd04d431ca4ccef4ca8` |
| [統合後push CI #42637270766](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42637270766) | push／SUCCESS、squash HEAD `f646eb48342eac60f5e05acbbea60c5e846a33fb` |
| Lean依存閉包 | 11,418 / 11,418 SUCCESS（統合後実ログ確認） |
| 新規宣言実公理出力 | 7/7、すべて `propext`／`Classical.choice`／`Quot.sound` のみ |
| AJD変更Lean warning／error | 0 / 0 |
| 新規 `sorryAx` | なし（7宣言実公理出力） |
| 独立completion receipt | SUCCESS（push実ログを確認） |
| Source／squash Git tree | `ce3176c00891e63ed5b7adaf796113a05fec1409` で一致（Git objectを直接確認） |
| 最終Lean blob | `7d443bad3c6db73962b8cf81cffbdb1171a4cf57` |

旧ファイル由来の非fatal警告はpush全体ログに残っているが、AJD変更leaf自身のwarning/errorはない。receiptはCI完了の受領記録であり、Lean kernelに代わる別個の形式証明ではない。固定環境：Lean v4.30.0-rc2／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## 5．未認証の障害とAJEへの境界

元ZW源の真正全top射影に必要な上界 `‖Π_Top f₀‖²<C_H,β` はOPEN。元ZW源のtop直交性、励起sectorの正の一様下界、全物理Hilbert coercivity、Hamiltonian spectral gap、4D連続体Yang–Mills mass gapは未証明として保持。AJEでは既存元源・topベクトル・実Wilson–Haar内積を調べ、上界を物理対象そのものから導けるか検証する。新しい仮定や代替モデルを挿入してはならない。

運用は append-only／tighten-only／overwrite-forbidden／same-root。
