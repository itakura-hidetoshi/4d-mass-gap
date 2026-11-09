# P4-Q2-PZ37AJB — 元の正規化ZW物理源像のtop/直交成分定量分解

2026年11月9日 JST。唯一のLean定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。本書は機械検証済み定理の適用条件とGit/CI来歴を記録する。説明文は証明ではない。

[Lean定理PR #6578](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6578) ／ [squash後Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0c98fec903366eae58722fdeeb5e2ae0ae81dca7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOrthogonalQuantitativeV5_PZ37AJB.lean)。

## 1．保存した元の物理対象

元の完全SU(2) Wilson one-slab作用、両端の空間halfweight、真正product-Haar確率測度、符号付きZW Gauss-law物理L²源 `f_{0,H}`、物理transfer `P_{H,β}`、その既存物理ノルム正規化 `N_{H,β}`、そして**既存の正規化transferの全top eigenspace**とその直交補空間を一切変更しない。Hilbert空間は有限体積Hごとに異なる。単一の選択top固有ベクトルへの直線射影と、全top固有空間への分解は同一視しない。

## 2．形式証明された定量的接続

各有限 `H∈ℕ` と各 `β>0` の**同一元物理Hilbert空間**で、元の正規化ZW源像には全top成分 `u_top` とその直交成分 `u_⊥` が存在して、

\[
N_{H,\beta}f_{0,H}=u_{\mathrm{top}}+u_\perp,\qquad
\|N_{H,\beta}f_{0,H}\|^2=\|u_{\mathrm{top}}\|^2+\|u_\perp\|^2.
\]

AJAの真正Haar-L²定量下界と接続し、元の正規化余裕 `m_{H,β}>0` と元の厳密負領域 `R_{H,β}` を用いて、

\[
\boxed{
0<m_{H,\beta}^2\,\operatorname{Measure.real}(\mu_H,R_{H,\beta})
\leq \|u_{\mathrm{top}}\|^2+\|u_\perp\|^2.
}
\]

これは**和**の下界であり、top成分または直交成分のどちらかに独立した正の下界があるとは主張しない。

さらに**条件付き**の定理として、実際に得られる任意のこの分解について

\[
\|u_{\mathrm{top}}\|^2<
m_{H,\beta}^2\,\operatorname{Measure.real}(\mu_H,R_{H,\beta})
\quad\Longrightarrow\quad u_\perp\ne0
\]

を証明した。左辺のtop成分が小さいこと自体は**今回のLean定理では証明していない**。元のZW源がtop固有空間の直交補に属するという仮定も追加していない。

## 3．既存の依存先と新規宣言

既存 `PeriodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceOrthogonalDecomposition` が、元の物理Hilbert空間での全top eigenspaceとその直交補空間の正確な直和分解を提供する。AJAは指定積分代表のHaar-a.e.接続から、元物理L²ノルム二乗に対する厳密正のH・β依存定量証明書を提供する。この2つを同じH・β・元作用素上で結合した。

新規Leanファイル：`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedSourceTopOrthogonalQuantitativeV5_PZ37AJB.lean`、158行追加・削除0、4定理・追加定義0。直接importは既存AJA、既存top-orthogonal decomposition、`Mathlib.Tactic` のみ。公理出力は全4定理に1件ずつ。

| 新規宣言 | 機械検証された対象 |
|---|---|
| `realHilbert_topOrthogonal_add_norm_sq` | 一般実Hilbert空間の直交二乗ノルム恒等式 |
| `p4Q2PZ37AJB_originalNormalizedSource_exists_top_orthogonal` | 元ZW正規化物理源像の全top/直交分解の存在 |
| `p4Q2PZ37AJB_originalNormalizedSource_quantitative_top_orthogonal_split` | 元AJAの正Haar-L²下界を直交二乗ノルム**和**へ接続 |
| `p4Q2PZ37AJB_originalNormalizedSource_orthogonal_ne_zero_of_top_small` | 実top成分の二乗ノルムが証明書より小さい場合の、直交成分非零性 |

すべての宣言には `MGAP4D.MathlibAnalytic` 名前空間（後ろ3件はその `GroundStatePosteriorJoint` 内）が付く。

## 4．初回失敗・修正版CI

初回source `ffbf7eef07ab87c1cdd0be0e7fb68c380d0fd432` の [CI #42612123173](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42612123173) は**FAILURE／未認証**。元の `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` の結論は `‖u+v‖*‖u+v‖=‖u‖*‖u‖+‖v‖*‖v‖` であり、目標の `‖u+v‖^2=‖u‖^2+‖v‖^2` とLeanの式が正規化されなかった。この失敗に続く回復用`sorryAx`は証明として扱わない。

既存の物理対象・新定理の型・仮定を変えず、定義上の二乗表現を `simpa only [pow_two]` で整合させた。最終認証sourceは `c776a9585b0082b63b0f834ccaacb60d97b57afe`。固定Lean `v4.30.0-rc2`／mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を保持し、新規ファイル全文・imports・旧分解定理署名・AJA証明書・固定mathlibの内積APIを確認した。

| 項目 | 最終Exact-source | 定理統合後push |
|---|---|---|
| CI | [#42613066943](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42613066943) | [#42613812145](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42613812145) |
| 判定 | completed / SUCCESS | completed / SUCCESS |
| HEAD | `c776a9585b0082b63b0f834ccaacb60d97b57afe` | `0c98fec903366eae58722fdeeb5e2ae0ae81dca7` |
| Lean依存閉包 | 11,416/11,416 | 11,416/11,416 |
| 新規実公理出力 | 4/4、標準3公理のみ | 4/4、標準3公理のみ |
| 新規warning/error・sorryAx | 0/0・なし | 0/0・なし |
| 独立completion receipt | SUCCESS | SUCCESS |

公理は `propext`、`Classical.choice`、`Quot.sound` のみ。独立receiptは実行結果の受領記録であって、別Lean kernelによる独立の再証明を意味しない。

## 5．Git同一性

| 対象 | SHA |
|---|---|
| AJA文書統合済み開始formal HEAD | `a3cd44eaaec3659554b8c70aa991823bbcc646cf` |
| 初回未認証AJB source | `ffbf7eef07ab87c1cdd0be0e7fb68c380d0fd432` |
| 最終認証source | `c776a9585b0082b63b0f834ccaacb60d97b57afe` |
| 定理squash | `0c98fec903366eae58722fdeeb5e2ae0ae81dca7` |
| source／squash同一Git tree | `96f9cccb415fcbffe90271f7ed7cca4515456426` |
| 新規Lean blob | `6ccf2f5479264e775d2025db176159770ff5cb43` |

定理PR #6578はMERGED。形式検証されたsourceとsquashのtreeおよび新規Leanのblobを照合した。文書専用PRでStrict Leanを手動実行しない。

## 6．障害と次研究（AJC候補）

**未証明:** 実際の元ZW正規化源像のtop成分が定量証明書より小さいこと、元ZW源そのもののtop直交性、直交成分の正の体積一様ノルム下限、全物理Hilbert coercivity、Hamiltonian spectral gap、非自明4D Yang–Mills連続体構成とmass gap。

次の研究候補AJCでは、既存の正値top固有ベクトル・top固有空間の射影・源の真の内積（top-overlap）を、同一H,βの物理Hilbert空間に直接接続する。必要な実上界がないなら**未認証障害として残す**。今回の全top eigenspace分解を任意の選択固有ベクトルへの一次元射影と同一視しない。固定physics／Lean pins、append-only／tighten-only／overwrite-forbidden／same-rootを維持する。
