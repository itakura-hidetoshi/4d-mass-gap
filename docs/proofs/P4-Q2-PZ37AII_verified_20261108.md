# P4-Q2-PZ37AII — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本は formal/real-hilbert-uniform-coercive-strong-limit。main は正式文書ミラー。運用は append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用と両端halfweight、ZW符号付き物理L²源、連続代表、空間積Haar、証明履歴、固定Lean/mathlib pin、workflowを保持した。

## 1．Exact-source証明・統合台帳

| 項目 | GitHub MCPで確認した値 |
| --- | --- |
| 定理PR | [#6521 — Full-margin Negative Haar Ball](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6521)、MERGED |
| 基礎canonical formal HEAD | 898b194263eb7b0ce042cab4122716dfa0010b9a |
| 検証済みsource HEAD | 0ca6128635619fa332a0944cfd7c3a2aed5a018f |
| exact-source test-merge HEAD | ce9e8782cb558213eedfa6c2318ad767d3a0f545 |
| 定理squash／統合時formal HEAD | 4cfe3caadfffc07cfb2ec98ad5bc83f86f459b9b |
| source／test-merge／squash共通Git tree | c6df48d623aee339cdae3790a01bb1087fc26362 |
| 新規Leanソースblob（統合後も同一） | c8765484ab7ada6f5485e75c1f2620bb0fdc45ff |
| [Exact-source CI #42479087966 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42479087966/attempts/1) | workflow completed／SUCCESS |
| 必須Lean job | 128726871647、completed／SUCCESS |
| 必須Lean step 17 | Run changed Lean fast check、completed／SUCCESS |
| Lean依存閉包 | **11,397／11,397 SUCCESS** |
| 変更AII leaf実ビルド | 29秒（元のheartbeat設定） |
| 新規Lean変更 | **1ファイル・259行・6定理**、既存ファイル変更0、削除0 |
| 新規宣言／print命令／実際のaxiom出力 | **6／6／6**、欠落・余剰・重複なし |
| 依存公理 | 全6件が propext・Classical.choice・Quot.sound のみ |
| sorryAx | 完成した公理出力に存在しない。Lean成功ログに回復sorryを認めない |
| 変更AII Lean warning／error | **0／0**（再生された他の依存ソース全体の警告0を意味しない） |
| 独立completion receipt job | 128728505425、completed／SUCCESS |
| Receipt実ログ | exact_sha=0ca6128635619fa332a0944cfd7c3a2aed5a018f source_result=success run=42479087966 attempt=1 |
| exact-head commit status | chatgpt-ci-receipt/PR Lean Fast Check、SUCCESS |
| 診断artifact | 13616412802、lean-fast-check-log |
| artifact GitHub SHA256 | 7429dc82f4f2bc9d88cf972143680d6ec76be7134f69419545663f8ba81958b3 |

AIIのsource Git tree、GitHub生成のtest-merge Git tree、および実際にsquash統合されたGit treeは一致する。squashの新規Lean blobは検証済みsourceと同一。run・必須job・必須Lean stepがcompleted／SUCCESSになった後に、実ジョブログの6宣言すべての公理表示、変更Lean error/warning、独立receipt、Git objectを照合した。新規定理は初回candidate・初回CI attemptで通過した。

Leanは v4.30.0-rc2、mathlibは 5450b53e5ddc75d46418fabb605edbf36bd0beb6。maxHeartbeats 3900000、synthInstance.maxHeartbeats 1050000を変更していない。CIにはtoolchain導入時間があったが、最終step17は成功しており、証明失敗と混同しない。

検証済み[Lean4ファイル全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/4cfe3caadfffc07cfb2ec98ad5bc83f86f459b9b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullMarginNegativeHaarBallV5_PZ37AII.lean)。

## 2．元の物理対象と数学的な前進

任意の有限体積 H∈ℕ、任意の正結合 β>0 に対し、元の完全Wilson一スラブ転送を

\[
t_{H,\beta}(B)
=\operatorname{decomposableOneSliceTransferIntegral}(H,2,\beta,f_{0,H},B)
\]

と記す。連続代表と元の物理L²源の積分同値はAHPの既証明橋渡しを使う。右境界は元の空間リンク上のSU(2)配置で、測度 \(\mu_H\) は元の正規化空間積Haar確率測度である。元の交差Haar分配積分 \(Z_H(\beta)>0\)、源分散 \(V_H>0\) と真の空間plaquette数 \(p_H\) を保持する。

AIGで既証明の負値余裕、重み付き平均および元の右境界重みの上界は

\[
\begin{gathered}
\varepsilon_{H,\beta}
=\frac{\beta Z_H(\beta)e^{-2\beta p_H}V_H}{2}>0,\qquad
D_{H,\beta}=\beta Z_H(\beta)e^{-\beta p_H}V_H>0,\\
\mathcal A_{H,\beta}
=\int e^{\beta W_H(B)/2}t_{H,\beta}(B)\,d\mu_H(B)
\le-D_{H,\beta},\\
\varepsilon_{H,\beta}e^{\beta p_H}=D_{H,\beta}/2,\qquad
e^{\beta W_H(B)/2}\le e^{\beta p_H}.
\end{gathered}
\]

この平均評価をさらに使用し、すべての右境界で \(t(B)\ge-3\varepsilon/2\) と仮定すると、正の重みに関する単調性と確率測度上の積分により

\[
-\tfrac34 D_{H,\beta}\le\mathcal A_{H,\beta}\le-D_{H,\beta}
\]

となり \(D_{H,\beta}>0\) に反する。したがって、**同じ元の物理転送**について

\[
\boxed{\exists B_H:\ t_{H,\beta}(B_H)<-3\varepsilon_{H,\beta}/2}
\]

が得られる。追加の正のtransfer点・full support・非零源の新仮定は不要。

AIHで証明済みの元の全リンクChordal距離と真のsource Haar L¹質量 \(M_{\mathrm{src},H}\) を用いると、

\[
\left|t_{H,\beta}(B)-t_{H,\beta}(C)\right|
\le\Lambda_H(\beta)D_{\mathrm{sp},H}(B,C),\qquad
\Lambda_H(\beta)=13\beta M_{\mathrm{src},H}\ge0
\]

である。AIIでは既存のAIH定義の半径

\[
R_H(\beta)=\frac{\varepsilon_{H,\beta}}{2(\Lambda_H(\beta)+1)}>0
\]

を**変更せず**利用する。\(\Lambda_H R_H<\varepsilon/2\) と上の強い負値中心から、元の球

\[
\operatorname{Ball}_H(B_H,R_H)
=\{C:D_{\mathrm{sp},H}(B_H,C)<R_H\}
\]

のすべての点で

\[
\boxed{t_{H,\beta}(C)<-\varepsilon_{H,\beta}}
\]

となる。AIHまでの半余裕 \(-\varepsilon/2\) ではなく、AIGが定義した**全余裕負領域そのもの**へ球が包含される。

\(n_H=\operatorname{Nat.card}(\mathrm{Link}_H)\)、\(\kappa\) は既存ADQの正の半径函数とする。AHLの**真正SU(2)空間積Haar球**の下界を適用すると、

\[
\boxed{
0<
\kappa\!\left(\frac{R_H(\beta)}{n_H+1}\right)^{n_H}
\le
\mu_H^{\mathrm{real}}\!
\left(\{C:t_{H,\beta}(C)<-\varepsilon_{H,\beta}\}\right).
}
\]

これはAIGの全余裕領域の単なる正測度を、明示的な球半径に基づく下界へ強化する。固定結合 \(\beta_0=\log(3/2)/64\) ではAIHのradiusとAIGの既存radiusは定義上等しい。

## 3．Lean新規宣言6件の対応

| 宣言末尾 | 型付き結論 |
| --- | --- |
| originalTransfer_exists_below_threeHalfMargin | 正結合で \(t(B)<-3\varepsilon/2\) の元境界が存在 |
| originalFullNegativeBall_stable | 非負結合、強い中心と正余裕から全余裕球への包含 |
| originalFullNegativeRegion_mass_of_center | 元のHaar球から全余裕負領域へ正の質量下界を移す |
| originalTransfer_exists_fullNegativeHaarBall | 正結合で中心・正半径・全余裕負性・真正Haar球と負領域の下界を同時構成 |
| originalFullNegativeRegion_mass_ge_explicit | 任意の正結合で元の全余裕負領域の明示的な厳密正下界 |
| originalFixedFullNegativeRegion_mass_ge_explicit | 固定元結合 \(\beta_0\) の同じ下界、AIG radiusに厳密整合 |

すべての宣言は MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint の名前空間にあり、6個の #print axioms と実際のログ6個を一対一に照合している。

## 4．依存証拠と未解決障害

直接importはPZ37AIH。AIGから負値余裕・元transfer重み・負平均、AEMから元作用と核の指数評価、AIHから全結合Lipschitz係数・半径、AHLとADQから元の正規化空間積Haar球の下界を継承する。**Preference ⇏ Descent ⇏ Authority**に従い、元の局所評価を使っているというだけで体積一様性・無限体積・連続体へ拡張しない。

未証明のまま残すものは、正のtransfer値を持つ境界、正負両符号の元Haar領域と二殻、具体的な境界リンク配置・数値符号表、体積Hに一様な余裕・半径・Haar下界、uniform coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gap。\(\kappa\)、\(M_{\mathrm{src},H}\)、\(Z_H\)、\(V_H\) の厳密な形式式は数値評価済みの定数を意味しない。

正式証明記録は定理のexact-source成功とsquash一致の後に独立したdocs-only PRで追加する。既存のLean、物理定義、仮定、workflowは変更しない。mainへはこの正式記録の内容と同一Git blobをミラーし、文書専用PRでStrict Leanを手動dispatchしない。

---
定理正本：[PR #6521](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6521)／[CI #42479087966](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42479087966)。
