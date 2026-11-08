# P4-Q2-PZ37AIK — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW符号付き物理L²源と連続代表、真正空間積Haar、既存定理・仮定、固定Lean/mathlib、workflowを保持した。

## 1．検証済みソースと実際の統合

| 項目 | 確認した値 |
| --- | --- |
| 定理PR | [#6527](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6527)、MERGED |
| 基礎canonical formal HEAD | `c250fb7a9211fd7fe9f2ed9355174fc69b544973` |
| 修正後exact-source HEAD | `18130a796198b6b8400ba9bd1efc1ab99e04db0f` |
| CIが実際に検査したtest-merge HEAD | `adf840da71f110baad1da289f063cfbab5ad4b56` |
| 定理squash | `3efbd6a356bc67351ff634f9a42b39028cef1e0f` |
| source／test-merge／squash共通Git tree | `dd19c4c3d4439d5c929d3bab8dbfde3a79559f76` |
| source／squash共通Lean blob | `bd585ac8c613f787935a450f4abf85bb1a904477` |
| 変更範囲 | 新規Lean 1件・324行、26定理＋4定義、既存ファイル変更0、削除0 |
| [Exact-source CI #42484562354 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42484562354/attempts/1) | workflow completed／SUCCESS |
| 必須Lean job | `128743485309`、completed／SUCCESS |
| 必須Lean step 17 | Run changed Lean fast check、completed／SUCCESS |
| Lake依存閉包 | **11,399／11,399 SUCCESS** |
| 新規AIK leaf実ビルド | **24秒** |
| 公開宣言／print命令／実際のaxiom出力 | **30／30／30**、一対一一致 |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 公理依存 | 全30件が `propext`・`Classical.choice`・`Quot.sound` のみ |
| 完成した診断ログのsorryAx | **0件** |
| 変更AIK Lean warning／error | **0／0** |
| 独立completion receipt job | `128744843152`、completed／SUCCESS |
| receipt実出力 | `exact_sha=18130a796198b6b8400ba9bd1efc1ab99e04db0f source_result=success run=42484562354 attempt=1` |
| exact-head commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| diagnostic artifact | `13618752493`、`lean-fast-check-log`、127522 bytes |
| archive SHA256（実取得bytesとGitHub metadata一致） | `dea2162181917edee19247c3700f17f4b468ea77b38141ca7ab7cfa567d77ac8` |
| 展開したlean-fast.log | 1888306 bytes |
| 展開ログSHA256 | `10343efec5ca1e4d5865ab702f63d409914a0c846736aa4796be7244eced5e69` |

[検証済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3efbd6a356bc67351ff634f9a42b39028cef1e0f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalElementaryNegativeHaarFloorV5_PZ37AIK.lean)。直接importはPZ37AIJとMathlib.Tactic。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` を保持した。

workflow・job・必須Lean stepの完了後に実際の診断artifactを取得し、archiveと展開ログのSHA256を再計算した。30宣言と30公理出力の名前を全件突合し、欠落・余剰・重複・非標準公理・sorryAx・変更Leanのwarning/errorを検査した。変更ファイルの警告0は、再生された依存ファイルの全ログが警告0という意味ではない。

独立receiptは、元Leanジョブの終了を受けてexact-source結果を記録する別CIジョブである。これは別の証明カーネルによる再検証や人間の査読を意味しない。新規ファイル全文、直接使う依存署名、固定mathlibの定義・型変換APIを照合し、別担当のソースレビューも実施した。歴史的な全推移依存定理を別途全面監査したとは主張しない。

CIログ内のcheckout SHAを確認し、sourceとtest-mergeのGit treeを取得した。実際のsquash後にもtreeとLean blobを再取得し、上表の一致を確認した。

## 2．初回失敗と型変換の修正履歴

初回source `8ea47f134254cc885219714425e81fd827f8654f` の [CI #42484064193 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42484064193/attempts/1) はcompleted／FAILURE。正半径での等式を示す58行付近に1件の直接Leanエラーがあり、`ring` の目標に未処理の係数 `↑4` が残った。変更Lean warningは0。失敗箇所と下流の公理診断には25件の `sorryAx` が現れ、このrunは認証に使用していない。

構造的原因は、`toSphereBallBound` の次元係数が自然数からNNReal、さらにRealへと変換されることだった。`NNReal.coe_ofNat` は数値リテラルに対応するが、この自然数キャストの正規化は別のAPIである。固定版 [NNReal/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/NNReal/Defs.lean) を読み、`NNReal.coe_natCast` を既存の `simp only` リストへ1件追加した。

定理の文、仮定、定義、元の物理対象、import、heartbeat、workflowは変更していない。修正後の新runで全30公理出力から `sorryAx` が消え、全依存閉包が成功した。初期PR本文は残し、失敗と修正を追記した。

初回診断も実取得して保持した。artifact `13618792614` は128306 bytes、archive SHA256は `aaff0fbfc326e8714ab19c030f5689096d8bfb21960b50e98261c57a6582672e`。展開ログは1891103 bytes、SHA256は `6db1e7439da0e1043006c26ee61ae31c9a4f40b1d4aad9144bddab121b9f7844` である。

## 3．適用範囲と固定した定義

対象は各 `H : ℕ` の既存の有限空間格子と、実結合定数 `β > 0` である。
Lean は `4.30.0-rc2`、mathlib は `5450b53e5ddc75d46418fabb605edbf36bd0beb6` に固定する。
参照する既存成果物の基点は `c250fb7a9211fd7fe9f2ed9355174fc69b544973` である。
以下の測度不等式は、Lean の `Measure.real` による実数値の比較として読む。

`κ = p4Q2PZ37ADQ_sphereRadiusFraction` の定義は、[ADQ] のとおり
\[
\kappa(r)=\frac{\operatorname{toSphereBallBound}(4,r)}4
\]
である。固定した [mathlib] の `MeasureTheory.Measure.toSphereBallBound` は
\[
b(n,r)=\begin{cases}n\bigl(\min(\operatorname{toNNReal}(r),2)/4\bigr)^n,&n\ne0\land r>0,\\1,&\text{それ以外}\end{cases}
\]
と定義される。ここで `b` の値域は `ℝ≥0` であり、`κ` では `ℝ` に埋め込む。

## 4．半径証明定数の正確な評価

正半径では `Real.coe_toNNReal r hr.le` により実数へ戻し、次の等式を得る。
\[
r>0\Longrightarrow\kappa(r)=\left(\frac{\min(r,2)}4\right)^4,
\qquad 0<r\le2\Longrightarrow\kappa(r)=\left(\frac r4\right)^4.
\]
非正半径では別の分岐が選ばれ、`r ≤ 0` なら `κ(r)=1/4` となる。
この値は定義の代替値であり、非正半径の球の Haar 質量下界としては使用しない。
したがって実数全域の単調性は成り立たない。AIK の証明経路は単調性を使わない。
恒等元近傍に使う半径では、正確な有理数演算により
\[
\kappa(1/96)=(1/384)^4=1/21743271936
\]
となる。対応する API は `MGAP4D.MathlibAnalytic` に属する。

- `p4Q2PZ37AIK_sphereRadiusFraction_eq`、`p4Q2PZ37AIK_sphereRadiusFraction_of_nonpos`
- `p4Q2PZ37AIK_sphereRadiusFraction_eq_quartic`、`p4Q2PZ37AIK_sphereRadiusFraction_pow`
- `p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius`、`p4Q2PZ37AIK_sphereRadiusFraction_at_identityRadius_rational`

## 5．元の積 Haar 測度への接続

[ADZ] の元の正規化 `SU(2)` Haar 測度と chordal 球に対する下界を、そのまま評価する。
`p4Q2PZ37AIK_originalOneLinkBall_mass_ge_elementary` は、全中心 `a`、`r>0` に対して
\[
\left(\min(r,2)/4\right)^4\le\mu_{SU(2)}(B_{\mathrm{chordal}}(a,r))
\]
を述べる。[AHL] の積球定理へ同じ評価を適用すると、全中心 `B`、`R>0` について
\[
\left(\frac{\min(R/(n_H+1),2)}4\right)^{4n_H}\le\mu_H(\operatorname{Ball}_H(B,R)).
\]
以下の有限体積 API はすべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。
この積球下界は `p4Q2PZ37AIK_originalSpatialBall_mass_ge_elementary` である。
`μ_H` と `Ball_H` は既存の積 Haar 測度と `p4Q2PZ37AHL_originalSpatialBall` を保つ。

## 6．既存の個数と AIJ の量を保った初等式

`n_H = Nat.card (PeriodicHypercubicEvenSpatialSliceLink H)` とする。
`p_H = p4Q2PZ37AFZ_plaquetteCount H` は既存の定義を保ち、別の格子個数に置き換えない。
数式中では必要な自然数の実数への埋め込みを省略する。AIK の四つの定義は
\[
v_H=\left(\frac{3p_H}8\right)^2(1/384)^{4n_H},\qquad
\delta_H(\beta)=\frac{\beta e^{-2\beta(n_H+p_H)}v_H}{2},
\]
\[
r_H(\beta)=\frac{\delta_H(\beta)}{13\beta p_H+2},\qquad
m_H(\beta)=\left(\frac{\min(r_H(\beta)/(n_H+1),2)}4\right)^{4n_H}.
\]

| 記号 | AIK 定義名 | AIJ との関係 |
|---|---|---|
| `v_H` | `p4Q2PZ37AIK_elementarySourceVarianceFloor` | `p4Q2PZ37AIJ_sourceVarianceFloor H` と等しい |
| `δ_H` | `p4Q2PZ37AIK_elementaryNegativeMargin` | `p4Q2PZ37AIJ_primitiveNegativeMargin H` と等しい |
| `r_H` | `p4Q2PZ37AIK_elementaryNegativeBallRadius` | `p4Q2PZ37AIJ_primitiveNegativeBallRadius H` と等しい |
| `m_H` | `p4Q2PZ37AIK_elementaryNegativeHaarFloor` | `β>0` で `κ(r_H(β)/(n_H+1))^n_H` と等しい |

各定義名に `_eq` を付けた定理がこれらの等式を担う。最初の三等式に `β>0` の仮定は不要である。
[AIJ] から `0<v_H≤Vsrc_H`、`β≥0` で `δ_H(β)≤ε_H(β)`、`δ_H(0)=0` を引き継ぐ。
ここで `Vsrc_H` は `p4Q2PZ37AHN_originalSource_HaarSecondMoment H`、`ε_H` は `p4Q2PZ37AIG_originalNegativeTransferMargin H` である。
`β>0` では `δ_H(β)>0`、`r_H(β)>0`、`m_H(β)>0` が成立する。

## 7．同じ AIG 全余裕負領域への下界

`T_H=decomposableOneSliceTransferIntegral H 2`、`f_{0,H}=p4Q2PZ37ZW_originalCenteredPhysicalDirection H` とする。
元の領域 `N_H(β)=p4Q2PZ37AIG_originalNegativeTransferRegion H β` は
\[
N_H(\beta)=\{C\mid T_H(\beta,f_{0,H},C)<-\varepsilon_H(\beta)\}
\]
である。既存の AII の存在定理は `T_H(β,f_{0,H},B)<-3ε_H(β)/2` を満たす中心 `B` を与える。
AIJ の半径比較と安定性を等式で引き継ぎ、`Ball_H(B,r_H(β)) ⊆ N_H(β)` を保つ。
`p4Q2PZ37AIK_originalTransfer_exists_elementaryNegativeHaarBall` は、この中心の存在・正半径・全余裕安定性・正質量下界をまとめる。
`p4Q2PZ37AIK_originalFullNegativeRegion_elementaryMass` の主張は、各 `H` と `β>0` に対する
\[
0<m_H(\beta)\le\mu_H(N_H(\beta))
\]
である。`δ_H≤ε_H` による大きい領域 `{C | T_H(β,f_{0,H},C)<-δ_H(β)}` の下界は、別定理 `p4Q2PZ37AIK_elementaryNegativeRegion_mass` で保持する。
`p4Q2PZ37AIK_originalFullNegativeRegion_combinedMass` は既存 AII 下界との最大値も保持し、両下界間の大小関係を仮定しない。

## 8．解消した障害と残る範囲

解消した障害は `κ` の未評価部分である。AIJ の同じ定数を、有理数・有限冪・指数関数・`min` の式へ厳密に評価する。
四次式は保守的な証明用下界であり、正規化 Haar 球の厳密な質量や最適な小半径評価を与えるものではない。
半径の飽和 `min(·,2)` を残し、新たな小半径仮定、球冠体積公式、符号仮定を追加しない。
元の Wilson 核、両側の空間半重み、符号付きの ZW 物理的 `L²` 源、元の Haar 測度と全余裕領域を保つ。
中心は存在量化のままであり、具体的な配置の評価は未解決である。正の転送値を持つ境界や両符号領域の構成も、この評価からは得られない。
`n_H,p_H` への依存は残る。体積一様な強圧性、Hamiltonian gap、連続体 mass gap への移行は別の未解決課題である。

## 9．30公開宣言の監査対象

共通prefixは `p4Q2PZ37AIK_`。最初の7件は `MGAP4D.MathlibAnalytic`、残りはその下の `GroundStatePosteriorJoint` 名前空間に属する。各宣言の `#print axioms` は実ログに一対一で存在し、全30件が標準3公理のみである。

| 宣言末尾 | 種別 |
| --- | --- |
| `sphereRadiusFraction_eq` | 定理 |
| `sphereRadiusFraction_of_nonpos` | 定理 |
| `sphereRadiusFraction_eq_quartic` | 定理 |
| `sphereRadiusFraction_at_identityRadius` | 定理 |
| `sphereRadiusFraction_at_identityRadius_rational` | 定理 |
| `sphereRadiusFraction_pow` | 定理 |
| `originalOneLinkBall_mass_ge_elementary` | 定理 |
| `originalSpatialBall_mass_ge_elementary` | 定理 |
| `elementarySourceVarianceFloor` | 定義 |
| `elementarySourceVarianceFloor_eq` | 定理 |
| `elementarySourceVarianceFloor_pos` | 定理 |
| `elementarySourceVarianceFloor_le_original` | 定理 |
| `elementaryNegativeMargin` | 定義 |
| `elementaryNegativeMargin_eq` | 定理 |
| `elementaryNegativeMargin_pos` | 定理 |
| `elementaryNegativeMargin_zero` | 定理 |
| `elementaryNegativeMargin_le_original` | 定理 |
| `elementaryNegativeBallRadius` | 定義 |
| `elementaryNegativeBallRadius_eq` | 定理 |
| `elementaryNegativeBallRadius_pos` | 定理 |
| `elementaryNegativeBallRadius_le_original` | 定理 |
| `elementaryNegativeHaarFloor` | 定義 |
| `elementaryNegativeHaarFloor_eq` | 定理 |
| `elementaryNegativeHaarFloor_pos` | 定理 |
| `elementaryNegativeBall_fullMargin_stable` | 定理 |
| `elementaryNegativeBall_mass_ge` | 定理 |
| `originalTransfer_exists_elementaryNegativeHaarBall` | 定理 |
| `originalFullNegativeRegion_elementaryMass` | 定理 |
| `elementaryNegativeRegion_mass` | 定理 |
| `originalFullNegativeRegion_combinedMass` | 定理 |

## 10．公開記録の扱い

本記録は定理のexact-source成功と実squashのtree・blob一致を確認してから、新規のdocs-only PRで追加する。mainへの文書ミラーには同じ記録Git blobを使う。既存のREADME・ROADMAP・証明記録を上書きせず、文書専用PRではStrict Leanを手動dispatchしない。

[ADQ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c250fb7a9211fd7fe9f2ed9355174fc69b544973/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSphereHaarBridgeV5_PZ37ADQ.lean
[ADZ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c250fb7a9211fd7fe9f2ed9355174fc69b544973/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnconditionalHaarRadiusV5_PZ37ADZ.lean
[AHL]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c250fb7a9211fd7fe9f2ed9355174fc69b544973/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL.lean
[AIJ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c250fb7a9211fd7fe9f2ed9355174fc69b544973/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimitiveNegativeHaarFloorV5_PZ37AIJ.lean
[mathlib]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean
