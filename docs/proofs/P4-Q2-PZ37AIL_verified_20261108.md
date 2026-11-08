# P4-Q2-PZ37AIL — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW符号付き物理L²源と連続代表、真正空間積Haar、元のAIG全余裕と負領域、既存定理・仮定、固定Lean/mathlib、workflowを保持した。

## 1．検証済みソースと実際の統合

| 項目 | 確認した値 |
| --- | --- |
| 定理PR | [#6530](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6530)、MERGED |
| 基礎canonical formal HEAD | `b366ff2e12e8e1e32121ff60639247a58ea530a5` |
| Exact-source HEAD | `8f37083b9aece3b74f721c0f87b59387567993c6` |
| CIが実際に検査したtest-merge HEAD | `8174d396df4caf7ce80da9287b151dee834106e3` |
| 定理squash | `13ac117bee1ed4300a420c30049a1f7f7b221c7c` |
| source／test-merge／squash共通Git tree | `84ce4465925e02ccf38a01bb3398cff876198d3c` |
| source／squash共通Lean blob | `118e84c280cb0584a9390583a0f1e5e1126fbcde` |
| 変更範囲 | 新規Lean 1件・316行、19定理＋1定義、既存ファイル変更0、削除0 |
| [Exact-source CI #42486677149 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42486677149/attempts/1) | workflow completed／SUCCESS |
| 必須Lean job | `128749960527`、completed／SUCCESS |
| 必須Lean step 17 | Run changed Lean fast check、completed／SUCCESS |
| Lake依存閉包 | **11,400／11,400 SUCCESS** |
| 新規AIL leaf実ビルド | **14秒** |
| 公開宣言／print命令／実際のaxiom出力 | **20／20／20**、一対一一致 |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 公理依存 | 全20件が `propext`・`Classical.choice`・`Quot.sound` のみ |
| 完成した診断ログのsorryAx | **0件** |
| 変更AIL Lean warning／error | **0／0** |
| 独立completion receipt job | `128751332142`、completed／SUCCESS |
| receipt実出力 | `exact_sha=8f37083b9aece3b74f721c0f87b59387567993c6 source_result=success run=42486677149 attempt=1` |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| diagnostic artifact | `13620330505`、`lean-fast-check-log`、129858 bytes |
| archive SHA256（実取得bytesとGitHub metadata一致） | `666e82c6e59b55326885472f93003ac882c576f191d1093670528a2b65815d1b` |
| 展開したlean-fast.log | 1900110 bytes |
| 展開ログSHA256 | `4dc9ca85ce93b2d5acbdc8b95f5ea40a3c1b48e16fc3b1e4846fcc22abd24434` |

[検証済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/13ac117bee1ed4300a420c30049a1f7f7b221c7c/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitSmallCouplingFullNegativeRegionV5_PZ37AIL.lean)。直接importはPZ37AIKとMathlib.Tactic。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` を保持した。

今回は初回runで成功し、定理ソースの修正・再runは不要だった。workflow・job・必須Lean stepのcompleted／success、実際の20件の公理出力、独立receiptを確認した。診断artifactを取得し、archiveと展開ログのSHA256を再計算して記録した。変更ファイルの警告0は、再生された歴史的な依存ファイルの全警告が0という意味ではない。

独立担当は、記録文書の記述ではなく完成した実ジョブログから11,400件のビルド、20件の標準公理のみの出力、sorryAxなし、変更warning/errorなし、receipt成功を確認した。artifact本体のハッシュ照合とGit treeの三者比較は主担当が実施した。receiptは別CIジョブによる正確なsource SHAの結果記録であり、別の証明カーネルを意味しない。

新規ファイル全文と、直接使う既存の型付き署名、固定mathlibの確率測度APIを照合した。独立したソースレビューも実施した。CI checkoutログのtest-merge SHAを確認し、実squash後にGit tree・Lean blobを再取得して上表の一致を確認した。

## 2．適用範囲と記号

各 `H : ℕ` の既存の有限空間格子を対象とする。`p_H` はAFZの元のplaquette list長を実数へ埋め込んだ数、`n_H` は元の空間リンク型の `Nat.card` である。両者を新しい格子個数に置き換えない。

`V_H = p4Q2PZ37AHN_originalSource_HaarSecondMoment H`、`M_H = p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H` とする。`V_H` は真正源二次モーメント、`M_H` は同じ符号付きZW物理源の真正Haar L1質量である。[AIK] の初等式は

\[
v_H=\left(\frac{3p_H}{8}\right)^2(1/384)^{4n_H},
\qquad 0<v_H\le V_H.
\]

`T_H = decomposableOneSliceTransferIntegral H 2`、`f_{0,H} = p4Q2PZ37ZW_originalCenteredPhysicalDirection H` を保つ。以下の `T_beta(B)` は、この元の物理源に作用した `T_H beta f_{0,H} B` の略記である。

## 3．既存の作用上界と明示的な小結合区間

[AHI] の `p4Q2PZ37AHI_cardLinks_eq_plaquettes` は、元の空間リンク型の `Fintype.card` と `p_H` の等式を与える。[GlobalBudget] の実定義は

\[
C_H=2\bigl(\text{元plaquette list長}+\text{元link list長}\bigr).
\]

AILの `p4Q2PZ37AIL_originalGlobalActionBudget_eq_fourCount` は、したがって `C_H=4p_H` を証明する。新しい定義 `p4Q2PZ37AIL_elementarySmallCoupling` は

\[
\boxed{\tau_H=\frac{v_H}{16p_H^3+1}>0}.
\]

`p4Q2PZ37AIL_elementarySmallCoupling_eq_actionBudget` は、これが厳密に `v_H/(C_H^2 p_H+1)` と等しいことを示す。この区間端点に未評価の源・L1・分配積分は現れない。有限体積依存は保持する。

## 4．元の全境界に対する厳密な負値評価

[AHR] の `p4Q2PZ37AHR_originalTransfer_varianceOnly_bound` は、すべての `beta>=0` とすべての元の右境界 `B` について

\[
|T_\beta(B)+\beta V_H|\le E_H(\beta),
\qquad E_H(\beta)=\frac{(\beta C_H)^2}{2}M_H
\]

を証明している。一次係数は `-beta V_H` である。[AHJ] の元のL1上界 `M_H<=p_H/2` を適用して、AILは

\[
E_H(\beta)\le\frac{\beta^2 C_H^2p_H}{4}
\]

を示す。ここから **`0<beta<=tau_H`** なら

\[
\beta(C_H^2p_H+1)\le v_H,
\qquad \beta C_H^2p_H<v_H,
\]

\[
E_H(\beta)<\frac{\beta v_H}{4}\le\frac{\beta V_H}{4}.
\]

分母の `+1` と `beta>0` により、閉じた上端 `beta=tau_H` でも厳密な余裕がある。従って

\[
\boxed{\forall B,\quad T_\beta(B)<-\frac{3\beta V_H}{4}
\le-\frac{3\beta v_H}{4}<0.}
\]

これは元の完全Wilson核による物理transferの評価である。Taylor多項式と実transferの差は、同じ源とHaar測度の既証明誤差評価で制御される。

## 5．元の全余裕負領域が全空間に等しい

元の一リンクWilsonエネルギーが非負であることを使い、`beta>=0` で実際の一リンク分配積分 `Z1(beta)<=1` を証明する。[AIF] の正確な積表示から `Zcross_H(beta)<=1` を得る。

[AIG] の元の余裕は

\[
\varepsilon_H(\beta)=\frac{\beta}{2}
Z_{\mathrm{cross},H}(\beta)e^{-2\beta p_H}V_H.
\]

AILは、その定義を変更せず

\[
\varepsilon_H(\beta)\le\frac{\beta V_H}{2}
\]

を証明する。`0<beta<=tau_H` では、すべての元の境界について

\[
T_\beta(B)<-\frac{3\beta V_H}{4}
\le-\frac32\varepsilon_H(\beta)<-\varepsilon_H(\beta).
\]

従って、**同じAIG全余裕負領域**

\[
\mathcal N_{H,\beta}=\{B\mid T_\beta(B)<-\varepsilon_H(\beta)\}
\]

は `Set.univ` と等しい。元の正規化積Haar測度について

\[
\boxed{\mu_H(\mathcal N_{H,\beta})=1,
\qquad \mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})=1}
\]

を証明した。確率測度の全空間質量のAPIは固定mathlib [Probability] で照合した。

## 6．指定した恒等配置と符号の障害

[AHN] に既に定義されている `p4Q2PZ37AHN_identity H` は、元の各空間リンクにSU(2)の恒等元を置く配置である。全称境界定理へこれを代入し、指定された配置について元の三半余裕と初等的負振幅を得る。

同じ区間では

\[
\{B\mid 0\le T_\beta(B)\}=\varnothing.
\]

この区間内の正またはゼロのtransfer境界は、不可能と証明される。区間外に同じ結論を延長しない。`p4Q2PZ37AIL_explicitEndpoint_certificate` は、指定された正の端点 `tau_H` 自体について、全境界の三半余裕と元の全余裕領域のHaar質量1をまとめる。

## 7．保存と残る障害

AIKの任意の正結合に対する正のHaar質量下界は、そのまま保持される。AILの追加結論は、明示的なH依存区間 `0<beta<=tau_H` に限る。元の完全Wilson作用、両端halfweight、符号付きZW物理L²源、真正Haar、元の全余裕と負領域に変更はない。

任意結合での具体的な負中心、元の固定結合 `beta0` がこの区間に入ること、区間外の正境界や両符号領域、Hに一様な正結合区間・一様coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは未証明である。今回の質量1は、境界配置空間に対する元のHaar測度の主張である。

## 8．公開宣言の監査

すべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。共通prefixは `p4Q2PZ37AIL_`。19定理と1定義の全20件に、公理出力命令と実ログの出力が一対一で対応する。

| 宣言末尾 | 種別 |
| --- | --- |
| `originalSingleLinkPartition_le_one` | 定理 |
| `originalGlobalActionBudget_eq_fourCount` | 定理 |
| `elementarySmallCoupling` | 定義 |
| `elementarySmallCoupling_pos` | 定理 |
| `elementarySmallCoupling_eq_actionBudget` | 定理 |
| `originalQuadraticBudget_le_elementary` | 定理 |
| `originalQuadraticBudget_lt_quarterVarianceFloor` | 定理 |
| `originalTransfer_lt_negThreeQuarterVariance` | 定理 |
| `originalTransfer_lt_negThreeQuarterElementary` | 定理 |
| `originalCrossingPartition_le_one` | 定理 |
| `originalNegativeMargin_le_halfVariance` | 定理 |
| `originalTransfer_below_threeHalfMargin` | 定理 |
| `originalFullNegativeRegion_eq_univ` | 定理 |
| `originalFullNegativeRegion_measure_one` | 定理 |
| `originalFullNegativeRegion_realMeasure_one` | 定理 |
| `originalIdentityTransfer_below_threeHalfMargin` | 定理 |
| `originalIdentityTransfer_lt_elementary` | 定理 |
| `originalTransfer_negative` | 定理 |
| `originalNonnegativeRegion_eq_empty` | 定理 |
| `explicitEndpoint_certificate` | 定理 |

## 9．公開記録の扱い

本記録は定理のexact-source成功と実squashのtree・blob一致を確認してから、新規docs-only PRで追加する。mainへの文書ミラーには同じ記録Git blobを使う。既存README・ROADMAP・証明記録を上書きせず、文書専用PRではStrict Leanを手動dispatchしない。

[AIK]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalElementaryNegativeHaarFloorV5_PZ37AIK.lean
[AHI]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitRationalRobustSignV5_PZ37AHI.lean
[GlobalBudget]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic.lean
[AHR]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOneCrossingHaarOrthogonalityV5_PZ37AHR.lean
[AHJ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTrueHaarHalfSourceSignStabilityV5_PZ37AHJ.lean
[AIF]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean
[AIG]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean
[Probability]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean

[AHN]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/b366ff2e12e8e1e32121ff60639247a58ea530a5/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean

