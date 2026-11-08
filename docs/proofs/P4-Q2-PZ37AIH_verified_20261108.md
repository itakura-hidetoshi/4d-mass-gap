# P4-Q2-PZ37AIH — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW signed source、元空間積Haar、物理的transfer、証明履歴、固定Lean/mathlibとworkflowを保持する。

## 1．Exact-source形式証明台帳

| 項目 | 確定値 |
|---|---|
| [AIH定理PR #6517](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6517) | MERGED |
| 継承したcanonical formal HEAD | `88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7` |
| Exact-source HEAD | `37b799c13b6b2b86b1471f0188717755fd27663b` |
| CIがcheckoutしたtest-merge HEAD | `9ca5d1ca6353b09690355b463704261f1b98ee1a` |
| 定理squash／定理統合時formal HEAD | `d2ca52eaf35da603774a6664d74a688905bd35ab` |
| source・test-merge・squash共通Git tree | `0ce1f185f26fffa0a88b42925f9bec0be830204e` |
| 新規Lean Git blob | `6afcb3b1b16694f688bc9a11b9051067a0379d73` |
| 新規Leanファイル | **1件・365行、17定理＋2定義** |
| [Exact-source CI #42476531600 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42476531600/attempts/1) | completed／SUCCESS |
| Workflow／job | `PR Lean Fast Check`／`Changed Lean fast check` |
| Lean job | `128719019032`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lean依存閉包 | **11,396／11,396 SUCCESS** |
| AIH leafの実ビルド | **17秒** |
| 独立completion receipt job | `128720592936`、completed／SUCCESS |
| Receipt実ログ | `exact_sha=37b799c13b6b2b86b1471f0188717755fd27663b source_result=success run=42476531600 attempt=1` |
| Commit status context | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| 新規公開宣言の公理検証 | **19／19**、全件 `propext`・`Classical.choice`・`Quot.sound` のみ |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 成功ログのsorryAx | **なし** |
| 変更AIH Leanのwarning／error | **0／0** |
| Diagnostic artifact | `13615947107`、`lean-fast-check-log` |
| Artifact digest | `sha256:04815aee765a02666dc26bff5e0cb26aae85f527dbfb87989d530882d04becf2` |
| 抽出された実LeanログSHA256 | `b0ca87261711c0bd0abaa25731b7c0ecabee70185dee47c74d79962225a16cdb` |
| 既存Lean／物理定義／仮定／workflow変更 | なし |

Leanは `v4.30.0-rc2`、実行バイナリcommitは `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`。mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。canonical baseでtoolchain blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26` とmanifest blob `01260678b674ab241e753563e913c7ce9c6ba659` を再読した。既存の `maxHeartbeats 3900000` と `synthInstance.maxHeartbeats 1050000` を保持する。

最初のsource候補のattempt 1で成功した。sourceの修正、仮定の追加、定理文の弱化、heartbeat上限の引き上げは行っていない。

Workflow、Lean job、必須Lean stepの完了後に、完成job logおよびartifact中の実Leanログを検査した。ソースの19公開宣言・19件の `#print axioms`・実際の19公理出力を一対一で照合した。warning 0件は変更AIH leafの値であり、依存ファイルの再生された警告等を含むジョブ全体の値ではない。

別の独立監査でも、GitHub MCPからsource、workflow、jobs、receipt、artifact metadata、commit treeを再取得した。公開sourceと検査した全文のバイト一致、実ZIP digestとGitHub metadataの一致、ZIP内のログと検査ログのバイト一致、全19公理出力を確認した。receiptは完了通知の裏付けであり、Leanの証明検証の根拠は実際の完成ログと検証対象の一致である。

CIがコンパイルしたのはPR test-merge commitであり、source HEADそのもののcheckoutではない。test-mergeのparentsは上記canonical baseとexact sourceで、Git treeはsourceと同一。定理マージ後にも実際のsquash treeとLean blobをGitHub MCPで読み戻し、同一性を確認した。

独立した別担当がAIHの全365行と直接使用する依存定理・定義を確認し、意味・条件・対象の同一性に関するCritical／Important／Minorの指摘はなかった。完全kernel、符号付き物理sourceから連続代表への接続、一般結合の係数、元Haar球、全余裕と半余裕の区別を確認した。これは推移的な依存ライブラリ全証明の再監査ではない。別途、作用・kernel、半径・Haar、および本記録の数式・量化・参照を照合した。

[Lean4定理全文（検証済みsquash）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d2ca52eaf35da603774a6664d74a688905bd35ab/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllCouplingNegativeHaarBallV5_PZ37AIH.lean)

## 2．継承と変更範囲

AIG定理 #6514・正式記録 #6515・main文書同期 #6516 は再観測でMERGED。formal基点は `88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7`、main基点は `c1ae2058e4e6444936dd892800122569c05e4327`。

本記録が説明する形式成果物は、[上記365行の検証済みLean source][src-aih]である。新規Leanファイル1件のみ。元Wilson完全作用、両端空間halfweight、ZW physical L2 source、AFZ連続代表、元空間積Haar、固定Lean/mathlib、既存証明履歴、workflowは変更しない。

使用する記号と既存の対象は次のとおりである。結論に追加のH>0条件は置かない。

| 記号 | 元の対象 |
|---|---|
| $H\in\mathbb N$ | 元の有限体積パラメータ。 |
| $\mathrm{Link}_H$ | `PeriodicHypercubicEvenSpatialSliceLink H`。 |
| $\mathcal C_H$ | `PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2`。 |
| $\mu_H$ | `periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2`。元の規格化された空間積Haar確率測度。 |
| $f_{0,H}$ | `p4Q2PZ37ZW_originalCenteredPhysicalDirection H`。元の符号付き物理的L2 source。 |
| $f_H$ | `p4Q2PZ37AFZ_originalCenteredContinuous H`。既に証明された連続代表。 |
| $p_H$ | `p4Q2PZ37AFZ_plaquetteCount H`。元の空間plaquette listの長さを実数に写したもの。 |
| $M_H$ | `p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H`。元sourceのHaar L1質量。AHNにより連続代表の絶対値積分と等しい。 |
| $V_H$ | `p4Q2PZ37AHN_originalSource_HaarSecondMoment H`。元sourceのHaar二次モーメント、既証明の正の量。 |
| $Z_{\mathrm{cross},H}(\beta)$ | `p4Q2PZ37AIF_originalCrossingPartition H beta`。実際の交差Haar分配積分。 |
| $T_{H,\beta}f_{0,H}(B)$ | `decomposableOneSliceTransferIntegral H 2 beta f0 B`。元の完全な一スラブtransfer。 |
| $D_{\mathrm{sp},H}$ | `p4Q2PZ37AGG_originalSpatialChordalDistance H`。元の全空間リンク弦距離の和。 |

## 3．一般結合での元作用・kernel変動

元完全作用は

$$
S_H(A,B)=\frac12 W_H(A)+S_H^{\mathrm{cross}}(A,B)+\frac12 W_H(B).
$$

右境界の一つの元リンクをgからhへ置き換える。AEMの真正SU(2)弦距離評価から

$$
|\Delta S_H^{\mathrm{cross}}|\le d_J(g,h),\qquad
|\Delta W_H|\le24d_J(g,h).
$$

左halfweightの作用は差で厳密に相殺されるので

$$
|\Delta S_H|\le13d_J(g,h).
$$

両方の元作用が非負であり、任意のbeta>=0について既証明のスカラー不等式

$$
|e^{-\beta x}-e^{-\beta y}|\le\beta|x-y|\quad(x,y\ge0)
$$

が適用できる。したがって新しい小結合仮定を置かず、

$$
|K_{H,\beta}(A,B[e\mapsto g])-K_{H,\beta}(A,B[e\mapsto h])|
\le13\beta d_J(g,h).
$$

AGGの有限座標telescopingは同じ元リンク型・元距離に適用され、

$$
|K_{H,\beta}(A,B)-K_{H,\beta}(A,C)|
\le13\beta D_{\mathrm{sp},H}(B,C).
$$

[AEMの交差・スカラー評価][src-aem1]、[AEMの空間作用評価][src-aem2]、[AGGの有限座標評価][src-agg]を元の型へ適用した。係数13はこの証明で得た上界であり、最適性は主張しない。

係数13*betaはこのkernel変動評価ではHを含まない。一方、以下のsourceを積分したtransfer係数・負値幅・半径・Haar下界の体積一様性は主張しない。

## 4．符号付き元sourceの積分

元sourceの真正Haar L1質量を

$$
M_H=\int |f_{0,H}|\,d\mu_H
$$

とする。AHPは任意結合における元physical L2 transferとAFZ連続代表を使った積分の等式を証明している。AEVの符号付き積分変動評価を適用し、AHNのL1等式で元物理量へ戻す。係数の定義は全実数betaに対して置き、次の変動評価はbeta>=0の下で証明する。

$$
\Lambda_H(\beta):=13\beta M_H,\qquad
|T_{H,\beta}f_{0,H}(B)-T_{H,\beta}f_{0,H}(C)|
\le\Lambda_H(\beta)D_{\mathrm{sp},H}(B,C)
\quad(\beta\ge0).
$$

AHJのM_H<=p_H/2を接続して

$$
0\le\Lambda_H(\beta)\le\frac{13\beta p_H}{2}
\quad(\beta\ge0)
$$

を得る。元sourceの符号を捨ててtransferを定義し直す操作はない。絶対値は変動の上界にのみ現れる。

beta=0で係数は0。元のbeta0ではAHHの係数と定義上等しく、旧結果をそのまま回収する。[AHP][src-ahp]、[AEV][src-aev]、[AHN][src-ahn]、[AHJ][src-ahj]、[AHH][src-ahh]

## 5．一般正結合の負値安定球

AIGの元の余裕

$$
\varepsilon_{H,\beta}=
\frac{\beta Z_{\mathrm{cross},H}(\beta)e^{-2\beta p_H}V_H}{2}>0
\quad(\beta>0)
$$

と、その余裕を超えて負になる元境界$B_{H,\beta}$を各H・各betaごとに使用する。

$$
R_H(\beta):=\frac{\varepsilon_{H,\beta}}{2(\Lambda_H(\beta)+1)}>0.
$$

R>0と定義からLambda*R=epsilon/2-R<epsilon/2。そのため

$$
D_{\mathrm{sp},H}(B_{H,\beta},C)<R_H(\beta)
\Longrightarrow
T_{H,\beta}f_{0,H}(C)<-\frac{\varepsilon_{H,\beta}}2.
$$

量化順序は「各H、各beta>0に対し、あるBが存在する」であり、全結合に共通する一つの中心を主張しない。

任意の正余裕epsilonを入力とする安定性も先に独立に証明する。存在定理においてはその余裕と中心を仮定として残さず、AIGの元モデルの定理から供給する。

beta0の半径はAIGの旧半径と定義上等しい。ここで元の固定結合はbeta0=log(3/2)/64のままである。[AIG][src-aig]

## 6．真正Haar質量下界

n_H=Nat.card Link_Hとする。AHLの同じ元空間積Haarの球評価を使い、

$$
0<
\Phi_H(\beta):=
\kappa\left(\frac{R_H(\beta)}{n_H+1}\right)^{n_H}
\le\mu_H\bigl(\operatorname{Ball}_H(B_{H,\beta},R_H(\beta))\bigr).
$$

球の半余裕領域への包含と有限測度の単調性から、

$$
\Phi_H(\beta)
\le\mu_H\left\{C:T_{H,\beta}f_{0,H}(C)
<-\frac{\varepsilon_{H,\beta}}2\right\}.
$$

ここでkappaは既存のADQ関数であり、正確には

```lean
noncomputable def p4Q2PZ37ADQ_sphereRadiusFraction (r : ℝ) : ℝ :=
  ((Measure.toSphereBallBound 4 r : NNReal) : ℝ) / 4
```

を指す。これは球測度そのものとの等式を表す関数ではない。ADQの関数値の正性と、正半径を要求するAHLの球評価への適用条件を区別する。[ADQ][src-adq]、[AHL][src-ahl]

LeanではMeasure.realを使う。Fintype.card_eq_nat_cardによって有限型表示に依存するcardを消去し、新しいMeasure.piや別のHaar measureを構成しない。実数値測度の単調性には元の確率測度の有限性を用いる。[固定mathlibのcard変換][ml-finite]、[実数値測度][ml-real]

全余裕領域{T<-epsilon}はAIGで正測度。今回のこの明示球は半余裕領域{T<-epsilon/2}に入る。両領域を同一視せず、同じ球下界を全余裕領域へ移す主張はしない。

## 7．未解決の事項

- 正の元transfer境界の存在、および正負両符号のHaar領域・二殻。
- 具体的な元境界リンク配置、Haar表、符号判定の数値評価。
- Hに一様な負値幅、半径、Haar質量下界。
- betaに一様な正の半径やHaar質量下界。
- beta<0での今回と同じLipschitz評価、およびbeta<=0に対する厳密な負性・正測度。
- Uniform coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gap。

式で指定した係数・半径・下界と、実数値や境界配置の数値計算は区別する。

## 8．公開宣言19件と監査対応

すべての宣言は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 内にある。以下の各宣言につき、source中の `#print axioms` 1件と完成ログの公理出力1件を照合した。全行の出力は `[propext, Classical.choice, Quot.sound]` のみである。

| # | 宣言名 | 種別・条件・結論 |
|---:|---|---|
| 1 | `p4Q2PZ37AIH_originalOneSlabAction_rightOneLinkChordSlope` | 定理。任意の元境界・一リンクに対する完全作用の係数13。 |
| 2 | `p4Q2PZ37AIH_originalKernel_rightOneLinkChordSlope` | 定理。beta>=0、元の完全kernelの一リンク係数13*beta。 |
| 3 | `p4Q2PZ37AIH_originalKernel_rightAllLinkChordSlope` | 定理。beta>=0、全リンク距離での元kernel変動。 |
| 4 | `p4Q2PZ37AIH_transferSlope` | 定義。Lambda_H(beta)=(13*beta)*M_H。 |
| 5 | `p4Q2PZ37AIH_transferSlope_nonneg` | 定理。beta>=0でLambda>=0。 |
| 6 | `p4Q2PZ37AIH_transferSlope_le_halfCount` | 定理。beta>=0でLambda<=(13*beta)*(p_H/2)。 |
| 7 | `p4Q2PZ37AIH_transferSlope_zero` | 定理。Lambda_H(0)=0。 |
| 8 | `p4Q2PZ37AIH_transferSlope_fixedCoupling` | 定理。beta0でAHHの既存係数と定義上等しい。 |
| 9 | `p4Q2PZ37AIH_originalTransfer_allLinkSlope` | 定理。beta>=0、同じ物理的transferの全リンクLipschitz評価。 |
| 10 | `p4Q2PZ37AIH_originalTransfer_allLinkHalfCountSlope` | 定理。beta>=0、元plaquette数による係数上界。 |
| 11 | `p4Q2PZ37AIH_originalNegativeBallRadius` | 定義。R_H(beta,epsilon)=epsilon/[2*(Lambda+1)]。 |
| 12 | `p4Q2PZ37AIH_originalNegativeBallRadius_pos` | 定理。beta>=0、epsilon>0で半径が正。 |
| 13 | `p4Q2PZ37AIH_originalNegativeBallRadius_fixedCoupling` | 定理。beta0でAIGの既存半径と定義上等しい。 |
| 14 | `p4Q2PZ37AIH_originalNegativeBall_stable` | 定理。beta>=0、epsilon>0、T(B)<-epsilonから球内T(C)<-epsilon/2。 |
| 15 | `p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit` | 定理。beta>=0、epsilon>0、任意の中心で真正Haar球下界。 |
| 16 | `p4Q2PZ37AIH_originalNegativeBall_mass_pos` | 定理。同じ条件で球の実数値Haar質量が正。 |
| 17 | `p4Q2PZ37AIH_originalHalfNegativeRegion_mass_of_center` | 定理。負中心から半余裕領域の明示的Haar下界と正測度。 |
| 18 | `p4Q2PZ37AIH_originalTransfer_exists_negativeHaarBall` | 定理。各H・各beta>0で、AIGの余裕・負中心を供給し、正半径・球内半余裕負性・正の明示的Haar下界を結合。 |
| 19 | `p4Q2PZ37AIH_originalHalfNegativeRegion_mass_ge_explicit` | 定理。各H・各beta>0で、半余裕負領域に正の明示的Haar下界。 |

## 9．一次資料

AIHは検証済みsource commit、既存依存は今回再観測したcanonical baseに固定して参照する。説明文の流暢さやreceiptだけで形式証明の成否を認定せず、上記完成ログ・全宣言監査・対象同一性と区別する。

[src-aih]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/37b799c13b6b2b86b1471f0188717755fd27663b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllCouplingNegativeHaarBallV5_PZ37AIH.lean
[src-aem1]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOneLinkChordKernelModulusV5_PZ37AEM.lean
[src-aem2]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialChordKernelV5_PZ37AEM.lean
[src-agg]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialChordalCellOscillationV5_PZ37AGG.lean
[src-aev]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryTransferKernelSlopeV5_PZ37AEV.lean
[src-ahp]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstOrderHaarExpansionV5_PZ37AHP.lean
[src-ahn]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean
[src-ahj]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTrueHaarHalfSourceSignStabilityV5_PZ37AHJ.lean
[src-ahh]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH.lean
[src-aig]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean
[src-adq]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSphereHaarBridgeV5_PZ37ADQ.lean
[src-ahl]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88d29c0dae48def0cd9dfc170a6d6f8c18c5c1e7/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL.lean
[ml-finite]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/SetTheory/Cardinal/Finite.lean
[ml-real]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean
