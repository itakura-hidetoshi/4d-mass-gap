# P4-Q2-PZ37AIW — 真正空間平均による正規化相対評価と元の負領域

2026年11月9日 JST。[定理PR #6563](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6563)はMERGED。全有限H・β≥0における元の物理ノルム下界の改善と、元の源・余裕を既存物理ノルムで正規化した相対評価を形式証明した。体積極限と余裕の厳密正値性にはβ>0を用いる。認証は以下の対象と量化の範囲に限る。

[統合済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/bd7357e21e0ab24de11d7f957d0000e503f95851/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSpatialMeanNormalizationV5_PZ37AIW.lean)。説明文はこの形式成果物の内容を記録し、文章自体を追加の証明根拠とはしない。

## 1. 対象と正本

定理正本は `itakura-hidetoshi/4d-mass-gap` の `formal/real-hilbert-uniform-coercive-strong-limit`。main は正式記録の同一 blob ミラーである。

元の完全 SU(2) Wilson 作用、両端の空間 halfweight、真正の正規化 Haar、符号付き ZW 物理 L² 源、AIG の元の余裕と厳密負領域を保持する。既存の仮定・証明・公開 root・固定環境・workflow を変更しない。

以下の有限体積評価は H∈ℕ・β≥0 のもとで述べる。有限 H ごとに元の配置空間を Cfg_H、Haar 確率を μ_H、元の空間作用を W_H、crossing kernel を K_C、完全 one-slab kernel を K、既存 Gauss-law 物理 transfer を P とする。体積極限と余裕の厳密正値性には固定した β>0 を用いる。

\[
p_H=24(H+1)^3,\qquad
Z_H(\beta)=Z_{\mathrm{cross},H}(\beta),\qquad
\lambda_H(\beta)=\|P_{H,\beta}\|>0.
\]

以下の Q は説明用の記号であり、新しい物理モデルの定義ではない。

\[
Q_H(\beta)=\int_{\mathrm{Cfg}_H\times\mathrm{Cfg}_H}
 K_{H,\beta}(A,B)\,d(\mu_H\otimes\mu_H)(A,B).
\]

Q は両端 halfweight を含む、**元の完全 one-slab・自由境界の pair-Haar 積分**である。周期時間方向の trace 分配関数とも、物理ノルム λ とも同一視しない。

## 2. 真正の空間平均による物理ノルム下界の改善

AFZ の物理平均から Haar 積分への橋と AGN の厳密平均から、元の作用に

\[
\int W_H\,d\mu_H=p_H
\]

を得る。AIF の右 crossing Haar 恒等式と AIU の左 Haar 恒等式を別々に適用し、積分可能性を先に満たしてから Fubini を用いる。

\[
\int W_H(A)K_C(A,B)\,d\mu_H^2
=\int W_H(B)K_C(A,B)\,d\mu_H^2
=p_H Z_H(\beta).
\]

これは両端の独立性を仮定したものではない。元の crossing kernel の両 Haar 周辺積分を使った恒等式である。

指数関数の接線不等式 1+x≤exp(x) に

\[
x=\beta p_H-\frac{\beta}{2}(W_H(A)+W_H(B))
\]

を代入し、exp(-βp_H)K_C を掛ける。右辺は元の二つの halfweight を含む完全 K に一致する。上の二つの厳密平均で一次項を積分すると相殺され、

\[
e^{-\beta p_H}Z_H(\beta)\le Q_H(\beta)
\]

となる。既存の物理定数単位ベクトル u_H を用い、Q_H=⟨P u_H,u_H⟩ を元の kernel pairing と結ぶ。Cauchy–Schwarz と作用素ノルム評価、AIV の上界から、**全有限 H・β≥0**に

\[
\boxed{e^{-\beta p_H}Z_H(\beta)
\le Q_H(\beta)\le\lambda_H(\beta)\le Z_H(\beta).}
\]

AIV の exp(-2βp_H)Z_H 下界を、元の条件を維持して exp(-βp_H)Z_H へ強めた。

## 3. 既存の正規化尺度との相対評価

正の真正 Z_H と正の物理ノルム λ_H で割り、

\[
e^{-\beta p_H}\le\frac{\lambda_H}{Z_H}\le1,
\qquad
1\le\frac{Z_H}{\lambda_H}\le e^{\beta p_H}
\]

を得る。AIU の元の率 ρ(β)=-log z(β)、Z_H=exp(-ρp_H) と結合すると、既存の逆ノルム正規化尺度は

\[
\boxed{e^{\rho(\beta)p_H}\le\lambda_H(\beta)^{-1}
\le e^{(\beta+\rho(\beta))p_H}.}
\]

右端は AIV の 2β+ρ から β+ρ への改善である。λ_H と Z_H の漸近同値や、物理ノルムの正確な指数率は導かない。

## 4. 元の源と既存正規化作用素の接続

新しい scalar function として

\[
\widehat T_{H,\beta}f_{0,H}(B)
=\frac{T_{H,\beta}f_{0,H}(B)}{\lambda_H(\beta)}
\]

を表記する。これは代替作用素ではない。既存の正規化物理作用素 N=P/‖P‖ の出力 L² class とこの積分関数が、真正 Haar に関してほとんど至る所で一致することを証明した。橋は任意の既存物理入力に対して構成し、元の ZW 源へ特殊化する。

ambient transfer の元の積分代表、Gauss-law 物理制限の coercion、`Lp.coeFn_smul` を明示する。L² class の任意代表に点ごとの等式を与えず、連続性と点ごとの符号はこの指定積分代表に対して述べる。

全境界に対する正直な上界も保持する。

\[
|\widehat T f_0(B)|\le\frac{p_H}{2}\frac{Z_H}{\lambda_H}
\le\frac{p_H}{2}e^{\beta p_H}.
\]

この上界は体積とともに増大し得るため、正規化後の実際の源像の減衰には使用しない。

## 5. 元の負領域を保つ正規化余裕

元の source Haar 二次モーメントを V_H とすると、AIG の余裕は変更せず

\[
\delta_H(\beta)=\frac{\beta V_H}{2}
 Z_H(\beta)e^{-2\beta p_H}.
\]

既存の物理正規化と同じ λ_H で割った scalar certificate を m_H=δ_H/λ_H とする。これは元の余裕を弱めて別の領域を作る操作ではない。

\[
\boxed{
\frac{\beta V_H}{2}e^{-2\beta p_H}
\le m_H(\beta)
\le\frac{\beta V_H}{2}e^{-\beta p_H}
\le\frac{\beta}{8}p_H^2e^{-\beta p_H}.}
\]

V_H≤p_H²/4 は既存の source moment 評価である。全有限 H・β>0 で m_H>0、**固定した β>0**に対して H→∞ で m_H→0。H に依存する配置空間や Hilbert 空間を同一視しない。

正の λ_H による除算で、厳密負領域は集合として正確に一致する。

\[
\boxed{\{B:\widehat T f_0(B)<-m_H\}
=\{B:T f_0(B)<-\delta_H\}.}
\]

したがって AIT の元の半-Haar 領域、0<m_H<η、既存正規化作用素の ‖N‖=1 は、任意の固定 β>0・η>0 に対し一つの共通 cutoff 以降で同時に成立する。

元の固定結合 β₀=log(3/2)/64 では、β₀≥1/192 と厳密 p_H の式を用い、

\[
\boxed{m_H(\beta_0)\le72\beta_0(H+1)^6
 e^{-(H+1)^3/8}.}
\]

## 6. この段階で未証明の事項

消失するのは **元の AIG 証明書を既存物理ノルムで正規化した余裕**である。実際の正規化源像が0へ近づくこと、より深い負領域が存在しないこと、正規化 coercivity の不可能性を意味しない。

正規化後の実際の源像の振幅・相対スペクトル、共通 Hilbert 空間上の極限、励起 gap、各固定有限 H で任意正結合における元の全余裕半-Haar 下界、Hamiltonian spectral gap、連続体4次元 Yang–Mills mass gap は別の未証明課題として残す。源像の負値を負固有値へ昇格させない。

次段 AIX の研究候補は、元の正規化源像または励起 sector の真正相対評価。今回の certificate-scale の結果と作用素 norm=1 だけから spectral 結論を補わない。


## 7. 形式成果物の宣言索引

| 種類 | 宣言 |
|---|---|
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalSpatialWilsonAction_haarMean` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_leftAction_pair_integrable` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_rightAction_pair_integrable` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_leftAction_pair_integral` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossing_rightAction_pair_integral` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_ge_spatialMeanTangent` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_ge_spatialMean` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_eq_constantExpectation` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFullKernel_pair_integral_le_physicalTransferNorm` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean` |
| def | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer` |
| def | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_coeFn` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_existingNormalizedPhysicalTransfer_coeFn` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_coeFn` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_continuous` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_neg_iff` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_lt_negativeMargin_iff` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNorm_div_crossingPartition_bounds` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_improvedRate` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalInverseNormalization_bounds` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_relativeEnvelope` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_spatialEnvelope` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedNegativeMargin_tendsto_zero` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalNormalizedHalfHaar_with_smallMargin` |
| theorem | `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIW_originalFixedNormalizedMargin_le_explicitVolumeBound` |

新規leafは725行、39,421 bytes、30定理＋2 scalar定義である。各宣言に完全修飾名の`#print axioms`を1件ずつ置き、名前・順序・実出力を一対一で照合した。最終2 runの全32件は`propext`、`Classical.choice`、`Quot.sound`のみ。新規公理・sorry・admit・unsafeは追加していない。

## 8. 依存関係と固定環境

直接importは次の2件。正本baseのblobに対して照合した。

| Source | Git blob |
|---|---|
| `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferOperatorNormVolumeDecayV5_PZ37AIV.lean` | `d298c6be6825cbf37410283f54ef0b67fe7b0db9` |
| `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPositiveHalfTransferPathIteration.lean` | `ee5ab29da849ad02c9e525f23e7c8d22c1e7dd9b` |

AIVを通じて元のAIF crossing Haar恒等式、AIUの左右Haar積分と分配関数率、AIGの源二次モーメント・余裕・領域、AITのeventual半Haar性を使う。既存ambient積分代表とGauss-law制限、既存正規化作用素の適用式を接続する。全依存を人手で再読したという意味ではなく、使用署名の照合と依存閉包の機械的検査を区別する。

| 環境 | 固定値 |
|---|---|
| Lean | `v4.30.0-rc2` |
| runtime Lean commit | `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` |
| mathlib manifest revision | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| maxHeartbeats | `3900000` |
| synthInstance.maxHeartbeats | `1050000` |
| autoImplicit | `false` |

元の固定manifest・toolchainのblobを保持し、CIログでexact checkoutのmanifest復元とLean runtimeを確認した。統合後pushの実ログでは、mathlibの固定revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6` へのcheckoutも明示的に記録されている。

## 9. Exact-source・統合後pushの実認証

Exact-source CI [42574638690](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42574638690/attempts/1) と統合後自動push CI [42575438682](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42575438682/attempts/1) は、全workflow・必須Lean step・独立receiptがSUCCESS。依存閉包は両runとも11411/11411、30定理＋2定義、全32実公理出力は標準3公理のみ。この最終認証2 runのsorryAx・全Lean error・変更warning/errorは0。認証source・実test-merge・[定理squash](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/bd7357e21e0ab24de11d7f957d0000e503f95851) のtreeは `a0315279084e58d44de4daafc4645168f1bc494f` で一致し、Lean全文とblobも一致した。初回失敗run [42573651318](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42573651318/attempts/1) の2件のelaboration errorと回復用sorryAx出力は正式記録に保持する。点ごとの関数形を明示する2か所の証明修正に限り、全32宣言の署名・仮定・固定環境・heartbeatを保持して再認証した。

| 項目 | Exact-source | 統合後push |
|---|---|---|
| run / attempt | [42574638690](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42574638690/attempts/1) / 1 | [42575438682](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42575438682/attempts/1) / 1 |
| event / result | pull_request / SUCCESS | push / SUCCESS |
| exact source / squash | `8a0c86219e4c8b5e352207489e32d17da4e47eba` | `bd7357e21e0ab24de11d7f957d0000e503f95851` |
| actual checkout | `b3a859941ad00f889ccced9265b852705179676d` | `bd7357e21e0ab24de11d7f957d0000e503f95851` |
| main job / step17 | `129019487916` / SUCCESS | `129021992767` / SUCCESS |
| receipt job / step2 | `129021512821` / SUCCESS | `129023819695` / SUCCESS |
| dependency closure | 11411/11411 SUCCESS | 11411/11411 SUCCESS |
| declarations / actual audits | 30 theorem + 2 def / 32 | 30 theorem + 2 def / 32 |
| sorryAx / all Lean errors | 0 / 0 | 0 / 0 |
| changed warning / error | 0 / 0 | 0 / 0 |
| artifact ID | 13655150880 | 13655271496 |
| actual ZIP bytes | 132799 | 134973 |
| actual ZIP SHA256 | 7e23a883e6cd1c17bebb76dae8e24fa864e4a8b914b26e50a4718d54a801a193 | 03d26308e3a41feec617ecaa11373d77171dfe0c0d38b76c070da7254b405d83 |
| extracted log bytes | 1993310 | 2000937 |
| extracted log SHA256 | b99aec13faff94e9b52481955725cff06aec749968917e674df13b830eceb24a | 0739206c6b7e04e99c11408b47e9761e2455e84d01fd2359fde732caa6f719a5 |
| inherited/dependency warning lines | 624 | 624 |

actual ZIP bytesのSHA256をGitHub metadata digestと照合し、展開実ログと完了主ジョブログの全32公理出力を別々に解析した。主ログのtimestampを除いてから複数行の公理集合を読む。両ログの宣言・順序・標準公理集合・closure countが一致し、missing/extra/duplicate/unknown axiomは0。変更warning 0は既存依存のwarningも0という意味ではない。独立レビューとreceiptは別Lean kernelでの再証明を意味しない。

```text
[mcp-receipt] event=pull_request exact_sha=8a0c86219e4c8b5e352207489e32d17da4e47eba source_result=success run=42574638690 attempt=1
[mcp-receipt] event=push exact_sha=bd7357e21e0ab24de11d7f957d0000e503f95851 source_result=success run=42575438682 attempt=1
```

| 来歴 | SHA |
|---|---|
| 開始formal HEAD | `a68659a03493c50cd8951521c78d0043015234fa` |
| 開始main HEAD | `2e3d678f6f7c9505020ea60faa077b18f799d61d` |
| 認証source | `8a0c86219e4c8b5e352207489e32d17da4e47eba` |
| 実test-merge | `b3a859941ad00f889ccced9265b852705179676d` |
| 定理squash | `bd7357e21e0ab24de11d7f957d0000e503f95851` |
| 共通Git tree | `a0315279084e58d44de4daafc4645168f1bc494f` |
| 新規Lean Git blob | `b7ca6055c94a5121eb26a243b46d66c84ecb8eff` |
| 新規Lean SHA256 | `300205e7c96451f6c1670d5921ca62ce5f6ff4cf2f28b260fa7e8af6bab447f2` |

base→sourceとbase→squashは、独立leaf 1件の追加725行・削除0に限る。squashの親は開始formal HEADそのもの。source/test-merge/squashのtree一致とLean全文のbyte一致を確認しており、認証後のsource修正はない。

## 10. 初回失敗の保持と構造修正

初回runの失敗を認証結果へ読み替えない。sourceレビューで数学的な矛盾は発見されなかったが、実際のLean実行は2件のelaboration失敗を検出した。receipt jobのSUCCESSは失敗結果の送信成功である。

| 項目 | 初回実行 |
|---|---|
| run / attempt | [42573651318](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42573651318/attempts/1) / 1 / FAILURE |
| source | `0827b5e96e7c554166cd67980278b0dbfb1c9f1d` |
| source tree | `af0e0aac20726e69937ee1cfa6284cfe2d9557c8` |
| source blob | `fee56217fd0eb56eb168e361186972689a35bd11` |
| source size | 720 lines / 39,264 bytes |
| main job / step17 | `129016437173` / FAILURE |
| receipt job / step2 | `129018107070` / SUCCESS, source_result=failure |
| changed Lean errors | 2 |
| artifact error lines / full job error lines | 4 / 5（終了・build・runner error行を含む） |
| sorryAx occurrences / nonstandard-axiom output rows | 15 / 15 |
| artifact ID | `13654157191` |
| actual ZIP bytes / SHA256 | 135,727 / `0650e0f2713129807ff78b07e448f4034511c8124558d08fce75958a421a60ff` |
| extracted log bytes / SHA256 | 2,001,519 / `446fb2c8a377fd13ec434ad9a4009fbd8798bc4946d2c710a07cd359724a9278` |

220:8では`integral_sub`の右積分関数が`c * (f + g) x`という関数空間の和から推論され、実目標の`c * (f x + g x)`に`rw`が一致しなかった。固定mathlibの`Integrable.fun_add`を用いて、和の積分可能性を点ごとの明示型`hSum`として置き、その型を差の積分に渡した。

320:2ではa.e.等式の右辺が最後の境界引数を欠いた部分適用であり、指定した積分定義のsimp展開が積分本体まで進まなかった。`filter_upwards ... with B hB`で各境界点の等式に特殊化し、完全適用された両定義を展開して元の積の順序を合わせた。

該当行だけでなく、変更全文、imports、依存署名、固定mathlibの`integral_sub`・`Integrable.add`・`Integrable.fun_add`・`const_mul`と既存代表の定義を照合した。初回から修正版まで全32宣言の型・仮定、imports、全options、全公理出力命令を保持し、変更はこの2証明内部に限る。heartbeat増加、警告抑止、新規公理、sorry、物理条件の弱化はない。

失敗したelaborationが生じた回復用sorryAx出力は失敗記録に保持する。sourceへsorryを追加したという意味でも、15件の認証定理があるという意味でもない。修正版の独立レビュー後、Exact-sourceと実squashの自動pushを別々に実認証した。ローカルLean実行を行ったという主張はない。

```text
[mcp-receipt] event=pull_request exact_sha=0827b5e96e7c554166cd67980278b0dbfb1c9f1d source_result=failure run=42573651318 attempt=1
```

## 11. 文書同期の範囲

開始時のGitHub MCP再観測でAIV定理・正式記録・mainミラー（PR #6560/#6561/#6562）が統合済みであることを確認したため、既存AIVを重複作成せず次のAIWとして追加した。append-only／tighten-only／overwrite-forbidden／same-rootを維持する。

この正式記録をformalへ追加し、README・ROADMAPは各branchの既存全文prefixを保持して末尾追記する。mainにはformal正式記録と同一Git blobをミラーする。文書専用PRのためStrict Leanを手動起動しない。main自動workflowは文書ミラー後の検査であり、定理のExact-source認証を置き換えない。本記録は後続のmain workflow成功を先取りして記載しない。
