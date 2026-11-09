# P4-Q2-PZ37AIS — 元のゲージWard交差評価による体積共通の半Haar結合区間

2026年11月9日 JST。元の完全Wilson物理対象を保持した新規leafを、固定Lean4環境のExact-source CIと実公理出力で認証した。定理PR #6551はMERGED。以下の数学は各定理の仮定・有限体積の範囲で形式証明された内容であり、未解決の物理的障害を別に保持する。

参照基準はcanonical formal `c38c6aa1a93d51d147a360a8b51ed3d3514009c2`。定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、`main` は文書ミラーである。元の完全SU(2) Wilson作用、両端の空間halfweight、符号付きZW物理L²源と既存連続代表、真正正規化積Haar、AIGの元の全余裕と厳密負領域を保持する。既存の仮定・定義・定理、公開root、固定Lean/mathlib、heartbeat上限を変更しない。

## 1．研究上の問題と同じ物理対象

AIRは、従来の補助床と元の全余裕を比較する方法の正確な閾値を証明した。しかし、その比較が成立しないことから、元のtransferの負領域が失われるとはいえない。AISは、元のtransferに現れる交差重み付き二次モーメントを追加評価し、この区別を具体的に示す。

有限体積指標を \(H\in\mathbb N\)、元のplaquette数を \(p_H\)、元の連続源を \(f_H\)、対応するZW物理源を \(f_{0,H}\)、真正空間積Haarを \(\mu_H\) とする。既証明の計数と二次モーメントは

\[
p_H=24(H+1)^3>0,
\qquad V_H=\int f_H(A)^2\,d\mu_H(A)>0.
\]

元の完全transferを \(T_{H,\beta}\)、元の交差作用を \(C_H(A,B)\) とし、同じ交差kernelは

\[
K^{\mathrm{cross}}_{H,\beta}(A,B)=e^{-\beta C_H(A,B)}
\]

である。AIGの元の余裕と厳密負領域はそのまま

\[
\varepsilon_{H,\beta}
=\frac{\beta Z_H^{\mathrm{cross}}(\beta)e^{-2\beta p_H}V_H}{2},
\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}
\]

とする。AISのために \(\varepsilon\) を縮めたり、零閾値の負領域へ置き換えたりしていない。

## 2．既証明のWard恒等式から新しい交差二次モーメント下界へ

[AHUの元の混合Haar恒等式](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c38c6aa1a93d51d147a360a8b51ed3d3514009c2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaugeWardCenterMixedHaarExactV5_PZ37AHU.lean) は

\[
\int f_H(A)^2C_H(A,B)\,d\mu_H(A)=p_HV_H
\qquad(\forall B)
\]

を与える。これは元の頂点ゲージ変換とSU(2)中心元による恒等式であり、重なり合うplaquetteの独立性を仮定していない。

したがって、元の源二乗で重み付けした中心化交差作用について

\[
\boxed{\int f_H(A)^2\bigl(C_H(A,B)-p_H\bigr)\,d\mu_H(A)=0}
\]

となる。固定mathlibの `Real.add_one_le_exp` を使った指数関数の接線評価は

\[
e^{-\beta C_H(A,B)}
\ge e^{-\beta p_H}\left[1-\beta\bigl(C_H(A,B)-p_H\bigr)\right].
\]

両辺に非負の \(f_H(A)^2\) を掛け、同じ真正Haarで積分する。全項の可積分性は元の連続関数とコンパクト性から明示的に証明する。括弧内が一部の配置で負になっても、不等式と可積分性は保たれる。中心化項の積分が消えるため

\[
\boxed{
e^{-\beta p_H}V_H
\le
\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)^2\,d\mu_H(A)
}
\qquad(\beta\in\mathbb R,\ \forall B)
\]

を得る。源二乗で正規化した別の確率測度は構成しない。正結合では、AINの旧下界 \(e^{-2\beta p_H}V_H\) より厳密に大きい。

## 3．両端halfweightを保った元transferの負値余裕の改善評価

[AINの元の符号付き二次評価](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c38c6aa1a93d51d147a360a8b51ed3d3514009c2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN.lean) に、新しい交差二次モーメント下界を代入する。\(\beta>0\)、\(f_H(B)\le0\) のとき、元の源の交差畳み込み項は非正である。元の左halfweightと既存の二次係数を保持したまま

\[
e^{\beta W_H(B)/2}T_{H,\beta}f_{0,H}(B)
\le-\beta e^{-2\beta p_H}V_H
\]

となる。さらにAIOで既証明の \(f_H(B)\le0\Rightarrow W_H(B)\le p_H\) を使って元の右halfweightを戻し、

\[
\boxed{
T_{H,\beta}f_{0,H}(B)\le-D_H(\beta),
\qquad
D_H(\beta)=\beta e^{-5\beta p_H/2}V_H>0
}
\qquad(\beta>0,\ f_H(B)\le0)
\]

を得る。負の量にhalfweightを掛ける際の不等号の方向を保持している。

AIOの旧補助床 \(\delta_H(\beta)=\beta e^{-7\beta p_H/2}V_H\) との関係は正確に

\[
D_H(\beta)=e^{\beta p_H}\delta_H(\beta),
\qquad
\delta_H(\beta)<D_H(\beta)\quad(\beta>0).
\]

新しい \(D_H\) は同じtransferに対する追加の補助床であり、元のAIG余裕の再定義ではない。

## 4．体積に共通する閉上端1の半Haar区間

元の余裕との恒等式は

\[
\boxed{
2\varepsilon_{H,\beta}
=\left[Z_H^{\mathrm{cross}}(\beta)e^{\beta p_H/2}\right]D_H(\beta)
}.
\]

[AIQの真正characterから導いた分配関数上界](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c38c6aa1a93d51d147a360a8b51ed3d3514009c2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHoeffdingHalfHaarComparisonCeilingV5_PZ37AIQ.lean) は、全実結合について

\[
Z_H^{\mathrm{cross}}(\beta)
\le e^{p_H(-\beta+\beta^2/2)}
\]

である。したがって

\[
Z_H^{\mathrm{cross}}(\beta)e^{\beta p_H/2}
\le e^{p_H(\beta^2-\beta)/2}\le1
\qquad(0\le\beta\le1).
\]

正結合では \(D_H(\beta)>0\) なので

\[
\boxed{2\varepsilon_{H,\beta}\le D_H(\beta),
\qquad\varepsilon_{H,\beta}<D_H(\beta)}
\qquad(0<\beta\le1).
\]

特に上端 \(\beta=1\) でGaussian予算の指数が0になっても、係数2の余裕によって厳密な領域包含が保たれる。

\[
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta}.
\]

AINの真正Haarを保つ源反転対称性から、源非正集合の測度は少なくとも \(1/2\) である。源のゼロ集合について追加の零測度仮定を置かずに

\[
\boxed{
\forall H\in\mathbb N,\quad
0<\beta\le1
\Longrightarrow
\mu_H(\mathcal N_{H,\beta})\ge\frac12,
\qquad
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\frac12
}
\]

を得る。結合区間と測度下界は \(H\) に依存しない。対象の空間・配置・余裕は引き続き各 \(H\) に属する。

## 5．旧比較法の障害と新しい物理評価が同時に成立する証明書

AIRの旧比較因子を \(F_H(\beta)=Z_H^{\mathrm{cross}}(\beta)e^{3\beta p_H/2}\)、一意閾値を \(\theta_H\)、旧上限を \(2\lambda_H=2\log2/p_H\) とする。旧結果を変更せずに

\[
\theta_H<2\lambda_H\le\frac1{12}<1
\]

から、AISは次を同じ定理内で与える。

\[
\boxed{
\theta_H<1,\quad F_H(1)>2,\quad
\mu_H^{\mathrm{real}}(\mathcal N_{H,1})\ge\frac12
}.
\]

旧比較因子が2を超えても、同じ旧全余裕の負領域に半Haar下界が成立する。これは旧比較法の不成立が、同じ負領域の半Haar性の喪失を意味しないことを、元対象の上で証明している。物理的臨界結合そのものは定義・認証していない。

さらに、元の固定結合

\[
\beta_0=\frac{\log(3/2)}{64},
\qquad \frac1{192}\le\beta_0\le\frac1{128}<1
\]

は全ての有限 \(H\) で新しい区間に入る。\(H\ge2\) ではAIBの既存評価

\[
\beta_0p_H\ge\frac{(H+1)^3}{8}\ge\frac{27}{8},
\qquad p_H\lambda_H=\log2\le1
\]

から \(\theta_H<2\lambda_H<\beta_0\)。AIRの比較同値を使い、AISは同時に

\[
\boxed{
\theta_H<\beta_0,\quad F_H(\beta_0)>2,\quad
\delta_H(\beta_0)<\varepsilon_{H,\beta_0}<D_H(\beta_0),\quad
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta_0})\ge\frac12
}
\qquad(H\ge2)
\]

を証明する。旧補助床だけでは届かないことと、新しいtransfer評価による成功を、同じ \(H,\beta_0\)、同じ作用・源・Haar・余裕について区別して保持する。

## 6．体積依存性と残る障害

元の点ごとの評価 \(|f_H|\le p_H/2\) を同じ確率Haarで積分して

\[
V_H\le\frac{p_H^2}{4}
\]

を証明する。新しい床についても

\[
\boxed{
D_H(\beta)\le\frac{\beta p_H^2}{4}e^{-5\beta p_H/2}
\quad(\beta\ge0),
\qquad
D_H(\beta)=\beta e^{-60\beta(H+1)^3}V_H
}
\]

を明示的に証明する。AISは結合区間とHaar質量下界を全有限体積で共通にしたが、体積一様の正の負値余裕を構成していない。このleafには \(H\to\infty\) の極限定理自体は追加していない。

未解決の範囲は、\(\beta>1\) を含む任意正結合での旧全余裕半Haar下界、体積一様の正の振幅・coercivity、元の作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapである。関数のある領域での負値を、作用素の負固有値へ昇格させない。

次段AITの候補は、元の交差作用・源のさらに強い相関評価による \(\beta>1\) の範囲、または既存の明示体積上界から振幅の非一様性を厳密に分離することである。新しい結果が得られるまで未証明として保持する。

## 7．新規Lean宣言と依存

| # | 宣言（共通接頭辞 p4Q2PZ37AIS_ を省略） | 内容 |
| --- | --- | --- |
| 1 | `originalSourceSquare_centeredCrossingHaar_zero` | 元の源二乗による中心化交差モーメント0 |
| 2 | `originalCrossingSecondMoment_wardLower` | 全実結合での真正交差二次モーメント下界 |
| 3 | `sourceNonpositiveWardFloor` | 新しい補助床 D_H の定義 |
| 4 | `sourceNonpositiveWardFloor_pos` | 正結合で D_H>0 |
| 5 | `wardFloor_eq_exp_mul_previous` | D_H=e^(beta*p_H) delta_H の恒等式 |
| 6 | `previousFloor_lt_wardFloor` | 正結合で旧補助床より厳密に大きい |
| 7 | `originalRightWeightedTransfer_le_negativeWardVariance` | 元の右重み付きtransferのWard二次評価 |
| 8 | `originalTransfer_le_negativeWardFloor` | 両端halfweightを保った T<=-D_H |
| 9 | `originalNegativeMargin_wardRatio_identity` | 旧余裕の正確な比 2epsilon=(Zcross exp(beta*p/2))D |
| 10 | `originalWardMarginFactor_le_gaussian` | 全実結合で新比較因子のGaussian上界 |
| 11 | `originalWardMarginFactor_le_one` | 0<=beta<=1で新比較因子<=1 |
| 12 | `twice_originalNegativeMargin_le_wardFloor` | 0<beta<=1で2epsilon<=D |
| 13 | `originalNegativeMargin_lt_wardFloor` | 0<beta<=1でepsilon<D |
| 14 | `originalSource_nonpos_subset_fullNegativeRegion` | 源非正集合の元の厳密負領域への包含 |
| 15 | `originalFullNegativeRegion_Haar_half` | 全有限H・0<beta<=1で拡張非負実数値半Haar下界 |
| 16 | `originalFullNegativeRegion_realHaar_half` | 同条件で実数値半Haar下界 |
| 17 | `previousComparisonThreshold_lt_one` | 旧閾値theta_H<1 |
| 18 | `oldComparisonObstruction_newEndpoint_certificate` | beta=1で旧比較の障害と元領域の半Haar成功 |
| 19 | `fixedCoupling_fullNegativeRegion_realHaar_half` | 元の固定beta0で全有限Hの半Haar下界 |
| 20 | `originalSourceSecondMoment_le_countSquare` | 元のHaar二次モーメント V_H<=p_H^2/4 |
| 21 | `wardFloor_le_explicitVolumeBound` | D_Hの明示的な体積上界 |
| 22 | `wardFloor_exactVolume` | 元の計数によるD_Hの正確な体積表示 |
| 23 | `originalFixedCoupling_mem_unitInterval` | 元の固定beta0が(0,1]に属する |
| 24 | `originalFixedCoupling_count_ge_twentySevenEighths` | H>=2で beta0*p_H>=27/8 |
| 25 | `oldComparisonCeiling_lt_originalFixedCoupling` | H>=2で旧比較上限2lambda_H<beta0 |
| 26 | `oldCriticalComparison_lt_originalFixedCoupling` | H>=2で旧一意閾値theta_H<beta0 |
| 27 | `oldMarginComparison_at_originalFixedCoupling_gt_two` | H>=2で旧比較因子F_H(beta0)>2 |
| 28 | `oldVarianceFloor_lt_originalFixedMargin` | H>=2で旧補助床delta_H(beta0)<epsilon_H(beta0) |
| 29 | `fixedCoupling_oldObstruction_newHalfHaar_certificate` | 同じ固定物理対象で旧障害と新成功の統合証明書 |

直接importはAIR、AHU、`Mathlib.Tactic`。AHUの元のmixed Haar恒等式、AINの交差畳み込みと符号付き二次評価、AIOの源非正集合における右作用上界、AIQの元分配関数Gaussian上界、AIBの真正計数と固定結合区間を接続する。新しい物理仮定や未証明公理を追加しない。

## 8．Exact-source認証・統合の実観測

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `c38c6aa1a93d51d147a360a8b51ed3d3514009c2` |
| [定理PR #6551](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6551) | MERGED |
| 認証対象source HEAD | `5dd160ee8420b50e5cd53841517fa1bbb43e86fa` |
| CI実checkout／test-merge HEAD | `f9adc45d60c600b652d82ff3b89fa925952189ed` |
| 実際の定理squash | `3dd12415adb88e30abbd97ab6d7d4cf7579eb38b` |
| source／test-merge／実squash共通Git tree | `a752ee83411955a74b4eddae55707f9c87a4ad40` |
| 新規Lean Git blob | `178365b8b478b4bd49b73429ccea8958103e2467` |
| 新規Lean SHA256 | `7595b3a5322db2ec7de3414ac43c78cb2969cddc7d2c29481ce46a33f6b6bb41` |
| 新規Lean | 552行・28定理・1定義・29公理出力命令・29,002 bytes |
| [CI #42540948252 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42540948252/attempts/1) | completed／SUCCESS |
| 主job | `128915498941`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11407／11407 SUCCESS** |
| 新規leaf build | 32秒 |
| 実際の公理出力 | **29／29**、全29件が `propext, Classical.choice, Quot.sound` のみ |
| 公理出力の欠落／余分／重複 | 0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更Lean全文warning／error | 0／0 |
| 独立completion receipt job | `128916871397`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| exact-source status ID | `58385697886` |
| check suite | `115230344009`、completed／SUCCESS、check runs 2件ともSUCCESS |
| 診断artifact | `13641526232`、130,879 bytes |
| 実ZIP SHA256 | `25cbfe58c63f34aaee5da0d89a4bdf8814108c833f1b43fcf302ee9ce89b10a1` |
| 抽出実ログ | 1,949,776 bytes |
| 抽出実ログSHA256 | `3b38439a2a0bbd92ffc56dcdb762517b6142d997b31790ed1d4be323da671556` |

receiptの9,701文字の実ログは `[mcp-receipt] event=pull_request exact_sha=5dd160ee8420b50e5cd53841517fa1bbb43e86fa source_result=success run=42540948252 attempt=1` を記録する。exact-source statusのtargetも同じrunを指す。

主担当は完了後の主ジョブログ全文3,376,085文字と、診断artifactの実bytesを取得した。全29宣言の完全修飾名と実公理出力を一対一で照合し、欠落・余分・重複、標準外公理、sorryAx、全Lean error・Actions error、変更ファイルのwarning/errorがないことを確認した。ZIP実SHA256はGitHub metadataのdigestと一致した。変更warning 0は、既存依存ファイルの再生warningまで全件0という主張ではない。

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。認証sourceの `lean-toolchain`（blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`）と `lake-manifest.json`（blob `01260678b674ab241e753563e913c7ce9c6ba659`）、実ログのLean versionとcheckoutを照合した。

base差分は新規Lean1件だけ（552行追加・削除0、sourceのahead2／behind0）。既存Lean・定義・定理・公開root・証明記録・workflow・pin・heartbeatを変更していない。修正後のGitHub source全文とローカル全文、統合後の全文・blobは一致した。

独立CI担当はworkflow・job・必須step・receipt全文・status・suite/check runs・source/test-merge tree・artifact metadataを別途確認した。主ログ全文とartifact実bytes・公理出力の解析は主担当によるものとして区別して記録した。別job receiptや独立の記録照合を、別のLean kernelによる独立再証明と同一視しない。

定理PR #6551の実squashを統合後に再取得した。実squashの唯一の親は元canonical baseであり、source／test-merge／実squashのtreeは一致した。canonical formalが同じsquashに進んだことと、新規Leanの同一blobを主担当・独立CI担当が再観測した。

[統合済みAIS Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/3dd12415adb88e30abbd97ab6d7d4cf7579eb38b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS.lean)。

### 統合後pushの再検証

実際の定理squashを対象とした自動 [push CI #42541570833 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42541570833/attempts/1) も完了後に確認した。

| 項目 | 実観測結果 |
| --- | --- |
| push対象／実checkout | `3dd12415adb88e30abbd97ab6d7d4cf7579eb38b` |
| 全workflow | completed／SUCCESS |
| 主job／必須Lean step 17 | `128917443771`、ともにcompleted／SUCCESS |
| Lake依存閉包／新規leaf | **11407／11407 SUCCESS**／14秒 |
| 実公理出力 | 29／29、全件が標準3公理のみ |
| sorryAx／標準外公理／全Lean error | 0／0／0 |
| 変更warning／error | 0／0 |
| receipt job／step 2 | `128918976524`、ともにcompleted／SUCCESS |
| exact-squash status | `58385967680`、SUCCESS |
| check suite／check runs | `115231901274`、SUCCESS／2件ともSUCCESS |
| 完了主ジョブログ | 3,388,288文字 |
| 診断artifact | `13640889084`、実ZIP 133,076 bytes |
| 実ZIP SHA256 | `a3e9398514c09b9afed50ced66043283cbab3710817b2d0602fe4da6e2b6f49f` |
| 抽出実ログ | 1,957,741 bytes |
| 抽出実ログSHA256 | `cfc7b13998101aa99d203974afec957424e35dd23465a87d6b212c3cc7a3c2a3` |

receiptの9,689文字の実ログは `[mcp-receipt] event=push exact_sha=3dd12415adb88e30abbd97ab6d7d4cf7579eb38b source_result=success run=42541570833 attempt=1` と記録する。主担当は完了主ログ・実artifact bytes・29の実公理出力を再照合した。実ZIPのdigestはGitHub metadataと一致し、欠落・余分・重複も0だった。統合前の認証sourceを、未確認の別treeへ読み替えていない。

### 初回sourceの失敗と、正の実数による乗法消去APIの修正

初回source `a49fd8ef98e2e95c3899f8f3fa0de7012f8a0bc3`（552行、28,996 bytes、Git blob `429816d68d85fad8b71e97a0c05ce0367646b195`、SHA256 `f6138c0b1a2a70344589d3dda8b6d1c107bce7f4b972d6dd9ceadda0cad4cec2`）の [CI #42540179585 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42540179585/attempts/1) は、workflow・主job `128913131740`・必須Lean step 17がFAILUREで完了した。実checkoutは `a694980866528bce5ec245d22f8077aead36b1fd`、sourceとの共通Git treeは `c55fbcb5710d71e40731ce13e1bafc3febbf9a19`。新規leafは `[11407/11407] Building ... (12s)` で失敗しており、依存閉包全体SUCCESSとは扱わない。

変更Leanの診断は次の2件、warningは0件だった。

| 箇所 | 実診断と原因 |
| --- | --- |
| 476:9 | `failed to synthesize instance of type class MulLeftStrictMono ℝ`。旧比較上限と固定結合の比較で、正の実数による乗法消去を意図して `mul_lt_mul_right` を使ったが、固定mathlibの同名補題は任意の左乗算の厳密単調性を型クラスとして要求する別のAPIだった。 |
| 477:2 | `No goals to be solved`。直前の失敗に続く診断であり、独立した数学的障害ではなかった。 |

失敗後に、変更Lean全文・imports・依存署名・固定mathlibの原定義を再確認した。固定 [順序付きmonoidのAPI](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean) の `mul_lt_mul_right` は、実数全体では満たされない任意乗算の厳密単調性を要求する。正の乗数の条件を明示する固定 [GroupWithZeroのAPI](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean) を用い、次の1行だけを置き換えた。

```lean
apply (mul_lt_mul_iff_left₀ (p4Q2PZ37AHN_count_pos H)).mp
```

これは既証明の `0 < p_H` を使い、`(2 * lambda_H) * p_H < beta0 * p_H` から目的の比較へ戻す。後続の `nlinarith only [hLog, hCount, hLower]` は変更しなかった。全29宣言の署名・仮定・定義値・他の証明本文・imports・heartbeat・全29公理出力命令は不変であり、ファイル全体が上のAPI名1か所の置換だけで一致することを機械的に確認した。

初回の静的レビューはこの固定APIの取り違えを検出できていなかった。静的な数学・ソース読解と、固定環境でのLean型検査・実公理出力の認証を区別する。

初回の実公理出力は29件、欠落・余分・重複は0だったが、失敗した比較定理とその下流の計5件に `sorryAx` が含まれた。残り24件が標準3公理のみであったことも、失敗source全体の認証には用いない。ソースに明示的な `sorry` や `axiom` を追加したものではない。

主担当は完了後の主ジョブログ全文3,388,221文字と診断artifactの実bytesを取得した。独立CI担当はworkflow・job・step・receipt・status・suite・tree/blobを別に照合した。別担当が同じ主ジョブログ全文を再取得したという主張はしない。

初回receipt job `128915040444` 自体はSUCCESSで完了したが、9,701文字の実ログは `event=pull_request exact_sha=a49fd8ef98e2e95c3899f8f3fa0de7012f8a0bc3 source_result=failure run=42540179585 attempt=1` と記録した。発行status `58385469918` とcheck suite `115228393910` もfailureである。receipt jobの成功を定理の成功と読み替えない。

初回artifact `13641745006` の実ZIPは133,213 bytes、SHA256 `1b8e79bfcf2fe73bac89d8775b11381dda0f661eb77535c83b0707e674aacf31`。抽出実ログは1,957,575 bytes、SHA256 `7e9d2aa9f48d4b69524e661388eed88636633b797e5d074341f95799cad0c1c7`。ZIP実bytesのdigestはGitHub metadataと一致した。失敗source・診断・receipt・公理出力の監査結果を保持し、修正後の認証対象と区別する。


## 9．独立レビューと文書同期

552行の変更Lean全文、全imports、依存する定理署名・証明構造を独立レビューした。Ward接線評価、両端halfweightの指数、旧余裕との恒等式、beta=1での厳密包含、固定結合での旧比較法の障害を点検した。静的レビューをLeanの型検査や公理出力の認証と同一視せず、CIの完了結果を別に確認した。

本文とREADME・ROADMAPの更新は文書専用PRで行い、既存全文を保持する。文書専用変更ではStrict Leanを手動起動しない。mainへはformalで認証された同一の正式記録Git blobをミラーする。
