# P4-Q2-PZ37AIQ — 真正Haarの分配関数両側評価と旧余裕比較の上限

**2026年11月9日 JST。AIQのexact-source認証と定理統合を完了。** 固定環境での型検査、33件の実公理出力、workflow・必須Lean step・独立completion receiptの完了、独立読解、実squashのtree/blob一致を確認した。観測値と失敗履歴は第7–8節に記録する。append-only／tighten-only／overwrite-forbidden／same-rootを保持する。

参照基準は canonical formal `47005e4fed8486a5611d55b90f281101cb8d9e3b`。元の完全SU(2) Wilson作用、両端halfweight、符号付きZW物理L²源と既存連続代表、真正正規化Haar、AIGの元の全余裕と厳密負領域、AIO・AIPの既存定義と仮定を保持する。

## 1．元の対象と保持する余裕

有限体積指標を `H : ℕ`、元のplaquette数を `p_H>0`、元の空間リンク数を `n_H` とする。真正空間積Haarを `μ_H`、元の連続源を `f_H`、その真正二次モーメントを `V_H=∫f_H² dμ_H>0` と書く。元の物理源は `f₀,H`、完全transferは `T_{H,β}` である。

[AIFの元の定義](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/47005e4fed8486a5611d55b90f281101cb8d9e3b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean)に従い、単リンク群 `G=SU(2)`、真正確率Haar `ν`、元のWilsonエネルギー `E` に対して

\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),\qquad
Z_H^{\mathrm{cross}}(\beta)=z(\beta)^{n_H},\qquad n_H=p_H.
\]

[AIGの元の全余裕と負領域](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/47005e4fed8486a5611d55b90f281101cb8d9e3b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)を変更しない。

\[
\varepsilon_{H,\beta}
=\frac{\beta Z_H^{\mathrm{cross}}(\beta)e^{-2\beta p_H}V_H}{2},
\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}.
\]

新しい評価はこの元の分配関数に対する上下界であり、別の分配関数・測度・物理源への置換ではない。plaquette独立性は追加しない。

## 2．元の単リンク関数とHoeffding上界

元の関数 `χ=p4Q2PZ35C_originalOneLinkCharacter=1-E` をそのまま用いる。元の範囲 `0≤E≤2` により `-1≤χ≤1`。連続性から真正Haarに関して可測であり、[既存のcharacter-zero恒等式](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/47005e4fed8486a5611d55b90f281101cb8d9e3b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarContractionV5_PZ35D4.lean)により `∫χ dν=0` である。

固定mathlibの [Hoeffding補題](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/SubGaussian.lean) `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` を、実際の `χ` と `ν` に適用する。区間 `[-1,1]` のパラメータは `((1-(-1))/2)²=1` なので、

\[
M(\beta):=\int_G e^{\beta\chi(g)}\,d\nu(g)
\le e^{\beta^2/2}\qquad(\beta\in\mathbb R).
\]

元のエネルギーとの恒等式を積分の中で確認して

\[
z(\beta)=e^{-\beta}M(\beta)
\]

を得る。したがって、

\[
\boxed{z(\beta)\le e^{-\beta+\beta^2/2}\qquad(\beta\in\mathbb R).}
\]

この評価には正結合条件や `β<1/4` 条件は不要である。Hoeffding補題の測度・可測性・範囲・平均の各条件は元の対象について証明しており、新しい仮定として与えない。

## 3．接線不等式による下界と元の交差分配関数

全実数について `1+t≤exp(t)` が成立する。`t=βχ(g)` を代入し、可積分性を確認して真正Haarで積分すると、

\[
1=\int_G(1+\beta\chi(g))\,d\nu(g)
\le M(\beta).
\]

これを第2節の正確な因数分解と合わせて

\[
\boxed{e^{-\beta}\le z(\beta)\le e^{-\beta+\beta^2/2}}
\]

を得る。左辺の証明も全実結合に有効であり、接線の値が負になる点を排除しない。

[AIPの元の計数接続](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/47005e4fed8486a5611d55b90f281101cb8d9e3b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP.lean) `(Nat.card Link : ℝ)=p_H` と非負な底の冪の単調性を使い、

\[
e^{-\beta p_H}
\le Z_H^{\mathrm{cross}}(\beta)
\le e^{p_H(-\beta+\beta^2/2)}
\]

を得る。元のリンク数や有限積Haarを変えない。

[AIOの元の余裕比較](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/47005e4fed8486a5611d55b90f281101cb8d9e3b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHalfHaarFullMarginCouplingV5_PZ37AIO.lean)に現れる因子を `F_H(β)=Z_H^{cross}(β)exp(3βp_H/2)` と略記すれば、

\[
\boxed{
e^{\beta p_H/2}\le F_H(\beta)
\le e^{p_H(\beta+\beta^2)/2}
\qquad(\beta\in\mathbb R).
}
\]

この `F_H` は説明用の略記であり、新しい物理transferの定義ではない。

## 4．厳密な二次予算と上端を含む有理式の区間

第3節の上界により、積分を含まない十分条件は

\[
\boxed{\frac{p_H(\beta+\beta^2)}2<\log2
\quad\Longrightarrow\quad F_H(\beta)<2.}
\]

さらに正結合なら、AIOを通じて旧全余裕負領域の実数値Haar質量が `1/2` 以上となる。

`L=\log2>0` とし、新しい明示上端を

\[
\boxed{q_H:=\frac{2L}{p_H+2L}>0}
\]

と定義する。`0<β≤q_H` なら `β(p_H+2L)≤2L`。`βL>0` から `βp_H<2L` が得られ、正の `β` を掛けると `p_Hβ²<2Lβ`。両式を合わせ、

\[
p_H\beta+p_H\beta^2<2L
\]

となる。このため二次予算は**新上端 `β=q_H` でも厳密**である。非厳密なHoeffding上界から、上端での厳密比較を仮定する操作は行わない。

## 5．旧全余裕への包含、半Haar下界、旧上端との比較

AIOの補助床 `δ_{H,β}=βexp(-7βp_H/2)V_H` は正結合で正であり、同じ元の対象について

\[
f_H(B)\le0\Longrightarrow T_{H,\beta}f_{0,H}(B)\le-\delta_{H,\beta},
\qquad
2\varepsilon_{H,\beta}=F_H(\beta)\delta_{H,\beta}
\]

が既証明である。第4節から `ε<δ` を得て、

\[
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta},
\qquad
\boxed{0<\beta\le q_H\Longrightarrow
\frac12\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})}.
\]

`ℝ≥0∞` 値のHaar測度でも同じ下界を証明する。源のゼロ集合を含み、その測度に追加仮定は置かない。旧 `ε` は縮小しない。

AIPの旧上端 `λ_H=L/p_H` は保持され、

\[
q_H=\frac{2p_H}{p_H+2L}\lambda_H,\qquad
\boxed{\frac{24}{13}\lambda_H\le q_H<2\lambda_H,\quad \lambda_H<q_H}.
\]

`p_H≥24` と `L≤1` から `p_H≥24L` が得られ、相対下界を導く。実装では既証明の `λ_H≤1/24` と `p_Hλ_H=L` を使う。`24/13` は区間上端の体積一様な**比**の保証であり、体積一様の正結合区間や負値余裕の保証ではない。

## 6．比較法の上限と、残る範囲

第3節の下界により、

\[
\boxed{\beta\ge2\lambda_H\Longrightarrow F_H(\beta)\ge2}.
\]

したがって同範囲ではAIOの厳密条件 `F_H(β)<2` は成立しない。逆に、その条件が成立するなら `β<2λ_H` でなければならない。`β≥2λ_H` は正結合を含意し、AIOの正確な比の恒等式から

\[
\boxed{\beta\ge2\lambda_H\Longrightarrow
\delta_{H,\beta}\le\varepsilon_{H,\beta}}
\]

も得る。

これは**AIOの特定の十分条件と補助床による余裕比較の障害**である。実際のtransfer負性や旧領域の半Haar下界が不可能という証明ではない。`q_H` は明示的な十分上端であり、最適上端とは主張しない。`q_H` より大きい結合でも二次予算を個別に満たせば、第4節の条件付き定理を適用できる。`q_H<β<2λ_H` の全域を一律認証するものでもない。

元の全余裕・負領域、AINの全正結合の既存結果、AIL・AIMの従来区間での全空間負性と質量1、AIO・AIPの旧結果は保持する。任意正結合の旧全余裕半Haar下界、任意正結合の全境界負性、体積一様の正の負値余裕・coercivity、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapへの昇格は行わない。

### 33宣言の対応表

名前空間は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`、共通prefixは `p4Q2PZ37AIQ_`。32定理・1定義があり、下表はprefixを省略する。型検査を完了し、各 `#print axioms` の実出力33件を全宣言と一対一で照合した。全件の公理は `propext, Classical.choice, Quot.sound` のみである。

| # | 宣言末尾 | 内容・必要条件 |
| --- | --- | --- |
| 1 | `originalSingleLinkCharacter_continuous` | 元の `χ=1-E` の連続性 |
| 2 | `originalSingleLinkCharacter_mean_zero` | 元の真正Haar平均0 |
| 3 | `originalSingleLinkCharacter_mem_interval` | 元の `χ(g)∈[-1,1]` |
| 4 | `originalSingleLinkCharacter_subgaussian` | 元の `χ,ν` に対するパラメータ1のMGF上界 |
| 5 | `originalSingleLinkPartition_characterMGF` | 全実 `β` で `z=e^{-β}M` |
| 6 | `originalSingleLinkPartition_le_gaussian` | 全実 `β` で `z≤exp(-β+β²/2)` |
| 7 | `originalSingleLinkCharacter_MGF_ge_one` | 全実 `β` で `1≤M` |
| 8 | `originalSingleLinkPartition_ge_expMean` | 全実 `β` で `exp(-β)≤z` |
| 9 | `originalCrossingPartition_le_gaussian` | 全実 `β` で元の交差分配関数の上界 |
| 10 | `originalCrossingPartition_ge_expMean` | 全実 `β` で元の交差分配関数の下界 |
| 11 | `originalMarginFactor_le_gaussian` | 全実 `β` で `F_H≤exp(p_H(β+β²)/2)` |
| 12 | `originalMarginFactor_ge_expHalf` | 全実 `β` で `exp(βp_H/2)≤F_H` |
| 13 | `originalPartitionCondition_of_quadraticBudget` | 厳密二次予算から `F_H<2` |
| 14 | `originalFullNegativeRegion_realHaar_half_of_quadraticBudget` | 正結合と二次予算から旧領域の実数値半Haar下界 |
| 15 | `rationalHalfHaarCouplingCutoff` | 新定義 `q_H=2log2/(p_H+2log2)` |
| 16 | `rationalHalfHaarCouplingCutoff_pos` | `q_H>0` |
| 17 | `originalCount_mul_previousCutoff` | `p_Hλ_H=log2` |
| 18 | `rationalCutoff_relative_identity` | 新旧上端の正確な比 |
| 19 | `rationalCutoff_ge_twentyFourThirteenths_previous` | `(24/13)λ_H≤q_H` |
| 20 | `previousCutoff_lt_rationalCutoff` | `λ_H<q_H` |
| 21 | `rationalCutoff_lt_twice_previous` | `q_H<2λ_H` |
| 22 | `quadraticBudget_of_le_rationalCutoff` | `0<β≤q_H` で厳密二次予算 |
| 23 | `originalPartitionCondition_of_le_rationalCutoff` | 同区間で `F_H<2` |
| 24 | `originalNegativeMargin_lt_varianceFloor` | 同区間で元の `ε<δ` |
| 25 | `originalSource_nonpos_subset_fullNegativeRegion` | 同区間で源非正集合を旧全余裕負領域に包含 |
| 26 | `originalFullNegativeRegion_Haar_half` | 同区間で `ℝ≥0∞` 値半Haar下界 |
| 27 | `originalFullNegativeRegion_realHaar_half` | 同区間で実数値半Haar下界 |
| 28 | `expandedEndpoint_certificate` | 新上端の真の拡大・正値性・厳密条件・半Haar |
| 29 | `originalMarginFactor_ge_two_of_large` | `β≥2λ_H` で `2≤F_H` |
| 30 | `originalPartitionCondition_implies_lt_twice_previous` | `F_H<2` なら `β<2λ_H` |
| 31 | `originalPartitionCondition_obstructed_of_large` | `β≥2λ_H` でAIOの厳密条件を否定 |
| 32 | `varianceFloor_le_originalNegativeMargin_of_large` | 同範囲で元の `δ≤ε` |
| 33 | `comparisonCeiling_certificate` | 比較上限 `2λ_H` における元の因子・床・余裕の証明書 |

## 7．Exact-source検証と統合の実観測

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `47005e4fed8486a5611d55b90f281101cb8d9e3b` |
| [定理PR #6545](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6545) | MERGED |
| 認証対象source HEAD | `3491bd266ac691d7614464d03815bb48cd6bb550` |
| CIの実checkout／test-merge HEAD | `09479b4fc091e860b8b6d43fbb33007ba7658a8d` |
| 実際の定理squash | `8a2d3bffba571de75ee31999894f22bec458baf3` |
| source／test-merge／実squash共通Git tree | `841e4b9f4143aef0efb8b37ef71f2d75ce7d0230` |
| 新規Lean Git blob | `4d1f4fbf9631e508b0396526f17295c694d40d6e` |
| 新規Lean SHA256 | `a37fbb443a5590065804ab2476ece1b5f4a1463f1a53d5fd09517c6dea263dd1` |
| 新規Lean | 441行・32定理・1定義・33公理出力命令・24,079 bytes |
| [CI #42530462705 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42530462705/attempts/1) | completed／SUCCESS |
| 主job | `128883317108`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11,405／11,405 SUCCESS** |
| 新規leaf build | 33秒 |
| 実際の公理出力 | **33／33**、全件 `propext, Classical.choice, Quot.sound` のみ |
| 公理出力の欠落／余分／重複 | 0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更Lean全文warning／error | 0／0 |
| 独立completion receipt job | `128884645661`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| exact-source status ID | `58381559306` |
| check suite | `115203361115`、completed／SUCCESS、check runs 2件ともSUCCESS |
| 診断artifact | `13637725311`、129,885 bytes |
| 実ZIP SHA256 | `0ab911e0936230194811913d4fce695a6492d242681c47e39270929b41d86d54` |
| 抽出実ログ | 1,930,350 bytes |
| 抽出実ログSHA256 | `9ab16158ce387030a41803db5ef0c239674c0c0c0c6ad8e70d2055abbd59c864` |

receipt実出力は `[mcp-receipt] event=pull_request exact_sha=3491bd266ac691d7614464d03815bb48cd6bb550 source_result=success run=42530462705 attempt=1`。exact-source statusのtargetも同じrunを指す。

主担当は、完了後の実ジョブログ全文（3,350,743文字）と診断artifactの実bytesを取得した。33宣言の完全修飾名と実公理出力を一対一で照合し、欠落・余分・重複、標準外公理、sorryAx、全Lean error・Actions error、変更ファイルのwarning/errorがないことを確認した。実ZIP SHA256はGitHub metadataのdigestと一致する。変更ファイルのwarning 0は、既存依存ファイルの再生warningもすべて0という意味ではない。

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。exact sourceの `lean-toolchain` と `lake-manifest.json`、実ログのLean versionとcheckoutを照合した。直接importはAIP、`Mathlib.Probability.Moments.SubGaussian`、Mathlib.Tactic。新しい確率論importは同じ固定mathlib内の補題を用いるもので、pin変更ではない。base差分は新規Lean1件だけ（441行追加・削除0、ahead2／behind0）。既存ファイルとworkflowは変更していない。

### 初回sourceのelaboration failureと修正

初回source `ec0bf6d173b6407bd9a6d8fdba47ddb97317125f` の [CI #42529988834 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42529988834/attempts/1) はworkflow・主job `128881830463`・必須step 17ともFAILUREだった。新規leafは `[11405/11405] Building ... (27s)` で失敗しており、依存閉包全体SUCCESSとして扱わない。

90行目の `(1 : ℝ≥0)` について `LE Type` と `OfNat Type 0` の型クラス解決エラーが生じた。固定 [NNRealの記法定義](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Data/NNReal/Defs.lean)では `ℝ≥0` は `NNReal` namespace内のscoped notationである。AIQは `ENNReal` scopeを開いていたが、別の `NNReal` scopeは開いていなかったため、この表記が型の別名として認識されず、実数型自体への比較式として解釈された。importの存在だけでは、この局所表記の有効化を意味しない。

全文・import・依存署名・固定mathlibの記法を照合し、修正は `(1 : NNReal)` という明示的な型注釈への変更1箇所に限定した。意図した同じ非負実数係数1を指定する修正であり、数学的命題・仮定・定数値・証明本体・import・scope・heartbeatを変更していない。下流の有効な証明や診断を削除・抑制せず、新しいexact-source CIで再検証した。

初回ログでは33件の出力名が各1回現れたが、壊れた宣言からのエラー回復により21件に `sorryAx` が伝播した。変更ファイルには型エラー2件と下流warning3件があり、初回sourceは未認証として保持する。明示的な `sorry` をソースに記載したものではない。独立担当も完了後主ログ3,354,623文字を取得して同じ結果を確認した。

初回receipt job `128882975421` はSUCCESSで完了し、9,705文字の実ログに `source_result=failure` と旧exact sourceを正しく記録した。発行したstatusはfailure、IDは `58381349575`、check suite `115202111505` もfailureである。receiptジョブの成功を、証明の成功として扱わない。

初回artifact `13637356394` の実ZIPは130,991 bytes、SHA256 `c9adfaa575391de76dac0ea72d5eb35ba538ecbec75fe28cc6497339f13e2c4e`。抽出実ログは1,933,898 bytes、SHA256 `b92f44c1046e3749efcbf14d925754b9054fc415d628a6f872069803def7ebed`。失敗履歴と認証済みsourceを区別して保持する。

## 8．独立照合、実squash、正式記録

数理担当と別のソース/API担当が変更Lean全文・全33署名を読解し、真正HaarへのHoeffding適用とJensen下界、元の計数、上端での厳密性、旧余裕と測度包含、比較法だけの障害を確認した。数学節1–6、33宣言表、既存APIと固定mathlibへのリンクも独立に照合した。初回の静的レビューではNNReal記法のscope依存を見落としたが、CI診断後には固定定義と全文scopeを別途照合し、明示型への1箇所修正を確認した。全推移依存ファイルを全文読解したという主張ではない。

別のCI監査担当も、workflow・全jobの完了後に主ジョブログ全文3,350,743文字とreceiptログ全文9,701文字を独立取得した。33件の完全修飾名が各1回、標準3公理のみ、sorryAx・全Lean error・変更warning/errorがすべて0であること、11,405件の依存閉包SUCCESS、実checkout、required step 17、receipt step 2、exact-source statusとcheck suiteのSUCCESSを照合した。ZIP実bytesのハッシュとGit tree/blobの照合は主担当が行った。独立担当による実ログ照合と独立receiptは、別のLean kernelで再証明したという意味ではない。

定理PR #6545の実squash `8a2d3bffba571de75ee31999894f22bec458baf3` を統合後に再取得し、source／test-merge／実squashのGit treeと、新規Leanの本文・Git blobが完全一致することを確認した。実squashの唯一の親は元canonical baseである。

[統合済みAIQ Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/8a2d3bffba571de75ee31999894f22bec458baf3/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHoeffdingHalfHaarComparisonCeilingV5_PZ37AIQ.lean)。

本記録は、exact-sourceの完了検証・全実公理出力監査・独立completion receipt・独立読解・実squashのtree/blob一致の後、別のdocs-only PRで新規追加する。mainには同じ既存記録Git blobを用いる。既存Lean・既存証明記録・README・ROADMAPは変更せず、docs-onlyでStrict Leanを手動起動しない。既存workflowも変更しない。

