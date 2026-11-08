# P4-Q2-PZ37AIP — 元の分配関数の厳密上界と上端を含む半Haar区間

2026年11月9日 JST ／ Lean4 exact-source検証済み・定理正本統合済み

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。固定Lean/mathlib、heartbeat上限、既存workflowを保持する。検証・統合の実観測と初回sourceの履歴は第7–8節に記載する。

既存APIの参照基準は canonical base `28e8137b8f17cd027981bc9326b22a22f643f29d`。元のSU(2) Wilson一スラブ作用、左右両半重み、符号付きZW物理L2源と既存の連続代表、真正正規化Haar、AIGの元の余裕と厳密負領域を保持する。AIOの定義・定理・記録も変更しない。

## 1．対象と、保持する元の余裕・負領域

有限体積指標を `H : ℕ`、元のプラケット数を `p_H>0`、元の配置空間の正規化積Haarを `μ_H` とする。元の連続源を `f_H`、その真正Haar二次モーメントを `V_H=∫f_H² dμ_H>0`、元のZW物理L2源を `f₀`、元の完全transferを `T_{H,β}` と書く。

[AIFの元の定義](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28e8137b8f17cd027981bc9326b22a22f643f29d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean)は、`G=SU(2)`、`ν=normalizedCompactHaar G`、元の単リンクWilsonエネルギー `E` に対して

\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),\qquad
Z_H(\beta)=z(\beta)^{n_H},\qquad
n_H=\#\{\text{元の空間リンク}\}
\]

である。有限積Haarと元の相対ホロノミーに基づく既証明の分配関数を用い、独立プラケット仮定や代替測度は導入しない。

[AIGの元の定義](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28e8137b8f17cd027981bc9326b22a22f643f29d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)は

\[
\varepsilon_H(\beta)
=\frac{\beta Z_H(\beta)e^{-2\beta p_H}V_H}{2},\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_0(B)<-\varepsilon_H(\beta)\}.
\]

AIPは、この `ε` と厳密不等号を保った集合に対する半Haar下界の結合区間を広げる。正結合での `z<1` と、指定区間での旧余裕半Haar下界は、異なる範囲の結論として区別する。

## 2．真正Haar平均1から、全正結合での分配関数の厳密欠損へ

元の単リンクエネルギーは連続で、コンパクトな `G` 上の真正Haarに関して可積分である。[PZ35D4の既証明](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28e8137b8f17cd027981bc9326b22a22f643f29d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarContractionV5_PZ35D4.lean) `p4Q2PZ35D4_originalOneLinkHaar_characterZero` と、元の関数 `χ=1-E` を用いて

\[
0=\int_G(1-E)\,d\nu=1-\int_GE\,d\nu,
\qquad\boxed{\int_GE\,d\nu=1}
\]

を得る。平均1は追加仮定ではなく、元のHaar恒等式からの帰結である。

スカラー補題の仮定は `β≥0` と `0≤x≤2`。`1+βx≤exp(βx)` に正の `exp(-βx)` を掛けると

\[
\beta x e^{-\beta x}\le1-e^{-\beta x}.
\]

さらに `x≤2` より `exp(-2β)≤exp(-βx)` なので

\[
\boxed{\beta e^{-2\beta}x\le1-e^{-\beta x}.}
\]

元の範囲評価 `0≤E(g)≤2` を代入し、可積分性を確認して積分すると

\[
\boxed{z(\beta)\le1-\beta e^{-2\beta}\quad(\beta\ge0).}
\]

したがって **すべての `β>0`** で `z(β)<1`。AIFの既存の正値性と合わせて `0<z(β)<1` となる。欠損量 `βexp(-2β)>0` は明示的であり、正測度集合の存在を新たに仮定しない。

## 3．指定されたスカラー区間での厳密指数評価と元のリンク数

さらに `0<β<1/4` とする。`Real.add_one_le_exp` により

\[
e^{-2\beta}\ge1-2\beta>\frac12,
\qquad
z(\beta)\le1-\beta e^{-2\beta}
<1-\frac\beta2\le e^{-\beta/2}.
\]

この厳密性は `β>0` と `β<1/4` から導かれる。

既存の計数定理 `p4Q2PZ37AHI_cardLinks_eq_plaquettes` を `Nat.card` に接続して

\[
(n_H:\mathbb R)=p_H>0,\qquad n_H>0
\]

を得る。AIFの元の定義 `Z_H=z^{n_H}` と正の整数冪の厳密単調性から、全 `β>0` で `Z_H(β)<1`、さらに `0<β<1/4` で

\[
\boxed{Z_H(\beta)<(e^{-\beta/2})^{n_H}
=e^{-\beta p_H/2}.}
\]

元のリンク数を別の数に置き換えず、元のtransferや物理源を再正規化しない。

## 4．新しい明示上端と、上端でも厳密な分配関数条件

[AIOの旧上端](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28e8137b8f17cd027981bc9326b22a22f643f29d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHalfHaarFullMarginCouplingV5_PZ37AIO.lean)を変更せず、新しい上端を追加する。

\[
\kappa_H=\frac{2\log2}{3p_H},\qquad
\boxed{\lambda_H:=\frac{\log2}{p_H}
=\frac32\kappa_H>\kappa_H>0.}
\]

[AIMの既証明の数え上げ下界](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28e8137b8f17cd027981bc9326b22a22f643f29d/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCauchyCubicSmallCouplingV5_PZ37AIM.lean) `p_H≥24` と `log2≤1` から `λ_H≤1/24<1/4`。したがって **上端を含む区間 `0<β≤λ_H`** 全体で第3節の厳密指数評価を使える。

同区間では `βp_H≤log2` であり、

\[
\boxed{
Z_H(\beta)e^{3\beta p_H/2}
<e^{-\beta p_H/2}e^{3\beta p_H/2}
=e^{\beta p_H}\le2.
}
\]

新上端 `β=λ_H` では最後の比較が等号になるが、前段の分配関数比較は厳密なままである。このため、AIOが要求する厳密条件 `<2` は新上端でも成立する。

## 5．元の全余裕負領域への包含と半Haar下界

AIOの補助評価量は

\[
\delta_H(\beta)=\beta e^{-7\beta p_H/2}V_H>0\quad(\beta>0).
\]

AIOでは、両半重みを保持した元のtransferについて、`f_H(B)≤0` なら `T_{H,β}f₀(B)≤-δ_H(β)`、また元の余裕との正確な関係

\[
2\varepsilon_H(\beta)
=Z_H(\beta)e^{3\beta p_H/2}\delta_H(\beta)
\]

が既に証明されている。第4節の条件によって `ε_H(β)<δ_H(β)` となり、

\[
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta}
\qquad(0<\beta\le\lambda_H)
\]

を得る。旧余裕を縮小せず、源がゼロの境界も含む。源のゼロ集合について追加の測度仮定は置かない。

AINからAIOに保持された真正Haarの源非正集合の下界と、証明済み包含への測度の単調性により

\[
\boxed{0<\beta\le\lambda_H
\quad\Longrightarrow\quad
\frac12\le\mu_H(\mathcal N_{H,\beta}).}
\]

結論は `ℝ≥0∞` 値と実数値 `Measure.real` の両形式である。旧上端 `β=κ_H` の半Haar系と、旧上端より真に大きい新上端 `β=λ_H` の証明書を明示する。新上端の証明書には、上端比較・正結合・厳密分配関数条件・実数値半Haar下界が含まれる。

## 6．保持する範囲、残る課題、宣言対応

AIGの元の余裕と負領域、AIL・AIMの従来の区間での全空間負性とHaar質量1、AINの従来の全正結合結果、AIOの旧開区間と固定 `H=0` の系を保持する。今回広げた区間の結論は、同じ旧全余裕負領域のHaar質量が **少なくとも1/2** というものである。

全 `β>0` での `Z_H(β)<1` だけから、全正結合での `Z_H(β)exp(3βp_H/2)<2` は従わない。本稿の旧余裕半Haar結論は、指定した `0<β≤λ_H` の範囲である。区間の最適性、区間外での不可能性、全正結合での旧余裕半Haar下界や全境界負性は主張しない。

上端 `λ_H` と正の評価量 `δ_H, ε_H` は体積に依存する。体積一様の正の負値余裕、体積一様coercivity、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapへの昇格は行わない。

### 23宣言の対応表

すべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 名前空間、接頭辞 `p4Q2PZ37AIP_`。下表は接頭辞を省略した名前を示す。22定理・1定義の型検査と、対応する23件の実公理出力を認証した。

| # | 宣言名（接頭辞省略） | 内容・必要条件 |
| --- | --- | --- |
| 1 | `originalSingleLinkEnergy_integrable` | 元の単リンクエネルギーの真正Haar可積分性 |
| 2 | `originalSingleLinkEnergy_Haar_mean` | 元のエネルギーのHaar平均は1 |
| 3 | `real_exp_deficit` | `β≥0`, `0≤x≤2` で `βexp(-2β)x≤1-exp(-βx)` |
| 4 | `originalSingleLinkPartition_le_deficit` | `β≥0` で `z(β)≤1-βexp(-2β)` |
| 5 | `originalSingleLinkPartition_lt_one` | `β>0` で `z(β)<1` |
| 6 | `originalSingleLinkPartition_lt_expHalf` | `0<β<1/4` で `z(β)<exp(-β/2)` |
| 7 | `originalLinkCount_eq_plaquettes` | 元のリンク数の実数値は `p_H` |
| 8 | `originalLinkCount_pos` | 元のリンク数は正 |
| 9 | `originalCrossingPartition_lt_one` | `β>0` で `Z_H(β)<1` |
| 10 | `originalCrossingPartition_lt_expHalfCount` | `0<β<1/4` で `Z_H(β)<exp(-βp_H/2)` |
| 11 | `closedHalfHaarCouplingCutoff` | 新定義 `λ_H=log2/p_H` |
| 12 | `closedHalfHaarCouplingCutoff_pos` | `λ_H>0` |
| 13 | `closedCutoff_eq_threeHalf_old` | `λ_H=(3/2)κ_H`、旧定義を保持 |
| 14 | `oldCutoff_lt_closedCutoff` | `κ_H<λ_H` |
| 15 | `closedCutoff_le_oneDiv24` | `λ_H≤1/24` |
| 16 | `coupling_lt_quarter_of_le_closedCutoff` | `β≤λ_H` から `β<1/4` |
| 17 | `originalPartitionCondition_of_le_closedCutoff` | `0<β≤λ_H` でAIOの厳密分配関数条件 `<2` |
| 18 | `originalNegativeMargin_lt_varianceFloor` | 同区間で旧 `ε_H(β)<δ_H(β)` |
| 19 | `originalSource_nonpos_subset_fullNegativeRegion` | 同区間で源非正集合を旧全余裕負領域に包含 |
| 20 | `originalFullNegativeRegion_Haar_half` | 同区間で旧領域の `ℝ≥0∞` 値Haar下界 `1/2` |
| 21 | `originalFullNegativeRegion_realHaar_half` | 同区間で旧領域の実数値Haar下界 `1/2` |
| 22 | `oldEndpoint_fullNegativeRegion_realHaar_half` | 旧上端 `κ_H` で旧領域の実数値Haar下界 `1/2` |
| 23 | `expandedEndpoint_certificate` | 新上端の真の拡大・正値性・厳密条件・半Haarを同時に記述 |

## 7．Exact-source検証と統合の実観測

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `28e8137b8f17cd027981bc9326b22a22f643f29d` |
| [定理PR #6542](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6542) | MERGED |
| 認証対象source HEAD | `6a40f5548a75ae51bec6e0275bbb51c43a23731a` |
| CIの実checkout／test-merge HEAD | `b3b232e7369a9b3945030aac9035f5bb0b04bf2d` |
| 実際の定理squash | `aead92df228c17e125d9b4fe2bb49508ce73a3e2` |
| source／test-merge／実squash共通Git tree | `4fbf3f283f67f77fbb2e661767141f5303438b99` |
| 新規Lean Git blob | `49004405b63265db818d6e08acd8c85617e9393a` |
| 新規Lean SHA256 | `4206ff534e48ee4a17ed186b6c3f28f05858fa8b81bdaec30a94d7613c4de08c` |
| 新規Lean | 320行・22定理・1定義・23公理出力命令・17,312 bytes |
| [CI #42526574075 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42526574075/attempts/1) | completed／SUCCESS |
| 主job | `128871448549`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11,404／11,404 SUCCESS** |
| 新規leaf build | 45秒 |
| 実際の公理出力 | **23／23**、全件 `propext, Classical.choice, Quot.sound` のみ |
| 公理出力の欠落／余分／重複 | 0／0／0 |
| 全実ログのsorryAx | 0 |
| 全実ログのLean error | 0 |
| 変更Lean全文warning／error | 0／0 |
| 独立completion receipt job | `128872654747`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| exact-source status ID | `58380044600` |
| 診断artifact | `13635369392`、129,371 bytes |
| 実ZIP SHA256 | `d976e8bc42097fefa54c325fc522ec4996072f962d964d2a9199db11b4630906` |
| 抽出実ログ | 1,920,853 bytes |
| 抽出実ログSHA256 | `f56eb8d3d685c2245b43973f6ceb50795c56d7f1958dcb7b88fb691ae7df4de1` |

receiptの実出力は `[mcp-receipt] event=pull_request exact_sha=6a40f5548a75ae51bec6e0275bbb51c43a23731a source_result=success run=42526574075 attempt=1`。対象sourceのcommit statusは、この同じrunを指す。

主担当は、完了後の実ジョブログ全文（3,336,517文字）と診断artifactの実bytesを取得した。新規23宣言と実公理出力を名前ごとに一対一で照合し、欠落・余分・重複、標準外公理、sorryAx、Lean error、変更ファイルのwarning/errorがないことを確認した。実ZIP SHA256はGitHub metadataのdigestと一致する。変更ファイルのwarning 0は、既存依存ファイルの再生warningもすべて0という意味ではない。

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。exact sourceの `lean-toolchain` と `lake-manifest.json` を再取得して固定値を照合した。実ジョブログのLean versionとcheckoutも一致する。直接importはAIOとMathlib.Tactic。baseからの差分は新規Lean1件だけ（320行追加・削除0、ahead2／behind0）であり、既存ファイル・workflowの変更はない。

### 初回sourceの警告と修正の履歴

初回source `d22a3bae22cee0520504fd0cb281533e9f38a0db` の [CI #42526133468 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42526133468/attempts/1) は、必須Lean step 17で11,404／11,404のbuildと23件の標準公理出力を完了した。しかし203行目に「ring tactic does nothing」「this tactic is never executed」の2件のwarningがあった。変更全文warning 0の認証条件を満たさないため、初回sourceは認証済みとして扱わない。

全文と既存APIを再確認した結果、`field_simp [hp]` が比の恒等式を既に閉じ、後続の `<;> ring` が不要になっていたことを原因として特定した。修正はこの余分な戦術の除去と、冒頭コメント2行を「上端を含む」と明確化した変更のみである。全23宣言の型・引数・仮定、唯一の定義の値、他の証明、import、局所インスタンス、定数、heartbeat、全公理出力命令は不変である。修正後sourceに対する別run #42526574075の完了を認証対象とする。

初回runは修正push後の後処理中にcancelledとなった。主job `128870046806` の完了ログにもActions cancellationがあり、独立receipt job `128871419034` は `source_result=cancelled` を正確に報告した。旧sourceのstatusはfailure、status IDは `58379890729` である。Lean stepの成功をworkflow全体の成功として扱わない。

初回artifact `13635736413` の実ZIPは131,075 bytes、SHA256は `a8ddde986b946b0385d2712265ec5690149e166b129a39c3aaacb1e6908a1208`、抽出ログは1,927,293 bytes、SHA256は `58b5a039b860ba6a4f480f5832b91aee21828aeb229c536a840abc2145dec420`。初回と認証済みsourceの来歴を区別して保持する。

## 8．独立照合、実squash、正式記録

独立した数理担当とソースレビュー担当が新規Lean全文を読解し、元のHaar平均、スカラー欠損、元の正のリンク数、厳密な冪比較、新上端での厳密性、旧余裕と測度包含を確認した。ソースレビュー担当は修正前後のGitHub本文を直接取得し、変更が上記3行だけで全23宣言の型が不変であることを別途確認した。数学節1–6と23宣言表、その既存APIリンクも独立に照合した。全推移依存ファイルを全文読解したという主張ではない。

独立ログ担当もGitHub MCPから、主ジョブログ全文3,336,517文字、receipt全文9,701文字、exact source、固定環境ファイル、run/jobs、exact-source status、check suiteを別途取得した。23件の実公理出力が各1回で標準3公理のみであること、欠落・余分・重複0、sorryAx・Lean error・Actions error・変更warning/error 0、実checkout、必須step 17、主job全体、receipt step 2の成功を独立に確認した。receiptの実POST応答status IDは `58380044600`。check suite `115193341022` もcompleted／SUCCESS、exact-source HEADが一致し、所属する2件のcheck runはともにcompleted／SUCCESSである。主担当もsourceのcheck-runsおよびcheck-suitesを再取得して照合した。独立ログ担当はZIP hash・Git treeの再監査を行っておらず、それらは主担当が実bytesとGitデータで確認した。receiptは別CIジョブの受領書であり、別の証明カーネルを意味しない。

定理PR #6542の実squash `aead92df228c17e125d9b4fe2bb49508ce73a3e2` を統合後に再取得し、source／test-merge／実squashのGit tree、および新規Leanの本文・Git blobの一致を確認した。squashの唯一の親は元canonical baseである。

[統合済みAIP Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/aead92df228c17e125d9b4fe2bb49508ce73a3e2/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP.lean)。

本記録は、exact-sourceの完了検証、公理出力監査、独立completion receipt、独立読解、実squashのtree/blob一致の後に、別のdocs-only PRで新規追加する。mainには同じ記録Git blobを用いる。既存Lean・既存証明記録・README・ROADMAPを変更せず、docs-onlyのStrict Leanは手動起動しない。既存workflowも変更しない。

