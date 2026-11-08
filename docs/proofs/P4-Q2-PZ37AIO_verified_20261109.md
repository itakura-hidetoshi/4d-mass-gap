# P4-Q2-PZ37AIO — 旧全余裕負領域の半Haar下界と明示的結合区間

2026年11月9日 JST ／ Lean4 exact-source検証済み・定理正本統合済み

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、符号付きZW物理L²源と既存連続代表、真正空間積Haar、AIGの元の全余裕と厳密負領域、既存定理・仮定、固定Lean/mathlib、heartbeat、workflowを保持する。

## 1．今回接続する二つの領域

AINは、任意の正結合で、源が非正の集合がゼロ閾値のtransfer負集合に含まれ、その真正Haar質量が少なくとも1/2になることを証明した。一方、AIGの旧全余裕負領域には正の閾値があり、この二つは同じ集合ではない。

AIOは旧閾値を変更せず、源の非正領域がその旧全余裕負領域に含まれるための明示的な十分条件を導く。条件を結論として証明する段階と、その条件の下で測度を移す段階を分ける。

任意の有限 `H : ℕ` について、元のplaquette数を `p_H>0`、空間作用を `W_H`、元の符号付きZW源の連続代表を

\[
f_H(A)=\frac{W_H(A)-p_H}{2},\qquad
V_H=\int f_H(A)^2\,d\mu_H(A)>0
\]

と書く。`mu_H` は元の正規化空間積Haar、`T_{H,beta}f_{0,H}` は元の完全Wilson transferである。AIGの定義をそのまま用いて

\[
\varepsilon_{H,\beta}
=\frac{\beta Z^{\mathrm{cross}}_H(\beta)e^{-2\beta p_H}V_H}{2},\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}.
\]

新しい定量評価は、この既存の `originalNegativeTransferMargin` と `originalNegativeTransferRegion` を直接参照する。

## 2．源の非正領域における定量的な負値上界

源と作用の既証明恒等式から

\[
f_H(B)\le0\quad\Longrightarrow\quad W_H(B)\le p_H.
\]

AINの二次上界と、同じ元交差核での二次モーメント下界を用いる。

\[
\begin{aligned}
e^{\beta W_H(B)/2}T_{H,\beta}f_{0,H}(B)
&\le e^{-\beta p_H/2}
\left[Z^{\mathrm{cross}}_H(\beta)\rho_\beta^4 f_H(B)
-\beta e^{-\beta p_H/2}S_{H,\beta}(B)\right],\\
S_{H,\beta}(B)&\ge e^{-2\beta p_H}V_H.
\end{aligned}
\]

`beta>0`、`f_H(B)<=0` では第一項が非正であり、

\[
e^{\beta W_H(B)/2}T_{H,\beta}f_{0,H}(B)
\le-\beta e^{-3\beta p_H}V_H.
\]

右halfweightを正確に戻す。`W_H(B)<=p_H` により
`exp(-beta*W_H(B)/2)>=exp(-beta*p_H/2)` となり、負の量を掛ける不等号の向きを保って

\[
\boxed{
f_H(B)\le0\quad\Longrightarrow\quad
T_{H,\beta}f_{0,H}(B)\le-\delta_{H,\beta},\qquad
\delta_{H,\beta}=\beta e^{-7\beta p_H/2}V_H>0.
}
\]

`delta` は新しい補助評価量 `sourceNonpositiveVarianceFloor` であり、旧 `epsilon` の再定義ではない。指数の `7/2` は、左halfweightと二次項に由来する `1`、元交差核下界の `2`、この領域での右halfweightの `1/2` を合計したものである。

## 3．旧全余裕との正確な比較

AIOの `originalNegativeMargin_ratio_identity` は、すべての実結合について

\[
\boxed{
2\varepsilon_{H,\beta}
=\left[Z^{\mathrm{cross}}_H(\beta)e^{3\beta p_H/2}\right]\delta_{H,\beta}
}
\]

を証明する。元の交差分配関数と真正源分散を保持した恒等式であり、近似や源の独立性の仮定はない。

したがって、正結合での明示的な十分条件は

\[
\boxed{Z^{\mathrm{cross}}_H(\beta)e^{3\beta p_H/2}<2.}
\]

この条件と `delta>0` から `epsilon<delta` を証明し、

\[
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta}
\]

を得る。ここで既存AIGの厳密不等号 `T<-epsilon` を保つ。源がゼロの境界も含まれ、源のゼロ集合の測度には条件を追加しない。

AINの真正Haarを保存する源反転から得られた

\[
\frac12\le\mu_H\{B:f_H(B)\le0\}
\]

を、この証明済み包含に対して測度の単調性で移し、

\[
\boxed{
\beta>0,\quad Z^{\mathrm{cross}}_H(\beta)e^{3\beta p_H/2}<2
\quad\Longrightarrow\quad
\frac12\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta}).
}
\]

ENNReal形式と実数値測度形式の両方がある。条件が満たされるか未確認の結合に、この結論を移してはいけない。

## 4．積分を含まない明示的な開区間

AILの既証明の元分配関数評価 `Zcross_H(beta)<=1` を用いて

\[
\boxed{
\kappa_H:=\frac{2\log2}{3p_H}>0,\qquad
0<\beta<\kappa_H
\quad\Longrightarrow\quad
\frac12\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta}).
}
\]

新定義は `halfHaarCouplingCutoff`。この区間の式には源分散・源L1積分・分配関数積分・Haar球定数が現れない。任意有限体積で `kappa_H/2` が正の具体的内部結合となることと、その結合での半Haar証明書も構成する。

上端は**開区間**である。`beta=kappa_H` では、今回使用した `Zcross<=1` のみからは必要な厳密比較が得られない。この原稿は上端の認証を主張しない。それは上端で結論が不可能だと証明したという意味でもない。

## 5．既存AIM区間と固定結合との関係

AIMの旧三次小結合端点を `theta_H` とする。その既存定義と `0<u_H<=1` から

\[
\theta_H=\frac{u_H}{16p_H+1}
\le\frac1{16p_H+1}
<\frac1{3p_H}
\le\frac{2\log2}{3p_H}=\kappa_H.
\]

最後の評価は、固定mathlibの `Real.one_sub_inv_le_log_of_pos` から `log2>=1/2` を用いる。したがって新しい半Haar区間は、AIMの旧区間（上端を含む）`0<beta<=theta_H` を厳密に含む。ただし結論の強さも区別する。旧区間では従来どおり全空間負性とHaar質量1が保たれ、新たに広げた区間で今回得られる下界は1/2である。

元の最小有限体積 `H=0` では、AIBの正確な数え上げにより `p_0=24`。元の固定結合

\[
\beta_0=\frac{\log(3/2)}{64}
<\frac{\log2}{36}=\kappa_0
\]

を証明する。これにより、元の `beta0` における旧全余裕負領域の半Haar下界を **H=0** で認証する。この固定結合での系は全体積への主張ではない。

## 6．保持する結果と残る課題

AIGの元の全余裕と負領域、AIKの初等的正Haar床、AIL・AIMの小結合全空間負性・Haar質量1、AINの任意正結合での恒等配置の厳密負性・初等的恒等余裕・ゼロ閾値負集合の半Haar下界は、そのまま保持される。

今回の旧全余裕での `1/2` は、指定した条件内での集合のHaar質量の下界である。`kappa_H` は体積依存し、`delta` と旧 `epsilon` の正の大きさも体積依存する。体積一様の正の負値余裕やcoercivityではない。

任意正結合での旧全余裕半Haar下界、任意正結合での全境界負性、正のtransfer境界・正負両符号領域、体積一様coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは未証明として残る。符号付き入力への点ごとの出力評価を、作用素の負固有値やmass gapへ昇格させない。

## 7．検証・統合証拠

### Exact-source完了後の実観測

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `28704838bf16b2df120bfa3d03b279738683b170` |
| [定理PR #6539](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6539) | MERGED |
| 検証済みsource HEAD | `2d2ab7bf13911af96d0c925191e690a3b878a4ac` |
| CIの実checkout／test-merge HEAD | `a445f7158da33c9c4dacdcf4130ec8ff9bee3cf8` |
| 実際の定理squash | `e30e453750e71f7a79feef9baa977c366996622f` |
| source／test-merge／実squash共通Git tree | `bc0c6288e8485b3ce454e3abf1ce53c8fe947d5e` |
| 新規Lean Git blob | `a76d453c523931a66110986d8e6b4a15a7455bc2` |
| 新規Lean SHA256 | `3a71d1c3598c0c4576069fd1d78b30df9f5043836ff345c2b9a76b05247b77ae` |
| 新規Lean | 354行・18定理・2定義・20公理出力命令 |
| [CI #42523704763 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42523704763/attempts/1) | workflow completed／SUCCESS |
| 主job | `128862516986`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11,403／11,403 SUCCESS** |
| 新規leaf build | 21秒 |
| 実際の公理出力 | **20／20**、全件 `propext, Classical.choice, Quot.sound` のみ |
| 欠落／余分／重複 | 0／0／0 |
| 全実ログのsorryAx | 0 |
| 全実ログのLean error | 0 |
| 変更Lean全文warning／error | 0／0 |
| 独立completion receipt job | `128863842279`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| 診断artifact | `13634801024`、129,353 bytes |
| 実ZIP SHA256 | `e82d3e5d6e546fa44617568b8f30772b96d023b612a760488b3ab9660deefa62` |
| 抽出実ログ | 1,914,432 bytes |
| 抽出実ログSHA256 | `5663f84c5a8fd043309185b5e15cb4a91230daf7bc6dcf82e2648370fcf91073` |

receipt実出力は `exact_sha=2d2ab7bf13911af96d0c925191e690a3b878a4ac source_result=success run=42523704763 attempt=1`。対象sourceのcommit statusは、この同じrunを指す。

主担当は、完了後の3,328,994文字の実ジョブログおよび診断artifactの実bytesを取得した。20件の実公理出力を新規宣言と一対一で照合し、名前の欠落・余分・重複、標準外公理、sorryAx、全Lean error、変更ファイルのwarning/errorがないことを確認した。artifactの実ZIP SHA256はGitHub metadataと一致する。変更ファイルのwarning 0は、古い依存ファイルの再生warningもすべて0という意味ではない。

直接importはPZ37AINとMathlib.Tactic。固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。実ジョブログにもLean 4.30.0-rc2が記録され、base/sourceの差分は新規Lean1件のみ（354行追加・削除0、ahead1／behind0）である。初回sourceがattempt1で成功し、証明修正のための条件・定数・環境の変更は行っていない。

### 独立照合と統合後の確認

独立ログ担当もGitHub MCPから主ジョブ全文（3,328,994文字）、receipt全文、source、run/jobs APIを別に取得した。20件の実公理出力と名前ごとの一対一対応、標準3公理のみ、sorryAx・Lean error・Actions error・変更warningの不存在、実checkout、必須Lean step 17、ジョブ全体、receipt step 2の成功を独立に確認した。receipt実POST応答のstatus IDは `58378958434`、exact-source・run・attempt・successが一致した。この担当はZIP hashやtreeを再監査していない。それらは主担当が実bytes・GitHub Gitデータ・統合後本文で別途確認した。receiptは別CIジョブの受領書であり、別の証明カーネルを意味しない。

数理担当と別のソースレビュー担当が、新規Lean全文の指数評価・符号・旧余裕・測度包含・区間・固定H=0の系を読解した。直接importのAIN全文と、使用するAIG・AIL・AIM・AIBの関連定義・型付き署名を照合した。全推移依存ファイルの全文読解を主張するものではない。正式記録の数学節1–6と20宣言表も独立に照合し、区間の呼称を「旧区間（上端を含む）」と明確化した。認証済みLeanの変更はない。

定理PR #6539の実squash `e30e453750e71f7a79feef9baa977c366996622f` は元canonical baseを唯一の親とする。統合後にGit commitと新規Leanを再取得し、source／test-merge／実squashのGit tree、および新規Lean本文・Git blobが完全一致することを確認した。

[統合済みAIO Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/e30e453750e71f7a79feef9baa977c366996622f/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHalfHaarFullMarginCouplingV5_PZ37AIO.lean)。


## 8．公開宣言と一次ソース

namespaceは `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`。すべての新規定理・定義を公理監査の対象とする。

| 宣言末尾（共通prefix `p4Q2PZ37AIO_`） | 種別 |
| --- | --- |
| `sourceNonpositiveVarianceFloor` | 定義 |
| `sourceNonpositiveVarianceFloor_pos` | 定理 |
| `originalAction_le_count_of_source_nonpos` | 定理 |
| `originalRightWeightedTransfer_le_negativeVariance` | 定理 |
| `originalTransfer_le_negativeVarianceFloor` | 定理 |
| `originalNegativeMargin_ratio_identity` | 定理 |
| `originalNegativeMargin_lt_varianceFloor` | 定理 |
| `originalSource_nonpos_subset_fullNegativeRegion` | 定理 |
| `originalFullNegativeRegion_Haar_half_of_partition` | 定理 |
| `originalFullNegativeRegion_realHaar_half_of_partition` | 定理 |
| `halfHaarCouplingCutoff` | 定義 |
| `halfHaarCouplingCutoff_pos` | 定理 |
| `originalPartitionCondition_of_below_cutoff` | 定理 |
| `originalSource_nonpos_subset_fullNegativeRegion_of_below_cutoff` | 定理 |
| `originalFullNegativeRegion_Haar_half` | 定理 |
| `originalFullNegativeRegion_realHaar_half` | 定理 |
| `oldCubicSmallCoupling_lt_halfHaarCutoff` | 定理 |
| `halfCutoff_certificate` | 定理 |
| `originalFixedCoupling_lt_cutoff_at_zero` | 定理 |
| `originalFixedFullNegativeRegion_realHaar_half_at_zero` | 定理 |

主要な既存根拠は次の固定canonical sourceにある。

- [AINのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28704838bf16b2df120bfa3d03b279738683b170/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN.lean)。
- [AIGのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28704838bf16b2df120bfa3d03b279738683b170/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)。
- [AILのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28704838bf16b2df120bfa3d03b279738683b170/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExplicitSmallCouplingFullNegativeRegionV5_PZ37AIL.lean)。
- [AIMのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28704838bf16b2df120bfa3d03b279738683b170/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCauchyCubicSmallCouplingV5_PZ37AIM.lean)。
- [AIBのLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/28704838bf16b2df120bfa3d03b279738683b170/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB.lean)。
- [固定mathlibの対数API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)：`Real.one_sub_inv_le_log_of_pos`、`Real.log_lt_log`、`Real.log_pos`、`Real.exp_log`。


## 9．正式記録とmainミラー

本記録は、定理のexact-source検証・全公理出力監査・独立completion receipt・独立読解・実squashのtree/blob一致を確認した後、別のdocs-only PRで新規追加する。mainには同じ記録Git blobを用いる。既存Lean・既存記録・README・ROADMAPは変更しない。docs-onlyではStrict Leanを手動起動せず、既存workflowも変更しない。
