# P4-Q2-PZ37AIN — 任意正結合の指定恒等負境界と半Haar負領域

2026年11月9日 JST ／ Lean4 exact-source検証済み・定理正本統合済み

唯一の定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、符号付きZW物理L²源と既存連続代表、真正空間積Haar、AIGの元の全余裕と負領域、既存定理・仮定、固定Lean/mathlib、workflowを保持した。

## 1．認証済み成果とexact-source証拠

任意の有限 `H : ℕ` と任意の `beta>0` について、元の全リンク恒等配置 `I_H` が元の物理transferの具体的な負境界であることを証明した。積分を含まない初等的な正余裕 `eta_H,beta` により `T_beta f0(I_H)<=-eta_H,beta<0`。さらに、元の源が非正の全境界でtransferは厳密に負となり、ゼロ閾値負集合の真正Haar質量は少なくとも `1/2`。旧全余裕集合への閾値の変更は行わない。

| 項目 | 実観測・照合結果 |
| --- | --- |
| Canonical base | `1e74f814b87352ea877711074a00ad0a3d8a6e0b` |
| [定理PR #6536](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6536) | MERGED |
| 検証済みexact source HEAD | `c2b5321c762e74ece9e7b8fe99311b55329a9380` |
| CIが実際に検査したtest-merge HEAD | `d368532a6d0ee402617aa300d0ad201b99a2c3d6` |
| 実際の定理squash | `484474336273656baff5b64f69375dce0ccdd604` |
| source／test-merge／squashの共通Git tree | `549ca1b5e281d284b84c6e3387f5d7b7a0c4a2ba` |
| 新規Leanの共通Git blob | `00afd9f819da0ec2c9ceaf074a54ee73aa36454e` |
| 新規Lean SHA256 | `4104237870b68f6fe8495ba223b1fdf656c1480a05e8d1fed6eb343629e3c26f` |
| 新規Lean | 532行・26定理・1定義・27公理出力命令 |
| [Exact-source CI #42494514231 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42494514231/attempts/1) | workflow completed／SUCCESS |
| 主job | `128773797229`、completed／SUCCESS |
| 必須Lean step 17 | SUCCESS |
| Lake依存閉包 | **11,402／11,402 SUCCESS** |
| 新規leaf build | 29秒 |
| 実際の公理出力 | **27／27**、すべて `propext, Classical.choice, Quot.sound` のみ |
| 欠落／余分／重複する公理出力 | 0／0／0 |
| 全実ログの `sorryAx` | なし |
| 全実ログのLean error行 | 0 |
| 変更Lean全文のwarning／error | 0／0 |
| 独立completion receipt job／step 2 | `128775230597`、両方completed／SUCCESS |
| receipt実出力 | `exact_sha=c2b5321c762e74ece9e7b8fe99311b55329a9380 source_result=success run=42494514231 attempt=1` |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| 診断artifact | `13623341405`、128,727 bytes |
| artifact ZIP SHA256 | `762e3f74a340d519b37e194c435448f20252fed48243c8276958e26d09a9e4cf` |
| 抽出実ログ | 1,908,807 bytes |
| 抽出実ログ SHA256 | `e794c604d0c137ce8267457aec3c41324ca4c83e4a5e4cdd9e8420d4c783ed55` |

[検証済みLean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/484474336273656baff5b64f69375dce0ccdd604/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN.lean)。直接importはPZ37AIM、PZ37ABP、PZ37AHW2、Mathlib.Tactic。Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` を保持した。baseからexact-sourceまでのcompareはahead 2／behind 0で、新規leaf以外の変更はない。実squashの親は上記canonical baseで、treeとleaf本文・blobは検証sourceと一致した。

### 独立照合の範囲

別担当は、workflow・jobが完了した後の **3,320,459文字の実ジョブログ**を独立に取得し、11,402件のビルド、27件の標準公理のみの実出力、sorryAxなし、Lean errorなし、変更warning/errorなし、正確なcheckout SHAを確認した。receipt実ログと対象commit statusも別に取得して照合した。途中の部分ログを成功根拠にしていない。

主担当は診断artifactの実bytesとGitHub metadataのSHA256を照合し、source／test-merge／実squashのGit treeおよびLean本文・blobの一致を確認した。receiptは別CIジョブによるexact-source結果記録であり、別の証明カーネルを意味しない。変更ファイルのwarning 0は、歴史的依存ファイルの再生warningがすべて0という意味ではない。

数学的内容について、全源畳み込みの正規化と有限和、両端halfweightと符号・余裕、源反転と半Haar測度の担当が分担してソースをレビューした。初回エラーの修正後も関連する既存の型付きAPIを再確認した。本記録の数学的記述とLean本文の範囲も別担当が照合した。読解レビューと機械的証明認証は区別する。

### 初回失敗と修正履歴

初回source `3e567e4db2db994d7a4b53debd97d33cf73e4544` の [CI #42493507004 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42493507004/attempts/1) はcompleted／FAILUREだった。実artifact `13623120931`（131,860 bytes、SHA256 `a40011722c0064e1e911abc18edee5a33aae336d0fb575e5cf70579ddbbfc0d9`）と実ログ（1,920,225 bytes、SHA256 `ae3010f44fd9fd9d3cf1beef7804c968cb93ea2c53794568edf7a49f088d8a89`）を取得し、変更leafの5件のLean errorを確認した。

初回113行では、PW2が保持する有限列挙と現在の有限列挙が、同じ全体集合でも定義的に同一ではないため、`Finset.sum_congr rfl` が失敗した。書かれたnative instance式の一致だけで定義的同一性が得られるとした初回静的レビューの判断を訂正した。既存AHW2と同様、全体finsetの等しさを外延性と所属条件で証明して接続した。

初回147・181行では、連続性の省略した合成表現の型推論が固定 `maxHeartbeats 3900000` に達した。既存ABPの型付き証明に合わせ、`Continuous.comp'` に合成する二つの写像を明示した。上限は増やしていない。

初回355行では、固定mathlibの `mul_lt_mul_left` は全域的な乗法の狭義単調性を要求する補題で、意図した正係数消去の同値補題ではなかった。その結果 `MulRightStrictMono ℝ` の合成に失敗し、続く356行にno-goal診断が出た。既存AIFと同じく、transferが非負だと仮定すれば正の指数との積も非負となり、得られた厳密負性と矛盾するという直接証明へ変更した。

27件の公開宣言の署名、仮定、物理量、定数、直接import、オプションを初回と文字列照合し、すべて同一であることを確認した。固定Lean/mathlib、heartbeat、workflow、証明認証条件は変更していない。変更leaf全文と関連する既存型付きAPIを再確認した。

初回実ログにはコンパイラのエラー回復による `sorryAx` を含む公理出力が16件あった。初回sourceを認証済みとは扱わない。修正版は別source・別CIとして検証し、失敗履歴をPRと本記録に保持する。

## 2．対象と元の量

任意の `H : ℕ` に対する元の有限空間格子と任意の正結合 `beta` を対象とする。`n_H` は元空間リンク型の `Nat.card`、`p_H` はAFZの元plaquette list長の実数値である。元の符号付きZW物理L²源を `f_{0,H}`、AFZの既存連続代表を `f_H`、元の空間Wilson作用を `W_H` と書く。[AGN]・[AHR] により

\[
f_H(A)=\frac{W_H(A)-p_H}{2}
=\sum_{q\in\mathrm{Plaq}_H}\frac{W_q(A)-1}{2},
\qquad |f_H(A)|\le\frac{p_H}{2}.
\]

`mu_H` は元の正規化空間積Haar測度であり、[AHN] の真正源二次モーメントは

\[
V_H=\int f_H(A)^2\,d\mu_H(A)>0.
\]

`T_{H,beta} f_{0,H}(B)` は元の完全Wilson一スラブtransferである。L²同値類の任意の点値を使用せず、[AIF] の既証明代表橋を介して `f_H` の積分に接続する。

## 3．全源の正確な交差核畳み込み

元の全リンク交差核を `K^cross_{H,beta}(A,B)`、[AIF] の正の交差分配を `Z^cross_H(beta)`、[ABN] の真正一リンクWilson係数を `r(beta)` とする。これらは既存定義のままである。

[ABP] は、各元plaquetteの実際の4辺について、全リンクの真正Haar積分を評価し、正規化された畳み込み係数が `r(beta)^4` であることを既に証明している。AINではAIFの一リンク分配とABNの一リンク質量が同じ積分であることを明示し、正の分母を取り除く。次に、各項のコンパクト連続性による可積分性を証明して元plaquetteの有限和を積分の外へ出す。

新定理 `p4Q2PZ37AIN_originalCrossingSource_convolution` は、すべての実結合とすべての元境界 `B` について

\[
\boxed{
\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)\,d\mu_H(A)
=Z^{\mathrm{cross}}_H(\beta)r(\beta)^4f_H(B)
}
\]

を証明する。重なり合うplaquetteの独立性は仮定していない。これは有限和の線形性であり、物理transferや物理測度の再正規化でもない。

## 4．両端halfweightを保持した定量的上界

略記

\[
a=e^{-\beta p_H/2},\qquad
S_{H,\beta}(B)=\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)^2\,d\mu_H(A)
\]

を用いる。左halfweightには元の恒等式

\[
e^{-\beta W_H(A)/2}=a\,e^{-\beta f_H(A)}
\]

を使う。[AIE] の不等式は、`x` の正負を問わず、`|x|<=p_H/2`、`beta>=0` の下で

\[
x e^{-\beta x}\le x-\beta a x^2
\]

を与える。正の交差核を掛けて積分し、[AIF] の右halfweightを含む正確な物理transferの等式と接続すると、AINの `originalRightWeightedTransfer_quadraticUpper` は

\[
\boxed{
e^{\beta W_H(B)/2}T_{H,\beta}f_{0,H}(B)
\le a\left[
Z^{\mathrm{cross}}_H(\beta)r(\beta)^4 f_H(B)
-\beta a S_{H,\beta}(B)
\right]
}
\]

を証明する。右halfweightを戻した `originalTransfer_upper` も証明している。

[AHQ] の元交差作用上界 `Cross_H(A,B)<=2*p_H` から

\[
S_{H,\beta}(B)\ge e^{-2\beta p_H}V_H>0
\]

となる。したがって、`beta>0` なら

\[
\boxed{f_H(B)\le0\ \Longrightarrow\ T_{H,\beta}f_{0,H}(B)<0.}
\]

等号 `f_H(B)=0` の場合も、真正な正のHaar分散による二次項が厳密な負性を与える。この点は単に一次の上界を使うだけでは得られない。

## 5．任意正結合における指定恒等境界と初等的余裕

`I_H := p4Q2PZ37AHN_identity H` は、すべての元空間リンクにSU(2)の恒等元を置く具体的配置である。[AHH] の既存源評価と元の源・作用関係から

\[
W_H(I_H)=0,\qquad f_H(I_H)=-p_H/2
\]

を用いる。AINは、すべての非負結合について

\[
T_{H,\beta}f_{0,H}(I_H)
\le-\frac{p_H}{2}e^{-\beta p_H/2}
Z^{\mathrm{cross}}_H(\beta)r(\beta)^4
\]

を証明する。[AIJ] と [ABN] の既証明下界

\[
Z^{\mathrm{cross}}_H(\beta)\ge e^{-2\beta n_H},\qquad
r(\beta)\ge\frac{\beta e^{-2\beta}}4
\]

を適用し、新しい有限体積余裕を

\[
\boxed{
\eta_{H,\beta}
=\frac{p_H}{2}e^{-\beta p_H/2}e^{-2\beta n_H}
\left(\frac{\beta e^{-2\beta}}4\right)^4
}
\]

と定義する。新定義は `p4Q2PZ37AIN_elementaryIdentityNegativeFloor`。AINは

\[
\boxed{
\beta>0\ \Longrightarrow\
0<\eta_{H,\beta},\qquad
T_{H,\beta}f_{0,H}(I_H)\le-\eta_{H,\beta}<0
}
\]

を証明する。`eta_H(0)=0` も証明済み。この式には未評価の交差分配、源分散、源L1積分、一リンクcharacter積分、Haar球定数が現れない。

元の固定結合 [ADC]

\[
\beta_0=\log(3/2)/64>0
\]

にも適用し、同じ恒等配置に対する厳密負性と初等的余裕の組を独立の定理にした。AIMの小結合区間からの除外と矛盾しない。AINはTaylor剰余の区間条件を使わず、正確な畳み込みと指数不等式を接続している。

## 6．ゼロ閾値負領域の真正Haar質量は少なくとも1/2

[AHW]・[AHW2] の実際のcochain中心捻り `tau_H` は、元の空間Haarを保存し、

\[
f_H(\tau_H B)=-f_H(B)
\]

を満たす。これは源を保存するAHZの別の中心反転とは異なる既存写像である。AINでは

\[
N_H=\{B:f_H(B)\le0\},\qquad
P_H=\{B:0\le f_H(B)\}
\]

を用い、`tau_H^{-1}(N_H)=P_H` と測度保存から `mu_H(N_H)=mu_H(P_H)` を示す。両者の和集合が全空間なので

\[
1\le\mu_H(N_H)+\mu_H(P_H)=2\mu_H(N_H),
\qquad \mu_H(N_H)\ge\frac12.
\]

源のゼロ集合の測度を仮定せず、重なりを許す。第4節の厳密負性を使って

\[
\boxed{
\forall H\in\mathbb N,\ \forall\beta>0,\quad
\frac12\le
\mu_H^{\mathrm{real}}
\left(\{B:T_{H,\beta}f_{0,H}(B)<0\}\right)
}
\]

を証明した。ENNRealの測度と実数値の測度の両形式があり、固定 `beta0` の系もある。

この `1/2` は体積・正結合によらない**ゼロ閾値の負集合のHaar質量**の下界である。負値の大きさやスペクトル量の体積一様下界ではない。

ここで判定しているのは符号付き入力 `f_{0,H}` に対する点ごとの出力の符号である。transfer作用素の負固有値や正定値性の否定を主張しているわけではない。

## 7．保持される旧結果と残る障害

AIGの元の全余裕負領域

\[
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}
\]

は変更していない。新しいゼロ閾値負集合とは異なる。新余裕 `eta_H,beta` と旧余裕 `epsilon_H,beta` の全体積・全正結合での比較は証明していない。したがって、今回の半Haar下界をそのまま旧全余裕領域へ移してはいけない。

AIKまでの元の全余裕領域の初等的正Haar床、AIL・AIMの明示的小結合区間での全空間負性・Haar質量1はそのまま保持される。AINは「具体的な負境界の指定」をすべての正結合に拡張した。

なお未証明として残るのは、正のtransfer境界と正負両符号領域、任意正結合での全境界負性、旧全余裕領域に対する今回の半Haar下界、体積一様の正の負値余裕・coercivity、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapである。有限体積の符号・Haar質量の認証を、これらへ昇格させない。

## 8．公開宣言の監査

すべて `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属し、共通prefixは `p4Q2PZ37AIN_`。26定理と1定義の全27件に、公理出力命令と実ログの出力が一対一で対応する。

| 宣言末尾 | 種別 |
| --- | --- |
| `originalSingleLinkPartition_eq_temporalMass` | 定理 |
| `originalCrossingPartition_eq_temporalMassPower` | 定理 |
| `originalSource_eq_centeredPlaquetteSum` | 定理 |
| `originalCrossingPlaquette_convolution` | 定理 |
| `originalCrossingSource_convolution` | 定理 |
| `originalCrossingKernel_leftContinuous` | 定理 |
| `originalCrossingKernel_pos` | 定理 |
| `originalCrossingKernel_lower` | 定理 |
| `originalCrossingSecondMoment_lower` | 定理 |
| `originalLeftHalfweight_factor` | 定理 |
| `originalRightWeightedTransfer_quadraticUpper` | 定理 |
| `originalRightWeightedTransfer_upper` | 定理 |
| `originalTransfer_upper` | 定理 |
| `originalTransfer_neg_of_source_nonpos` | 定理 |
| `originalIdentity_action_zero` | 定理 |
| `originalIdentityTransfer_le_negativeCoefficient` | 定理 |
| `elementaryIdentityNegativeFloor` | 定義 |
| `elementaryIdentityNegativeFloor_pos` | 定理 |
| `elementaryIdentityNegativeFloor_zero` | 定理 |
| `originalIdentityTransfer_le_negativeElementaryFloor` | 定理 |
| `originalIdentityTransfer_neg` | 定理 |
| `originalFixedIdentityTransfer_neg` | 定理 |
| `originalFixedIdentityTransfer_elementaryCertificate` | 定理 |
| `originalSource_nonpos_Haar_half` | 定理 |
| `originalTransfer_negative_Haar_half` | 定理 |
| `originalTransfer_negative_realHaar_half` | 定理 |
| `originalFixedTransfer_negative_realHaar_half` | 定理 |

## 9．公開記録の扱い

本記録は、定理のexact-source成功と実squashのtree・blob一致を確認した後、新規docs-only PRで追加する。mainへの文書ミラーには同じ記録Git blobを使う。既存README・ROADMAP・証明記録を上書きしない。文書専用PRではStrict Leanを手動dispatchせず、既存の自動workflowの設定も変更しない。

[AGN]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN.lean
[AHR]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalOneCrossingHaarOrthogonalityV5_PZ37AHR.lean
[AHN]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentitySourceHaarMomentV5_PZ37AHN.lean
[ABP]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAllLinkTemporalHaarRestrictionV5_PZ37ABP.lean
[ABN]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN.lean
[AIF]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean
[AIE]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceHaarLaplaceAnticorrelationV5_PZ37AIE.lean
[AHQ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenteredCrossingHaarBudgetV5_PZ37AHQ.lean
[AHH]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH.lean
[AIJ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalPrimitiveNegativeHaarFloorV5_PZ37AIJ.lean
[AIK]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalElementaryNegativeHaarFloorV5_PZ37AIK.lean
[AHW]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterCochainV5_PZ37AHW.lean
[AHW2]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalEvenTorusCenterSourceOddV5_PZ37AHW2.lean
[ADC]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1e74f814b87352ea877711074a00ad0a3d8a6e0b/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingCertificateV5_PZ37ADC.lean
