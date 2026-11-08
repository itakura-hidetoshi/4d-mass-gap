# P4-Q2-PZ37AIG — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元の完全SU(2) Wilson一スラブ作用、両端halfweight、ZW signed source、空間積Haar、物理的transfer、型付き証明履歴、固定Lean/mathlibおよびworkflowを保持する。

## 1．Exact-source形式証明台帳

| 項目 | 確定値 |
| --- | --- |
| [AIG定理PR #6514](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6514) | MERGED |
| 継承したcanonical formal HEAD | `6aaadd0682297dc307ad40da2833b81163f36dfa` |
| 最終exact-source HEAD | `fe76de6aa674af9ef7c0791173eb3cf37127b810` |
| 最終test-merge HEAD | `697ba273324e6221054aa2d950cd5ebf657444fb` |
| 定理squash／定理統合時formal HEAD | `c9b5be1c0f77fbf1d610c94493ddd6348cb921d9` |
| source・test-merge・squash共通Git tree | `35e82ac3b815efe39a3cfb21a43d8dcf3eae0748` |
| 最終Lean Git blob | `21512d119a2b9dd87a5ad4ea90d3595f80b20e40` |
| [最終exact-source CI #42473887497 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42473887497/attempts/1) | completed／SUCCESS |
| Workflow／job | `PR Lean Fast Check`／`Changed Lean fast check` |
| Lean job | `128710774029`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Strict Lean依存閉包 | **11,395／11,395 SUCCESS** |
| 変更AIG leafの実ビルド | **7.8秒**、元のheartbeat上限を保持 |
| 独立completion receipt job | `128712475637`、completed／SUCCESS |
| Receipt実ログ | `exact_sha=fe76de6aa674af9ef7c0791173eb3cf37127b810 source_result=success run=42473887497 attempt=1` |
| Commit status context | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| 新規公開宣言の公理検証 | **21／21**、全件 `propext`・`Classical.choice`・`Quot.sound` のみ |
| 公理出力の欠落／余剰／重複 | **0／0／0** |
| 最終成功ログのsorryAx | **なし** |
| 変更AIG Leanのwarning／error | **0／0** |
| 最終diagnostic artifact | `13614767932`、`lean-fast-check-log` |
| Artifact digest | `sha256:b8b1dcd229435d7593c1fd97f0c7398b8eb1d51dd7e7273e5f2d9791c1cbe271` |
| 新規Leanファイル | **1件・401行、18定理＋3定義** |
| 既存Lean／物理定義／仮定／workflow変更 | なし |

Leanは `v4.30.0-rc2`、実行バイナリcommitは `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`。mathlibは `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。toolchain blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26` とmanifest blob `01260678b674ab241e753563e913c7ce9c6ba659` をcanonical baseで再読し、固定値を確認した。

最終workflow・job・Lean stepがすべて完了してから、完成ログの21公理出力をソースの全21公開宣言および21出力命令と一対一で照合した。独立receiptの実出力、commit status、artifact metadataと実ログのdigestも照合した。別の独立GitHub MCP監査でも同じソース・ログ・receipt・artifactを再取得して確認した。警告0件は変更したAIG leafの値であり、ジョブ全体には再生された依存ファイルの警告等が含まれる。

GitHub MCPで実際のsquash後のtreeとcanonical Lean blobを読み戻し、検証対象との一致を確認した。

[Lean4定理全文（検証済みsquash）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/c9b5be1c0f77fbf1d610c94493ddd6348cb921d9/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)

## 2．保存した失敗履歴と局所修正

| 対象 | 観測された結果 | 扱い |
| --- | --- | --- |
| 初期source `0e34ddea4b0827e96abab91c0266feec8348fb64`、[CI #42472471482 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42472471482/attempts/1) | elan releaseの計5回の取得試行がHTTP 504／502／503で失敗。Lean stepはSKIPPED。 | 証明成否は未認定。同じsourceの失敗ジョブを再実行。 |
| 同source、[CI #42472471482 attempt 2](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42472471482/attempts/2) | 395行の初期leafで1 error、0 warning。152行目の完全kernelと座標交換の合成 `hk` が `isDefEq` の上限3,900,000 heartbeatに到達。leaf実行282秒。 | 全体を不合格とした。依存する連続性・可積分性・開性・可測性の4宣言に現れたerror-recovery `sorryAx` は受理していない。 |
| 修正版source `fe76de6aa674af9ef7c0791173eb3cf37127b810`、CI #42473887497 attempt 1 | 401行、元の上限のまま実ビルド7.8秒。全21宣言が標準公理のみ。 | 本記録の検証済み正本。 |

初期位置の暫定的な読み取りでは直前のsource合成 `hf` を疑ったが、番号付き全文と完成エラーログの照合により、実際の152行目は完全kernelの座標交換合成 `hk` だと訂正した。修正は旧3行を型付きの `hKernel`・`hSwap` と明示的な `Continuous.comp` の9行へ置き換えた箇所だけである。外側関数を `g`、内側の型付き `Prod.swap` を `f` に指定し、関数を未確定のまま完全kernelの定義展開へ進む型照合を避ける構造とした。固定mathlibの [Continuous.comp][ml-continuous] と [continuous_swap][ml-sumprod] の実際の署名を照合した。

数学的主張、物理的定義、仮定、imports、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000` は維持した。最終候補全文を再読してから再検証した。過去のfailed receiptと最終success receiptを混同せず、各試行のworkflow・job・stepの完了を待って判定した。初期sourceと両試行の履歴はPRに保持されている。

## 数学的対象と証拠の範囲

本節は、P4-Q2-PZ37AIG の [401行の検証済みソース][src-aig] に記された数学を説明する。対象の source commit は `fe76de6aa674af9ef7c0791173eb3cf37127b810`、Lean ファイルの blob は `21512d119a2b9dd87a5ad4ea90d3595f80b20e40` である。新規宣言は18定理・3定義で、対応する `#print axioms` は21件ある。コンパイラ検証、実際の axioms 出力、CI の attempt、マージ状態は前掲の検証台帳に記録する。本節の説明だけでそれらの成功を認定しない。

既存定理の参照点は formal 正本の `6aaadd0682297dc307ad40da2833b81163f36dfa` とする。AIG は AIF・AHH・AHL を直接 import し、AIE・AHP・AGN・AHN などの既存の成果をその依存関係から利用する。以下の物理的対象を保持する。

| 記号 | 対象 |
|---|---|
| \(H\in\mathbb N\) | 元の有限体積パラメータ。結論に追加の \(H>0\) 条件はない。 |
| \(\mathrm{Link}_H\) | `PeriodicHypercubicEvenSpatialSliceLink H`。 |
| \(\mathcal C_H\) | `PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2`。 |
| \(\mu_H\) | `periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2`。元の規格化された空間リンク積 Haar 確率測度。 |
| \(W_H\) | `periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2`。 |
| \(p_H\) | `p4Q2PZ37AFZ_plaquetteCount H`。元の空間 plaquette list の長さを実数に写したもの。 |
| \(f_H^0\) | `p4Q2PZ37ZW_originalCenteredPhysicalDirection H`。元の符号付き物理的 \(L^2\) 源。 |
| \(f_H\) | `p4Q2PZ37AFZ_originalCenteredContinuous H`。既存の連続代表で、AGN により \(f_H(A)=(W_H(A)-p_H)/2\)。 |
| \(V_H\) | `p4Q2PZ37AHN_originalSource_HaarSecondMoment H`、すなわち \(\int f_H(A)^2\,d\mu_H(A)\)。AHN の既存定理が \(V_H>0\) を与える。 |
| \(t_{H,\beta}(B)\) | `decomposableOneSliceTransferIntegral H 2 beta f0 B`。元の完全な一層物理的転送。 |
| \(Z_H(\beta)\) | `p4Q2PZ37AIF_originalCrossingPartition H beta`。AIF の実際の交差 Haar 分配積分。全実数 \(\beta\) について正。 |

元の完全なカーネルを \(K_{H,\beta}\) とすると、AHP の代表一致の橋渡しによって、すべての右境界 \(B\) に対し

\[
t_{H,\beta}(B)
=\int_{\mathcal C_H}f_H(A)K_{H,\beta}(A,B)\,d\mu_H(A)
\]

が成立する。カーネルに入る作用は

\[
\frac{W_H(A)}2+S_{\mathrm{cross},H}(A,B)+\frac{W_H(B)}2
\]

であり、左右両方の空間半重みを保持する。この点ごとの転送恒等式により、元の \(L^2\) 源と連続代表の既存の a.e. 一致を正しく用いる。[AHP][src-ahp]、[AGN][src-agn]、[AIF][src-aif]

## 平均の定量上界と明示的な負の余裕

説明用の記号として

\[
w_{H,\beta}(B)=e^{\beta W_H(B)/2},\qquad
\mathcal A_{H,\beta}=\int w_{H,\beta}(B)t_{H,\beta}(B)\,d\mu_H(B)
\]

と置く。\(\mathcal A\) は AIF の `originalRightWeightedTransferAverage` そのものである。AIF の厳密な恒等式と AIE の源 Laplace 評価は、\(\beta\ge0\) のとき

\[
\begin{aligned}
\mathcal A_{H,\beta}
&=Z_H(\beta)e^{-\beta p_H/2}
  \int f_H(A)e^{-\beta f_H(A)}\,d\mu_H(A),\\
\int f_H(A)e^{-\beta f_H(A)}\,d\mu_H(A)
&\le-\beta e^{-\beta p_H/2}V_H
\end{aligned}
\]

を与える。正の係数を掛け、2つの指数を合わせると

\[
\boxed{\mathcal A_{H,\beta}\le-D_{H,\beta}},\qquad
D_{H,\beta}:=\beta Z_H(\beta)e^{-\beta p_H}V_H.
\]

\(D\) はこの記録での略記であり、AIG に追加した定義ではない。\(\beta>0\) では、既存の \(Z_H(\beta)>0\) と \(V_H>0\) により \(D_{H,\beta}>0\) となる。[AIE][src-aie]、[AIF][src-aif]

AIG の新しい余裕は厳密に

\[
\boxed{
\varepsilon_{H,\beta}
=\frac{\beta Z_H(\beta)e^{-2\beta p_H}V_H}{2}
}
\]

である。Lean 名は `p4Q2PZ37AIG_originalNegativeTransferMargin H beta`。\(\beta>0\) で正であり、全実数 \(\beta\) について

\[
\varepsilon_{H,\beta}e^{\beta p_H}=D_{H,\beta}/2
\]

を満たす。これは \(-2\beta p_H+\beta p_H=-\beta p_H\) に対応する。

元の Wilson 作用の上界 \(W_H(B)\le2p_H\) から、\(\beta\ge0\) では

\[
0<w_{H,\beta}(B)\le M_{H,\beta}:=e^{\beta p_H}
\]

を得る。\(M\) も記録上の略記である。平均の評価、余裕の定義、重みの上界は、すべて元の物理的量についての等式・不等式である。\(Z_H\) と \(V_H\) は実際の積分として残り、数値を評価した定数を供給したという意味ではない。[AIG][src-aig]

## 厳密な負領域の正の Haar 測度

AIG の負領域は

\[
\mathcal N_{H,\beta}
:=\{B\in\mathcal C_H\mid t_{H,\beta}(B)<-\varepsilon_{H,\beta}\}
\]

であり、Lean 名は `p4Q2PZ37AIG_originalNegativeTransferRegion H beta` である。

\(\beta>0\) の下で \(\mu_H(\mathcal N_{H,\beta})=0\) と仮定すると、`ae_iff` と `not_le` により

\[
-\varepsilon_{H,\beta}\le t_{H,\beta}(B)
\quad\text{for }\mu_H\text{-a.e. }B
\]

となる。\(w>0\)、\(w\le M\)、\(\varepsilon>0\) を用いると、同じ a.e. 範囲で

\[
-\varepsilon M
\le-\varepsilon w(B)
\le w(B)t(B)
\]

が成立する。最初の不等号は、\(w\le M\) に非正の \(-\varepsilon\) を掛けることによる向きである。

AIF は \(B\mapsto w(B)t(B)\) の可積分性を既に与える。確率測度 \(\mu_H\) 上の定数関数も可積分なので、`integral_mono_ae` により

\[
-\varepsilon M\le\mathcal A_{H,\beta}.
\]

\(\mu_H(\mathcal C_H)=1\) による定数積分と、\(\varepsilon M=D/2\) を用いると

\[
-D/2\le\mathcal A_{H,\beta}\le-D,
\]

となり、\(D>0\) に矛盾する。したがって

\[
\boxed{0<\mu_H(\mathcal N_{H,\beta})}.
\]

\(\mu_H\) は有限測度なので、この集合の測度は \(\infty\) ではない。`ENNReal.toReal_pos` により

\[
\boxed{0<\mu_H.\mathrm{real}(\mathcal N_{H,\beta})}
\]

も得る。集合が空なら測度はゼロになるため、さらに

\[
\exists B\in\mathcal C_H,\quad
t_{H,\beta}(B)<-\varepsilon_{H,\beta}
\]

が従う。AIG では `hEmpty` で空集合との等しさを導き、正測度と矛盾させて存在を抽出する。正測度の証明自体は、新しい full-support 仮定や負の一点からの推測を用いない。[AIG][src-aig]

## 実際の転送関数の連続性と可測性

AIG はすべての実数 \(\beta\) について

\[
B\longmapsto t_{H,\beta}(B)
\]

の連続性を示す。積空間の座標順を \((B,A)\) として

\[
(B,A)\longmapsto f_H(A)K_{H,\beta}(A,B)
\]

が連続であることを、連続代表と元の完全なカーネルの連続性から組み立てる。有限個のコンパクトな \(SU(2)\) の積である \(\mathcal C_H\) と、有限な元の Haar 測度に対して、固定 mathlib の `continuous_parametric_integral_of_continuous` を積分集合 `Set.univ` で適用する。その後、AHP の全右境界における転送恒等式へ接続する。[AIG][src-aig]、[mathlib Bochner.Set][ml-set]

この結果から、すべての実数 \(\beta\) について次が得られる。

- 元の転送関数は \(\mu_H\)-可積分。
- \(\mathcal N_{H,\beta}\) は厳密な不等式の逆像として開集合。
- したがって \(\mathcal N_{H,\beta}\) は可測集合。

連続性・可積分性・開性の結論は全実数の結合に対するものであり、正の余裕と正測度の結論には \(\beta>0\) を用いる。

## 固定結合の球と明示的な質量下界

ここでは既存の `p4Q2PZ37ADC_fixedCoupling`、すなわち \(\beta_0=\log(3/2)/64\) を \(\beta_0\)、\(t_{H,\beta_0}\) を \(t_H\) と書く。結合の定義を変更しない。

既存の全リンク距離と傾きを

\[
\begin{aligned}
D_{\mathrm{sp},H}(B,C)
&:=\texttt{p4Q2PZ37AGG\_originalSpatialChordalDistance H B C},\\
L_H&:=\texttt{p4Q2PZ37AHH\_transferSlope H}
\end{aligned}
\]

とする。この傾きは、元sourceのHaar \(L^1\) 質量 \(M_{\mathrm{src},H}\) を使った \(L_H=(13\beta_0)M_{\mathrm{src},H}\) である。AHH は \(L_H\ge0\) と

\[
|t_H(B)-t_H(C)|\le L_H D_{\mathrm{sp},H}(B,C)
\]

を、元の物理的転送について与える。AHL の元の球は

\[
\operatorname{Ball}_H(B,R)
=\{C\mid D_{\mathrm{sp},H}(B,C)<R\}.
\]

AIG は \(\epsilon>0\) に対して

\[
R_H(\epsilon):=\frac{\epsilon}{2(L_H+1)}>0
\]

を定義する。\(R_H(\epsilon)\,2(L_H+1)=\epsilon\) より

\[
L_HR_H(\epsilon)=\epsilon/2-R_H(\epsilon)<\epsilon/2.
\]

したがって \(t_H(B)<-\epsilon\) なら、球内のすべての \(C\) で

\[
t_H(C)\le t_H(B)+L_HD_{\mathrm{sp},H}(B,C)<-\epsilon/2
\]

となる。[AHH][src-ahh]、[AHL][src-ahl]、[AIG][src-aig]

### 全余裕の領域と半余裕の領域

\(\epsilon_0:=\varepsilon_{H,\beta_0}\) とすると、保証する集合を次のように区別する。

| 集合 | AIG の保証 |
|---|---|
| \(\mathcal N_{H,\beta_0}=\{C\mid t_H(C)<-\epsilon_0\}\) | 開・可測、元の Haar 測度が正。この集合から中心 \(B\) が得られる。 |
| \(\operatorname{Ball}_H(B,R_H(\epsilon_0))\) | 正の半径、正の元の Haar 測度、明示的な質量下界。 |
| \(\{C\mid t_H(C)<-\epsilon_0/2\}\) | 上記の球を含み、その球の明示的な質量下界が移る。 |

球内の符号安定性は半余裕 \(\epsilon_0/2\) に対するものである。全余裕の領域の正測度は先の平均による証明から得られる。AIG は、球の明示的な下界を全余裕の領域にも適用したとは主張しない。

### 球面定数と元の積 Haar 測度

\(n_H:=\operatorname{Nat.card}(\mathrm{Link}_H)\) と置く。使用する既存の ADQ 定数は、正確に

```lean
noncomputable def p4Q2PZ37ADQ_sphereRadiusFraction (r : ℝ) : ℝ :=
  ((Measure.toSphereBallBound 4 r : NNReal) : ℝ) / 4
```

である。第1引数 `4` は実次元、第2引数 `r` が半径で、最後に `4` で割る。ここではこの関数を \(\kappa(r)\) と記す。ADQ は全実数 \(r\) に対する関数値の正性を持つ一方、元の球の質量下界への適用では正の半径を要する。AIG は \(R_H(\epsilon)>0\) と \(n_H+1>0\) によりその条件を満たす。[ADQ][src-adq]、[ADZ][src-adz]

AHL の既存の元の積 Haar 測度の定理を適用すると

\[
\boxed{
\kappa\!\left(\frac{R_H(\epsilon)}{n_H+1}\right)^{n_H}
\le
\mu_H.\mathrm{real}\bigl(\operatorname{Ball}_H(B,R_H(\epsilon))\bigr)
}
\]

となり、球の実数値測度も正である。指数は一つの空間境界のリンク数 \(n_H\)。この \(\kappa\) は既存の球面評価から元の Haar 測度へ運ばれた下界であり、球の測度そのものとの等式ではない。

元の AHL 定理には、その宣言時の `Fintype.card Link` が含まれる。AIG は固定 mathlib の

```lean
theorem Fintype.card_eq_nat_card {_ : Fintype α} :
    Fintype.card α = Nat.card α
```

を `simpa only` で使い、半径の分母と累乗の指数を `Nat.card` にそろえる。この補題は有限型構造を非 instance の暗黙引数として受け取るため、推論された構造と異なる既存の有限型構造にも適用できる。リンクの型、積 Haar 測度、球の定義はそのままである。[mathlib Cardinal.Finite][ml-finite]

最後に \(\epsilon=\epsilon_0\) を代入し、全余裕の負領域から得た中心を使うことで、次を追加仮定なしに一つの存在定理へ閉じる。

\[
\exists B:\quad
\begin{cases}
t_H(B)<-\epsilon_0,\\
R_H(\epsilon_0)>0,\\
\forall C\in\operatorname{Ball}_H(B,R_H(\epsilon_0)),\quad
t_H(C)<-\epsilon_0/2,\\
\kappa(R_H(\epsilon_0)/(n_H+1))^{n_H}
\le\mu_H.\mathrm{real}(\operatorname{Ball}_H(B,R_H(\epsilon_0))),\\
0<\mu_H.\mathrm{real}(\operatorname{Ball}_H(B,R_H(\epsilon_0))).
\end{cases}
\]

## 宣言21件と結論の対応

すべての宣言は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 内にある。下表の全宣言にそれぞれ1件の `#print axioms` が対応する。ここでの件数はソースの宣言・出力指示の対応であり、実際の出力内容は検証台帳で確認する。

| # | 宣言名 | 種別・条件・結論 |
|---:|---|---|
| 1 | `p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance` | 定理。\(\beta\ge0\) で \(\mathcal A\le-D\)。 |
| 2 | `p4Q2PZ37AIG_originalNegativeTransferMargin` | 定義。\(\varepsilon=\beta Z e^{-2\beta p_H}V_H/2\)。 |
| 3 | `p4Q2PZ37AIG_originalNegativeTransferMargin_pos` | 定理。\(\beta>0\) で \(\varepsilon>0\)。 |
| 4 | `p4Q2PZ37AIG_originalNegativeTransferMargin_weightIdentity` | 定理。全実数 \(\beta\) で \(\varepsilon e^{\beta p_H}=D/2\)。 |
| 5 | `p4Q2PZ37AIG_originalRightWeight_le_expCount` | 定理。\(\beta\ge0\)、全右境界で \(w(B)\le e^{\beta p_H}\)。 |
| 6 | `p4Q2PZ37AIG_originalTransfer_continuous` | 定理。全実数 \(\beta\) で元の転送の右境界連続性。 |
| 7 | `p4Q2PZ37AIG_originalTransfer_integrable` | 定理。全実数 \(\beta\) で元の転送の \(\mu_H\)-可積分性。 |
| 8 | `p4Q2PZ37AIG_originalNegativeTransferRegion` | 定義。\(\mathcal N=\{B\mid t(B)<-\varepsilon\}\)。 |
| 9 | `p4Q2PZ37AIG_originalNegativeTransferRegion_isOpen` | 定理。全実数 \(\beta\) で \(\mathcal N\) は開集合。 |
| 10 | `p4Q2PZ37AIG_originalNegativeTransferRegion_measurable` | 定理。全実数 \(\beta\) で \(\mathcal N\) は可測。 |
| 11 | `p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos` | 定理。\(\beta>0\) で \(0<\mu_H(\mathcal N)\)（ENNReal 値）。 |
| 12 | `p4Q2PZ37AIG_originalNegativeTransferRegion_realMeasure_pos` | 定理。\(\beta>0\) で \(0<\mu_H.\mathrm{real}(\mathcal N)\)。 |
| 13 | `p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin` | 定理。\(\beta>0\) で \(t(B)<-\varepsilon\) となる右境界が存在。 |
| 14 | `p4Q2PZ37AIG_originalFixedNegativeTransferRegion_realMeasure_pos` | 定理。既存の固定 \(\beta_0\) における全余裕の負領域の正の実数値 Haar 測度。 |
| 15 | `p4Q2PZ37AIG_originalFixedNegativeBallRadius` | 定義。\(R_H(\epsilon)=\epsilon/[2(L_H+1)]\)。 |
| 16 | `p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos` | 定理。\(\epsilon>0\) で \(R_H(\epsilon)>0\)。 |
| 17 | `p4Q2PZ37AIG_originalFixedNegativeBall_stable` | 定理。\(\epsilon>0\)、\(t_H(B)<-\epsilon\) から球内全点で \(t_H(C)<-\epsilon/2\)。 |
| 18 | `p4Q2PZ37AIG_originalFixedNegativeBall_mass_ge_explicit` | 定理。\(\epsilon>0\)、任意の中心に対する \(\kappa(R_H(\epsilon)/(n_H+1))^{n_H}\) の球質量下界。 |
| 19 | `p4Q2PZ37AIG_originalFixedNegativeBall_mass_pos` | 定理。\(\epsilon>0\)、任意の中心に対する球の正の実数値 Haar 測度。 |
| 20 | `p4Q2PZ37AIG_originalFixedNegativeRegion_mass_of_center` | 定理。\(\epsilon>0\)、\(t_H(B)<-\epsilon\) から、半余裕領域 \(\{C\mid t_H(C)<-\epsilon/2\}\) の明示的質量下界と正測度。 |
| 21 | `p4Q2PZ37AIG_originalFixedTransfer_exists_negativeHaarBall` | 定理。\(\epsilon_0=\varepsilon_{H,\beta_0}\) とその負中心を既存の結論から供給し、中心・正半径・球内負性・明示的質量下界・正測度の存在を閉じる。 |

## 固定 API と使用条件

Lean は `v4.30.0-rc2`、mathlib は `5450b53e5ddc75d46418fabb605edbf36bd0beb6` を前提とする。AIG は次の既存 API の条件をそのまま満たす。

| API | 使用した条件・役割 |
|---|---|
| `p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance H beta hbeta` | `hbeta : 0 ≤ beta`。本来の源 Laplace 積分に対する分散による上界。 |
| `p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace H beta` | 全実数の結合。元の転送平均と源 Laplace 積分の厳密な橋渡し。 |
| `p4Q2PZ37AIF_originalRightWeightedTransfer_integrable H beta` | AIF で証明済みの元の重み付き転送の可積分性。AIG の `integral_mono_ae` に渡す。 |
| `p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B` | 全実数の結合・全右境界。物理的 \(L^2\) 源と連続代表を接続する。 |
| `continuous_parametric_integral_of_continuous` | `Continuous f.uncurry`、積分集合の `IsCompact`、第一可算・局所コンパクトなパラメータ空間、`SecondCountableTopologyEither`、`IsLocallyFiniteMeasure`。元の有限積と有限 Haar 測度で満たし、`s := Set.univ` を使う。 |
| `integral_mono_ae` | 比較する両関数の `Integrable` と a.e. 不等式。定数関数と AIF の重み付き転送を比較する。 |
| `integral_const`・`probReal_univ` | 定数積分を `μ.real Set.univ • c` とし、確率測度で \(c\) に簡約する。 |
| `ENNReal.toReal_pos` | 測度がゼロでなく、かつ無限大でないこと。後者は `measure_ne_top` で満たす。 |
| `measureReal_mono` | 集合包含と上側の有限測度。球の質量下界を半余裕領域へ運ぶ。 |
| `p4Q2PZ37AHH_originalTransfer_allLinkSlope H B C` | 既存の固定 \(\beta_0\)、元の源、元の全リンク距離に対する傾き評価。 |
| `p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B R hR` | 元の球・元の \(\mu_H\)、`hR : 0 < R`。`Fintype.card_eq_nat_card` で同じ有限リンク数を表す。 |

`ae_iff` による零測度の補集合への移行、有限測度を要する実数値測度の単調性、物理的転送との代表一致をそれぞれ独立に使用している。これらを置き換える新しい物理的仮定はない。[AIG][src-aig]、[mathlib Bochner.Basic][ml-basic]、[mathlib Measure.Real][ml-real]

## 主張していない範囲

本成果が扱うのは、各有限 \(H\)、各 \(\beta>0\) に対する元の転送の定量的負領域と、その正の元の Haar 測度である。固定結合ではさらに元の全リンク球と明示的な質量下界を持つ。

以下はこの成果から認定しない。

- 正の転送値を持つ右境界の存在、および正負両符号の領域・shell。
- 中心境界の具体的なリンク値、数値評価された境界、評価済みの符号表。
- \(H\) に一様な負の余裕、半径、Haar 質量下界、coercivity。
- Hamiltonian のスペクトルギャップ、および連続極限の Yang–Mills 質量ギャップ。
- \(\beta\le0\) に対する厳密な負性・正測度。全実数に対する連続性とは条件が異なる。

中心の存在は正測度からの存在命題であり、中心を数値的に選択したという結論ではない。\(Z_H\)、\(V_H\)、\(p_H\)、\(L_H\) と有限リンク数を含む定量式の体積依存性は保持する。ソースだけの積分評価を物理的転送の主張へ移す箇所は、既存の AIF 恒等式と AHP の代表一致によって明示されている。

[src-aig]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/fe76de6aa674af9ef7c0791173eb3cf37127b810/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean
[src-aif]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean
[src-aie]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSourceHaarLaplaceAnticorrelationV5_PZ37AIE.lean
[src-ahp]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFirstOrderHaarExpansionV5_PZ37AHP.lean
[src-agn]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN.lean
[src-ahh]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH.lean
[src-ahl]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL.lean
[src-adq]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSphereHaarBridgeV5_PZ37ADQ.lean
[src-adz]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/6aaadd0682297dc307ad40da2833b81163f36dfa/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUnconditionalHaarRadiusV5_PZ37ADZ.lean
[ml-set]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean
[ml-basic]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean
[ml-real]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean
[ml-finite]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/SetTheory/Cardinal/Finite.lean

[ml-continuous]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Continuous.lean
[ml-sumprod]: https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Constructions/SumProd.lean
