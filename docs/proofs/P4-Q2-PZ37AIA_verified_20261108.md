# P4-Q2-PZ37AIA — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub main は正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の空間積Haar、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証済みの結果 |
| --- | --- |
| [AIA定理PR #6496](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6496) | **MERGED** |
| 継承元AHZ正式記録HEAD | `d09309435fe65026b91fbd3183f5bbfb9553b50e` |
| 最終exact-source HEAD | `0ab58a6752957a39504b031f538fa5a8680ee1c6` |
| exact test-merge HEAD | `d3b5f885c494d5f7ccde3218a219998e95c10912` |
| 定理squash HEAD | `5b1e9602e85d802a1f6c26bc86184591a7714e16` |
| source／test-merge／squash共通Git tree | `ad173ba82d4e255ead7cf5eed584ee59b7e794fd`、完全一致 |
| 最終exact-source CI | [#42442712302](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42442712302) — **completed／SUCCESS** |
| Changed Lean job・Lean step 17 | `128615140164` — **completed／SUCCESS** |
| 独立completion receipt job | `128616212191` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,389／11,389 SUCCESS** |
| 新規定理の公理確認 | **34／34**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13601947793`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・687行**、既存ファイル変更なし |
| 新規Lean blob | `b1df1c92faabd2d62b6fcf683aa8cb05bc3ea5ea`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログの最終結果は `Build completed successfully (11389 jobs).`。変更ファイルの34定理を個別に確認。既存依存ファイルの歴史的warningと今回の変更ファイルのwarningを区別する。

成功artifactのdigest：`sha256:bfceffb640c1177e21ce9a5a1283a1730f28a1534f1893fd3b2cd72626608e6d`。CI workflow、Lean job、必須Lean step 17、独立receiptがそれぞれ完了した状態で成功を確認し、receiptのtarget URLも同一の最終runである。source／test-merge／squash treeの一致をGitHub MCPで直接確認した。

## 2．元の作用・source・Haar・物理的転送

任意の有限の元格子パラメータ $H\in\mathbb N$ を固定する。配置空間は `PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2`、$\mu_H$ は `periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2` である。元の正規化 SU(2) 有限積 Haar 測度を用いる。

$W_H$ を元の空間 Wilson action、$S_H^{\mathrm{cross}}$ を元の temporal crossing action、$p_H$ を元の空間 plaquette 数とする。既存の exact count により、$p_H$ は元の crossing link 数にも等しい。元の連続 source と完全作用は

$$
f_H(A)=\frac{W_H(A)-p_H}{2},\qquad
S_H(A,B)=\frac12W_H(A)+S_H^{\mathrm{cross}}(A,B)+\frac12W_H(B).
$$

source は `p4Q2PZ37AFZ_originalCenteredContinuous H`、物理的な $L^2$ 方向 $f_0$ は `p4Q2PZ37ZW_originalCenteredPhysicalDirection H` である。AHP の Haar-a.e. 代表元の接続を通じて、元の物理的転送 `decomposableOneSliceTransferIntegral H 2` は

$$
T_\beta f_0(B)
=\int f_H(A)K_\beta(A,B)\,d\mu_H(A),\qquad
K_\beta(A,B)=e^{-\beta S_H(A,B)}
$$

に一致する。両境界の空間半重みを含む同じ完全作用、同じ符号付き source、同じ Haar 測度を保持する。

以下、

$$
V_H:=\int f_H^2\,d\mu_H>0,\qquad
M_H:=\int|f_H|\,d\mu_H,\qquad
L_H(B):=3p_H+W_H(B)
$$

と書く。AHY の境界依存作用予算と既存の大域予算は

$$
C_{H,B}:=3p_H+\frac{W_H(B)}2,\qquad
C_{\mathrm{slab},H}=4p_H,\qquad
0\le S_H(A,B)\le C_{H,B}\le C_{\mathrm{slab},H}
$$

である。$C_{H,B}$ は作用の証明された上界であり、実現される最大値という主張はしない。[AIA] [AHY]

## 3．任意の実数 $\beta$ に対する厳密な三次展開

AHX の二次中心を

$$
Q_{2,H}(\beta,B)
=-\beta V_H+\frac{\beta^2}{2}L_H(B)V_H
$$

とし、AHZ の元の符号付き完全作用三次モーメントを

$$
M_{3,H}^{\mathrm{full}}(B)
:=\int f_H(A)S_H(A,B)^3\,d\mu_H(A)
$$

とする。AIA の三次中心は

$$
\boxed{
P_{3,H}(\beta,B)
=Q_{2,H}(\beta,B)-\frac{\beta^3}{6}M_{3,H}^{\mathrm{full}}(B).
}
$$

定義は `p4Q2PZ37AIA_originalCubicApproximation` である。

スカラーの三次多項式を $q_3(x)=1-x+x^2/2-x^3/6$ と書く。新しい剰余は、実際の kernel 差を元の source に掛けた積分

$$
\boxed{
R_{4,H}(\beta,B)
:=\int f_H(A)\bigl[K_\beta(A,B)-q_3(\beta S_H(A,B))\bigr]\,d\mu_H(A)
}
$$

として定義する。Lean 定義は `p4Q2PZ37AIA_originalFourthOrderRemainder` である。

AHY の元の $R_3$ 被積分関数の可積分性と、AHZ の $f_HS_H^3$ の可積分性を用い、被積分関数の代数恒等式を積分すると

$$
\boxed{
R_{4,H}(\beta,B)
=R_{3,H}(\beta,B)+\frac{\beta^3}{6}M_{3,H}^{\mathrm{full}}(B)
}
$$

を得る。対応する宣言は `p4Q2PZ37AIA_originalFourthOrderRemainder_integrable` と `p4Q2PZ37AIA_originalFourthOrderRemainder_eq_third_add` である。AHX の厳密な転送・剰余の接続を用いると

$$
R_{4,H}(\beta,B)=T_\beta f_0(B)-P_{3,H}(\beta,B)
$$

となる。これが `p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub` であり、従って

$$
\boxed{
T_\beta f_0(B)
=-\beta V_H+\frac{\beta^2}{2}L_H(B)V_H
-\frac{\beta^3}{6}M_{3,H}^{\mathrm{full}}(B)
+R_{4,H}(\beta,B).
}
$$

`p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion` までのこれらの可積分性・恒等式は、すべて任意の実数 $\beta$ に対する結果である。$\beta\ge0$ は、この後の剰余の符号と上界に用いる。[AIA]

### AHZ の係数を代入した形

$X_H(A,B):=S_H^{\mathrm{cross}}(A,B)-p_H$ と置く。AHZ は、実際の積分

$$
Q_{4,H}:=\int f_H^4\,d\mu_H\ge0,\qquad
D_H(B):=\int f_H(A)^2X_H(A,B)^2\,d\mu_H(A)\ge0
$$

を保持して、

$$
M_{3,H}^{\mathrm{full}}(B)
=Q_{4,H}+\frac34L_H(B)^2V_H+3D_H(B)>0
$$

を与える。`p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion_exactCubic` は、この恒等式をそのまま代入した

$$
\boxed{
T_\beta f_0(B)
=-\beta V_H+\frac{\beta^2}{2}L_H(B)V_H
-\frac{\beta^3}{6}
\left[Q_{4,H}+\frac34L_H(B)^2V_H+3D_H(B)\right]
+R_{4,H}(\beta,B)
}
$$

である。$Q_{4,H}$ と $D_H(B)$ の個別の数値評価は、この代入によって追加されない。[AIA] [AHZ]

## 4．非負のスカラー四次剰余

$$
r_4(x):=e^{-x}-\left(1-x+\frac{x^2}{2}-\frac{x^3}{6}\right)
$$

と置く。`p4Q2PZ37AIA_exp_neg_quarticRemainder` は全半直線 $x\ge0$ で

$$
\boxed{0\le r_4(x)\le\frac{x^4}{24}}
$$

を与える。下界は AHX の二次多項式の剰余上界から得る。上界では

$$
r_4'(x)=1-x+\frac{x^2}{2}-e^{-x}\le\frac{x^3}{6}
$$

という AHX の結果を用い、$r_4(0)=0$ と $(x^4/24)'=x^3/6$ を導関数比較に接続する。

$\beta\ge0$ と $S_H(A,B)\ge0$ により $x=\beta S_H(A,B)$ を代入でき、`p4Q2PZ37AIA_originalKernel_thirdOrder_signedInterval` は

$$
0\le K_\beta(A,B)-q_3(\beta S_H(A,B))
\le\frac{(\beta S_H(A,B))^4}{24}
$$

を与える。この評価に $\beta C_{H,B}\le1$ などの小ささの仮定や指数関数の損失係数はない。ただし、元の source は符号を持つため、被積分 kernel 誤差の非負性を $R_{4,H}\ge0$ に読み替えることはできない。[AIA]

## 5．四次 source/action 相関と符号付き区間

AHY の source 部分

$$
f_+(A)=\frac{|f_H(A)|+f_H(A)}2,\qquad
f_-(A)=\frac{|f_H(A)|-f_H(A)}2
$$

を引き継ぐ。両者は非負で $f_H=f_+-f_-$ を満たす。元の Haar 中心化により、重みを掛けない質量は

$$
\int f_+\,d\mu_H=\int f_-\,d\mu_H=\frac{M_H}{2}
$$

である。[AHY]

AIA は四次の実際の相関を

$$
\begin{aligned}
J_{4,+}(B)&:=\int f_+(A)S_H(A,B)^4\,d\mu_H(A),\\
J_{4,-}(B)&:=\int f_-(A)S_H(A,B)^4\,d\mu_H(A),\\
J_{4,\mathrm{abs}}(B)&:=\int |f_H(A)|S_H(A,B)^4\,d\mu_H(A)
\end{aligned}
$$

と定義する。対応する定義は `p4Q2PZ37AIA_originalPositiveActionFourthMoment`、`p4Q2PZ37AIA_originalNegativeActionFourthMoment`、`p4Q2PZ37AIA_originalAbsoluteActionFourthMoment`。連続性とコンパクト性から可積分性を得て、非負性と

$$
J_{4,+}(B)+J_{4,-}(B)=J_{4,\mathrm{abs}}(B)
$$

を示す。四次で重みを掛けた二部分の等値や大小関係は仮定しない。

非負の誤差 $0\le r\le d$ に対する実数の補題

$$
-f_-d\le fr\le f_+d
$$

を積分すると、$\beta\ge0$ に対して

$$
\boxed{
-\frac{\beta^4}{24}J_{4,-}(B)
\le R_{4,H}(\beta,B)
\le\frac{\beta^4}{24}J_{4,+}(B)
}
$$

となる。これは `p4Q2PZ37AIA_real_signedNonnegativeError_interval` と `p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval` に対応する。下端は負の source 部分、上端は正の source 部分が担う。AHY の非正の三次剰余から向きが入れ替わる。

加えて、`p4Q2PZ37AIA_originalFourthOrderRemainder_abs_weightedBound` は

$$
|R_{4,H}(\beta,B)|
\le\frac{\beta^4}{24}J_{4,\mathrm{abs}}(B)
$$

を与える。これらの積分は元の完全作用との相関を保持しており、source と作用の独立性を用いない。[AIA]

## 6．境界依存予算の $1/48$、count-only の $1/96$

以下の剰余評価と大域作用予算との比較では、$\beta\ge0$ とする。

$0\le S_H(A,B)\le C_{H,B}$ を各非負 source 部分に適用すると、

$$
J_{4,\pm}(B)\le C_{H,B}^4\,\frac{M_H}{2},\qquad
J_{4,\mathrm{abs}}(B)\le C_{H,B}^4M_H.
$$

前者が `p4Q2PZ37AIA_originalSourcePartFourthMoments_le_halfMass`、後者が `p4Q2PZ37AIA_originalAbsoluteActionFourthMoment_le_mass` である。二つの source 部分をそれぞれ評価した符号付き区間から、

$$
\boxed{
|R_{4,H}(\beta,B)|\le E_{4,H}(\beta,B),\qquad
E_{4,H}(\beta,B):=\frac{(\beta C_{H,B})^4}{48}M_H
}
$$

を得る。予算の定義は `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget`、剰余評価は `p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound`。分母 $48=24\cdot2$ の第二の因子は、元の source の二部分がそれぞれ質量 $M_H/2$ を持つことによる。絶対 source の相関だけを大域予算で評価する場合の分母は $24$ である。

元の大域作用予算との比較、および既存の $M_H\le p_H/2$ を使った count-only 評価は

$$
E_{4,H}(\beta,B)
\le\frac{(\beta C_{\mathrm{slab},H})^4}{48}M_H,\qquad
|R_{4,H}(\beta,B)|
\le\frac{(\beta C_{H,B})^4}{96}p_H
$$

となる。対応する宣言は `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_le_global` と `p4Q2PZ37AIA_originalFourthOrderRemainder_abs_halfCount` である。[AIA]

### AHY の予算との比較

AHY の境界依存三次予算を $E_{3,H}^{B}(\beta,B)=(\beta C_{H,B})^3M_H/12$ と書くと、

$$
\boxed{
E_{4,H}(\beta,B)=\frac{\beta C_{H,B}}4\,E_{3,H}^{B}(\beta,B)
}
$$

が任意の実数 $\beta$ で成り立つ。これは `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_eq_scaledCubic` である。$\beta C_{H,B}>4$ の場合まで含めた無条件の幅の減少は主張しない。二次中心 $Q_{2,H}$ と三次中心 $P_{3,H}$ は異なるため、幅の比較だけで二つの転送区間の包含関係も結論しない。[AIA]

## 7．完成平方による三次中心の負性

AHZ の下界

$$
M_{3,H}^{\mathrm{full}}(B)\ge\frac34L_H(B)^2V_H
$$

を、$\beta\ge0$ のとき非負の係数 $\beta^3/6$ で乗じる。これを三次中心の減算項に代入し、平方完成すると

$$
\begin{aligned}
P_{3,H}(\beta,B)
&\le-\beta V_H+\frac{\beta^2}{2}L_H(B)V_H
       -\frac{\beta^3}{8}L_H(B)^2V_H\\
&=-\frac{\beta V_H}{2}
  -\frac{\beta V_H}{8}\bigl(\beta L_H(B)-2\bigr)^2.
\end{aligned}
$$

従って、

$$
\boxed{
P_{3,H}(\beta,B)\le-\frac{\beta V_H}{2}\quad(\beta\ge0),
\qquad
P_{3,H}(\beta,B)<0\quad(\beta>0).
}
$$

宣言は `p4Q2PZ37AIA_originalCubicApproximation_le_completedSquare`、`p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance`、`p4Q2PZ37AIA_originalCubicApproximation_neg` である。この結論には coupling-budget の小ささの仮定は不要である。ここで負性が確定した対象は三次中心であり、実転送については $R_{4,H}$ の上側評価を併せる必要がある。[AIA]

## 8．実転送の区間と条件付き負性

$\beta\ge0$ に対し、元の実転送は

$$
\boxed{
P_{3,H}(\beta,B)-\frac{\beta^4}{24}J_{4,-}(B)
\le T_\beta f_0(B)
\le P_{3,H}(\beta,B)+\frac{\beta^4}{24}J_{4,+}(B)
}
$$

を満たし、対称な予算を使えば

$$
P_{3,H}(\beta,B)-E_{4,H}(\beta,B)
\le T_\beta f_0(B)
\le P_{3,H}(\beta,B)+E_{4,H}(\beta,B)
$$

となる。対応する宣言は `p4Q2PZ37AIA_originalTransfer_weightedQuarticInterval` と `p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval` である。

### 実際の四次相関を残す margin

$$
\frac{\beta^2}{2}L_H(B)V_H
+\frac{\beta^4}{24}J_{4,+}(B)
<
\beta V_H+\frac{\beta^3}{6}M_{3,H}^{\mathrm{full}}(B)
$$

が成立すれば $T_\beta f_0(B)<0$ となる。これが `p4Q2PZ37AIA_originalTransfer_negative_of_weightedQuarticMargin` である。負性の証明には上端が必要なため、ここでは正の source 部分の四次相関 $J_{4,+}$ を使う。

### 半分散と scaled margin

完成平方から得た上界を用いると、

$$
E_{4,H}(\beta,B)<\frac{\beta V_H}{2}
$$

も実転送の負性の十分条件となる。$\beta>0$ に対する具体的な scaled 条件は

$$
\boxed{\beta^3C_{H,B}^4M_H<24V_H.}
$$

宣言は `p4Q2PZ37AIA_originalTransfer_negative_of_halfVarianceQuarticMargin` と `p4Q2PZ37AIA_originalTransfer_negative_of_scaledQuarticMargin` である。後者は表示された不等式を正の $\beta$ で乗じ、$E_{4,H}<\beta V_H/2$ に接続する。

元の固定結合 $\beta_0$ には既存の `p4Q2PZ37ADC_fixedCoupling_pos` を用いる。`p4Q2PZ37AIA_originalFixedTransfer_boundaryHalfQuarticInterval` は追加の小ささの仮定なしで区間を与える。一方、`p4Q2PZ37AIA_originalFixedTransfer_negative_of_weightedQuarticMargin` と `p4Q2PZ37AIA_originalFixedTransfer_negative_of_scaledQuarticMargin` は、それぞれの具体的な margin を仮定した条件付き結論である。AIA はその数値条件の成立を評価していない。[AIA]

## 9．下端の非正性が意味する範囲

$J_{4,-}\ge0$ と三次中心の上界により、$\beta\ge0$ では

$$
\boxed{
P_{3,H}(\beta,B)-\frac{\beta^4}{24}J_{4,-}(B)\le0.
}
$$

これは `p4Q2PZ37AIA_originalCubicQuarticLowerEndpoint_nonpos` である。この区間評価の下端は正にならないため、この下端だけを用いる正値性の証明経路では実転送の正の符号を確定できない。実転送自体が正になり得ないという主張ではない。[AIA]

## 10．到達範囲と次段階 AIB

AIA は、元の完全 Boltzmann 転送の厳密な三次展開、全ての非負結合での四次剰余評価、三次中心の全ての正結合での負性、および実転送の具体的な条件付き負性を接続する。固定結合での符号を無条件に確定したものではなく、体積に一様な coercivity、Hamiltonian gap、連続極限の Yang–Mills mass gap も結論していない。

次段階 AIB では、まず元の固定結合 $\beta_0$ と元の格子数に照らし、粗い scaled／半分散 margin が成立し得る範囲を確認する。この成立可能性の検討は今回の34定理には含まれず、相関を保持した weighted margin や実転送そのものの符号とは区別する。その上で、元の符号付き完全作用四次モーメント

$$
M_{4,H}^{\mathrm{full}}(B):=
\int f_H(A)S_H(A,B)^4\,d\mu_H(A)
$$

の評価、または実際の $J_{4,+}(B)$・$J_{4,-}(B)$ の相関評価を進め、固定 $\beta_0$ の margin をより鋭くすることである。$M_{4,H}^{\mathrm{full}}$ とその候補恒等式 $J_{4,+}-J_{4,-}=M_{4,H}^{\mathrm{full}}$ は、今後形式化・評価する対象として扱う。AHZ の三次相関の順序を四次相関へそのまま移したり、二つの四次相関が等しいと仮定したりしない。これらの AIB 候補は AIA の到達結果には含めない。

## 11．検証済みの34定理

下表の1・2は `MGAP4D.MathlibAnalytic`、3〜34は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 内にある。最終CIの個別 `#print axioms` 出力と、以下の全34宣言を照合した。

| No. | Lean theorem |
| --- | --- |
| 1 | `p4Q2PZ37AIA_exp_neg_quarticRemainder` |
| 2 | `p4Q2PZ37AIA_real_signedNonnegativeError_interval` |
| 3 | `p4Q2PZ37AIA_originalFourthOrderRemainder_integrable` |
| 4 | `p4Q2PZ37AIA_originalFourthOrderRemainder_eq_third_add` |
| 5 | `p4Q2PZ37AIA_originalFourthOrderRemainder_eq_sub` |
| 6 | `p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion` |
| 7 | `p4Q2PZ37AIA_originalTransfer_thirdOrder_expansion_exactCubic` |
| 8 | `p4Q2PZ37AIA_originalKernel_thirdOrder_signedInterval` |
| 9 | `p4Q2PZ37AIA_originalWeightedActionFourth_integrable` |
| 10 | `p4Q2PZ37AIA_originalActionFourthMoments_nonneg` |
| 11 | `p4Q2PZ37AIA_originalActionFourthMoments_sum` |
| 12 | `p4Q2PZ37AIA_originalWeightedActionFourth_le_boundaryBudget` |
| 13 | `p4Q2PZ37AIA_originalSourcePartFourthMoments_le_halfMass` |
| 14 | `p4Q2PZ37AIA_originalAbsoluteActionFourthMoment_le_mass` |
| 15 | `p4Q2PZ37AIA_originalFourthOrderRemainder_weightedInterval` |
| 16 | `p4Q2PZ37AIA_originalFourthOrderRemainder_abs_weightedBound` |
| 17 | `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_nonneg` |
| 18 | `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_zero` |
| 19 | `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_eq_scaledCubic` |
| 20 | `p4Q2PZ37AIA_originalBoundaryHalfQuarticBudget_le_global` |
| 21 | `p4Q2PZ37AIA_originalFourthOrderRemainder_abs_boundaryHalfBound` |
| 22 | `p4Q2PZ37AIA_originalFourthOrderRemainder_abs_halfCount` |
| 23 | `p4Q2PZ37AIA_originalTransfer_weightedQuarticInterval` |
| 24 | `p4Q2PZ37AIA_originalTransfer_boundaryHalfQuarticInterval` |
| 25 | `p4Q2PZ37AIA_originalCubicApproximation_le_completedSquare` |
| 26 | `p4Q2PZ37AIA_originalCubicApproximation_le_negativeHalfVariance` |
| 27 | `p4Q2PZ37AIA_originalCubicApproximation_neg` |
| 28 | `p4Q2PZ37AIA_originalCubicQuarticLowerEndpoint_nonpos` |
| 29 | `p4Q2PZ37AIA_originalTransfer_negative_of_weightedQuarticMargin` |
| 30 | `p4Q2PZ37AIA_originalTransfer_negative_of_halfVarianceQuarticMargin` |
| 31 | `p4Q2PZ37AIA_originalTransfer_negative_of_scaledQuarticMargin` |
| 32 | `p4Q2PZ37AIA_originalFixedTransfer_boundaryHalfQuarticInterval` |
| 33 | `p4Q2PZ37AIA_originalFixedTransfer_negative_of_weightedQuarticMargin` |
| 34 | `p4Q2PZ37AIA_originalFixedTransfer_negative_of_scaledQuarticMargin` |

## 12．全文確認と修正履歴

直接importは検証済みAHZ leafと `Mathlib.Tactic`。変更Lean全文、AHXの元の二次中心とR3、AHYの非正剰余・source部分・可積分性・境界依存予算、AHZの真正三次完全作用モーメントと分散下界、AHNの正値性、元のBoltzmann kernelと物理的L2転送への接続を再確認した。スカラー導関数比較には固定mathlibの [MeanValue API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/MeanValue.lean) を用いる。積分の加法・定数倍・単調性は固定版の [Bochner積分API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) と照合した。

初回 [CI #42442102068](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42442102068) は、R4被積分関数の可積分性を示す1箇所で失敗した。`Integrable.add` が返す未適用の関数和 `f + g` の内部では、`Pi.add_apply` と点ごとの恒等式による `simpa` が期待したlambdaへの書き換えを行わなかった。固定版の [Integrable.congr API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean) を直接確認し、既知の可積分関数の和から目的の被積分関数へ、Haar-a.e. の点ごとの等式を渡す形に修正した。

```lean
  refine (hR3.add (hCube.const_mul (beta ^ 3 / 6))).congr ?_
  filter_upwards with A
  exact (hPoint A).symm
```

独立レビューでも、`.congr` の向き、既存の二つの可積分性、後続の `integral_add`・`integral_mono` への接続、非負剰余に対応する四次source部分の向き、係数48／96、平方完成と実転送marginの区別を確認した。初回失敗時の可積分性と依存定理に付いた自動的な `sorryAx` 出力は、成功証拠として採用していない。

ステップ一覧には一時的に完了ログと一致しない古い表示が残ったため、完了workflow・job・必須検査ログ・独立receiptを個別に再確認した。その後、必須Lean step 17のAPI表示も `completed／success` となったことを再取得で確認してから定理PRをマージした。

修正は証明表現に限定され、定理文・仮定・物理定義・toolchain・workflowを変更していない。最終sourceの全文readbackと構造検査を実施した。新規leaf以外の既存Lean、過去の証明記録、canonical rootを変更していない。


[AIA]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0ab58a6752957a39504b031f538fa5a8680ee1c6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalThirdOrderTaylorQuarticRemainderV5_PZ37AIA.lean
[AHY]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0ab58a6752957a39504b031f538fa5a8680ee1c6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY.lean
[AHZ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/0ab58a6752957a39504b031f538fa5a8680ee1c6/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformCenterCubicActionMomentV5_PZ37AHZ.lean
