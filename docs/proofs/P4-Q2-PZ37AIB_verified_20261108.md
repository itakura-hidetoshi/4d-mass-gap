# P4-Q2-PZ37AIB — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub main は正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の空間積Haar、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証済みの結果 |
| --- | --- |
| [AIB定理PR #6499](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6499) | **MERGED** |
| 継承元AIA正式記録HEAD | `b692eb1853330910f690616ff67d6598648ef2f7` |
| 最終exact-source HEAD | `ebeadc9e6630e74867b21855060813bd743af90a` |
| exact test-merge HEAD | `33a70fe444d69007dba43fdd2626c3226fcd7181` |
| 定理squash HEAD | `7f9fe4b595bc37f5d9b2074bf2ebef3779efebe2` |
| source／test-merge／squash共通Git tree | `4da6ab33dce991032e588bbded3bb4d34b4b91fe`、完全一致 |
| 最終exact-source CI | [#42444583711](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42444583711) — **completed／SUCCESS** |
| Changed Lean job | `128620723305` — **completed／SUCCESS** |
| 必須Lean step 17 | **completed／SUCCESS** |
| 独立completion receipt job | `128621758768` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,390／11,390 SUCCESS** |
| 新規宣言の公理確認 | **36／36**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13602154494`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・583行**、35定理と明示的同値1定義、既存ファイル変更なし |
| 新規Lean blob | `3da94b4d2ef9a4b4bc4777c854d64ec9eba819d1`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログの最終結果は `Build completed successfully (11390 jobs).`。新規35定理と明示的同値1定義の全36個別 `#print axioms` 出力を宣言一覧と照合し、欠落・余剰・重複がないことを確認した。既存依存の歴史的warningと今回の変更ファイルのwarningを区別する。

成功artifactのdigest：`sha256:f53e8d7fb779128d7bbb8b1448b794f6ce29f08552365ea2c984eab5f730caf2`。receiptは同一exact-source SHA・同一runのattempt 1を対象とし、`source_result=success` を返した。CI workflow、Lean job、必須Lean step 17、独立receiptがそれぞれ完了した状態で成功を確認してからマージした。source／test-merge／squash treeの一致をGitHub MCPで直接確認した。

証明ソース：[P4-Q2-PZ37AIB（検証済みexact-source）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ebeadc9e6630e74867b21855060813bd743af90a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB.lean)。

## 2．対象と到達点

AIB の対象は、AIA が元の Wilson transfer に与えた二つの粗い四次剰余十分条件である。格子、元の符号付き ZW source、積 Haar 測度、完全な one-slab action、両端の空間半重み、固定結合をそのまま用いる。

今回の中心となる結論は、元の結合 $\beta_0=\log(3/2)/64$ では、すべての $H\ge1$ とすべての元の右境界 $B$ に対して、この二つの粗い十分条件が成立しないというものである。その前段にある個数だけの必要条件は、元の体積族の中では厳密に $H=0$ の場合に成立する。

これは粗い誤差予算による判定の限界である。実際の剰余や transfer の符号を決める結論ではない。$H=0$ における十分条件の成立を与える境界の存在も、今回の結論には含めない。

## 3．元の格子と明示的な頂点同値

元の側長は

$$
L_H=2(H+1)
$$

であり、四次元の軸と頂点はそれぞれ `PeriodicHypercubicAxis = Fin 4` と `PeriodicHypercubicEvenVertex H = Fin 4 → ZMod L_H` である。primary reflection plane は、時刻座標が零であるという実際の条件

$$
v(0)=0
$$

で定義されている。

元の空間 slice 頂点と空間方向を

$$
\mathcal V_H
=
\{v:\operatorname{Fin}(4)\to\mathbb Z/L_H\mathbb Z\mid v(0)=0\},
\qquad
\mathcal D
=
\{\mu:\operatorname{Fin}(4)\mid\mu\ne0\}
$$

と書く。AIB の `p4Q2PZ37AIB_originalSliceVertexEquiv H` は、$\Phi_H:\mathcal V_H\to(\mathcal D\to\mathbb Z/L_H\mathbb Z)$ を与える。次の制限写像と零拡張を明示的に組み合わせた同値である。

$$
\begin{aligned}
\Phi_H(v)(\mu)&=v(\mu),\\
\Phi_H^{-1}(x)(i)
&=
\begin{cases}
0,&i=0,\\
x(i),&i\ne0.
\end{cases}
\end{aligned}
$$

逆写像の第二の場合には、$i\ne0$ の証明を伴う元の空間方向 subtype を用いる。往復の恒等性は、時刻座標では $v(0)=0$、空間座標ではそのままの座標値から従う。別の格子や代替 carrier を定義して個数を仮定する構成ではない。

空間方向と、増加順で一度だけ選ばれる空間方向対

$$
\mathcal D_2
=
\{(\mu,\nu)\in\mathcal D\times\mathcal D\mid\mu<\nu\}
$$

の個数は、いずれも3である。明示的同値に `Nat.card_fun` と `Nat.card_zmod` を適用することで、

$$
\#\mathcal V_H=L_H^3,
\qquad
\#\mathcal D=3,
\qquad
\#\mathcal D_2=3
$$

を得る。

対応する宣言は `p4Q2PZ37AIB_spatialDirection_card`、`p4Q2PZ37AIB_spatialDirectionPair_card`、`p4Q2PZ37AIB_originalSliceVertex_card` である。方向数の二つの定理には $H$ 引数はない。

## 4．同じ元の plaquette list の正確な個数

元の正向き空間 link carrier は $\mathcal V_H\times\mathcal D$、空間 plaquette carrier は $\mathcal V_H\times\mathcal D_2$ である。したがって、両者の個数はともに $3L_H^3$ となる。

AFZ の $p_H$ は、元の `periodicHypercubicEvenSpatialSlicePlaquetteList H` の長さを実数へ埋め込んだ値である。この list は元の plaquette carrier の `Finset.univ.toList` であるため、AIB はその同じ list の長さを直接評価する。

$$
\boxed{
p_H=3L_H^3=24(H+1)^3
}
$$

Lean の主定理は、自然数 $H$ の実数への埋め込みを明記した

`p4Q2PZ37AIB_plaquetteCount_exact (H : ℕ)`

であり、その結論は

$$
\texttt{p4Q2PZ37AFZ\_plaquetteCount}\ H
=
24\bigl((H:\mathbb R)+1\bigr)^3
$$

である。特に、

$$
p_0=24,\qquad p_1=192,\qquad H\ge1\Longrightarrow p_H\ge192.
$$

これらは `p4Q2PZ37AIB_plaquetteCount_zero`、`p4Q2PZ37AIB_plaquetteCount_one`、`p4Q2PZ37AIB_plaquetteCount_ge_192` に対応する。数えているのは primary spatial slice の元の carrier であり、antipodal slice を追加していない。方向対も増加順で数えるため、反対順序による二重計数はない。

## 5．元の source、Haar モーメント、境界 action 予算

$f_H$ を、元の符号付き ZW source の連続代表 `p4Q2PZ37AFZ_originalCenteredContinuous H` とする。$\mu_H$ は元の空間配置上の積 Haar 確率測度である。用いる二つの量は、

$$
V_H=\int f_H(A)^2\,d\mu_H(A),
\qquad
M_H=\int |f_H(A)|\,d\mu_H(A)
$$

である。

$V_H$ は AHN の `originalSource_HaarSecondMoment` の定義そのものである。$M_H$ は、元の物理的 $L^2$ source から定義された AEV の L1 質量に、AHN の `originalSource_L1_eq_continuousIntegral` を適用した同じ量である。連続代表の使用によって source や測度を変更しない。既存 AHN は、各元の体積で $M_H>0$ と $V_H>0$ を与えている。

元の source の点ごとの評価 $|f_H(A)|\le p_H/2$ から、

$$
f_H(A)^2
=
|f_H(A)|^2
\le
\frac{p_H}{2}|f_H(A)|
$$

となる。両辺は、元の compact configuration space 上の連続関数として可積分であり、Haar 積分の単調性から

$$
\boxed{
V_H\le\frac{p_H}{2}M_H
}
$$

を得る。対応する主定理は `p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass` である。source の点ごとの非負性は仮定しない。

元の完全 action は

$$
S_H(A,B)
=
\frac12W_H(A)
+
S_H^{\mathrm{cross}}(A,B)
+
\frac12W_H(B)
$$

であり、AHY の境界に依存する action 上界は

$$
C_{H,B}=3p_H+\frac12W_H(B)
$$

である。AIB は元の $W_H(B)\ge0$ を用いて

$$
\boxed{3p_H\le C_{H,B}}
$$

を取り出す。対応する定理は `p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount` である。この $C_{H,B}$ は既存の上界であり、action の達成される最大値と同一だとは主張しない。

## 6．元の固定結合の有理数による評価

結合は ADC の元の定義

$$
\beta_0=\frac{\log(3/2)}{64}
$$

のままである。固定 mathlib の `Real.one_sub_inv_le_log_of_pos` を $x=3/2$ に適用すると、

$$
\frac13=1-\left(\frac32\right)^{-1}
\le\log\frac32
$$

となり、

$$
\frac1{192}\le\beta_0
$$

を得る。既存 AHI の上界と合わせた AIB の宣言 `p4Q2PZ37AIB_fixedCoupling_rationalInterval` は、

$$
\boxed{
\frac1{192}\le\beta_0\le\frac1{128}
}
$$

である。浮動小数点近似や結合の体積依存の再調整は用いない。

## 7．粗い四次誤差予算に対する下界

AIA の粗い境界四次誤差予算は、元の量だけで定義された

$$
E_{4,H,\beta}(B)
=
\frac{(\beta C_{H,B})^4}{48}\,M_H
$$

である。分母48は、符号別 source の非加重 Haar 質量が等しく、それぞれ $M_H/2$ となることを AIA が用いた予算の係数をそのまま保持している。

AIA における真の剰余との関係 $|R_{4,H,\beta}(B)|\le E_{4,H,\beta}(B)$ は $\beta\ge0$ の範囲である。一方、今回の予算の下界は任意の実数 $\beta$ に対する代数的不等式である。

$3p_H\le C_{H,B}$、$M_H\ge0$、$2V_H\le p_HM_H$ から、

$$
\begin{aligned}
E_{4,H,\beta}(B)
&\ge
\frac{\beta^4}{48}(3p_H)^4M_H\\
&=
\frac{27}{16}\beta^4p_H^4M_H\\
&\ge
\frac{27}{8}\beta^4p_H^3V_H\\
&=
\frac{27}{8}(\beta p_H)^3(\beta V_H).
\end{aligned}
$$

したがって、`p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound` の内容は

$$
\boxed{
\frac{27}{8}(\beta p_H)^3(\beta V_H)
\le E_{4,H,\beta}(B)
\qquad(\beta\in\mathbb R)
}
$$

である。証明は $\beta$ による除算を行わず、$\beta^4\ge0$ を使う。これが負の $\beta$ を含む理由である。AIA の剰余評価を負の $\beta$ へ拡張する主張ではない。

また、この不等式の右辺は予算である。真の $R_4$ の絶対値や符号に対する下界を意味しない。

## 8．正の結合における二つの粗い十分条件

$\beta>0$ とする。AIA の半分散に基づく条件と、そのスケールを整理した条件は、

$$
\begin{aligned}
\mathcal Q_H(\beta,B)
&:\quad
E_{4,H,\beta}(B)<\frac{\beta V_H}{2},\\
\mathcal S_H(\beta,B)
&:\quad
\beta^3C_{H,B}^4M_H<24V_H
\end{aligned}
$$

である。正の共通因子 $\beta/48$ を消去すると、

$$
\boxed{
\mathcal Q_H(\beta,B)\iff\mathcal S_H(\beta,B)
\qquad(\beta>0)
}
$$

となる。これは `p4Q2PZ37AIB_originalQuarticMargin_iff_scaled` である。

この共通の条件が成立するなら、前節の予算下界から

$$
\frac{27}{8}(\beta p_H)^3(\beta V_H)
<
\frac{\beta V_H}{2}
$$

となる。既存の $V_H>0$ と仮定 $\beta>0$ により $\beta V_H>0$ を消去でき、

$$
\boxed{81(\beta p_H)^3<12}
$$

が必要となる。

対応する宣言は `p4Q2PZ37AIB_originalScaledQuarticMargin_necessary` と `p4Q2PZ37AIB_originalHalfVarianceQuarticMargin_necessary` である。ここで得た個数条件は必要条件であり、その成立から元の十分条件へ戻る同値は主張しない。

## 9．元の固定結合での体積別の定量的限界

個数公式と固定結合の下界を組み合わせると、

$$
\frac{(H+1)^3}{8}\le\beta_0p_H
$$

となる。これは `p4Q2PZ37AIB_originalFixedCoupling_count_cubicFloor` である。特に $H\ge1$ では、

$$
p_H\ge192,\qquad \beta_0\ge\frac1{192}
\quad\Longrightarrow\quad
\boxed{\beta_0p_H\ge1}.
$$

この結果を粗い予算下界へ入れると、すべての元の右境界 $B$ に対して

$$
\boxed{
\frac{27}{8}\beta_0V_H
\le E_{4,H,\beta_0}(B)
\qquad(H\ge1)
}
$$

となる。さらに $\beta_0V_H>0$ であるため、

$$
\boxed{
\frac{\beta_0V_H}{2}
<
E_{4,H,\beta_0}(B)
\qquad(H\ge1)
}
$$

という厳密な分離を得る。対応する宣言は `p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor` と `p4Q2PZ37AIB_originalFixedQuarticBudget_gt_halfVariance` である。

したがって、`p4Q2PZ37AIB_originalFixedCoarseQuarticMargins_impossible` は、

$$
\begin{gathered}
H\ge1\Longrightarrow
\neg\bigl(\beta_0^3C_{H,B}^4M_H<24V_H\bigr),\\
H\ge1\Longrightarrow
\neg\left(E_{4,H,\beta_0}(B)<\frac{\beta_0V_H}{2}\right)
\end{gathered}
$$

を同時に与える。これは一つの境界の計算例ではなく、元のすべての右境界に対する結論である。

## 10．必要な個数条件の厳密な分類

$H\ge1$ では $\beta_0p_H\ge1$ なので、

$$
81(\beta_0p_H)^3\ge81>12.
$$

したがって必要な個数条件は成立しない。

一方、$H=0$ では $p_0=24$ と $\beta_0\le1/128$ から、

$$
0\le\beta_0p_0\le\frac{3}{16}
$$

であり、

$$
81(\beta_0p_0)^3
\le81\left(\frac3{16}\right)^3
=
\frac{2187}{4096}
<12.
$$

この二方向をまとめた `p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero` の結論は、

$$
\boxed{
81(\beta_0p_H)^3<12
\iff
H=0
}
$$

である。

この同値の左辺は、あくまで個数だけの必要条件である。$H=0$ における $\mathcal Q_H(\beta_0,B)$ または $\mathcal S_H(\beta_0,B)$ の成立は、ここからは従わない。

そのため、実際の粗い十分条件についての `p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero` と `p4Q2PZ37AIB_originalFixedHalfVarianceQuarticMargin_only_zero` は、

$$
\mathcal S_H(\beta_0,B)\Longrightarrow H=0,
\qquad
\mathcal Q_H(\beta_0,B)\Longrightarrow H=0
$$

という一方向の帰結にとどめている。

## 11．代表的な宣言と役割

以下の `p4Q2PZ37AIB_` 宣言は、いずれも `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 名前空間に属する。

| 主な宣言 | 数学的役割 |
|---|---|
| `p4Q2PZ37AIB_originalSliceVertexEquiv` | 元の primary-plane 頂点と三つの空間座標の明示的同値 |
| `p4Q2PZ37AIB_plaquetteCount_exact` | 同じ元の plaquette list に対する $p_H=24(H+1)^3$ |
| `p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass` | 真の Haar モーメントの関係 $V_H\le(p_H/2)M_H$ |
| `p4Q2PZ37AIB_fixedCoupling_rationalInterval` | 元の結合の区間 $1/192\le\beta_0\le1/128$ |
| `p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount` | 元の境界上界 $C_{H,B}$ の下限 $3p_H$ |
| `p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound` | 任意の実 $\beta$ に対する粗い四次予算の下界 |
| `p4Q2PZ37AIB_originalQuarticMargin_iff_scaled` | $\beta>0$ での二つの粗い十分条件の同値 |
| `p4Q2PZ37AIB_originalScaledQuarticMargin_necessary` | 個数条件 $81(\beta p_H)^3<12$ の必要性 |
| `p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor` | $H\ge1$ での予算と $\beta_0V_H$ の定量的比較 |
| `p4Q2PZ37AIB_originalFixedCoarseQuarticMargins_impossible` | $H\ge1$・任意の元の右境界で二つの粗い条件を排除 |
| `p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero` | 必要な個数条件が成立する体積の分類 |
| `p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero` | 実際の粗い十分条件の成立には $H=0$ が必要 |

## 12．結論の範囲と次段階 AIC

AIB が排除するのは、AIA の元の粗い予算 $E_{4,H,\beta_0}(B)$ を用いた半分散条件と、それと同値な scaled condition である。次の事項は今回の定理内容に含まれない。

- 真の四次剰余 $R_4$ の絶対値が大きいという主張。
- 相関を保持した符号別四次モーメントによる条件の失敗。
- 三次近似中心の追加の負項を活用する別の判定の成否。
- 元の固定結合 transfer の正負、正負 shell の存在。
- 体積一様な coercivity、Hamiltonian gap、連続極限の Yang–Mills mass gap。
- 最小体積 $H=0$ における十分条件の成立例。

次段階 AIC では、元の完全作用の既知の分解を使い、積分変数に依存しない定数を指数因子として正確に抽出することを第一の候補とする。

$$
X_H(A,B)=S_H^{\mathrm{cross}}(A,B)-p_H,\qquad
a_H(B)=\frac{3p_H+W_H(B)}2,\qquad
Y_H(A,B)=f_H(A)+X_H(A,B).
$$

AHZ の $S_H=f_H+a_H+X_H$ から、次に形式化する恒等式は

$$
T_\beta f_0(B)
=e^{-\beta a_H(B)}
\int f_H(A)e^{-\beta Y_H(A,B)}\,d\mu_H(A)
$$

である。元の両halfweight、source、積Haar、転送を保持し、既知の定数部分を Taylor 展開の外へ出す。この式、およびsource付きcentered moments $(0,V_H,0,Q_{4,H}+3D_H(B))$ の接続は、AIB の新規36宣言には含まれない次段階の証明対象として扱う。ここで $Q_{4,H}=\int f_H^4\,d\mu_H$、$D_H(B)=\int f_H^2X_H^2\,d\mu_H$ は AHZ の量である。

具体的な課題は $Y_H$ が正負の値を取り得ることである。既存の $|f_H|\le p_H/2$ と $|X_H|\le p_H$ から $|Y_H|\le3p_H/2$ を接続できるが、AIA の非負引数 $x\ge0$ に対する四次剰余上界を $\beta Y_H$ へ直接適用することはできない。符号付き区間で有効なスカラー剰余と、元のsourceとの相関評価が別途必要になる。新しい剰余上界や実際の固定結合transferの符号は今回主張しない。

併せて、AIA の相関を保持した量

$$
J_{4,H}^{+}(B)=\int f_H^{+}(A)S_H(A,B)^4\,d\mu_H(A),
\qquad
J_{4,H}^{-}(B)=\int f_H^{-}(A)S_H(A,B)^4\,d\mu_H(A),
$$

ただし $f_H^{\pm}=(|f_H|\pm f_H)/2$、または元の符号付き四次action momentを評価する方向も残る。これらは今後の課題であり、今回その評価値や改善された符号証明の成立を示したものではない。

## 13．検証済みの36宣言

下表の1〜4は `MGAP4D.MathlibAnalytic`、5〜36は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` 内にある。35定理と、7番の明示的同値の定義を区別する。最終CIの個別 `#print axioms` 出力と全36宣言を照合した。

| No. | Lean declaration | 種別 |
| --- | --- | --- |
| 1 | `p4Q2PZ37AIB_real_quarticMargin_iff_scaled` | 定理 |
| 2 | `p4Q2PZ37AIB_real_quarticBudget_lowerBound` | 定理 |
| 3 | `p4Q2PZ37AIB_real_scaledQuarticMargin_necessary` | 定理 |
| 4 | `p4Q2PZ37AIB_real_coarseQuarticMargins_impossible` | 定理 |
| 5 | `p4Q2PZ37AIB_spatialDirection_card` | 定理 |
| 6 | `p4Q2PZ37AIB_spatialDirectionPair_card` | 定理 |
| 7 | `p4Q2PZ37AIB_originalSliceVertexEquiv` | 明示的同値の定義 |
| 8 | `p4Q2PZ37AIB_originalSliceVertex_card` | 定理 |
| 9 | `p4Q2PZ37AIB_originalSliceLink_card` | 定理 |
| 10 | `p4Q2PZ37AIB_originalSlicePlaquette_card` | 定理 |
| 11 | `p4Q2PZ37AIB_originalPlaquetteList_length` | 定理 |
| 12 | `p4Q2PZ37AIB_plaquetteCount_exact` | 定理 |
| 13 | `p4Q2PZ37AIB_plaquetteCount_zero` | 定理 |
| 14 | `p4Q2PZ37AIB_plaquetteCount_one` | 定理 |
| 15 | `p4Q2PZ37AIB_plaquetteCount_ge_192` | 定理 |
| 16 | `p4Q2PZ37AIB_originalSourceSquare_le_halfCount_abs` | 定理 |
| 17 | `p4Q2PZ37AIB_originalSourceSecondMoment_le_halfCount_L1Mass` | 定理 |
| 18 | `p4Q2PZ37AIB_fixedCoupling_ge_oneDiv192` | 定理 |
| 19 | `p4Q2PZ37AIB_originalBoundaryActionBudget_ge_threeCount` | 定理 |
| 20 | `p4Q2PZ37AIB_originalQuarticMargin_iff_scaled` | 定理 |
| 21 | `p4Q2PZ37AIB_originalQuarticBudget_varianceLowerBound` | 定理 |
| 22 | `p4Q2PZ37AIB_originalScaledQuarticMargin_necessary` | 定理 |
| 23 | `p4Q2PZ37AIB_originalHalfVarianceQuarticMargin_necessary` | 定理 |
| 24 | `p4Q2PZ37AIB_originalCoarseQuarticMargins_impossible_of_largeCount` | 定理 |
| 25 | `p4Q2PZ37AIB_originalQuarticBudget_signalFloor_of_largeCount` | 定理 |
| 26 | `p4Q2PZ37AIB_fixedCoupling_rationalInterval` | 定理 |
| 27 | `p4Q2PZ37AIB_originalFixedCoupling_count_cubicFloor` | 定理 |
| 28 | `p4Q2PZ37AIB_originalFixedCoupling_count_ge_one` | 定理 |
| 29 | `p4Q2PZ37AIB_originalFixedQuarticBudget_signalFloor` | 定理 |
| 30 | `p4Q2PZ37AIB_originalFixedQuarticBudget_gt_halfVariance` | 定理 |
| 31 | `p4Q2PZ37AIB_originalFixedCoarseQuarticMargins_impossible` | 定理 |
| 32 | `p4Q2PZ37AIB_originalFixedNecessaryCriterion_impossible` | 定理 |
| 33 | `p4Q2PZ37AIB_originalFixedNecessaryCriterion_zero` | 定理 |
| 34 | `p4Q2PZ37AIB_originalFixedNecessaryCriterion_iff_zero` | 定理 |
| 35 | `p4Q2PZ37AIB_originalFixedScaledQuarticMargin_only_zero` | 定理 |
| 36 | `p4Q2PZ37AIB_originalFixedHalfVarianceQuarticMargin_only_zero` | 定理 |

## 14．全文確認と固定APIの照合

直接importは検証済みAIA leaf、`Mathlib.Analysis.SpecialFunctions.Log.Basic`、`Mathlib.SetTheory.Cardinal.Finite`、`Mathlib.Tactic`。583行の変更Lean全文を確認し、三担当の独立した全文レビューでも修正を要する点は残らなかった。変更ファイルの構造事前検査も成功した。

元のprimary planeの条件、空間方向と増加方向対、元のplaquette list、AFZの個数定義、AGNのsource上界、AHNの連続代表と物理的L1質量の接続、ADCの元固定結合、AHIの結合上界、AHYの境界action予算、AIAの四次予算と十分条件を追跡した。元のcarrierを別の有限型へ取り替えたり、必要な個数・モーメントを追加仮定にしたりしていない。

固定mathlibのAPIは、次を直接照合した。

- [有限型とNat.card](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/SetTheory/Cardinal/Finite.lean)：`Nat.card_congr`、`Nat.card_fun`、`Nat.card_zmod`、`Nat.card_prod`、`Nat.card_eq_fintype_card`、`Fintype.card_eq_nat_card`。明示的同値と `Nat.card` を用い、元のlistで選ばれたFintypeとの接続を確認した。有限方向数の `decide` は `open scoped Classical` の前に置き、計算可能な判定を保持した。
- [対数](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean)：`Real.one_sub_inv_le_log_of_pos` により $\log(3/2)\ge1/3$ を得た。
- [正因子の順序消去](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean)：`mul_lt_mul_iff_right₀` は共通の左正因子、`mul_lt_mul_iff_left₀` は共通の右正因子を消去する。この固定版の署名を初回CI前に確認し、旧名を用いた候補を修正した。
- [Bochner積分](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)：連続性とcompact supportから両辺の可積分性を供給し、`integral_mono`、定数倍、元のL1質量への恒等式を接続した。

初回exact-source CIが成功し、CI実行後のLeanソース変更はない。CIエラーを受けて定理文を弱めた修正もない。任意の実 $\beta$ に対する予算下界と、$\beta>0$ を要する因子消去を区別し、$H=0$ の必要条件成立から十分条件成立へ逆向きの推論をしていない。

ステップ一覧には一時的に完了workflow・job・ログと一致しない古い表示が残った。必須Lean step 17の直接APIを再取得し、2026-11-08 04:09:13 UTCの独立確認と04:09:16 UTCの最終確認で `completed／success` を観測した後、定理PRをマージした。独立receiptだけを根拠に必須Lean検査の完了を推定していない。

既存Lean、過去の証明記録、物理定義、canonical root、toolchain、workflowは変更していない。定理は新規leafとして、正式記録は新規Markdownとして追加する。mainには同一Git blobの正式記録だけを同期する。
