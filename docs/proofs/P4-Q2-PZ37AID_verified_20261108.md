# P4-Q2-PZ37AID — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の積Haar、物理的L2 transfer、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。AICの同じ近似中心と実剰余を用いる。

## 1．Exact-source証明台帳

| 項目 | 検証結果 |
| --- | --- |
| [AID定理PR #6505](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6505) | **MERGED** |
| 継承元AIC正式記録HEAD | `21d545073eea2d35a1b4330234f511a610b69155` |
| 最終exact-source HEAD | `1d3bf1e875197595c6fab1082ef9512a72c9eb54` |
| exact test-merge HEAD | `9c5d73edecdb6eb389ddda17be2baa0254142d8f` |
| 定理squash HEAD | `ea38510980ccd33a959bd6cc77eea1a7e4d18208` |
| source／test-merge／squash共通Git tree | `27998f2918b2084ff5fc36e32c6d30493b7a337b`、完全一致 |
| 最終exact-source CI | [#42451301562](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42451301562) — **completed／SUCCESS** |
| Changed Lean job | `128640900306` — **completed／SUCCESS** |
| 必須Lean step 17 | **completed／SUCCESS** |
| 独立completion receipt job | `128642158215` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,392／11,392 SUCCESS** |
| 新規宣言の公理確認 | **45／45**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13606091247`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・875行**、39定理と6定義、既存ファイル変更なし |
| 新規Lean blob | `7d07847e16d348b4afe70e1eb43ff40af0304e89`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

成功ログの最終結果は `Build completed successfully (11392 jobs).`。新規39定理と6定義の全45個別 `#print axioms` 出力を宣言一覧と照合し、欠落・余剰・重複がないことを確認した。45件すべての公理集合は `[propext, Classical.choice, Quot.sound]` であり、`sorryAx` は含まれない。変更Leanのwarning／errorは0／0で、既存依存の歴史的warningと区別した。

成功artifactのdigest：`sha256:0d44c57526f619dfa7ac84289d7de0ae1bdc34ed10776045e3c6f348d306d3ef`。独立receiptの実ログは `event=pull_request exact_sha=1d3bf1e875197595c6fab1082ef9512a72c9eb54 source_result=success run=42451301562 attempt=1`。CI workflow、Lean job、必須Lean step 17、独立receipt jobがそれぞれ完了した状態で成功を確認してからマージした。receiptの通知処理の成功だけでLean成功を推定せず、実際の `source_result=success` と完成Leanログを確認した。

実装担当と独立確認担当が、artifactと完成jobログにおける45宣言・公理・診断をそれぞれ照合した。GitHub MCPでsource／test-merge／squashの共通treeを直接確認した。初回CIの失敗と、定理内容を保持した修正は第17節に記録する。

証明ソース：[P4-Q2-PZ37AID（検証済みexact-source）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/1d3bf1e875197595c6fab1082ef9512a72c9eb54/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalConvexChordQuarticRemainderV5_PZ37AID.lean)。

## 2． 対象と今回の接続

AID は、AIC で定義した同じ近似中心と同じ実際の剰余について、指数関数の凸性から四次上界を改善する。元の source、完全 one-slab Wilson action、両端の空間半重み、積 Haar 測度、物理的 transfer、固定結合を保持する。

スカラーの新しい評価は、

$$
0\le
e^{-x}-\left(1-x+\frac{x^2}{2}-\frac{x^3}{6}\right)
\le
\frac{4+e^{-x}}{120}x^4
\qquad(x\in\mathbb R)
$$

である。この評価を元の完全 Boltzmann kernel に戻すと、重みは

$$
\frac{4e^{-\beta a_H(B)}+K_{H,\beta}(A,B)}5
$$

となる。右側には実際の完全 kernel が残る。

この重みと source の正負部分を同じ Haar 積分内に保持し、全実数 $\beta$ における実剰余と transfer の区間を接続する。さらに $\beta\ge0$ では AIC の区間への包含を示し、正規化した正の source 部分について、support に基づく一方向の上界を与える。

実際の transfer の負性には、真正相関またはその上側予算に関する明示的な margin が残る。固定結合でその margin を満たす境界の構成は今回の内容に含まれない。

## 3． 元の量と、保持する AIC の中心・剰余

元の有限格子の配置空間上の積 Haar 確率測度を $\mu_H$、元の物理的 ZW source を $f_{0,H}$、その連続代表を $f_H$ とする。空間 Wilson action を $W_H$、crossing action を $S_H^{\mathrm{cross}}$、元の plaquette 個数を $p_H$ とする。

既存の source 表示は、

$$
f_H(A)=\frac{W_H(A)-p_H}{2},
\qquad
\int f_H\,d\mu_H=0.
$$

元の完全 action と kernel は、

$$
S_H(A,B)
=\frac12W_H(A)+S_H^{\mathrm{cross}}(A,B)+\frac12W_H(B),
\qquad
K_{H,\beta}(A,B)=e^{-\beta S_H(A,B)}.
$$

物理的 transfer は AHP の既存の橋渡しにより、

$$
\mathcal T_{H,\beta}(B)
=(T_{H,\beta}f_{0,H})(B)
=
\int f_H(A)K_{H,\beta}(A,B)\,d\mu_H(A)
$$

と表される。これは全実数 $\beta$ と各元の境界 $B$ に対する表示である。

AIC の表記を引き継ぎ、

$$
X_H(A,B)=S_H^{\mathrm{cross}}(A,B)-p_H,
\qquad
a_H(B)=\frac{3p_H+W_H(B)}2,
$$

$$
Y_H^{\mathrm c}(A,B)=f_H(A)+X_H(A,B),
\qquad
S_H(A,B)=a_H(B)+Y_H^{\mathrm c}(A,B)
$$

とする。本文の $Y_H^{\mathrm c}$ は centered action を表し、AHU の mixed Haar moment の記号とは区別する。

同じ真の Haar モーメントを、

$$
V_H=\int f_H^2\,d\mu_H>0,\qquad
Q_{4,H}=\int f_H^4\,d\mu_H\ge0,\qquad
D_H(B)=\int f_H(A)^2X_H(A,B)^2\,d\mu_H(A)\ge0
$$

と書く。AID は $Q_{4,H}$ や $D_H(B)$ を数値的に評価せず、真の積分として保持する。

AIC のスカラー関数と近似中心・実際の剰余は、

$$
r_4(x)=e^{-x}-\left(1-x+\frac{x^2}{2}-\frac{x^3}{6}\right),
$$

$$
P^{\mathrm c}_{3,H,\beta}(B)
=
e^{-\beta a_H(B)}
\left[
-\beta V_H
-\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
\right],
$$

$$
R^{\mathrm c}_{4,H,\beta}(B)
=
\int f_H(A)
\left[
e^{-\beta a_H(B)}
r_4\bigl(\beta Y_H^{\mathrm c}(A,B)\bigr)
\right]d\mu_H(A)
$$

である。既存 AIC の全実数 $\beta$ の恒等式

$$
R^{\mathrm c}_{4,H,\beta}(B)
=\mathcal T_{H,\beta}(B)-P^{\mathrm c}_{3,H,\beta}(B)
$$

をそのまま使う。AID では、新しい中心や新しい実剰余を定義していない。

対応する既存の宣言は `p4Q2PZ37AIC_originalFactoredCubicApproximation`、`p4Q2PZ37AIC_originalFactoredFourthOrderRemainder`、`p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub` である。

## 4． 全実数引数に対する凸性による四次上界

新しいスカラー定理は、

$$
\boxed{
0\le r_4(x)\le\frac{4+e^{-x}}{120}x^4
=\frac{x^4}{24}\,\frac{4+e^{-x}}5
\qquad(x\in\mathbb R)
}
$$

である。対応する宣言は、

- `p4Q2PZ37AID_expCubicRemainder_chordUpper`
- `p4Q2PZ37AID_expCubicRemainder_chordInterval`

である。$x$ の符号や小ささは仮定しない。下側の非負性には AIC の全実数剰余評価を用い、上側を凸性から構成する。

証明では、

$$
P_3(x)=1-x+\frac{x^2}{2}-\frac{x^3}{6},
$$

$$
F_x(s)
=
e^{-sx}P_3\bigl((1-s)x\bigr)
$$

を用いる。微分を正確に整理すると、

$$
F_x'(s)
=\frac{x^4}{6}(1-s)^3e^{-sx}.
$$

$0\le s\le1$ では指数の凸性から、

$$
e^{-sx}\le (1-s)+se^{-x}.
$$

係数 $x^4(1-s)^3/6$ は非負なので、

$$
F_x'(s)
\le
\frac{x^4}{6}(1-s)^3\bigl((1-s)+se^{-x}\bigr).
$$

右辺の原始関数として実装するのは、

$$
B_x(s)
=
P_3(x)
+\frac{x^4}{6}
\left[
\frac{1-e^{-x}}5\bigl(1-(1-s)^5\bigr)
+
\frac{e^{-x}}4\bigl(1-(1-s)^4\bigr)
\right].
$$

$F_x(0)=B_x(0)=P_3(x)$ であり、固定 mathlib の `image_le_of_deriv_right_le_deriv_boundary` による微分比較から $F_x(1)\le B_x(1)$ を得る。終点では、

$$
F_x(1)=e^{-x},
$$

$$
B_x(1)-P_3(x)
=
\frac{x^4}{6}
\left(\frac{1-e^{-x}}5+\frac{e^{-x}}4\right)
=
\frac{4+e^{-x}}{120}x^4.
$$

したがって、重みの係数 $4/5$ と $1/5$、四次剰余の係数 $1/24$ はこの微分比較から生じる。

凸性の入力は固定 mathlib の `convexOn_exp` であり、直接 import は `Mathlib.Analysis.Convex.SpecificFunctions.Basic` である。

## 5． 実際の完全 kernel を含む新しい重み

AIC の全実数 $\beta$ の因子化

$$
K_{H,\beta}(A,B)
=
e^{-\beta a_H(B)}
e^{-\beta Y_H^{\mathrm c}(A,B)}
$$

を使い、新しい重みを

$$
\boxed{
q^{\mathrm{ch}}_{H,\beta}(A,B)
=
\frac{
4e^{-\beta a_H(B)}+K_{H,\beta}(A,B)
}{5}
}
$$

と定義する。Lean の定義は `p4Q2PZ37AID_originalChordRemainderWeight` である。

これは、積分変数に依存しない正確な外因子と、元の完全 kernel の凸結合である。両端の空間半重みは元の $K_{H,\beta}$ と $a_H$ の中に保持されている。

全実数 $\beta$ で、$q^{\mathrm{ch}}_{H,\beta}>0$ であり、左配置 $A$ に関して連続である。これらは `p4Q2PZ37AID_originalChordRemainderWeight_pos` と `p4Q2PZ37AID_originalChordRemainderWeight_continuous` に対応する。

スカラー評価に正の外因子を掛けると、

$$
\boxed{
0\le
e^{-\beta a_H(B)}
r_4\bigl(\beta Y_H^{\mathrm c}(A,B)\bigr)
\le
\frac{\beta^4}{24}
q^{\mathrm{ch}}_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4
\qquad(\beta\in\mathbb R)
}
$$

となる。

宣言は `p4Q2PZ37AID_expCubicRemainder_factoredChordInterval` と `p4Q2PZ37AID_originalFactoredKernelRemainder_chordInterval` である。$\beta^4$ の非負性と全実数引数の剰余評価を用いるため、この段階に $\beta\ge0$ は必要ない。

## 6． Source の正負部分と真正相関

AHY の元の定義を使い、

$$
f_H^+(A)=\frac{|f_H(A)|+f_H(A)}2,
\qquad
f_H^-(A)=\frac{|f_H(A)|-f_H(A)}2
$$

とする。両者は非負で、$f_H=f_H^+-f_H^-$ である。元の Haar 平均零によって、

$$
\int f_H^+\,d\mu_H
=
\int f_H^-\,d\mu_H
=
\frac{M_H}{2},
\qquad
M_H=\int |f_H|\,d\mu_H
$$

という非加重質量の恒等式がある。

AID の二つの真正相関は、

$$
J^{\mathrm{ch},+}_{4,H,\beta}(B)
=
\int
f_H^+(A)
q^{\mathrm{ch}}_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\,d\mu_H(A),
$$

$$
J^{\mathrm{ch},-}_{4,H,\beta}(B)
=
\int
f_H^-(A)
q^{\mathrm{ch}}_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\,d\mu_H(A)
$$

である。定義は `p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment` と `p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment` に対応する。

各被積分関数は連続であり、元の compact 配置空間上で可積分となる。一般の連続な重み $g$ についての可積分性は `p4Q2PZ37AID_originalChordWeightedFourth_integrable` が供給する。両方の真正相関の非負性は、全実数 $\beta$ に対する `p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_nonneg` である。

非加重質量の等値から、この二つの相関の等値を推論しない。source の符号、実際の kernel、centered action の四次を同じ積分内に残す。

## 7． 全実数 β の実剰余区間と物理的 transfer 区間

source を掛ける前の kernel 剰余は非負である。そのため、負の source 部分が下側、正の source 部分が上側に入る。

AIA の実数の符号分解不等式と Haar 積分の単調性から、

$$
\boxed{
-\frac{\beta^4}{24}J^{\mathrm{ch},-}_{4,H,\beta}(B)
\le
R^{\mathrm c}_{4,H,\beta}(B)
\le
\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
\qquad(\beta\in\mathbb R)
}
$$

を得る。対応する宣言は `p4Q2PZ37AID_originalFactoredFourthOrderRemainder_chordInterval` である。

符号付き source と積分した $R^{\mathrm c}_4$ 自体の非負性は主張しない。

同じ AIC の恒等式 $\mathcal T=P^{\mathrm c}_3+R^{\mathrm c}_4$ を使うと、

$$
\boxed{
P^{\mathrm c}_{3,H,\beta}(B)
-\frac{\beta^4}{24}J^{\mathrm{ch},-}_{4,H,\beta}(B)
\le
\mathcal T_{H,\beta}(B)
\le
P^{\mathrm c}_{3,H,\beta}(B)
+\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
\qquad(\beta\in\mathbb R)
}
$$

となる。これが `p4Q2PZ37AID_originalTransfer_chordQuarticInterval` である。

この区間は負の結合と零結合を含む。ただし、負性の具体的な境界や margin が得られたという主張を含まない。

## 8． β≥0 における AIC 区間への包含

AIC の既存の重みを、

$$
q^{\mathrm{AIC}}_{H,\beta}(A,B)
=
e^{-\beta\min(a_H(B),S_H(A,B))}
$$

と書く。

全実数 $x$ に対し、スカラーの係数比較

$$
\frac{4+e^{-x}}5
\le e^{\max(0,-x)}
$$

が成り立つ。これは `p4Q2PZ37AID_expCubicRemainder_endpoint_coefficient_le` である。

元の配置の重みについては、$\beta\ge0$ のもとで両方の端点指数が AIC の重み以下となり、

$$
\boxed{
q^{\mathrm{ch}}_{H,\beta}(A,B)
\le q^{\mathrm{AIC}}_{H,\beta}(A,B)
\qquad(\beta\ge0)
}
$$

を得る。宣言は `p4Q2PZ37AID_originalChordRemainderWeight_le_AIC` である。

さらに、$\beta>0$ かつ $Y_H^{\mathrm c}(A,B)\ne0$ では、二つの端点指数が異なるため、

$$
q^{\mathrm{ch}}_{H,\beta}(A,B)
<
q^{\mathrm{AIC}}_{H,\beta}(A,B)
$$

となる。これは `p4Q2PZ37AID_originalChordRemainderWeight_lt_AIC_of_centeredAction_ne_zero` の点ごとの主張である。積分後の真正相関について厳密な改善を証明したものではない。

同じ $\beta\ge0$ の範囲で、

$$
q^{\mathrm{ch}}_{H,\beta}(A,B)
\le e^{-\beta W_H(B)/2}\le1
$$

という既存の右半重みによる評価も継承する。対応する宣言は `p4Q2PZ37AID_originalChordRemainderWeight_le_rightHalfweight` と `p4Q2PZ37AID_originalChordRemainderWeight_le_one` である。

AIC の二つの真正四次相関を $J^{\mathrm{AIC},\pm}_{4,H,\beta}$ と書くと、非負の source 部分と四次を掛けて積分することで、

$$
J^{\mathrm{ch},+}_{4,H,\beta}(B)
\le J^{\mathrm{AIC},+}_{4,H,\beta}(B),
\qquad
J^{\mathrm{ch},-}_{4,H,\beta}(B)
\le J^{\mathrm{AIC},-}_{4,H,\beta}(B)
$$

が従う。これは `p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC` である。

中心 $P^{\mathrm c}_3$ が同一なので、下端は上がり、上端は下がる。したがって、

$$
\boxed{
\begin{aligned}
&
\left[
P^{\mathrm c}_3-\frac{\beta^4}{24}J^{\mathrm{ch},-}_4,\;
P^{\mathrm c}_3+\frac{\beta^4}{24}J^{\mathrm{ch},+}_4
\right]\\
&\qquad\subseteq
\left[
P^{\mathrm c}_3-\frac{\beta^4}{24}J^{\mathrm{AIC},-}_4,\;
P^{\mathrm c}_3+\frac{\beta^4}{24}J^{\mathrm{AIC},+}_4
\right]
\qquad(\beta\ge0).
\end{aligned}
}
$$

この集合としての包含が `p4Q2PZ37AID_originalChordTransferInterval_subset_AIC` である。同じ physical transfer、同じ中心、同じ実剰余についての比較である。

## 9． 真正相関による条件付き負性と固定結合

完全な三次係数を用いた十分条件は、

$$
\boxed{
\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
<
e^{-\beta a_H(B)}
\left[
\beta V_H
+\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
\right]
}
$$

である。この条件から

$$
\mathcal T_{H,\beta}(B)<0
$$

を結論する宣言が `p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin` である。全実数の剰余区間を用いるため、定理文には追加の結合符号条件を置かない。

分散項だけを利用する、より強い十分条件は、

$$
\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
<
e^{-\beta a_H(B)}\beta V_H
\qquad(\beta\ge0)
$$

である。こちらは AIC の近似中心の比較を使うため、`p4Q2PZ37AID_originalTransfer_negative_of_chordVarianceMargin` に $\beta\ge0$ が残る。

また、$\beta\ge0$ で既存 AIC の完全な weighted margin が成立すれば、新しい chord margin も成立する。これは `p4Q2PZ37AID_originalAICQuarticMargin_implies_chordMargin` に対応する。逆向きの同値は主張しない。

元の固定結合

$$
\beta_0=\frac{\log(3/2)}{64}>0
$$

について、`p4Q2PZ37AID_originalFixedTransfer_chordQuarticInterval` が区間を特殊化し、`p4Q2PZ37AID_originalFixedTransfer_negative_of_chordQuarticMargin` が同じ真正 margin を仮定した負性を与える。区間の特殊化には margin 仮定はなく、負性には明示的に残る。

## 10． 全実数 β の正規化と margin の厳密な同値

新しい正規化重みを、

$$
\boxed{
n^{\mathrm{ch}}_{H,\beta}(A,B)
=
\frac{4+e^{-\beta Y_H^{\mathrm c}(A,B)}}5
}
$$

と定義する。これは `p4Q2PZ37AID_originalNormalizedChordRemainderWeight` である。全実数 $\beta$ で非負かつ連続であり、対応する宣言は同名接頭辞の `_nonneg` と `_continuous` である。

元の kernel の正確な因子化により、

$$
\boxed{
q^{\mathrm{ch}}_{H,\beta}(A,B)
=
e^{-\beta a_H(B)}n^{\mathrm{ch}}_{H,\beta}(A,B)
\qquad(\beta\in\mathbb R)
}
$$

となる。宣言は `p4Q2PZ37AID_originalChordRemainderWeight_eq_const_mul_normalized` である。

正の source 部分の真正正規化相関を、

$$
N^{\mathrm{ch},+}_{4,H,\beta}(B)
=
\int f_H^+(A)n^{\mathrm{ch}}_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\,d\mu_H(A)
$$

と定義する。定義は `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment` である。連続な重みに対する `p4Q2PZ37AID_originalNormalizedChordWeightedFourth_integrable` が可積分性を供給し、この相関の非負性は `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_nonneg` に対応する。

外因子が $A$ に依存しないことから、

$$
\boxed{
J^{\mathrm{ch},+}_{4,H,\beta}(B)
=
e^{-\beta a_H(B)}
N^{\mathrm{ch},+}_{4,H,\beta}(B)
}
$$

となる。宣言は `p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized` である。ここでも相関の独立性は使わない。

指数因子は厳密に正なので、全実数 $\beta$ と任意の実数 $s$ について、

$$
\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
<e^{-\beta a_H(B)}s
\quad\Longleftrightarrow\quad
\frac{\beta^4}{24}N^{\mathrm{ch},+}_{4,H,\beta}(B)<s
$$

が成り立つ。これは `p4Q2PZ37AID_originalPositiveChordQuarticMargin_iff_normalized` である。

完全な三次信号を代入した同値は、

$$
\boxed{
\begin{aligned}
&
\frac{\beta^4}{24}J^{\mathrm{ch},+}_{4,H,\beta}(B)
<
e^{-\beta a_H(B)}
\left[
\beta V_H+\frac{\beta^3}{6}(Q_{4,H}+3D_H(B))
\right]\\
&\quad\Longleftrightarrow\quad
\frac{\beta^4}{24}N^{\mathrm{ch},+}_{4,H,\beta}(B)
<
\beta V_H+\frac{\beta^3}{6}(Q_{4,H}+3D_H(B)).
\end{aligned}
}
$$

宣言は `p4Q2PZ37AID_originalChordQuarticMargin_iff_normalized` である。正規化された右側の条件から実際の transfer の負性へ進む宣言は `p4Q2PZ37AID_originalTransfer_negative_of_normalizedChordQuarticMargin` であり、全実数 $\beta$ の定理文を保持する。

外因子を消す操作は厳密な同値である。指数因子が小さいことだけで margin が成立したと判断しない。

## 11． 正の source 部分の support に合わせた四次 cap

元の評価

$$
|f_H(A)|\le\frac{p_H}{2},
\qquad
|X_H(A,B)|\le p_H
$$

に加えて $f_H(A)\ge0$ を用いると、

$$
\boxed{
-p_H
\le Y_H^{\mathrm c}(A,B)
\le\frac{3p_H}{2}
\qquad\bigl(f_H(A)\ge0\bigr)
}
$$

となる。これは `p4Q2PZ37AID_originalPositiveSource_centeredAction_interval` である。負の source 部分には同じ下端を適用しない。

スカラー定理 `p4Q2PZ37AID_real_chordQuartic_cap_of_support` は、

$$
\beta\ge0,\quad p\ge0,\quad -p\le y\le3p/2
$$

のもとで、

$$
\boxed{
\frac{4+e^{-\beta y}}5\,y^4
\le
p^4\max\left(\frac{4+e^{\beta p}}5,\frac{81}{16}\right)
}
$$

を与える。

証明では $y$ の符号により分ける。

- $y\ge0$ では $e^{-\beta y}\le1$ なので重みは1以下であり、$y^4\le(3p/2)^4=(81/16)p^4$。
- $y\le0$ では $0\le-y\le p$ なので、$y^4\le p^4$ かつ $e^{-\beta y}\le e^{\beta p}$。

ここで必要なのは $\beta\ge0$ であり、この support cap を負の結合へ拡張していない。

一般の cap に対する積分接続は、`p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_of_support_cap` によって分離されている。すなわち、

$$
f_H(A)\ge0
\Longrightarrow
n^{\mathrm{ch}}_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\le c
$$

から、

$$
N^{\mathrm{ch},+}_{4,H,\beta}(B)\le\frac{cM_H}{2}
$$

が従う。この一般接続自体には $\beta$ や $c$ の符号条件を追加しない。$f_H<0$ の領域では $f_H^+=0$ を用い、残る領域では非負の $f_H^+$ を掛けて積分する。最後に使うのは非加重質量の恒等式 $\int f_H^+=M_H/2$ である。

## 12． 正規化された一方向の上側予算

便宜的に本文で

$$
b_H(\beta)
=
\max\left(
\frac{4+e^{\beta p_H}}5,\frac{81}{16}
\right)
$$

と書く。この記号は説明用であり、追加の模型を導入しない。

前節の cap を積分して、

$$
N^{\mathrm{ch},+}_{4,H,\beta}(B)
\le
\frac{M_Hp_H^4}{2}b_H(\beta)
\qquad(\beta\ge0)
$$

を得る。宣言は `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_supportBudget` である。

新しい予算の定義は、

$$
\boxed{
E^{\mathrm{ch},+}_{H}(\beta)
=
\frac{\beta^4 M_Hp_H^4}{48}b_H(\beta)
}
$$

であり、`p4Q2PZ37AID_originalPositiveChordQuarticBudget` に対応する。この定義自体は全実数 $\beta$ に対して置かれるが、真正相関を上から支配する定理には $\beta\ge0$ が必要である。

具体的には、

$$
\boxed{
\frac{\beta^4}{24}
N^{\mathrm{ch},+}_{4,H,\beta}(B)
\le
E^{\mathrm{ch},+}_{H}(\beta)
\qquad(\beta\ge0)
}
$$

が `p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized` である。係数 $1/48$ は四次剰余の $1/24$ と、正の source の非加重半質量 $M_H/2$ から生じる。

これは正の source 部分に対応する**上側の予算**である。実剰余の下界や絶対値の対称評価、負の source 部分に対する同じ予算を意味しない。

元の transfer に戻すと、

$$
\boxed{
\mathcal T_{H,\beta}(B)
\le
e^{-\beta a_H(B)}
\left[
-\beta V_H
-\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
+E^{\mathrm{ch},+}_{H}(\beta)
\right]
\qquad(\beta\ge0)
}
$$

となる。これが `p4Q2PZ37AID_originalTransfer_le_chordSupportBudget` である。正確な指数因子は、負の信号と上側予算の両方に掛かる。

したがって、$\beta\ge0$ と

$$
\boxed{
E^{\mathrm{ch},+}_{H}(\beta)
<
\beta V_H
+\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
}
$$

から $\mathcal T_{H,\beta}(B)<0$ が従う。宣言は `p4Q2PZ37AID_originalTransfer_negative_of_chordSupportBudget` である。真正正規化相関の margin に対して、上界を代入した強い十分条件となる。

元の固定結合への特殊化は `p4Q2PZ37AID_originalFixedTransfer_negative_of_chordSupportBudget` であり、同じ support-budget margin を仮定として残す。

## 13． 結合の仮定と結論の整理

| 内容 | 結合の範囲 | 結論の範囲 |
|---|---|---|
| スカラー chord 剰余評価 | $x\in\mathbb R$ | 同じ $r_4$ の非負性と四次上界 |
| 元の kernel 剰余・実剰余・transfer の chord 区間 | $\beta\in\mathbb R$ | 同じ AIC の中心と剰余を用いた区間 |
| Chord 重み・真正相関と AIC の比較 | $\beta\ge0$ | 点ごとの非厳密比較と、積分相関の非厳密比較 |
| Chord 重みの厳密比較 | $\beta>0$、$Y_H^{\mathrm c}\ne0$ | 点ごとの厳密不等式 |
| AIC 区間への包含 | $\beta\ge0$ | 同じ中心を持つ閉区間の包含 |
| 正規化と完全 margin の同値 | $\beta\in\mathbb R$ | 正の外因子を厳密に取り除いた同値 |
| 完全な真正 chord margin からの実 transfer 負性 | $\beta\in\mathbb R$ | margin を仮定した条件付き結論 |
| 分散のみの margin からの負性 | $\beta\ge0$ | より強い十分条件 |
| 正の source support による具体的 cap と上側予算 | $\beta\ge0$ | 正の source 部分に対する一方向の上界 |
| 固定結合 $\beta_0$ | 元の結合を維持 | 区間は無条件、負性は真正または予算の margin を保持 |

## 14． 未証明事項と次段階 AIE

AID は、同じ実際の誤差について改善された相関区間を与える。次の事項は今回の定理内容に含めない。

- 元の固定結合で真正 chord margin、正規化 margin、support-budget margin を満たす具体的な境界の構成。
- 元の物理的 transfer の無条件の正負判定や、正負双方の shell の存在。
- 新旧の真正四次相関の厳密な積分上の差、または幅の厳密改善。
- 正負の weighted quartic moments の等値、独立性、数値評価。
- Support 予算からの実剰余の下界・対称絶対値評価。
- 新しい support-budget margin の固定結合における体積分類。
- AIB が示した旧粗い予算の障害が消えたという主張。
- 体積一様な coercivity、Hamiltonian gap、連続極限の Yang–Mills mass gap。

次段階 AIE の研究候補は、元の transfer に正の右境界重み $e^{\beta W_H(B)/2}$ を掛けた Haar 平均を評価し、その平均の負性から負の transfer を持つ境界の存在へ進むルートである。座標ごとの Haar 平行移動、Fubini、元の平均零 source と $V_H>0$ の接続が新たに必要となる。この平均の負性・境界の存在は、現段階では未形式化の研究目標であり、AID の成立済みの結論として扱わない。


## 15．新規45宣言と個別公理出力

次の39定理と6定義を、個別の `#print axioms` 対象とする。No. 1–5は `MGAP4D.MathlibAnalytic`、No. 6–45は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。ローカルinstanceはこの新規公開宣言数には含めない。

| No. | 宣言 | 種別 |
| --- | --- | --- |
| 1 | `p4Q2PZ37AID_expCubicRemainder_chordUpper` | 定理 |
| 2 | `p4Q2PZ37AID_expCubicRemainder_chordInterval` | 定理 |
| 3 | `p4Q2PZ37AID_expCubicRemainder_factoredChordInterval` | 定理 |
| 4 | `p4Q2PZ37AID_expCubicRemainder_endpoint_coefficient_le` | 定理 |
| 5 | `p4Q2PZ37AID_real_chordQuartic_cap_of_support` | 定理 |
| 6 | `p4Q2PZ37AID_originalChordRemainderWeight` | 定義 |
| 7 | `p4Q2PZ37AID_originalChordRemainderWeight_continuous` | 定理 |
| 8 | `p4Q2PZ37AID_originalChordRemainderWeight_pos` | 定理 |
| 9 | `p4Q2PZ37AID_originalChordRemainderWeight_le_AIC` | 定理 |
| 10 | `p4Q2PZ37AID_originalChordRemainderWeight_lt_AIC_of_centeredAction_ne_zero` | 定理 |
| 11 | `p4Q2PZ37AID_originalChordRemainderWeight_le_rightHalfweight` | 定理 |
| 12 | `p4Q2PZ37AID_originalChordRemainderWeight_le_one` | 定理 |
| 13 | `p4Q2PZ37AID_originalChordWeightedFourth_integrable` | 定理 |
| 14 | `p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment` | 定義 |
| 15 | `p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment` | 定義 |
| 16 | `p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_nonneg` | 定理 |
| 17 | `p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC` | 定理 |
| 18 | `p4Q2PZ37AID_originalFactoredKernelRemainder_chordInterval` | 定理 |
| 19 | `p4Q2PZ37AID_originalFactoredFourthOrderRemainder_chordInterval` | 定理 |
| 20 | `p4Q2PZ37AID_originalTransfer_chordQuarticInterval` | 定理 |
| 21 | `p4Q2PZ37AID_originalChordTransferInterval_subset_AIC` | 定理 |
| 22 | `p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin` | 定理 |
| 23 | `p4Q2PZ37AID_originalTransfer_negative_of_chordVarianceMargin` | 定理 |
| 24 | `p4Q2PZ37AID_originalAICQuarticMargin_implies_chordMargin` | 定理 |
| 25 | `p4Q2PZ37AID_originalFixedTransfer_chordQuarticInterval` | 定理 |
| 26 | `p4Q2PZ37AID_originalFixedTransfer_negative_of_chordQuarticMargin` | 定理 |
| 27 | `p4Q2PZ37AID_originalNormalizedChordRemainderWeight` | 定義 |
| 28 | `p4Q2PZ37AID_originalNormalizedChordRemainderWeight_continuous` | 定理 |
| 29 | `p4Q2PZ37AID_originalNormalizedChordRemainderWeight_nonneg` | 定理 |
| 30 | `p4Q2PZ37AID_originalChordRemainderWeight_eq_const_mul_normalized` | 定理 |
| 31 | `p4Q2PZ37AID_originalNormalizedChordWeightedFourth_integrable` | 定理 |
| 32 | `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment` | 定義 |
| 33 | `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_nonneg` | 定理 |
| 34 | `p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized` | 定理 |
| 35 | `p4Q2PZ37AID_originalPositiveChordQuarticMargin_iff_normalized` | 定理 |
| 36 | `p4Q2PZ37AID_originalChordQuarticMargin_iff_normalized` | 定理 |
| 37 | `p4Q2PZ37AID_originalTransfer_negative_of_normalizedChordQuarticMargin` | 定理 |
| 38 | `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_of_support_cap` | 定理 |
| 39 | `p4Q2PZ37AID_originalPositiveSource_centeredAction_interval` | 定理 |
| 40 | `p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_supportBudget` | 定理 |
| 41 | `p4Q2PZ37AID_originalPositiveChordQuarticBudget` | 定義 |
| 42 | `p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized` | 定理 |
| 43 | `p4Q2PZ37AID_originalTransfer_le_chordSupportBudget` | 定理 |
| 44 | `p4Q2PZ37AID_originalTransfer_negative_of_chordSupportBudget` | 定理 |
| 45 | `p4Q2PZ37AID_originalFixedTransfer_negative_of_chordSupportBudget` | 定理 |


最終成功CIログで45件の完全修飾名を一対一照合した。欠落・余剰・重複は0件で、45件とも標準 `propext`・`Classical.choice`・`Quot.sound` のみである。新しい公理・`sorry`・`admit`・`sorryAx` を用いない。

## 16．全文・imports・依存定理・固定mathlib APIの照合

新規Leanの直接importは次の3件である。

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredBoltzmannFactorizationV5_PZ37AIC
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
```

既存AICの依存閉包を継承し、指数関数の凸性を使うために固定mathlibのmoduleを直接追加した。AHPの元の物理的transferの連続積分表示・kernelのBoltzmann表示・完全作用の連続性、AHQの中心化crossing評価、AHYの元sourceの正負部分と**重みなし**half-mass、AIAのsigned sourceと非負誤差に対する点ごとの区間、AICの正確な因子化・同じ近似中心・同じ実剰余・旧相関区間を、実際のsignatureに照らして確認した。

固定mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` の参照先は次のとおり。

| 固定source | 照合したAPI・用途 |
| --- | --- |
| [Convex/SpecificFunctions/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean) | global `convexOn_exp`。名前は `Real.convexOn_exp` ではない |
| [Convex/Function.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Function.lean) | `ConvexOn` の端点・非負係数・係数和の引数順 |
| [Calculus/MeanValue.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/MeanValue.lean) | `image_le_of_deriv_right_le_deriv_boundary`。閉区間の連続性と半開区間の片側微分比較 |
| [SpecialFunctions/ExpDeriv.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean) | `HasDerivAt.exp` による微分の指数合成 |
| [SpecialFunctions/Exp.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Exp.lean) | `Real.continuous_exp.comp` による元kernelの連続性 |
| [Complex/Exponential.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean) | `Real.one_le_exp` による端点係数の比較 |
| [GroupWithZero/Unbundled/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean) | `mul_lt_mul_iff_right₀`。この固定APIは共通する**左側**の正因子を取り消す |

スカラー証明は、指数関数の凸性を区間 $[0,1]$ の微分比較に接続する。$x$ で割らず、$x=0$・負の $x$ も含めた一つの証明で扱う。積分はcompact configuration space上の連続性から可積分性を供給し、実際の相関に対して単調性を適用する。正規化では共通する厳密に正の指数因子だけを取り消し、重み付き相関を重みなし質量に置き換えない。

公開前の全文レビューでは、中心化crossingの上下界に `-pH ≤ X A B ∧ X A B ≤ pH` という型注釈を加え、`linarith` に渡す式をAHZの定義と明示的にそろえた。また二つの初等微分は `simpa using` とし、導関数の係数 $0-1$ と $(-1)x+(1-t)0$ を整理した。これらは定理文・定義・仮定を変えない証明の調整であり、未公開の候補をCI成功として扱うことはしていない。

最終sourceの全文、imports、依存定理、全実数結合と非負結合の仮定の区別を確認した。静的preflightで参照したAICはcanonical blob `c568eb52b8a5ce721b42301fa6ceba6452a67c04` とbyte一致する既存ファイルであり、PR差分には含まれない。リモート差分はAIDの追加Lean leaf一件である。

## 17．初回CI失敗と定理内容を保持した修正

初回source `8da39aaf56ad96e2ed298ed4cdc832d63f67aeed` の [CI #42450748284](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42450748284) は、workflow・Lean job `128639235742`・必須step 17の完了状態で **FAILURE** と確定した。変更ファイルのerrorは1件、warningは0件である。

失敗は `p4Q2PZ37AID_originalTransfer_le_chordSupportBudget` の証明に限られた。初回の `add_le_add_left he _` が生成する式は $kN+c\le E+c$ であり、目標の $c+kN\le c+E$ と加法の順序が一致しなかった。

固定mathlibの [Monoid/Unbundled/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean)（blob `bbd2372aab7fd64036f9d13757840cd8b86ede6f`）にある `@[to_additive] theorem mul_le_mul_right` の実際の型 $a b\le a c$ を確認し、加法版の `add_le_add_right he _` に修正した。この固定版では、共通の項を左側に加えるAPIが `add_le_add_right` である。

修正はこのAPI呼び出し1箇所だけであり、前後の875行は当該置換以外byte一致する。定理文、定義、仮定、物理対象、imports、toolchain、workflowを変えていない。修正版全文と同種の加法・乗法の不等式API、依存定理のsignatureを再点検し、構造preflightを再実行した。

初回ログには45個別出力が過不足なくあったが、当該定理の1出力にerror由来の `sorryAx` が含まれていた。独立receipt job `128640356998` は通知処理としてsuccessを返し、実出力は `event=pull_request exact_sha=8da39aaf56ad96e2ed298ed4cdc832d63f67aeed source_result=failure run=42450748284 attempt=1` であった。このreceiptや初回の公理出力を証明成功の根拠にしない。

新しいexact-sourceに対する全45出力・完了ログ・独立receiptを改めて確認し、第1節の成功台帳を最終的な証拠とする。初回の失敗履歴を保持したまま、修正済みsourceのtreeだけを定理マージ対象とする。

## 18．保存範囲と文書同期

元の完全Wilson一スラブ作用・両端halfweight・signed ZW source・積Haar・物理的L2 transfer・固定結合・型付き証明履歴・canonical root・Lean/mathlib pin・workflowを保持する。AICの近似中心と実剰余も再定義せず、同じ対象の評価を狭める。

この正式記録は新規path `docs/proofs/P4-Q2-PZ37AID_verified_20261108.md` へappendし、formalからmainへ同一Git blobを文書だけのPRで同期する。文書PRはLeanを変更せず、Strict Leanを追加実行しない。main mergeで既存設定により自動起動するpush workflowは、exact-source定理CIおよび文書PRと区別し、設定変更や手動dispatchは行わない。

AIDの到達点は、指数凸性による真正kernel混合重み、同じ実剰余・transferのより狭い相関区間、正確なmarginの正規化、正sourceのsupportから得る片側上界である。固定結合でmarginを満たす実例、無条件のtransfer符号、正負二殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは、今回の定理に含まれない。
