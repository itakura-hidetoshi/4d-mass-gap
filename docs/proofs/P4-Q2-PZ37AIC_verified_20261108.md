# P4-Q2-PZ37AIC — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。mainは正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の積Haar、物理的L2 transfer、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証結果 |
| --- | --- |
| [AIC定理PR #6502](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6502) | **MERGED** |
| 継承元AIB正式記録HEAD | `56e262d0e681e8955bb41175e5578b601c3d5c28` |
| 最終exact-source HEAD | `8c7e7639fbe75db35c64054311f370abfbbbd300` |
| exact test-merge HEAD | `22bd52238a5abf63a0f24a015bca903ccfe53077` |
| 定理squash HEAD | `3618a0c6d66fad30a95687d687b87eed624d830e` |
| source／test-merge／squash共通Git tree | `5f73f86294ffae33032d8d5f7005405f9ed0d355`、完全一致 |
| 最終exact-source CI | [#42447749390](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42447749390) — **completed／SUCCESS** |
| Changed Lean job | `128630180475` — **completed／SUCCESS** |
| 必須Lean step 17 | **completed／SUCCESS** |
| 独立completion receipt job | `128631154579` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,391／11,391 SUCCESS** |
| 新規宣言の公理確認 | **46／46**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13604516817`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・893行**、38定理と8定義、既存ファイル変更なし |
| 新規Lean blob | `c568eb52b8a5ce721b42301fa6ceba6452a67c04`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

成功ログの最終結果は `Build completed successfully (11391 jobs).`。新規38定理と8定義の全46個別 `#print axioms` 出力を宣言一覧と照合し、欠落・余剰・重複がないことを確認した。46件すべての公理集合は `[propext, Classical.choice, Quot.sound]` であり、`sorryAx` は含まれない。変更Leanのwarning／errorは0／0で、既存依存の歴史的warningと区別した。

成功artifactのdigest：`sha256:0e1cebdf40dc969231b3b0d9d390a5d9a79ec061172b5c3f95842dce75da580f`。独立receiptの実ログは `event=pull_request exact_sha=8c7e7639fbe75db35c64054311f370abfbbbd300 source_result=success run=42447749390 attempt=1`。CI workflow、Lean job、必須Lean step 17、独立receipt jobがそれぞれ完了した状態で成功を確認してからマージした。receiptは完了通知であり、実際のLean検証ログと置き換えない。GitHub MCPでsource／test-merge／squashの共通treeを直接確認した。

証明ソース：[P4-Q2-PZ37AIC（検証済みexact-source）](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/8c7e7639fbe75db35c64054311f370abfbbbd300/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCenteredBoltzmannFactorizationV5_PZ37AIC.lean)。

## 2． 対象と到達点

AIC は、元の完全 Wilson one-slab action のうち積分変数に依存しない部分を、正確な指数因子として積分の外へ取り出す。そのうえで、残る符号付きの中心化作用について三次までの source 付きモーメントを接続し、実際の transfer と近似中心との差を真の積分として定義する。

主な内容は、任意の実結合で成り立つ正確な展開と、非負結合で成り立つ相関を保持した四次剰余区間である。元の格子、符号付き ZW source、両端の空間半重み、積 Haar 測度、物理的 $L^2$ transfer、固定結合は変更しない。

新しい近似中心は正の結合で厳密に負となる。一方、実際の transfer の負性には、真の重み付き四次モーメントに関する明示的な margin を残す。その margin を満たす具体的な元の境界は、今回の定理内容には含まれない。

## 3． 元の量と中心化作用の表記

$\mu_H$ を元の空間配置上の積 Haar 確率測度、$f_{0,H}$ を元の物理的 ZW source とする。$f_H$ はその連続代表

`p4Q2PZ37AFZ_originalCenteredContinuous H`

である。物理的 source と連続代表の Haar ほとんど至る所の一致は既存の結果を用いる。

元の空間 Wilson action を $W_H$、crossing action を $S_H^{\mathrm{cross}}$、元の plaquette list の個数を $p_H$ とする。完全 action は、両端の半重みを含む

$$
S_H(A,B)
=
\frac12W_H(A)
+
S_H^{\mathrm{cross}}(A,B)
+
\frac12W_H(B)
$$

である。元の kernel と物理的 transfer の連続代表表示は、

$$
K_{H,\beta}(A,B)=e^{-\beta S_H(A,B)},
\qquad
\mathcal T_{H,\beta}(B)
=
(T_{H,\beta}f_{0,H})(B)
=
\int f_H(A)K_{H,\beta}(A,B)\,d\mu_H(A)
$$

であり、この表示は任意の実数 $\beta$ で利用する。

AIC では、

$$
\begin{aligned}
X_H(A,B)&=S_H^{\mathrm{cross}}(A,B)-p_H,\\
a_H(B)&=\frac{3p_H+W_H(B)}2,\\
Y_H^{\mathrm c}(A,B)&=f_H(A)+X_H(A,B)
\end{aligned}
$$

と置く。$X_H$ は AHZ の元の centered crossing である。$a_H$ と $Y_H^{\mathrm c}$ はそれぞれ新しい `p4Q2PZ37AIC_originalBoundaryConstant`、`p4Q2PZ37AIC_originalCenteredAction` に対応する。

本文の $Y_H^{\mathrm c}$ は、AHU で用いられた mixed Haar moment の記号との混同を避けるための表記である。ここでは積分前の、二つの配置に依存する実数値関数を表す。

AHZ の既存の分解を組み替えることで、

$$
\boxed{
S_H(A,B)=a_H(B)+Y_H^{\mathrm c}(A,B)
}
$$

となる。右境界の空間半重みも、この式にそのまま残っている。

## 4． 中心化作用の範囲と正確な Boltzmann 因子抽出

元の評価

$$
|f_H(A)|\le\frac{p_H}{2},
\qquad
|X_H(A,B)|\le p_H
$$

から、

$$
\boxed{
|Y_H^{\mathrm c}(A,B)|\le\frac{3p_H}{2}
}
$$

を得る。$Y_H^{\mathrm c}$ の非負性は仮定しない。これは、後で指数剰余を全実数引数について扱う必要がある理由でもある。

また、元の各 Wilson action の非負性により、

$$
a_H(B)\ge0,
\qquad
\boxed{
\frac{W_H(B)}2
\le
\min\bigl(a_H(B),S_H(A,B)\bigr)
}.
$$

後者は、$a_H(B)=3p_H/2+W_H(B)/2$ と、完全 action に残る左半重み・crossing action の非負性をそれぞれ用いる。

任意の実数 $\beta$ に対して、指数の加法則から元の kernel は厳密に

$$
\boxed{
K_{H,\beta}(A,B)
=
e^{-\beta a_H(B)}
e^{-\beta Y_H^{\mathrm c}(A,B)}
}
$$

と因子化される。したがって、同じ物理的 transfer は

$$
\boxed{
\mathcal T_{H,\beta}(B)
=
e^{-\beta a_H(B)}
\int f_H(A)e^{-\beta Y_H^{\mathrm c}(A,B)}\,d\mu_H(A)
}
$$

と表される。ここで $a_H(B)$ は積分変数 $A$ に依存しない。元の半重みを削除したり、kernel を近似したりする操作ではない。

この接続は `p4Q2PZ37AIC_originalKernel_factorization` と `p4Q2PZ37AIC_originalTransfer_factorization` に対応する。中心化 kernel と source の積の可積分性は、元の compact configuration space 上の連続性から明示されている。

## 5． Source 付き中心化モーメント

既存 AHN の真の二次モーメントと、AHZ の真の四次・混合モーメントを

$$
V_H=\int f_H(A)^2\,d\mu_H(A),
\qquad
Q_{4,H}=\int f_H(A)^4\,d\mu_H(A),
$$

$$
D_H(B)
=
\int f_H(A)^2X_H(A,B)^2\,d\mu_H(A)
$$

と書く。これらは同じ元の source と Haar 測度に対する積分である。既存の結果として $V_H>0$、$Q_{4,H}\ge0$、$D_H(B)\ge0$ を利用する。

AIC で接続する source 付き中心化モーメントは次のとおりである。

| 次数 $n$ | $\displaystyle\int f_H(A)\bigl(Y_H^{\mathrm c}(A,B)\bigr)^n\,d\mu_H(A)$ | 接続 |
|---|---|---|
| $0$ | $0$ | 既存 AHP の source の平均零 |
| $1$ | $V_H$ | `p4Q2PZ37AIC_originalCenteredAction_firstMoment` |
| $2$ | $0$ | `p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero` |
| $3$ | $Q_{4,H}+3D_H(B)$ | `p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact` |

一次では、

$$
f_HY_H^{\mathrm c}=f_H^2+f_HX_H
$$

と展開し、AHZ の $\int f_HX_H\,d\mu_H=0$ を用いる。

二次では、

$$
f_H(Y_H^{\mathrm c})^2
=
f_H^3+2f_H^2X_H+f_HX_H^2
$$

である。第一項は AHW2 の純粋な source 三次モーメントの相殺、第二項は AHZ の uniform-center 相殺、第三項は AHS の Ward 相殺を保持した AHZ の別の定理で消える。特に、偶数の crossing power を含む $\int f_HX_H^2\,d\mu_H=0$ を、奇対称性だけから導いてはいない。

三次では、

$$
f_H(Y_H^{\mathrm c})^3
=
f_H^4+3f_H^3X_H+3f_H^2X_H^2+f_HX_H^3.
$$

AHZ の $\int f_H^3X_H\,d\mu_H=0$ と $\int f_HX_H^3\,d\mu_H=0$ を用い、$Q_{4,H}$ と $3D_H(B)$ を保持する。$D_H(B)$ を独立なモーメントの積へ置き換えたり、零としたりしない。

各項の可積分性は、連続性と compact support から供給する。さらに `p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable` は、任意の自然数 $n$ について $\int f_H(Y_H^{\mathrm c})^n\,d\mu_H$ の被積分関数の可積分性を与える。

## 6． 中心化三次積分と近似中心

前節のモーメントと source の平均零により、任意の実数 $\beta$ について

$$
\begin{aligned}
&\int f_H(A)
\left(
1-\beta Y_H^{\mathrm c}(A,B)
+\frac{(\beta Y_H^{\mathrm c}(A,B))^2}{2}
-\frac{(\beta Y_H^{\mathrm c}(A,B))^3}{6}
\right)d\mu_H(A)\\
&\qquad
=
-\beta V_H
-\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr).
\end{aligned}
$$

これは `p4Q2PZ37AIC_originalCenteredCubicIntegral` である。二次の項が消える一方、三次の係数には真の四次・混合相関が残る。

正確な外因子を戻した近似中心を、

$$
\boxed{
P^{\mathrm c}_{3,H,\beta}(B)
=
e^{-\beta a_H(B)}
\left[
-\beta V_H
-\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
\right]
}
$$

と定義する。Lean の定義は `p4Q2PZ37AIC_originalFactoredCubicApproximation` である。

これは、中心化された指数に三次 Taylor 多項式を用い、外側の指数は正確に保持した近似中心である。外因子を含む全体を、$\beta$ に関する単なる三次多項式と扱わない。また、完全作用 $S_H$ を直接展開した AIA の近似中心とは区別する。

## 7． 全実数引数のスカラー四次剰余

スカラー関数

$$
r_4(x)
=
e^{-x}
-
\left(1-x+\frac{x^2}{2}-\frac{x^3}{6}\right)
$$

を `p4Q2PZ37AIC_expCubicRemainder` として定義する。中心化作用の符号を制限しないため、対象はすべての実数 $x$ である。

AIC のスカラー定理は、

$$
\boxed{
0\le r_4(x)
\le
e^{\max(0,-x)}\frac{x^4}{24}
\qquad(x\in\mathbb R)
}
$$

である。対応する宣言は `p4Q2PZ37AIC_expCubicRemainder_interval` であり、小ささの仮定は置かない。

$x\ge0$ の場合は、既存 AIA の $0\le r_4(x)\le x^4/24$ を使う。この半直線では $\max(0,-x)=0$ なので、指数係数は厳密に1となる。

$x\le0$ の場合は $u=-x\ge0$ と置き、正の指数から指数因子を取り除いた関数

$$
g(u)
=
1-e^{-u}
\left(1+u+\frac{u^2}{2}+\frac{u^3}{6}\right)
$$

を使う。実装では積の微分と多項式の整理によって、

$$
g(0)=0,
\qquad
g'(u)=e^{-u}\frac{u^3}{6}
$$

を接続する。$u\ge0$ では $0<e^{-u}\le1$ であるから、

$$
0\le g'(u)\le\frac{u^3}{6}
=
\frac{d}{du}\left(\frac{u^4}{24}\right).
$$

固定 mathlib の `image_le_of_deriv_right_le_deriv_boundary` による二つの微分比較から、

$$
0\le g(u)\le\frac{u^4}{24}
$$

を得る。これは `p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval` である。

最後に、

$$
r_4(-u)=e^u g(u)
$$

を用いて負の半直線の評価を得る。この方法は係数 $1/24$ を保持し、符号付きの引数を非負と仮定することなく全実数へ接続する。

## 8． 外因子を含む実際の剰余と正確な展開

新しい剰余を、元の source と Haar 測度による真の積分

$$
\boxed{
R^{\mathrm c}_{4,H,\beta}(B)
=
\int f_H(A)
\left[
e^{-\beta a_H(B)}
r_4\bigl(\beta Y_H^{\mathrm c}(A,B)\bigr)
\right]d\mu_H(A)
}
$$

として定義する。対応する定義は `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder` である。

外因子を積分の外に出す同じ剰余の表示は、

$$
R^{\mathrm c}_{4,H,\beta}(B)
=
e^{-\beta a_H(B)}
\int f_H(A)r_4\bigl(\beta Y_H^{\mathrm c}(A,B)\bigr)\,d\mu_H(A)
$$

である。連続なスカラー剰余、中心化作用、source の合成・積として、被積分関数の可積分性も任意の実 $\beta$ について供給される。

元の kernel の因子化と中心化三次積分を合わせることで、

$$
\boxed{
R^{\mathrm c}_{4,H,\beta}(B)
=
\mathcal T_{H,\beta}(B)-P^{\mathrm c}_{3,H,\beta}(B)
}
$$

および

$$
\boxed{
\mathcal T_{H,\beta}(B)
=
P^{\mathrm c}_{3,H,\beta}(B)+R^{\mathrm c}_{4,H,\beta}(B)
\qquad(\beta\in\mathbb R)
}
$$

を得る。主要な宣言は `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub` と `p4Q2PZ37AIC_originalTransfer_centeredCubic_expansion` である。

この $R^{\mathrm c}_4$ は、同じ物理的 transfer に対する新しい近似中心の実際の誤差である。AIA の完全作用を直接展開した剰余 $R_4$ と同一だとは扱わない。

## 9． 非負結合で残る点ごとの指数重み

ここから、剰余区間の評価には $\beta\ge0$ を仮定する。

任意の実数 $a,y$ について、

$$
e^{-\beta a}e^{\max(0,-\beta y)}
=
e^{-\beta\min(a,a+y)}
$$

である。$y\ge0$ と $y\le0$ の場合に分けることで、$a$ や $y$ の非負性を仮定せずにこの恒等式を使える。

全実数引数の剰余評価に正の外因子を掛けると、

$$
0\le e^{-\beta a}r_4(\beta y)
\le
e^{-\beta\min(a,a+y)}
\frac{\beta^4 y^4}{24}.
$$

これが `p4Q2PZ37AIC_expCubicRemainder_factored_interval` である。

元の $a_H(B)$ と $Y_H^{\mathrm c}(A,B)$ を代入し、$a_H+Y_H^{\mathrm c}=S_H$ を用いて、点ごとの重みを

$$
q_{H,\beta}(A,B)
=
e^{-\beta\min(a_H(B),S_H(A,B))}
$$

と定義する。Lean の定義は `p4Q2PZ37AIC_originalFactoredRemainderWeight` であり、第二の min 引数には元の完全作用が入る。

得られる元の kernel 剰余の評価は、

$$
\boxed{
0
\le
e^{-\beta a_H(B)}
r_4\bigl(\beta Y_H^{\mathrm c}(A,B)\bigr)
\le
\frac{\beta^4}{24}
q_{H,\beta}(A,B)
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4
}
$$

である。外因子の効果を、積分変数に依存するこの重みの中へ正確に保持する。

さらに、元の右半重みの下限から、

$$
\boxed{
0<q_{H,\beta}(A,B)
\le e^{-\beta W_H(B)/2}
\le1
\qquad(\beta\ge0)
}
$$

となる。上側の二つの不等式は `p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight` と `p4Q2PZ37AIC_originalFactoredRemainderWeight_le_one` に対応する。

## 10． Source の符号別に相関を保持した四次積分

元の source の正負部分を、AHY の定義のまま

$$
f_H^+(A)=\frac{|f_H(A)|+f_H(A)}2,
\qquad
f_H^-(A)=\frac{|f_H(A)|-f_H(A)}2
$$

とする。いずれも非負で、$f_H=f_H^+-f_H^-$ である。

AIC の新しい二つの量は、

$$
J^{\mathrm{w},+}_{4,H,\beta}(B)
=
\int f_H^+(A)\,
q_{H,\beta}(A,B)\,
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\,d\mu_H(A),
$$

$$
J^{\mathrm{w},-}_{4,H,\beta}(B)
=
\int f_H^-(A)\,
q_{H,\beta}(A,B)\,
\bigl(Y_H^{\mathrm c}(A,B)\bigr)^4\,d\mu_H(A)
$$

である。それぞれ `p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment` と `p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment` に対応する。

これらは source の符号、元の完全作用から作る指数重み、中心化作用の四次を同じ積分内に残した相関量である。各量は連続性から可積分であり、任意の実 $\beta$ で非負となる。

元の source の非加重正負質量が等しいことから、この二つの重み付き量の等しさを推論しない。両者を独立な積分の積や一様な個数予算へ置き換えず、別々の量として保持する。

## 11． 真の剰余区間と物理的 transfer の区間

$\beta\ge0$ において、外因子付きのスカラー剰余は非負である。したがって、その積に source の符号を反映すると、負の source 部分が下側、正の source 部分が上側に入る。

AIA の実数の符号分解不等式と Haar 積分の単調性を用いることで、

$$
\boxed{
-\frac{\beta^4}{24}J^{\mathrm{w},-}_{4,H,\beta}(B)
\le
R^{\mathrm c}_{4,H,\beta}(B)
\le
\frac{\beta^4}{24}J^{\mathrm{w},+}_{4,H,\beta}(B)
}
$$

を得る。これは `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_weightedInterval` である。

非負なのは source を掛ける前の kernel 剰余である。符号付き source を積分した $R^{\mathrm c}_4$ 自体が非負だとは主張しない。

正確な恒等式 $\mathcal T=P^{\mathrm c}_3+R^{\mathrm c}_4$ から、物理的 transfer の区間は

$$
\boxed{
P^{\mathrm c}_{3,H,\beta}(B)
-
\frac{\beta^4}{24}J^{\mathrm{w},-}_{4,H,\beta}(B)
\le
\mathcal T_{H,\beta}(B)
\le
P^{\mathrm c}_{3,H,\beta}(B)
+
\frac{\beta^4}{24}J^{\mathrm{w},+}_{4,H,\beta}(B)
}
$$

となる。対応する宣言は `p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval` である。

この区間は、元の相関量を残したままの評価である。以前の別の近似中心に対する区間との包含関係や、一様な幅の改善は主張しない。

## 12． 負の近似中心と条件付きの実 transfer 負性

$\beta\ge0$ では $Q_{4,H}+3D_H(B)\ge0$ であるため、

$$
P^{\mathrm c}_{3,H,\beta}(B)
\le
-e^{-\beta a_H(B)}\beta V_H.
$$

$\beta>0$ では、$V_H>0$ と指数の正値性から、

$$
\boxed{
P^{\mathrm c}_{3,H,\beta}(B)<0
}
$$

となる。これらは `p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance` と `p4Q2PZ37AIC_originalFactoredCubicApproximation_neg` に対応する。負なのは近似中心であり、実際の transfer の負性には剰余の上側を比較する必要がある。

完全な三次係数を利用した条件付き定理は、$\beta\ge0$ と

$$
\boxed{
\frac{\beta^4}{24}J^{\mathrm{w},+}_{4,H,\beta}(B)
<
e^{-\beta a_H(B)}
\left[
\beta V_H+\frac{\beta^3}{6}\bigl(Q_{4,H}+3D_H(B)\bigr)
\right]
}
$$

を仮定すると、

$$
\mathcal T_{H,\beta}(B)<0
$$

を結論する。宣言は `p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin` である。

また、$\beta>0$ における、より強い十分条件

$$
\frac{\beta^4}{24}J^{\mathrm{w},+}_{4,H,\beta}(B)
<
e^{-\beta a_H(B)}\beta V_H
$$

からも同じ負性が従う。これは `p4Q2PZ37AIC_originalTransfer_negative_of_factoredVarianceMargin` である。こちらは右辺に有利な三次項を使わないため、条件としては強くなる。

元の固定結合

$$
\beta_0=\frac{\log(3/2)}{64}>0
$$

については、区間定理と完全な重み付き margin による負性定理をそのまま特殊化する。対応する宣言は `p4Q2PZ37AIC_originalFixedTransfer_centeredWeightedQuarticInterval` と `p4Q2PZ37AIC_originalFixedTransfer_negative_of_weightedCenteredQuarticMargin` である。

固定結合の区間には追加の margin 仮定はない。一方、その区間の上端を負にするための真の重み付き margin は、固定結合版の負性定理にも明示的に残っている。

## 13． 下端の非正性が示す範囲

$\beta\ge0$ では、近似中心が非正であり、$J^{\mathrm{w},-}_{4,H,\beta}(B)\ge0$ なので、

$$
\boxed{
P^{\mathrm c}_{3,H,\beta}(B)
-
\frac{\beta^4}{24}J^{\mathrm{w},-}_{4,H,\beta}(B)
\le0
}
$$

となる。これは `p4Q2PZ37AIC_originalCenteredQuarticLowerEndpoint_nonpos` である。

この区間の下端は、正の transfer を保証する正の下界にはならない。それは、この下端を使う証明方法の限界である。実際の transfer が非正であることや、正の transfer が存在しないことを示す定理ではない。

## 14． 主要 API の対応

スカラー宣言は `MGAP4D.MathlibAnalytic`、元の模型に関する宣言は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。

| 主な宣言 | 役割・仮定 |
|---|---|
| `p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval` | $u\ge0$ での $g(u)$ の微分比較と係数 $1/24$ |
| `p4Q2PZ37AIC_expCubicRemainder_interval` | 全実数 $x$ の非負剰余と指数付き上界 |
| `p4Q2PZ37AIC_expCubicRemainder_factored_interval` | $\beta\ge0$、任意の実 $a,y$ における min-weight 評価 |
| `p4Q2PZ37AIC_originalTransfer_factorization` | 全実 $\beta$ に対する同じ物理的 transfer の正確な因子化 |
| `p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero` | Ward 相殺を含む $\int f_H(Y_H^{\mathrm c})^2=0$ |
| `p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact` | 真の $Q_{4,H}+3D_H(B)$ の保持 |
| `p4Q2PZ37AIC_originalCenteredCubicIntegral` | 全実 $\beta$ の中心化三次多項式積分 |
| `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub` | 新しい真の誤差 $R^{\mathrm c}_4=\mathcal T-P^{\mathrm c}_3$ |
| `p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval` | $\beta\ge0$ の相関を保持した transfer 区間 |
| `p4Q2PZ37AIC_originalFactoredCubicApproximation_neg` | $\beta>0$ の近似中心の厳密な負性 |
| `p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin` | 完全な重み付き margin からの条件付き実 transfer 負性 |
| `p4Q2PZ37AIC_originalCenteredQuarticLowerEndpoint_nonpos` | 正の下界をこの区間から得ることの限界 |
| `p4Q2PZ37AIC_originalFixedTransfer_negative_of_weightedCenteredQuarticMargin` | 元の固定結合で margin を保持した特殊化 |

## 15． AIB の障害との関係、未解決範囲、次段階 AID

AIB が示した、元の旧粗い四次予算に基づく半分散・scaled margin の障害は保持される。AIC はその定理や予算の定義を変更しない。中心化作用の三次展開と、新しい実際の剰余 $R^{\mathrm c}_4$ を導入し、元の物理的 transfer に対する別の正確な表示と条件付き区間を接続する。

新しい重み付き条件の成立は、今回の結果ではない。特に、指数因子が誤差の評価に現れることだけで符号を結論しない。近似中心の信号にも正確な外因子 $e^{-\beta a_H(B)}$ が掛かっており、示すべき比較は前節の明示的な margin そのものである。

次の事項は今回の定理内容に含まれない。

- 元の固定結合で重み付き margin を満たす具体的な境界の構成。
- 元の実 transfer の無条件の正負判定や、正負 shell の存在。
- $J^{\mathrm{w},+}_{4,H,\beta}(B)$ と $J^{\mathrm{w},-}_{4,H,\beta}(B)$ の等値、数値評価、独立性。
- 旧区間に対する新しい区間の無条件の包含関係や、幅の一様な改善。
- AIB が扱った旧粗い条件の障害が消えたという主張。
- 体積一様な coercivity、Hamiltonian gap、連続極限の Yang–Mills mass gap。

次段階 AID の候補は、元の source・完全作用・Haar 測度を保ったまま、実際の重み付き四次相関を評価し、有効な margin が成立するかを検証することである。負性の証明では、とくに上端に現れる $J^{\mathrm{w},+}_{4,H,\beta}(B)$ を、正確な外因子と真の三次係数を含む信号と比較する必要がある。

$|Y_H^{\mathrm c}|\le3p_H/2$ や $q_{H,\beta}\le e^{-\beta W_H(B)/2}$ という一様評価だけを代入して、新しい margin の成立や実際の transfer の符号を結論しない。保持した相関がどこまで評価できるか、また必要な厳密不等式が元の境界で成立するかは、今後の証明対象として残る。

## 16．新規46宣言と個別公理出力

次の38定理と8定義を、それぞれ個別の `#print axioms` 対象とする。No. 1–5 は `MGAP4D.MathlibAnalytic`、No. 6–46 は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint` に属する。ローカルinstanceはこの新規公開宣言数には含めない。

| No. | 宣言 | 種別 |
| --- | --- | --- |
| 1 | `p4Q2PZ37AIC_expCubicRemainder` | 定義 |
| 2 | `p4Q2PZ37AIC_expCubicRemainder_continuous` | 定理 |
| 3 | `p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval` | 定理 |
| 4 | `p4Q2PZ37AIC_expCubicRemainder_interval` | 定理 |
| 5 | `p4Q2PZ37AIC_expCubicRemainder_factored_interval` | 定理 |
| 6 | `p4Q2PZ37AIC_originalBoundaryConstant` | 定義 |
| 7 | `p4Q2PZ37AIC_originalCenteredAction` | 定義 |
| 8 | `p4Q2PZ37AIC_originalCenteredAction_continuous` | 定理 |
| 9 | `p4Q2PZ37AIC_originalCenteredAction_abs_le_threeHalfCount` | 定理 |
| 10 | `p4Q2PZ37AIC_originalBoundaryConstant_nonneg` | 定理 |
| 11 | `p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction` | 定理 |
| 12 | `p4Q2PZ37AIC_originalMinAction_ge_rightHalfweight` | 定理 |
| 13 | `p4Q2PZ37AIC_originalKernel_factorization` | 定理 |
| 14 | `p4Q2PZ37AIC_originalCenteredKernel_continuous` | 定理 |
| 15 | `p4Q2PZ37AIC_originalCenteredKernelWeightedSource_integrable` | 定理 |
| 16 | `p4Q2PZ37AIC_originalTransfer_factorization` | 定理 |
| 17 | `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder` | 定義 |
| 18 | `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_integrable` | 定理 |
| 19 | `p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable` | 定理 |
| 20 | `p4Q2PZ37AIC_originalCenteredAction_firstMoment` | 定理 |
| 21 | `p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero` | 定理 |
| 22 | `p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact` | 定理 |
| 23 | `p4Q2PZ37AIC_originalCenteredCubicIntegrand_integrable` | 定理 |
| 24 | `p4Q2PZ37AIC_originalCenteredCubicIntegral` | 定理 |
| 25 | `p4Q2PZ37AIC_originalFactoredCubicApproximation` | 定義 |
| 26 | `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_const_mul` | 定理 |
| 27 | `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub` | 定理 |
| 28 | `p4Q2PZ37AIC_originalTransfer_centeredCubic_expansion` | 定理 |
| 29 | `p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance` | 定理 |
| 30 | `p4Q2PZ37AIC_originalFactoredCubicApproximation_neg` | 定理 |
| 31 | `p4Q2PZ37AIC_originalFactoredRemainderWeight` | 定義 |
| 32 | `p4Q2PZ37AIC_originalFactoredRemainderWeight_continuous` | 定理 |
| 33 | `p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable` | 定理 |
| 34 | `p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment` | 定義 |
| 35 | `p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment` | 定義 |
| 36 | `p4Q2PZ37AIC_originalWeightedCenteredFourthMoments_nonneg` | 定理 |
| 37 | `p4Q2PZ37AIC_originalFactoredKernelRemainder_interval` | 定理 |
| 38 | `p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_weightedInterval` | 定理 |
| 39 | `p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight` | 定理 |
| 40 | `p4Q2PZ37AIC_originalFactoredRemainderWeight_le_one` | 定理 |
| 41 | `p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval` | 定理 |
| 42 | `p4Q2PZ37AIC_originalCenteredQuarticLowerEndpoint_nonpos` | 定理 |
| 43 | `p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin` | 定理 |
| 44 | `p4Q2PZ37AIC_originalTransfer_negative_of_factoredVarianceMargin` | 定理 |
| 45 | `p4Q2PZ37AIC_originalFixedTransfer_centeredWeightedQuarticInterval` | 定理 |
| 46 | `p4Q2PZ37AIC_originalFixedTransfer_negative_of_weightedCenteredQuarticMargin` | 定理 |

最終成功CIログで、この46件の完全修飾名を宣言一覧と一対一照合した。欠落・余剰・重複は0件で、46件とも標準 `propext`・`Classical.choice`・`Quot.sound` のみである。新しい公理・`sorry`・`admit`・`sorryAx` を用いない。

## 17．全文・imports・依存定理・固定APIの照合

新規ファイルの直接importは次の2件である。

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB
import Mathlib.Tactic
```

AIBの既存依存閉包をそのまま継承する。AHPの元の物理的transferの連続積分表示と可積分性、AHQの元crossingの非負性・中心化評価、AHW2のsource三次モーメント消滅、AHYの元source正負部分、AHZの真正混合相殺と四次相関、AIAの非負引数スカラー剰余・符号分解不等式の実際のsignatureを照合した。

固定mathlibでは、[MeanValue.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/MeanValue.lean) の `image_le_of_deriv_right_le_deriv_boundary` を使う。境界値と区間上の片側微分比較を明示し、割引指数関数を零関数および四次多項式と比較する。微分の指数合成は [ExpDeriv.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean) の `HasDerivAt.exp` を使う。これは連続性のmethod名とは別である。

指数関数の連続性は [Exp.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Exp.lean) の `Real.continuous_exp.comp` により明示的に合成する。絶対値の三角不等式は [Algebra/Order/Group/Unbundled/Abs.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/Group/Unbundled/Abs.lean) の `@[to_additive] lemma mabs_mul_le` が生成する `abs_add_le` を使う。

各積分の加法分解では可積分性を先に供給し、入れ子の関数加法は `Pi.add_apply` で明示的に整形した。`Integrable.congr` による代替sourceへのすり替えは行っていない。元の物理的sourceと連続代表の接続には既存のAHP定理を用いる。定義上の積の結合や符号の正規化には `ring` を用い、定理の仮定を強くしてelaborationを回避しない。

最終893行全文、すべてのimports、各既存依存定理の引数、全実結合と非負結合の使い分けを再点検した。静的preflightのローカル参照として配置したAIBファイルは、canonical blob `3da94b4d2ef9a4b4bc4777c854d64ec9eba819d1` とbyte一致し、PRの変更対象ではない。リモート差分はAICの新規Lean leaf一件のみである。

## 18．初回CI失敗と主張を保持した修正

初回source `66864ef333a7389baad0a62353aaacfc43c19196` の [CI #42447001486](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42447001486) は、workflow・Lean job・必須stepの完了状態で **FAILURE** と確定した。変更ファイルのerrorは2件、warningは0件である。

- `abs_add` は固定mathlibに存在する目的のAPI名ではなかったため、`abs_add_le` に修正した。
- `Continuous.exp` はこの固定版には存在しないため、`Real.continuous_exp.comp` による明示的な合成へ修正した。固定版の連続性methodは `Continuous.rexp` である。

初回ログの46個別出力のうち9件には、上記errorに由来する `sorryAx` が伝播していた。そのログおよび `source_result=failure` のreceiptを成功根拠にしない。初回に存在した標準公理だけの37件も、最終成功の代用にはしていない。

修正前後で全宣言の型、定義、仮定、物理対象、imports、toolchain、workflowは不変である。同種の絶対値・指数連続性の呼び出しを全文で再走査し、正しい微分method `HasDerivAt.exp` は保持した。修正版の全文readbackとpreflightを再実行し、新しいexact-sourceに対する完了結果を第1節の証拠とした。

## 19．保存範囲と文書同期

既存Lean、元のhalfweight・source・Wilson action・Haar・物理的transfer・固定結合・型付き証明履歴、canonical root、Lean/mathlib pin、workflowを変更しない。AICで追加したのは補助的な中心化量・因子化された近似中心・実際の誤差・相関量と、それらを元の物理的transferへ接続する定理である。

この正式記録は新規path `docs/proofs/P4-Q2-PZ37AIC_verified_20261108.md` へappendし、formalからmainへ同一Git blobを文書だけのPRで同期する。文書PRではLeanを変更せず、Strict Leanを追加実行しない。main mergeに既存設定で自動起動するpush workflowは、上記exact-source定理CIおよび文書PRの実行とは区別し、設定変更や手動dispatchは行わない。

本記録の数学的到達点は、真正中心化Boltzmann因子化と重み付き四次剰余区間、および明示的marginを前提とする符号定理である。固定結合でのmargin成立の実例、正負二殻、体積一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills質量ギャップは未証明のままである。
