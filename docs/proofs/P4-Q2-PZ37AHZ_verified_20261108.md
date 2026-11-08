# P4-Q2-PZ37AHZ — 正式Lean4証明記録（2026-11-08 JST）

著作権：板倉英俊（Hidetoshi Itakura）。

唯一の形式定理正本：`formal/real-hilbert-uniform-coercive-strong-limit`。GitHub main は正式文書ミラー。append-only／tighten-only／overwrite-forbidden／same-root。元のSU(2)完全Wilson一スラブ作用、両端の空間halfweight、元ZW signed source、元の空間積Haar、型付き証明履歴、root、固定Lean/mathlib、workflowを保持。

## 1．Exact-source証明台帳

| 項目 | 検証済みの結果 |
| --- | --- |
| [AHZ定理PR #6493](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6493) | **MERGED** |
| 継承元AHY正式記録HEAD | `48954d8ccb304c81981cd983991740441a77a3a8` |
| 最終exact-source HEAD | `31008ce886146f45e83d2ca676c1edbb12f60a10` |
| exact test-merge HEAD | `ce5ee88f3c502c0860e25602332f5f596a500ae4` |
| 定理squash HEAD | `82837f5851b9e29cbae29683d43c9cb251fbc119` |
| source／test-merge／squash共通Git tree | `a5d99eec2c9f1290fc8bba3834550b3cfa51c9a8`、完全一致 |
| 最終exact-source CI | [#42440526585](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42440526585) — **completed／SUCCESS** |
| Changed Lean job・Lean step 17 | `128608586293` — **completed／SUCCESS** |
| 独立completion receipt job | `128609605643` — **completed／SUCCESS** |
| exact-head receipt context | `chatgpt-ci-receipt/PR Lean Fast Check` — **success** |
| Strict Lean依存閉包 | **11,388／11,388 SUCCESS** |
| 新規定理の公理確認 | **26／26**、`propext`・`Classical.choice`・`Quot.sound` のみ |
| `sorryAx` | **なし** |
| 変更Lean warning／error | **0／0** |
| 成功CIログartifact | `13601801543`、`lean-fast-check-log` |
| 新規Leanファイル | **1件・560行**、既存ファイル変更なし |
| 新規Lean blob | `89f05bfda92700d9a58ad520ee1444368a69f091`、最終全文readback一致 |

固定環境：Lean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。成功ログの最終結果は `Build completed successfully (11388 jobs).`。変更ファイルの26定理を個別に確認。既存依存ファイルの歴史的warningと今回の変更ファイルのwarningを区別する。

成功artifactのdigest：`sha256:56ad57349b9fc3b16dc21f01acd4cf3e129f03f608b03a732e6a3350c6b4c1dc`。CI workflow、Lean job、Lean step、独立receiptはいずれも完了した状態で確認し、receiptのtarget URLも同一の最終runである。source／test-merge／squash treeの一致をGitHub MCPで直接確認した。

## 2． 元の定義と主結論

任意の有限の元格子パラメータ $H\in\mathbb N$ と元の右境界配置 $B$ を固定する。配置空間は `PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2`、測度 $\mu_H$ は `periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2`、すなわち元の正規化 SU(2) 有限積 Haar 測度である。

元の Wilson エネルギーを $E=\texttt{specialUnitaryWilsonPlaquetteEnergy 2}$ と書く。実際の空間 plaquette と crossing link のリストを用いて、

$$
\begin{aligned}
W_H(A)&=\sum_{q} E\bigl(\operatorname{Hol}(A,q)\bigr),\\
S_H^{\mathrm{cross}}(A,B)&=\sum_e E\bigl(A(e)^{-1}B(e)\bigr),\\
p_H&=\#\{\text{元の空間 plaquette}\}
     =\#\{\text{元の crossing link}\},\\
f_H(A)&=\frac{W_H(A)-p_H}{2},\\
S_H(A,B)&=\frac12W_H(A)+S_H^{\mathrm{cross}}(A,B)+\frac12W_H(B).
\end{aligned}
$$

source は `p4Q2PZ37AFZ_originalCenteredContinuous H`、$p_H$ は `p4Q2PZ37AFZ_plaquetteCount H` である。両境界の空間半重み、元の source、元の Haar 測度を保持する。

既存の中心化とモーメント定理は、

$$
\int f_H\,d\mu_H=0,\qquad
\int f_H^3\,d\mu_H=0,\qquad
V_H:=\int f_H^2\,d\mu_H>0
$$

を与える。二番目は AHW2 の source 奇対称性による既存結果である。AHZ の対象は、これとは異なる元の完全作用の符号付き三次モーメント

$$
M_{3,H}^{\mathrm{full}}(B):=
\int f_H(A)S_H(A,B)^3\,d\mu_H(A)
$$

である。その主恒等式は

$$
\boxed{
M_{3,H}^{\mathrm{full}}(B)
=Q_{4,H}+\frac34\bigl(3p_H+W_H(B)\bigr)^2V_H+3D_H(B),
}
$$

ここで $Q_{4,H}\ge0$、$D_H(B)\ge0$ は、以下で定義する実際の元の Haar 積分である。[AHZ]

## 3． 一様な左中心写像と Haar 保存

SU(2) の実際の中心元 $z=-I$ を用い、

$$
U_H(A)(e)=zA(e)
$$

を明示的に構成する。Lean 定義は `p4Q2PZ37AHZ_originalUniformCenter`。$z^2=1$ から $U_H^2=\mathrm{id}$ を得る。各座標の左乗法が正規化 Haar を保存することを `normalizedCompactHaar_measurePreserving_mul_left_right` から取り出し、`Measure.pi_map_pi` で元の有限積測度へ持ち上げる。

対応する宣言は `p4Q2PZ37AHZ_originalUniformCenter_involutive` と `p4Q2PZ37AHZ_originalUniformCenter_Haar_measurePreserving` である。

空間 holonomy の四つの中心因子は、逆向きの二辺も含めて相殺する。これにより

$$
\operatorname{Hol}(U_HA,q)=\operatorname{Hol}(A,q),\qquad
W_H(U_HA)=W_H(A),\qquad f_H(U_HA)=f_H(A)
$$

を得る。一方、一つの crossing エネルギーは $E\mapsto2-E$ となるため、元のリンク数を正確に合計して

$$
S_H^{\mathrm{cross}}(U_HA,B)=2p_H-S_H^{\mathrm{cross}}(A,B)
$$

を得る。これらは `p4Q2PZ37AHZ_originalPlaquetteHolonomy_uniformCenter`、`p4Q2PZ37AHZ_originalSpatialWilson_uniformCenter_invariant`、`p4Q2PZ37AHZ_originalSource_uniformCenter_invariant`、`p4Q2PZ37AHZ_originalCrossing_uniformCenter_complement` に対応する。この写像は全リンクで同じ中心元を用い、source を保存する。[AHZ]

## 4． 中心化した crossing と二種類の消去

$$
X_H(A,B):=S_H^{\mathrm{cross}}(A,B)-p_H,\qquad
a_H(B):=\frac{3p_H+W_H(B)}2
$$

と置く。Lean の $X_H$ の定義は `p4Q2PZ37AHZ_originalCenteredCrossing` である。完全作用の正確な分解と中心写像の作用は

$$
S_H(A,B)=f_H(A)+a_H(B)+X_H(A,B),\qquad
X_H(U_HA,B)=-X_H(A,B)
$$

となる。前者は `p4Q2PZ37AHZ_originalFullAction_centered_decomposition`、後者は `p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd` である。

### 4.1 奇数次 crossing の消去

連続関数 $g$ が $g\circ U_H=-g$ を満たすとき、実際に構成した Haar 保存写像による積分の変数変換から $\int g\,d\mu_H=0$ を得る。これが `p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero` である。

従って、任意の連続な $U_H$-不変重み $g$ に対して

$$
\int g(A)X_H(A,B)\,d\mu_H(A)=0,\qquad
\int g(A)X_H(A,B)^3\,d\mu_H(A)=0.
$$

対応する一般定理は `p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingHaar_zero` と `p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingCubeHaar_zero`。特に、任意の $n\in\mathbb N$ に対して

$$
\int f_H^nX_H\,d\mu_H=0,\qquad
\int f_H^nX_H^3\,d\mu_H=0
$$

が `p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero` と `p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero` により得られる。source の次数 $n$ は任意であり、ここで明示的に扱った crossing の次数は 1 と 3 である。相関積分の因数分解は用いない。[AHZ]

### 4.2 偶数次の $\int f_HX_H^2$ は AHS で消去

$f_HX_H^2$ は一様中心写像に対して偶であるため、上記の奇対称性だけでは消えない。実装は

$$
X_H^2=p_H^2-2p_HS_H^{\mathrm{cross}}+\bigl(S_H^{\mathrm{cross}}\bigr)^2
$$

を展開し、既存の `p4Q2PZ37AHS_originalSource_quadraticCrossingHaar_zero H B (pH ^ 2) (-2 * pH) 1` を適用する。結果は

$$
\int f_HX_H^2\,d\mu_H=0
$$

であり、AHZ の宣言は `p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero` である。この偶数次の消去には、AHS の実際の二 crossing Ward 結果が必要である。[AHZ] [AHS]

## 5． 十項展開から完全作用三次モーメントへ

以下、$f=f_H(A)$、$X=X_H(A,B)$、$a=a_H(B)$ と略記する。元の被積分関数は、正確に

$$
\begin{aligned}
f(f+a+X)^3={}&f^4+3af^3+3f^3X+3a^2f^2+6af^2X\\
&+3f^2X^2+a^3f+3a^2fX+3afX^2+fX^3
\end{aligned}
$$

と展開される。各項の扱いは次のとおり。

| 項 | Haar 積分後 | 根拠 |
|---|---|---|
| $f^4$ | $Q_{4,H}$ | 実際の四次 source モーメントとして保持 |
| $3af^3$ | $0$ | AHW2 の $\int f^3=0$ |
| $3f^3X$ | $0$ | AHZ の source 次数 3、crossing 次数 1 |
| $3a^2f^2$ | $3a^2V_H$ | 元の source 二次モーメント |
| $6af^2X$ | $0$ | AHZ の source 次数 2、crossing 次数 1 |
| $3f^2X^2$ | $3D_H(B)$ | 実際の非負相関として保持 |
| $a^3f$ | $0$ | AHP の元の Haar 中心化 |
| $3a^2fX$ | $0$ | AHZ の source 次数 1、crossing 次数 1 |
| $3afX^2$ | $0$ | AHS による偶数次消去 |
| $fX^3$ | $0$ | AHZ の source 次数 1、crossing 次数 3 |

保持する二つの積分は

$$
Q_{4,H}:=\int f_H(A)^4\,d\mu_H(A),\qquad
D_H(B):=\int f_H(A)^2X_H(A,B)^2\,d\mu_H(A).
$$

Lean 定義は `p4Q2PZ37AHZ_originalSourceFourthHaarMoment` と `p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment`。非負性はそれぞれの被積分関数から得られる。

代数と積分の分配は `p4Q2PZ37AHZ_cubicIntegral_of_centeredCancellations` にまとめられている。ここで受け取る五つの消去等式は、最終定理で上記の元モデルの補題からすべて供給する。有限積のコンパクト配置空間上で各項の連続性・可積分性を確認してから積分を分配する。

従って `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact` は

$$
M_{3,H}^{\mathrm{full}}(B)
=Q_{4,H}+3a_H(B)^2V_H+3D_H(B)
=Q_{4,H}+\frac34(3p_H+W_H(B))^2V_H+3D_H(B)
$$

を与える。$Q_{4,H}$ と $D_H(B)$ は保持された実際の積分であり、個別の数値を評価したという意味ではない。[AHZ]

## 6． 明示的な正の下界

非負な二項を残した恒等式から、

$$
\boxed{
L_{3,H}(B):=\frac34(3p_H+W_H(B))^2V_H
\le M_{3,H}^{\mathrm{full}}(B).
}
$$

既存の `p4Q2PZ37AHN_count_pos H`、`p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H`、元の空間 Wilson action の非負性により、$p_H>0$、$V_H>0$、$W_H(B)\ge0$ である。従って

$$
L_{3,H}(B)>0,\qquad M_{3,H}^{\mathrm{full}}(B)>0
$$

が任意の元の有限 $H$ と右境界 $B$ について得られる。対応する宣言は `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor` と `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_pos` である。下界は元の $V_H$ を含み、体積に依存しない定数を与える主張ではない。[AHZ]

## 7． AHY の $J_+$ と $J_-$ の正確な差

AHY の source 部分は

$$
f_+(A)=\frac{|f_H(A)|+f_H(A)}2,\qquad
f_-(A)=\frac{|f_H(A)|-f_H(A)}2
$$

であり、$f_H=f_+-f_-$ を満たす。AHY の元の cubic 相関は

$$
J_+(B)=\int f_+(A)S_H(A,B)^3\,d\mu_H(A),\qquad
J_-(B)=\int f_-(A)S_H(A,B)^3\,d\mu_H(A).
$$

これらは `p4Q2PZ37AHY_originalPositiveActionCubeMoment` と `p4Q2PZ37AHY_originalNegativeActionCubeMoment` である。source の元の中心化から、重みを掛けない質量はともに $\frac12\int|f_H|\,d\mu_H$ となる。[AHY]

作用三乗で重みを掛けると、AHZ は

$$
\boxed{
J_+(B)-J_-(B)=M_{3,H}^{\mathrm{full}}(B)>0,
\qquad
J_-(B)+L_{3,H}(B)\le J_+(B)
}
$$

を与える。宣言は `p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub`、`p4Q2PZ37AHZ_originalSourcePartCubeMoments_strictOrder`、`p4Q2PZ37AHZ_originalSourcePartCubeMoments_varianceSeparation`。source 自体を正値関数へ置き換えず、同じ符号付き source の二部分を比較している。[AHZ]

## 8． 到達範囲と次段階 AIA

AHZ の結果は、元の Haar 測度における完全作用三次モーメントの正確な分解と正値性である。純粋な source 三次モーメント $\int f_H^3=0$ と両立する。$Q_{4,H}$ と $D_H(B)$ の個別の exact value、相関の独立性、固定結合での転送の符号、体積に一様な coercivity、Hamiltonian gap、連続極限の Yang–Mills gap はここでは得ていない。

特に、$J_+>J_-$ だけでは AHY の二次 Taylor 剰余 $R_3$ の符号は決まらない。AHY の保証は、$\beta\ge0$ に対する

$$
-\frac{\beta^3}{6}J_+(B)\le R_3(\beta,B)
\le\frac{\beta^3}{6}J_-(B)
$$

であり、これを $R_3<0$ と読み替えることはできない。[AHY]

次段階 AIA の候補は、元の Boltzmann 転送

$$
T_\beta f_0(B)=\int f_H(A)e^{-\beta S_H(A,B)}\,d\mu_H(A)
$$

に対する三次 Taylor 展開と四次剰余の形式化である。接続すべき形は

$$
T_\beta f_0(B)
=-\beta V_H
+\frac{\beta^2}{2}(3p_H+W_H(B))V_H
-\frac{\beta^3}{6}M_{3,H}^{\mathrm{full}}(B)
+R_4(\beta,B).
$$

AHZ はこの三次項に投入する正の $M_{3,H}^{\mathrm{full}}$ を供給する。実際の転送に対する上式と制御された四次剰余は AIA 側の新たな証明課題である。固定結合での符号を得るには、完成した剰余評価を含む具体的な margin の証明がさらに必要となる。

## 9．検証済みの26定理

共通namespace：`MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`。以下の26定理について、最終CIの個別 `#print axioms` 出力を照合した。

| No. | Lean theorem |
| --- | --- |
| 1 | `p4Q2PZ37AHZ_originalUniformCenter_involutive` |
| 2 | `p4Q2PZ37AHZ_originalUniformCenter_Haar_measurePreserving` |
| 3 | `p4Q2PZ37AHZ_originalPlaquetteHolonomy_uniformCenter` |
| 4 | `p4Q2PZ37AHZ_originalSpatialWilson_uniformCenter_invariant` |
| 5 | `p4Q2PZ37AHZ_originalSource_uniformCenter_invariant` |
| 6 | `p4Q2PZ37AHZ_originalSingleCrossing_uniformCenter_complement` |
| 7 | `p4Q2PZ37AHZ_originalCrossing_uniformCenter_complement` |
| 8 | `p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd` |
| 9 | `p4Q2PZ37AHZ_originalCenteredCrossing_continuous` |
| 10 | `p4Q2PZ37AHZ_originalFullAction_centered_decomposition` |
| 11 | `p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero` |
| 12 | `p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingHaar_zero` |
| 13 | `p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingCubeHaar_zero` |
| 14 | `p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero` |
| 15 | `p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero` |
| 16 | `p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero` |
| 17 | `p4Q2PZ37AHZ_originalSourceFourthHaarMoment_nonneg` |
| 18 | `p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment_nonneg` |
| 19 | `p4Q2PZ37AHZ_originalThirdFullAction_integrable` |
| 20 | `p4Q2PZ37AHZ_cubicIntegral_of_centeredCancellations` |
| 21 | `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact` |
| 22 | `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor` |
| 23 | `p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_pos` |
| 24 | `p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub` |
| 25 | `p4Q2PZ37AHZ_originalSourcePartCubeMoments_strictOrder` |
| 26 | `p4Q2PZ37AHZ_originalSourcePartCubeMoments_varianceSeparation` |

## 10．全文確認と修正履歴

直接importは検証済みAHY leafと `Mathlib.Tactic`。変更Lean全文、元の中心元に関するPV/AHW/AHW2、AHSの二crossing Ward消去、AHNの正値性、AHYの可積分性とsource部分の定義を確認した。固定mathlibの [Bochner積分API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) を読み、実際の `integral_add`、`integral_sub`、`integral_const_mul`、`integral_map` と照合した。独立レビューでも十項展開、残る三項、五つの明示的な消去条件の無条件な供給、非負性とstrict positivity、AHYへの接続を確認した。

初回 [CI #42439618243](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42439618243) は、積分分配helperの2箇所で失敗した。複合 `Integrable.add` から推論された関数和 `Pi.add` と、点ごとに展開されたlambdaの表現がrewrite時に一致しなかった。固定APIと既存AHS/AHPの実装を確認し、局所分割等式を `simp only [Pi.add_apply]` で正規化してから外側から内側へ書き換える形に修正した。初回の失敗時にhelperと依存定理へ付いた自動的な `sorryAx` 出力は成功証拠として採用していない。

二回目 [CI #42440128838](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42440128838) は全26定理を標準公理のみで検証し、独立receiptも成功した。ただし点ごとの等式で不要となった `change` 命令にwarningが1件残ったため、その1行だけを削除した。最終source `31008ce886146f45e83d2ca676c1edbb12f60a10` のCIでwarning／error 0／0を確認した。

修正は証明の表現に限定され、定理文・仮定・物理定義・toolchain・workflowを弱めたり変更したりしていない。新規leaf以外の既存ファイル、過去の証明記録、canonical rootを変更していない。

[AHZ]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/31008ce886146f45e83d2ca676c1edbb12f60a10/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformCenterCubicActionMomentV5_PZ37AHZ.lean
[AHY]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/31008ce886146f45e83d2ca676c1edbb12f60a10/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY.lean
[AHS]: https://github.com/itakura-hidetoshi/4d-mass-gap/blob/31008ce886146f45e83d2ca676c1edbb12f60a10/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingQuadraticHaarSecondMomentV5_PZ37AHS.lean

