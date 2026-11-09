# P4-Q2-PZ37AIT — 元の有理Ward transfer評価と体積により拡大する半Haar結合範囲

2026年11月9日 JST。元の完全Wilson物理対象を保持した新規leafを、固定Lean4環境のExact-source CIと実公理出力で認証した。定理PR #6554はMERGED。以下の数学は各定理の仮定・有限体積の範囲で形式証明された内容であり、未解決の物理的障害を別に保持する。

参照基準はcanonical formal `948431e2aab5b957ae5a737d763b3b1326afc86e`。定理正本は `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラーである。append-only／tighten-only／overwrite-forbidden／same-rootを維持する。元の完全SU(2) Wilson作用、両端halfweight、符号付きZW物理源と連続代表、真正正規化積Haar、AIGの元の全余裕と厳密負領域、既存仮定・定理・公開root・固定環境を保持する。

## 1．研究対象と保持する元の物理量

本節は、[認証済みAIT source](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/57cbe6241f41adbface0d8e379f9e98d81bf723a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT.lean)に記載した数学的内容と証明構造を整理する。CIの完了・実公理出力・統合状態は、認証欄で別に確定する。

有限体積指標を \(H\in\mathbb N\)、元のplaquette数を \(p_H\)、元の連続源を \(f_H\)、対応する符号付きZW物理L²源を \(f_{0,H}\)、真正正規化空間積Haarを \(\mu_H\) とする。既存の物理定義と恒等式は

\[
p_H=24(H+1)^3>0,\qquad
V_H=\int f_H(A)^2\,d\mu_H(A)>0,
\]
\[
|f_H(A)|\le\frac{p_H}{2},\qquad
W_H(A)=p_H+2f_H(A).
\]

元の完全Wilson作用によるtransferを \(T_{H,\beta}\)、元の交差kernelを \(K^{\mathrm{cross}}_{H,\beta}\)、元の交差分配関数を \(Z_H^{\mathrm{cross}}\) とする。両端の空間halfweightを保持し、AIGの元の余裕と厳密負領域もそのまま

\[
\varepsilon_{H,\beta}
=\frac{\beta Z_H^{\mathrm{cross}}(\beta)e^{-2\beta p_H}V_H}{2},
\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}
\]

とする。以下の有理係数・補助床・結合上端は、この同じ対象に対する追加評価である。既存の作用、源、Haar、余裕、領域、AIRの比較閾値、AISの床と定理は保持する。

## 2．源の両符号を保つ有理二次補正

まず \(\beta\ge0\)、\(c\ge0\)、\(|x|\le c\) のもとで

\[
a(\beta,c)=\frac{\beta}{1+\beta c},
\qquad 0\le a(\beta,c)\le\beta
\]

を扱う。分母は厳密に正であり、\(\beta>0\) なら係数も正である。新しいスカラー評価は

\[
\boxed{
x\bigl(e^{-\beta x}-1\bigr)
\le-\frac{\beta}{1+\beta c}x^2
}
\]

であり、同値な積分向けの形は

\[
x e^{-\beta x}\le x-\frac{\beta}{1+\beta c}x^2.
\]

証明は \(x\) の両符号を分けて保持する。

- \(x\ge0\) の場合、指数関数の接線評価から \((1+\beta x)e^{-\beta x}\le1\) を得る。さらに \(x\le c\) と \(1-e^{-\beta x}\ge0\) により、\(\beta x\le(1+\beta c)(1-e^{-\beta x})\)。これに非負の \(x\) を掛け、正の分母で割る。
- \(x\le0\) の場合、\(e^{-\beta x}\ge1-\beta x\) に非正の \(x\) を掛けるため不等号が反転し、\(x(e^{-\beta x}-1)\le-\beta x^2\)。\(a(\beta,c)\le\beta\) を使えば同じ有理二次補正が得られる。

\(\beta>0\)、\(c>0\) では厳密な接線不等式 \(e^{\beta c}>1+\beta c\) により

\[
\boxed{\beta e^{-\beta c}<\frac{\beta}{1+\beta c}}
\]

となる。したがって、元の源の範囲 \(c=p_H/2\) に適用する係数

\[
a_H(\beta)=\frac{\beta}{1+\beta p_H/2}
\]

は、AINとAISで使った \(\beta e^{-\beta p_H/2}\) より全正結合で厳密に大きい。符号付き源の両部分が、同じ点ごとの不等式と同じ積分に残る。

## 3．真正crossing積分と両端halfweightへの接続

[AINの元のhalfweight分解とcrossing畳み込み](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/948431e2aab5b957ae5a737d763b3b1326afc86e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN.lean)を用いる。まず \(\beta\ge0\) とする。\(W_H(A)=p_H+2f_H(A)\) から

\[
e^{-\beta W_H(A)/2}=e^{-\beta p_H/2}e^{-\beta f_H(A)}.
\]

元の非負crossing kernelをスカラー不等式に掛け、同じ真正Haarで積分する。源、kernel、源二乗、指数を含む全項の可積分性は、既存の連続性とコンパクト性から明示する。元の畳み込み恒等式

\[
\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)\,d\mu_H(A)
=Z_H^{\mathrm{cross}}(\beta)r(\beta)^4f_H(B)
\]

を保持して

\[
\begin{aligned}
e^{\beta W_H(B)/2}T_{H,\beta}f_{0,H}(B)
\le e^{-\beta p_H/2}\Bigl[
&Z_H^{\mathrm{cross}}(\beta)r(\beta)^4f_H(B)\\
&-a_H(\beta)\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)^2\,d\mu_H(A)
\Bigr]
\end{aligned}
\]

を得る。\(r\) は既存の元のtemporal Wilson coefficientである。

\(\beta>0\)、\(f_H(B)\le0\) なら線形項は非正となる。[AISの真正Ward下界](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/948431e2aab5b957ae5a737d763b3b1326afc86e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS.lean)

\[
\int K^{\mathrm{cross}}_{H,\beta}(A,B)f_H(A)^2\,d\mu_H(A)
\ge e^{-\beta p_H}V_H
\]

を用いると、右重み付きtransferは \(-a_H(\beta)e^{-3\beta p_H/2}V_H\) 以下になる。さらにAIOの \(f_H(B)\le0\Rightarrow W_H(B)\le p_H\) により元の右halfweightを戻す。負の量を掛ける際の順序を保持した結果は

\[
\boxed{
T_{H,\beta}f_{0,H}(B)\le-\widehat D_H(\beta),
\qquad
\widehat D_H(\beta)
=\frac{\beta}{1+\beta p_H/2}e^{-2\beta p_H}V_H>0
}
\qquad(\beta>0,\ f_H(B)\le0).
\]

指数 \(2\beta p_H\) は、左halfweightの \(\beta p_H/2\)、Ward crossing評価の \(\beta p_H\)、右halfweightの \(\beta p_H/2\) の和である。

AISの床 \(D_H^{\mathrm{AIS}}(\beta)=\beta e^{-5\beta p_H/2}V_H\) との厳密比較も、同じ \(H\)、同じ正結合で

\[
\boxed{D_H^{\mathrm{AIS}}(\beta)<\widehat D_H(\beta)}
\]

となる。改善されるのは元transferに対する補助床であり、AIGの元の \(\varepsilon\) は同じ定義を保つ。

## 4．元の全余裕との正確な比と、真正分配関数の単調性

\(\beta\ge0\) では \(1+\beta p_H/2>0\) なので有理係数が正確に消去され、

\[
\boxed{
2\varepsilon_{H,\beta}
=\left[\left(1+\frac{\beta p_H}{2}\right)Z_H^{\mathrm{cross}}(\beta)\right]
\widehat D_H(\beta)
}
\]

が成立する。

[AIFの元の単リンクHaar分配関数と有限積](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/948431e2aab5b957ae5a737d763b3b1326afc86e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean)は

\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),\qquad
Z_H^{\mathrm{cross}}(\beta)=z(\beta)^{n_H},\qquad (n_H:\mathbb R)=p_H.
\]

ここで \(n_H\) は元の空間リンク型の自然数値の要素数である。実数値の \(p_H\) との一致は、AIPの既存定理 `p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H` による自然数から実数へのcastを含む等式である。

元のWilson link energyが \(E(g)\ge0\) であるため、全実結合について \(\beta\le\gamma\Rightarrow z(\gamma)\le z(\beta)\)。正の単リンク積分の有限冪を通して、元の \(Z_H^{\mathrm{cross}}\) も単調非増加になる。重なり合う空間plaquetteの独立性を新たに仮定していない。

特に \(\beta\ge1\) では、[AIQの真正Gaussian評価](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/948431e2aab5b957ae5a737d763b3b1326afc86e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHoeffdingHalfHaarComparisonCeilingV5_PZ37AIQ.lean)を結合1で用いて

\[
\boxed{Z_H^{\mathrm{cross}}(\beta)\le Z_H^{\mathrm{cross}}(1)\le e^{-p_H/2}}
\]

となる。

## 5．体積とともに増大する閉上端と、全有限体積共通の区間

新しい十分条件の上端を

\[
\boxed{b_H=1+\frac{p_H}{4}=1+6(H+1)^3\ge7}
\]

と定義する。最小体積では \(b_0=7\) である。この量は補助比較の明示的な十分上端であり、最適値・一意閾値・物理的臨界結合の認証ではない。

\(0\le\beta\le1\) の部分では、AISの既存評価と接線不等式から

\[
\left(1+\frac{\beta p_H}{2}\right)Z_H^{\mathrm{cross}}(\beta)
\le e^{\beta p_H/2}Z_H^{\mathrm{cross}}(\beta)\le1.
\]

\(1\le\beta\le b_H\) の部分では、固定mathlibの `Real.quadratic_le_exp_of_nonneg` を \(p_H/2\ge0\) に適用する。

\[
e^{p_H/2}\ge1+\frac{p_H}{2}+\frac{p_H^2}{8}
\ge1+\frac{\beta p_H}{2}.
\]

これと \(Z_H^{\mathrm{cross}}(\beta)\le e^{-p_H/2}\) を合わせる。両区間を接続すると

\[
\boxed{
0\le\beta\le b_H\Longrightarrow
\left(1+\frac{\beta p_H}{2}\right)Z_H^{\mathrm{cross}}(\beta)\le1
}
\]

を得る。\(\beta>0\) では \(\widehat D_H(\beta)>0\) であるため、上端を含めて

\[
2\varepsilon_{H,\beta}\le\widehat D_H(\beta),
\qquad
\varepsilon_{H,\beta}<\widehat D_H(\beta).
\]

したがって

\[
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta}.
\]

元の源反転対称性によるAINの半Haar下界を使い、

\[
\boxed{
\forall H\in\mathbb N,\quad
0<\beta\le1+6(H+1)^3
\Longrightarrow
\mu_H(\mathcal N_{H,\beta})\ge\frac12,
\quad
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\frac12
}
\]

となる。源のゼロ集合も包含され、その零測度性を仮定しない。\(\beta=b_H\) 自体の実数値半Haar証明書と、全有限体積に共通する

\[
\boxed{
\forall H\in\mathbb N,\quad
0<\beta\le7\Longrightarrow
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\frac12
}
\]

も含む。半Haar結論は正結合を仮定しており、\(\beta=0\) まで含む主張ではない。

## 6．任意の固定正結合に対するeventual-H結果

同じ明示式から \(H\le b_H\) が成立する。任意の固定実数 \(\beta\) に対して `exists_nat_ge` で \(\beta\le N\) を満たす自然数を選べば、\(H\ge N\) で \(\beta\le H\le b_H\) となる。

従って主結果の量化順序は

\[
\boxed{
\forall\beta>0\;\exists N\in\mathbb N\;\forall H\ge N,
\qquad
\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\frac12
}
\]

である。結合 \(\beta\) を先に固定し、\(N\) はその \(\beta\) に依存してよい。これを「各固定 \(H\) で全正結合が成立する」や「単一の \(N\) が全正結合を同時に覆う」という量化へ移し替えない。

ここでの各測度・配置空間・余裕・領域は、それぞれの有限 \(H\) に属する。共通の無限体積配置空間上の領域や、その上の極限測度を構成したという結論は含まない。

## 7．改善された特定の補助床の減衰と、一様な正の下界の不可能性

\(\widehat D_H\) の体積依存性は、元の計数を代入した正確な式

\[
\boxed{
\widehat D_H(\beta)
=\frac{\beta}{1+12\beta(H+1)^3}
e^{-48\beta(H+1)^3}V_H
}
\]

として残る。\(\beta\ge0\) では有理係数 \(a_H(\beta)\le\beta\) とAISの元の二次モーメント上界 \(V_H\le p_H^2/4\) を使い、

\[
\boxed{
\widehat D_H(\beta)
\le\frac{\beta}{4}p_H^2e^{-2\beta p_H}
}
\]

と評価する。

元の \(p_H\) は \(H\to\infty\) で無限大へ向かう。固定 \(a>0\) に対し、固定mathlibの \(x^2e^{-x}\to0\) を \(x=a p_H\) に合成して

\[
p_H^2 e^{-a p_H}\longrightarrow0
\]

を得る。従って、各固定 \(\beta>0\) について正値性と上界による挟み撃ちから

\[
\boxed{\widehat D_H(\beta)>0\quad(\forall H),
\qquad\widehat D_H(\beta)\longrightarrow0\quad(H\to\infty)}
\]

となる。この特定の証明書については

\[
\boxed{
\neg\exists\eta>0\;\forall H\in\mathbb N,
\qquad\eta\le\widehat D_H(\beta)
}
\qquad(\beta>0\text{ を固定})
\]

も導く。正の一様下界 \(\eta\) があると仮定すれば、0への収束によって得られる \(\widehat D_H(\beta)<\eta\) と矛盾する。

元の固定 \(\beta_0=\log(3/2)/64\) に対しても、各有限体積での正値性、0への収束、全体積共通の正の下界の不可能性を一つの証明書にまとめる。減衰の定理では \(\beta\) を固定しており、任意の \(H\) 依存結合列に同じ結論を無条件で適用していない。

## 8．同時に成立する結果と残る物理的障害

最後の統合証明書は、各固定正結合について次の三つを同時に保持する。

\[
\boxed{
\begin{gathered}
\exists N\;\forall H\ge N,
\quad \mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\frac12,\\
\widehat D_H(\beta)\longrightarrow0,\\
\neg\exists\eta>0\;\forall H,\quad\eta\le\widehat D_H(\beta).
\end{gathered}
}
\]

減衰の対象は、今回構成した数値的な補助床 \(\widehat D_H\) である。transfer評価の向きは、源非正集合上で \(\widehat D_H(\beta)\le -T_{H,\beta}f_{0,H}(B)\) である。したがって床の0への収束は、実際の負値振幅の上界や、その振幅が0へ収束するという結論を与えない。別の評価・証明書による体積一様の正の余裕を不可能としたものでもない。

未解決の範囲は、各固定有限 \(H\) における任意正結合での旧全余裕半Haar性、別の構成による体積一様の正の余裕・coercivity、共通の無限体積・連続体作用素への接続、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapである。元の関数の負領域についての評価を、作用素のスペクトルに関する結論へ昇格させない。

## 9．新規Lean宣言

全49宣言（46定理・3定義）それぞれに完全修飾名の `#print axioms` を置く。先頭6件は `MGAP4D.MathlibAnalytic`、残り43件は同namespace内の `GroundStatePosteriorJoint` に属する。表では共通接頭辞 `p4Q2PZ37AIT_` を省略する。

| # | 宣言 | 内容 |
| --- | --- | --- |
| 1 | `real_rationalCoefficient_nonneg` | 実スカラー有理係数の非負性 |
| 2 | `real_rationalCoefficient_pos` | 実スカラー有理係数の正性 |
| 3 | `real_rationalCoefficient_le_beta` | 有理係数の beta 上界 |
| 4 | `real_previousCoefficient_lt_rational` | 正結合・正の振幅上界で旧指数係数より厳密に大きい |
| 5 | `real_centeredLaplace_rationalQuadraticUpper` | 符号の両側を保った中心化Laplace有理二次上界 |
| 6 | `real_signedLaplace_rationalUpper` | 元の符号付きLaplace上界 |
| 7 | `rationalSourceCoefficient` | 元の p_H による有理係数の定義 |
| 8 | `rationalSourceCoefficient_nonneg` | 物理有理係数の非負性 |
| 9 | `rationalSourceCoefficient_pos` | 物理有理係数の正性 |
| 10 | `rationalSourceCoefficient_le_beta` | 物理有理係数の beta 上界 |
| 11 | `previousCoefficient_lt_rationalSourceCoefficient` | 旧物理二次係数からの厳密改善 |
| 12 | `originalRightWeightedTransfer_rationalQuadraticUpper` | 元の右重み付きtransferに対する有理二次上界 |
| 13 | `sourceNonpositiveRationalWardFloor` | 新しい補助床の定義 |
| 14 | `sourceNonpositiveRationalWardFloor_pos` | 正結合で新補助床が正 |
| 15 | `previousWardFloor_lt_rationalWardFloor` | 正結合でAIS床より厳密に大きい |
| 16 | `originalRightWeightedTransfer_le_negativeRationalWardVariance` | 真正Ward二次モーメントを用いた右重み付きtransfer上界 |
| 17 | `originalTransfer_le_negativeRationalWardFloor` | 両端halfweightを保った元transferの負値評価 |
| 18 | `originalNegativeMargin_rationalWardRatio_identity` | 非負結合での元余裕との正確な比恒等式 |
| 19 | `originalSingleLinkPartition_antitone` | 元の一リンク真正Haar分配関数の反単調性 |
| 20 | `originalCrossingPartition_antitone` | 元の交差分配関数の反単調性 |
| 21 | `originalCrossingPartition_le_unitGaussian` | beta >= 1でunit Gaussian上界 |
| 22 | `volumeGrowingCouplingCutoff` | 体積とともに増大する十分結合上端の定義 |
| 23 | `volumeGrowingCutoff_eq_cubic` | 上端の正確な立方体積表示 |
| 24 | `volumeGrowingCutoff_ge_seven` | 全有限体積で上端 >= 7 |
| 25 | `volumeGrowingCouplingCutoff_pos` | 上端の正性 |
| 26 | `volumeGrowingCutoff_zero` | H = 0で上端 = 7 |
| 27 | `volumeGrowingCutoff_ge_cast` | 上端 >= H |
| 28 | `eventually_le_volumeGrowingCutoff` | 固定した実数betaが十分大きい体積で上端以下 |
| 29 | `rationalBudget_le_expHalf_of_le_cutoff` | 上端以下での有理予算の指数上界 |
| 30 | `originalRationalMarginFactor_le_one_of_le_one` | 0 <= beta <= 1で新比較因子 <= 1 |
| 31 | `originalRationalMarginFactor_le_one_of_one_le` | 1 <= beta <= 上端で新比較因子 <= 1 |
| 32 | `originalRationalMarginFactor_le_one` | 全閉区間で新比較因子 <= 1 |
| 33 | `originalRationalMarginFactor_le_one_of_le_seven` | 全体積共通の0 <= beta <= 7で新比較因子 <= 1 |
| 34 | `twice_originalNegativeMargin_le_rationalWardFloor` | 上端を含む正結合範囲で元余裕の2倍が新補助床以下 |
| 35 | `originalNegativeMargin_lt_rationalWardFloor` | 上端を含む正結合範囲で元余裕が新補助床より厳密に小さい |
| 36 | `originalSource_nonpos_subset_fullNegativeRegion` | 元の源非正集合の元の全余裕厳密負領域への包含 |
| 37 | `originalFullNegativeRegion_Haar_half` | 拡張非負実数値の半Haar下界 |
| 38 | `originalFullNegativeRegion_realHaar_half` | 実数値の半Haar下界 |
| 39 | `originalFullNegativeRegion_realHaar_half_of_le_seven` | 全有限体積共通の0 < beta <= 7で実数値半Haar下界 |
| 40 | `originalFullNegativeRegion_realHaar_half_at_cutoff` | 体積依存上端そのもので半Haar下界 |
| 41 | `originalFullNegativeRegion_realHaar_half_eventually` | 固定beta > 0で十分大きいHにおける半Haar下界 |
| 42 | `rationalWardFloor_exactVolume` | 新補助床の正確な体積表示 |
| 43 | `originalCount_tendsto_atTop` | 元のplaquette数が体積とともに無限大へ発散 |
| 44 | `originalCountSquareExp_tendsto_zero` | 固定正係数で計数二乗と指数減衰の積が0へ収束 |
| 45 | `rationalWardFloor_le_explicitVolumeBound` | 新補助床の明示体積上界 |
| 46 | `rationalWardFloor_tendsto_zero` | 固定beta > 0で新補助床が0へ収束 |
| 47 | `rationalWardFloor_no_uniformPositiveFloor` | この補助床に全体積一様の正の下床がない |
| 48 | `fixedRationalWardFloor_vanishing_certificate` | 元の固定結合で新補助床の正性・消失・一様下床不存在 |
| 49 | `eventualHalfHaar_vanishingFloor_certificate` | 固定beta > 0でeventual半Haarと新補助床消失・一様下床不存在の統合証明書 |


## 10．依存構造・固定環境・Exact-source認証と定理統合

直接importsは次の6件である。

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
```

AISの真正Ward二次モーメント、元の二次モーメント上界、unit比較を、AIFの元のpartition・右重み付きtransfer恒等式、AINの元の左halfweight・源convolution・半Haar対称性、AIOの源非正集合での作用上界へ接続した。AHNの計数・分散正値性、AGNの元源の絶対値上界、AIBの正確な体積表示、ADCの既存固定結合を用いる。旧余裕・strict regionはAIGの同じ定義である。新しい物理仮定や未証明公理を追加していない。

固定mathlibの指数接線・二次下界・指数減衰極限、およびfilterの合成・正定数倍・挟み撃ち・近傍APIを原定義と照合した。全依存閉包の全ソースを人手で再読したという主張ではなく、使用署名の確認と、以下の固定環境での依存を含む型検査を区別する。

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `948431e2aab5b957ae5a737d763b3b1326afc86e` |
| [定理PR #6554](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6554) | MERGED |
| 認証対象source HEAD | `781a9c82c24083492d759ae466c1c1bb50fc1a16` |
| CI実checkout／test-merge HEAD | `d34ae8897da7e6869eac4aa248e5c66e56d88cb8` |
| 実際の定理squash | `57cbe6241f41adbface0d8e379f9e98d81bf723a` |
| source／test-merge／定理squash共通Git tree | `95c1647ee996fff0ba88ba9281f4a3207afd02b1` |
| 新規Lean Git blob | `10d079143870929f2df37a18a2703a94a78c300e` |
| 新規Lean SHA256 | `b81b83f65d7e9cad4e947a9425de305fca22acf15ef705a6e3eefddb0c38f933` |
| 新規Lean | 853行・46定理・3定義・49公理出力命令・44,279 bytes |
| [CI #42554354126 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42554354126/attempts/1) | completed／SUCCESS |
| 主job | `128956644578`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11408／11408 SUCCESS** |
| 新規leaf build | 28秒 |
| 実際の公理出力 | **49／49**、全49件が `propext, Classical.choice, Quot.sound` のみ |
| 公理出力の欠落／余分／重複 | 0／0／0 |
| AIT全49宣言の非標準公理 | 0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更Lean warning／error | 0／0 |
| 独立completion receipt job | `128958264436`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| exact-source status ID | `58391013903` |
| check suite | `115264152505`、completed／SUCCESS、check runs 2件ともSUCCESS |
| 完了主ジョブログ | 3,394,302文字 |
| 診断artifact | `13647101580`、実ZIP 131,309 bytes |
| 実ZIP SHA256 | `5db452fef914f9347440f4634185314aa2082a71b86f0f88e4bdb7e932e4b605` |
| 抽出実ログ | 1,963,233 bytes |
| 抽出実ログSHA256 | `4a1577f127f57b01e77a755ada8b6aea423d1f815fcecd2aba13f4d7af62dd19` |

receiptの9,704文字の実ログは `event=pull_request exact_sha=781a9c82c24083492d759ae466c1c1bb50fc1a16 source_result=success run=42554354126 attempt=1` を記録する。exact-source statusのtargetも同じrunを指す。

主担当は完了後の主ジョブログ全文と診断artifactの実bytesを取得した。全49宣言の完全修飾名と実公理出力を一対一で照合し、欠落・余分・重複、標準外公理、sorryAx、全Lean error・Actions error、変更warning/errorがないことを確認した。実ZIPのSHA256はGitHub metadataのdigestと一致した。主ジョブログではGitHubが各行に付ける時刻接頭辞を除いて複数行の公理集合を解析し、時刻のないartifact実ログとも照合した。変更warning 0は、既存依存ファイルの再生warningまで全件0という主張ではない。

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。認証sourceにおける `lean-toolchain`（blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`）と `lake-manifest.json`（blob `01260678b674ab241e753563e913c7ce9c6ba659`）、実ログのLean/Lake versionを照合した。既存の環境・上限は変更していない。

base差分は新規Lean1件だけ（853行追加・削除0、sourceはbaseから2コミット）。既存Lean・定義・定理・公開root・証明記録・workflow・pinを変更しない。独立担当は、PR patchの全853追加行が認証source全文に一致することも確認した。

定理PR #6554の実squashを統合後に再取得した。その唯一の親は元canonical baseであり、source／test-merge／実squashのtreeは一致した。定理統合直後のcanonical formalが同じsquashに進んだこと、統合されたLean全文とblobが認証sourceと同じことを主担当と独立担当が再観測した。後続の文書専用commitのtreeを、この定理共通treeと同一視しない。

[統合済みAIT Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/57cbe6241f41adbface0d8e379f9e98d81bf723a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT.lean).

独立担当はworkflow・job・必須step・receipt全文・status・suite/check runs・source/test-merge tree・artifact metadataを別途確認した。主ログ全文とartifact実bytes・公理出力の解析は主担当によるものとして区別する。別job receiptや独立の記録照合は、別のLean kernelによる独立再証明ではない。


## 11．初回CIの成功と、zero-warning統合条件による見送り

初回source `96fa415d162b38c9e292e13f4c1c658158a9dcb0` の [CI #42553679112 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42553679112/attempts/1) は、workflow・主job・必須Lean step・独立receiptがすべてSUCCESSで完了した。Leanの失敗とは記録しない。一方、変更Leanのwarningが4件あったため、zero-warning統合条件を満たさず、このsourceはマージしなかった。

| 項目 | 初回の実観測 |
| --- | --- |
| Source HEAD | `96fa415d162b38c9e292e13f4c1c658158a9dcb0` |
| 実checkout／test-merge | `25d4fce195538ee5bce111cbec9645a433a5ac04` |
| source／test-merge共通tree | `9f9e7883ea1e5f99bc4a60a5abac5da5a1ac9bc1` |
| 初回Lean blob | `931a3f44f44e4a079a355d7ff0f0a06b0c925f56` |
| 初回Lean SHA256 | `8a21e9b7cf123de589f7b9ffc730a761a74e94e2ae3a2a5ea0e0e55b34e27956` |
| 新規Lean | 853行・44,297 bytes・46定理＋3定義 |
| 主job／必須step 17 | `128954568611`、ともにcompleted／SUCCESS |
| Lake依存閉包／leaf | 11408／11408 SUCCESS／30秒 |
| 実公理出力 | 49／49、全件が標準3公理のみ |
| AIT全49宣言の欠落／余分／重複／非標準公理 | 0／0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更warning／error | **4／0** |
| 独立receipt job／step 2 | `128956103391`、ともにcompleted／SUCCESS |
| exact-source status／suite | `58390733383`／`115262411256`、ともにSUCCESS |
| 完了主ジョブログ | 3,396,640文字 |
| 診断artifact | `13646307500`、実ZIP 131,639 bytes |
| 実ZIP SHA256 | `9f62b4ac64f727ec00cda275b89c9644890eb9d6d8f137c1c34485e2daf080a2` |
| 抽出実ログ | 1,964,159 bytes |
| 抽出実ログSHA256 | `f63bd986b7b05e306914b42cd6e1fc911d1e93a940f318ecb231f5954c185a01` |

receiptの9,701文字の実ログには `event=pull_request exact_sha=96fa415d162b38c9e292e13f4c1c658158a9dcb0 source_result=success run=42553679112 attempt=1` が含まれる。ZIPの実SHA256はGitHub metadataのdigestと一致した。主担当は全公理出力とdiagnosticsを実artifactから確認し、完了後の主ジョブログ全文も照合した。

warningの発生箇所は427:26と716:33であり、各箇所に `'ring' tactic does nothing` と `this tactic is never executed` が1件ずつ出た。いずれも直前の `field_simp` が既にゴールを閉じた後の冗長な継続tacticである。

変更Lean全文、imports、依存署名、固定APIと実診断を再確認し、次の2行だけから末尾の `<;> ring` を削除した。

```lean
field_simp [hDen]
field_simp [ne_of_gt ha]
```

前者は元余裕との恒等式の分母消去、後者は体積極限における正の定数による再尺度化である。主担当と独立担当が、全文を比較してこの2か所の削除以外は一致することを確認した。全49宣言の署名・仮定・定義値、その他の証明、imports、heartbeat、公理出力命令は不変である。修正版は853行・44,279 bytes。修正版sourceに新しい自動Exact-source CIを要求し、初回の成功を修正版の認証へ流用しなかった。


## 12．統合後pushの再検証

実際の定理squashを対象とした自動 [push CI #42555080816 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42555080816/attempts/1) も、workflowと全jobが完了した後に認証した。

| 項目 | 実観測結果 |
| --- | --- |
| push対象／実checkout | `57cbe6241f41adbface0d8e379f9e98d81bf723a` |
| 全workflow | completed／SUCCESS |
| 主job／必須Lean step 17 | `128958868107`、ともにcompleted／SUCCESS |
| Lake依存閉包／新規leaf | **11408／11408 SUCCESS**／36秒 |
| 実公理出力 | 49／49、全件が標準3公理のみ |
| 公理出力の欠落／余分／重複／非標準公理 | 0／0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更warning／error | 0／0 |
| receipt job／step 2 | `128960250270`、ともにcompleted／SUCCESS |
| exact-squash status | `58391265047`、SUCCESS |
| check suite／check runs | `115265957703`、SUCCESS／2件ともSUCCESS |
| 完了主ジョブログ | 3,394,216文字 |
| 診断artifact | `13647480671`、実ZIP 131,631 bytes |
| 実ZIP SHA256 | `021a6577fe5f4119dea8450dc2e019af69910cc21a63ad6478b93241b23e993f` |
| 抽出実ログ | 1,963,251 bytes |
| 抽出実ログSHA256 | `381f02677b651e30941c448037f632ae0afa3b5cb6be50712467abe6b34bb062` |

receiptの9,683文字の実ログは `event=push exact_sha=57cbe6241f41adbface0d8e379f9e98d81bf723a source_result=success run=42555080816 attempt=1` と記録する。主担当は完了主ログ・実artifact bytes・49の実公理出力を再照合した。実ZIPのdigestはGitHub metadataと一致した。独立担当もworkflow・job・step・receipt全文・status・suite/check runs・artifact metadataと、実squashのtree/blob・唯一の親を再確認した。

このpush検証でも、元の固定Lean/mathlib、source全文・49宣言・heartbeatは認証sourceと同じである。統合前の認証sourceを未確認の別treeへ読み替えず、実squashを対象に結果を記録した。


## 13．独立レビュー・文書同期・次段の研究

変更Lean全853行、imports、使用する依存署名・証明構造・固定mathlib APIをレビューした。独立担当は、源の両符号、有理係数の分母正値性、元の左右halfweight、Ward下界、元余裕との恒等式、上端を含む厳密領域包含、結合を先に固定するeventual-H量化、この特定の床だけについての体積極限を点検した。初回の静的レビューでは冗長tacticのwarningを検出しておらず、静的な数学・ソース読解を固定環境のLean認証と同一視しない。

文書では、transferの点ごとの負値床が源非正集合上の評価であることを明記する。全体積に共通する正結合の範囲は半開区間 (0,7] であり、上端7を含むが0は含まない。非負結合での比較因子の評価 0<=beta<=b_H と、正結合での半Haar結論 0<beta<=b_H を区別する。

本文とREADME・ROADMAPは文書専用PRで更新し、既存README・ROADMAPの全文を保持して末尾に追記する。文書専用変更ではStrict Leanを手動起動しない。mainへはformalの正式記録と同一のGit blobをミラーし、定理正本をmainへ移さない。main側の自動workflowは文書ミラー後のbranch状態の検査として扱い、formalのExact-source定理認証を置き換えない。

次段AIUの候補は、各固定有限Hで残る大きい正結合を扱うための、元の真正分配関数の結合依存減衰評価である。または、今回の消失する証明書を超えて、既存の正規化を保持したまま元transferの負値振幅や正規化因子の体積依存性を制御する評価を検討する。これらは研究候補であって、AITで証明した追加結論ではない。体積一様の正の余裕・coercivity、共通の極限作用素への接続、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは、それぞれ必要な証明が得られるまで未認証として保持する。

