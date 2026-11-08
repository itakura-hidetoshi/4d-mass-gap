# P4-Q2-PZ37AIR — 真正Haar分散による閉上端と元の余裕比較の一意閾値

**正式認証記録（2026年11月9日 JST）。** 固定環境のexact-source CI、全公理出力監査、独立completion receiptと完了ログ照合を終え、定理PR #6548をcanonical formalへ統合した。統合後に、実squashのGit tree・Lean本文・Git blobが認証対象と一致することを確認した。

参照基準はcanonical formal `88a2d26def8aaeb782faf1a4a9694cd681d7c59e`。元の完全SU(2) Wilson作用、両端halfweight、符号付きZW物理L²源と既存連続代表、真正正規化Haar、AIGの元の全余裕と厳密負領域、既存の仮定・定義・定理を保持する。append-only／tighten-only／overwrite-forbidden／same-rootの下で、新規leafを追加した。

## 1．元の対象と厳密な余裕比較

有限体積指標を `H : ℕ`、元のplaquette数を \(p_H>0\)、元の空間リンク数を \(n_H\) とする。真正空間積Haarを \(\mu_H\)、元の連続源を \(f_H\)、物理源を \(f_{0,H}\)、完全transferを \(T_{H,\beta}\) と書く。元の真正二次モーメントは
\[
V_H=\int f_H(A)^2\,d\mu_H(A)>0
\]
である。

[AIFの元の分配関数](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean)は、元の単リンク群 \(G=SU(2)\)、真正確率Haar \(\nu\)、元のWilsonエネルギー \(E\) に対して
\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),
\qquad Z_H^{\mathrm{cross}}(\beta)=z(\beta)^{n_H}
\]
である。[AIPの元の計数接続](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP.lean)により \(n_H=p_H\) を用いる。

[AIGの旧全余裕と負領域](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean)は変更しない。
\[
\varepsilon_{H,\beta}
=\frac{\beta Z_H^{\mathrm{cross}}(\beta)e^{-2\beta p_H}V_H}{2},
\qquad
\mathcal N_{H,\beta}
=\{B:T_{H,\beta}f_{0,H}(B)<-\varepsilon_{H,\beta}\}.
\]

[AIOの既存補助床と恒等式](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHalfHaarFullMarginCouplingV5_PZ37AIO.lean)は
\[
\delta_{H,\beta}=\beta e^{-7\beta p_H/2}V_H,
\qquad
2\varepsilon_{H,\beta}
=\left[Z_H^{\mathrm{cross}}(\beta)e^{3\beta p_H/2}\right]\delta_{H,\beta}.
\]
正結合では \(\delta_{H,\beta}>0\)。AIRは同じ括弧内の式に
\[
F_H(\beta):=Z_H^{\mathrm{cross}}(\beta)e^{3\beta p_H/2}
\]
という補助名を付ける。別の物理partition・測度・源・transferを定義するものではない。

## 2．真正SU(2)の分散 \(1/4\) による厳密な改善

元の \(\chi(g)=1-E(g)\) を用いる。[AIQの既存結果](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalHoeffdingHalfHaarComparisonCeilingV5_PZ37AIQ.lean)により
\[
-1\le\chi(g)\le1,\qquad \int_G\chi\,d\nu=0,
\qquad
z(\beta)=e^{-\beta}M(\beta),
\quad
M(\beta)=\int_G e^{\beta\chi(g)}\,d\nu(g).
\]
この \(M\) は実際の元の関数と測度のMGFである。

[ABNの元のcharacter二次モーメント](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/88a2d26def8aaeb782faf1a4a9694cd681d7c59e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTemporalCharacterTransmissionV5_PZ37ABN.lean)は、同じ \(\chi,\nu\) に対して
\[
\boxed{\int_G\chi(g)^2\,d\nu(g)=\frac14}
\]
を与える。この \(1/4\) を新しい仮定として置かない。

固定mathlibの [実指数関数の剰余評価](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Complex/Exponential.lean) `Real.abs_exp_sub_one_sub_id_le` を使う。\(|\beta|\le1\) なら \(|\beta\chi(g)|\le1\) なので、
\[
e^{\beta\chi(g)}
\le1+\beta\chi(g)+\beta^2\chi(g)^2.
\]
形式実装では、一般の確率測度と実関数に対する `boundedCenteredVariance_integral_le` を先に証明する。範囲・平均0・各項の可積分性を明示したこの補助定理は、二次モーメントを積分のまま残す。元の物理定理では、それらの条件を既存AIQの結果から供給し、ABNの真正二次モーメント \(1/4\) を適用する。補助定理の条件を新しい物理仮定として加えていない。

全項の可積分性を証明して元のHaarで積分し、符号付き線形項を平均0で消去すると
\[
\boxed{|\beta|\le1\Longrightarrow M(\beta)\le1+\frac{\beta^2}{4}}
\]
となる。

さらに \(0<\beta\le1\) では \(\beta^2/4>0\) であり、同じ固定mathlibの \(1+x<e^x\) を使って
\[
\boxed{0<\beta\le1\Longrightarrow M(\beta)<e^{\beta^2/4}}
\]
を得る。厳密性はこの正のスカラーから生じる。非厳密な積分評価をそのまま厳密評価へ読み替えてはいない。

元の正の自然数 \(n_H=p_H\) による冪と両端halfweightを保持した正確な式から
\[
F_H(\beta)=e^{\beta p_H/2}M(\beta)^{n_H}
\]
となり、
\[
\boxed{
0<\beta\le1
\Longrightarrow
F_H(\beta)<\exp\!\left(\frac{p_H(2\beta+\beta^2)}4\right)
}
\]
を得る。したがって新しい十分予算は非厳密に
\[
\boxed{
0<\beta\le1,\quad
\frac{p_H(2\beta+\beta^2)}4\le\log2
\Longrightarrow F_H(\beta)<2
}
\]
と書ける。AIQの全実結合のGaussian上界も保持されるが、今回の改善上界には指定したスカラー範囲が必要である。

## 3．新しい明示閉上端とAIQ区間からの厳密拡大

AIPの既存上端を \(\lambda_H=\log2/p_H\)、AIQの既存上端を
\[
q_H=\frac{2\log2}{p_H+2\log2}
\]
とする。いずれも変更しない。

新しい明示上端は
\[
\boxed{r_H=\sqrt{1+4\lambda_H}-1}.
\]
正値性と平方根の恒等式から
\[
r_H>0,\qquad r_H^2+2r_H=4\lambda_H,
\qquad
r_H<2\lambda_H\le\frac1{12}
\]
を得る。したがって \(r_H<1/12<1\) であり、第2節のスカラー条件を満たす。

\(0<\beta\le r_H\) なら
\[
2\beta+\beta^2\le2r_H+r_H^2=4\lambda_H
\]
である。元の計数恒等式 \(p_H\lambda_H=\log2\) により新予算が成立し、
\[
\boxed{
0<\beta\le r_H
\Longrightarrow F_H(\beta)<2
\Longrightarrow
\frac12\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})
}
\]
となる。特に上端 \(\beta=r_H\) の予算は等号だが、MGF評価の厳密性が残るため \(F_H(r_H)<2\) である。旧 \(\varepsilon\) を縮めて上端を含める操作ではない。

AIQで既証明の \(q_H>0\) と \(q_H^2+q_H<2\lambda_H\) から
\[
q_H^2+2q_H<4\lambda_H=r_H^2+2r_H
\]
が従い、正の範囲での二次式の増加性によって
\[
\boxed{q_H<r_H}
\]
となる。これによりAIQの既存の明示閉区間を厳密に拡大する。\(r_H\) は積分を含まない明示式であり、体積一様の正の結合上端という主張ではない。

## 4．元の比較因子の連続性・厳密単調性

MGFの連続性には、AIQで証明済みの全実結合における指数可積分性を用いる。固定mathlibの [MGF連続性定理](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/Moments/MGFAnalytic.lean) を同じ \(\chi,\nu\) に適用し、\(F_H\) の正確な因数分解と接続する。

非負結合での単調性は、実装では次の初等不等式から証明する。
\[
0\le a\le b
\quad\Longrightarrow\quad
e^{ax}+(b-a)x\le e^{bx}
\qquad(x\in\mathbb R).
\]
\(x\) の正負をともに扱い、元の \(\chi\) を代入して可積分な式をHaar積分すると、線形増分の積分が0となるため \(M(a)\le M(b)\) である。

\(M(\beta)\ge1\) はAIQで既証明である。正の因子 \(e^{\beta p_H/2}\) が厳密に増加するので
\[
\boxed{F_H\text{ は連続で、 }[0,\infty)\text{ 上で厳密増加}}
\]
となる。この厳密増加性を全実数上に拡張しない。

さらに、元の恒等元で \(\chi(1)=1\)。正結合に対して
\[
d(g)=e^{\beta\chi(g)}-(\beta\chi(g)+1)
\]
は連続・非負で、\(d(1)>0\) である。真正Haarの開集合正測度性とコンパクト性を、固定mathlibの [連続非負関数の正積分定理](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Set.lean) に接続する。単一の点が正測度を持つとは仮定しない。

\(\int(\beta\chi+1)\,d\nu=1\) なので、
\[
\boxed{
\beta>0\Longrightarrow M(\beta)>1
\Longrightarrow F_H(\beta)>e^{\beta p_H/2}
}
\]
を得る。特に旧比較上限で
\[
\boxed{F_H(2\lambda_H)>2}
\]
となり、AIQの非厳密な下界を厳密にする。

## 5．同じ比較法の一意な閾値

第3–4節から
\[
F_H(r_H)<2<F_H(2\lambda_H).
\]
固定mathlibの [中間値の定理](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/IntermediateValue.lean) と連続性により、実際の元の比較因子が2となる結合が存在する。

証明された存在から `Classical.choose` で新しい補助量 \(\theta_H\) を定義する。指定する仮定を追加して選ぶのではなく、先に構成された存在証明の証人を選ぶものである。
\[
\boxed{
q_H<r_H<\theta_H<2\lambda_H,\qquad F_H(\theta_H)=2
}
\]
となる。

非負結合上の厳密単調性から、その範囲で根は一意であり、
\[
\boxed{
\begin{aligned}
F_H(\beta)<2&\iff\beta<\theta_H,\\
F_H(\beta)=2&\iff\beta=\theta_H,\\
2<F_H(\beta)&\iff\theta_H<\beta
\end{aligned}
\qquad(\beta\ge0)
}
\]
を得る。ここで非負結合条件は明示的に保持する。

\(\theta_H\) は同じ真正分配関数から定まる暗黙の比較閾値であり、Haar積分を初等閉形式で評価した量ではない。\(r_H\) という明示上端と、\(\theta_H\) という正確な比較閾値を区別する。

## 6．旧余裕の三分比較と半Haar結論の範囲

正結合では \(\delta_{H,\beta}>0\) なので、元の恒等式 \(2\varepsilon=F_H\delta\) と第5節から
\[
\boxed{
\begin{aligned}
\varepsilon_{H,\beta}<\delta_{H,\beta}&\iff\beta<\theta_H,\\
\varepsilon_{H,\beta}=\delta_{H,\beta}&\iff\beta=\theta_H,\\
\delta_{H,\beta}<\varepsilon_{H,\beta}&\iff\theta_H<\beta
\end{aligned}
\qquad(\beta>0)
}
\]
を証明する。零結合では両余裕が0となるため、この三分比較には正結合条件が必要である。

AIOの元のtransfer評価と接続し、
\[
\boxed{
0<\beta<\theta_H
\Longrightarrow
\{B:f_H(B)\le0\}\subseteq\mathcal N_{H,\beta}
}
\]
を得る。AINの真正Haarでの源非正集合の半質量と合わせ、
\[
\boxed{
0<\beta<\theta_H
\Longrightarrow
\frac12\le\mu_H(\mathcal N_{H,\beta}),
\qquad
\frac12\le\mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})
}
\]
となる。前者は \(\mathbb R_{\ge0}\cup\{\infty\}\) 値の測度、後者は実数値測度である。源のゼロ集合も含み、その測度について新しい仮定は置かない。

閾値そのものでは
\[
F_H(\theta_H)=2,\qquad
\varepsilon_{H,\theta_H}=\delta_{H,\theta_H},
\qquad
\neg\bigl(F_H(\theta_H)<2\bigr).
\]
現在の補助床から得られる \(T\le-\delta\) は、この点では \(T\le-\varepsilon\) までである。厳密な旧領域への包含をこの非厳密評価から推論しない。

\(\theta_H\) は**この十分条件と補助床を用いた余裕比較の一意閾値**であり、物理的な臨界結合や、実際の半Haar性が成立する最大結合ではない。閾値以上での物理的負性・半Haar性の失敗は主張しない。任意正結合の旧全余裕半Haar下界、任意正結合の全境界負性、正のtransfer境界と正負両符号領域、体積一様の正の負値余裕・coercivity、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは、本leafの結論ではない。元の完全作用・両端halfweight・符号付き源・真正Haar・既存定理は保持される。

## 7．40宣言の対応表

名前空間は `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`、共通prefixは `p4Q2PZ37AIR_`。37定理・3定義があり、下表はprefixを省略する。全40件の型検査と実公理出力を、第8節のexact-source CIで確認した。

| # | 宣言末尾 | 内容・必要条件 |
| --- | --- | --- |
| 1 | `originalCharacterMGF_continuous` | 元のcharacter・HaarのMGFの連続性 |
| 2 | `real_exp_increment_lower` | \(0\le a\le b\)、任意の実 \(x\) に対する指数増分の下界 |
| 3 | `originalCharacterMGF_monotoneOn` | 元のMGFの非負結合上の単調性 |
| 4 | `originalCharacter_one` | 元の \(\chi(1)=1\) |
| 5 | `originalCharacterMGF_gt_one` | 正結合で \(1<M(\beta)\) |
| 6 | `boundedCenteredVariance_integral_le` | 一般の確率空間・平均0・絶対値1以下の関数に対する積分剰余上界。各項の可積分性と \(\lvert\beta\rvert\le1\) を明示 |
| 7 | `originalCharacterMGF_le_varianceQuadratic` | \(\lvert\beta\rvert\le1\) で \(M\le1+\beta^2/4\) |
| 8 | `originalCharacterMGF_lt_varianceGaussian` | \(0<\beta\le1\) で \(M<e^{\beta^2/4}\) |
| 9 | `originalMarginComparisonFactor` | AIOの元の比較因子 \(F_H\) に名前を付ける定義 |
| 10 | `originalMarginFactor_characterMGF` | 全実結合で \(F_H=e^{\beta p_H/2}M^{n_H}\) |
| 11 | `originalMarginFactor_continuous` | 元の \(F_H\) の連続性 |
| 12 | `originalMarginFactor_strictMonoOn` | 非負結合上で元の \(F_H\) が厳密増加 |
| 13 | `originalMarginFactor_gt_expHalf` | 正結合で \(e^{\beta p_H/2}<F_H\) |
| 14 | `originalMarginFactor_lt_varianceGaussian` | \(0<\beta\le1\) で分散による厳密上界 |
| 15 | `originalPartitionCondition_of_varianceBudget` | 正結合・\(\beta\le1\)・非厳密な新二次予算から \(F_H<2\) |
| 16 | `varianceRootCouplingCutoff` | 新しい明示上端 \(r_H=\sqrt{1+4\lambda_H}-1\) の定義 |
| 17 | `varianceRootCouplingCutoff_pos` | \(r_H>0\) |
| 18 | `varianceRoot_quadratic_identity` | \(r_H^2+2r_H=4\lambda_H\) |
| 19 | `varianceRoot_lt_twice_previous` | \(r_H<2\lambda_H\) |
| 20 | `varianceRoot_lt_oneDivTwelve` | \(r_H<1/12\) |
| 21 | `previousRational_lt_varianceRoot` | AIQの元の \(q_H<r_H\) |
| 22 | `varianceBudget_of_le_root` | \(0<\beta\le r_H\) で新二次予算 |
| 23 | `originalPartitionCondition_of_le_root` | 同閉区間で \(F_H<2\) |
| 24 | `originalFullNegativeRegion_realHaar_half_of_le_root` | 同閉区間で旧全余裕領域の実数値半Haar下界 |
| 25 | `originalMarginFactor_at_ceiling_gt_two` | 旧上限で \(2<F_H(2\lambda_H)\) |
| 26 | `exists_criticalComparisonCoupling` | \((r_H,2\lambda_H)\) 内の元の方程式 \(F_H=2\) の根の存在 |
| 27 | `criticalComparisonCoupling` | 証明済み存在から選ぶ補助閾値 \(\theta_H\) の定義 |
| 28 | `criticalComparisonCoupling_spec` | \(r_H<\theta_H<2\lambda_H\)、\(F_H(\theta_H)=2\) |
| 29 | `criticalComparisonCoupling_pos` | \(\theta_H>0\) |
| 30 | `originalMarginFactor_eq_two_iff` | \(\beta\ge0\) で \(F_H=2\iff\beta=\theta_H\) |
| 31 | `originalPartitionCondition_iff_below_critical` | \(\beta\ge0\) で \(F_H<2\iff\beta<\theta_H\) |
| 32 | `originalMarginFactor_gt_two_iff` | \(\beta\ge0\) で \(2<F_H\iff\theta_H<\beta\) |
| 33 | `originalNegativeMargin_lt_floor_iff` | \(\beta>0\) で旧 \(\varepsilon<\delta\iff\beta<\theta_H\) |
| 34 | `originalNegativeMargin_eq_floor_iff` | \(\beta>0\) で旧 \(\varepsilon=\delta\iff\beta=\theta_H\) |
| 35 | `originalFloor_lt_negativeMargin_iff` | \(\beta>0\) で旧 \(\delta<\varepsilon\iff\theta_H<\beta\) |
| 36 | `originalSource_nonpos_subset_fullNegativeRegion` | \(0<\beta<\theta_H\) で源非正集合を旧全余裕領域に包含 |
| 37 | `originalFullNegativeRegion_Haar_half` | 同区間で拡張非負実数値半Haar下界 |
| 38 | `originalFullNegativeRegion_realHaar_half` | 同区間で実数値半Haar下界 |
| 39 | `expandedClosedEndpoint_certificate` | \(q_H<r_H<\theta_H<2\lambda_H\)、新閉上端の厳密条件と半Haar |
| 40 | `comparisonBoundary_certificate` | 元の \(F_H(\theta_H)=2\)、\(\varepsilon=\delta\)、厳密比較の不成立 |


## 8．Exact-source認証と統合の実観測

| 項目 | 実観測結果 |
| --- | --- |
| Canonical base | `88a2d26def8aaeb782faf1a4a9694cd681d7c59e` |
| [定理PR #6548](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6548) | MERGED |
| 認証対象source HEAD | `009b71059f19c596c6f0eeb38c6c7bc8377febbc` |
| CIの実checkout／test-merge HEAD | `77c737b8592f0a11e624f7f13ffd605e8427226d` |
| 実際の定理squash | `df0bdf6f5c70951009e0d55cd7eb10953f28cd8a` |
| source／test-merge／実squash共通Git tree | `01711f0a4a04cfeed0fc5273eeb6120f78cab3ea` |
| 新規Lean Git blob | `c0ddee5d3c0f42e17b5d3d070523199e08831f4b` |
| 新規Lean SHA256 | `653b98daaa2cfb6ca1ee300f230a575abd62e0900e9e195119c9f4e021b4728f` |
| 新規Lean | 690行・37定理・3定義・40公理出力命令・36840 bytes |
| [CI #42536744908 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42536744908/attempts/1) | completed／SUCCESS |
| 主job | `128902602642`、completed／SUCCESS |
| 必須Lean step 17 | completed／SUCCESS |
| Lake依存閉包 | **11406／11406 SUCCESS** |
| 新規leaf build | 47秒 |
| 実際の公理出力 | **40／40**、全40件が `propext, Classical.choice, Quot.sound` のみ |
| 公理出力の欠落／余分／重複 | 0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 |
| 変更Lean全文warning／error | 0／0 |
| 独立completion receipt job | `128903810005`、completed／SUCCESS |
| receipt step 2 | completed／SUCCESS |
| exact-source commit status | `chatgpt-ci-receipt/PR Lean Fast Check`、SUCCESS |
| exact-source status ID | `58383994205` |
| check suite | `115219560257`、completed／SUCCESS、check runs 2件ともSUCCESS |
| 診断artifact | `13640095722`、130232 bytes |
| 実ZIP SHA256 | `69a93e956a35f549d5481acb786510b236c1ce56ebeff620d7ab8f88638bc096` |
| 抽出実ログ | 1941462 bytes |
| 抽出実ログSHA256 | `42ba72354dd9a681e7a3af8fa99940624a5317dd4cbdeed3f5f585382f026e82` |

receiptの実出力は `[mcp-receipt] event=pull_request exact_sha=009b71059f19c596c6f0eeb38c6c7bc8377febbc source_result=success run=42536744908 attempt=1`。exact-source statusのtargetも同じrunを指す。

主担当は完了後の主ジョブログ全文3364415文字と、診断artifactの実bytesを取得した。全40宣言の完全修飾名と実公理出力を一対一で照合し、欠落・余分・重複、標準外公理、sorryAx、全Lean error・Actions error、変更ファイルのwarning/errorがないことを確認した。ZIPの実SHA256はGitHub metadataのdigestと一致した。変更ファイルのwarning 0は、既存依存ファイルの再生warningまで全件0という主張ではない。

固定環境はLean `v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`、`maxHeartbeats 3900000`、`synthInstance.maxHeartbeats 1050000`。認証sourceの `lean-toolchain` と `lake-manifest.json`、実ログのLean versionとcheckoutを照合した。直接importはAIQ、`Mathlib.Data.Real.Sqrt`、`Mathlib.Topology.Order.IntermediateValue`、Mathlib.Tacticであり、すべて既存の同一固定環境に属する。

base差分は新規Lean1件だけ（690行追加・削除0、ahead3／behind0）。既存Lean・証明記録・workflow・pin・heartbeatは変更していない。

### 初回sourceの失敗と、公開署名を保持した証明構造の修正

初回source `431143e929d0bb3f86288da72c06840ca95fb121`（629行、Git blob `88ac663cb8a55678af696518411142b15112a3c9`、SHA256 `d9fec8e3addf4b8995c99494289c7a940a01e38196f188bb8dc833f46274edbf`）の [CI #42533953543 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42533953543/attempts/1) は、workflow・主job `128894011478`・必須step 17ともFAILUREで完了した。実checkoutは `06fa9d5d118ba2a381c651836a7bb11f3131812c`。新規leafは `[11406/11406] Building ... (420s)` で失敗しており、依存閉包全体SUCCESSとは扱わない。

変更ファイルのerrorは4件、warningは0件だった。

| 箇所 | 実診断と構造 |
| --- | --- |
| 119:6 | `integral_mono` から推論された積分内の関数和 `Pi.add` に、点ごとの和を対象とする `integral_add` のrewriteが一致しなかった。 |
| 167:0 | `originalCharacterMGF_le_varianceQuadratic` の宣言で、`whnf` のdeterministic timeoutが固定上限3,900,000 heartbeatsに到達した。ログは消費量を支配した局所ステップまでは示していない。 |
| 215:8 | 上の宣言が成立しなかったため、後続でkernelのunknown constantが生じた。 |
| 270:66 | 固定版には `Continuous.exp` フィールドが存在しなかった。実指数関数の拡張名は `Continuous.rexp` である。 |

失敗後に変更Lean全文・imports・依存署名・固定mathlibを再読し、修正を3つの証明本体に限定した。

1. 固定 [Bochner積分API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) の、関数和を直接対象とする `integral_add'` を使い、`integral_const_mul` のスカラーと関数も明示した。
2. 分散評価では、実数変数だけのスカラー不等式を先に証明し、その後に元の `chi g` を代入する構造へ分離した。元のHaarに対する0次・1次・2次モーメントを別々の型付き等式として証明し、引数を指定した積分補題と `congrArg` で接続した。具体的なSU(2)積分全体に対する汎用的な書換えを避けた。元timeoutの正確な内部hotspotは未特定であり、特定の `simp` 呼出しが原因だったとは断定しない。
3. 固定 [実指数関数の連続性API](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Exp.lean) の `Real.continuous_exp.comp` を、型を明示した実数値の内側写像に適用した。

全39の公開署名、定義の値、仮定、数学的定数、imports、heartbeat、全39公理出力命令は、初回版と修正版で一致することを機械的な比較と独立全文レビューで確認した。診断の削除・抑制、heartbeat増加、下流定理の条件の変更は行っていない。初回の静的レビューは、実際のrewrite形・固定拡張名・評価コストの問題を検出できていなかったため、認証にはCI完了と実出力を必須とした。

初回の公理出力名は39件が各1回現れたが、38件は `depends on axioms` 形式、1件は `does not depend on any axioms` 形式だった。後者の対象はtimeoutした分散定理であり、失敗したbuildの見かけ上の「公理なし」を証明の認証に用いない。18件に `sorryAx`、20件にエラー回復による自己名の非標準公理 `p4Q2PZ37AIR_originalCharacterMGF_lt_varianceGaussian` が含まれた。15件の出力が標準3公理のみだったことも、失敗sourceの部分認証とは扱わない。明示的な `sorry` や `axiom` をソースに追加したものではない。

監査parserはこの2種類の公理出力形式をともに認識し、完全修飾名の39件一致と、標準外公理・sorryAx・診断・build完了の全条件を別々に検査する。

主担当と独立CI担当は、主job完了後の全文3,385,384文字を別々に取得して照合した。途中のAPIが返した2,107,663文字の部分ログにはAIRの出力がなく、その部分だけでは認証していない。

初回receipt job `128897118234` はSUCCESSで完了したが、9,702文字の実ログは `source_result=failure` と旧sourceを正しく記録した。発行status `58383142905` はfailure、check suite `115212344539` もfailureである。receipt成功を証明成功に読み替えない。

初回artifact `13639176055` の実ZIPは133,666 bytes、SHA256 `e33f87dec354b8d34d881969c8bbd7ee34af0d235dd695cd7e69f83301daf80a`。抽出実ログは1,955,436 bytes、SHA256 `47d16bed6ad89ddf29facc1042d4154669b797c6659573d74521e5486e0d349b`。失敗sourceとその記録を保持し、認証済みsourceとは区別する。

### 2回目sourceの失敗と、具体的な積分からの追加分離

2回目source `420a583516c56f508c3d297b16d1918daa2695cf`（663行、35,398 bytes、Git blob `ad33c3852b930d0463099b34c30c18245e6f8a82`、SHA256 `3fd44f14aabec1c41b6afff7ad53d8221ef7b3f2cafa932f627a21eccc9add2f`）の [CI #42535523218 attempt 1](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42535523218/attempts/1) も、workflow・主job `128898856864`・必須step 17がFAILUREで完了した。実checkoutは `4cb75a1a3ee6d160068ab2882df925400bd768b1`、sourceとの共通treeは `b40ca87ecc09772f66dc4a78640448f82d6578ce`。

変更Leanの診断は、167:0の分散上界での `whnf` timeout（固定3,900,000 heartbeats）と、246:8の後続kernel unknown constantの2件である。初回の関数和rewriteと `Continuous.exp` のエラーは解消した。warningは0、leafは `[11406/11406] Building ... (226s)` で失敗した。スカラー部分だけの先行分離では完了に至らなかったが、正確な内部hotspotを特定したという主張はしない。

主担当と独立CI担当は、完了主ログ3,369,417文字とreceipt全文9,702文字を別々に取得した。39の公理出力名は各1回で、欠落・余分・重複は0。`sorryAx` は0だったが、20件に前回と同じ非標準の自己名回復公理が含まれた。標準3公理のみ18件と、timeout宣言に対する見かけ上の公理なし1件は、失敗sourceの認証には用いない。

Receipt job `128900911308` とそのstep 2はSUCCESSで、実出力は `event=pull_request exact_sha=420a583516c56f508c3d297b16d1918daa2695cf source_result=failure run=42535523218 attempt=1`。発行status `58383627018` とsuite `115216434003` はfailureである。

Artifact `13639601648` の実ZIPは130,865 bytes、SHA256 `2e1b5a874c549e2ad9b96749d950bf8f45164187f279a2e8f8c7720cf46627dd`。抽出ログは1,945,785 bytes、SHA256 `dd7c5d1f82c509e150f515c5865518da8efa7cf0ca131bc1690205b63b852455`。ZIP実bytesのdigestはGitHub metadataと一致し、公理・診断・build完了の監査はFAILとなった。

続く修正では `boundedCenteredVariance_integral_le` を独立の一般定理として追加した。抽象的な型・確率測度・実関数のもとで、範囲、平均0、各項の可積分性から積分剰余評価を証明する。二次モーメントは積分のまま保持し、元の物理定理で既存AIQの条件とABNの真正二次モーメントを供給する。一般定理の証明を具体的なSU(2)への適用から分離したが、過去のtimeoutの内部原因を特定したという主張はしない。

元の39宣言の型、物理仮定、定義値、数学的定数、imports、固定上限は保持した。新しい補助定理を含む監査範囲は37定理・3定義・40公理出力となる。主担当と2名の独立ソース担当は統合後の690行全文を再読し、元の39署名の文字列一致、追加宣言1件、全40宣言と出力命令の順序・完全一致、残余本文の不変を確認した。静的レビューと実CI認証は区別した。

## 9．独立照合、実squash、正式記録

数理担当と別のソース/API担当が変更Lean全文・全40署名を読解し、元の真正二次モーメント、指数増分によるMGF単調性、真正Haarによる厳密性、明示閉上端、同じ比較因子の一意閾値、元の余裕の三分比較を確認した。単リンクの局所定義とAIO・AIP・AIQ・ABNの型付き署名、使用する固定mathlib APIも照合した。全推移依存ファイルを全文読解したという主張ではない。

独立CI担当も、主job完了後の実ログ3,364,415文字とreceipt全文9,708文字を、主担当とは別にGitHub MCPで取得した。exact-sourceから40の完全修飾名を再導出し、全40件が各1回で標準3公理のみ、欠落・余分・重複0、sorryAx・非標準公理・全Lean/Actions error・変更warning/error 0であることを照合した。依存閉包11,406件、leaf 47秒、実checkout、固定Lean version、全workflow/job/必須step/receiptの完了、exact-source statusとsuite/check runsも別途確認した。主担当はこれに加えて、診断ZIPの実bytes・SHA256とGit tree/blob・本文一致を照合した。これらの独立ログ照合および別job receiptは、別のLean kernelによる独立再証明を意味しない。

定理PR #6548の実squash `df0bdf6f5c70951009e0d55cd7eb10953f28cd8a` を統合後に再取得した。source／test-merge／実squashのGit treeは一致し、新規Leanの本文・Git blobも一致した。実squashの唯一の親は元canonical baseである。

[統合済みAIR Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/df0bdf6f5c70951009e0d55cd7eb10953f28cd8a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalVarianceRootCriticalComparisonV5_PZ37AIR.lean)。

本記録は、exact-sourceの全体完了、実公理出力監査、別jobのcompletion receipt、独立読解、実squashのtree/blob一致を確認した後、別のdocs-only PRで新規追加する。mainには同じ既存記録Git blobを用いる。既存Lean・既存記録・README・ROADMAP・workflowは変更せず、docs-onlyでStrict Leanを手動起動しない。
