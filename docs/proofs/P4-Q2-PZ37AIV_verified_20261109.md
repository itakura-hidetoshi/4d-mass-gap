# P4-Q2-PZ37AIV — 元transfer作用素ノルムの体積減衰と既存正規化尺度の発散

2026年11月9日 JST。元の完全SU(2) Wilson transferのambient Haar L²作用素と既存のGauss-law物理制限について、真正crossing分配関数によるノルム評価、固定正結合での体積極限、既存の逆ノルム正規化尺度の発散を形式証明した。[定理PR #6560](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6560)はMERGED。認証範囲は以下の定理の量化と対象に限る。

定理正本branchは `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラーである。開始時formalは `474543e46393d6a675a18417be99a6aee0bab7ac`、mainは `6f102470944e89628c3b7832a520e61d14e55de3`。append-only／tighten-only／overwrite-forbidden／same-rootを維持する。

元の完全作用、両端halfweight、真正正規化積Haar、符号付きZW物理源と既存連続代表、AIGの元の余裕・厳密負領域、既存仮定・定理・公開root・固定環境を変更していない。変更はLean leaf 1件の追加である。新しい正規化作用素・物理源・余裕の定義は導入していない。

[統合済みAIV Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/33cb9e84a415ac46275cc8a118c54b5e4336aa3a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferOperatorNormVolumeDecayV5_PZ37AIV.lean)。以下の数学説明はこの形式成果物の内容を記録するものであり、文章自体を追加の証明根拠とはしない。

## 1．証明された数学と範囲

AIUの単一源の点ごとの評価に加え、全L²単位球を既存ambient作用素 `R_H,β` と物理制限 `P_H,β` の作用素ノルムで評価した。β≥0で `‖P‖≤‖R‖≤√Zcross_H(2β)`、さらに物理ノルムには `exp(-2βp_H)Zcross_H(β)≤‖P‖≤Zcross_H(β)` を得る。β>0を固定すると両ノルムはHとともに0へ近づく一方、既存の正規化作用素のノルムは各Hで1のままである。AIVのL²ノルム評価はAIUの全境界点ごとの評価と異なる型の結果であり、AIVだけからAIUの全定理が従うとは主張しない。

### Unchanged mathematical objects

For each original finite volume `H : Nat`, let

\[
p_H=24(H+1)^3,
\qquad
\mu_H=\text{the original normalized spatial product Haar measure}.
\]

Write `K_{H,beta}(A,B)` for the existing complete SU(2) one-slab Wilson kernel and `K^cross_{H,beta}` for its existing crossing factor. The complete kernel retains both endpoint halfweights:

\[
K_{H,\beta}(A,B)
=e^{-\beta W_H(A)/2}
 K^{\mathrm{cross}}_{H,\beta}(A,B)
 e^{-\beta W_H(B)/2}.
\]

The operators under study are the already-defined ambient real Haar-L2 transfer

\[
R_{H,\beta}:
L^2(\mu_H;\mathbb R)\longrightarrow L^2(\mu_H;\mathbb R)
\]

and its already-defined Gauss-law physical restriction `P_{H,beta}`. In Lean these are respectively `periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator` and `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator`, at rank 2. The scalar

\[
\lambda_H(\beta)=\|P_{H,\beta}\|
\]

is notation in this explanation, not a replacement operator or a new definition in the leaf. Existing source theorems identify this positive scalar as a physical top eigenvalue at each finite volume.

The signed ZW physical source, its established continuous representative, the AIG original positive negative-transfer margin, and the original strict negative region remain unchanged. Alongside AIU's pointwise estimate for that one source image, the new operator-norm bounds control the full L2 unit ball in the stated operator domain. These are different types of estimates: AIV's L2 bounds alone do not imply all of AIU's pointwise boundary statements, and the original ZW source norm may depend on H.

The genuine crossing partition is still

\[
Z_H^{\mathrm{cross}}(\beta)=z(\beta)^{n_H},
\qquad
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),
\qquad (n_H:\mathbb R)=p_H.
\]

AIU's existing scalar rates are

\[
\rho(\beta)=-\log z(\beta),
\qquad d(\beta)=\beta e^{-2\beta}.
\]

The earlier exact identity is `Zcross_H(beta)=exp(-rho(beta)*p_H)`, and `0<d(beta)<=rho(beta)` for every positive beta. The leaf reuses these rates without modifying the coupling or any transfer normalization.

### Actual squared-kernel and ambient L2 bounds

For every real beta, squaring the original complete Boltzmann kernel gives the exact identity

\[
K_{H,\beta}(A,B)^2=K_{H,2\beta}(A,B).
\]

For beta >= 0, nonnegativity of both spatial half-actions gives

\[
K_{H,\beta}(A,B)^2
\le K^{\mathrm{cross}}_{H,2\beta}(A,B).
\]

Here `2*beta` arises only from the exact square of the kernel originally evaluated at beta. The statement does not replace the physical coupling of the operator being bounded.

The actual pair-Haar crossing integral is exactly `Zcross_H(2*beta)`. Compact continuity supplies joint integrability, and Fubini integrates the right boundary first, matching AIF's proved right-Haar mass identity. Therefore

\[
\iint |K_{H,\beta}(A,B)|^2\,d\mu_H(A)d\mu_H(B)
\le Z_H^{\mathrm{cross}}(2\beta).
\]

The equality between this literal squared integral and the norm square of the existing pair-Haar L2 kernel vector uses its explicit a.e. representative bridge. The existing Hilbert-Schmidt operator bound and the existing physical restriction norm bound then give

\[
\boxed{
\|P_{H,\beta}\|
\le\|R_{H,\beta}\|
\le\|K_{H,\beta}\|_{L^2(\mu_H\otimes\mu_H)}
\le\sqrt{Z_H^{\mathrm{cross}}(2\beta)}
}
\qquad(\beta\ge0).
\]

In particular, the original unnormalized physical norm is strictly less than one at every finite H and every beta > 0. This strengthens the previously inspected LX upper bound <= 1 to a strict bound < 1; it is not a claim that the normalized physical transfer has norm below one.

### A crossing-partition sandwich for the physical norm

The unchanged complete spatial action satisfies `0<=W_H(A)<=2*p_H`. Hence each original endpoint halfweight lies between `exp(-beta*p_H)` and one at beta >= 0. Multiplication of positive factors yields

\[
e^{-2\beta p_H}K^{\mathrm{cross}}_{H,\beta}(A,B)
\le K_{H,\beta}(A,B)
\le K^{\mathrm{cross}}_{H,\beta}(A,B).
\]

Integrating the left boundary uses AIU's genuine left-Haar crossing identity, which already incorporates the actual crossing-kernel symmetry. Thus every full-kernel row mass satisfies

\[
e^{-2\beta p_H}Z_H^{\mathrm{cross}}(\beta)
\le\int K_{H,\beta}(A,B)\,d\mu_H(A)
\le Z_H^{\mathrm{cross}}(\beta).
\]

Let `v` be the **existing** strictly positive continuous representative of the nonnegative unit physical top eigenvector. Its pointwise original-kernel equation is used with the existing Haar-L2 eigenvector only under the integral, then the already-proved a.e. equality replaces that class by `v`. This gives

\[
\lambda_H(\beta)v(B)
=\int v(A)K_{H,\beta}(A,B)\,d\mu_H(A).
\]

The original boundary configuration space is compact. The continuous function `v` therefore attains its maximum and minimum, and its existing pointwise positivity makes both extremal values positive. Applying the upper row-mass estimate at a maximum, and the lower row-mass estimate at a minimum, permits cancellation of these strictly positive finite-volume values.

The source separates this extremum argument into two general compact positive-eigenfunction comparison theorems, with explicitly stated integrability, positivity, eigen-equation and row-mass premises. Every premise is discharged from the original kernel and existing vacuum when proving the concrete physical results; no additional assumption is added to their finite-H, beta >= 0 statements. A separately typed continuity bridge uses the pinned lambda-form `Continuous.comp'` API with explicit insertion and joint-kernel functions, then fixes the same actual full-kernel target with `change`. These three structural helpers preserve the original physical conclusions and do not add assumptions to them. The result is

\[
\boxed{
e^{-2\beta p_H}Z_H^{\mathrm{cross}}(\beta)
\le\lambda_H(\beta)
\le Z_H^{\mathrm{cross}}(\beta)
}
\qquad(\beta\ge0).
\]

This sandwich concerns the existing physical restriction. Its upper bound by `Zcross(beta)` is not separately asserted for the ambient operator in this leaf; the ambient bound is the proved doubled-coupling square-root estimate above.

Using the exact partition rate gives the equivalent physical scalar estimates

\[
e^{-(2\beta+\rho(\beta))p_H}
\le\lambda_H(\beta)
\le e^{-\rho(\beta)p_H}
\le e^{-d(\beta)p_H}.
\]

The interval between these upper and lower bounds is volume dependent. The source does not prove that `lambda_H` is asymptotic to `Zcross_H`, or identify its exact exponential volume rate.

### Fixed-coupling volume limits and the ambient unit ball

For each fixed beta > 0, the physical rate `rho(beta)` and the ambient rate `rho(2*beta)/2` are strictly positive. Since the original `p_H` tends to infinity, the scalar norm sequences satisfy

\[
\boxed{
\lim_{H\to\infty}\|R_{H,\beta}\|=0,
\qquad
\lim_{H\to\infty}\|P_{H,\beta}\|=0
}
\qquad(\beta>0\text{ fixed}).
\]

The quantitative ambient estimate used here is

\[
\|R_{H,\beta}\|
\le e^{-[\rho(2\beta)/2]p_H}.
\]

The formal unit-ball consequence states

\[
\forall\beta>0\ \forall\eta>0\ \exists N\ \forall H\ge N\quad
\forall f\in L^2(\mu_H;\mathbb R),
\qquad \|f\|\le1\ \Longrightarrow\ \|R_{H,\beta}f\|<\eta.
\]

The same N works for all ambient unit-ball vectors at each sufficiently large H. Beta is fixed before the volume limit. The Hilbert spaces at different H retain their original distinct types; no common-space operator convergence is asserted.

The corresponding physical norm-floor obstruction is also formalized:

\[
\neg\exists\eta>0\ \forall H,\quad
\eta\le\lambda_H(\beta)
\qquad(\beta>0\text{ fixed}).
\]

Every finite-volume physical norm remains strictly positive. The obstruction concerns a common positive lower bound across all volumes for this unchanged raw operator norm.

### The existing normalization scale grows

The repository already defines its normalized physical operator by

\[
\widehat P_{H,\beta}=\lambda_H(\beta)^{-1}P_{H,\beta}
\]

and already proves its norm equals one. AIV introduces no alternative normalized operator. Positivity of the original physical norm and the proved sandwich give

\[
\boxed{
e^{\rho(\beta)p_H}
\le\lambda_H(\beta)^{-1}
\le e^{(2\beta+\rho(\beta))p_H}
}
\qquad(\beta\ge0).
\]

For every fixed beta > 0, this already-used inverse-norm normalization scale tends to positive infinity with H. A common-cutoff theorem combines, for any eta > 0 and any real R,

\[
0<\lambda_H(\beta)<\eta,
\qquad
R\le\lambda_H(\beta)^{-1},
\qquad
\|\widehat P_{H,\beta}\|=1
\]

for all sufficiently large H. This formally separates decay of the original unnormalized norm from the behavior of the existing normalized operator. It does not establish a normalized physical gap, coercivity or excitation estimate.

### Quantitative statement at the unchanged original beta0

For the same original coupling

\[
\beta_0=\frac{\log(3/2)}{64},
\]

AIU proves `d(beta0)>=1/384`. Combining this with `p_H=24(H+1)^3` yields

\[
\boxed{
\lambda_H(\beta_0)
\le e^{-(H+1)^3/16},
\qquad
\lambda_H(\beta_0)^{-1}
\ge e^{(H+1)^3/16}.
}
\]

The physical norm bound has no polynomial source-amplitude prefactor because it bounds the original operator norm itself. The existing beta0 and all its prior rational bounds are unchanged.

### Retained obstructions and interpretation limits

The actual original signed-source image and original negative region from AIU/AIT remain unchanged. AIV adds operator-norm information; it neither replaces their original margins nor reverses finite-volume negativity results.

The leaf proves a scalar norm-volume limit and an obstruction for a positive volume-uniform raw physical norm floor. It does not construct a common Hilbert-space continuum limit, prove decay of the normalized physical operator norm, establish a normalized coercivity or excitation gap, establish a negative eigenvalue from source-image negativity, extend full-original-margin half-Haar to all positive beta at each fixed H, or prove a Hamiltonian spectral gap or continuum four-dimensional Yang-Mills mass gap. These implications require their own compatible hypotheses and proofs.


## 2．宣言と完全な実公理出力監査

新規sourceは816行、46,136 bytes、38定理＋0定義である。全38宣言に対して完全修飾名の `#print axioms` を1回ずつ置き、宣言・出力命令・実出力の名前と順序を一対一で照合した。

```text
MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint
```

表では共通接頭辞 `p4Q2PZ37AIV_` を省略する。

| # | 種別 | 宣言suffix |
| --- | --- | --- |
| 1 | theorem | `originalCrossingAction_le_fullSlabAction` |
| 2 | theorem | `originalKernel_sq_eq_doubledCoupling` |
| 3 | theorem | `originalKernel_sq_le_doubledCrossing` |
| 4 | theorem | `originalCrossingKernel_pair_integrable` |
| 5 | theorem | `originalCrossingKernel_pair_integral` |
| 6 | theorem | `originalKernelPair_normSqIntegral_le_crossingPartition` |
| 7 | theorem | `originalKernelPairL2_normSq_eq_integral` |
| 8 | theorem | `originalKernelPairL2_normSq_le_crossingPartition` |
| 9 | theorem | `originalKernelPairL2_norm_le_sqrtCrossingPartition` |
| 10 | theorem | `originalAmbientTransfer_norm_le_sqrtCrossingPartition` |
| 11 | theorem | `originalPhysicalTransfer_norm_le_sqrtCrossingPartition` |
| 12 | theorem | `originalPhysicalTransfer_norm_lt_one` |
| 13 | theorem | `compactPositiveEigenfunction_le_uniformRowMass` |
| 14 | theorem | `uniformRowMass_le_compactPositiveEigenfunction` |
| 15 | theorem | `originalFullKernel_leftContinuous` |
| 16 | theorem | `originalSpatialHalfweight_ge_expFloor` |
| 17 | theorem | `originalFullKernel_le_crossingKernel` |
| 18 | theorem | `originalFullKernel_ge_halfweightFloorCrossing` |
| 19 | theorem | `originalFullKernel_leftHaarIntegral_le_crossingPartition` |
| 20 | theorem | `originalFullKernel_leftHaarIntegral_ge_halfweightFloorCrossingPartition` |
| 21 | theorem | `originalContinuousVacuum_eigenIntegral` |
| 22 | theorem | `originalPhysicalTransfer_norm_le_crossingPartition` |
| 23 | theorem | `originalCrossingPartition_mul_halfweightFloor_le_physicalTransferNorm` |
| 24 | theorem | `originalPhysicalTransfer_norm_le_exactRate` |
| 25 | theorem | `originalPhysicalTransfer_norm_ge_exactRate` |
| 26 | theorem | `originalPhysicalTransfer_norm_le_explicitRate` |
| 27 | theorem | `originalAmbientTransfer_norm_le_exactRate` |
| 28 | theorem | `originalExponentialVolume_tendsto_zero` |
| 29 | theorem | `originalAmbientTransfer_norm_tendsto_zero` |
| 30 | theorem | `originalPhysicalTransfer_norm_tendsto_zero` |
| 31 | theorem | `originalAmbientTransfer_unitBall_small_eventually` |
| 32 | theorem | `originalPhysicalTransfer_no_uniformPositiveNormFloor` |
| 33 | theorem | `originalPhysicalTransfer_inverseNorm_ge_exactRate` |
| 34 | theorem | `originalPhysicalTransfer_inverseNorm_le_exactRate` |
| 35 | theorem | `originalPhysicalTransfer_inverseNorm_tendsto_atTop` |
| 36 | theorem | `originalRawDecay_and_existingNormalization_eventually` |
| 37 | theorem | `originalFixedCoupling_physicalNorm_le_explicitVolumeBound` |
| 38 | theorem | `originalFixedCoupling_inverseNorm_ge_explicitVolumeBound` |

最終Exact-source・統合後pushの各認証runにおける全38件の実公理出力は `propext`、`Classical.choice`、`Quot.sound` の標準3公理のみ。sorryAx、非標準公理、欠落、余分、重複は0である。それ以前の2回の失敗runの診断出力は第5節に別に保持する。別jobのreceiptや独立した記録照合は、別Lean kernelによる再証明を意味しない。

## 3．依存構造と固定環境

直接importsは11件である。

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
```

AIFの真正crossing Haar積分、AIUの左Haar積分・正確な分配関数率・明示率を、元の完全kernel・ambient Hilbert–Schmidt作用素・Gauss-law制限へ接続する。literal kernelとpair L²代表の一致、元の物理top eigenvectorと既存連続代表の一致は、それぞれのa.e.橋を明示的に用いる。両端halfweightの積を保持してkernelと行積分を上下評価し、既存の正値連続vacuumのコンパクト最大・最小から物理ノルムを挟む。最大・最小の正値性は各有限Hの定理であり、Hに一様な正のvacuum下限を仮定しない。

固定mathlibでは `integral_prod` とその可積分性仮定、`integral_const_mul`、`Real.sqrt_le_sqrt`、`Real.sqrt_sq`、`Real.sqrt_lt_sqrt`、`Real.exp_half`、`Real.tendsto_exp_atTop`、`Real.tendsto_exp_neg_atTop_nhds_zero`、コンパクト極値定理、正の因子の消去、逆数の順序反転を原署名で確認した。全依存ソースを人手で再読したという意味ではなく、使用署名の確認と依存閉包の機械的検査を区別する。

現在のformal baseでtreeと取得blobを照合した作用素・正規化・vacuum関連のfocused依存は次のとおりである。共通ディレクトリは `MGAP4D/MathlibAnalytic/`。

| 依存source | Git blob |
| --- | --- |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer.lean` | `4ba2fe9712c364429ec5e4bf88d6e7aa7bcc0fe9` |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2TransferFactorization.lean` | `bc35c94cd1c12ee28e4b2e911d2852b38a8ab8fd` |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel.lean` | `c398b45389f8e8c72c02ce17780e1e86210f8cbb` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferOneSlabOperatorNormBetaLipschitz.lean` | `e27ae517132966f3b2cae81492a8bf42a5add80d` |
| `RealL2HilbertSchmidtKernelOperator.lean` | `fc223e6716f52443b99951bc49d8613266909b66` |
| `RealL2HilbertSchmidtKernelOperatorContinuity.lean` | `d3c751c48211fce7aeb82c16ae6fc079c7343e3b` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay.lean` | `13d21ce23c09b08ed86f860d9aa1f8b7ee27eb55` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay.lean` | `c52f912d6d94f032db7e3375520cd08088ac68fa` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay.lean` | `082a6fa8567e077eee65b74b9fb65e0ce328087e` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryStrongLimit.lean` | `d6936f2002f1377b7f3ffe4b11e102197f688498` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenvector.lean` | `9f0598c18fb47b762cccbb35cafd91b36090fc00` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz.lean` | `283546cfef7f5cbe9eb963f02594af2fe3af0d58` |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferCompact.lean` | `bddab99b294c7b4eb318eadf0dadad387613f33e` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction.lean` | `484153447a39409e258ebdadf06558bc19e7b249` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay.lean` | `b2f73d0201b3e34a7aa4012fe4a4d16608c96db6` |
| `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTransferNormOneGITrueFloorV5_LX.lean` | `b1573d23d7c62c235a5dbe307af5b1f9154621a3` |
| `PhysicalYangMillsWilsonSU2OriginalPhysicalRawNormFirstVariationV5_PZ37ZV.lean` | `669e7cb1481fa2501a307761420740831e2cd315` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalization.lean` | `d043f505d78cffa592a19cca5403d7e04972816f` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor.lean` | `89b52086f6b41d75c2e791f6d322955868a7f147` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization.lean` | `f0a9fa2b018467de9b95347f8bb9c69e11f52828` |
| `PeriodicHypercubicEvenSpecialUnitaryGaussLawTransfer.lean` | `33a15172d4bb66c5f720973956a73b8dd909d381` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative.lean` | `8ac2a8af6eae791e686114cbea4411aa569b25f5` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack.lean` | `fb28eea623da0550ac07125965da49d74cb4c2e9` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack.lean` | `813ca1218fd26e9b58d26f4c1f899094f0b01763` |
| `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion.lean` | `b1555feba05c42276f215204a28367ea010246e6` |
| `PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU.lean` | `84b59eb50635e2eba29834927ac2f032492e1219` |
| `PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean` | `a3a0899a9688479e49b605c0051cb5050f489d89` |
| `PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP.lean` | `49004405b63265db818d6e08acd8c85617e9393a` |
| `PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT.lean` | `10d079143870929f2df37a18a2703a94a78c300e` |

| 固定項目 | 値 |
| --- | --- |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| maxHeartbeats | `3900000` |
| synthInstance.maxHeartbeats | `1050000` |
| lean-toolchain blob | `6c7e31fffe3e03be3e0d7021acd9cd848e44db26` |
| lake-manifest.json blob | `01260678b674ab241e753563e913c7ce9c6ba659` |
| Exact-source workflow blob | `4efb6399db1e4f3817c79f78a8d1338ea1c24c70` |

固定環境・workflow・既存仮定・heartbeatを変更していない。Lakeによる依存を含む型検査が認証主体であり、既存の `LEAN_FAST_DIRECT_ELAB=false` は重複した直接elaborationを行わない設定のままである。Strict Leanを省略する変更はない。

## 4．Exact-source CI・定理squash・統合後push CI

| 対象 | 実観測値 |
| --- | --- |
| Canonical formal base | `474543e46393d6a675a18417be99a6aee0bab7ac` |
| 認証source HEAD | `1eaaf80a65e0f217caae8d00dd0317c1086db385` |
| 実test-merge／PR checkout | `7f9a44279fdeff251fc4aed8d26a9c3630fda6ca` |
| 実定理squash | `33cb9e84a415ac46275cc8a118c54b5e4336aa3a` |
| source／test-merge／squash共通Git tree | `52191ac4df018b4b7307825c09fd67ffb09ec371` |
| 新規Lean共通Git blob | `d298c6be6825cbf37410283f54ef0b67fe7b0db9` |
| 新規Lean SHA256 | `63e384f489da6e927561936a7ccf312b4dae4a30627d5de8bd31cadb8cdba313` |

source・実test-merge・実squashのtreeが一致し、source全文とblobも一致した。実squashの唯一の親は開始時formal baseであり、統合直後のformal refが実squashへ進んだことを再観測した。後続の文書専用commitのtreeと定理共通treeを同一視しない。

| 検証 | Exact-source PR | 統合後push |
| --- | --- | --- |
| Run／attempt | [#42567459390](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42567459390/attempts/1)、attempt 1、completed／SUCCESS | [#42568082026](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42568082026/attempts/1)、attempt 1、completed／SUCCESS |
| 対象SHA | `1eaaf80a65e0f217caae8d00dd0317c1086db385` | `33cb9e84a415ac46275cc8a118c54b5e4336aa3a` |
| 実checkout | `7f9a44279fdeff251fc4aed8d26a9c3630fda6ca` | `33cb9e84a415ac46275cc8a118c54b5e4336aa3a` |
| 主job／必須Lean step 17 | `128996996676`、ともにSUCCESS | `128998923045`、ともにSUCCESS |
| 依存閉包 | 11410／11410 SUCCESS | 11410／11410 SUCCESS |
| 新規leaf | ℹ [11410/11410] Built MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferOperatorNormVolumeDecayV5_PZ37AIV (39s) | ℹ [11410/11410] Built MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferOperatorNormVolumeDecayV5_PZ37AIV (47s) |
| 実公理出力 | 38／38、標準3公理のみ | 38／38、標準3公理のみ |
| 欠落／余分／重複／非標準公理 | 0／0／0／0 | 0／0／0／0 |
| 当該認証runの全実ログsorryAx／Lean error | 0／0 | 0／0 |
| 変更Lean warning／error | 0／0 | 0／0 |
| 独立receipt job／step 2 | `128998386389`、ともにSUCCESS | `129000849304`、ともにSUCCESS |
| exact-SHA status ID | `58396173959`、SUCCESS | `58396476915`、SUCCESS |
| check suite／check runs | `115297343738`、SUCCESS／2件SUCCESS | `115298887978`、SUCCESS／2件SUCCESS |
| 完了主ログの取得・公理照合 | 全文3,422,617文字、38／38一致 | 全文3,422,336文字、38／38一致 |
| 診断artifact ID | `13651787328` | `13652516944` |
| 実ZIP bytes | 132,615 | 132,389 |
| 実ZIP SHA256 | `13b622608cc0cae771f5ebf7c6819b75530878a9ddb2151789691ca739bebaf3` | `3c92fe5b36ee24c4949881f791aff9c868bae6fd7358233073d5c251f3d89b84` |
| 抽出実ログ bytes | 1,984,303 | 1,984,291 |
| 抽出実ログ SHA256 | `742631c91d99469a35c9058aa894189a1b039dc9d81ccd7592a6bc28267e00db` | `01eae90d433e05e3c2866f5ea9fd480c65c29e39a50b926ced97aa0e15c5a1de` |

両runとも全workflow・主job・必須Lean step 17・独立receipt jobとstep 2・exact-SHA commit status・check runsの完了を確認した。実receipt識別行は次のとおりである。

```text
[mcp-receipt] event=pull_request exact_sha=1eaaf80a65e0f217caae8d00dd0317c1086db385 source_result=success run=42567459390 attempt=1
[mcp-receipt] event=push exact_sha=33cb9e84a415ac46275cc8a118c54b5e4336aa3a source_result=success run=42568082026 attempt=1
```

完了主ジョブログ全文と診断artifactの実ZIP bytesを取得した。ZIPのSHA256をGitHub metadata digestと一致させ、抽出した実 `lean-fast.log` の全38公理出力を新規全宣言に照合した。主ログではtimestamp接頭辞を除いてから複数行の公理集合を解析し、artifact実ログと同じ全宣言・標準公理集合であることを確認した。

変更Lean warning 0は、既存依存から再生されるwarningまで全件0という主張ではない。この最終認証2 runでの全Lean errorとsorryAxの不存在は、主ログ・artifactで別に確認した。以前の失敗runには適用しない。SUCCESS metadataやartifact名だけを実ログの代わりにはしていない。

## 5．作成・新規性レビュー・試行履歴

開始時にGitHub MCPでformal/mainのHEAD、AIU統合状態、未統合PR、正本treeを再観測した。正本tree `68ad5472f7f0e6637d93af779b9c98c0fbd3cc00` は9,072 entries、truncated=false、AGENTS.mdはなかった。未統合PR18件は以前の別作業であり、AIV並行PRはなかった。

新規性レビューでは、前段で取得・索引化した元source family 288ファイルのblobを今回の正本treeと再照合し、全件不変であることを確認した。AIUを加えた現在のfamilyは289ファイルであり、さらに作用素・正規化・vacuumのfocused 25ファイルを今回の正本で取得して調べた。既存LXの物理ノルム上界1、旧正規化の正値性とglobal minorization下界、固定Hでの結合極限、正規化された作用素冪の時間減衰、共通空間への別条件付きの構成を、本件の固定正結合・元体積におけるraw作用素ノルム極限から区別した。リポジトリ全定理に対する意味的非同値性を網羅的に証明したという主張ではない。

CI前の全文レビューで、固定mathlibの因子消去補題の左右の命名を確認し、物理上界の最後を `mul_le_mul_iff_left₀`、物理下界の最後を `mul_le_mul_iff_right₀` に修正した。固定APIでは前者は共通右因子、後者は共通左因子を消去する。これは公開sourceのCI実行前の静的修正であり、失敗したLean実行とは記録しない。修正後の全文・imports・全署名・a.e.橋・極値の正値性・量化・指数の符号と有理係数を再レビューした。

### 保存した不成立の実 CI と構造修正

以下の2 run はともにFAILUREであり、認証済みの実行へ読み替えない。独立receipt jobのSUCCESSは失敗結果の発行成功であり、Lean証明の成功ではない。各runの実ZIP digest、展開実ログ、当該source、failure receiptを照合して保持する。

| 項目 | 初回 | 2回目 |
| --- | --- | --- |
| 実run／attempt | [#42564655886](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42564655886/attempts/1)、attempt 1、FAILURE | [#42566323927](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42566323927/attempts/1)、attempt 1、FAILURE |
| Source HEAD | `cad70873f870b62dc78dabc5a0511639e340719e` | `9413b5fc58e96457d1e3155b52e24c948fa74167` |
| Source Git blob | `25158031198e8420a3916b4c3ff5b06b721ba922` | `76b1ce713f39cd1fa67956ed972011b638f1514c` |
| Source規模 | 763行、43,117 bytes、35定理 | 811行、45,871 bytes、38定理 |
| 主job／必須step 17 | `128988433306`、FAILURE | `128993482611`、FAILURE |
| Receipt job／step 2 | `128991937315`、SUCCESS／source_result=failure | `128996223359`、SUCCESS／source_result=failure |
| 変更Lean error／全error行 | 8／10 | 1／3 |
| 失敗ログ中のsorryAx／非標準公理を含む出力件数 | 5／13 | 16／16 |
| Artifact ID | `13651322570` | `13652095885` |
| 実ZIP bytes／SHA256 | 133,348／`c47ecb81cc266662de15b899c9b4101cddf40d70d46cce7ff7bde99575cba9e6` | 133,070／`4668463112850438611c869e354c44bad70f3ff147014df270b1c3649dfce393` |
| 展開実ログ bytes／SHA256 | 1,989,163／`0ce27681d84db5f4464d6ee863db740308484ab4ea0929c79336bee1c9da46c7` | 1,986,784／`2f453e4e46f8caf5e3ac8712dcef35850f3839506c632eb09a3ddc646b105885` |

初回は354:4、372:4の具体的kernelの連続性合成と404:0、446:0の具体的物理ノルム極値証明で、固定上限3900000のisDefEq／whnf timeoutが生じた。509:8、518:8、533:8は未成立の宣言を参照する後続unknown constant、586:14は別の物理ノルム非負性の型推論不一致である。全error行には、それぞれ変更sourceのerrorに加えてLean終了とbuild失敗の2行が含まれる。

初回35定理の全署名を保持し、一般のコンパクト空間上の正値固有関数について行積分による上界・下界を示す2補題と、元kernelの左変数連続性1補題を追加した。一般補題の可積分性・正値性・固有方程式・行積分境界の前提は、具体的な物理定理では既存対象の事実から全て満たす。元の結論への仮定追加はない。物理ノルム非負性には対象作用素を明示した。

2回目は、型を明示した `hJoint` と `hInsert` の `hJoint.comp hInsert` における354:8のwhnf timeoutだけが残った。固定mathlibの `Continuous.comp` が `g ∘ f` を返す形を避け、同じ固定版のlambda形API `Continuous.comp'` に `f` と `g` を明示し、`change` で既存kernelの目標型を指定した。これは正本AINの既存証明構造に合わせた変更であり、数学的前提・対象・結論を変更しない。2回目の38定理全署名は最終認証sourceでも同一であり、imports・局所記法・namespace・section変数・optionsも両失敗sourceと照合して不変である。

補題の追加後も `maxHeartbeats=3900000` と `synthInstance.maxHeartbeats=1050000` を維持し、heartbeat増加や警告抑止を使っていない。失敗ログのsorryAxと非標準公理出力は失敗したelaborationの回復結果として残し、認証出力として採用しない。sourceに `sorry` や公理を追加したという記録でもない。最終認証の全公理出力は別に検査しており、この失敗診断値を消去・上書きしない。

```text
[mcp-receipt] event=pull_request exact_sha=cad70873f870b62dc78dabc5a0511639e340719e source_result=failure run=42564655886 attempt=1
[mcp-receipt] event=pull_request exact_sha=9413b5fc58e96457d1e3155b52e24c948fa74167 source_result=failure run=42566323927 attempt=1
```

確認した連続性APIの来歴は、正本AIN Git blob `00afd9f819da0ec2c9ceaf074a54ee73aa36454e` と固定mathlib `Mathlib/Topology/Continuous.lean` Git blob `294a9ca405aa750cd301ebf09937af5384148d62` である。

### 最終認証への再試行記録

初回Exact-source CI #42564655886は変更Lean error 8件でFAILUREとなり、2回目 #42566323927は連続性の合成におけるwhnf timeout 1件でFAILUREとなった。両runのsource・実ZIP digest・完全実ログ・failure receiptを保存し、失敗したelaborationによる回復用公理出力（sorryAx出現5件／16件）を認証結果として採用していない。初回35定理の全署名を維持して一般の正値固有関数による行積分比較2補題と連続性1補題を追加し、具体的な物理定理の全前提を元の対象から満たした。2回目の全38署名を保持したまま、既存AINのContinuous.comp'・明示f/g・changeの構造を採用した。固定環境とheartbeat上限を維持し、source 1eaaf80a65e0f217caae8d00dd0317c1086db385に対する3回目 #42567459390で全workflow・必須Lean step・独立receipt・全38実公理出力・actual artifact digestが認証された。修正後sourceを変更せずsquashし、統合後の自動push CIは別欄の実証拠で検査した。ローカルLean実行を行ったという主張はない。

## 6．残る課題と文書同期

今回、元の非正規化物理作用素ノルムには固定正結合で正の体積一様下限が存在しないことを形式証明した。ambient作用素の単位球全体も、同じ十分大きいHで任意に小さくなる。ただしHごとのHilbert空間は異なり、共通空間上の作用素極限を構成したわけではない。既存正規化尺度は発散し、既存正規化作用素のノルムは各Hで1である。この事実から正規化後のcoercivityや励起gapの成否は決まらない。

元の符号付き源・余裕・厳密負領域を保持する。各固定Hでの任意正結合における元の全余裕半Haar下界、正規化後の実際の作用素比較とスペクトル／coercivity評価、共通の極限対象への接続、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは、必要な対応する証明が得られるまで未認証として残す。源像の負値を作用素の負固有値へ昇格させない。

次段AIWの候補は、既存正規化作用素に対する相対評価と、真正のスペクトル・coercivityへの接続条件の検討である。ノルム1という既存事実をgapの証明と扱わず、正規化尺度の体積依存性を明示的に保持する。これは研究候補であり、本記録の追加定理ではない。

正式記録とREADME・ROADMAPを文書専用PRで追加し、各branchでREADME・ROADMAPの既存全文prefixを保って末尾追記する。文書専用変更のためStrict Leanを手動起動しない。mainにはformalの正式記録と同一Git blobをミラーする。mainの自動workflowは文書ミラー後の検査であり、formalのExact-source定理認証を置き換えない。本記録は後続のmain workflow成功を先取りして記載しない。
