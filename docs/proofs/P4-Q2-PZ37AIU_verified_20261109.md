# P4-Q2-PZ37AIU — 元transfer像の全境界一様な体積減衰と正の一様負値深さの不存在

2026年11月9日 JST。固定した正結合における、元の非正規化transferを元の符号付き物理源へ作用させた値について、新しい絶対値上界と体積極限を形式証明した。[定理PR #6557](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6557)はMERGED。認証した範囲は以下の定理の量化と物理対象に限る。

正本branchは `formal/real-hilbert-uniform-coercive-strong-limit`、mainは文書ミラーである。開始時のcanonical formalは `ef4fc8c592898a513e8abc9bbff6b269e43768bd`、mainは `8192d365146c57b434581b263cb79ff0e195ff41`。append-only／tighten-only／overwrite-forbidden／same-rootを維持する。

元の完全SU(2) Wilson作用、両端の空間halfweight、符号付きZW物理L²源と既存の連続代表、真正正規化積Haar、AIGの元の余裕と厳密負領域、既存仮定・定理・公開root・固定環境は変更していない。追加はLean leaf 1件のみである。

[統合済みAIU Lean全文](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU.lean)。本記録の数学部分はこの形式成果物の説明であり、説明の文章自体を追加の証明根拠とはしない。

## 1．証明された内容と適用範囲

主結果は、任意に固定した `beta > 0` と `eta > 0` に対して `∃N, ∀H≥N, ∀B:Cfg_H, |T_H,beta f0_H(B)|<eta` である。Hに依存する境界空間を同一視せず、境界に依存しない共通の体積cutoffを構成する。これはAITの特定補助床が消失するという定理から推測した結論ではなく、真正crossing分配関数による実際のtransfer像の上界から導く。

### Original objects and notation

Let \(H\in\mathbb N\) be the original finite-volume index and put
\[
p_H=24(H+1)^3,\qquad
u_{H,\beta}(B)=T_{H,\beta}f_{0,H}(B).
\]
Here \(T_{H,\beta}\) is the existing unnormalized full-action transfer,
\(f_{0,H}\) is the existing signed ZW physical L2 source, and \(B\) belongs
to the original configuration space at volume \(H\). Its original continuous
representative \(f_H\) supplies the established pointwise integral bridge.

The complete SU(2) Wilson action, both spatial halfweights, genuine normalized
Haar measure, original source, AIG margin, and AIG strict negative region are
unchanged. Write \(W_H\) for the original spatial action and
\[
z(\beta)=\int_G e^{-\beta E(g)}\,d\nu(g),\qquad
Z_H^{\mathrm{cross}}(\beta)=z(\beta)^{n_H},\qquad (n_H:\mathbb R)=p_H.
\]
These are AIF's genuine partitions; the count equality is the existing AIP
identity for the actual original spatial links. Here \(E(g)\) is the original
SU(2) Wilson plaquette energy and \(\nu\) is genuine normalized Haar measure.

### An upper bound on the actual transfer image

For every \(H\), every \(\beta\ge0\), and every original boundary \(B\),
\[
|u_{H,\beta}(B)|
\le e^{-(\beta/2)W_H(B)}\frac{p_H}{2}Z_H^{\mathrm{cross}}(\beta)
\le \frac{p_H}{2}Z_H^{\mathrm{cross}}(\beta).
\]
The proof uses the existing absolute bound on the original signed continuous
source, nonnegativity of the complete spatial action, and the actual crossing
kernel. Kernel symmetry converts AIF's right Haar integral into the left Haar
integral required by the transfer. The left halfweight is estimated explicitly;
the right halfweight remains visible in the first displayed bound.

Thus this is an estimate for the actual original source image at every
boundary. Its proof does not infer an actual-transfer upper bound from a
negative lower certificate. It does not assert an operator-norm bound.

### Exact and elementary crossing-partition rates

AIU introduces scalar rates and the corresponding scalar envelope:
\[
\rho(\beta)=-\log z(\beta),\qquad d(\beta)=\beta e^{-2\beta},\qquad
E_H(\beta)=\frac{p_H}{2}Z_H^{\mathrm{cross}}(\beta).
\]
AIF's strict positivity of \(z\) makes
\[
Z_H^{\mathrm{cross}}(\beta)=e^{-\rho(\beta)p_H}
\]
an exact identity for every real \(\beta\). For \(\beta\ge0\), AIP's genuine
deficit \(z(\beta)\le1-d(\beta)\), together with \(1-d\le e^{-d}\), gives
\[
d(\beta)\le\rho(\beta),\qquad
Z_H^{\mathrm{cross}}(\beta)\le e^{-d(\beta)p_H}.
\]
Both rates are strictly positive when \(\beta>0\). Consequently,
\[
|u_{H,\beta}(B)|\le E_H(\beta)
=\frac{p_H}{2}e^{-\rho(\beta)p_H}
\le\frac{p_H}{2}e^{-d(\beta)p_H}.
\]

### Fixed-coupling volume limit and dependent boundary spaces

For each fixed \(\beta>0\), the original count tends to infinity and
\(p_H e^{-a p_H}\to0\) for each fixed \(a>0\). Hence \(E_H(\beta)\to0\), and
\[
\forall\beta>0\;\forall\eta>0\;\exists N\in\mathbb N\;
\forall H\ge N\;\forall B\in\mathrm{Cfg}_H,
\qquad |u_{H,\beta}(B)|<\eta.
\]
The coupling is fixed before choosing the volume cutoff. This statement does
not quantify over arbitrary volume-dependent couplings \(\beta_H\).

The boundary domains vary with \(H\). No common configuration space is
constructed. For any dependent choice \(B_H\in\mathrm{Cfg}_H\), the resulting
real-valued sequence satisfies \(u_{H,\beta}(B_H)\to0\). The uniform estimate
holds for every such boundary, so choosing a boundary as a function of volume
cannot preserve a fixed positive absolute amplitude.

In particular, for fixed \(\beta>0\) and \(\eta>0\), the set
\[
\{B\in\mathrm{Cfg}_H:u_{H,\beta}(B)\le-\eta\}
\]
is empty for all sufficiently large \(H\). The source also states explicitly
that neither a positive absolute amplitude nor a positive negative depth can
be attained at some boundary in every volume with one common positive bound.

### Original margin, finite-volume negativity, and half Haar mass

The original AIG margin is retained exactly:
\[
\varepsilon_H(\beta)
=\frac{\beta}{2}Z_H^{\mathrm{cross}}(\beta)e^{-2\beta p_H}V_H,
\qquad V_H=\int f_H^2\,d\mu_H.
\]
For every fixed \(\beta>0\), AIP's \(Z_H^{\mathrm{cross}}<1\) and AIS's
\(V_H\le p_H^2/4\) give
\[
0<\varepsilon_H(\beta)
\le\frac{\beta}{8}p_H^2e^{-2\beta p_H}\longrightarrow0.
\]
AIG's existing finite-volume negative witnesses remain compatible with this
limit: \(\varepsilon_H(\beta)>0\) holds separately for each finite \(H\),
while the positive margin varies with volume and tends to zero.

Let \(\mathcal N_{H,\beta}=\{B:u_{H,\beta}(B)<-\varepsilon_H(\beta)\}\)
be the unchanged strict region. Combining AIT's eventual full-margin half-Haar
theorem with the two vanishing estimates gives one common cutoff:
\[
\forall\beta>0\;\forall\eta>0\;\exists N\;\forall H\ge N:
\quad \mu_H^{\mathrm{real}}(\mathcal N_{H,\beta})\ge\tfrac12,
\quad 0<\varepsilon_H(\beta)<\eta,
\quad \forall B\in\mathrm{Cfg}_H,\ |u_{H,\beta}(B)|<\eta.
\]
A region defined by the varying original margin can therefore retain half
Haar mass while every actual amplitude becomes small. The eventual emptiness
statement above concerns a fixed depth \(\eta\), not this varying-margin region.

### Unchanged fixed coupling

At \(\beta_0=\log(3/2)/64\), the existing exact enclosure
\(1/192\le\beta_0\le1/128\) and the exponential tangent imply
\(e^{-2\beta_0}\ge1/2\), hence \(d(\beta_0)\ge1/384\). Therefore,
\[
|u_{H,\beta_0}(B)|\le
12(H+1)^3\exp\!\left(-\frac{(H+1)^3}{16}\right)
\qquad\text{for every original }H\text{ and }B.
\]
The constants are rational consequences of the original fixed coupling and
the exact count; no numerical approximation or rescaled coupling is used.

### Theorem-name map

All names in this table have prefix `p4Q2PZ37AIU_` in namespace
`MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`.

| Statement | Declaration suffix |
| --- | --- |
| Genuine left crossing Haar integral | `originalCrossingKernel_leftHaarIntegral` |
| All-boundary bound with retained right halfweight | `originalTransfer_abs_le_rightHalfweightCrossingEnvelope` |
| All-boundary crossing envelope | `originalTransfer_abs_le_crossingEnvelope` |
| Exact partition exponent | `originalCrossingPartition_eq_exp_rate` |
| Elementary rate below exact rate | `explicitPartitionDecayRate_le_original` |
| Actual transfer bounds by exact/elementary rates | `originalTransfer_abs_le_exactRate`, `originalTransfer_abs_le_explicitRate` |
| Scalar envelope volume limit | `originalTransferPartitionEnvelope_tendsto_zero` |
| Uniform smallness over varying boundary domains | `originalTransfer_uniformly_small_eventually` |
| Limit for each dependent boundary selection | `originalTransfer_boundarySequence_tendsto_zero` |
| Eventual emptiness at fixed negative depth | `originalTransfer_fixedNegativeSublevel_eventually_empty` |
| No common positive amplitude/depth | `originalTransfer_no_uniformPositiveAmplitude`, `originalTransfer_no_uniformNegativeMargin` |
| Unchanged AIG margin upper bound and limit | `originalNegativeMargin_le_explicitVolumeBound`, `originalNegativeMargin_tendsto_zero` |
| Joint half-Haar and amplitude statement | `originalHalfHaar_with_uniformly_small_transfer` |
| Explicit unchanged-beta0 bound | `originalFixedCoupling_transfer_abs_le_explicitVolumeBound` |

### What the result does and does not settle

AIT establishes decay of its particular rational Ward lower certificate.
That fact alone does not imply decay of the actual transfer image. AIU supplies
an independent actual-image upper bound from the original crossing partition
and source envelope, then obtains the fixed-coupling uniform-volume conclusion.

For this original unnormalized transfer/source family at fixed positive beta,
the amplitude obstruction is explicit: a volume-uniform positive negative
depth is impossible.

No conclusion is supplied about arbitrary volume-dependent couplings,
normalized transfers, arbitrary source families, an operator-norm limit,
coercivity, negative operator eigenvalues, a Hamiltonian spectral gap, or the
continuum four-dimensional Yang--Mills mass gap. These questions require
their own objects, compatibility conditions, and proofs.


## 2．新規宣言と完全な公理出力監査

新規sourceは670行、35,359 bytes、32定理＋3スカラー定義である。すべての新規宣言について、次の完全修飾名前空間で `#print axioms` を1回ずつ置いた。

```text
MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint
```

以下では共通接頭辞 `p4Q2PZ37AIU_` を省略する。表の全35件を、sourceの宣言・出力命令・実公理出力の順序まで照合した。

| # | 種別 | 宣言suffix |
| --- | --- | --- |
| 1 | def | `originalPartitionDecayRate` |
| 2 | def | `explicitPartitionDecayRate` |
| 3 | theorem | `explicitPartitionDecayRate_nonneg` |
| 4 | theorem | `explicitPartitionDecayRate_pos` |
| 5 | theorem | `originalSingleLinkPartition_eq_exp_rate` |
| 6 | theorem | `originalPartitionDecayRate_pos` |
| 7 | theorem | `originalSingleLinkPartition_le_explicitRate` |
| 8 | theorem | `explicitPartitionDecayRate_le_original` |
| 9 | theorem | `originalPartitionDecayRate_nonneg` |
| 10 | theorem | `originalCrossingPartition_eq_exp_rate` |
| 11 | theorem | `originalCrossingPartition_le_explicitRate` |
| 12 | def | `originalTransferPartitionEnvelope` |
| 13 | theorem | `originalTransferPartitionEnvelope_pos` |
| 14 | theorem | `originalTransferPartitionEnvelope_eq_exp_rate` |
| 15 | theorem | `originalTransferPartitionEnvelope_le_explicitRate` |
| 16 | theorem | `originalCountExp_tendsto_zero` |
| 17 | theorem | `originalTransferPartitionEnvelope_tendsto_zero` |
| 18 | theorem | `originalNegativeMargin_le_explicitVolumeBound` |
| 19 | theorem | `originalNegativeMargin_tendsto_zero` |
| 20 | theorem | `originalSpatialHalfweight_le_one` |
| 21 | theorem | `originalCrossingKernel_leftHaarIntegral` |
| 22 | theorem | `originalLeftWeightedSource_abs_le_halfCount` |
| 23 | theorem | `originalRightWeightedTransfer_abs_le_crossingEnvelope` |
| 24 | theorem | `originalTransfer_abs_le_rightHalfweightCrossingEnvelope` |
| 25 | theorem | `originalTransfer_abs_le_crossingEnvelope` |
| 26 | theorem | `originalTransfer_abs_le_exactRate` |
| 27 | theorem | `originalTransfer_abs_le_explicitRate` |
| 28 | theorem | `originalTransfer_uniformly_small_eventually` |
| 29 | theorem | `originalTransfer_boundarySequence_tendsto_zero` |
| 30 | theorem | `originalTransfer_fixedNegativeSublevel_eventually_empty` |
| 31 | theorem | `originalTransfer_no_uniformPositiveAmplitude` |
| 32 | theorem | `originalTransfer_no_uniformNegativeMargin` |
| 33 | theorem | `originalHalfHaar_with_uniformly_small_transfer` |
| 34 | theorem | `originalFixedCoupling_explicitRate_ge_oneDiv384` |
| 35 | theorem | `originalFixedCoupling_transfer_abs_le_explicitVolumeBound` |

全35件の実出力は `propext`、`Classical.choice`、`Quot.sound` の標準3公理のみである。非標準公理、sorryAx、欠落、余分、重複はない。別jobのreceiptや独立の記録照合は、別のLean kernelによる独立再証明を意味しない。

## 3．依存構造と固定API

直接importsは以下の6件である。

```lean
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
```

AIFの元L²源に対する正確なtransfer積分恒等式と真正crossing Haar積分、AGNの元の連続源の絶対値上界、元の完全空間作用の非負性、元のkernelの対称性とAINの連続性・正性を接続する。左積分と右積分の向きは対称性によって明示的に一致させる。両端halfweightは、それぞれの作用非負性による評価まで保持される。

分配関数にはAIFの正値性と有限積、AIPの厳密欠損と元リンク数の一致、体積にはAIBの正確な立方計数を用いる。旧余裕はAIGの同じ定義であり、AISの元二次モーメント上界を用いてその消失を示す。AITの計数発散・二乗指数減衰極限・eventual半Haarを同じ固定結合で接続する。

固定mathlibの `Real.exp_log`、`Real.log_neg`、`Real.exp_nat_mul`、`Real.add_one_le_exp`、`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`、`norm_integral_le_of_norm_le`、`Filter.eventually_atTop`、`gt_mem_nhds`、挟み撃ち極限、`Set.eq_empty_iff_forall_notMem` の使用署名を原定義に照合した。全依存ソースを人手で再読したという意味ではなく、使用する署名の読解と、依存閉包の機械的型検査を区別する。

正本baseで再観測した主な依存blobは以下である。共通ディレクトリは `MGAP4D/MathlibAnalytic/`。

| 依存source | Git blob |
| --- | --- |
| `PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF.lean` | `a3a0899a9688479e49b605c0051cb5050f489d89` |
| `PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP.lean` | `49004405b63265db818d6e08acd8c85617e9393a` |
| `PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG.lean` | `21512d119a2b9dd87a5ad4ea90d3595f80b20e40` |
| `PhysicalYangMillsWilsonSU2OriginalRationalWardGrowingHalfHaarV5_PZ37AIT.lean` | `10d079143870929f2df37a18a2703a94a78c300e` |
| `PhysicalYangMillsWilsonSU2OriginalWardCrossingHalfHaarUnitCouplingV5_PZ37AIS.lean` | `178365b8b478b4bd49b73429ccea8958103e2467` |
| `PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN.lean` | `3362e7d97b663feab065e5aaf1907e99e4fc3c05` |
| `PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN.lean` | `00afd9f819da0ec2c9ceaf074a54ee73aa36454e` |
| `PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB.lean` | `3da94b4d2ef9a4b4bc4777c854d64ec9eba819d1` |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer.lean` | `4ba2fe9712c364429ec5e4bf88d6e7aa7bcc0fe9` |
| `PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel.lean` | `c398b45389f8e8c72c02ce17780e1e86210f8cbb` |

| 項目 | 固定値 |
| --- | --- |
| Lean | `v4.30.0-rc2` |
| mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| maxHeartbeats | `3900000` |
| synthInstance.maxHeartbeats | `1050000` |
| lean-toolchain Git blob | `6c7e31fffe3e03be3e0d7021acd9cd848e44db26` |
| lake-manifest.json Git blob | `01260678b674ab241e753563e913c7ce9c6ba659` |
| CI workflow Git blob | `4efb6399db1e4f3817c79f78a8d1338ea1c24c70` |

固定環境・workflow・既存仮定を変更していない。Lakeによる依存を含む検査が認証主体であり、CIの重複した直接elaborationは既存設定の `LEAN_FAST_DIRECT_ELAB=false` のままである。Strict Leanを省略する設定変更はない。

## 4．Exact-source認証、定理squash、統合後push

| 対象 | 実観測値 |
| --- | --- |
| Canonical base | `ef4fc8c592898a513e8abc9bbff6b269e43768bd` |
| 認証source HEAD | `90dde3aa09fc52af3c30ef69238578b1cf4d9235` |
| PR実checkout／test-merge HEAD | `5c180963e9cd05961ff527138588ade1a5e3337a` |
| 実際の定理squash | `ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e` |
| source／test-merge／squash共通Git tree | `18b2c818e2266ca590ffd484498e4f1964959e78` |
| 新規Lean共通Git blob | `84b59eb50635e2eba29834927ac2f032492e1219` |
| 新規Lean SHA256 | `cbd9b0340816c1586ac13398e60a9f7291958213631164ecb4f7dd5f85a71666` |

統合前sourceと実test-merge、統合後の実squashをそれぞれ取得した。共通treeとLean全文・blobは一致し、squashの唯一の親は開始時canonical baseであった。統合直後のformal refが実squashへ進んだことを再観測した。後続の文書専用commitのtreeを、上記の定理共通treeと同一視しない。

| 検証 | Exact-source PR | 統合後push |
| --- | --- | --- |
| Run | [#42559591642](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42559591642/attempts/1)、completed／SUCCESS | [#42560361781](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/42560361781/attempts/1)、completed／SUCCESS |
| 対象SHA | `90dde3aa09fc52af3c30ef69238578b1cf4d9235` | `ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e` |
| 実checkout | `5c180963e9cd05961ff527138588ade1a5e3337a` | `ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e` |
| 主job／必須Lean step 17 | `128972855964`、ともにSUCCESS | `128975214561`、ともにSUCCESS |
| 依存閉包 | 11409／11409 SUCCESS | 11409／11409 SUCCESS |
| 新規leaf | ℹ [11409/11409] Built MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU (8.2s) | ℹ [11409/11409] Built MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU (13s) |
| 実公理出力 | 35／35、標準3公理のみ | 35／35、標準3公理のみ |
| 欠落／余分／重複／非標準公理 | 0／0／0／0 | 0／0／0／0 |
| 全実ログのsorryAx／Lean error | 0／0 | 0／0 |
| 変更Lean warning／error | 0／0 | 0／0 |
| 独立receipt job／step 2 | `128974305870`、ともにSUCCESS | `128976889758`、ともにSUCCESS |
| exact-SHA status ID | `58393096764`、SUCCESS | `58393430736`、SUCCESS |
| check suite／check runs | `115277471562`、SUCCESS／2件SUCCESS | `115279407345`、SUCCESS／2件SUCCESS |
| 完了主ログの取得・公理照合 | 全文3,415,272文字、35／35一致 | 全文3,419,782文字、35／35一致 |
| 診断artifact ID | `13649291101` | `13649033684` |
| 実ZIP bytes | 133,696 | 134,062 |
| 実ZIP SHA256 | `3d227d05b24faeb9c66ed7d829a0a5c4d2a696d46c0d6e8be92504b07ab6f22b` | `a9d417be36a597bd7fb53d40c0f4ea659855893969418f04fd53b74451d67c6b` |
| 抽出実ログ bytes | 1,976,996 | 1,980,750 |
| 抽出実ログ SHA256 | `7f18e2f6b8a416cbcb9d794156c23e9c0b6610066fa9ccba2275b300b6ccc905` | `2e446c6d12f0b4bb788bb4c45e1bb206705d7c194fb90de316fc75ac50147f47` |

両runで、主jobだけでなく全workflowの完了、必須Lean step 17、独立receipt jobとそのstep 2、exact-SHA commit status、2件のcheck runsを確認した。receipt実ログの識別行は以下である。

```text
[mcp-receipt] event=pull_request exact_sha=90dde3aa09fc52af3c30ef69238578b1cf4d9235 source_result=success run=42559591642 attempt=1
[mcp-receipt] event=push exact_sha=ac30f9db7932c94f5a2cb82fd6d1998102cf0c4e source_result=success run=42560361781 attempt=1
```

主担当は完了後の主ジョブログ全文と、診断artifactの実ZIP bytesを取得した。実ZIPのSHA256をGitHub artifact metadataのdigestと一致させ、抽出した `lean-fast.log` の実公理出力35件を全宣言に一対一で照合した。主ジョブログでは各行のtimestamp接頭辞を除いてから複数行の公理集合を解析し、artifact実ログと同じ35件・同じ標準公理集合であることを確認した。

変更Lean warning 0は、既存依存ファイルから再生されるwarningまで全件0という主張ではない。公理監査では今回追加した35宣言の依存公理を調べ、主ログ・artifactとも全Lean errorとsorryAxの不存在を別に確認した。artifact名やSUCCESSというmetadataだけで実ログの代わりとはしていない。

## 5．作成・レビュー・試行履歴

開始時にGitHub MCPでformal/mainのHEAD、AITの3件のMERGED PR、未統合PR、正本treeを再観測した。正本treeは9,070 entriesでtruncatedではなく、AGENTS.mdはなかった。18件の未統合PRは以前の別作業であり、AIUの並行PRはなかった。

新規性レビューでは、正本の `PhysicalYangMillsWilsonSU2Original*.lean` 288ファイルを取得・宣言索引化し、関連する旧正規化・作用素冪の5ファイルも確認した。調査したfamilyの固定正結合での実際の源像の体積極限は、AITの補助床極限や旧定理の固定H・結合極限、体積依存結合の対角構成と区別された。リポジトリ全体の全定理に対する意味的非同値性を網羅的に証明したという主張ではない。

初期の局所草稿では、固定API照合によりSetの空集合補題名を `Set.eq_empty_iff_forall_notMem` に合わせた。全文の独立レビューは匿名 `noncomputable section` の終了 `end` 欠落を検出し、PR作成前に補った。修正後の670行全文を再レビューし、物理対象、両端halfweight、Hの引数scope、dependent boundary、量化、三つのcutoffの最大値による同時成立、固定結合の有理定数を確認した。これらはCI前の静的修正であり、失敗したLean実行とは記録しない。

初回のExact-source CI #42559591642は、workflow・必須Lean step・独立receiptを含めすべてSUCCESSで完了し、実ログでも変更warning/errorが0であった。PR sourceを修正するCI再試行はなく、初回sourceをそのままsquashした。統合後の自動push CIについては、上記の別欄に実ログ・全公理出力・receiptの観測結果を記録する。ローカルLean実行を行ったという主張はない。

## 6．未証明の課題と文書同期

今回認証された障害は、元の非正規化transferと一つの元の物理源からなるfamilyの、固定正結合での絶対振幅・負値深さについてのものである。正規化後のtransfer、別の源族、作用素ノルム、coercivity一般の不可能性には昇格しない。各有限Hで負の境界があることと、固定した正の深さでは十分大きいHに証人がなくなることは両立する。

各固定有限Hにおける任意正結合での元の全余裕半Haar下界、正規化因子を含む比較、共通の極限作用素への接続、作用素の負固有値、Hamiltonian spectral gap、連続体4次元Yang–Mills mass gapは、対応する証明が得られるまで未認証として残す。任意の体積依存結合に対する一様結論も含まない。

次段AIVでは、この実際の源像の減衰を踏まえ、元の真正分配関数・正規化因子との相対評価、または各固定Hで残る大きい正結合の全余裕負領域評価を検討する。これは研究候補であって、本記録に追加の証明を記載したものではない。元の物理対象を変更せず、局所的な評価を未証明の作用素・連続体結論へ貼り合わせない。

正式記録とREADME・ROADMAPは文書専用PRで追加し、既存README・ROADMAPの全文prefixを各branchで保持して末尾に追記する。文書専用変更でStrict Leanを手動起動しない。mainにはformalの正式記録と同一のGit blobをミラーする。mainの自動workflowは文書ミラー後の状態の検査であり、formalのExact-source定理認証を置き換えない。
