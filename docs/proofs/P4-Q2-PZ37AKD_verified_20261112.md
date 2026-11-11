# P4-Q2-PZ37AKD — original Wilson adjacent-power Haar retention ratio floor

2026年11月12日 JST。ここに記すのは固定Lean4で認証した真正定理の説明と実行時来歴であり、このMarkdown自身は証明ではない。

## 1. Canonical source, exact checks, independent post-merge push

- Repository: `itakura-hidetoshi/4d-mass-gap`; theorem canonical: `formal/real-hilbert-uniform-coercive-strong-limit`. `main`は文書の同一blobミラーであり、定理正本ではない。
- [AKD theorem PR #6665](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6665) **MERGED**。exact source HEAD `d4fd6295f23f77040296d10692cfaafe01026391`、exact-head squash `9f71815ec5df4336493f492b28f6d9108538b456`。
- [Exact-source CI #43112959710](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43112959710) は `event=pull_request`、`completed/SUCCESS`。changed Lean job・実Lean step とも `completed/SUCCESS`、dependency closure **11,444/11,444**。
- [Independent formal post-merge push CI #43114001431](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43114001431) は `event=push`、exact squash HEAD `9f71815ec5df4336493f492b28f6d9108538b456`、`completed/SUCCESS`。changed Lean job・実Lean step `completed/SUCCESS`、**11,444/11,444**。
- 両CIとも独立 `Publish MCP CI completion receipt` job `completed/SUCCESS`、`chatgpt-ci-receipt/PR Lean Fast Check` exact-head commit status `success`。受領書は別の形式証明ではなく、実行結果の証跡。
- 新規**7宣言／7個の独立 `#print axioms`**。実ログで各宣言の公理依存は `propext`, `Classical.choice`, `Quot.sound` のみ。追加 `sorryAx` なし、変更AKD leafの `error/warning` **0/0**。新規 `sorry`/`admit`/`axiom` なし。
- Source／GitHub test-merge／formal squashのGit treeは `a1f4842fea48791b75551b02c2d6640e295a7e6e` で完全一致。新規AKD Lean blob `54bb51de36ab7d4ce1d3972451cf0aff54ee6520`、1ファイル**282行追加**、旧Lean編集・削除0。
- 新規leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalAdjacentPowerHaarRatioFloorV5_PZ37AKD.lean`。直接imports: AKC、`Mathlib.Analysis.InnerProductSpace.Projection.Basic`、`Mathlib.Tactic`。固定 `leanprover/lean4:v4.30.0-rc2`、mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`。

## 2. Genuine finite-H mathematics and hypotheses

固定有限 `H : ℕ`、`β>0`。真正SU(2) Wilson正規化physical one-slab対称transferを `S`、元中心化ZW源を `f₀`、元の真正Haar分散を `V=‖f₀‖²>0`、元AJA真正Haar証明書を `B=m²·Measure.real(μ_H)({u<−m})>0` と置く。既存AJA証明 `B≤‖Sf₀‖²` を**同じH・β・元measure・source**で使用する。

`a_n=‖S^n f₀‖²` と定義する。AKCの固定済み対称Hilbert作用素Cauchy–Schwarzから `a_(n+1)²≤a_n*a_(n+2)` が全 `n` で成立。既存 `a₀=V>0`, `a₁≥B>0` から全 `a_n>0` と `a_n*a₁≤a_(n+1)*a₀` を得る。したがってLean4で以下を全自然数 `n` に形式認証した。

```
B * ‖S^n f₀‖² ≤ V * ‖S^(n+1) f₀‖²,
B / V ≤ ‖S^(n+1) f₀‖² / ‖S^n f₀‖².
```

さらに **`q*V<B` を仮定した場合に限り**、どの `n` に対しても `‖S^(n+1) f₀‖²≤q*‖S^n f₀‖²` は成り立たない、と形式認証。これは真正源orbitの有限H局所的な**下からの保持率障害**であり、作用素全体のノルム・スペクトルギャップ・指数減衰上界を意味しない。別系統AJXの真正 `B≤V/16` と矛盾しない。比率下界 `B/V` はH・βに依存する。

## 3. Seven certified theorem declarations

1. `real_positive_logConvex_sequence_margin_step_akd`
2. `real_positive_logConvex_sequence_margin_ratio_akd`
3. `real_positive_logConvex_sequence_no_subcritical_step_akd`
4. `GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_energy_pos`
5. `GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_HaarMargin_mul_energy_le_variance_next`
6. `GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_HaarMargin_div_variance_le_next_ratio`
7. `GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_no_subcritical_step_factor`

いずれも名前空間 `MGAP4D.MathlibAnalytic`。定理の厳密署名・公理依存については認証Lean leafを一次の権威とする。

## 4. OPEN (NO_DATA) and governance

真正Wilson有限冪の **厳密AJA上界** `‖S^n f₀‖²<B`、無条件 `n=2,n=3` 証人または不存在、真正全top射影の大きさとAJA予算の直接比較、top一次元性、H一様coercivity、Hamiltonian spectral gap、連続体4D Yang–Mills mass gapは依然**OPEN**。局所の正の保持率下界を一様ギャップ・上界・証人に昇格させない。

Append-only／tighten-only／overwrite-forbidden／same-root。元Wilson/Haar/ZW/AJAの量、定義、仮定、旧定理、公開rootとLean/mathlib pinを変えず、docs-only Strict Leanの手動実行は禁止。
