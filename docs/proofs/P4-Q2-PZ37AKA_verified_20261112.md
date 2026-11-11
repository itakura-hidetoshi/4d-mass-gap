# P4-Q2-PZ37AKA — original second-power Haar–Cauchy floor

2026年11月12日 JST。これは固定Lean4カーネルで機械検証した定理の説明記録であり、文章そのものは形式証明ではない。

## 1. Source of authority and exact certification

- Repository: `itakura-hidetoshi/4d-mass-gap`; canonical theorem branch `formal/real-hilbert-uniform-coercive-strong-limit`. `main` is a documentation mirror only.
- [Theorem PR #6656](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6656): MERGED. Exact certified source HEAD `9265a9ef537d6a5e8898181af8098ac523587e95`, formal squash HEAD `7baa491a509eeda8d1e0b46fa68f8c1018992485`.
- [Exact-source CI #43011969101](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43011969101) `event=pull_request`, `completed/SUCCESS`, changed-Lean job and actual Lean step `completed/SUCCESS`, full dependency closure **11,441/11,441**. Independent completion receipt job `completed/SUCCESS`; exact-source commit status `chatgpt-ci-receipt/PR Lean Fast Check` success.
- Seven new declarations, seven individual `#print axioms`: solely `propext`, `Classical.choice`, `Quot.sound`; new `sorryAx` absent; changed AKA warning/error 0/0.
- Source, GitHub test-merge, and formal squash Git tree are identical: `d27a22ad4d545799804c2c4d025b7954c3504011`. Only one new Lean leaf (259 lines), no existing file changed/deleted.
- New leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalSecondPowerHaarCauchyFloorV5_PZ37AKA.lean`; direct imports AJZ, Mathlib Projection.Basic, Mathlib.Tactic. Fixed Lean `v4.30.0-rc2`; fixed mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Formal post-merge independent [push CI #43046698800](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43046698800): **in_progress at initial documentation audit**. This is not a completed push certification; append an independently reobserved receipt after completion.

## 2. Proven claims and exact scope

For every fixed finite spatial slice `H : ℕ` and `β>0`, reuse without modification the original physical SU(2) normalized Wilson one-slab operator `S`, centered signed ZW source `f₀`, genuine Haar variance `V=‖f₀‖²>0`, and original AJA negative-margin Haar certificate

```
B = m² * Measure.real(μ_H)({u < -m}) > 0.
```

The original transfer is symmetric; therefore, in its actual real Hilbert space,

```
(‖S f₀‖²)² ≤ ‖f₀‖² * ‖S² f₀‖² = V * ‖S² f₀‖².
```

The existing original AJA inequality `B≤‖Sf₀‖²` and AJR's exact variance identity give the **unconditional actual Wilson second-power floor**

```
0 < B² / V ≤ ‖S² f₀‖².
```

AJX's `B≤V/16`, together with `B,V>0`, separately implies `B²/V<B`. Thus the lower bound itself cannot rule out the n=2 strict AJA budget condition. **Only if** the real strict witness `‖S²f₀‖²<B` is separately proved does the exact interval follow:

```
B²/V ≤ ‖S² f₀‖² < B.
```

The conditional interval is a theorem, **not** an unconditional n=2 witness. No top rank-one assumption, invented spectral gap, or volume-uniform estimate is used.

## 3. Seven verified Lean declarations

1. `realHilbert_symmetric_secondPower_normSq_Cauchy_aka`
2. `realHilbert_oneStep_margin_secondPower_Cauchy_aka`
3. `GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_mul_variance_ge_AJA_sq`
4. `GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_ge_AJA_square_div_variance`
5. `GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_pos`
6. `GroundStatePosteriorJoint.p4Q2PZ37AKA_originalAJA_square_div_variance_lt_AJA`
7. `GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_AJA_witness_interval`

All names above are within `MGAP4D.MathlibAnalytic`. The seven `#print axioms` output lines, full dependency build, and independent receipt are in the exact-source CI log.

## 4. The remaining obstruction (NO_DATA)

An actual upper estimate `‖S² f₀‖²<B`, a numerical full-top projection bound, and any original finite-power AJA witness remain unproved. AJZ's full-top/orthogonal-tail equivalence is unchanged; AKA is an independent genuine **lower** bound only. Top one-dimensionality, `H`-uniform coercivity, Hamiltonian gap, and four-dimensional continuum Yang–Mills mass gap are **OPEN**. Do not upgrade an interval's nonemptiness to an actually realized witness.

Append-only / tighten-only / overwrite-forbidden / same-root. Original Wilson/Haar/ZW/AJA quantities, existing hypotheses and theorem statements, and pinned environment remain unchanged.
