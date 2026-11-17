# P4-Q2-PZ37AMR — actual identity control within the abstract Wilson OS semigroup interface

2026-11-17 JST. Formal proof record for the **scoped nonuniqueness/control obstruction**. Not an identification of the physically normalized one-slab Wilson transfer with any abstract positive-time semigroup. Not a continuum mass-gap theorem.

## Original source and pinned environment

- Repository `itakura-hidetoshi/4d-mass-gap`. Authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is a documentation mirror.
- Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original finite even-periodic SU(N) Wilson Gibbs coherent positive-half pullback `Q` and reflection invariance `hInvariant`, as in AMQ. Neither `Q` nor the existing physical Wilson kernel, Haar, Gauss-law, beta0, AJA or normalization are altered.
- New additive Lean file `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2CompletedOSAbstractOneStepIdentityControlV5_PZ37AMR.lean` (181 source lines, 3 printed-axiom declarations).

## Mathematical theorem scope

For arbitrary allowed finite Wilson OS data `Q` and `hInvariant`, the published structure `PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily` is satisfied by **identity translation on positive-time observables**

```text
C_id.translate(t) = AlgHom.id R D.positiveTimeSubalgebra
```

for every `t : NNReal`. The semigroup law is definitional and `osQuadratic_translate_le` is equality, since the translated carrier equals the original carrier. The construction does not assert that this identity is the physical Wilson transfer.

For every scale `n`, transfer time `t`, and actual OS carrier observable `F`, let `m_F` be its canonical shared-boundary Haar L2 moment. Then the **completed** OS boundary transfer satisfies

```text
completedBoundaryTransfer(Q, hInvariant, C_id, n, t)(m_F) = m_F.
```

Consequently, for every ambient boundary-Haar L2 test `z`,

```text
inner_real(completedBoundaryTransfer(Q,hInvariant,C_id,n,t)(m_F),z)
    = inner_real(m_F,z).
```

This identity is on actual canonical boundary moments. The completed boundary operator may project onto the OS image outside that subspace; no ambient identity operator is asserted.

Lean declarations:
1. `p4Q2PZ37AMR_identityAbstractOSSemigroup` — explicitly constructs a genuine `C_id` satisfying all existing algebra/contractivity fields.
2. `p4Q2PZ37AMR_identityAbstractOS_completedBoundary_apply_canonicalMoment` — fixed canonical moment, every nonnegative time.
3. `p4Q2PZ37AMR_identityAbstractOS_completedBoundary_inner_canonicalMoment` — arbitrary-test scalar coefficient.

## Source-level independent Lean certification

- Research PR [#6820](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6820).
- Exact certified source HEAD `98f0eb5be0a6a05842e5c8edf60eb1de0f120b72`.
- [PR exact-source CI #43949005729](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43949005729), event `pull_request`, workflow **completed/SUCCESS**.
- Required Lean job `133586173194`, mandatory `Run changed Lean fast check` step **completed/SUCCESS**.
- Full decoded Lean log: **11,494/11,494** dependency-aware Lake build, AMR local warning/error **0/0**. Each of three `#print axioms` prints only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Independent exact-source completion receipt job `133722141946` **completed/SUCCESS**, with observed text:

  ```text
  [mcp-receipt] event=pull_request exact_sha=98f0eb5be0a6a05842e5c8edf60eb1de0f120b72 source_result=success run=43949005729 attempt=1
  ```

- Exact source HEAD Git tree `7fae131f00a2512195a9e9daff6125b86e986957` equals PR test-merge `105f8a2b787cc3d6ad1ebbc17c5c2d8600c2e3dd` tree.
- Formal theorem PR **MERGED** with merge commit `30551be0570d66e63c03b2ac04b4f7552fcf97bb`. The AMR Lean file blob in canonical Formal is **exactly** the source-certified blob `4e6f03d14f22190f9fa98d80831e026aeb581c26`. The total Formal merge Git tree differs from the source/test-merge tree because Formal concurrently received a *docs-only* AMQ record #6819, not because of a changed AMR Lean file.

## Later independent canonical push reobservation — pending

- Exact Formal theorem merge HEAD `30551be0570d66e63c03b2ac04b4f7552fcf97bb`.
- [Independent canonical push CI #43989916990](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43989916990) initially observed `in_progress` at record creation.
- **No assertion yet** that the postmerge push required Lean step, workflow or exact-merge-HEAD completion receipt succeeded. Append a later separately dated reobservation before merging this record to Formal.

## What is still not proved (obstruction retained)

The AMQ finite Wilson Gibbs equality and the AMR abstract identity control are both scoped theorems; the source hypotheses do **not** determine which abstract OS translation `C.translate 1` matches the positive Haar-averaging **physical normalized Wilson one-slab operator**. This is a representation/selection obstruction, *not* a proof of physical inconsistency or a no-go theorem for a correctly constructed transfer.

Independently, the original physical normalized transfer `T_H` has a proved strict contraction on the orthogonal complement `E_H` of its full top eigenspace (`periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one`). If there exists `v ≠ 0` in this physical complement then `T_H v ≠ v`. However the norm inequality alone does **not** construct such a nonzero physical `v`; and an OS positive-time canonical moment representing the same `v`, with compatible time/normalization, is not established by the identity-control construction.

For genuine OS–Wilson four-Haar gluing one must independently prove:
1. Nonzero physical Gauss-law excitation in the original model at the target `H, beta0` and its typed OS carrier realization, not a surjectivity assumption.
2. Exact model-interpolated reflected positive-time observable `Theta(translate_1 F)*G` to temporal-gauge path readout with boundary order, gauge-fixing and wraparound controlled.
3. The Markov/Fubini path integral and its inward-message readout match arbitrary physical endpoint `f,g` and arbitrary pair-Haar test `z`, including `||P_H||^-2`.
4. Physical one-step time calibration; `C.translate 1 = R.positiveTranslation n 1` is currently an unproved optional seam, not the answer.

The existing proven full finite Wilson path identity `periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_pairTransferOperator_inner` has a **specific inward Wilson message**, not arbitrary AMP endpoints. No continuum four-dimensional Yang–Mills mass gap is claimed.
