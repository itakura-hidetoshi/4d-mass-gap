# P4-Q2-PZ37AMM — actual Wilson/OS finite one-step raw-path kernel defect

2026-11-16 JST. Mathematical scope: **exact finite-source quantitative obstruction** between an OS completed semigroup and genuine realizable integer-one-step Wilson dynamics. It is **not** proof that the defect vanishes.

## Canonical setting

- Formal authority branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Original Wilson/Haar/Gauss/AJA and related finite models preserved.
- Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Source hypotheses retain the original existing `PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection`, coherent positive-time pullback, realizable integer-lattice temporal covariance, and common approximating OS semigroup interfaces. Their required existence/compatibility is **not** asserted unconditionally; notably the proof never assumes `CommonSemigroupOneStepCoherentAt` or `RealizableOneStepPhysicalTopRawKernelLimitAtFor`.
- The rectangular Gram kernel is constructed from the actual finite Wilson boundary/open-half Haar feature analysis. By the preexisting theorem `periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_eq_rawPath`, it has the original normalized unfixed finite Wilson raw-path kernel as its a.e. representative.
- One new additive Lean file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OneStepOSRawPathKernelDefectV5_PZ37AMM.lean`, three theorem declarations, three explicit `#print axioms` commands. No existing Wilson action, coupling, OS operator or mathlib API was changed.

## Certified theorem 1: physical Hilbert norm equality, no coherence assumption

For a genuine realizable OS carrier observable `F` at cutoff `n`, let `Jn` be the canonical completed physical-state-to-boundary Haar `L²` isometry, and `K_OS,n(2)` the completed boundary OS transfer at boundary time two (physical semigroup time one). Then the difference between its action on `Jn(physicalState F)` and the actually realizable integer lattice translation `Jn(physicalState(R_one F))` has **exactly the same norm** as the corresponding physical Hilbert discrepancy. This follows from the proved completed-boundary compression on the physical range and the genuine boundary isometry. There is no implicit zero-defect assumption and no claim of an all-scale gap.

`PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.completedBoundaryTransfer_two_realizableOneStep_defect_norm_eq`

## Certified theorem 2: exact rectangular raw-path coefficient defect

For the canonical physical model, arbitrary actual carrier `F` and any pair-Haar test `z`, write `uC` for its common-semigroup translated open-half `L²` vector at completed-boundary time two, `uR` for the actual realizable integer-one-step open-half `L²` vector, `K` for the already-constructed genuine Wilson rectangular Gram `L²` kernel, and `fz` for the boundary coordinate representation of `z`. The theorem proves the *literal nonzero-permitted defect identity*:

```text
  inner(pairIso(K_OS,n(2) canonicalBoundaryMoment(F)), z)
    - realL2HilbertSchmidtKernelPairing(K, fz, uR)
  = realL2HilbertSchmidtKernelPairing(K, fz, uC - uR).
```

The proof uses the exact actual boundary synthesis identity, the existing finite Wilson Hilbert–Schmidt pairing, and real linearity; no new Wilson Markov law, fake Haar covariance, or time-identification hypothesis is added. The existing a.e. raw-path representation identifies the specific physical kernel involved.

`PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection.canonicalRealizableOneStep_OS_rawPath_defect_eq_kernelPairing`

## Certified theorem 3: sharp norm error budget

The same difference obeys:

```text
  |defect(F,z)| <= norm(K) * norm(z) * norm(uC-uR)
```

by the actual Hilbert–Schmidt kernel Cauchy–Schwarz estimate and the exact pair/boundary Haar isometry.

`PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection.canonicalRealizableOneStep_OS_rawPath_defect_abs_le`

This is a quantitative usable bound, but it cannot force the right-hand side to zero. The **remaining substantive obstacle** is proving that the genuinely defined semigroup-positive-half and actual realizable Wilson-step open-half vectors are compatible (or their discrepancy tends to zero in a specified physical/scaling limit) and separately identifying the resulting literal one-slab kernel coefficient on physical top-mode boundary vectors.

## Initial source failure, retained as failure

- Initial source HEAD `54b0d28e1d8e19a522a65d8598e7b768ff65594b`, [exact PR CI #43856394163](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43856394163). Its required Lean step failed during elaboration of a **local geometry NeZero instance** at source line 40. The general `simp [PeriodicHypercubicEvenSideLength]` unexpectedly left an unmet `periodicHypercubicEvenPositiveHalfCylinderSlabCount H ≠ 0` goal, which did not follow by simplification. The initial run was subsequently cancelled after the update and is NOT a successful source. The three theorem bodies printed standard-three-only axioms but this did not certify the failed file.
- The structural failure was recorded append-only in [PR #6806](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6806) issue comment `6915052092`. The exact repair preserved all three theorem statements: replace only the local instance proof by `change 2 * (H + 1) ≠ 0; omega`, as established in the already pinned adjacent original physical lattice Lean modules.
- Repaired source HEAD `da7df6ff450cdfe3759d71c9a667929b842a4a24`. No new assumptions, weaker inequality, sorry, axioms or physics changes.

## Independently exact-source certified

- [Exact-source CI #43857347890](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43857347890), `event=pull_request`, `head_sha=da7df6ff450cdfe3759d71c9a667929b842a4a24`, **workflow completed/SUCCESS**.
- Changed Lean job `133264957622` and required `Run changed Lean fast check` step **completed/SUCCESS**, exact pinned dependency-aware build **8,710/8,710**.
- Three AMM declarations: **3/3** `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; AMM direct warning/error **0/0**. Unrelated existing imported warning lines are not attributed to AMM.
- Independent receipt job `133267447772` completed/SUCCESS, actual log line:
  ```text
  [mcp-receipt] event=pull_request exact_sha=da7df6ff450cdfe3759d71c9a667929b842a4a24 source_result=success run=43857347890 attempt=1
  ```
- Actual Formal theorem merge commit `7aed955a6533cdc106b40bf8808dd829402fed8a`, parents previous authoritative Formal HEAD `8308b35f9760ae2eaf2201a9a5bf36e368ceef1e` and exact repaired source HEAD `da7df6ff450cdfe3759d71c9a667929b842a4a24`.
- Source/test-merge `1310d7aee6651961504bc48314d9b72c85468f5d`/actual canonical theorem merge Git tree identical: `5643adbeca3fab65c82668b3f83266b4ff14e18e`.
- Independent [canonical push CI #43858181657](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43858181657) launched against the actual merged HEAD. Initially `in_progress`. Historical in-progress status is not promoted to SUCCESS without later exact-head workflow, job, required Lean step, three axiom outputs and independent completion receipt.

## Claim boundaries and next physical tasks

Finite Wilson physical-time one-slab pair-Haar operator and one-sided sector estimates already exist. AMM does **not** prove `CommonSemigroupOneStepCoherentAt`, `RealizableOneStepPhysicalTopRawKernelLimitAtFor`, the precise cross-H physical Hilbert compatibility, or a scale-uniform top-eigenspace ratio strictly below one. It also does **not** identify random-scan update count with OS time or establish the Hamiltonian or four-dimensional continuum Yang–Mills mass gap.

AMM supplies a concrete, auditable residual identity and sharp quantitative norm budget for the **actual** finite Wilson kernel under the stated canonical realization/semigroup interfaces. The first next task is to prove a non-assumed finite Wilson temporal Markov/Fubini identity that constrains `uC-uR` for a certified class of positive-time observables, then extend with an independently justified closure/density/descent argument. Neither KuuOS CodeAI execution nor standalone Lean-MCP proof execution is asserted without a corresponding receipt.
