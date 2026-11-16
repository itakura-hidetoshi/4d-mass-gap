# P4-Q2-PZ37AMQ — completed OS boundary coefficient as finite Wilson Gibbs integral

Date: 2026-11-17 JST. **Source-verified Lean4 finite OS-side coefficient theorems**, not a proof of the full OS–Wilson one-slab intertwining. Canonical authoritative branch: \`formal/real-hilbert-uniform-coercive-strong-limit\`; \`main\` is a documentation mirror only.

## Pin, original model, and exact proof scope

- Lean: \`v4.30.0-rc2\`; mathlib: \`5450b53e5ddc75d46418fabb605edbf36bd0beb6\`.
- Same-root periodic lattice \`PeriodicHypercubicEvenSideLength (halfExtent n)\`, original \`periodicHypercubicSpecialUnitaryWilsonSystem\`, original exact Gibbs measure and \`Q.interpolate n\`; no change to plaquettes, Wilson action, Haar, Gauss-law, AJA, beta or normalization.
- The theorems are parametrized by a coherent positive-time pullback \`Q\`, reflection invariance \`hInvariant\` and a contractive positive-time OS semigroup \`C\`. These inputs are **not** a proof that arbitrary physical endpoint vectors or normalized Wilson one-slab steps are realized by \`C.translate\`.
- Generic SU(N) / \`beta n\` results include a fixed SU(2) beta0 instance when supplied with the existing model-compatible Q/C data; **the new theorem statements do not independently construct a fixed-beta0 Q/C instance or identify them with the AMP transfer**.

## Mathematical result — OS side, on canonical positive-time carrier moments

For positive-time carrier observables \`F,G\` and their canonical boundary-Haar moments \`m_F, m_G\`, the original completed OS boundary-time-two transfer satisfies

\`\`\`text
  inner_real( K_OS(n,2) m_F, m_G )
     = B_OS,n( translate_1(F), G )
     = omega_n( Theta(translate_1 F) * G )
     = integral_{U ~ original periodic Wilson Gibbs(n,beta n)}
         [Theta(translate_1 F) * G](Q.interpolate n U).
\`\`\`

The convention \`K_OS(n,t) = J_n ◦ T_OS(n,t/2) ◦ J_n^{-1} ◦ P_range(J_n)\` implies \`t=2\` represents one unit of **OS observable time**, not a proof of conversion to physical continuum time. The final integral is the actual periodic Wilson Gibbs integral, **not** a four-Haar disintegration or equality with the separately defined positive Haar-averaging normalized Wilson operator.

Three Lean declarations:
1. \`p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_OSForm\`: completed boundary coefficient equals reflected positive-time OS bilinear coefficient.
2. \`p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_originalGibbs\`: for oriented physical embeddings \`E,Gauge,L\`, the same coefficient is an original oriented finite Wilson Gibbs integral. This is an additional model specialization, not the periodic identity itself.
3. \`p4Q2PZ37AMQ_completedBoundary_two_canonicalMoments_inner_eq_periodicWilsonGibbs\`: same-root periodic Wilson Gibbs integral using \`Q.approximatingMeasure_toMeasure_eq n\`, preserving actual Q/lattice/coupling.

Additive proof files:
- \`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0CompletedOSGibbsCoefficientV5_PZ37AMQ.lean\`.
- \`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2SameRootCompletedOSPeriodicGibbsCoefficientV5_PZ37AMQ.lean\`.

## Append-only version-bound failure and repair record

- First AMQ source \`6533526cf65be1e8c550272188f93621c6e73f09\`, followed by same-root addition \`2ec12215ff70646013127e5e69876ae3939fd2f5\`.
- Original exact-source [CI #43875960398](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43875960398) **completed/FAILURE**, required Lean job \`133329138613\`. Full decoded job log (4,080,918 characters) records one changed-source error: \`PhysicalYangMillsWilsonSU2OriginalFixedBeta0CompletedOSGibbsCoefficientV5_PZ37AMQ.lean:31:52\` unsolved \`NeZero\` goal \`¬periodicHypercubicEvenPositiveHalfCylinderSlabCount H = 0\`. This was a local elaboration/proof-completion error, not an integral identity counterexample.
- Existing certified AMP uses the explicit Lean arithmetic proof \`change 2 * (H + 1) ≠ 0; omega\`. The same proof was substituted locally in both AMQ files without changing theorem statements or any physical data. Repair commits \`062a6adbdf55c8a9086efeeba0b6fa06b17fe91f\` and \`bbe99206eed808c4d0d65b67c348033c8145bc55\`.
- Historical cancelled earlier run [#43874530923](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43874530923) is **not** counted as certification.

## Exact-source independent source certification

- Exact certified source HEAD: \`bbe99206eed808c4d0d65b67c348033c8145bc55\`.
- [Exact-source PR CI #43926337514](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43926337514): \`event=pull_request\`, workflow **completed/SUCCESS**.
- Required Lean job \`133506695490\`, required \`Run changed Lean fast check\` step: both **completed/SUCCESS**.
- Full decoded GitHub job log: **11,493/11,493** dependency-closed Lake build; three \`#print axioms\` outputs contain exactly \`propext\`, \`Classical.choice\`, \`Quot.sound\`; no \`sorryAx\`; direct AMQ source warning/error **0/0**.
- Independent exact-head completion receipt job \`133509791947\`: **completed/SUCCESS**, actual emitted text:

\`\`\`text
[mcp-receipt] event=pull_request exact_sha=bbe99206eed808c4d0d65b67c348033c8145bc55 source_result=success run=43926337514 attempt=1
\`\`\`

- Actual AMQ theorem [PR #6818](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6818) was **MERGED** by GitHub MCP, merge method \`merge\`, yielding canonical Formal theorem HEAD \`0198fa8571bd519b7f9102f8b2940e6ce57517c1\`. Exactly two parents: old Formal \`fc198afe16332232ae8ea8e9bdd98cf7dd699f75\` and certified source \`bbe99206eed808c4d0d65b67c348033c8145bc55\`.
- Certified source, GitHub test-merge \`0499a920b58e923808be6a61b24b0c4d1c60157e\`, and actual canonical Formal theorem merge have the **same Git tree**: \`b8d516795d4c342b1c0b27a6716d42892b91261a\`.

## Independent postmerge push reobservation

- [Canonical push CI #43927499955](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43927499955) on exact merge HEAD \`0198fa8571bd519b7f9102f8b2940e6ce57517c1\` initially observed \`in_progress\` at record drafting.
- **Pending independent final workflow/job/required step/receipt and logs**: this section is not an assertion of independent push certification. Append a new section with later exact-HEAD observations; do not reinterpret the earlier \`in_progress\` observation.

## Frontier / obstruction preserved

AMP #6815 independently proves the original fixed \`beta0=log(3/2)/64\` SU(2) normalized **physical two-ended pair** four-Haar coefficient for all physical Gauss-law \`f,g\` and arbitrary pair-Haar test \`z\`. AMQ independently proves the **completed OS boundary** coefficient on canonical moments as an original same-root finite Wilson Gibbs expectation.

The unresolved identification demands **new**, typed proofs, not an assumed bridge:
1. Represent relevant arbitrary Gauss-law endpoint tensors \`f⊗g\` by actual OS positive-time canonical moments or prove a sufficiently strong applicable image/density statement without making \`J_n\` onto by fiat.
2. Identify translated positive-time observable pullbacks \`Theta(translate_1 F)*G\` pointwise (or in the actual Gibbs integrals) with the real finite Wilson temporal-gauge path integrands; existing Markov/Fubini \`PositiveHalfTemporalGaugePath_integral_headTail\` and two-boundary \`PositiveHalfCylinderTemporalGaugePathKernel_eq_pairKernel_mul_interior\` are partial ingredients.
3. Verify reflection orientation, boundary order, pair-Haar normalization \`||P_H||^{-2}\`, positive-time semigroup **\`C.translate\`** versus the literal Wilson one-slab kernel, physical step-size calibration and no hidden wraparound.
4. Show equality against all required \`z\` and only then establish \`CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt\`. Do not treat conditional re-expression of the target as a proof.

In particular, \`C.translate\` is defined abstractly as an algebra endomorphism semigroup with OS contraction; existing Q's finite Gibbs pullback alone does not automatically identify it with the physical normalized one-slab Wilson transfer. Neither a static Gibbs covariance estimate nor AMN deterministic periodic shift can fill the gap. No continuum four-dimensional Yang–Mills mass gap is certified by AMQ.
