# P4-Q2-PZ37ALD — authentic full Wilson one-slab pair-Laplace physical norm floor

2026-11-13 JST. Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
[ALD theorem PR #6734](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6734) **MERGED**.

## Scope and original-model definition compatibility

One new append-only Lean4 module `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFullKernelPairLaplaceNormV5_PZ37ALD.lean` (240 added lines; nine audited declarations). All prior Lean4 files, the original SU(2) Wilson spatial action/relative crossing and full one-slab kernels, both original spatial halfweights, Gauss-law ZW centered physical source and its continuous Haar representative, original product Haar, original physical transfer operator, AJA event and margin, full-top projection, coupling `beta0=log(3/2)/64`, original period H, toolchain pins and canonical root remain unchanged.

AGN previously certified exactly `f_H(A)=(W_H(A)-p_H)/2`. ALD confirms pointwise
`K_full,H(beta,A,B) = exp(-beta*p_H)*K_cross,H(beta,A,B)*exp(-beta*(f_H(A)+f_H(B)))`.
It then uses the true product-Haar integration and ALB's original pair-Laplace `Lpair_H(beta,t)` to prove the EXACT identity
`∫_{A,B} K_full,H(beta,A,B) d(mu_H×mu_H) = exp(-beta*p_H) * Lpair_H(beta,-beta)`.
No replacement of the full Wilson transfer by a new source model occurs.

AIW's authenticated original physical constant-vector matrix coefficient and genuine norm comparison ensure
`exp(-beta*p_H)*Lpair_H(beta,-beta) <= ||P_H(beta)||` at `beta>=0`.
ALC's certified quadratic Haar moment lower bound gives the new true original physical bound
`exp(-beta*p_H)*(Z_cross,H(beta) + (beta^2/4)*M2pair_H(beta)) <= ||P_H(beta)||`.
ALD also proves the original H22 form, the EXACT beta0 specialization with p22=292008, and a strict improvement over AIW **conditional** on positive `M2pair_H(beta)` at beta>0.

## Nine Lean4 declarations and kernel audit

1. `p4Q2PZ37ALD_originalWilsonAction_eq_centeredSource`
2. `p4Q2PZ37ALD_originalFullKernel_eq_pairLaplaceIntegrand`
3. `p4Q2PZ37ALD_originalFullKernel_pairHaar_eq_originalLaplace`
4. `p4Q2PZ37ALD_originalPhysicalConstantExpectation_eq_laplace`
5. `p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace`
6. `p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_quadraticMoment`
7. `p4Q2PZ37ALD_originalH22_physicalNorm_ge_quadraticMoment`
8. `p4Q2PZ37ALD_originalH22_fixedCoupling_physicalNorm_floor`
9. `p4Q2PZ37ALD_originalPhysicalNorm_strictly_gt_spatialMean_of_M2_pos`

## Exact-source CI and squash provenance

- Authenticated PR exact source HEAD: `8ec67a50d8b0ee3b9a447ac2f423099921a65d38`.
- [Actual exact-source CI #43408076701](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43408076701) **completed/SUCCESS**. Pinned Lean v4.30.0-rc2 and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Dependency closure **11,466/11,466**; all nine `#print axioms` evaluated to the standard three `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx`; new ALD warning/error **0/0**.
- Changed-Lean job `131827269339` completed SUCCESS, independent completion receipt job `131829406486` completed SUCCESS and logged:
  `[mcp-receipt] event=pull_request exact_sha=8ec67a50d8b0ee3b9a447ac2f423099921a65d38 source_result=success run=43408076701 attempt=1`.
- Source Git tree, tested PR merge tree, canonical formal squash tree all EXACTLY `7d1d9304e0e9da0712c6bfea6c183b52aa5d8f9e`, directly fetched from Git objects. Canonical formal theorem squash: `4683de2e6aeffbbb26baa58d7b87d8eeb669a1a1`.

## Independent formal push — historical pending checkpoint

Canonical formal [push CI #43408865099](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43408865099), keyed to `4683de2e6aeffbbb26baa58d7b87d8eeb669a1a1`, was initially **in_progress**, so its exact-head completion receipt and final outcome remain PENDING in this initial snapshot. Append an independently verified completed outcome once observed; never retroactively replace the pending observation.

## Open mathematical obligations

The new quadratic correction `M2pair_H(beta)` has certified nonnegativity, but **no unconditional strictly positive numerical floor** in ALD. Proving exact original crossing-weighted second source moment via AIF/AIU Haar marginal invariance and AHR's original source-crossing orthogonality, then pairing AHN's positive source variance, is a mathematically motivated NEXT step, not yet machine certified in this record.

The actual original H22 Haar-negative-region upper mass `r22 <= 4*exp(-(44/351)*beta0^2*292008)`, about 0.920418, is still **NO_DATA**; AKY's complementary cells remain conditional. H>=25 is an obstruction for the OLD AKX sufficient scalar premise only, NOT for every future norm-based criterion or a proof of AJA witness existence. H-uniform coercivity, physical Hamiltonian gap and continuum Yang--Mills 4D mass gap remain OPEN.

Append-only / tighten-only / overwrite-forbidden / same-root.


## Compatibility obstruction for the proposed next second-moment descent

The preceding exploratory note about AHR is **not** a proof of exact pair-Haar factorization. Source inspection confirms AHR's `p4Q2PZ37AHR_originalCrossingCorrelation_zero` is the identity `∫ f_H(A)*C_cross,H(A,B) dmu_H(A)=0` for the original **crossing action** `C_cross,H`, whereas ALD/ALC use the exponential **crossing kernel** `K_cross,H(beta,A,B)=exp(-beta*C_cross,H(A,B))`. Orthogonality against the linear crossing action does not imply orthogonality against its exponential. In particular no `M2pair_H(beta)=2*V_H*Zcross_H(beta)` equality is established, and it MUST NOT be assumed.

A more reliable next task is a separately proven uniform strictly positive lower bound for the *actual* crossing kernel on the finite compact product SU(2) configuration space, combined with the independently certified AHN positive original source second Haar moment and exact original Haar centering. Only after proving the required integrability, measure-preserving or product-Haar compatibility and lower-kernel inequality may one infer a strictly positive original `M2pair_H(beta)`. Any quantitative bound remains NO_DATA until its Lean CI succeeds.
