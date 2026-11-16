# P4-Q2-PZ37AME — certified real shared-link SU(2) plaquette pair and full interacting Wilson Gibbs covariance identity

Date: 2026-11-16 JST. Authoritative Formal theorem [PR #6782](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6782) **MERGED**, canonical two-parent merge commit `021deafa6aada17ab0cc43fcb360fcba5de2b710`.

## Actual mathematical result, with exact scope

New append-only Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalInteractingSharedLinkPlaquetteCovarianceV5_PZ37AME.lean`.

The source extends, without modifying, the **genuine four-link canonical spatial SU(2) plaquette** from AMB/AMC/AMD and proves that its first-axis unit translated plaquette is **different** and shares **at least one genuine physical lattice link**. The theorem `periodicHypercubicPlaquetteAdjacent_shift_first` from the exact finite incidence geometry supplies this link witness at every even periodic physical length `n=2(H+1)>=2`. At the smallest torus `H=0` this does not assert exactly one shared link. Neither a surrogate independent-plaquette law nor a generated independent Wilson group variable is substituted.

For actual full finite-volume Wilson Gibbs measure `mu_{H,beta}` and character `chi=1-E`, the leaf defines the two-observable real connected correlation for those actual adjacent plaquettes:

```text
Cov_Gibbs(H,beta;p,q)
  = ∫ chi(hol_p(A)) * chi(hol_q(A)) d mu_Gibbs(A)
    - (∫ chi(hol_p(A)) d mu_Gibbs(A))
      * (∫ chi(hol_q(A)) d mu_Gibbs(A)).
```

It proves for arbitrary real observables `f,g` the **exact Gibbs/complete-Haar-density identity**

```text
Cov_Gibbs(f,g)
  = ∫ [exp(-beta*S_H(A))/Z_H] f(A)g(A) d mu_Haar(A)
    - (∫ [exp(-beta*S_H(A))/Z_H] f(A) d mu_Haar(A))
      * (∫ [exp(-beta*S_H(A))/Z_H] g(A) d mu_Haar(A)),
Z_H = ∫ exp(-beta*S_H(A)) d mu_Haar(A) > 0.
```

Here `S_H` contains **ALL physical plaquettes**, with their shared links and interactions. The full-volume `Z_H` remains present in every moment, as opposed to the ABN/AMD one-plaquette Haar partition mass. This is an algebraic equality for the **true interacting Wilson law**, not a claimed nontrivial estimate of `Cov_Gibbs(H,beta;p,q)`.

**No H-independent cluster-decay constant, no neighbor-pair sign/strictness, no transfer norm contraction or uniform physical beta0 gap follows from this equality alone.** The original `beta0=log(3/2)/64` and SU(2) Wilson action, fixed Haar, Gauss/AJA, original physical transfer, Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, roots and existing proof files were not altered.

## Seven-declaration pinned Lean audit

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, prefix `p4Q2PZ37AME_`:

1. `originalPrimarySharedLinkNeighbor`
2. `originalPrimarySharedLinkNeighbor_adjacent`
3. `originalPrimarySharedLinkNeighbor_physicalEdge`
4. `originalPrimaryNeighborGibbsConnected`
5. `actualWilsonGibbsIntegral_eq_fullHaarDensity`
6. `actualWilsonGibbsConnected_eq_fullHaarDensity`
7. `originalFiniteWilsonPartition_pos`

## Actual version-bound repair trajectory — no false initial certification

- Canonical pre-AME Formal HEAD `d5e7d27bb165982987e3a6c6e942d175446ebf8b`; unchanged main reference at start `cc703d03bac0ca018ea5d23b1b9fe192cafb8238`.
- Initial new source `2f1fda5fa028c4c83fe425ea3ac3cf984c5a0f89`, [PR exact-head CI #43778845941](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43778845941) **completed/FAILURE**. Full Lean elaboration diagnosed **three direct errors**: line 35 `NeZero` goal remained in normalized half-cylinder notation after `simp`; line 74 `omega` could not normalize the even side length without explicitly `change` to arithmetic `2*(H+1)`; line 120 density-weighted Haar formula still used unfolded integral `∫exp` vs named full Wilson `partitionFunction`. Initial `#print axioms` displayed `sorryAx` on unclosed declarations via error recovery. **Do not treat initial source as certified.**
- Proof-only repair `d1ecfde018be0954083bb5064ebbd1c3180132e5` replaces those tactics with `change 2 * (H+1) ≠ 0; omega`, `change 2 ≤ 2 * (H+1); omega`, and `simp only [smul_eq_mul, CompactOrientedGaugeWilsonSystem.partitionFunction]`. No theorem signature, assumptions, physical definitions, pinned imports or coefficients were weakened.
- Independent [exact-head PR Lean CI #43779493581](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43779493581) **workflow completed/SUCCESS**, pinned dependency build **11,466/11,466**, all seven `#print axioms` only `propext` / `Classical.choice` / `Quot.sound`, no `sorryAx`, direct AME warnings/errors **0/0**. Main Lean job `133013221215` and independent receipt job `133014715880` both **completed/SUCCESS**. Actual receipt `event=pull_request exact_sha=d1ecfde018be0954083bb5064ebbd1c3180132e5 source_result=success run=43779493581 attempt=1`.
- Source commit `d1ecfde018be0954083bb5064ebbd1c3180132e5`, synthetic test-merge commit `2297624b04bbdb5de13bf87080ed74ac8ae3b5e3`, and actual canonical Formal merge commit `021deafa6aada17ab0cc43fcb360fcba5de2b710` all have Git tree `a1f8192db3ca8c0313e45620358f6daf293087e9`. Actual canonical merge parents are pre-AME Formal `d5e7d27bb165982987e3a6c6e942d175446ebf8b` and the exact certified repaired source `d1ecfde018be0954083bb5064ebbd1c3180132e5`.
- Distinct postmerge [canonical event=push CI #43780128247](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43780128247) on **actual integrated commit `021deafa6aada17ab0cc43fcb360fcba5de2b710`** was independently observed `in_progress`. This is an **historical observation**, not a success claim: record its eventual result separately after actual workflow, Lean job, required step and exact-head receipt complete.

CodeAI/standalone Lean MCP execution receipt: **NO_DATA** in this session. The machine checker actually observed is GitHub Actions with pinned Lean; never claim an unavailable CodeAI service ran.

## Next independent physical obstruction — AMF/next

Use true adjacent shared-link Wilson Gibbs pair to derive a **nontrivial, explicit bound** on the full Gibbs connected correlation that is uniform in physical volume, without assuming plaquette independence. If a cluster expansion / conditional-link influence certificate is needed, derive it from the original SU(2) Haar/Wilson action and local interaction incidence, do not insert a free-standing hypothesis and report it as a proof. Next verify summability in lattice separation, compatibility with the physical Gauss-law Hilbert carrier, and a valid link to original one-slab transfer bounds/cross-H uniformity.

**OPEN/NO_DATA:** physical fixed-beta0 all-volume transfer gap, Hamiltonian mass gap, continuum four-dimensional Yang–Mills mass gap. Neither AMD's positive single-plaquette Haar covariance nor this AME exact two-plaquette Gibbs identity establishes them.
