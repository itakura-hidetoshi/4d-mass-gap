# P4-Q2-PZ37AMK — genuine original SU(2) Wilson Gibbs plaquette covariance Schur ℓ²

Date: 2026-11-16 JST. **Exact-source independently certified**; postmerge push evidence is a separate gate.

## Fixed canonical source, unchanged model

- Repository: `itakura-hidetoshi/4d-mass-gap`.
- Formal authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
- Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original full interacting finite SU(2) compact-Haar Wilson Gibbs law, fixed `beta0=log(3/2)/64`, with physical four-edge oriented plaquette fundamental characters `chi_p`.
- Existing Wilson/Haar/Gauss/AJA law, physical OS operators and toolchain were not changed; new Lean source is append-only.

## Actual mathematical theorem

For every finite physical volume `H>0`, every real weight function `a` on all actual physical plaquettes, and `rho0=18*periodicHypercubicSpecialUnitaryActiveTVMajorant(beta0)<1`:

```text
  SUM(p : ALL physical plaquettes)
    (SUM(q : ALL physical plaquettes)
      Cov_(actual Wilson Gibbs mu[H,beta0])(chi_q, chi_p) * a(q))^2
    <= (96/(1-rho0))^2 * SUM(q) a(q)^2.
```

The kernel is the *signed, actual Gibbs connected covariance* `K(p,q)=Cov(chi_q,chi_p)`, not a random-scan transition, a product-Haar surrogate, or a postulated covariance estimate. The resulting finite real ℓ² covariance operator is bounded uniformly in H by `96/(1-rho0)`.

## Proof-relevant dependency chain: three new declarations

1. `MGAP4D.MathlibAnalytic.finiteRealKernel_l2_sq_le_of_abs_row_column`: signed finite real Schur estimate; use `abs(K)`, actual finite row/column bounds, existing `FiniteNonnegativeSchur.row_action_sq_le`, Cauchy–Schwarz and finite double-sum interchange.
2. `MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_symm`: for the actual compact-Haar Gibbs integral, covariance symmetry is derived from integral multiplication commutativity and scalar Gibbs means, not assumed.
3. `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMK_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l2_sq_le`: specialize the generic signed Schur result using certified AMJ #6797 row bound `SUM(q) abs(Cov(chi_q,chi_p))<=96/(1-rho0)`; symmetry supplies the column bound. The strength, constant and original law are preserved.

One new source: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0GibbsCovarianceSchurL2V5_PZ37AMK.lean`; three new declarations and three explicit `#print axioms` audits. No `sorry` or new axioms.

## Exact-source GitHub Actions certification

- Theorem [PR #6800](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6800), source head `9242090554ab8ccddddea9a9760e85fc9e45d4de`; MERGED.
- [Exact-source PR CI #43846973063](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43846973063), event `pull_request`, workflow **completed/SUCCESS**; changed Lean job `133229474928`, required Lean step **completed/SUCCESS**.
- Pinned dependency build **11,514/11,514**; three new declarations **3/3**. Each actual `#print axioms` contains only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`; AMK direct warnings/errors **0/0**. Unrelated pre-existing dependency warnings are not reclassified as AMK errors.
- Independent exact-source receipt job `133233137878` **completed/SUCCESS**, output:
  ```text
  [mcp-receipt] event=pull_request exact_sha=9242090554ab8ccddddea9a9760e85fc9e45d4de source_result=success run=43846973063 attempt=1
  ```
- Actual Formal theorem merge commit `bcd4b548606b51d5e4336f2f06e370431ef98426` with two parents `3bfd523029f49b3196daaa9660e6a4bcf587e374` and exact source head `9242090554ab8ccddddea9a9760e85fc9e45d4de`.
- Git tree source = synthetic test-merge = actual Formal theorem merge: `20b5dc8aeb2209bf60f12abbe9de0b2d21c9e776`.
- Independent postmerge [event=push CI #43848369472](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43848369472) launched against the exact integrated Formal HEAD. The initial run state was **in_progress**, not a claim of successful postmerge verification. Append a later separate exact-HEAD observation only after workflow/job/required step and receipt succeed.

## Explicit open boundary

This establishes a finite-volume genuine Gibbs covariance **upper** bound on the plaquette ℓ² operator. It does NOT identify this kernel with physical Euclidean one-slab time transfer, prove OS transfer spectral gap, Gauss-law Hamiltonian spectral gap, all-distance clustering, varying-beta weak-coupling continuum reconstruction or the four-dimensional Yang–Mills mass gap.

The distinct currently unresolved physical gluing seam is witnessed in `PhysicalYangMillsWilsonSU2CompletedBoundaryTransferOneSlabIntertwining.lean`, where `CompletedBoundaryTransferOneSlabPairIntertwiningAt` is a structural physical-boundary/one-slab operator compatibility condition that must be established on the original gauge-invariant carrier, not inferred from a static covariance norm. KuuOS CodeAI or independent Lean-MCP execution is not claimed; this record certifies actual GitHub Actions Lean only.
