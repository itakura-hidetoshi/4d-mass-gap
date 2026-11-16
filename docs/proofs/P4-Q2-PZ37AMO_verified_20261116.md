# P4-Q2-PZ37AMO — actual original SU2 Wilson physical one-slab triple-Haar coefficient

Date: 2026-11-16 JST. This is an exact finite-model theorem from original physical Wilson, not a completed OS/continuum mass-gap assertion.

## Authoritative model

- Canonical theorem branch `formal/real-hilbert-uniform-coercive-strong-limit`, Lean `v4.30.0-rc2`, mathlib pin `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- The actual positive Haar-averaging one-slab Wilson kernel `K_Wilson,H,beta(A,B)`, exact spatial-slice compact-group Haar probability `mu_H`, genuine gauge-invariant `L²` physical Hilbert carrier, existing physical one-slab transfer `P_H,beta`, its normalization `P_H,beta / ||P_H,beta||`, the existing strictly positive top eigenvector `Omega_H,beta`, and the exact one-sided physical pair-Haar isometry `J_H,beta`. Nothing is changed in those original definitions.
- The original fixed SU2 coupling is exactly `p4Q2PZ37ADC_fixedCoupling = log(3/2)/64`; its original independently proved positivity provides the `hbeta` argument.
- The kernel `K_Wilson` is **not** the finite static connected Gibbs plaquette covariance kernel from AMJ/AMK/AML. Neither is it the finite-order deterministic configuration-translation action excluded by AMN. Original Wilson/Haar/Gauss-law/AJA and public roots are untouched.

## New kernel-checked Lean theorem (full physical sector and arbitrary pair test)

File: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0PhysicalOneSlabTripleHaarV5_PZ37AMO.lean`. New declarations: 2, new `#print axioms` commands: 2.

1. `MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_tripleHaar`, for every finite H, SU(N) rank N>0, nonnegative beta, any genuine Gauss-law physical `f` and any **arbitrary** ordered pair-Haar `L²` test `z`, proves exactly:

```text
  inner( J_H,beta (P_normalized f), z)
   = ||P_H,beta||^(-1) *
     integral_{C ~ mu_H} integral_{B ~ mu_H}
       inner_real( z(B,C),
         (integral_{A ~ mu_H} f(A)*K_Wilson,H,beta(A,B))
            * Omega_H,beta(C))
```

This is a **literal spatial three-Haar-integral coefficient** of the actual one-step Wilson transfer. It uses the previously independently proved normalized physical one-sided pair coefficient `periodicHypercubicEvenSpecialUnitaryOneSidedPhysicalPair_oneStep_inner_eq_rawKernel`, the true fiber-integral `periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn`, and the generic real Hilbert–Schmidt Fubini theorem `realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives`. Thus no arbitrary postulated integrability, test-tensor density or OS time gluing is required.
2. `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMO_originalFixedBeta0PhysicalOneSlab_oneStep_inner_eq_tripleHaar`: instantiate the same exact three-Haar integral for the actual original SU2 rank 2 and unchanged `beta0 = log(3/2)/64`, preserving the true physical top eigenmode.

These are not conditional physical OS gluing statements: the two theorems assert exact finite Wilson one-slab **matrix coefficient formulae** without introducing a new compatibility certificate. They do **not** assert that a separately specified completed OS boundary semigroup equals this operator.

## Exact-source independent CI

- [Theorem PR #6812](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6812) `MERGED`, source HEAD `aadb8407872722c31c1f8df9173198bf696be471`. No source amendment was necessary; the first candidate succeeded.
- [Exact-source CI #43865754292](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43865754292), `event=pull_request`, `head_sha=aadb8407872722c31c1f8df9173198bf696be471`, `workflow completed/SUCCESS`.
- Changed-Lean job `133293744396`, required step `Run changed Lean fast check` **completed/SUCCESS**. Actual dependency-checked build **11,490/11,490**; both AMO `#print axioms` outputs explicitly list only `propext`, `Classical.choice`, `Quot.sound` (2/2), no `sorryAx`, and **AMO direct warning/error 0/0**. Actual source `lean-fast.log` independently inspected from GitHub Actions artifact ID `14226445641`. Existing unrelated dependency warnings are not counted as AMO source warnings.
- Distinct independent completed/SUCCESS receipt job `133296358893` emitted:

```text
[mcp-receipt] event=pull_request exact_sha=aadb8407872722c31c1f8df9173198bf696be471 source_result=success run=43865754292 attempt=1
```

- The actual Formal two-parent theorem MERGE `2a8678ce835bb6bccdfeee7be107223b1bba253f` has parents `e5f4b96ee6239992dd9934914e809ef28037b978` (previous authoritative Formal) and the exact certified source `aadb8407872722c31c1f8df9173198bf696be471`.
- Exact source, test-merge `c02cea5f19f6b00396b6fb112e485a6527d7872c`, and actual canonical theorem merge have the exact matching Git tree `d2bf4eed0bc10a1a9b282e5f0e79a33afbcc6e47`.
- Distinct canonical independent [event=push CI #43866727941](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43866727941) started against the actual theorem merge HEAD. **Initial status in_progress.** This is a separate certification gate requiring actual workflow/job/required step/axiom outputs and independent exact-head receipt, not an inference from source CI; append its later outcome without altering this historical observation.

## Exact remaining obstruction and next objective

AMM already exposed an exact residual between the separately specified completed OS boundary time-one action and the genuinely realizable deterministic integer lattice-step pullback. AMN showed that a strict norm decay for that *periodic deterministic shift* would collapse nontrivial physical OS excitations. AMO has now put the *actual distinct Wilson positive Haar one-slab transfer* on the other side as a complete, concrete, three-Haar-integral coefficient for an arbitrary pair-Haar test.

The next model construction must use true finite Wilson Markov/Fubini conditional integration, on a certified class of positive-time physical observables, to identify the original **Haar-averaging one-slab transfer** with a correctly time-calibrated OS boundary action, and then independently prove density/range compatibility for the completed physical OS carrier. Neither the original `CommonSemigroupOneStepCoherentAt` deterministic periodic-shift identification nor a fake assumed zero residual can be substituted. Physical lattice spacing and scale-uniformity are separate constraints; original continuum 4D SU2 Yang–Mills mass gap remains **OPEN / NO_DATA**.

## Independent canonical push verification — later exact-HEAD observation

The preceding historical status of independent canonical event=push CI #43866727941 remains as originally observed; it is not overwritten. GitHub MCP subsequently observed that [run #43866727941](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43866727941), **event=push**, actual merged Formal theorem `head_sha=2a8678ce835bb6bccdfeee7be107223b1bba253f`, **workflow completed/SUCCESS**. Required changed-Lean job `133297064763` and `Run changed Lean fast check` step both **completed/SUCCESS**. Actual independent push-head Lean diagnostic `lean-fast.log` from GitHub Actions artifact ID `14226127795` confirms pinned dependency-checked build **11,490/11,490**, 2/2 AMO new theorem `#print axioms` prints only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, and AMO directly changed-file warning/error **0/0**.

Independent completion receipt job `133300621389` separately **completed/SUCCESS**, actual line:

```text
[mcp-receipt] event=push exact_sha=2a8678ce835bb6bccdfeee7be107223b1bba253f source_result=success run=43866727941 attempt=1
```

Source `aadb8407872722c31c1f8df9173198bf696be471`, test-merge `c02cea5f19f6b00396b6fb112e485a6527d7872c`, and canonical theorem integration `2a8678ce835bb6bccdfeee7be107223b1bba253f` share the same verified Git tree `d2bf4eed0bc10a1a9b282e5f0e79a33afbcc6e47`.

**Claim boundaries retained:** genuine Wilson finite physical one-slab triple-Haar coefficient certified; actual OS boundary identification, uniform volume scaling, Hamiltonian and continuum 4D Yang–Mills mass gap remain unproved.
