# P4-Q2-PZ37AMP — actual full two-ended original SU2 Wilson one-slab four-Haar coefficient

Date 2026-11-16 JST. This is an original finite Wilson/Haar **physical one-slab integral theorem** with three independently source-certified Lean declarations; no assertion that a separately constructed completed OS boundary operator acts by this kernel.

## Canonical model and source

- Repository: `itakura-hidetoshi/4d-mass-gap`. Authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is a docs mirror.
- Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original `SU(2)` at fixed positive `beta0 = log(3/2)/64`, original compact spatial-slice Haar probability measure `mu_H`, original Wilson temporal-gauge one-slab kernel `K_Wilson,H,beta(A,B)`, the exact physical Gauss-law `L²` sector `G_H`, original `P_H,beta` and normalized physical one-slab operator `P_hat_H,beta` defined with its existing factor `||P_H,beta||^-1`; no Wilson action, plaquettes, Gauss law, Haar, AJA, source root, or transfer was changed.
- New additive proof file `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0FullPairFourHaarV5_PZ37AMP.lean`, **269 lines in the verified source**, three actual theorem declarations and three `#print axioms`.
- Distinguish from AMJ/AMK/AML static interacting Gibbs covariance, which is *not* OS time, and from AMN's finite-order periodic **deterministic** configuration shift, which is *not* the positive Haar-averaging physical one-slab transfer.

## Mathematical statement — original model rather than a formal operator alias

For any two independent, arbitrary Gauss-law physical spatial states `f,g ∈ G_H` and every arbitrary, possibly nondecomposable ordered pair-Haar `L²` test vector `z`, prove the **genuine four-Haar coefficient** of the physical double-ended one-step transfer:

```text
  inner_real( (P_hat f) tensor (P_hat g), z )
     = ||P||^(-2) * ∫_{C ~ mu_H} ∫_{B ~ mu_H}
         inner_real( z(B,C),
           (∫_{A ~ mu_H} f(A)*K_Wilson(A,B)) *
           (∫_{D ~ mu_H} g(D)*K_Wilson(D,C)) ).
```

The input is a tensor of two arbitrary physical states; **no decomposition or density premise** is placed on the test `z`. The normalization is a **square** of the original actual physical transfer norm because both endpoints evolve, unlike AMO's one-sided top-mode triple-Haar statement.

Three new Lean declarations:
1. `MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_fourHaar`: genuine ambient pair-Haar Wilson operator on any decomposable input, arbitrary `z`, equals the original fourfold Haar integral. This follows from the preexisting **vector-level** `periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_apply_externalTensor`, true one-slab fiber integral `periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn`, and `realL2HilbertSchmidtKernelPairing_eq_integral_integral_of_representatives`.
2. `MGAP4D.MathlibAnalytic.periodicHypercubicEvenSpecialUnitaryPhysicalPairBothOneStep_inner_eq_fourHaar`: both endpoints are genuine Gauss-invariant physical vectors acted upon by normalized original Wilson one-slab transfer, with exact `||P||^-2`.
3. `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMP_originalFixedBeta0PhysicalPairBothOneStep_inner_eq_fourHaar`: exact SU2 original fixed `beta0` specialization. No new physical rate, compatibility, scale-uniformity or gap assumption.

## Version-bound failure/repaired Lean record — append-only

First exact-source commit `b88d7244a9b57a6bd2ad891f294b86544f701c8d`, [CI #43869530270](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43869530270) **required Lean step FAILURE**. Downloaded complete GitHub `lean-fast-check-log` artifact `14227950493` and inspected 2,208,682-byte `lean-fast.log`. The **single direct changed-file error** was line 212:6: `No goals to be solved`. The preceding `rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_inner_externalTensor_eq_fourHaar ...]` already closed the `calc` equality, and the following `rfl` therefore had no goal. The three partial axiom prints contained only standard three axioms; the initial failed source is nevertheless **NOT certified**. This is a Lean elaboration sequencing error, not a counterexample to the physical integral identity.

Repair preserved all three theorem statements, original exact Wilson kernel, coupling, physical normalization, and dependencies. Removed only the unnecessary trailing `rfl` after that complete `rw`, source HEAD `7c3c64cd8c1eca22bc260538cbf74ff5478853fc`. The typed failure and exact version provenance were appended in [PR #6815](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6815), comment `6916963023`. No duplicate red PR was introduced.

## Independently source-certified, tree-matched

- [Repaired exact-source CI #43870614121](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43870614121): `event=pull_request`, `head_sha=7c3c64cd8c1eca22bc260538cbf74ff5478853fc`, **workflow completed/SUCCESS**.
- Changed Lean job `133310479192` and mandatory `Run changed Lean fast check` step **completed/SUCCESS**; pinned dependency-aware build **11,491/11,491**. Full exact-source GitHub Actions `lean-fast.log` artifact `14227063830` confirms **3/3** `#print axioms`, each only `propext`, `Classical.choice`, `Quot.sound`; **no `sorryAx`**; direct AMP warning/error **0/0**. No existing unrelated import warnings are conflated with AMP.
- Independent exact-source completion receipt job `133313314407` **completed/SUCCESS**, emitted:

```text
[mcp-receipt] event=pull_request exact_sha=7c3c64cd8c1eca22bc260538cbf74ff5478853fc source_result=success run=43870614121 attempt=1
```

- Actual Formal two-parent theorem merge `d6ab7a593c70e5db73b6bfd19627a32d407e7cb1` has parents previous Formal `3a3ccfe948b747a4fa2754f5a0ceb264d352fe9b` and exact source `7c3c64cd8c1eca22bc260538cbf74ff5478853fc`.
- Exact source, GitHub test-merge `ec46cac7974ee8b781edf5dbf3c79c100a01d4aa`, and actual canonical theorem merge Git tree are identical: `b92a3708ab86b1d25fad8f24dac084a28e9e8769`.
- Independent canonical [event=push CI #43871520062](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43871520062) was initially `in_progress` against the actual merged theorem HEAD `d6ab7a593c70e5db73b6bfd19627a32d407e7cb1`. This historical observation remains; only separately reobserved workflow/job/required Lean step, 3/3 axioms and distinct exact-HEAD completion receipt may certify it. Append any later actual result in another section without overwriting.

## Exact scope and next unresolved OS seam

The original completed boundary-OS pair weak intertwining predicate
`PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.CompletedBoundaryTransferOneSlabPairWeakIntertwiningAt`
still demands, for all `f,g,z`, equality between the completed boundary time-`2` coefficient and the genuine both-endpoint one-slab pair coefficient. AMP has proved **the true Wilson side** of that equality as four Haar integrals, not the OS side. Showing those four-Haar coefficients actually equal the separately defined OS operator requires finite model-facing Markov/Fubini + correct physical time-scaling + source observational range/descent compatibility, none of which is discharged merely by having the right-hand-side formula.

One should not replace this missing identity with AMN's finite-order periodic deterministic shift or postulate its vanishing defect. True Haar one-slab physical transfer spectral bounds uniform in H and the continuum four-dimensional Yang–Mills mass gap remain **unproved / OPEN / NO_DATA**.
