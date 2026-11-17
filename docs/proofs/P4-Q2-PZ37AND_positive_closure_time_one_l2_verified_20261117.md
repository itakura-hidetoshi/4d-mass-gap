# P4-Q2-PZ37AND — nonzero real L2 state of the genuine periodic positive closure

Date: 2026-11-17 JST. Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root.

## Certified statement and exact scope

For each finite lattice parameter H, beta >= 0, and the original nontrivial SU(2) carrier, let muPlus be the pushforward of the unchanged normalized full-periodic Wilson Gibbs probability under the original boundary/positive-open-half restriction. Let F be ANC's literal time-one two-mode Wilson cylinder on that positive closure.

AND proves that muPlus is a probability, that every such F has its inherited pointwise finite bound and belongs to MemLp 2, and constructs its real L2 class with exactly F as the almost-everywhere representative. For the coefficients supplied by ANC, this L2 class is nonzero. Thus there exist c0, c1 and psi in Lp R 2 muPlus with psi != 0 and psi = F almost everywhere. The same coefficients define a top-eigenspace-orthogonal vector in the ORIGINAL physical one-slab Hilbert space; no transfer of that orthogonality to Gibbs L2 or the OS quotient is asserted.

The measure is not replaced by ANA's separately normalized temporal-gauge half-path probability. No existing Wilson action, Haar measure, partition function, theorem statement, pin or workflow was modified.

## Five audited theorems

One additive Lean file (194 lines):
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureTimeOneL2V5_PZ37AND.lean`.

1. `p4Q2PZ37AND_originalPeriodicPositiveClosure_isProbabilityMeasure`.
2. `p4Q2PZ37AND_timeOnePositiveClosureObservable_norm_le`.
3. `p4Q2PZ37AND_truePeriodicTimeOnePositiveClosure_memLp`.
4. `p4Q2PZ37AND_truePeriodicTimeOnePositiveClosureL2_coeFn`.
5. `p4Q2PZ37AND_exists_nonzero_truePeriodicPositiveClosureTimeOneL2`.

The probability proof uses the existing original Gibbs mass-one theorem and an explicitly typed `Measure.map_apply (mu := originalGibbs)` calculation (Lean parameter spelling is `μ`). The remaining proofs use ANC measurability/nonzero, ANA's unchanged pointwise bound, `MemLp.of_bound`, `MemLp.toLp`, and `Lp.coeFn_zero`.

## Same-PR failure and repair history (not overwritten)

All candidates were kept within [PR #6858](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6858).

- Initial source `7523f01f1cbfef678b27c6873213e0139b0760a3`, [CI 44064732251](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44064732251), required job `133975346470`, failed at line 80:8: source Gibbs `IsProbabilityMeasure` instance could not be synthesized for `Measure.isProbabilityMeasure_map`. Artifact `14319846881` was downloaded and inspected.
- Second source `8a9a9f06e18aef1019533539d9570083087bd878`, [CI 44066630921](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44066630921), job `133981857108`, added the existing probability theorem as a local `letI`, but the same synthesis failure remained at line 86:8. Artifact `14321320805` was inspected. This attempted repair was not successful.
- Third source `763eeec81b7431f12a73963d9b6ab7b9739c6c1d`, [CI 44067361765](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44067361765), job `133984392803`, obtained the explicit original mass-one equality but failed at line 88:6 when rewriting `map_apply_of_aemeasurable`: the displayed pattern contained unresolved source measure `?m.119` and did not match the target. Artifact `14320942801` was inspected.
- Final source `6d44b68e7f56af2c03c629e4ca8cf9fb677d1645` replaced the rewrite by a typed calculation with the exact source measure supplied to `Measure.map_apply`. All five theorem statements and hypotheses stayed unchanged. This candidate passed independent source and merged-push checks below.

The repository already contains a Gibbs probability theorem AND a specialized instance. The first failures therefore are not evidence of absent mathematical normalization. A detailed instance-synthesis trace was not collected; the deeper search-path explanation remains a hypothesis. Failed candidates' downstream `sorryAx` outputs were elaboration artifacts and were never accepted as proofs.

## Exact source, test-merge and actual Formal tree

- Base Formal HEAD: `bbc57ebf207d051103066620ce22269f1a71958e`.
- Certified source HEAD: `6d44b68e7f56af2c03c629e4ca8cf9fb677d1645`.
- Certified Lean blob: `fff9d90688f2714ea4c211214e5752583ed820ab`.
- Test-merge commit: `b744b0ac941a507f7f9a4e6caaa57c4a8ec13a42`.
- Actual Formal squash HEAD: `64b023cf5fb8cd6bb85b8f53988f64e1ff189d73`.
- Source / test-merge / actual squash Git trees are identical: `5005128d2c082399ee9a988c4c3b5e66a358450f`.
- Theorem PR #6858 MERGED with the exact expected source SHA.

## Independent exact-source verification

[CI 44068323375](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44068323375), event `pull_request`, attempt 1, exact source `6d44b68e7f56af2c03c629e4ca8cf9fb677d1645`: workflow, required job `133987725888`, and `Run changed Lean fast check` step completed/SUCCESS. Actual artifact `14320629531` reports `Build completed successfully (8859 jobs).` All five AND axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; changed-file warnings/errors 0/0.

Source artifact SHA256: `bc75aa3e2066d077b4b6f4d7ef2da0ea19bdffcc36afd3b3b8738d09de2f708c`.

Separate receipt job `133989325368` completed/SUCCESS:

```text
[mcp-receipt] event=pull_request exact_sha=6d44b68e7f56af2c03c629e4ca8cf9fb677d1645 source_result=success run=44068323375 attempt=1
```

## Independent canonical push verification

[CI 44069041571](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44069041571), event `push`, attempt 1, exact Formal merge `64b023cf5fb8cd6bb85b8f53988f64e1ff189d73`: workflow, required job `133990201540`, and `Run changed Lean fast check` step completed/SUCCESS. Its separately downloaded artifact `14321737397` reports `Build completed successfully (8859 jobs).` Five AND audits again contain only the standard three axioms; no `sorryAx`; changed-file warnings/errors 0/0.

Push artifact SHA256: `4706f158c23326a698a64e5ba9f2c18c4d33e487d54631253f68a6e7d1e9e5fd`.

Separate receipt job `133991686085` completed/SUCCESS:

```text
[mcp-receipt] event=push exact_sha=64b023cf5fb8cd6bb85b8f53988f64e1ff189d73 source_result=success run=44069041571 attempt=1
```

Status: **FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, restricted to these finite-volume genuine periodic positive-closure L2 statements. Dependency replay warnings outside the changed AND file are not asserted to be zero.

## Execution provenance and remaining barriers

KuuOS CodeAI runtime and Lean MCP loop sources were inspected, but CodeAI synthesis, standalone direct Lean and Lean MCP were **NOT_RUN** in this conversation. No executable Lean/Lake or connected execution route was obtained in the working environment. Actual machine verification used the repository's pinned GitHub Actions Lean jobs, with GitHub MCP observation and artifact/receipt inspection. This operational limitation must not be described as successful CodeAI/Lean-MCP execution.

Ordinary Gibbs L2 nonzero does not by itself prove that the observable survives the reflection-positive OS null quotient. A typed bounded-continuous positive-time realization, the relevant OS seminorm/nondegeneracy, genuine one-slab/completed-OS intertwining, volume-uniform spectral estimates, and continuum four-dimensional Yang-Mills construction remain unproved by AND. The existing negative-half-independent observable reconstruction theorem is a possible next bridge, not an already certified application to this witness.

Documentation-only record. No manual Strict Lean rerun is requested for this record or its byte-identical main mirror. Existing README/ROADMAP contents are left unchanged in this documentation unit.
