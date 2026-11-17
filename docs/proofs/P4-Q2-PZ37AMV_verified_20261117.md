# P4-Q2-PZ37AMV — true finite-volume normalized Wilson one-slab is not the identity

Date: 2026-11-17 JST. Canonical authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`; separately maintained `main` documentation mirror.

## Exact original-model scope

- Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; append-only / tighten-only / overwrite-forbidden / same-root.
- Genuine finite even-periodic SU(2) physical spatial-slice Gauss-law Hilbert carrier, genuine normalized Wilson one-slab operator, and **complete** original physical eigenvalue-one top eigenspace. The existing model's plaquette action, Haar, beta0, Gauss law, AJA budget, normalization, and abstract positive-time OS semigroup are not changed.
- From the independently push-certified AMU theorem, for each `H` and `beta≥0` there is an actual unit physical Gauss-law state in the original normalized Wilson one-slab top eigenspace orthogonal complement. Separately, the existing `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one` gives a strict norm bound on exactly this complement, using original physical Wilson data.
- One additive proof file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalNormalizedOneSlabNonidentityV5_PZ37AMV.lean`, 127 final source lines, certified source blob SHA `7952192202834cced60504ec73667da0f6e3f5e7`.

## Three exact-source Lean-certified theorems

1. `p4Q2PZ37AMV_exists_originalPhysical_unit_strict_oneSlab_contraction`: constructs a genuine original physical `u` with `‖u‖=1` and `‖T_normalized u‖<1`, using AMU's unit witness, exact restricted/ambient transport and existing physical strict contraction. No abstract witness hypothesis.
2. `p4Q2PZ37AMV_exists_originalPhysical_unit_nonfixed_oneSlab`: for the same finite original Wilson model, a unit Gauss-law physical vector exists with `T_normalized u ≠ u`.
3. `p4Q2PZ37AMV_originalPhysical_normalized_oneSlab_ne_identity`: the actual normalized Wilson one-slab continuous linear operator on the full physical Gauss-law Hilbert carrier is not the identity, for all finite `H` and `beta≥0`.

These are **not** statements about the independent AMR identity OS semigroup or a hypothetical identification of that semigroup with Wilson time evolution.

## Exact-source failed elaboration and corrected source (append-only provenance)

- First AMV source HEAD `b09ba22e67a4ff66bd6e4cb5122334a4307388e2`; [CI #44015151522](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44015151522), required Lean step **FAILURE**. Exactly one direct source error at line 59:38: `failed to synthesize NormedSpace ℝ ↥K`, where `K` is the actual top-orthogonal submodule and the source attempted `R.le_opNorm w`. Three ensuing `#print axioms` outputs included `sorryAx` because the upstream declaration did not elaborate, not because the target theorem was certified.
- Structural cause: the pinned Lean4/Mathlib context cannot reconstruct the subtype normed-space instance required at the direct method call. The existing canonical `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay.lean` explicitly proves a generic ambient-Hilbert bound `realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le` to avoid this failure.
- Minimal same-PR repair: import that already compiled source and instantiate its existing norm inequality at `n=1`, using `pow_one` and the exact symmetric physical normalized Wilson operator. Original theorem statements, witness, beta range and physical model are unchanged.
- Final corrected source HEAD `5f005bb555132e0c0033fdcc5f80b2a35bb5100c`. Final certified source blob `7952192202834cced60504ec73667da0f6e3f5e7`.

## Exact-source independent proof authentication

- [AMV theorem PR #6827](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6827) **MERGED**.
- [Exact-source PR CI #44016119489](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44016119489), event `pull_request`, exact HEAD `5f005bb555132e0c0033fdcc5f80b2a35bb5100c`, workflow completed/SUCCESS, mandatory Lean job `133814345815` and `Run changed Lean fast check` step completed/SUCCESS.
- Decoded Lean log: **Build completed successfully (8831 jobs).** Three new theorem `#print axioms` audits use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; changed-source warning/error `0/0`.
- Independent exact-source completion receipt job `133815237803` completed/SUCCESS: `[mcp-receipt] event=pull_request exact_sha=5f005bb555132e0c0033fdcc5f80b2a35bb5100c source_result=success run=44016119489 attempt=1`.
- Exact-source tree, actual PR test-merge tree and actual Formal merged Git tree all **`48b976dfa811003f551dcd5c737fb8403078fe06`**.
- Formal theorem merge HEAD **`e6d54aa613c9535f456ad50b3baf3b30be148309`**.

## Independent canonical push — separate pending checkpoint

- [Postmerge push CI #44016487023](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44016487023), event `push`, exactly `head_sha=e6d54aa613c9535f456ad50b3baf3b30be148309`.
- At record drafting, workflow `in_progress`: this does **not** constitute a successful independent canonical push certificate. Append the exact later workflow/job/required Lean step/log and receipt as a separate dated section, without changing this earlier observation.

## Remaining model-facing seams — unproved

The AMR abstract identity OS semigroup `C_id.translate t=identity` is one permitted algebraic/contractive control and remains distinct from the genuine nonidentity normalized Wilson transfer just proved. There is **no contradiction** until a typed model-specific one-slab operator identification and actual common OS boundary carrier realization have been proved.

In particular the arbitrary physical Gauss-law state built by AMU/AMV has not been proven to arise from the same positive-time OS canonical boundary moment with the required reflection, time-calibration, normalization and physical endpoint compatibility. No physical Wilson/OS complete one-slab identification and no continuum 4D Yang–Mills mass gap is certified.

This is a docs-only record; **do not run Strict Lean**.

## 2026-11-17 JST append-only postmerge independent push certification

The earlier `in_progress` checkpoint above is preserved. A subsequent independent GitHub MCP reobservation now establishes canonical-push completion on the exact merged source state:

- [Independent Formal canonical push CI #44016487023](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44016487023): event `push`, exact `head_sha=e6d54aa613c9535f456ad50b3baf3b30be148309`, attempt 1, workflow **completed/SUCCESS**.
- Mandatory Lean job `133815551202` and `Run changed Lean fast check` step: both completed/SUCCESS.
- Full decoded Lean job log: `Build completed successfully (8831 jobs).`; AMV three explicit theorem axiom prints use only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`. AMV source-direct warning/error `0/0`.
- Independent completion receipt job `133816447364` completed/SUCCESS, actual emitted receipt: `[mcp-receipt] event=push exact_sha=e6d54aa613c9535f456ad50b3baf3b30be148309 source_result=success run=44016487023 attempt=1`.
- Source-certified HEAD `5f005bb555132e0c0033fdcc5f80b2a35bb5100c`, test-merge and canonical Formal integrated Git trees all agree at `48b976dfa811003f551dcd5c737fb8403078fe06`.

**Certification state:** FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED for the three AMV source-scoped physical Wilson nonidentity declarations. The model-specific OS–Wilson one-slab intertwining, actual compatible OS boundary realization and continuum mass gap remain unproved.

This is a docs-only append. No Strict Lean is requested or required.
