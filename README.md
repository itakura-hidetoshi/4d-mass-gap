# MGAP4D

MGAP4D is a Lean 4 repository for developing and checking the proof architecture of a normalized 4D mass gap theorem.

The repository is organized as a GitHub-native Lean project: the active source tree, CI, documentation, theorem-surface checkpoints, and migration history live directly in the repository.

## Current active Lean root

The current active Lean root is:

```text
MGAP4D.lean
```

It imports the current proof-hardening architecture, including:

```text
MGAP4D/Foundation
MGAP4D/Certificates
MGAP4D/Spectral
MGAP4D/Hamiltonian
MGAP4D/OSPositivity
MGAP4D/Plaquette
MGAP4D/Constructive
MGAP4D/Audit
MGAP4D/Release
MGAP4D/ProofHardening
MGAP4D/DependencyMap
MGAP4D/ReplacementCheckpoint
MGAP4D/ReplacementClosure
MGAP4D/ReplacementPass2
MGAP4D/ReplacementPass2Closure
MGAP4D/MathlibAdoptionGate
MGAP4D/PreMathlibClosure
MGAP4D/Phase3CandidateClosure
MGAP4D/Phase3CIConfirmationClosure
MGAP4D/PostMathlibHoldTheoremHardening
MGAP4D/R3R7RouteSpecificHardening
MGAP4D/R3R7ClosureCandidateSeriesReview
MGAP4D/R3R7TheoremRouteQueue
MGAP4D/R3R7HardeningPassSeriesReview
MGAP4D/PostHardeningPassClosure
MGAP4D/PostHardeningPassTighteningSegmentSelection
MGAP4D/R1--R7
MGAP4D/Global
MGAP4D/FinalSpine
```

## Phase 3 status

The current `main` branch is closed at a **R7 proof-obligation tightening closure checkpoint** after the R7 atom / exact-gap proof-obligation tightening pass series was observed green through CI.

The active proof-hardening route is:

```text
TheoremSurface
  -> Replacement pass 1
  -> Replacement pass 2
  -> Pass2Closure
  -> MathlibAdoptionGate
  -> MathlibRequestRegistry
  -> R1/R2/R3/R4/R5/R6/R7 theorem-candidate milestones
  -> Phase3CandidateClosure
  -> Phase3CIConfirmationClosure
  -> PreMathlibClosure
  -> R1--R7 scoped Mathlib dry-run series
  -> Mathlib main-adoption hold decision
  -> PostMathlibHoldTheoremHardening
  -> R3--R7 route-specific closure-candidate checkpoints
  -> R3--R7 theorem-route queue
  -> R3--R7 theorem-route hardening passes
  -> R3--R7 hardening pass series review
  -> PostHardeningPassClosure
  -> PostHardeningPassTighteningSegmentSelection
  -> R3 proof-obligation tightening closure
  -> R4 proof-obligation tightening closure
  -> R5 proof-obligation tightening closure
  -> R6 proof-obligation tightening closure
  -> R7 proof-obligation tightening pass 1
  -> R7 proof-obligation tightening pass 2
  -> R7 proof-obligation tightening pass 3
  -> R7 proof-obligation tightening series review
  -> R7 proof-obligation tightening closure
```

Important invariant:

```text
Mathlib is not yet introduced on main.
lakefile.lean is not modified for Mathlib.
No active main-branch Lean module imports Mathlib.
Public theorem claims remain review-gated.
R7 theorem completion is not claimed.
Final gap theorem release is not unlocked.
```

## R1--R7 theorem-candidate coverage

Phase 3 candidate preparation covers the full R1--R7 spine:

```text
R1 Hilbert path
R2 self-adjoint restriction path
R3 shifted-operator / zero-form route
R4 lower-bound path
R5 spectrum / infimum path
R6 interval-exclusion path
R7 atom / exact-gap path
```

R3 proof-obligation tightening is closed at the review-surface level:

```text
R3 proof-obligation tightening pass 1: CI green
R3 proof-obligation tightening pass 2: CI green
R3 proof-obligation tightening pass 3: CI green
R3 proof-obligation tightening series review: CI green
R3 proof-obligation tightening closure: CI green
```

R4 proof-obligation tightening is closed at the review-surface level:

```text
R4 proof-obligation tightening pass 1: CI green
R4 proof-obligation tightening pass 2: CI green
R4 proof-obligation tightening pass 3: CI green
R4 proof-obligation tightening series review: CI green
R4 proof-obligation tightening closure: CI green
```

R5 proof-obligation tightening is closed at the review-surface level:

```text
R5 proof-obligation tightening pass 1: CI green
R5 proof-obligation tightening pass 2: CI green
R5 proof-obligation tightening pass 3: CI green
R5 proof-obligation tightening series review: CI green
R5 proof-obligation tightening closure: CI green
```

R6 proof-obligation tightening is closed at the review-surface level:

```text
R6 proof-obligation tightening pass 1: CI green
R6 proof-obligation tightening pass 2: CI green
R6 proof-obligation tightening pass 3: CI green
R6 proof-obligation tightening series review: CI green
R6 proof-obligation tightening closure: CI green
```

R7 proof-obligation tightening is now closed at the review-surface level:

```text
R7 proof-obligation tightening pass 1: CI green
R7 proof-obligation tightening pass 2: CI green
R7 proof-obligation tightening pass 3: CI green
R7 proof-obligation tightening series review: CI green
R7 proof-obligation tightening closure: CI green
```

Earlier R3--R7 pass-level hardening surfaces remain green:

```text
R3 shifted / zero-form hardening pass: CI green
R4 lower-bound hardening pass: CI green
R5 spectrum / infimum hardening pass: CI green
R6 interval-exclusion hardening pass: CI green
R7 atom / exact-gap hardening pass: CI green
R3--R7 hardening pass series review: CI green
Post-hardening-pass closure: CI green
```

## CI confirmation

The latest closure CI recorded in the repository is:

```text
R7 proof-obligation tightening closure main CI:
Lean Direct Elan CI
Run ID: 25777833754
Build job ID: 75714049832
Commit: 0cd1419ace5c1c1266b79a3c012514f3f7ff6ebf
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

Earlier confirmed checkpoints include:

```text
PR #2 observation CI: success, closed unmerged
Manual main workflow_dispatch CI before confirmation closure: success
Post-Phase3CIConfirmationClosure manual main workflow_dispatch CI: success
R1--R7 scoped Mathlib dry-run series: success
Mathlib main-adoption hold decision: CI green
Post-Mathlib-hold theorem-route hardening: CI green
R3--R7 closure-candidate series review: CI green
R3--R7 theorem-route queue: CI green
R3--R7 hardening pass series review: CI green
Post-hardening-pass closure: CI green
R3 proof-obligation tightening closure: CI green
R4 proof-obligation tightening closure: CI green
R5 proof-obligation tightening closure: CI green
R6 proof-obligation tightening closure: CI green
R7 proof-obligation tightening closure: CI green
```

## Mathlib dry-run policy

Mathlib adoption may be tested only through scoped dry-run branches.

Dry-run success is accepted as contact-surface buildability only. It is not theorem completion and not permission to introduce Mathlib into `main`.

Relevant documents and modules:

```text
docs/phase3_pre_mathlib_closure_checkpoint.md
docs/phase3_mathlib_adoption_gate.md
docs/phase3_mathlib_request_registry.md
docs/phase3_mathlib_dry_run_result_ledger.md
docs/phase3_mathlib_main_adoption_hold_decision.md
docs/phase3_post_mathlib_hold_theorem_route_hardening_ci.md
docs/phase3_r3_r7_hardening_pass_series_review_ci.md
docs/phase3_post_hardening_pass_closure_ci.md
docs/phase3_r3_proof_obligation_tightening_closure_ci.md
docs/phase3_r4_proof_obligation_tightening_closure_ci.md
docs/phase3_r5_proof_obligation_tightening_closure_ci.md
docs/phase3_r6_proof_obligation_tightening_closure_ci.md
docs/phase3_r7_proof_obligation_tightening_closure_ci.md
MGAP4D/Phase3CandidateClosure.lean
MGAP4D/Phase3CIConfirmationClosure.lean
MGAP4D/PostMathlibHoldTheoremHardening.lean
MGAP4D/R3R7HardeningPassSeriesReview.lean
MGAP4D/PostHardeningPassClosure.lean
MGAP4D/R3/Theorem/R3ProofObligationTighteningClosure.lean
MGAP4D/R4/Theorem/LowerBoundProofObligationTighteningClosure.lean
MGAP4D/R5/Theorem/SpectrumInfimumProofObligationTighteningClosure.lean
MGAP4D/R6/Theorem/IntervalExclusionProofObligationTighteningClosure.lean
MGAP4D/R7/Theorem/AtomExactProofObligationTighteningClosure.lean
```

## Build

Install Lean through `elan`, then run:

```bash
lake update
lake build
```

For the full local audit sequence, run:

```bash
bash scripts/check.sh
```

The check script runs:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/replay_summary.py
lake update
lake build
```

GitHub Actions uses the workflow:

```text
Lean Direct Elan CI
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native project documentation and migration notes
maps/                    Lightweight source maps and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Migration and proof-hardening policy

The repository is populated and hardened in small, reviewable batches.

Each batch should satisfy:

```bash
bash scripts/check.sh
```

The GitHub branch should remain buildable after each source migration or proof-hardening batch.

## Archived release metadata

Earlier Zenodo-oriented metadata is retained as archival/release provenance. It should not drive the GitHub source layout. The active development source of truth is the GitHub Lean project and its CI status.

## Status

- GitHub-native Lean project: active
- CI: direct `elan` workflow
- Source migration: active, batch-based
- Phase 3: R7 proof-obligation tightening closure checkpoint reached
- R1--R7 theorem-candidate milestones: recorded
- R3--R7 hardening pass series: CI green
- Post-hardening-pass closure: CI green
- R3 proof-obligation tightening closure: CI green
- R4 proof-obligation tightening closure: CI green
- R5 proof-obligation tightening closure: CI green
- R6 proof-obligation tightening closure: CI green
- R7 proof-obligation tightening closure: CI green
- Mathlib on main: not introduced
- Dry-run branch policy: recorded
- Main-adoption decision: hold_main_adoption
- Public final theorem claim: review-gated pending independent replay and external audit
