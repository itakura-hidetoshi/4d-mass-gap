# MGAP4D

MGAP4D is a Lean 4 repository for developing and checking the proof architecture of a normalized 4D mass gap theorem.

The repository is organized as a GitHub-native Lean project. The active source tree, CI, documentation, theorem-surface checkpoints, and migration history live directly in this repository.

## Current active Lean root

```text
MGAP4D.lean
```

The root imports the Phase 3 proof-hardening architecture, including the R1--R7 theorem-candidate surfaces, scoped Mathlib dry-run gates, post-Mathlib-hold theorem-route hardening, R3--R7 proof-obligation tightening closures, and the post-proof-obligation-tightening closure path.

## Phase 3 status

The current `main` branch has reached a **post-proof-obligation-tightening closure checkpoint**.

The proof-hardening route has advanced through:

```text
TheoremSurface
  -> Replacement pass 1
  -> Replacement pass 2
  -> MathlibAdoptionGate
  -> R1--R7 theorem-candidate milestones
  -> Phase3CandidateClosure
  -> Phase3CIConfirmationClosure
  -> PreMathlibClosure
  -> R1--R7 scoped Mathlib dry-run series
  -> Mathlib main-adoption hold decision
  -> PostMathlibHoldTheoremHardening
  -> R3--R7 route-specific hardening
  -> R3--R7 theorem-route queue
  -> R3--R7 hardening pass series review
  -> PostHardeningPassClosure
  -> R3--R7 proof-obligation tightening closures
  -> R3--R7 proof-obligation tightening closure series review
  -> PostProofObligationTighteningClosure
```

Important invariant:

```text
main remains pre-Mathlib
lakefile.lean is not modified for Mathlib
No active main-branch Lean module imports Mathlib
Mathlib main-adoption decision remains hold_main_adoption
R3--R7 theorem completions are not claimed
Final gap theorem release is not unlocked
Public theorem boundary remains review-gated
```

## R3--R7 proof-obligation tightening status

```text
R3 proof-obligation tightening closure: CI green
R4 proof-obligation tightening closure: CI green
R5 proof-obligation tightening closure: CI green
R6 proof-obligation tightening closure: CI green
R7 proof-obligation tightening closure: CI green
R3--R7 proof-obligation tightening closure series review: CI green
Post-proof-obligation-tightening closure: CI green
```

## Latest CI confirmation

```text
Post-proof-obligation-tightening closure main CI
Workflow: Lean Direct Elan CI
Run ID: 25780731720
Build job ID: 75722560830
Commit: e74aaf1b12287012c5d5549ef9e946aa017d8cea
Result: success
Audit metadata and Lean source: success
Build Lean project via direct elan: success
Generate Lake manifest: success
lake build: success
```

## Mathlib dry-run policy

Mathlib adoption may be tested only through scoped dry-run branches.

Dry-run success is accepted as contact-surface buildability only. It is not theorem completion and not permission to introduce Mathlib into `main`.

Relevant documents and modules include:

```text
docs/phase3_mathlib_main_adoption_hold_decision.md
docs/phase3_r3_r7_proof_obligation_tightening_closure_series_review_ci.md
docs/phase3_post_proof_obligation_tightening_closure_ci.md
MGAP4D/R3R7ProofObligationTighteningClosureSeriesReview.lean
MGAP4D/PostProofObligationTighteningClosure.lean
```

## Build

```bash
lake update
lake build
```

For the full local audit sequence:

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

GitHub Actions uses:

```text
Lean Direct Elan CI
```

## Repository layout

```text
MGAP4D/                  Active Lean source tree
MGAP4D.lean              Top-level Lean import root
docs/                    GitHub-native documentation and checkpoint ledger
maps/                    Lightweight source and dependency maps
scripts/                 Local and CI audit scripts
.github/workflows/       GitHub Actions CI
```

## Status

- GitHub-native Lean project: active
- CI: direct `elan` workflow
- Phase 3: post-proof-obligation-tightening closure checkpoint reached
- R1--R7 theorem-candidate milestones: recorded
- R3--R7 hardening pass series: CI green
- R3--R7 proof-obligation tightening closures: CI green
- Post-proof-obligation-tightening closure: CI green
- Mathlib on main: not introduced
- Main-adoption decision: hold_main_adoption
- Public final theorem claim: review-gated pending independent replay and external audit
