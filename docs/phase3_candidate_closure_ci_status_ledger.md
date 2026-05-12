# Phase 3 Candidate Closure CI Status Ledger

This ledger records the current CI/status observation after the R1--R7 candidate closure and request-import cleanup.

## Main commit observation

Checked commit:

```text
268a065dfe242189eaf354af29aea0659969f6c2
```

Checked items:

```text
fetch_commit_workflow_runs -> []
get_commit_combined_status -> statuses: []
```

Interpretation:

```text
CI status: not observed / not confirmed
```

This was not recorded as CI green.

## Main trigger note observation

A non-semantic documentation note was added to try to trigger a main push CI observation.

```text
trigger commit: eda28516f6dc7e9d4d87de630cdba3540ba345f4
file: docs/phase3_candidate_closure_ci_trigger_note.md
```

Observed immediately after that trigger commit:

```text
fetch_commit_workflow_runs -> []
get_commit_combined_status -> statuses: []
```

Interpretation:

```text
CI status: not observed / not confirmed
```

This was also not recorded as CI green.

## PR CI observation

A draft PR was opened to observe the pull_request workflow without changing main source semantics.

```text
PR: #2
Title: ci: observe Phase 3 candidate closure
Branch: ci/phase3-candidate-closure-observation
Head commit: 26d2e344178b3b6a6eaa382f05174ca7adfb5e34
Workflow: Lean Direct Elan CI
Run ID: 25712798053
Run number: 547
```

Observed workflow result:

```text
status: completed
conclusion: success
```

Observed jobs:

```text
Audit metadata and Lean source -> success
Build Lean project via direct elan -> success
```

Interpretation:

```text
PR CI status: green for the observation branch head
```

This confirms that the pull_request workflow can build the R1--R7 candidate-closure state plus the PR-only non-semantic note.

It does not mean Mathlib has been added to main.

## Manual main workflow_dispatch CI observation

A manual workflow run URL was provided and verified:

```text
Run URL: https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/25713735152/job/75499172664
Run ID: 25713735152
Build job ID: 75499172664
Workflow: Lean Direct Elan CI
```

Observed run jobs:

```text
Audit metadata and Lean source -> completed / success
Build Lean project via direct elan -> completed / success
```

Observed build job steps:

```text
Set up job -> success
Checkout repository -> success
Confirm direct elan workflow -> success
Install elan and Lean toolchain -> success
Show Lean and Lake versions -> success
Generate Lake manifest -> success
Build Lean project with lake build -> success
Complete job -> success
```

Interpretation:

```text
main workflow_dispatch CI status: green
```

This confirms that the manually executed main workflow successfully completed audit and build.

It does not mean Mathlib has been added to main.

## Current source-side state

The main branch now records:

```text
R1--R7 theorem-candidate milestones
R3 omission corrected
Phase3CandidateClosure imported by MGAP4D.lean
MathlibAdoptionGate request files using Requester direct import
Mathlib still not added to main
lakefile.lean still not changed for Mathlib
```

## Required next action

Keep PR #2 as a draft observation PR or close it after recording. Do not merge it unless a non-semantic CI observation note is desired on main.

Main remains pre-Mathlib.
