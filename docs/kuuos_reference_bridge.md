# KuuOS Reference Bridge

This document records how the MGAP4D / 4D mass gap proof repository is referenced from KuuOS.

## Canonical Proof Repository

The canonical proof repository for the 4D mass gap proof architecture is this repository:

```text
itakura-hidetoshi/4d-mass-gap
```

This repository contains the active GitHub-native Lean project, including:

```text
MGAP4D.lean
MGAP4D/Phase3ReleaseGate.lean
MGAP4D/Spectral.lean
MGAP4D/Spectral/GapFormalization.lean
MGAP4D/SpectralGapFormalizationGate.lean
```

## KuuOS Reference Repository

KuuOS references the 4D mass gap proof architecture as a physics-facing bridge and governance-facing public-core surface:

```text
itakura-hidetoshi/KuuOS
```

KuuOS may maintain documents that summarize, govern, or interpret the proof architecture, such as:

```text
docs/MGAP4D_4D_MASS_GAP_PROOF_MEMORY_v0_1.md
docs/MGAP4D_PHASE3_RELEASE_GATE_MEMORY_v0_1.md
docs/MGAP4D_R1_R7_RELEASE_EVIDENCE_MAP_v0_1.md
docs/MGAP4D_PROOF_ARTIFACT_MAP_v0_1.md
docs/MGAP4D_NORMALIZATION_CONVENTION_RECORD_v0_1.md
docs/MGAP4D_FINAL_THEOREM_BOUNDARY_DECISION_RECORD_v0_1.md
```

Those KuuOS documents are reference, governance, and interpretation surfaces. They do not replace this repository as the canonical Lean proof repository.

## Direction of Reference

```text
4d-mass-gap
  = canonical Lean proof repository

KuuOS
  = public-core governance / philosophy / bridge repository that references 4d-mass-gap
```

## Boundary

KuuOS references should not be read as independently opening final theorem release.

Current boundary remains:

```text
spectral gap formalization: CI green
R1--R7 theorem completions: not claimed here
final release: not opened
public theorem boundary: held
```

## Development Rule

```text
append-only / tighten-only / overwrite-forbidden
```
