# Independent Replay Guide

This document gives a minimal independent replay procedure for the MGAP4D Lean 4 repository.

## Scope

This guide checks the public repository state only. It confirms the repository audit chain, lane hardening chain, four-lane residual closure, internal review residual closure gate, external audit readiness gate, replay summary, Lake manifest generation, and Lean build.

It does not claim external mathematical consensus, peer-review completion, Clay-style public final theorem acceptance, or a dimensional physical mass gap without an external reference scale `E0`.

## Fresh clone replay

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
cat lean-toolchain
lean --version
lake --version
```

Expected Lean family:

```text
Lean 4.30.0-rc2
Lake 5.0.0-src+3dc1a08 or compatible Lake for the pinned Lean toolchain
```

## One-command repository check

```bash
bash scripts/check.sh
```

This executes, in order:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] audit Hilbert construction lane hardening
[check] audit self-adjoint HPhys lane hardening
[check] audit continuum Yang-Mills lane hardening
[check] audit plaquette spectral weight lane hardening
[check] audit four-lane residual closure
[check] audit internal review residual closure gate
[check] audit external audit readiness gate
[check] replay summary
[check] lake update
[check] lean external audit readiness gate
[check] lake build
```

## Manual replay

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/audit_hilbert_construction_lane_hardening.py
python3 scripts/audit_self_adjoint_hphys_lane_hardening.py
python3 scripts/audit_continuum_yang_mills_lane_hardening.py
python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py
python3 scripts/audit_four_lane_residual_closure.py
python3 scripts/audit_internal_review_residual_closure_gate.py
python3 scripts/audit_external_audit_readiness_gate.py
python3 scripts/replay_summary.py
lake update
lake env lean MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean
lake build
```

## Residual closure chain

```text
InfiniteDimensionalYangMillsRealizationTargets
  -> InfiniteDimensionalResidualFillingBridge
  -> HardPhysicalResidualHardeningMap
      -> HilbertConstructionLaneHardening
      -> SelfAdjointHPhysLaneHardening
      -> ContinuumYangMillsLaneHardening
      -> PlaquetteSpectralWeightLaneHardening
  -> FourLaneResidualClosure
  -> InternalReviewResidualClosureGate
  -> ExternalAuditReadinessGate
```

## External audit readiness anchors

```text
repositoryInternalResidualClosed
noReviewLevelResidualLeft
independentReplayVisible
auditScriptRouteVisible
ciRouteVisible
externalAuditReady
externalConsensusNotClaimed
publicBoundaryHeld
finalReleaseHeld
exactValuePreserved
```

## GitHub Actions parity

The main replay path is mirrored by:

```text
.github/workflows/full-local-check.yml
```

The external audit readiness gate also has a dedicated workflow:

```text
.github/workflows/external-audit-readiness-ci.yml
```

## Review boundary

A successful independent replay means the repository builds with the pinned Lean toolchain, declared audit scripts pass, lane-hardening and closure gates pass, the external audit readiness gate passes, and the replay summary is reproducible.

It does not mean external consensus has been obtained or that the gate layers alone complete the physical continuum proof.
