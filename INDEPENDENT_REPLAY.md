# Independent Replay Guide

This document gives a minimal independent replay procedure for the MGAP4D Lean 4 repository.

It is intended for external reviewers who want to reproduce the repository-level audit and Lean build without relying on local, unpublished state.

## Scope

This guide checks the public repository state only.

It confirms:

```text
release manifest consistency
Lean forbidden-token audit
major theorem non-placeholder audit
analytic bridge-coherence audit
infinite-dimensional Yang-Mills target-layer audit
infinite-dimensional residual-filling bridge audit
hard physical residual hardening-map audit
Hilbert construction lane hardening audit
self-adjoint HPhys lane hardening audit
continuum Yang-Mills lane hardening audit
Lean replay summary generation
Lake manifest generation
Lean build via lake build
```

It does not by itself establish:

```text
external mathematical consensus
peer-review completion
Clay-style final theorem acceptance
a dimensional physical mass gap without choosing the reference scale E0
that syntactic audit scripts replace Lean kernel checking
that Lean CI replaces expert mathematical review
that the target / residual-filling / hardening-map / lane-hardening layers by themselves complete the continuum proof
```

The current public boundary is an internal normalized theorem-body / proof-architecture surface with explicit audit, target-obligation, residual-filling, hardening-map, Hilbert-lane hardening, self-adjoint HPhys lane hardening, continuum Yang-Mills lane hardening, and replay support.

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
[check] replay summary
[check] lake update
[check] lake build
```

## Manual step-by-step replay

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
python3 scripts/replay_summary.py
lake update
lake build
```

## Audit stages

```text
verify_manifest.py: archived manifest consistency
audit_lean_forbidden_tokens.py: sorry/admit/axiom/constant audit
audit_major_theorem_nonplaceholder.py: load-bearing theorem surface audit
audit_bridge_coherence.py: bridge import/anchor/boundary audit
audit_infinite_dimensional_target_layer.py: target-obligation layer audit
audit_infinite_dimensional_residual_filling.py: residual-filling bridge audit
audit_hard_physical_residual_hardening_map.py: four-lane hard residual map audit
audit_hilbert_construction_lane_hardening.py: Hilbert construction lane audit
audit_self_adjoint_hphys_lane_hardening.py: self-adjoint HPhys lane audit
audit_continuum_yang_mills_lane_hardening.py: continuum Yang-Mills lane audit
replay_summary.py: replay summary generation
lake build: Lean kernel build gate
```

## Hardened lanes currently audited

```text
Hilbert construction lane:
  countableBasisHardened
  finiteSpanDensityHardened
  normTopologyHardened
  cauchyCompletionHardened
  completeNormedSpaceHardened
  innerProductHardened
  hilbertInstanceHardened

Self-adjoint HPhys lane:
  interfaceHardened
  theoremBodyHardened
  domainClosureHardened
  symmetryOnDomainHardened
  selfAdjointCertificateHardened
  rayleighCompatibilityHardened
  physicalOperatorSkeletonHardened
  concreteHPhysBridgeHardened

Continuum Yang-Mills lane:
  concreteYMHardened
  hphysBuiltFromYMHardened
  plaquetteCenteredHardened
  normalizationBridgeHardened
  spectralRealizationHardened
  exactAtomHardened
  continuumSpectralTheoremHardened
  continuumLimitBoundaryVisible
```

## GitHub Actions parity

The main CI workflow is:

```text
.github/workflows/lean-direct-elan.yml
```

The audit job runs the same audit families, including Hilbert construction, self-adjoint HPhys, and continuum Yang-Mills lane hardening.

The one-command local replay path is mirrored by:

```text
.github/workflows/full-local-check.yml
```

## Review boundary

A successful independent replay means:

```text
the repository builds with the pinned Lean toolchain
the declared audit scripts pass
the theorem-surface, bridge-surface, target-layer, residual-filling, hardening-map, and lane-hardening checks pass
the replay summary is reproducible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
CI output alone is a substitute for proof review
the target / residual-filling / hardening-map / lane-hardening layers alone complete the physical continuum proof
```
