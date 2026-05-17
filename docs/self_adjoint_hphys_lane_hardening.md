# Self-adjoint HPhys Lane Hardening

Lean source:

```text
MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean
```

Audit script:

```text
scripts/audit_self_adjoint_hphys_lane_hardening.py
```

Upstream Hilbert construction anchor:

```text
completeHilbertConstructionLaneReady
completeInfiniteDimensionalHilbertConstructionLaneData.ready
```

The self-adjoint HPhys lane now depends on the renamed complete infinite-dimensional Hilbert construction lane, not on the former hardening-oriented Hilbert lane name.

Hardened surfaces:

```text
interfaceHardened
theoremBodyHardened
domainClosureHardened
symmetryOnDomainHardened
selfAdjointCertificateHardened
rayleighCompatibilityHardened
physicalOperatorSkeletonHardened
concreteHPhysBridgeHardened
```

Boundary anchors:

```text
hardPhysicalBoundaryVisible
exactValuePreserved
reviewLevelOnly
publicBoundaryHeld
finalReleaseHeld
```
