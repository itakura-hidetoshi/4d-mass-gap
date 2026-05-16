# MGAP4D External Audit Packet

This packet is the top-level navigation surface for external audit and independent replay of the MGAP4D repository.

## Boundary statement

The current repository state is an internal normalized theorem-body / proof-architecture surface with explicit replay, theorem-surface audit, bridge-coherence audit, target-obligation layers, review-level residual filling, hard residual hardening lanes, and public-boundary markers.

It does not claim:

```text
external mathematical consensus
peer-review completion
Clay-style public final theorem acceptance
a dimensional physical mass gap without choosing E0
that CI output replaces mathematical review
that audit scripts replace Lean kernel checking
that target / residual-filling / hardening-map layers alone complete the continuum proof
```

## Primary review route

| Step | File / command | Purpose |
|---:|---|---|
| 1 | `README.md` | Repository role, theorem claim, CI/audit status, and boundary. |
| 2 | `INDEPENDENT_REPLAY.md` | Fresh-clone replay procedure. |
| 3 | `bash scripts/check.sh` | Complete local replay path. |
| 4 | `.github/workflows/full-local-check.yml` | CI mirror of the one-command replay path. |
| 5 | `THEOREM_INDEX.md` | Theorem / bridge / target surface map. |
| 6 | `PHYSICAL_REALIZATION_BOUNDARY.md` | Physical interpretation boundary. |
| 7 | `docs/infinite_dimensional_yang_mills_target_layer.md` | Target-obligation layer ledger. |
| 8 | `docs/infinite_dimensional_residual_filling_bridge.md` | Review-level residual filling ledger. |
| 9 | `docs/hard_physical_residual_hardening_map.md` | Four-lane hard residual hardening ledger. |

## One-command replay

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
```

Expected stages:

```text
[check] verify manifest
[check] audit Lean forbidden tokens
[check] audit major theorem non-placeholder surfaces
[check] audit analytic bridge coherence
[check] audit infinite-dimensional Yang-Mills target layer
[check] audit infinite-dimensional residual filling bridge
[check] audit hard physical residual hardening map
[check] replay summary
[check] lake update
[check] lake build
```

## Manual replay path

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
python3 scripts/audit_major_theorem_nonplaceholder.py
python3 scripts/audit_bridge_coherence.py
python3 scripts/audit_infinite_dimensional_target_layer.py
python3 scripts/audit_infinite_dimensional_residual_filling.py
python3 scripts/audit_hard_physical_residual_hardening_map.py
python3 scripts/replay_summary.py
lake update
lake build
```

## Audit scripts

| Script | Role |
|---|---|
| `scripts/verify_manifest.py` | Archived manifest consistency. |
| `scripts/audit_lean_forbidden_tokens.py` | Checks `sorry/admit/axiom/constant` outside comments and strings. |
| `scripts/audit_major_theorem_nonplaceholder.py` | Checks named theorem surfaces for non-placeholder anchors. |
| `scripts/audit_bridge_coherence.py` | Checks analytic / physical bridge anchors and boundary markers. |
| `scripts/audit_infinite_dimensional_target_layer.py` | Checks the infinite-dimensional Yang--Mills target-obligation layer. |
| `scripts/audit_infinite_dimensional_residual_filling.py` | Checks review-level residual filling bridge. |
| `scripts/audit_hard_physical_residual_hardening_map.py` | Checks four visible hard residual hardening lanes. |
| `scripts/replay_summary.py` | Generates replay summary. |
| `scripts/check.sh` | Runs the complete replay path. |

## Core Lean roots

```text
MGAP4D.lean
MGAP4D/MathlibAnalytic.lean
```

The analytic root imports:

```text
MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean
MGAP4D/MathlibAnalytic/InfiniteDimensionalResidualFillingBridge.lean
MGAP4D/MathlibAnalytic/HardPhysicalResidualHardeningMap.lean
```

## Residual evolution chain

```text
InfiniteDimensionalYangMillsRealizationTargets
  -> InfiniteDimensionalResidualFillingBridge
  -> HardPhysicalResidualHardeningMap
```

Meaning:

```text
target layer: makes analytic obligations first-class
residual filling bridge: fills immediately bridgeable review-level residuals
hardening map: keeps remaining hard physical residual split into visible lanes
```

## Filled review-level residuals

```text
filledInfiniteDimensionalNecessity
filledFiniteSpanDensity
filledHilbertInstanceSkeleton
filledSelfAdjointHPhysSkeleton
filledContinuumSpectralSkeleton
filledNormalizationBridge
```

## Remaining hardening lanes

```text
hilbertConstructionLane
selfAdjointHPhysLane
continuumYangMillsLane
plaquetteSpectralWeightLane
```

The hardening map also requires:

```text
noLaneHidden
exactValuePreserved
reviewLevelOnly
publicBoundaryHeld
finalReleaseHeld
```

## Physical normalization boundary

The normalized theorem-body value is dimensionless:

```text
exactGapValueReal = 33 / 20
```

Dimensional reading requires an external reference scale:

```text
physicalGap_dimensional = E0 * (33/20)
```

## Successful packet review means

```text
the repository can be replayed from a fresh clone
the pinned Lean toolchain is visible
the audit scripts pass
the Lean build passes
the target layer is present
the residual filling bridge is present
the four hard residual lanes are visible
public boundary markers are visible
```

It does not mean:

```text
external consensus has been obtained
all analytic residuals have been accepted by the mathematical community
Clay-style final theorem status has been reached
target / residual-filling / hardening-map layers alone complete the physical continuum proof
```

## Reviewer record template

```text
Repository: itakura-hidetoshi/4d-mass-gap
Commit SHA reviewed:
Date reviewed:
Lean version:
Lake version:
scripts/check.sh result:
lake build result:
Target-layer audit result:
Residual-filling audit result:
Hardening-map audit result:
Physical boundary interpretation preserved: yes/no
Normalization boundary preserved: yes/no
Reviewer notes:
```
