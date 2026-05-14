# Spectral sector separation core bridge

This note records a pre-Mathlib bridge from sector separation into the spectral core certificate.

## Lean artifacts

```text
MGAP4D/Spectral/SectorSeparationCoreBridge.lean
MGAP4D/Spectral.lean
```

## Added surface

```text
SectorSeparationCoreBridge
SectorSeparationCoreBridge.ready
spectral3320SectorSeparationCoreBridge
sector_separation_core_bridge_pack
spectral3320_sector_separation_core_bridge_ready
spectral3320_sector_separation_core_bridge_value
spectral3320_sector_separation_core_bridge_positive_numerator
spectral3320_sector_separation_core_bridge_witness_orthogonal
spectral3320_sector_separation_core_bridge_witness_not_vacuum
spectral3320_sector_separation_core_bridge_no_collapse
```

## Meaning

The bridge makes the stronger vacuum / orthogonal separation certificate visible from the spectral core certificate.

```text
spectral core ready
sector separation ready
sector boundary matches core lower-bound boundary
positive witness matches core witness
witness sector is orthogonal
witness sector is not vacuum
vacuum / orthogonal collapse is blocked
33/20 positive value remains visible
positive numerator is preserved
```

## Boundary

```text
pre-Mathlib structural sector-separation core bridge only
R1--R7 theorem completions not claimed
Mathlib on main not introduced
public theorem boundary held
```
