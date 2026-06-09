# R4 terminal status supersession note

This note resolves a potential ambiguity in the R4 route.

Some older R4 endpoint-stage files still contain identifiers such as:

```text
SpectralMeasurePVMActualBorelSetAlgebraRealizationStillOpen
SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen
SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen
SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
```

These names are append-only historical boundary markers for earlier local stages. They are not the current global R4 status on `main`.

## Current canonical status

The current public route treats the R1--R7 terminal receipt chain as canonical:

```text
R4 genuine PVM closure
  -> R5 compact centered plaquette observable closure
  -> R6 non-definitional exact atom 33/20 closure
  -> R7 positive spectral-weight closure
  -> R1--R7 terminal discharge chain index
```

The current R4 operator-topology top-level final packet is:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
```

Primary current R4 final-packet anchors:

```text
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_ready
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_public_boundary_held
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_extracts_operator_topology_convergence_target
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_extracts_genuine_bridge
spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_final_packet_preserves_no_shell_collapse
```

## Endpoint-stage files

Files such as:

```text
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedActualBorelEndpointSetAlgebra.lean
```

should be read as earlier local endpoint-stage lineage. Their `StillOpen` predicates preserve the state of that local file at the time it was introduced and keep the no-shell-to-full-collapse boundary explicit.

They do not override the current terminal route.

## Review rule

When an older R4 file says that an item is `StillOpen`, read it as:

```text
still open at this earlier local endpoint-stage boundary
```

not as:

```text
still open in the current global R1--R7 terminal public route
```

For current public status, use:

```text
THEOREM_INDEX.md
docs/current_proof_status.md
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
MGAP4D/R4/Theorem/SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelFinalPacket.lean
```

## Boundary retained

The supersession is not a silent collapse from shell to full spectral-measure theorem. The current R4 route still preserves:

```text
no-shell-to-full-collapse boundary
publicBoundaryLocked / finalReleaseHeld at the terminal route
external mathematical consensus not claimed by documentation alone
```

Thus the correct external reading is:

```text
old endpoint-stage StillOpen markers = historical local lineage
current terminal R4 status = R4 genuine-PVM/operator-topology closure is terminal-visible and carried into R5/R6/R7
```
