# Mathlib physical Hamiltonian normalization bridge CI

Run ID: 25943821976
Audit job ID: 76267448064
Build job ID: 76267458360
Commit checked out by CI: a1ffa896fd4e35ad48b118098769cb5a314fa1a5
Result: success

Status: CI green.

Confirmed:
- Audit metadata and Lean source: success
- Build Lean project via direct elan: success
- lake build: success

Observed toolchain:
- Lean 4.30.0-rc2
- Lake 5.0.0-src+3dc1a08

Checked artifacts:
- MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean
- MGAP4D/MathlibAnalytic.lean

Meaning:
- physical Hamiltonian normalization bridge is CI green
- reference energy scale E0 is explicit and positive
- normalized Hamiltonian convention is explicit
- normalizedGap = physicalGap / E0 is present
- physicalGap = E0 * normalizedGap is present
- internal normalized units set E0 = 1
- dimensionless exact gap is 33/20
- dimensional physical gap reads as E0 * 33/20

Boundary:
- normalization bridge only
- theorem body is unchanged
- external consensus is not claimed
- public theorem boundary is held
