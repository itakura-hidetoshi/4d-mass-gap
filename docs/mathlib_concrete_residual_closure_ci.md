# Mathlib concrete residual closure CI

Run ID: 25942891907
Audit job ID: 76264474753
Build job ID: 76264489947
Commit checked out by CI: 5fa3f700c013097c43b0b8f0750a878a2f1aed31
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
- MGAP4D/MathlibAnalytic/ConcreteResidualClosure.lean
- MGAP4D/MathlibAnalytic.lean

Meaning:
- concrete residual closure is CI green
- concrete Hilbert residual is closed
- unbounded operator residual is closed
- PVM residual is closed
- plaquette residual is closed
- operator-measure residual is closed
- exact value 33/20 is preserved

Boundary:
- internal concrete residual closure only
- external consensus is not claimed
- public theorem boundary is held
