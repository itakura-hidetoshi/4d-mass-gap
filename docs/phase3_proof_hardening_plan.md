# Phase 3: Proof Hardening Plan

Phase 3 begins after the GitHub-native source migration batches 001--010.

The goal is to move from status interfaces toward theorem surfaces while keeping `main` buildable after every change.

## Phase 3 principles

1. Keep `MGAP4D.lean` buildable.
2. Restore deferred imports only in dependency-closed groups.
3. Add Mathlib only when a theorem-level module requires it.
4. Preserve status interfaces until the corresponding theorem surface builds.
5. Record every proof-hardening step in `docs/` and `maps/`.

## Initial hardening layers

### H1: OperatorAPI theorem surface

Convert OperatorAPI status interfaces into theorem-surface modules that expose stable propositions and pack theorems.

### H2: R1 theorem surface

Introduce theorem surfaces for:

- Hilbert scaffold;
- excited subspace;
- inner functional;
- projection pair;
- export to R2.

### H3: R2 theorem surface

Introduce theorem surfaces for:

- reducing subspace;
- self-adjoint restriction;
- excited Hamiltonian;
- spectrum union;
- export to R3/R4/R5.

### H4: R3--R7 theorem surfaces

Tighten each remaining layer only after its dependencies are ready.

## CI gate

Every hardening step must pass:

```bash
bash scripts/check.sh
```

or the equivalent GitHub Actions workflow.

## Current next step

Add a Lean-side `ProofHardening` module that records the hardening plan and the current gate state.
