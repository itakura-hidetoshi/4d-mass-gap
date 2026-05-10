# MGAP4D v1.6 Source Tree Migration Plan

This document defines the incremental GitHub migration plan for the expanded source snapshot:

```text
MGAP4D_v1_6_expanded_source_snapshot.zip
```

The full Zenodo package audit summary records:

- Lean files: 12,308
- Declarations: 52,137
- sorry: 0
- admit: 0
- axiom: 0
- constant: 0

## Migration principle

The expanded source snapshot should not be imported as one unreviewed blob. It should be moved in CI-checkable batches, preserving buildability after each batch.

## Target repository layout

```text
MGAP4D/
  Basic.lean
  Axioms.lean
  Certificates.lean
  Gap3320.lean
  FinalSpine.lean
  Foundation/
  Spectral/
  OSPositivity/
  Hamiltonian/
  Plaquette/
  Constructive/
  Audit/
  Release/
```

## Batch order

### Batch 0: current scaffold

- `MGAP4D.Basic`
- `MGAP4D.Axioms`
- `MGAP4D.Certificates`
- `MGAP4D.Gap3320`
- `MGAP4D.FinalSpine`

### Batch 1: Foundation interfaces

Purpose: move definitions that other files import but that have minimal theorem weight.

Suggested paths:

```text
MGAP4D/Foundation/Types.lean
MGAP4D/Foundation/Units.lean
MGAP4D/Foundation/Names.lean
MGAP4D/Foundation/Indexing.lean
MGAP4D/Foundation/RationalNormalization.lean
```

### Batch 2: Certificate layer

Purpose: move certificate structures and invariants.

```text
MGAP4D/Certificates/Born.lean
MGAP4D/Certificates/ClassicalLimit.lean
MGAP4D/Certificates/RGScaleBridge.lean
MGAP4D/Certificates/EmpiricalID.lean
MGAP4D/Certificates/Packet.lean
```

### Batch 3: Spectral and Hamiltonian layer

Purpose: move the normalized operator and spectral interfaces.

```text
MGAP4D/Spectral/Basic.lean
MGAP4D/Spectral/Gap.lean
MGAP4D/Hamiltonian/Basic.lean
MGAP4D/Hamiltonian/Physical.lean
```

### Batch 4: OS positivity and reconstruction layer

```text
MGAP4D/OSPositivity/Basic.lean
MGAP4D/OSPositivity/Reflection.lean
MGAP4D/OSPositivity/Reconstruction.lean
```

### Batch 5: Plaquette observable layer

```text
MGAP4D/Plaquette/Basic.lean
MGAP4D/Plaquette/Smeared.lean
MGAP4D/Plaquette/SpectralMeasure.lean
```

### Batch 6: 33/20 theorem layer

```text
MGAP4D/Constructive/Gap3320.lean
MGAP4D/Constructive/Eigenvector.lean
MGAP4D/Constructive/PlaquetteWitness.lean
MGAP4D/Constructive/FinalTheorem.lean
```

### Batch 7: Audit and release layer

```text
MGAP4D/Audit/NoForbiddenTokens.lean
MGAP4D/Audit/DeclarationCount.lean
MGAP4D/Release/V16.lean
```

## CI rule

Each batch should satisfy:

```bash
python3 scripts/verify_manifest.py
python3 scripts/audit_lean_forbidden_tokens.py
lake build
```

## Required data from the source snapshot

Before moving the full source, extract and paste one of the following:

1. top-level directory listing;
2. the first 20 smallest `.lean` files;
3. the import graph root file;
4. the actual contents of the next file to migrate.

Without the zip contents available in this chat, this repository can only receive scaffold and metadata files. Source files must be pasted or uploaded in batches.
