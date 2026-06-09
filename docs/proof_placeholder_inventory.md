# Proof placeholder inventory

This document separates proof-bearing mathematical theorems from review markers,
prototype witnesses, receipts, and readiness packets.  It is intended for
external reviewers who need to know when a Lean object closes a mathematical
obligation and when it only records a boundary, interface, or audit status.

## Reading rule

A Lean declaration in this repository should not be treated as a mathematical
replacement for an analytic theorem merely because it is a theorem, a `ready`
anchor, or a receipt.  The review question is:

```text
Does the declaration prove the analytic property directly, or does it only
register that a route, interface, witness slot, or boundary marker is available?
```

## Placeholder classes

| Class | Typical surface | Mathematical replacement strength | Reviewer action |
|---|---|---:|---|
| `PUnit` carrier | Interface / skeleton / target API placeholder | 0/5 | Treat as structural placeholder only. Demand replacement by a typed mathematical object before accepting theorem closure. |
| `True` field or trivial proof | Boundary marker, non-promotion marker, visibility marker | 0/5 by itself | Accept only as an audit flag. It must never replace a substantive analytic lemma. |
| `concrete...StillOpen` / `...StillOpen` | Historical open-boundary marker | 0/5 | Read as an explicit non-closure marker, unless superseded by a newer terminal receipt that is separately cited. |
| `theoremWitnessOnly` | Witness slot stating a theorem-body source exists | 1/5 | Treat as provenance or pointer. Inspect the upstream theorem body before accepting the claim. |
| `receipt` / `packet` / `manifest` | Audit ledger and review chain | 1/5 | Treat as governance/provenance evidence. It may bind review order, but does not by itself close analysis. |
| `ready` | Readiness predicate or assembled surface | 1-3/5 | Determine payload: if all fields are substantive theorem fields, it may be strong; if it includes `True`, `PUnit`, or witness-only slots, it remains a readiness record. |
| actual theorem over Mathlib object | e.g. equality, closedness, self-adjointness, positivity, countable additivity, PVM law | 4-5/5 | Review as a mathematical proof, subject to assumptions and definitions. |

## Current high-risk tokens

The following tokens should trigger review rather than automatic acceptance:

```text
PUnit
True
StillOpen
theoremWitnessOnly
receipt
Receipt
ready
Ready
prototype
Prototype
skeleton
Skeleton
boundary
Boundary
packet
Packet
manifest
Manifest
```

## Current repository observations

Search surfaces show `PUnit` in R4 target APIs, projection shells, and several
Mathlib analytic skeleton/interface files.  These should be read as placeholder
or target-API carriers unless the same file, or a downstream file, replaces them
with a typed analytic object.

Search surfaces show `theoremWitnessOnly` near the continuum Hamiltonian and
Yang-Mills spectral derivation route.  These should be read as witness/provenance
slots until the upstream theorem-body route is inspected.

Search surfaces show `StillOpen` in historical R4 and exact-gap separation
contexts.  These identifiers are useful because they explicitly preserve a
non-closure boundary, but their presence must be reconciled with any later
terminal route that claims a superseding closure.

## Replacement hierarchy

Use this hierarchy when reviewing a claim:

```text
Level 0: PUnit / True / StillOpen marker
Level 1: receipt / packet / manifest / theoremWitnessOnly
Level 2: ready surface that assembles mixed Level 0-1 and theorem fields
Level 3: ready surface whose fields are mostly substantive theorem anchors
Level 4: theorem proving a typed Mathlib property for the concrete object
Level 5: theorem proving the final target property and linking it to the public route
```

## External-review checklist

For each public theorem route, record:

1. Which declarations are Level 0 markers.
2. Which declarations are Level 1 provenance or receipt objects.
3. Which `ready` declarations are pure assembly and which contain substantive theorem payloads.
4. Which typed Mathlib properties are actually proven.
5. Which final claims still depend on a witness slot or terminal receipt.
6. Whether a `StillOpen` marker is historical, active, or explicitly superseded.

## Current R2 / R3 interpretation

The current R2 infinite-dimensional completed `ℓ²` diagonal lane has substantive
closedness and unboundedness surfaces.  Its R2-to-R3 and R2-to-spectral-input
handoffs are readiness and boundary objects, not shortcuts from R2 closedness to
full spectral theorem, PVM construction, exact atom `33/20`, or positive spectral
weight.

## Audit command

Run the companion audit script to produce a grep-style inventory:

```bash
python3 scripts/audit_proof_placeholder_inventory.py
```

This script is informational by default.  It should fail only when the inventory
contract itself is broken, not merely because placeholders exist.  Placeholders
are allowed when they are visible, classified, and not misrepresented as final
analytic theorems.
