# Proof placeholder inventory

This document separates proof-bearing mathematical theorems from review markers,
prototype witnesses, receipts, and readiness packets. It is intended for
external reviewers who need to know when a Lean object closes a mathematical
obligation and when it records an undischarged proof debt.

## Reading rule

A Lean declaration in this repository must not be accepted as a mathematical
replacement for an analytic theorem merely because it is a theorem, a `ready`
anchor, a receipt, or a terminal-looking packet. The review question is:

```text
Does the declaration prove the analytic property directly, or does it leave an
open proof debt that must be discharged, replaced, or explicitly superseded?
```

## Hard correction: PUnit / True / StillOpen

`PUnit`, `True`, and `StillOpen` are not just weak evidence. They are
**undischarged proof-debt markers** unless a nearby or downstream typed theorem
explicitly replaces or supersedes them.

```text
PUnit
  = placeholder carrier / target-API shell
  = requires replacement by a typed mathematical object
  = cannot close a public analytic theorem

True
  = trivial marker / visibility flag / non-promotion flag
  = requires a separate substantive theorem field for any mathematical claim
  = cannot discharge an analytic lemma by itself

StillOpen
  = active or historical open-obligation marker
  = requires explicit status: active, historical, or superseded-by <theorem>
  = cannot coexist with a final closure claim unless the supersession route is cited
```

For external review, any public route that depends essentially on these markers
without a typed replacement theorem must be classified as **not yet discharged**.

## Placeholder classes

| Class | Typical surface | Replacement status | Reviewer action |
|---|---|---|---|
| `PUnit` carrier | Interface / skeleton / target API placeholder | Open proof debt | Demand replacement by a typed mathematical object before accepting theorem closure. |
| `True` field or trivial proof | Boundary marker, non-promotion marker, visibility marker | Open proof debt for any analytic claim | Accept only as metadata. Require a separate substantive theorem for the claim. |
| `concrete...StillOpen` / `...StillOpen` | Active or historical open-boundary marker | Open proof debt until status-resolved | Require explicit classification: active, historical, or superseded with theorem citation. |
| `theoremWitnessOnly` | Witness slot stating a theorem-body source exists | Provenance only | Inspect the upstream theorem body before accepting the claim. |
| `receipt` / `packet` / `manifest` | Audit ledger and review chain | Governance/provenance only | It may bind review order, but does not by itself close analysis. |
| `ready` | Readiness predicate or assembled surface | Payload-dependent | If it includes `True`, `PUnit`, `StillOpen`, or witness-only slots, classify remaining proof debt. |
| actual theorem over Mathlib object | Equality, closedness, self-adjointness, positivity, countable additivity, PVM law | Candidate mathematical proof | Review assumptions, definitions, and dependency chain. |

## Current high-risk tokens

The following tokens should trigger review and proof-debt classification rather
than automatic acceptance:

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
Mathlib analytic skeleton/interface files. These are open proof-debt carriers
until a typed analytic object replaces them in the same lane or in a cited
downstream lane.

Search surfaces show `True` in many boundary and readiness surfaces. These are
acceptable as visibility flags only. They do not discharge analytic content
unless paired with a separate substantive theorem field.

Search surfaces show `theoremWitnessOnly` near the continuum Hamiltonian and
Yang-Mills spectral derivation route. These are witness/provenance slots until
the upstream theorem-body route is inspected.

Search surfaces show `StillOpen` in historical R4 and exact-gap separation
contexts. Each occurrence must be classified as active, historical, or
superseded. A final closure claim may cite a `StillOpen` identifier only when it
also cites the superseding route.

## Replacement hierarchy

Use this hierarchy when reviewing a claim:

```text
Level -1: PUnit / True / StillOpen used as theorem closure
          => invalid as closure; proof debt remains
Level 0: PUnit / True / StillOpen visible and classified
         => open obligation marker
Level 1: receipt / packet / manifest / theoremWitnessOnly
         => provenance or review ordering only
Level 2: ready surface that assembles mixed Level 0-1 and theorem fields
         => readiness record with residual proof debt
Level 3: ready surface whose fields are mostly substantive theorem anchors
         => candidate route, still dependency-audited
Level 4: theorem proving a typed Mathlib property for the concrete object
         => mathematical proof candidate
Level 5: theorem proving the final target property and linking it to the public route
         => final-route proof candidate subject to external review
```

## External-review checklist

For each public theorem route, record:

1. Which declarations contain `PUnit`, `True`, or `StillOpen`.
2. Whether each such declaration is active, historical, or superseded.
3. Which typed theorem replaces each placeholder marker.
4. Which declarations are provenance-only: `receipt`, `packet`, `manifest`, or `theoremWitnessOnly`.
5. Which `ready` declarations are pure assembly and which contain substantive theorem payloads.
6. Which typed Mathlib properties are actually proven.
7. Which final claims still depend on a witness slot, terminal receipt, or placeholder marker.

## Current R2 / R3 interpretation

The current R2 infinite-dimensional completed `ℓ²` diagonal lane has substantive
closedness and unboundedness surfaces. Its R2-to-R3 and R2-to-spectral-input
handoffs are readiness and boundary objects, not shortcuts from R2 closedness to
full spectral theorem, PVM construction, exact atom `33/20`, or positive spectral
weight.

If any R2/R3 route uses `PUnit`, `True`, or `StillOpen` as a mathematical closure
of symmetry, adjoint-domain agreement, self-adjointness, spectral theorem, PVM,
or positive spectral weight, that route remains **not discharged** until a typed
replacement theorem is cited.

## Euclidean construction target / spine interpretation

The OS/Wightman--Euclidean construction lane is a higher-level theorem route, not
a shortcut around construction proof debt.

```text
EuclideanYangMillsMeasureUnconditionalConstructionTarget
  = proof-field socket for an eventual concrete Euclidean Yang--Mills measure construction
  = candidate route only after each construction field is reviewed as a typed theorem or externally supplied construction proof

EuclideanYangMillsContinuumMeasureConstructionSpine
  = finite-volume / continuum construction spine
  = carries projective consistency, tightness, weak-limit, continuum-measure identification, and Schwinger-function limit proof fields

ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection
  = construction-spine external-audit projection
  = review-routing projection, not external acceptance
```

Key fields requiring dependency review:

```text
continuumFourDimensionalYangMillsMeasureConstructed_proof
nontrivialCompactGaugeGroupConstructed_proof
interactingContinuumLimitConstructed_proof
gaugeInvariantSchwingerFunctionsConstructed_proof
projectiveConsistency_proof
tightness_proof
weakLimitExists_proof
continuumMeasureIdentified_proof
schwingerFunctionsAreContinuumLimits_proof
```

Typed theorem anchors currently projecting the construction spine into the
mass-gap route include:

```text
euclidean_yang_mills_unconditional_measure_construction_mass_gap
euclidean_yang_mills_finite_volume_continuum_construction_mass_gap
external_audit_readiness_euclidean_yang_mills_construction_spine_projection
external_audit_readiness_euclidean_construction_spine_exact_gap_positive
external_audit_readiness_euclidean_construction_spine_exact_gap_threshold
external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation
```

Boundary rule:

```text
The construction-spine external-audit projection is not external acceptance.
External acceptance of the construction-spine external-audit projection is not claimed.
A concrete Euclidean Yang--Mills measure construction and external validation remain separate review tasks.
```

## Audit command

Run the companion audit script to produce a grep-style inventory:

```bash
python3 scripts/audit_proof_placeholder_inventory.py
```

This script is informational by default, but its output must be treated as a
proof-debt map. Placeholders are allowed only when they are visible, classified,
and not represented as final analytic theorem closures.
