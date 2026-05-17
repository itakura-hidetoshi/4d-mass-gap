# Complete Infinite-Dimensional Hilbert Construction

Lean source:

```text
MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean
```

Audit script:

```text
scripts/audit_complete_infinite_dimensional_hilbert_construction.py
```

## Lane surface

The old hardening-oriented name is replaced by a construction-oriented name:

```text
CompleteInfiniteDimensionalHilbertConstructionLaneData
completeInfiniteDimensionalHilbertConstructionLaneData
complete_infinite_dimensional_hilbert_construction_lane_ready
```

## Strengthened upstream surface

The lane carries a dedicated complete infinite-dimensional construction surface:

```text
CompleteInfiniteDimensionalHilbertConstructionData
completeInfiniteDimensionalHilbertConstructionData
complete_infinite_dimensional_hilbert_construction_ready
```

This surface records:

```text
carrier
basisVector
finiteBasisFamily
finiteBasisFamily_def
finiteRestrictionLinearlyIndependent
arbitraryFiniteRankWitness
noFiniteRankCollapse
```

The key strengthening is that the Hilbert lane is no longer only a boolean
collection of imported skeleton readiness flags.  It now routes the Hilbert
instance through a Nat-indexed countable basis tower with arbitrarily large
finite independent restrictions, blocking bounded finite-rank collapse before
the physical unbounded-operator bridge.

## Hardened surfaces retained as lane fields

```text
countableBasisHardened
finiteSpanDensityHardened
normTopologyHardened
cauchyCompletionHardened
completeNormedSpaceHardened
innerProductHardened
hilbertInstanceHardened
```

These are now backed by:

```text
countableBasisRealized
finiteSpanDenseInCompletion
normTopologyRealized
cauchyCompletionRealized
completeNormedSpaceRealized
innerProductRealized
hilbertInstanceRealized
```

## Boundary anchors

```text
hardPhysicalBoundaryVisible
exactValuePreserved
reviewLevelOnly
publicBoundaryHeld
finalReleaseHeld
```

Boundary remains unchanged: this is an internal review-level construction
surface, not an external-consensus theorem and not a public-final physical
acceptance claim.
