# R2 infinite-dimensional `ℓ²` diagonal operator lane

This note fixes the current public reading of R2.

Older PR taxonomy and older R2 frontier notes remain useful as historical context, but the current proof-facing R2 lane on `main` is the infinite-dimensional completed `ℓ²` diagonal operator route.

## Current canonical R2 lane

Lean anchor:

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
```

Primary theorem:

```text
concrete_analytic_spine_l2_r2_infinite_diagonal_operator_lane_ready
```

This theorem bundles the current R2 main lane:

```text
concrete real Hilbert carrier
completed ℓ² carrier
dense-domain operator surface
diagonal-operator evidence
finite-support core
graph-norm finite-support density
graph-norm core release
graph-closedness readiness promotion
graph-closedness obligation promotion
graph-closure closed theorem
closed-operator theorem
completed diagonal operator closedness
completed Hilbert operator-norm unboundedness
self-adjointness concrete preconditions
physical/spectral promotion audit checklist
```

## Why this supersedes older R2 taxonomy

The old R2 taxonomy was useful while the route was split across local residuals:

```text
diagonal domain candidate
finite support seed
submodule frontier
graph norm frontier
closed-operator frontier
formal adjoint frontier
```

That taxonomy is now historical.  It should not be read as the current top-level R2 status unless a PR is explicitly working inside one of those local subroutes.

Current public reading:

```text
R2 = infinite-dimensional completed ℓ² diagonal operator lane
```

not merely:

```text
R2 = old local residual taxonomy
```

## Proof-facing route

The current route is:

```text
ConcreteL2R1HilbertCarrier
  -> ConcreteL2R2DiagonalDomainCandidate
  -> finite-support domain/core
  -> graph-norm finite-support density
  -> graph-norm core release
  -> graph-closedness readiness promotion
  -> graph-closedness obligation promotion
  -> graph-closure closed theorem
  -> completed diagonal graph-defined closed operator
  -> completed Hilbert operator-norm unboundedness
  -> self-adjointness concrete preconditions
  -> R3 self-adjointness lane
```

## Important boundaries

The R2 lane now gives a genuine completed diagonal closed-operator and unboundedness surface.  It still does not by itself assert:

```text
symmetry theorem
adjoint-domain agreement theorem
resolvent / deficiency-index theorem
essential self-adjointness theorem
self-adjointness theorem
spectral theorem application
PVM construction
exact atom 33/20
positive spectral weight
```

Those are downstream R3--R7 surfaces or separately indexed terminal receipts.

## Review rule

For current R2 review, start from:

```text
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2InfiniteDiagonalOperatorLane.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundedness.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditions.lean
MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2R2PhysicalSpectralPromotionAuditChecklist.lean
```

Then trace back to the older local files only as needed.

## Relation to PR #157-style notes

When older PR text says that an old R2 taxonomy has been superseded by the R1--R7 receipt chain, read it as follows:

```text
old taxonomy = historical local decomposition
current R2 body = completed ℓ² diagonal operator lane
R1--R7 chain = terminal/public receipt route that consumes the current R2 body
```

This keeps R2 mathematically meaningful rather than reducing it to a label in the terminal receipt chain.
