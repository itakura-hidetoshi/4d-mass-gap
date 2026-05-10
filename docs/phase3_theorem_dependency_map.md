# Phase 3: Theorem Dependency Map

This step adds a checked Lean-side dependency map for the current theorem-surface chain.

## Purpose

The repository now has theorem-surface layers for:

```text
R1
R2
R3
R4
R5
R6
R7
Global
```

This dependency map records the intended proof-flow order and the key directed edges between these layers.

## Added Lean modules

```text
MGAP4D/DependencyMap.lean
MGAP4D/DependencyMap/TheoremChain.lean
MGAP4D/DependencyMap/SurfaceEdges.lean
MGAP4D/DependencyMap/GlobalRoute.lean
```

## Scope

This is still a minimal Lean step. It does not add Mathlib. It records dependency structure and gate surfaces that later concrete theorem modules can inhabit.

## Next step

After CI is green, add a local replay/declaration-count script and then consider the first small deferred-import restoration batch.
