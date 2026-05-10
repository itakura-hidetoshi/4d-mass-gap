# Phase 3: FinalAssembly Concrete Replacement Pass 1

This step applies the first status-to-theorem replacement checkpoint to the final assembly concrete readiness layer.

## Target

```text
MGAP4D/Global/FinalAssembly.lean
```

## Goal

Final assembly already connects:

```text
GlobalInputLedger
Global.TheoremSurface
Global.Concrete.SummarySurface
PublicClaimBoundary
```

This pass connects `FinalAssemblyConcreteReady` to the general replacement checkpoint:

```text
MGAP4D.ReplacementCheckpoint
```

## Scope

This pass does not remove existing status or assembly surfaces. It preserves them and adds a replacement-ready wrapper.

## Result

This closes the first status-to-theorem replacement pass across OperatorAPI, R1--R7 exits, Global/Concrete summary, and FinalAssembly concrete readiness.
