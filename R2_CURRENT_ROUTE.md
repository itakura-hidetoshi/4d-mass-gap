# R2 Current Route

This document records the current concrete `l2` R2 analytic route state after the narrow Lean umbrella was added, the legacy R2f graph-norm core blocker was closed, the residual-zero audit surface was added, and the completed diagonal unbounded-operator surface was consolidated.

## Lean import entries

Use the narrow route import rather than the full `MGAP4D.MathlibAnalytic` umbrella:

```lean
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CurrentRoute
```

For the residual-zero audit surface, use:

```lean
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ResidualZeroAuditSurface
```

For the consolidated completed diagonal unbounded-operator surface, use:

```lean
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalUnboundedOperatorSurface
```

The main theorem entry is:

```lean
concrete_l2_r2_current_route_ready
```

The R2f graph-norm core blocker closure theorem is:

```lean
concrete_l2_r2_current_route_graph_norm_core_blocker_closed
```

The residual-zero audit theorem is:

```lean
concrete_analytic_spine_l2_r2_residual_zero_audit_surface_ready
```

The consolidated completed diagonal unbounded-operator theorem is:

```lean
concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready
```

The boundary-preservation theorem is:

```lean
concrete_l2_r2_current_route_boundary_preserved
```

## Current route chain

```text
graph-norm finite-support density closed
  -> R2f graph-norm core blocker closed
  -> R2 analytic lane final precondition index ready
  -> R2 analytic lane release surface ready
  -> R2 top-level route index ready
  -> R2 current route umbrella ready
  -> R2 residual-zero audit surface ready
  -> completed diagonal unbounded-operator surface ready
```

## Closed / ready surfaces

```text
concrete_l2_r2_graph_norm_core_target_ready
concrete_l2_r2_current_route_graph_norm_core_blocker_closed
concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_density_closed
concrete_analytic_spine_l2_r2_analytic_lane_final_precondition_index_ready
concrete_analytic_spine_l2_r2_analytic_lane_release_surface_ready
concrete_analytic_spine_l2_r2_top_level_route_index_ready
concrete_l2_r2_current_route_ready
concrete_analytic_spine_l2_r2_residual_zero_audit_surface_ready
concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready
```

## Consolidated completed diagonal unbounded-operator surface

The consolidated surface packages the first non-placeholder operator-side route for item 2:

```text
completed diagonal graph carrier
+ graph-defined completed diagonal operator domain
+ completed diagonal single-valuedness theorem
+ chosen partial operator value
+ unit-domain growth certificate
```

Its unit-domain growth certificate has the form:

```text
for every threshold k,
there exists a domain point x with norm one such that
k < norm of the chosen completed diagonal partial-operator value at x.
```

This is stronger than a documentation-only placeholder and weaker than the completed closed-operator / self-adjoint spectral route.

## Boundary preserved

The current route umbrella, residual-zero audit surface, and consolidated completed diagonal unbounded-operator surface do not claim:

```text
completed diagonal closed graph theorem
completed Hilbert operator-norm theorem
self-adjointness theorem
spectral theorem
PVM construction
exact atom 33/20 derivation
positive spectral weight
physical Yang-Mills Hamiltonian
```

## Why this is not imported through the full root umbrella

A direct import into `MGAP4D/MathlibAnalytic.lean` was tested in PR #150 and closed in favor of this narrower route entry. The top-level route index itself had already passed Lean fast check in PR #149, and the narrow current-route umbrella passed Lean fast check in PR #151.

This keeps the full analytic umbrella stable while still exposing the R2 route state through dedicated route imports.
