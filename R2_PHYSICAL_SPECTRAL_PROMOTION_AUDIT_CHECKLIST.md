# R2 Physical Spectral Promotion Audit Checklist

This document records the promotion checklist for moving from the current R2 residual-zero audit surface to any future physical spectral claim.

The current state remains an audit/checklist surface only. It does not claim the closed operator theorem, self-adjointness theorem, spectral theorem, PVM construction, exact atom `33/20` derivation, positive spectral weight, or the physical Yang--Mills Hamiltonian.

## Lean import entry

```lean
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2PhysicalSpectralPromotionAuditChecklist
```

## Theorem entry

```lean
concrete_analytic_spine_l2_r2_physical_spectral_promotion_audit_checklist_ready
```

## Current Lean surface note

The Lean checklist surface is intentionally minimized: it connects the currently available R2 surfaces and represents the remaining boundary slots as `True` placeholders. This avoids projection fragility while preserving the promotion boundary.

## Inherited route state

```text
graph-norm finite-support density closed
  -> R2f graph-norm core blocker closed
  -> R2 analytic lane final precondition index ready
  -> R2 analytic lane release surface ready
  -> R2 top-level route index ready
  -> R2 current route umbrella ready
  -> R2 residual-zero audit surface ready
  -> R2 physical spectral promotion audit checklist ready
  -> R2 graph-norm finite-support density ready
  -> R2 graph-norm core release ready
  -> R2 graph-closedness readiness promotion ready
  -> R2 graph-closedness obligation promotion ready
  -> R2 graph-norm closure carrier closed theorem ready
```

## Promotion checklist

```text
[x] Concrete real Hilbert space
    Supplied by: concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready

[x] Densely defined operator surface
    Supplied by: concrete_analytic_spine_l2_r2_densely_defined_operator_ready
    Boundary: nontrivial unboundedness is not asserted here.

[x] Finite-support core surface
    Supplied by: concrete_analytic_spine_l2_r2_finite_support_core_ready

[x] Graph-norm finite-support density
    Supplied by: concrete_analytic_spine_l2_r2_graph_norm_finite_support_density_ready

[x] Graph-norm core release
    Supplied by: concrete_analytic_spine_l2_r2_graph_norm_core_release_ready

[x] Graph-closedness readiness
    Supplied by: concrete_analytic_spine_l2_r2_graph_closedness_readiness_promotion_ready

[x] Graph-closedness / closure-uniqueness obligations
    Supplied by: concrete_analytic_spine_l2_r2_graph_closedness_obligation_promotion_ready

[x] Graph-norm closure carrier is closed
    Supplied by: concrete_analytic_spine_l2_r2_graph_closure_closed_theorem_ready
    Boundary: this is the closedness of the closure carrier, not yet diagonal graph closedness.

[ ] Diagonal graph equals closure
    Required before promoting diagonal graph closedness.

[ ] Graph-closedness theorem
    Required before promoting the closed-operator theorem.

[ ] Closure-uniqueness theorem
    Required before promoting the closed-operator theorem.

[ ] Closed operator theorem
    Required before self-adjointness or spectral theorem promotion.

[ ] Nontrivial unboundedness theorem
    Required to distinguish the concrete route from the full-domain bounded zero-operator surface.

[ ] Essential/self-adjointness proof
    Required: adjoint-domain equality or essentially self-adjoint core closure.

[ ] PVM / spectral measure
    Required: spectral theorem bridge and singleton spectral projection E({33/20}).

[ ] Compact centered plaquette observable
    Required: compact/finite support, centeredness, vacuum orthogonality, nonzero excitation.

[ ] Non-definitional exact atom 33/20
    Required: 33/20 derived from local/block/finite computation or equivalent analytic mechanism.

[ ] Nontrivial positive spectral weight
    Required: E({33/20}) psi_A != 0 or equivalent overlap proof.
```

## Boundary preserved

This checklist does not promote any of the following surfaces:

```text
diagonal graph equals closure
diagonal graph closedness
closed operator theorem
self-adjointness theorem
spectral theorem
PVM construction
exact atom 33/20 derivation
positive spectral weight
physical Yang-Mills Hamiltonian
```

## Next Lean target

The next non-documentation Lean target is the diagonal-graph-equals-closure bridge. Once that bridge is available, graph-norm closure carrier closedness can be transported to diagonal graph closedness, which is the natural predecessor of the closed-operator theorem.
