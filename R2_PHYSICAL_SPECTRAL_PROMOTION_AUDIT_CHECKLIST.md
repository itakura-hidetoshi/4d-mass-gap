# R2 Physical Spectral Promotion Audit Checklist

This document records the promotion checklist for moving from the current R2 residual-zero audit surface to any future physical spectral claim.

The current state remains an audit/checklist surface only.  It does not claim the closed operator theorem, self-adjointness theorem, spectral theorem, PVM construction, exact atom `33/20` derivation, positive spectral weight, or the physical Yang--Mills Hamiltonian.

## Lean import entry

```lean
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2PhysicalSpectralPromotionAuditChecklist
```

## Theorem entry

```lean
concrete_analytic_spine_l2_r2_physical_spectral_promotion_audit_checklist_ready
```

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
```

## Promotion checklist

```text
[ ] Concrete real Hilbert space
    Required: l2-type or Mathlib-standard Hilbert space.

[ ] Densely defined unbounded operator
    Required: explicit domain, dense domain proof, graph norm/core control.

[ ] Self-adjointness
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
closed operator theorem
self-adjointness theorem
spectral theorem
PVM construction
exact atom 33/20 derivation
positive spectral weight
physical Yang-Mills Hamiltonian
```

## Next Lean target

The next non-documentation Lean target should replace one checklist placeholder by an actual Mathlib-grounded theorem, preferably beginning with the concrete real Hilbert-space layer and then the densely defined operator/domain layer.
