import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphSubmoduleNextPRBoundary

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
An explicit linear-closed-set surface for the concrete diagonal graph, stated
with the custom graph-pair operations from the R2 lane.

This is intentionally weaker than a mathlib `Submodule`: it packages the exact
zero/add/smul closure data already proved for the diagonal graph, without
claiming that the ambient graph-pair space has a typeclass-backed vector-space
structure.
-/
structure ConcreteL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurface where
  carrier : Set ConcreteL2GraphPairSpace
  carrier_eq : carrier = ConcreteL2DiagonalGraphL2Carrier
  zeroMem : concreteL2GraphPairZero ∈ carrier
  addClosure : ∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ carrier → q ∈ carrier → concreteL2GraphPairAdd p q ∈ carrier
  smulClosure : ∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ carrier → concreteL2GraphPairSmul c p ∈ carrier
  inheritedNextPRBoundary :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphSubmoduleNextPRBoundarySurfaceReady
  boundaryNotMathlibSubmodule :
    concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRSubmoduleObligation
  graphNormDensitySeparate : Prop

/-- Concrete explicit linear-closed-set surface for the diagonal graph. -/
def concreteL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurface :
    ConcreteL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurface :=
  { carrier := ConcreteL2DiagonalGraphL2Carrier
    carrier_eq := rfl
    zeroMem := concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_zero_mem
    addClosure := fun hp hq =>
      concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_add_closure hp hq
    smulClosure := fun c {p} hp =>
      concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_smul_closure c hp
    inheritedNextPRBoundary :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_boundary_surface_ready
    boundaryNotMathlibSubmodule :=
      concrete_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_submodule_obligation_held
    graphNormDensitySeparate :=
      concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRGraphNormDensitySeparate }

/--
Readiness predicate for the explicit linear-closed-set diagonal graph surface.
-/
def concreteAnalyticSpineL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphSubmoduleNextPRBoundarySurfaceReady ∧
  concreteL2GraphPairZero ∈ ConcreteL2DiagonalGraphL2Carrier ∧
  (∀ {p q : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      q ∈ ConcreteL2DiagonalGraphL2Carrier →
        concreteL2GraphPairAdd p q ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  (∀ (c : ℝ) {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2GraphPairSmul c p ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRSubmoduleObligation ∧
  concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRHardResidualBoundaryHeld

/-- Readiness theorem for the explicit linear-closed-set diagonal graph surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_explicit_linear_closed_graph_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2ExplicitLinearClosedGraphSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_boundary_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_zero_mem,
    concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_add_closure,
    concrete_l2_mathlib_spectral_audit_r2_diagonal_graph_smul_closure,
    concrete_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_submodule_obligation_held,
    concrete_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_hard_residual_boundary_held⟩

/--
The explicit linear-closed graph surface still separates mathlib Submodule
packaging from graph-norm density.
-/
def concreteL2MathlibSpectralAuditR2ExplicitLinearClosedGraphBoundaryHeld : Prop :=
  concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRSubmoduleObligation ∧
  concreteL2MathlibSpectralAuditR2GraphSubmoduleNextPRHardResidualBoundaryHeld

/-- Boundary theorem for the explicit linear-closed graph surface. -/
theorem concrete_l2_mathlib_spectral_audit_r2_explicit_linear_closed_graph_boundary_held :
    concreteL2MathlibSpectralAuditR2ExplicitLinearClosedGraphBoundaryHeld := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_submodule_obligation_held,
    concrete_l2_mathlib_spectral_audit_r2_graph_submodule_next_pr_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
