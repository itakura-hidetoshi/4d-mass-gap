import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditRealHilbertProjection
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomain

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
R2 handoff for the dense-domain obligation in the spectral audit checklist.

This bridge uses the previous R2 topology lane: finite-support density plus the
conditional diagonal-domain-candidate handoff.  It does not claim an unbounded
operator, graph-norm core, self-adjointness, PVM, spectral atom, or positive
spectral weight theorem.
-/
def concreteL2MathlibSpectralAuditR2DenseDomainHandoff : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditRealHilbertProjectionSurfaceReady ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady ∧
  concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady

/-- Readiness theorem for the R2 dense-domain handoff. -/
theorem concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_ready :
    concreteL2MathlibSpectralAuditR2DenseDomainHandoff := by
  unfold concreteL2MathlibSpectralAuditR2DenseDomainHandoff
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_real_hilbert_projection_surface_ready,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready,
    concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready⟩

/--
The R2 dense-domain handoff exposes the conditional law that the diagonal-domain
candidate is dense once the finite-coordinate-submodule inclusion is supplied.
-/
def concreteL2MathlibSpectralAuditR2ConditionalDenseDomainLaw : Prop :=
  concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate →
    concreteL2R2DiagonalDomainCandidateDenseTarget

/-- The conditional dense-domain law is available from the previous R2 handoff. -/
theorem concrete_l2_mathlib_spectral_audit_r2_conditional_dense_domain_law_ready :
    concreteL2MathlibSpectralAuditR2ConditionalDenseDomainLaw := by
  exact concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_finite_coordinate_submodule_subset

/--
R2 finite-combination domain law, reused directly from the earlier R2 finite
support proof.
-/
def concreteL2MathlibSpectralAuditR2FiniteCombinationDomainLaw : Prop :=
  concreteL2R2FiniteCoordinateCombinationDomainMembershipAdapter

/-- The R2 finite-combination domain law is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_combination_domain_law_ready :
    concreteL2MathlibSpectralAuditR2FiniteCombinationDomainLaw := by
  exact concrete_l2_r2_finite_coordinate_combination_domain_membership_adapter_ready

/--
The R2 dense-domain handoff keeps all stronger spectral obligations unreleased.
-/
def concreteL2MathlibSpectralAuditR2DenseDomainHandoffHardResidualBoundaryHeld : Prop :=
  concreteL2MathlibSpectralAuditRealHilbertProjectionHardResidualBoundaryHeld ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffHardResidualBoundaryHeld ∧
  concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainHardResidualBoundaryHeld

/-- Hard residual boundary for the R2 dense-domain handoff. -/
theorem concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_hard_residual_boundary_held :
    concreteL2MathlibSpectralAuditR2DenseDomainHandoffHardResidualBoundaryHeld := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_real_hilbert_projection_hard_residual_boundary_held,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_hard_residual_boundary_held,
    concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_hard_residual_boundary_held⟩

/-- Surface for the R2 dense-domain handoff into the spectral audit checklist. -/
structure ConcreteL2MathlibSpectralAuditR2DenseDomainHandoffSurface where
  realHilbertProjectionReady :
    concreteAnalyticSpineL2MathlibSpectralAuditRealHilbertProjectionSurfaceReady
  r2DenseDiagonalDomainCandidateHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainCandidateHandoffSurfaceReady
  r2FiniteCoordinateCombinationsInDomainReady :
    concreteAnalyticSpineL2R2FiniteCoordinateCombinationsInDomainSurfaceReady
  conditionalDenseDomainLaw : concreteL2MathlibSpectralAuditR2ConditionalDenseDomainLaw
  finiteCombinationDomainLaw : concreteL2MathlibSpectralAuditR2FiniteCombinationDomainLaw
  hardResidualBoundaryHeld :
    concreteL2MathlibSpectralAuditR2DenseDomainHandoffHardResidualBoundaryHeld

/-- Concrete R2 dense-domain handoff surface. -/
def concreteL2MathlibSpectralAuditR2DenseDomainHandoffSurface :
    ConcreteL2MathlibSpectralAuditR2DenseDomainHandoffSurface :=
  { realHilbertProjectionReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_real_hilbert_projection_surface_ready
    r2DenseDiagonalDomainCandidateHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_candidate_handoff_surface_ready
    r2FiniteCoordinateCombinationsInDomainReady :=
      concrete_analytic_spine_l2_r2_finite_coordinate_combinations_in_domain_surface_ready
    conditionalDenseDomainLaw :=
      concrete_l2_mathlib_spectral_audit_r2_conditional_dense_domain_law_ready
    finiteCombinationDomainLaw :=
      concrete_l2_mathlib_spectral_audit_r2_finite_combination_domain_law_ready
    hardResidualBoundaryHeld :=
      concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_hard_residual_boundary_held }

/-- Readiness predicate for the R2 dense-domain handoff surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoffSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2DenseDomainHandoff ∧
  concreteL2MathlibSpectralAuditR2ConditionalDenseDomainLaw ∧
  concreteL2MathlibSpectralAuditR2FiniteCombinationDomainLaw ∧
  concreteL2MathlibSpectralAuditR2DenseDomainHandoffHardResidualBoundaryHeld

/-- Readiness theorem for the R2 dense-domain handoff surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_dense_domain_handoff_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoffSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoffSurfaceReady
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_ready,
    concrete_l2_mathlib_spectral_audit_r2_conditional_dense_domain_law_ready,
    concrete_l2_mathlib_spectral_audit_r2_finite_combination_domain_law_ready,
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
