import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusion

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
R2 additive-closure reduction for the dense-domain obligation.

The previous R2d lane proves that the finite-coordinate-submodule inclusion, and
therefore density of the diagonal-domain candidate, follows from one analytic
additive-closure target for the diagonal-domain candidate.
-/
def concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReduction : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoffSurfaceReady ∧
  concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady

/-- Readiness theorem for the R2 additive-closure reduction. -/
theorem concrete_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_ready :
    concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReduction := by
  unfold concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReduction
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_dense_domain_handoff_surface_ready,
    concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready⟩

/--
Additive closure is the remaining analytic target that releases the R2 dense
candidate target.
-/
def concreteL2MathlibSpectralAuditR2DenseDomainReleasedByAddClosure : Prop :=
  concreteL2R2DiagonalDomainCandidateAddClosureTarget →
    concreteL2R2DiagonalDomainCandidateDenseTarget

/-- The R2 dense-domain target is released by the additive-closure target. -/
theorem concrete_l2_mathlib_spectral_audit_r2_dense_domain_released_by_add_closure_ready :
    concreteL2MathlibSpectralAuditR2DenseDomainReleasedByAddClosure := by
  exact concrete_l2_r2_diagonal_domain_candidate_dense_target_ready_of_add_closure

/--
The finite-coordinate-submodule inclusion is also released by the same
additive-closure target.
-/
def concreteL2MathlibSpectralAuditR2SubmoduleInclusionReleasedByAddClosure : Prop :=
  concreteL2R2DiagonalDomainCandidateAddClosureTarget →
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate

/-- The submodule inclusion is released by additive closure. -/
theorem concrete_l2_mathlib_spectral_audit_r2_submodule_inclusion_released_by_add_closure_ready :
    concreteL2MathlibSpectralAuditR2SubmoduleInclusionReleasedByAddClosure := by
  exact concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate_of_add_closure

/--
Hard residual boundary: this reduction does not prove additive closure itself and
still does not construct an unbounded operator, graph-norm core, self-adjointness,
PVM, spectral atom, or positive spectral weight.
-/
def concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionHardResidualBoundaryHeld : Prop :=
  concreteL2MathlibSpectralAuditR2DenseDomainHandoffHardResidualBoundaryHeld ∧
  concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionHardResidualBoundaryHeld

/-- Hard residual boundary theorem for the R2 additive-closure reduction. -/
theorem concrete_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_hard_residual_boundary_held :
    concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionHardResidualBoundaryHeld := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_handoff_hard_residual_boundary_held,
    concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_hard_residual_boundary_held⟩

/-- Surface for the R2 dense-domain additive-closure reduction. -/
structure ConcreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurface where
  r2DenseDomainHandoffReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainHandoffSurfaceReady
  r2DomainInclusionReady :
    concreteAnalyticSpineL2R2FiniteCoordinateSubmoduleDomainInclusionSurfaceReady
  denseDomainReleasedByAddClosure :
    concreteL2MathlibSpectralAuditR2DenseDomainReleasedByAddClosure
  submoduleInclusionReleasedByAddClosure :
    concreteL2MathlibSpectralAuditR2SubmoduleInclusionReleasedByAddClosure
  hardResidualBoundaryHeld :
    concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionHardResidualBoundaryHeld

/-- Concrete R2 dense-domain additive-closure reduction surface. -/
def concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurface :
    ConcreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurface :=
  { r2DenseDomainHandoffReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_dense_domain_handoff_surface_ready
    r2DomainInclusionReady :=
      concrete_analytic_spine_l2_r2_finite_coordinate_submodule_domain_inclusion_surface_ready
    denseDomainReleasedByAddClosure :=
      concrete_l2_mathlib_spectral_audit_r2_dense_domain_released_by_add_closure_ready
    submoduleInclusionReleasedByAddClosure :=
      concrete_l2_mathlib_spectral_audit_r2_submodule_inclusion_released_by_add_closure_ready
    hardResidualBoundaryHeld :=
      concrete_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_hard_residual_boundary_held }

/-- Readiness predicate for the R2 additive-closure reduction surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReduction ∧
  concreteL2MathlibSpectralAuditR2DenseDomainReleasedByAddClosure ∧
  concreteL2MathlibSpectralAuditR2SubmoduleInclusionReleasedByAddClosure ∧
  concreteL2MathlibSpectralAuditR2DenseDomainAddClosureReductionHardResidualBoundaryHeld

/-- Readiness theorem for the R2 additive-closure reduction surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2DenseDomainAddClosureReductionSurfaceReady
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_ready,
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_released_by_add_closure_ready,
    concrete_l2_mathlib_spectral_audit_r2_submodule_inclusion_released_by_add_closure_ready,
    concrete_l2_mathlib_spectral_audit_r2_dense_domain_add_closure_reduction_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
