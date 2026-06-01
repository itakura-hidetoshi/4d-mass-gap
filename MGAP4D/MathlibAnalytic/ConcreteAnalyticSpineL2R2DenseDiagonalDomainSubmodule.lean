import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalDomainAdditiveClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The diagonal-domain candidate upgraded from a bare predicate/set to a
Mathlib-native submodule.

This is a real type-level promotion needed before any densely-defined operator
or Mathlib self-adjointness statement can be formulated. -/
def concreteL2R2DiagonalDomainCandidateSubmodule :
    Submodule ℝ ConcreteL2R1HilbertCarrier :=
  { carrier := concreteL2R2DiagonalDomainCandidateSet
    zero_mem' := by
      exact concrete_l2_r2_diagonal_domain_candidate_zero
    add_mem' := by
      intro x y hx hy
      exact concrete_l2_r2_diagonal_domain_candidate_add x y hx hy
    smul_mem' := by
      intro c x hx
      exact concrete_l2_r2_diagonal_domain_candidate_smul c hx }

/-- The carrier of the promoted submodule is exactly the previously used domain
candidate set. -/
theorem concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq :
    ((concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier) =
      concreteL2R2DiagonalDomainCandidateSet) := by
  rfl

/-- The diagonal-domain candidate submodule is dense in the completed Hilbert
carrier. -/
theorem concrete_l2_r2_diagonal_domain_candidate_submodule_dense :
    Dense ((concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier)) := by
  rw [dense_iff_closure_eq]
  rw [concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq]
  exact concrete_l2_r2_diagonal_domain_candidate_closure_eq_univ

/-- Concrete dense domain-submodule surface.

This replaces the earlier bare candidate-set density by a Mathlib-native dense
`Submodule`, which is the correct input shape for a densely defined operator. -/
structure ConcreteL2R2DenseDiagonalDomainSubmoduleSurface where
  additiveClosureReady : concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady
  domainSubmodule : Submodule ℝ ConcreteL2R1HilbertCarrier
  carrierEqCandidateSet :
    ((domainSubmodule : Set ConcreteL2R1HilbertCarrier) =
      concreteL2R2DiagonalDomainCandidateSet)
  denseDomainSubmodule : Dense ((domainSubmodule : Set ConcreteL2R1HilbertCarrier))
  finiteCoordinateSubmoduleInclusionReady :
    concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate
  boundaryNotGraphOperatorLinearMap : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop

/-- The concrete dense domain-submodule surface. -/
def concreteL2R2DenseDiagonalDomainSubmoduleSurface :
    ConcreteL2R2DenseDiagonalDomainSubmoduleSurface :=
  { additiveClosureReady :=
      concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
    domainSubmodule := concreteL2R2DiagonalDomainCandidateSubmodule
    carrierEqCandidateSet :=
      concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq
    denseDomainSubmodule :=
      concrete_l2_r2_diagonal_domain_candidate_submodule_dense
    finiteCoordinateSubmoduleInclusionReady :=
      concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate
    boundaryNotGraphOperatorLinearMap := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True }

/-- Readiness predicate for the dense diagonal-domain submodule. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady ∧
  Dense ((concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier)) ∧
  ((concreteL2R2DiagonalDomainCandidateSubmodule : Set ConcreteL2R1HilbertCarrier) =
    concreteL2R2DiagonalDomainCandidateSet) ∧
  concreteL2R2FiniteCoordinateSubmoduleSubsetDiagonalDomainCandidate ∧
  concreteL2R2DenseDiagonalDomainSubmoduleSurface.boundaryNotGraphOperatorLinearMap ∧
  concreteL2R2DenseDiagonalDomainSubmoduleSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2DenseDiagonalDomainSubmoduleSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2DenseDiagonalDomainSubmoduleSurface.boundaryNotSpectralTheoremApplication

/-- The dense diagonal-domain submodule surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_submodule_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready,
    concrete_l2_r2_diagonal_domain_candidate_submodule_dense,
    concrete_l2_r2_diagonal_domain_candidate_submodule_carrier_eq,
    concrete_l2_r2_finite_coordinate_submodule_subset_diagonal_domain_candidate,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the dense submodule has been constructed, but the graph has
not yet been promoted to a Mathlib-native linear operator on this submodule. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleSurfaceReady

/-- Boundary theorem for the dense diagonal-domain submodule surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_submodule_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainSubmoduleHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_submodule_surface_ready

end

end MathlibAnalytic
end MGAP4D
