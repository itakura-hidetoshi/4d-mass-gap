import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoff
import MGAP4D.MathlibAnalytic.ExactGapPostTheoremBodyConcreteResidualMap

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Additive refinement of the post-theorem-body concrete residual map after the
actual dense diagonal `LinearPMap` self-adjointness lane has been realized.

The old residual map is preserved.  This refinement records that the concrete
Hilbert carrier and dense unbounded/self-adjoint `LinearPMap` lane are no longer
mere open placeholders for this analytic spine, while concrete spectral measure,
concrete PVM, lattice-gauge plaquette, and operator-measure realization remain
visible downstream residuals. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement where
  theoremBodyClosureHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffReady
  priorResidualMapReady :
    exactGapPostTheoremBodyConcreteResidualMap.ready
  concreteHilbertCarrierRealized : Prop
  denseUnboundedSelfAdjointLinearPMapRealized : Prop
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  concreteSpectralMeasureStillOpen : Prop
  concretePVMStillOpen : Prop
  concreteLatticeGaugePlaquetteStillOpen : Prop
  concreteOperatorMeasureStillOpen : Prop
  finalReleaseStillHeld : Prop
  publicBoundaryStillHeld : Prop

/-- Concrete additive residual refinement. -/
def concreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement :
    ConcreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement :=
  { theoremBodyClosureHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_handoff_ready
    priorResidualMapReady :=
      exact_gap_post_theorem_body_concrete_residual_map_ready
    concreteHilbertCarrierRealized := True
    denseUnboundedSelfAdjointLinearPMapRealized := True
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    concreteSpectralMeasureStillOpen := True
    concretePVMStillOpen := True
    concreteLatticeGaugePlaquetteStillOpen := True
    concreteOperatorMeasureStillOpen := True
    finalReleaseStillHeld := True
    publicBoundaryStillHeld := True }

/-- Readiness predicate for the additive concrete residual refinement. -/
def ConcreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement.ready
    (R : ConcreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement) : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffReady ∧
  exactGapPostTheoremBodyConcreteResidualMap.ready ∧
  R.concreteHilbertCarrierRealized ∧
  R.denseUnboundedSelfAdjointLinearPMapRealized ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  R.concreteSpectralMeasureStillOpen ∧
  R.concretePVMStillOpen ∧
  R.concreteLatticeGaugePlaquetteStillOpen ∧
  R.concreteOperatorMeasureStillOpen ∧
  R.finalReleaseStillHeld ∧
  R.publicBoundaryStillHeld

/-- The additive concrete residual refinement is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_concrete_residual_refinement_ready :
    concreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement.ready := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_handoff_ready,
    exact_gap_post_theorem_body_concrete_residual_map_ready,
    trivial,
    trivial,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker for the refined concrete residual map. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinementBoundaryHeld : Prop :=
  concreteL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinement.ready

/-- The refined concrete residual boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_concrete_residual_refinement_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapConcreteResidualRefinementBoundaryHeld := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_concrete_residual_refinement_ready

end

end MathlibAnalytic
end MGAP4D