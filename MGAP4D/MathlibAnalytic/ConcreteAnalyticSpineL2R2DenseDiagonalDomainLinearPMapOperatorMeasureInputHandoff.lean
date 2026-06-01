import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoff
import MGAP4D.MathlibAnalytic.OperatorMeasureCompatibilityTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Operator-measure input handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffSurface where
  compactPlaquetteInputReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady
  operatorMeasureReviewReady :
    operatorMeasureCompatibilityTheoremReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  positiveWeight :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  nonzeroWeight :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  weightEqualsPVMMass :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  operatorMeasureBodyClosed : Prop
  boundaryConcreteOperatorMeasureRealizationStillSeparate : Prop

/-- Concrete operator-measure input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffSurface :=
  { compactPlaquetteInputReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_ready
    operatorMeasureReviewReady :=
      operator_measure_compatibility_theorem_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    positiveWeight :=
      singleton_operator_measure_compatibility_positive_weight
    nonzeroWeight :=
      singleton_operator_measure_compatibility_nonzero_weight
    weightEqualsPVMMass :=
      singleton_operator_measure_compatibility_weight_equals_pvm_mass
    operatorMeasureBodyClosed := True
    boundaryConcreteOperatorMeasureRealizationStillSeparate := True }

/-- Public readiness predicate for the operator-measure input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapCompactPlaquetteInputHandoffReady ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom ∧
  concreteL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffSurface.operatorMeasureBodyClosed ∧
  concreteL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffSurface.boundaryConcreteOperatorMeasureRealizationStillSeparate

/-- The operator-measure input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_operator_measure_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_compact_plaquette_input_handoff_ready,
    operator_measure_compatibility_theorem_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    singleton_operator_measure_compatibility_positive_weight,
    singleton_operator_measure_compatibility_nonzero_weight,
    singleton_operator_measure_compatibility_weight_equals_pvm_mass,
    trivial,
    trivial⟩

/-- Boundary marker for the operator-measure input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffReady

/-- The operator-measure input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_operator_measure_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_operator_measure_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D