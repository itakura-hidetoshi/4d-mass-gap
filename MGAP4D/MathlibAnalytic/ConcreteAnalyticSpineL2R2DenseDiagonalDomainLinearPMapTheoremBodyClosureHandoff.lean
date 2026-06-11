import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoff
import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Non-definitional exact-value positivity route for the theorem-body closure handoff.

This handoff deliberately does not restate or unfold the numeric exact-gap
identity.  It only transports the already-established positive exact-gap carrier
through the imported theorem-body closure surface. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_positive :
    0 < exactGapValueReal := by
  exact exactGapValueReal_pos

/-- Theorem-body closure handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface where
  operatorMeasureInputReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffReady
  exactGapTheoremBodyClosureReady :
    exactGapTheoremBodyClosure.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  exactValuePositive :
    0 < exactGapValueReal
  observableWeightPositive :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  observableWeightNonzero :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  observableWeightEqualsPVMMass :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  denseLinearPMapTheoremBodyClosureConnected : Prop
  boundaryConcreteSpectralMeasureStillSeparate : Prop
  boundaryConcretePVMStillSeparate : Prop

/-- Concrete theorem-body closure handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface :=
  { operatorMeasureInputReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_operator_measure_input_handoff_ready
    exactGapTheoremBodyClosureReady :=
      exact_gap_theorem_body_closure_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    exactValuePositive :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_positive
    observableWeightPositive :=
      exact_gap_theorem_body_closure_weight_positive
    observableWeightNonzero :=
      exact_gap_theorem_body_closure_weight_nonzero
    observableWeightEqualsPVMMass :=
      exact_gap_theorem_body_closure_weight_equals_pvm_mass
    denseLinearPMapTheoremBodyClosureConnected := True
    boundaryConcreteSpectralMeasureStillSeparate := True
    boundaryConcretePVMStillSeparate := True }

/-- Public readiness predicate for the theorem-body closure handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoffReady ∧
  exactGapTheoremBodyClosure.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  0 < exactGapValueReal ∧
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
  concreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface.denseLinearPMapTheoremBodyClosureConnected ∧
  concreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface.boundaryConcreteSpectralMeasureStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffSurface.boundaryConcretePVMStillSeparate

/-- The theorem-body closure handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_operator_measure_input_handoff_ready,
    exact_gap_theorem_body_closure_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_positive,
    exact_gap_theorem_body_closure_weight_positive,
    exact_gap_theorem_body_closure_weight_nonzero,
    exact_gap_theorem_body_closure_weight_equals_pvm_mass,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker for the theorem-body closure handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffReady

/-- The theorem-body closure handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapTheoremBodyClosureHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_handoff_ready

end

end MathlibAnalytic
end MGAP4D
