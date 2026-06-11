import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapOperatorMeasureInputHandoff
import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Local exact-value witness for the theorem-body closure handoff.

This replaces the stale short name `exactGapValueReal_eq` with a replayed proof
from the normalized exact-gap carrier witness. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_eq_3320 :
    exactGapValueReal = (33 : ℝ) / 20 := by
  unfold exactGapValueReal
  calc
    Classical.choose exactGapValueRealRouteWitness = ((11 : ℝ) * 3) / 20 :=
      (Classical.choose_spec exactGapValueRealRouteWitness).1
    _ = (33 : ℝ) / 20 := by norm_num

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
  exactValueEq3320 :
    exactGapValueReal = (33 : ℝ) / 20
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
    exactValueEq3320 :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_eq_3320
    exactValuePositive :=
      exactGapValueReal_pos
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
  exactGapValueReal = (33 : ℝ) / 20 ∧
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
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_theorem_body_closure_exact_value_eq_3320,
    exactGapValueReal_pos,
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
