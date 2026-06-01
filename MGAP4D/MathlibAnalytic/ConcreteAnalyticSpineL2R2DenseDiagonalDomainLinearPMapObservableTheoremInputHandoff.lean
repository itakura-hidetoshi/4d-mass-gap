import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoff
import MGAP4D.MathlibAnalytic.ObservableAtomTheoremTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Observable theorem input handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffSurface where
  observableInputHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady
  observableTheoremReviewReady :
    observableAtomTheoremTheoremReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  positiveWeight :
    0 < singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom
  nonzeroWeight :
    singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom ≠ 0
  compactSupportReady :
    singletonObservableAtomTheoremTheoremData.compactSupport
      singletonObservableAtomTheoremTheoremData.chosenObservable
  centeredReady :
    singletonObservableAtomTheoremTheoremData.centered
      singletonObservableAtomTheoremTheoremData.chosenObservable
  smearedReady :
    singletonObservableAtomTheoremTheoremData.smeared
      singletonObservableAtomTheoremTheoremData.chosenObservable
  boundaryConcretePlaquetteStillSeparate : Prop
  boundaryOperatorMeasureCompatibilityStillSeparate : Prop

/-- Concrete observable theorem input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffSurface :=
  { observableInputHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_ready
    observableTheoremReviewReady :=
      observable_atom_theorem_theorem_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    positiveWeight :=
      singleton_observable_atom_theorem_positive_weight
    nonzeroWeight :=
      singleton_observable_atom_theorem_nonzero_weight
    compactSupportReady :=
      singleton_observable_atom_theorem_compact_support
    centeredReady :=
      singleton_observable_atom_theorem_centered
    smearedReady :=
      singleton_observable_atom_theorem_smeared
    boundaryConcretePlaquetteStillSeparate := True
    boundaryOperatorMeasureCompatibilityStillSeparate := True }

/-- Public readiness predicate for the observable theorem input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  0 < singletonObservableAtomTheoremTheoremData.spectralWeight
    singletonObservableAtomTheoremTheoremData.chosenObservable
    singletonObservableAtomTheoremTheoremData.atom ∧
  singletonObservableAtomTheoremTheoremData.spectralWeight
    singletonObservableAtomTheoremTheoremData.chosenObservable
    singletonObservableAtomTheoremTheoremData.atom ≠ 0 ∧
  singletonObservableAtomTheoremTheoremData.compactSupport
    singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  singletonObservableAtomTheoremTheoremData.centered
    singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  singletonObservableAtomTheoremTheoremData.smeared
    singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  concreteL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffSurface.boundaryConcretePlaquetteStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffSurface.boundaryOperatorMeasureCompatibilityStillSeparate

/-- The observable theorem input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_theorem_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_ready,
    observable_atom_theorem_theorem_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    singleton_observable_atom_theorem_positive_weight,
    singleton_observable_atom_theorem_nonzero_weight,
    singleton_observable_atom_theorem_compact_support,
    singleton_observable_atom_theorem_centered,
    singleton_observable_atom_theorem_smeared,
    trivial,
    trivial⟩

/-- Boundary marker for the observable theorem input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffReady

/-- The observable theorem input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_theorem_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableTheoremInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_theorem_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D