import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoff
import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Observable input handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface where
  pvmInputHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady
  observableReviewReady :
    observableAtomReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  exactValueInAtom :
    exactGapValueReal ∈ singletonObservableAtomInterface.atom
  positiveWeight :
    0 < singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom
  nonzeroWeight :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ≠ 0
  compatibleWithPVM :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom =
      singletonObservableAtomInterface.pvm.projectionMass
        singletonObservableAtomInterface.pvm.exactAtom
  boundaryObservableTheoremStillSeparate : Prop

/-- Concrete observable input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface :=
  { pvmInputHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready
    observableReviewReady :=
      observable_atom_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    exactValueInAtom :=
      singleton_observable_atom_interface_exact_in_atom
    positiveWeight :=
      singleton_observable_atom_interface_positive_weight
    nonzeroWeight :=
      singleton_observable_atom_interface_nonzero_weight
    compatibleWithPVM :=
      singleton_observable_atom_interface_compatible_with_pvm
    boundaryObservableTheoremStillSeparate := True }

/-- Public readiness predicate for the dense diagonal `LinearPMap` observable input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  observableAtomReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ singletonObservableAtomInterface.atom ∧
  0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0 ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  concreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface.boundaryObservableTheoremStillSeparate

/-- The dense diagonal `LinearPMap` observable input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready,
    observable_atom_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    singleton_observable_atom_interface_exact_in_atom,
    singleton_observable_atom_interface_positive_weight,
    singleton_observable_atom_interface_nonzero_weight,
    singleton_observable_atom_interface_compatible_with_pvm,
    trivial⟩

/-- Boundary marker for the observable input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady

/-- The observable input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D