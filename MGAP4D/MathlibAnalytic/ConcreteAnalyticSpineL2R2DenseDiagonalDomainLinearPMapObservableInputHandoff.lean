import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoff
import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Observable input handoff for the dense diagonal `LinearPMap` lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface where
  pvmInputHandoffCertified :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified
  observableReviewCertified :
    observableAtomReviewSurface.certified
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  exactValueInAtom :
    exactGapValueReal ∈ exactAtomObservableInterface.atom
  positiveWeight :
    0 < exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom
  nonzeroWeight :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ≠ 0
  compatibleWithPVM :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom =
      exactAtomObservableInterface.pvm.projectionMass
        exactAtomObservableInterface.pvm.exactAtom
  observableInterfaceCertified :
    exactAtomObservableInterface.certified

/-- Concrete observable input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffSurface :=
  { pvmInputHandoffCertified :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_certified
    observableReviewCertified :=
      observable_atom_review_surface_certified
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    exactValueInAtom :=
      exact_atom_observable_interface_exact_in_atom
    positiveWeight :=
      exact_atom_observable_interface_positive_weight
    nonzeroWeight :=
      exact_atom_observable_interface_nonzero_weight
    compatibleWithPVM :=
      exact_atom_observable_interface_compatible_with_pvm
    observableInterfaceCertified :=
      exact_atom_observable_interface_certified }

/-- Public certification predicate for the dense diagonal `LinearPMap` observable input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffCertified : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified ∧
  observableAtomReviewSurface.certified ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ exactAtomObservableInterface.atom ∧
  0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0 ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom ∧
  exactAtomObservableInterface.certified

/-- Backward-compatible readiness name during downstream migration. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffCertified

/-- The dense diagonal `LinearPMap` observable input handoff is certified. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_certified :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffCertified := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_certified,
    observable_atom_review_surface_certified,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    exact_atom_observable_interface_exact_in_atom,
    exact_atom_observable_interface_positive_weight,
    exact_atom_observable_interface_nonzero_weight,
    exact_atom_observable_interface_compatible_with_pvm,
    exact_atom_observable_interface_certified⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffReady := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_certified

/-- Boundary marker for the observable input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffCertified

/-- The observable input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapObservableInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_observable_input_handoff_certified

end

end MathlibAnalytic
end MGAP4D