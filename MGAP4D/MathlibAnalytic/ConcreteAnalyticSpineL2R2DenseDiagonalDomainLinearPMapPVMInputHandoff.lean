import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff
import MGAP4D.MathlibAnalytic.PVMInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- PVM input handoff for the dense diagonal `LinearPMap` lane.

This layer connects the actual Mathlib self-adjoint dense diagonal `LinearPMap`
and the spectral input handoff to the certified PVM review surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface where
  spectralInputHandoffCertified :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified
  pvmReviewCertified :
    pvmReviewSurface.certified
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  exactValueInAtom :
    exactGapValueReal ∈ exactAtomPVMInterface.exactAtom
  exactAtomMassPositive :
    0 < exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom
  exactAtomMassNonzero :
    exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ≠ 0
  pvmInterfaceCertified :
    exactAtomPVMInterface.certified
  exactAtomDef :
    exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal
  exactAtomMassInPositiveRay :
    exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Concrete PVM input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface :=
  { spectralInputHandoffCertified :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_certified
    pvmReviewCertified :=
      pvm_review_surface_certified
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    exactValueInAtom :=
      exact_atom_pvm_interface_exact_value_in_atom
    exactAtomMassPositive :=
      exact_atom_pvm_interface_exact_atom_mass_positive
    exactAtomMassNonzero :=
      exact_atom_pvm_interface_exact_atom_mass_nonzero
    pvmInterfaceCertified :=
      exact_atom_pvm_interface_certified
    exactAtomDef :=
      rfl
    exactAtomMassInPositiveRay :=
      exact_atom_pvm_interface_exact_atom_mass_in_positive_ray }

/-- Public certification predicate for the dense diagonal `LinearPMap` PVM input
handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified ∧
  pvmReviewSurface.certified ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ exactAtomPVMInterface.exactAtom ∧
  0 < exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∧
  exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ≠ 0 ∧
  exactAtomPVMInterface.certified ∧
  exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal ∧
  exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified

/-- The dense diagonal `LinearPMap` PVM input handoff is certified. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_certified :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_certified,
    pvm_review_surface_certified,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    exact_atom_pvm_interface_exact_value_in_atom,
    exact_atom_pvm_interface_exact_atom_mass_positive,
    exact_atom_pvm_interface_exact_atom_mass_nonzero,
    exact_atom_pvm_interface_certified,
    rfl,
    exact_atom_pvm_interface_exact_atom_mass_in_positive_ray⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_certified

/-- Boundary marker for the PVM input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffCertified

/-- The PVM input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_certified

end

end MathlibAnalytic
end MGAP4D