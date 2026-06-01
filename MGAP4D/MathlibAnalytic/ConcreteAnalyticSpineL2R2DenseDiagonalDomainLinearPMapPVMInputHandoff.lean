import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff
import MGAP4D.MathlibAnalytic.PVMInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- PVM input handoff for the dense diagonal `LinearPMap` lane.

This layer connects the actual Mathlib self-adjoint dense diagonal `LinearPMap`
and the spectral input handoff to the existing abstract PVM review surface.  It is
not a construction of the full projection-valued measure; it records that the PVM
lane now has the concrete self-adjoint operator input and the abstract singleton
PVM review surface available. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface where
  spectralInputHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady
  pvmReviewReady :
    pvmReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  exactValueInAtom :
    exactGapValueReal ∈ singletonPVMInterface.exactAtom
  exactAtomMassPositive :
    0 < singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom
  exactAtomMassNonzero :
    singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ≠ 0
  boundaryFullPVMTheoremStillSeparate : Prop
  boundaryProjectionMeasureConstructionStillSeparate : Prop
  boundaryPositiveSpectralWeightStillSeparate : Prop

/-- Concrete PVM input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface :=
  { spectralInputHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready
    pvmReviewReady :=
      pvm_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    exactValueInAtom :=
      singleton_pvm_interface_exact_value_in_atom
    exactAtomMassPositive :=
      singleton_pvm_interface_exact_atom_mass_positive
    exactAtomMassNonzero :=
      singleton_pvm_interface_exact_atom_mass_nonzero
    boundaryFullPVMTheoremStillSeparate := True
    boundaryProjectionMeasureConstructionStillSeparate := True
    boundaryPositiveSpectralWeightStillSeparate := True }

/-- Public readiness predicate for the dense diagonal `LinearPMap` PVM input
handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  pvmReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ singletonPVMInterface.exactAtom ∧
  0 < singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ∧
  singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ≠ 0 ∧
  concreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface.boundaryFullPVMTheoremStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface.boundaryProjectionMeasureConstructionStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- The dense diagonal `LinearPMap` PVM input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    pvm_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    singleton_pvm_interface_exact_value_in_atom,
    singleton_pvm_interface_exact_atom_mass_positive,
    singleton_pvm_interface_exact_atom_mass_nonzero,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker for the PVM input handoff.

The concrete dense diagonal `LinearPMap` has the actual Mathlib self-adjointness
and spectral input needed for a PVM lane.  Full PVM construction and positive
spectral-weight construction remain separate downstream obligations. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady

/-- The PVM input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D