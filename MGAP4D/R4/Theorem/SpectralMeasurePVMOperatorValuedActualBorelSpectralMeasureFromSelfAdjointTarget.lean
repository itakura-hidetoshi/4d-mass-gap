import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelGenuineCountableAdditivityBoundaryCertificateSigmaCarrierHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoff

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- External-review law profile for the R4 actual-Borel spectral-measure step.

This structure does not pretend that the genuine spectral theorem has already
been discharged.  It makes the reviewer-facing target explicit: an arbitrary
Borel index `SpectralMeasurePVMActualBorelCarrierSet`, a projection-valued
output shell, normalization/projection/countable-additivity law slots, and a
concrete self-adjoint `LinearPMap` input. -/
structure SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget where
  borelIndex : Type
  projectionTarget : Type
  spectralMeasureCandidate : borelIndex → projectionTarget
  selfAdjointInputReady :
    MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady
  actualSelfAdjoint :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap
  arbitraryBorelIndex : borelIndex = SpectralMeasurePVMActualBorelCarrierSet
  targetProjectionShell : projectionTarget = SpectralMeasurePVMTargetProjectionType
  emptySetNormalizationLaw : Prop
  wholeSpaceNormalizationLaw : Prop
  projectionValuedLaw : Prop
  disjointOrthogonalityLaw : Prop
  countableAdditivityOnPairwiseDisjointBorelLaw : Prop
  spectralTheoremCompatibilityLaw : Prop
  genuineCountableAdditivityBoundary :
    SpectralMeasurePVMActualBorelGenuineCountableAdditivityBoundaryCertificateSigmaCarrierHandoffPublicBoundaryHeld
  genuineCountableAdditivityStillOpen :
    SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
  genuineSelfAdjointSpectralTheoremStillOpen :
    SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen
  genuineSpectralMeasureConstructionStillOpen :
    SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen
  noShellToFullCollapse : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Projection shell used by the actual-Borel spectral-measure target. -/
def spectralMeasurePVMActualBorelSpectralMeasureProjectionShell
    (_ : SpectralMeasurePVMActualBorelCarrierSet) :
    SpectralMeasurePVMTargetProjectionType :=
  { obligationTag := SpectralMeasurePVMObligationTag.spectralTheoremCompatibility
    stageLabel := "actual-borel-spectral-measure-from-self-adjoint-target" }

/-- Canonical reviewer-facing R4 target for a genuine Borel spectral measure from
an actual self-adjoint operator input.

The law fields are intentionally retained as explicit obligations rather than
collapsed to theorem claims. This prevents the finite/local PVM receipt from
being mistaken for a fully discharged countably additive Borel PVM. -/
def spectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget :
    SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget :=
  { borelIndex := SpectralMeasurePVMActualBorelCarrierSet
    projectionTarget := SpectralMeasurePVMTargetProjectionType
    spectralMeasureCandidate :=
      spectralMeasurePVMActualBorelSpectralMeasureProjectionShell
    selfAdjointInputReady :=
      MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready
    actualSelfAdjoint :=
      MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    arbitraryBorelIndex := rfl
    targetProjectionShell := rfl
    emptySetNormalizationLaw :=
      SpectralMeasurePVMObligationMapReady
    wholeSpaceNormalizationLaw :=
      SpectralMeasurePVMObligationMapReady
    projectionValuedLaw :=
      SpectralMeasurePVMObligationMapReady
    disjointOrthogonalityLaw :=
      SpectralMeasurePVMObligationMapReady
    countableAdditivityOnPairwiseDisjointBorelLaw :=
      SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
    spectralTheoremCompatibilityLaw :=
      SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen
    genuineCountableAdditivityBoundary :=
      spectral_measure_pvm_actual_borel_genuine_countable_additivity_boundary_certificate_sigma_carrier_handoff_public_boundary_held
    genuineCountableAdditivityStillOpen :=
      spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready
    genuineSelfAdjointSpectralTheoremStillOpen :=
      spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready
    genuineSpectralMeasureConstructionStillOpen :=
      spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready
    noShellToFullCollapse :=
      spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready }

/-- The R4 actual-Borel spectral-measure target has arbitrary Borel sets as its
index type and receives the concrete self-adjoint operator input. -/
def SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTargetReady : Prop :=
  spectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget.borelIndex =
    SpectralMeasurePVMActualBorelCarrierSet ∧
  spectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget.projectionTarget =
    SpectralMeasurePVMTargetProjectionType ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapPVMInputHandoffReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  SpectralMeasurePVMActualBorelGenuineCountableAdditivityBoundaryCertificateSigmaCarrierHandoffPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The reviewer-facing R4 actual-Borel spectral-measure target is ready. -/
theorem spectral_measure_pvm_actual_borel_spectral_measure_from_self_adjoint_target_ready :
    SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTargetReady := by
  exact ⟨
    rfl,
    rfl,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_pvm_input_handoff_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    spectral_measure_pvm_actual_borel_genuine_countable_additivity_boundary_certificate_sigma_carrier_handoff_public_boundary_held,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection: the target is indexed by arbitrary actual Borel subsets of `ℝ`,
not merely finite-supported/local slots. -/
theorem spectral_measure_pvm_actual_borel_spectral_measure_target_arbitrary_borel_index :
    spectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTarget.borelIndex =
      SpectralMeasurePVMActualBorelCarrierSet := by
  rfl

/-- Projection: the target is fed by the concrete self-adjoint dense diagonal
`LinearPMap` lane. -/
theorem spectral_measure_pvm_actual_borel_spectral_measure_target_self_adjoint_input :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

/-- Public boundary: this target advances R4 from finite/local PVM receipts to an
actual-Borel, self-adjoint-operator-facing spectral-measure target, while keeping
the full countably additive PVM construction visibly open. -/
def SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointTargetReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the actual-Borel spectral-measure target is held. -/
theorem spectral_measure_pvm_actual_borel_spectral_measure_from_self_adjoint_public_boundary_held :
    SpectralMeasurePVMActualBorelSpectralMeasureFromSelfAdjointPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_spectral_measure_from_self_adjoint_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
