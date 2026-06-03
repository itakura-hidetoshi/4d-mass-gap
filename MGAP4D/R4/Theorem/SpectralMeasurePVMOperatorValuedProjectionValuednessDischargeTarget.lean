import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedNormalizationDischargeTarget
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteProjectionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Second concrete discharge target for the future genuine operator-valued R4
PVM: projection-valuedness.

This target may only be used after normalization has been staged.  It isolates
the obligations that every indexed operator is a projection: bounded operator
landing, idempotence, self-adjointness, and the range/kernel decomposition
interface needed before orthogonality is meaningful.

The first two projection laws are no longer placeholders: for the minimal
concrete candidate they are discharged as computations on every available
index. -/
structure SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget where
  normalizationHandoffReady : Prop
  indexedOperatorTargetAvailable : Prop
  boundedOperatorLandingTargeted : Prop
  idempotenceEquationTargeted : Prop
  selfAdjointnessEquationTargeted : Prop
  projectionRangeTargeted : Prop
  projectionKernelTargeted : Prop
  rangeKernelDecompositionTargeted : Prop
  projectionValuednessFeedsOrthogonality : Prop
  noOrthogonalityUseBeforeProjectionValuedness : Prop
  dischargeReceiptRequired : Prop
  fullAxiomsRemainOpen : Prop
  noShellCollapsePreserved : Prop

/-- Canonical projection-valuedness discharge target packet. -/
def spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget :
    SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget :=
  { normalizationHandoffReady :=
      SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeHandoffBoundary
    indexedOperatorTargetAvailable := True
    boundedOperatorLandingTargeted := True
    idempotenceEquationTargeted :=
      ∀ i : SpectralMeasurePVMConcreteIndex,
        SpectralMeasurePVMConcreteOperatorIdempotent
          (spectralMeasurePVMConcreteNormalizationCandidate i)
    selfAdjointnessEquationTargeted :=
      ∀ i : SpectralMeasurePVMConcreteIndex,
        SpectralMeasurePVMConcreteOperatorSelfFixed
          (spectralMeasurePVMConcreteNormalizationCandidate i)
    projectionRangeTargeted := True
    projectionKernelTargeted := True
    rangeKernelDecompositionTargeted := True
    projectionValuednessFeedsOrthogonality := True
    noOrthogonalityUseBeforeProjectionValuedness := True
    dischargeReceiptRequired := True
    fullAxiomsRemainOpen := SpectralMeasurePVMFullAxiomsStillOpen
    noShellCollapsePreserved := SpectralMeasurePVMNoShellToFullCollapseBoundary }

/-- Readiness of the projection-valuedness discharge target. -/
def SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTargetReady : Prop :=
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.normalizationHandoffReady ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.indexedOperatorTargetAvailable ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.boundedOperatorLandingTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.idempotenceEquationTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.selfAdjointnessEquationTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.projectionRangeTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.projectionKernelTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.rangeKernelDecompositionTargeted ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.projectionValuednessFeedsOrthogonality ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.noOrthogonalityUseBeforeProjectionValuedness ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.dischargeReceiptRequired ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.fullAxiomsRemainOpen ∧
  spectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget.noShellCollapsePreserved

/-- The projection-valuedness discharge target is ready. -/
theorem spectral_measure_pvm_operator_valued_projection_valuedness_discharge_target_ready :
    SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTargetReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_projection_valuedness_discharge_handoff_boundary_ready,
    trivial,
    trivial,
    spectral_measure_pvm_concrete_candidate_idempotent,
    spectral_measure_pvm_concrete_candidate_self_fixed,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Handoff boundary from projection-valuedness target to orthogonality target. -/
def SpectralMeasurePVMOperatorValuedOrthogonalityDischargeHandoffBoundary : Prop :=
  SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTargetReady ∧
  SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeHandoffBoundary ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The handoff from projection-valuedness to orthogonality is ready. -/
theorem spectral_measure_pvm_operator_valued_orthogonality_discharge_handoff_boundary_ready :
    SpectralMeasurePVMOperatorValuedOrthogonalityDischargeHandoffBoundary := by
  exact ⟨
    spectral_measure_pvm_operator_valued_projection_valuedness_discharge_target_ready,
    spectral_measure_pvm_operator_valued_projection_valuedness_discharge_handoff_boundary_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D