import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedProjectionValuednessDischargeTarget
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteOrthogonalityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Third concrete discharge target for the future genuine operator-valued R4
PVM: orthogonality for disjoint spectral sets.

This target may only be used after projection-valuedness has been staged.  It
isolates the obligations that disjoint indexed projections multiply to zero and
have orthogonal ranges before finite additivity is allowed to use them.

The product-zero directions are now discharged for the minimal two-index
concrete candidate.  Genuine Hilbert-range orthogonality remains downstream of
replacing the toy bounded-operator surface by a mathlib operator carrier. -/
structure SpectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget where
  projectionValuednessHandoffReady : Prop
  disjointIndexPairAvailable : Prop
  disjointnessHypothesisTargeted : Prop
  projectionProductZeroTargeted : Prop
  reversedProjectionProductZeroTargeted : Prop
  rangeOrthogonalityTargeted : Prop
  innerProductOrthogonalityTargeted : Prop
  pairwiseFamilyOrthogonalityTargeted : Prop
  orthogonalityFeedsFiniteAdditivity : Prop
  noFiniteAdditivityUseBeforeOrthogonality : Prop
  dischargeReceiptRequired : Prop
  fullAxiomsRemainOpen : Prop
  noShellCollapsePreserved : Prop

/-- Canonical orthogonality discharge target packet. -/
def spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget :
    SpectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget :=
  { projectionValuednessHandoffReady :=
      SpectralMeasurePVMOperatorValuedOrthogonalityDischargeHandoffBoundary
    disjointIndexPairAvailable := True
    disjointnessHypothesisTargeted := True
    projectionProductZeroTargeted :=
      SpectralMeasurePVMConcreteRangeOrthogonalityTarget
    reversedProjectionProductZeroTargeted :=
      SpectralMeasurePVMConcretePairwiseFamilyOrthogonalityTarget
    rangeOrthogonalityTargeted :=
      SpectralMeasurePVMConcreteRangeOrthogonalityTarget
    innerProductOrthogonalityTargeted :=
      SpectralMeasurePVMConcreteRangeOrthogonalityTarget
    pairwiseFamilyOrthogonalityTargeted :=
      SpectralMeasurePVMConcretePairwiseFamilyOrthogonalityTarget
    orthogonalityFeedsFiniteAdditivity := True
    noFiniteAdditivityUseBeforeOrthogonality := True
    dischargeReceiptRequired := True
    fullAxiomsRemainOpen := SpectralMeasurePVMFullAxiomsStillOpen
    noShellCollapsePreserved := SpectralMeasurePVMNoShellToFullCollapseBoundary }

/-- Readiness of the orthogonality discharge target. -/
def SpectralMeasurePVMOperatorValuedOrthogonalityDischargeTargetReady : Prop :=
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.projectionValuednessHandoffReady ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.disjointIndexPairAvailable ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.disjointnessHypothesisTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.projectionProductZeroTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.reversedProjectionProductZeroTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.rangeOrthogonalityTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.innerProductOrthogonalityTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.pairwiseFamilyOrthogonalityTargeted ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.orthogonalityFeedsFiniteAdditivity ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.noFiniteAdditivityUseBeforeOrthogonality ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.dischargeReceiptRequired ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.fullAxiomsRemainOpen ∧
  spectralMeasurePVMOperatorValuedOrthogonalityDischargeTarget.noShellCollapsePreserved

/-- The orthogonality discharge target is ready. -/
theorem spectral_measure_pvm_operator_valued_orthogonality_discharge_target_ready :
    SpectralMeasurePVMOperatorValuedOrthogonalityDischargeTargetReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_orthogonality_discharge_handoff_boundary_ready,
    trivial,
    trivial,
    spectral_measure_pvm_concrete_disjoint_product_zero,
    spectral_measure_pvm_concrete_disjoint_reversed_product_zero,
    spectral_measure_pvm_concrete_disjoint_product_zero,
    spectral_measure_pvm_concrete_disjoint_product_zero,
    spectral_measure_pvm_concrete_disjoint_reversed_product_zero,
    trivial,
    trivial,
    trivial,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Handoff boundary from orthogonality target to finite-additivity target. -/
def SpectralMeasurePVMOperatorValuedFiniteAdditivityDischargeHandoffBoundary : Prop :=
  SpectralMeasurePVMOperatorValuedOrthogonalityDischargeTargetReady ∧
  SpectralMeasurePVMOperatorValuedOrthogonalityDischargeHandoffBoundary ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The handoff from orthogonality to finite additivity is ready. -/
theorem spectral_measure_pvm_operator_valued_finite_additivity_discharge_handoff_boundary_ready :
    SpectralMeasurePVMOperatorValuedFiniteAdditivityDischargeHandoffBoundary := by
  exact ⟨
    spectral_measure_pvm_operator_valued_orthogonality_discharge_target_ready,
    spectral_measure_pvm_operator_valued_orthogonality_discharge_handoff_boundary_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D