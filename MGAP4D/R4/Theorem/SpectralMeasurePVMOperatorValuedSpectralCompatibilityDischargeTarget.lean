import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTarget
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteSpectralCompatibilityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Sixth concrete discharge target for the future genuine operator-valued R4
PVM: compatibility with a self-adjoint spectral resolution.

This target may only be used after countable additivity has been staged.  It
isolates the bridge from a sigma-additive projection-valued measure candidate to
a spectral resolution for the intended self-adjoint operator.  Functional
calculus remains a later discharge target.

At the current two-index concrete stage, the spectral operator is the identity
constructor, the spectral projection family is the already-defined concrete PVM
candidate, and compatibility is closed by computation on the zero/identity
operator table. -/
structure SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget where
  countableAdditivityHandoffReady : Prop
  selfAdjointOperatorTargetAvailable : Prop
  spectralProjectionFamilyTargeted : Prop
  spectralResolutionEquationTargeted : Prop
  supportCompatibilityTargeted : Prop
  commutingProjectionFamilyTargeted : Prop
  operatorIntegralInterfaceTargeted : Prop
  identityFunctionRecoveryTargeted : Prop
  spectralCompatibilityFeedsFunctionalCalculus : Prop
  noFunctionalCalculusUseBeforeSpectralCompatibility : Prop
  dischargeReceiptRequired : Prop
  fullAxiomsRemainOpen : Prop
  noShellCollapsePreserved : Prop

/-- Canonical spectral-compatibility discharge target packet. -/
def spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget :
    SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget :=
  { countableAdditivityHandoffReady :=
      SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeHandoffBoundary
    selfAdjointOperatorTargetAvailable :=
      SpectralMeasurePVMConcreteSelfAdjointOperatorTarget
    spectralProjectionFamilyTargeted :=
      SpectralMeasurePVMConcreteSpectralProjectionFamilyTarget
    spectralResolutionEquationTargeted :=
      SpectralMeasurePVMConcreteSpectralResolutionEquationTarget
    supportCompatibilityTargeted :=
      SpectralMeasurePVMConcreteSupportCompatibilityTarget
    commutingProjectionFamilyTargeted :=
      SpectralMeasurePVMConcreteCommutingProjectionFamilyTarget
    operatorIntegralInterfaceTargeted :=
      SpectralMeasurePVMConcreteOperatorIntegralInterfaceTarget
    identityFunctionRecoveryTargeted :=
      SpectralMeasurePVMConcreteIdentityFunctionRecoveryTarget
    spectralCompatibilityFeedsFunctionalCalculus :=
      SpectralMeasurePVMConcreteSpectralCompatibilityFeedsFunctionalCalculusTarget
    noFunctionalCalculusUseBeforeSpectralCompatibility :=
      SpectralMeasurePVMConcreteNoFunctionalCalculusUseBeforeSpectralCompatibilityTarget
    dischargeReceiptRequired :=
      SpectralMeasurePVMConcreteSpectralCompatibilityDischargeReceiptTarget
    fullAxiomsRemainOpen := SpectralMeasurePVMFullAxiomsStillOpen
    noShellCollapsePreserved := SpectralMeasurePVMNoShellToFullCollapseBoundary }

/-- Readiness of the spectral-compatibility discharge target. -/
def SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTargetReady : Prop :=
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.countableAdditivityHandoffReady ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.selfAdjointOperatorTargetAvailable ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.spectralProjectionFamilyTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.spectralResolutionEquationTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.supportCompatibilityTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.commutingProjectionFamilyTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.operatorIntegralInterfaceTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.identityFunctionRecoveryTargeted ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.spectralCompatibilityFeedsFunctionalCalculus ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.noFunctionalCalculusUseBeforeSpectralCompatibility ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.dischargeReceiptRequired ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.fullAxiomsRemainOpen ∧
  spectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTarget.noShellCollapsePreserved

/-- The spectral-compatibility discharge target is ready. -/
theorem spectral_measure_pvm_operator_valued_spectral_compatibility_discharge_target_ready :
    SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTargetReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_spectral_compatibility_discharge_handoff_boundary_ready,
    spectral_measure_pvm_concrete_self_adjoint_operator_target_ready,
    spectral_measure_pvm_concrete_spectral_projection_family_target_ready,
    spectral_measure_pvm_concrete_spectral_resolution_equation_target_ready,
    spectral_measure_pvm_concrete_support_compatibility_target_ready,
    spectral_measure_pvm_concrete_commuting_projection_family_target_ready,
    spectral_measure_pvm_concrete_operator_integral_interface_target_ready,
    spectral_measure_pvm_concrete_identity_function_recovery_target_ready,
    spectral_measure_pvm_concrete_spectral_compatibility_feeds_functional_calculus_target_ready,
    spectral_measure_pvm_concrete_no_functional_calculus_use_before_spectral_compatibility_target_ready,
    spectral_measure_pvm_concrete_spectral_compatibility_discharge_receipt_target_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Handoff boundary from spectral compatibility target to functional calculus target. -/
def SpectralMeasurePVMOperatorValuedFunctionalCalculusDischargeHandoffBoundary : Prop :=
  SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeTargetReady ∧
  SpectralMeasurePVMOperatorValuedSpectralCompatibilityDischargeHandoffBoundary ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The handoff from spectral compatibility to functional calculus is ready. -/
theorem spectral_measure_pvm_operator_valued_functional_calculus_discharge_handoff_boundary_ready :
    SpectralMeasurePVMOperatorValuedFunctionalCalculusDischargeHandoffBoundary := by
  exact ⟨
    spectral_measure_pvm_operator_valued_spectral_compatibility_discharge_target_ready,
    spectral_measure_pvm_operator_valued_spectral_compatibility_discharge_handoff_boundary_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
