import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableFiniteAdditivityFinalReceipt
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableSetCountableBranch

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Symbolic spectral-integral value of the all-empty supported countable-union
branch is the zero slot. -/
theorem spectral_measure_pvm_finite_supported_measurable_countable_union_all_empty_spectral_integral_zero
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E) :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E) =
      SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_eq_empty E hE]
  exact spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_empty_slot

/-- Symbolic spectral-integral value of the pinned single-whole supported
countable-union branch is the identity slot. -/
theorem spectral_measure_pvm_finite_supported_measurable_countable_union_single_whole_spectral_integral_identity
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (k : Nat)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k) :
    spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k) =
      SpectralMeasurePVMSpectralIntegralSlot.identityIntegral := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_eq_whole E k hE]
  exact spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_whole_slot

/-- The all-empty branch is read by the local PVM surface as the empty branch at
both operator and symbolic-integral levels. -/
def SpectralMeasurePVMFiniteSupportedMeasurableAllEmptyBranchReadingTarget : Prop :=
  ∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E →
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E) =
        SpectralMeasurePVMConcreteBoundedOperator.zero ∧
      spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
          (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E) =
        SpectralMeasurePVMSpectralIntegralSlot.zeroIntegral

/-- The all-empty branch reading target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_all_empty_branch_reading_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableAllEmptyBranchReadingTarget := by
  intro E hE
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_operator_zero E hE,
    spectral_measure_pvm_finite_supported_measurable_countable_union_all_empty_spectral_integral_zero E hE⟩

/-- The pinned single-whole branch is read by the local PVM surface as the whole
branch at both operator and symbolic-integral levels. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSingleWholeBranchReadingTarget : Prop :=
  ∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    ∀ k : Nat,
      SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k →
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
            (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k) =
          SpectralMeasurePVMConcreteBoundedOperator.identity ∧
        spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
            (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k) =
          SpectralMeasurePVMSpectralIntegralSlot.identityIntegral

/-- The pinned single-whole branch reading target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_single_whole_branch_reading_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSingleWholeBranchReadingTarget := by
  intro E k hE
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_operator_identity E k hE,
    spectral_measure_pvm_finite_supported_measurable_countable_union_single_whole_spectral_integral_identity E k hE⟩

/-- Countable-branch reading target for the supported finite measurable local
surface.  This only covers the two explicitly supported local branches:
all-empty and pinned single-whole. -/
def SpectralMeasurePVMFiniteSupportedMeasurableCountableBranchReadingTarget : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableAllEmptyBranchReadingTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSingleWholeBranchReadingTarget

/-- The countable-branch reading target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_countable_branch_reading_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableCountableBranchReadingTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_target_ready,
    spectral_measure_pvm_finite_supported_measurable_all_empty_branch_reading_target_ready,
    spectral_measure_pvm_finite_supported_measurable_single_whole_branch_reading_target_ready⟩

/-- Bridge registering countable-branch reading for the supported finite
measurable local PVM surface. -/
def SpectralMeasurePVMFiniteSupportedMeasurableCountableBranchReadingBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableFiniteAdditivityPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSupportedMeasurableCountableBranchReadingTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalPVMReadingCertificateReady ∧
  SpectralMeasurePVMActualSpectralIntegralRealizationStillOpen ∧
  SpectralMeasurePVMSpectralIntegralSlotRealizationCompatibilityStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported finite measurable countable-branch reading bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_countable_branch_reading_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableCountableBranchReadingBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_finite_additivity_public_boundary_held,
    spectral_measure_pvm_finite_supported_measurable_countable_branch_reading_target_ready,
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_pvm_reading_certificate_ready,
    spectral_measure_pvm_actual_spectral_integral_realization_still_open_ready,
    spectral_measure_pvm_spectral_integral_slot_realization_compatibility_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
