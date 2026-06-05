import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableLocalSpectralTheoremFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A local spectral-measure candidate on the finite supported measurable surface.

This is the most concrete local object currently available for R4: a supported
measurable set class `{∅, univ}`, an actual finite measurable carrier, an
operator-valued assignment, local PVM laws, countable branch data, and symbolic
spectral-integral compatibility.  It is still not a genuine Borel PVM. -/
structure SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidate where
  SupportedSet : Type
  toSet : SupportedSet → SpectralMeasurePVMFiniteSetCarrier
  operatorValue : SupportedSet → SpectralMeasurePVMConcreteBoundedOperator
  integralSlot : SupportedSet → SpectralMeasurePVMSpectralIntegralSlot
  measurableTarget : Prop
  ovmLawTarget : Prop
  spectralIntegralTarget : Prop
  finalReceiptTarget : Prop
  noShellCollapse : Prop

/-- Concrete finite supported measurable spectral-measure candidate. -/
def spectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidate :
    SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidate where
  SupportedSet := SpectralMeasurePVMFiniteSupportedMeasurableSet
  toSet := spectralMeasurePVMFiniteSupportedMeasurableSetToSet
  operatorValue := spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
  integralSlot := spectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralSlot
  measurableTarget :=
    ∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
      @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
        spectralMeasurePVMFiniteSetCarrierMeasurableSpace
        (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)
  ovmLawTarget := SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMLawTarget
  spectralIntegralTarget :=
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget ∧
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget
  finalReceiptTarget :=
    SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremFinalReceiptReady
  noShellCollapse := SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Existence target for the finite supported measurable spectral-measure candidate. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidate

/-- The finite supported measurable spectral-measure candidate exists. -/
theorem spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_existence_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateExistenceTarget := by
  exact ⟨spectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidate⟩

/-- Laws packaged by the finite supported measurable spectral-measure candidate. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateLawTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet E)) ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalOVMLawTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralEndpointTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralIntegralIndicatorTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremFinalReceiptReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite supported measurable spectral-measure candidate law target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_law_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateLawTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_measurable,
    spectral_measure_pvm_finite_supported_measurable_local_ovm_law_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_endpoint_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_integral_indicator_target_ready,
    spectral_measure_pvm_finite_supported_measurable_local_spectral_theorem_final_receipt_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Bridge packaging the finite supported measurable local spectral-measure
candidate and preserving the genuine-PVM frontier. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableLocalSpectralTheoremPublicBoundaryHeld ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateExistenceTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateLawTarget ∧
  SpectralMeasurePVMFiniteMeasurableLocalPVMBundleReady ∧
  SpectralMeasurePVMOperatorValuedGenuinePVMTransitionCompletionFrontier ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite supported measurable spectral-measure candidate bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSpectralMeasureCandidateBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_local_spectral_theorem_public_boundary_held,
    spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_existence_target_ready,
    spectral_measure_pvm_finite_supported_measurable_spectral_measure_candidate_law_target_ready,
    spectral_measure_pvm_finite_measurable_local_pvm_bundle_ready,
    spectral_measure_pvm_operator_valued_genuine_pvm_transition_completion_frontier_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
