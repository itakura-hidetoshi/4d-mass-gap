import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierMeasurableRealizationBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- In the finite carrier with the discrete/top measurable structure, every
explicit countable union hosted by the finite `Set` carrier is measurable. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_measurable
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSetCarrierCountableUnion F) := by
  trivial

/-- The all-empty countable-union branch is measurable on the finite carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_all_empty_measurable
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier)
    (_hF : SpectralMeasurePVMFiniteSetCarrierAllEmptyFamily F) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSetCarrierCountableUnion F) := by
  exact spectral_measure_pvm_finite_set_carrier_countable_union_measurable F

/-- The pinned single-whole countable-union branch is measurable on the finite carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_single_whole_measurable
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier)
    (k : Nat)
    (_hF : SpectralMeasurePVMFiniteSetCarrierSingleWholeAt F k) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSetCarrierCountableUnion F) := by
  exact spectral_measure_pvm_finite_set_carrier_countable_union_measurable F

/-- Measurable countable-union target for the finite carrier. -/
def SpectralMeasurePVMFiniteSetCarrierMeasurableCountableUnionTarget : Prop :=
  (∀ F : Nat → SpectralMeasurePVMFiniteSetCarrier,
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSetCarrierCountableUnion F)) ∧
  (∀ F : Nat → SpectralMeasurePVMFiniteSetCarrier,
    SpectralMeasurePVMFiniteSetCarrierAllEmptyFamily F →
      @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
        spectralMeasurePVMFiniteSetCarrierMeasurableSpace
        (spectralMeasurePVMFiniteSetCarrierCountableUnion F)) ∧
  (∀ F : Nat → SpectralMeasurePVMFiniteSetCarrier,
    ∀ k : Nat,
      SpectralMeasurePVMFiniteSetCarrierSingleWholeAt F k →
        @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
          spectralMeasurePVMFiniteSetCarrierMeasurableSpace
          (spectralMeasurePVMFiniteSetCarrierCountableUnion F))

/-- The finite carrier measurable countable-union target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_measurable_countable_union_target_ready :
    SpectralMeasurePVMFiniteSetCarrierMeasurableCountableUnionTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_countable_union_measurable,
    spectral_measure_pvm_finite_set_carrier_countable_union_all_empty_measurable,
    spectral_measure_pvm_finite_set_carrier_countable_union_single_whole_measurable⟩

/-- Finite measurable sigma-host bridge: endpoint measurability and explicit
countable-union measurability are both available on the local finite carrier.
This is still not a genuine Borel carrier for the R4 self-adjoint operator. -/
def SpectralMeasurePVMFiniteSetCarrierMeasurableCountableUnionBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierMeasurableRealizationBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierMeasurableEndpointTarget ∧
  SpectralMeasurePVMFiniteSetCarrierMeasurableCountableUnionTarget ∧
  SpectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureBundleReady ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSigmaBooleanClosureStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite measurable countable-union bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_measurable_countable_union_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierMeasurableCountableUnionBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_measurable_realization_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_measurable_endpoint_target_ready,
    spectral_measure_pvm_finite_set_carrier_measurable_countable_union_target_ready,
    spectral_measure_pvm_finite_set_carrier_sigma_boolean_closure_bundle_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_sigma_boolean_closure_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
