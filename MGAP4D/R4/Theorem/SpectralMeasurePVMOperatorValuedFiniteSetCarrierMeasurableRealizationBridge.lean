import Mathlib.MeasureTheory.MeasurableSpace.Basic
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierLocalSpectralTheoremBundle

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The finite `Set` carrier equipped with the discrete/top measurable structure.

This is a genuine `MeasurableSpace` on the finite carrier point type, but it is
still only the local/two-slot carrier, not the Borel sigma algebra of the
self-adjoint operator. -/
def spectralMeasurePVMFiniteSetCarrierMeasurableSpace :
    MeasurableSpace SpectralMeasurePVMFiniteSetCarrierPoint :=
  ⊤

/-- In the discrete/top measurable structure, the empty local carrier is measurable. -/
theorem spectral_measure_pvm_finite_set_carrier_empty_measurable :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      spectralMeasurePVMFiniteSetCarrierEmpty := by
  trivial

/-- In the discrete/top measurable structure, the whole local carrier is measurable. -/
theorem spectral_measure_pvm_finite_set_carrier_whole_measurable :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      spectralMeasurePVMFiniteSetCarrierWhole := by
  trivial

/-- Every realized local spectral slot is measurable in the finite carrier. -/
theorem spectral_measure_pvm_finite_set_carrier_slot_measurable
    (s : SpectralMeasurePVMSpectralSetSlot) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMSpectralSlotToFiniteSetCarrier s) := by
  cases s
  · exact spectral_measure_pvm_finite_set_carrier_empty_measurable
  · exact spectral_measure_pvm_finite_set_carrier_whole_measurable

/-- Measurability target for the finite local carrier endpoints and slot image. -/
def SpectralMeasurePVMFiniteSetCarrierMeasurableEndpointTarget : Prop :=
  @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
    spectralMeasurePVMFiniteSetCarrierMeasurableSpace
    spectralMeasurePVMFiniteSetCarrierEmpty ∧
  @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
    spectralMeasurePVMFiniteSetCarrierMeasurableSpace
    spectralMeasurePVMFiniteSetCarrierWhole ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMSpectralSlotToFiniteSetCarrier s))

/-- The finite local carrier measurability target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_measurable_endpoint_target_ready :
    SpectralMeasurePVMFiniteSetCarrierMeasurableEndpointTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_empty_measurable,
    spectral_measure_pvm_finite_set_carrier_whole_measurable,
    spectral_measure_pvm_finite_set_carrier_slot_measurable⟩

/-- A finite measurable carrier interface bundling the local finite `Set` carrier,
its discrete/top measurable structure, and the already-built local spectral
 theorem bundle. -/
def SpectralMeasurePVMFiniteSetCarrierMeasurableRealizationBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierLocalSpectralTheoremBundleReady ∧
  SpectralMeasurePVMFiniteSetCarrierMeasurableEndpointTarget ∧
  SpectralMeasurePVMFiniteSetCarrierSigmaBooleanClosureBundleReady ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite measurable carrier realization bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_measurable_realization_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierMeasurableRealizationBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_local_spectral_theorem_bundle_ready,
    spectral_measure_pvm_finite_set_carrier_measurable_endpoint_target_ready,
    spectral_measure_pvm_finite_set_carrier_sigma_boolean_closure_bundle_ready,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
