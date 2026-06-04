import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionNormalizationCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Union with the empty endpoint preserves the canonical packet range component. -/
theorem spectral_measure_pvm_spectral_resolution_union_empty_range_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.emptySet) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent := by
  cases s <;> rfl

/-- Union with the empty endpoint preserves the canonical packet kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_union_empty_kernel_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.emptySet) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent := by
  cases s <;> rfl

/-- Intersection with the whole endpoint preserves the canonical packet range component. -/
theorem spectral_measure_pvm_spectral_resolution_inter_whole_range_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent := by
  cases s <;> rfl

/-- Intersection with the whole endpoint preserves the canonical packet kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_inter_whole_kernel_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent := by
  cases s <;> rfl

/-- Intersection with the empty endpoint has zero range component. -/
theorem spectral_measure_pvm_spectral_resolution_inter_empty_range_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.emptySet) x).rangeComponent = 0 := by
  cases s <;> rfl

/-- Intersection with the empty endpoint has kernel component equal to the original vector. -/
theorem spectral_measure_pvm_spectral_resolution_inter_empty_kernel_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.emptySet) x).kernelComponent = x := by
  cases s <;> rfl

/-- Union with the whole endpoint has range component equal to the original vector. -/
theorem spectral_measure_pvm_spectral_resolution_union_whole_range_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).rangeComponent = x := by
  cases s <;> rfl

/-- Union with the whole endpoint has zero kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_union_whole_kernel_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).kernelComponent = 0 := by
  cases s <;> rfl

/-- Endpoint absorption target for range components of canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointRangeAbsorptionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.emptySet) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.emptySet) x).rangeComponent = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).rangeComponent = x)

/-- Endpoint absorption target for kernel components of canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointKernelAbsorptionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.emptySet) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s SpectralMeasurePVMSpectralSetSlot.emptySet) x).kernelComponent = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s SpectralMeasurePVMSpectralSetSlot.wholeSet) x).kernelComponent = 0)

/-- Genuine endpoint absorption for spectral resolutions remains open beyond the R4
local two-slot surface. -/
def SpectralMeasurePVMGenuineSpectralResolutionEndpointAbsorptionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Endpoint range absorption is ready. -/
theorem spectral_measure_pvm_spectral_resolution_endpoint_range_absorption_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointRangeAbsorptionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_union_empty_range_component,
    spectral_measure_pvm_spectral_resolution_inter_whole_range_component,
    spectral_measure_pvm_spectral_resolution_inter_empty_range_component_zero,
    spectral_measure_pvm_spectral_resolution_union_whole_range_component_eq_self⟩

/-- Endpoint kernel absorption is ready. -/
theorem spectral_measure_pvm_spectral_resolution_endpoint_kernel_absorption_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointKernelAbsorptionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_union_empty_kernel_component,
    spectral_measure_pvm_spectral_resolution_inter_whole_kernel_component,
    spectral_measure_pvm_spectral_resolution_inter_empty_kernel_component_eq_self,
    spectral_measure_pvm_spectral_resolution_union_whole_kernel_component_zero⟩

/-- Genuine endpoint absorption remains explicitly open. -/
theorem spectral_measure_pvm_genuine_spectral_resolution_endpoint_absorption_still_open_ready :
    SpectralMeasurePVMGenuineSpectralResolutionEndpointAbsorptionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution endpoint absorption core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionNormalizationCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointRangeAbsorptionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionEndpointKernelAbsorptionTarget ∧
  SpectralMeasurePVMGenuineSpectralResolutionEndpointAbsorptionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution endpoint absorption core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_endpoint_absorption_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_normalization_core_ready,
    spectral_measure_pvm_spectral_resolution_endpoint_range_absorption_target_ready,
    spectral_measure_pvm_spectral_resolution_endpoint_kernel_absorption_target_ready,
    spectral_measure_pvm_genuine_spectral_resolution_endpoint_absorption_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution endpoint absorption core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionNormalizationBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralResolutionEndpointAbsorptionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution endpoint absorption boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_endpoint_absorption_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_endpoint_absorption_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_normalization_boundary_held,
    spectral_measure_pvm_genuine_spectral_resolution_endpoint_absorption_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
