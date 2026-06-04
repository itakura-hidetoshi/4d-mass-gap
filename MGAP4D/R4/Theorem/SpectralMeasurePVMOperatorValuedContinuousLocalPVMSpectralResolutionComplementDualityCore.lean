import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range component of the complement packet is the kernel component of the
original packet.  This is the R4-local two-slot surface. -/
theorem spectral_measure_pvm_spectral_resolution_complement_range_eq_kernel_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent := by
  cases s <;> rfl

/-- The kernel component of the complement packet is the range component of the
original packet. -/
theorem spectral_measure_pvm_spectral_resolution_complement_kernel_eq_range_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent := by
  cases s <;> rfl

/-- The complement-packet range component lies in the original kernel. -/
theorem spectral_measure_pvm_spectral_resolution_complement_range_mem_original_kernel
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent := by
  rw [spectral_measure_pvm_spectral_resolution_complement_range_eq_kernel_component s x]
  exact spectral_measure_pvm_continuous_functional_calculus_kernel_component_mem_kernel s x

/-- The complement-packet kernel component lies in the original range. -/
theorem spectral_measure_pvm_spectral_resolution_complement_kernel_mem_original_range
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember s
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent := by
  rw [spectral_measure_pvm_spectral_resolution_complement_kernel_eq_range_component s x]
  exact spectral_measure_pvm_continuous_functional_calculus_range_component_mem_range s x

/-- The original projection kills the complement-packet range component. -/
theorem spectral_measure_pvm_spectral_resolution_complement_range_original_projection_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent = 0 := by
  rw [spectral_measure_pvm_spectral_resolution_complement_range_eq_kernel_component s x]
  exact spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_zero_apply s x

/-- The original projection fixes the complement-packet kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_complement_kernel_original_projection_fixed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent := by
  rw [spectral_measure_pvm_spectral_resolution_complement_kernel_eq_range_component s x]
  exact spectral_measure_pvm_continuous_functional_calculus_slot_indicator_idempotent_apply s x

/-- Complement-packet component-swap target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementSwapTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent)

/-- Complement-packet membership target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementMembershipTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMKernelMember s
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent)

/-- Complement-packet original-projection action target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementActionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
            (spectralMeasurePVMSpectralSetSlotComplement s) x).rangeComponent = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
            (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotComplement s) x).kernelComponent)

/-- Genuine complement spectral-resolution duality remains open beyond the R4
local two-slot surface. -/
def SpectralMeasurePVMGenuineComplementSpectralResolutionDualityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The complement-swap target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_complement_swap_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementSwapTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_complement_range_eq_kernel_component,
    spectral_measure_pvm_spectral_resolution_complement_kernel_eq_range_component⟩

/-- The complement membership target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_complement_membership_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementMembershipTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_complement_range_mem_original_kernel,
    spectral_measure_pvm_spectral_resolution_complement_kernel_mem_original_range⟩

/-- The complement action target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_complement_action_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementActionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_complement_range_original_projection_zero,
    spectral_measure_pvm_spectral_resolution_complement_kernel_original_projection_fixed⟩

/-- Genuine complement spectral-resolution duality remains explicitly open. -/
theorem spectral_measure_pvm_genuine_complement_spectral_resolution_duality_still_open_ready :
    SpectralMeasurePVMGenuineComplementSpectralResolutionDualityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution complement duality core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementDualityCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementSwapTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementMembershipTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementActionTarget ∧
  SpectralMeasurePVMGenuineComplementSpectralResolutionDualityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution complement duality core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_duality_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementDualityCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_disjoint_additivity_core_ready,
    spectral_measure_pvm_spectral_resolution_complement_swap_target_ready,
    spectral_measure_pvm_spectral_resolution_complement_membership_target_ready,
    spectral_measure_pvm_spectral_resolution_complement_action_target_ready,
    spectral_measure_pvm_genuine_complement_spectral_resolution_duality_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution complement duality core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementDualityBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementDualityCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityBoundaryHeld ∧
  SpectralMeasurePVMGenuineComplementSpectralResolutionDualityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution complement duality boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_duality_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementDualityBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_duality_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_disjoint_additivity_boundary_held,
    spectral_measure_pvm_genuine_complement_spectral_resolution_duality_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
