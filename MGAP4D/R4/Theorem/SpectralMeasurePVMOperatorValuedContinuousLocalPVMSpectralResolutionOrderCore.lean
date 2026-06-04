import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- If `s ⊆ t`, then the canonical range component for `s` belongs to the range
of `P(t)`. -/
theorem spectral_measure_pvm_spectral_resolution_range_component_mem_super_range
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember t
      (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) := by
  exact spectral_measure_pvm_continuous_local_pvm_range_inclusion_of_subset s t hst
    (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x)
    (spectral_measure_pvm_continuous_functional_calculus_range_component_mem_range s x)

/-- If `s ⊆ t`, then the canonical kernel component for `t` belongs to the
kernel of `P(s)`. -/
theorem spectral_measure_pvm_spectral_resolution_kernel_component_mem_sub_kernel
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s
      (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x) := by
  exact spectral_measure_pvm_continuous_local_pvm_kernel_antitone_of_subset s t hst
    (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x)
    (spectral_measure_pvm_continuous_functional_calculus_kernel_component_mem_kernel t x)

/-- If `s ⊆ t`, the canonical range component of `s` is fixed by `FC(χ_t)`. -/
theorem spectral_measure_pvm_spectral_resolution_range_component_super_reprojection
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) =
      spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x := by
  exact spectral_measure_pvm_continuous_functional_calculus_subset_right_absorption_apply s t hst x

/-- If `s ⊆ t`, the canonical kernel component of `t` is killed by `FC(χ_s)`. -/
theorem spectral_measure_pvm_spectral_resolution_kernel_component_sub_projection_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x) = 0 := by
  calc
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x) :=
        spectral_measure_pvm_continuous_functional_calculus_slot_indicator_projection s
          (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x)
    _ = 0 := spectral_measure_pvm_spectral_resolution_kernel_component_mem_sub_kernel s t hst x

/-- If `s ⊆ t`, the `s`-range component of the canonical packet is absorbed by
the `t`-range projection. -/
theorem spectral_measure_pvm_spectral_resolution_packet_range_component_super_reprojection
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent := by
  exact spectral_measure_pvm_spectral_resolution_range_component_super_reprojection s t hst x

/-- If `s ⊆ t`, the `t`-kernel component of the canonical packet is killed by the
`s`-range projection. -/
theorem spectral_measure_pvm_spectral_resolution_packet_kernel_component_sub_projection_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).kernelComponent = 0 := by
  exact spectral_measure_pvm_spectral_resolution_kernel_component_sub_projection_zero s t hst x

/-- Order-induced membership target for canonical spectral-resolution components. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderMembershipTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        SpectralMeasurePVMContinuousLocalPVMRangeMember t
          (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        SpectralMeasurePVMContinuousLocalPVMKernelMember s
          (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x))

/-- Order-induced action target for canonical spectral-resolution components. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderActionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
            (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) =
          spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
            (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent t x) = 0)

/-- Order-induced packet action target for canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderPacketTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent =
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).kernelComponent = 0)

/-- Genuine ordered spectral-resolution theorem remains open beyond this R4-local
functional-calculus packet. -/
def SpectralMeasurePVMGenuineOrderedSpectralResolutionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Order membership target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_order_membership_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderMembershipTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_range_component_mem_super_range,
    spectral_measure_pvm_spectral_resolution_kernel_component_mem_sub_kernel⟩

/-- Order action target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_order_action_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderActionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_range_component_super_reprojection,
    spectral_measure_pvm_spectral_resolution_kernel_component_sub_projection_zero⟩

/-- Order packet target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_order_packet_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderPacketTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_packet_range_component_super_reprojection,
    spectral_measure_pvm_spectral_resolution_packet_kernel_component_sub_projection_zero⟩

/-- Genuine ordered spectral resolution remains explicitly open. -/
theorem spectral_measure_pvm_genuine_ordered_spectral_resolution_still_open_ready :
    SpectralMeasurePVMGenuineOrderedSpectralResolutionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution order core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderMembershipTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderActionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionOrderPacketTarget ∧
  SpectralMeasurePVMGenuineOrderedSpectralResolutionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution order core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_order_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_spectral_resolution_core_ready,
    spectral_measure_pvm_spectral_resolution_order_membership_target_ready,
    spectral_measure_pvm_spectral_resolution_order_action_target_ready,
    spectral_measure_pvm_spectral_resolution_order_packet_target_ready,
    spectral_measure_pvm_genuine_ordered_spectral_resolution_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution order core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionBoundaryHeld ∧
  SpectralMeasurePVMGenuineOrderedSpectralResolutionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution order boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_order_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_order_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_spectral_resolution_boundary_held,
    spectral_measure_pvm_genuine_ordered_spectral_resolution_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
