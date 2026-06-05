import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Every R4-local spectral set slot is either the empty endpoint or the whole endpoint. -/
theorem spectral_measure_pvm_spectral_set_slot_two_way_classification
    (s : SpectralMeasurePVMSpectralSetSlot) :
    s = SpectralMeasurePVMSpectralSetSlot.emptySet ∨
      s = SpectralMeasurePVMSpectralSetSlot.wholeSet := by
  cases s <;> simp

/-- The canonical packet range component is either zero or the original vector. -/
theorem spectral_measure_pvm_spectral_resolution_range_component_two_way_classification
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0 ∨
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = x := by
  cases s <;> simp [spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket,
    spectralMeasurePVMContinuousFunctionalCalculusRangeComponent,
    spectralMeasurePVMSpectralSetSlotIndicatorFunction,
    spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
    spectralMeasurePVMConcreteIndicatorFunction,
    spectralMeasurePVMContinuousFunctionalCalculus]

/-- The canonical packet kernel component is either the original vector or zero. -/
theorem spectral_measure_pvm_spectral_resolution_kernel_component_two_way_classification
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = x ∨
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = 0 := by
  cases s <;> simp [spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket,
    spectralMeasurePVMContinuousFunctionalCalculusKernelComponent,
    spectralMeasurePVMSpectralSetSlotIndicatorFunction,
    spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
    spectralMeasurePVMConcreteIndicatorFunction,
    spectralMeasurePVMContinuousFunctionalCalculus,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- Empty slot packets classify as `(range,kernel)=(0,x)`. -/
theorem spectral_measure_pvm_spectral_resolution_empty_component_pair_classification
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        SpectralMeasurePVMSpectralSetSlot.emptySet x).rangeComponent = 0 ∧
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        SpectralMeasurePVMSpectralSetSlot.emptySet x).kernelComponent = x := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_empty_range_component_zero x,
    spectral_measure_pvm_spectral_resolution_empty_kernel_component_eq_self x⟩

/-- Whole slot packets classify as `(range,kernel)=(x,0)`. -/
theorem spectral_measure_pvm_spectral_resolution_whole_component_pair_classification
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        SpectralMeasurePVMSpectralSetSlot.wholeSet x).rangeComponent = x ∧
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        SpectralMeasurePVMSpectralSetSlot.wholeSet x).kernelComponent = 0 := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_whole_range_component_eq_self x,
    spectral_measure_pvm_spectral_resolution_whole_kernel_component_zero x⟩

/-- Any canonical packet is one of the two endpoint component pairs. -/
theorem spectral_measure_pvm_spectral_resolution_component_pair_two_way_classification
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0 ∧
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = x) ∨
    ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = x ∧
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = 0) := by
  cases s
  · exact Or.inl (spectral_measure_pvm_spectral_resolution_empty_component_pair_classification x)
  · exact Or.inr (spectral_measure_pvm_spectral_resolution_whole_component_pair_classification x)

/-- Two-way slot classification target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionSlotClassificationTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    s = SpectralMeasurePVMSpectralSetSlot.emptySet ∨
      s = SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- Two-way component classification target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComponentClassificationTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0 ∨
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = x ∨
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = 0)

/-- Two-way endpoint pair classification target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPairClassificationTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0 ∧
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = x) ∨
      ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = x ∧
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = 0)

/-- Genuine spectral-resolution slot classification remains open beyond this R4
local two-slot surface. -/
def SpectralMeasurePVMGenuineSpectralResolutionSlotClassificationStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Slot classification target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_slot_classification_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionSlotClassificationTarget := by
  exact spectral_measure_pvm_spectral_set_slot_two_way_classification

/-- Component classification target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_component_classification_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComponentClassificationTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_range_component_two_way_classification,
    spectral_measure_pvm_spectral_resolution_kernel_component_two_way_classification⟩

/-- Pair classification target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_pair_classification_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPairClassificationTarget := by
  exact spectral_measure_pvm_spectral_resolution_component_pair_two_way_classification

/-- Genuine slot classification remains explicitly open. -/
theorem spectral_measure_pvm_genuine_spectral_resolution_slot_classification_still_open_ready :
    SpectralMeasurePVMGenuineSpectralResolutionSlotClassificationStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution two-slot classification core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionTwoSlotClassificationCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionSlotClassificationTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComponentClassificationTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPairClassificationTarget ∧
  SpectralMeasurePVMGenuineSpectralResolutionSlotClassificationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution two-slot classification core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_two_slot_classification_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionTwoSlotClassificationCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_partition_core_ready,
    spectral_measure_pvm_spectral_resolution_slot_classification_target_ready,
    spectral_measure_pvm_spectral_resolution_component_classification_target_ready,
    spectral_measure_pvm_spectral_resolution_pair_classification_target_ready,
    spectral_measure_pvm_genuine_spectral_resolution_slot_classification_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution two-slot classification core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionTwoSlotClassificationBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionTwoSlotClassificationCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralResolutionSlotClassificationStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution two-slot classification boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_two_slot_classification_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionTwoSlotClassificationBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_two_slot_classification_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_partition_boundary_held,
    spectral_measure_pvm_genuine_spectral_resolution_slot_classification_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
