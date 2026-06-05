import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionBooleanNormalFormCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The union of a slot with its complement has whole-set range component. -/
theorem spectral_measure_pvm_spectral_resolution_union_complement_range_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x).rangeComponent = x := by
  cases s <;> rfl

/-- The union of a slot with its complement has zero kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_union_complement_kernel_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x).kernelComponent = 0 := by
  cases s <;> rfl

/-- The reversed complement union has whole-set range component. -/
theorem spectral_measure_pvm_spectral_resolution_complement_union_range_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion
          (spectralMeasurePVMSpectralSetSlotComplement s) s) x).rangeComponent = x := by
  cases s <;> rfl

/-- The reversed complement union has zero kernel component. -/
theorem spectral_measure_pvm_spectral_resolution_complement_union_kernel_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion
          (spectralMeasurePVMSpectralSetSlotComplement s) s) x).kernelComponent = 0 := by
  cases s <;> rfl

/-- The intersection of a slot with its complement has zero range component. -/
theorem spectral_measure_pvm_spectral_resolution_inter_complement_range_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x).rangeComponent = 0 := by
  cases s <;> rfl

/-- The intersection of a slot with its complement has kernel component equal to
`x`. -/
theorem spectral_measure_pvm_spectral_resolution_inter_complement_kernel_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x).kernelComponent = x := by
  cases s <;> rfl

/-- The reversed complement intersection has zero range component. -/
theorem spectral_measure_pvm_spectral_resolution_complement_inter_range_component_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter
          (spectralMeasurePVMSpectralSetSlotComplement s) s) x).rangeComponent = 0 := by
  cases s <;> rfl

/-- The reversed complement intersection has kernel component equal to `x`. -/
theorem spectral_measure_pvm_spectral_resolution_complement_inter_kernel_component_eq_self
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter
          (spectralMeasurePVMSpectralSetSlotComplement s) s) x).kernelComponent = x := by
  cases s <;> rfl

/-- Complement-union partition target for canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementUnionPartitionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x).rangeComponent = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x).kernelComponent = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion
            (spectralMeasurePVMSpectralSetSlotComplement s) s) x).rangeComponent = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion
            (spectralMeasurePVMSpectralSetSlotComplement s) s) x).kernelComponent = 0)

/-- Complement-intersection partition target for canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementInterPartitionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x).rangeComponent = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x).kernelComponent = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter
            (spectralMeasurePVMSpectralSetSlotComplement s) s) x).rangeComponent = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter
            (spectralMeasurePVMSpectralSetSlotComplement s) s) x).kernelComponent = x)

/-- Genuine complement partition for spectral resolutions remains open beyond the
R4 local two-slot surface. -/
def SpectralMeasurePVMGenuineSpectralResolutionComplementPartitionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Complement-union partition target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_complement_union_partition_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementUnionPartitionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_union_complement_range_component_eq_self,
    spectral_measure_pvm_spectral_resolution_union_complement_kernel_component_zero,
    spectral_measure_pvm_spectral_resolution_complement_union_range_component_eq_self,
    spectral_measure_pvm_spectral_resolution_complement_union_kernel_component_zero⟩

/-- Complement-intersection partition target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_complement_inter_partition_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementInterPartitionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_inter_complement_range_component_zero,
    spectral_measure_pvm_spectral_resolution_inter_complement_kernel_component_eq_self,
    spectral_measure_pvm_spectral_resolution_complement_inter_range_component_zero,
    spectral_measure_pvm_spectral_resolution_complement_inter_kernel_component_eq_self⟩

/-- Genuine complement partition remains explicitly open. -/
theorem spectral_measure_pvm_genuine_spectral_resolution_complement_partition_still_open_ready :
    SpectralMeasurePVMGenuineSpectralResolutionComplementPartitionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution complement partition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionBooleanNormalFormCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementUnionPartitionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionComplementInterPartitionTarget ∧
  SpectralMeasurePVMGenuineSpectralResolutionComplementPartitionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution complement partition core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_partition_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_boolean_normal_form_core_ready,
    spectral_measure_pvm_spectral_resolution_complement_union_partition_target_ready,
    spectral_measure_pvm_spectral_resolution_complement_inter_partition_target_ready,
    spectral_measure_pvm_genuine_spectral_resolution_complement_partition_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution complement partition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionBooleanNormalFormBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralResolutionComplementPartitionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution complement partition boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_partition_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionComplementPartitionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_complement_partition_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_boolean_normal_form_boundary_held,
    spectral_measure_pvm_genuine_spectral_resolution_complement_partition_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
