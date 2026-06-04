import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range component of the R4 local PVM decomposition. -/
def spectralMeasurePVMContinuousLocalPVMRangeComponent
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMSpectralSetSlotContinuousProjection s x

/-- The kernel component of the R4 local PVM decomposition. -/
def spectralMeasurePVMContinuousLocalPVMKernelComponent
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMSpectralSetSlotContinuousProjection
    (spectralMeasurePVMSpectralSetSlotComplement s) x

/-- The range component lies in the range of `P(s)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_component_mem_range
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember s
      (spectralMeasurePVMContinuousLocalPVMRangeComponent s x) := by
  exact spectral_measure_pvm_continuous_local_pvm_projected_range_member s x

/-- The kernel component lies in the kernel of `P(s)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_component_mem_kernel
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s
      (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) := by
  exact spectral_measure_pvm_continuous_local_pvm_complement_range_subset_kernel s
    (spectralMeasurePVMContinuousLocalPVMKernelComponent s x)
    (spectral_measure_pvm_continuous_local_pvm_projected_range_member
      (spectralMeasurePVMSpectralSetSlotComplement s) x)

/-- The range and kernel components reconstruct the original vector. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_decomposition_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
        spectralMeasurePVMContinuousLocalPVMKernelComponent s x = x := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_decomposition_apply s x

/-- Reprojecting the range/kernel decomposition onto `P(s)` recovers the range
component. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_first_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
          spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
      spectralMeasurePVMContinuousLocalPVMRangeComponent s x := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_first_reprojection_apply s x

/-- Reprojecting the range/kernel decomposition onto `P(sᶜ)` recovers the kernel
component. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_complement_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
          spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
      spectralMeasurePVMContinuousLocalPVMKernelComponent s x := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_complement_reprojection_apply s x

/-- The range component is fixed by `P(s)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_component_fixed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMContinuousLocalPVMRangeComponent s x) =
      spectralMeasurePVMContinuousLocalPVMRangeComponent s x := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_first_component_fixed s x

/-- The kernel component is killed by `P(s)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_component_killed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) = 0 := by
  exact spectral_measure_pvm_continuous_local_pvm_kernel_component_mem_kernel s x

/-- The kernel component is fixed by the complement projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_component_complement_fixed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
      spectralMeasurePVMContinuousLocalPVMKernelComponent s x := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_complement_component_fixed s x

/-- Existence of the range/kernel decomposition for every vector. -/
def SpectralMeasurePVMContinuousLocalPVMRangeKernelDecompositionTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s
        (spectralMeasurePVMContinuousLocalPVMRangeComponent s x) ∧
      SpectralMeasurePVMContinuousLocalPVMKernelMember s
        (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) ∧
      spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
          spectralMeasurePVMContinuousLocalPVMKernelComponent s x = x

/-- Reprojection target for the range/kernel decomposition. -/
def SpectralMeasurePVMContinuousLocalPVMRangeKernelReprojectionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
            spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
        spectralMeasurePVMContinuousLocalPVMRangeComponent s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMContinuousLocalPVMRangeComponent s x +
            spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
        spectralMeasurePVMContinuousLocalPVMKernelComponent s x)

/-- Component action target for the range/kernel decomposition. -/
def SpectralMeasurePVMContinuousLocalPVMRangeKernelComponentActionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMContinuousLocalPVMRangeComponent s x) =
        spectralMeasurePVMContinuousLocalPVMRangeComponent s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMContinuousLocalPVMKernelComponent s x) =
        spectralMeasurePVMContinuousLocalPVMKernelComponent s x)

/-- Genuine Hilbert range/kernel direct-sum theorem remains open. -/
def SpectralMeasurePVMGenuineRangeKernelDirectSumStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The range/kernel decomposition target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_decomposition_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeKernelDecompositionTarget := by
  intro s x
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_component_mem_range s x,
    spectral_measure_pvm_continuous_local_pvm_kernel_component_mem_kernel s x,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_decomposition_apply s x⟩

/-- The range/kernel reprojection target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_reprojection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeKernelReprojectionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_kernel_first_reprojection_apply,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_complement_reprojection_apply⟩

/-- The component action target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_component_action_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeKernelComponentActionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_component_fixed,
    spectral_measure_pvm_continuous_local_pvm_kernel_component_killed,
    spectral_measure_pvm_continuous_local_pvm_kernel_component_complement_fixed⟩

/-- Genuine range/kernel direct-sum theorem remains explicitly open. -/
theorem spectral_measure_pvm_genuine_range_kernel_direct_sum_still_open_ready :
    SpectralMeasurePVMGenuineRangeKernelDirectSumStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM range/kernel decomposition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelCoreReady ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelDecompositionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelReprojectionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelComponentActionTarget ∧
  SpectralMeasurePVMGenuineRangeKernelDirectSumStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM range/kernel decomposition core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_decomposition_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_kernel_core_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_decomposition_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_reprojection_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_component_action_target_ready,
    spectral_measure_pvm_genuine_range_kernel_direct_sum_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 range/kernel decomposition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelBoundaryHeld ∧
  SpectralMeasurePVMGenuineRangeKernelDirectSumStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 range/kernel decomposition boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_decomposition_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_decomposition_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_kernel_boundary_held,
    spectral_measure_pvm_genuine_range_kernel_direct_sum_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
