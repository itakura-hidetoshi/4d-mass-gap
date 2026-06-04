import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Uniqueness of the range component in the R4 local range/kernel decomposition.
If `x = r + k`, with `r ∈ Ran P(s)` and `k ∈ Ker P(s)`, then `r = P(s)x`.
This is still the two-slot R4 surface, not a genuine Hilbert direct-sum theorem. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_range_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hr : SpectralMeasurePVMContinuousLocalPVMRangeMember s r)
    (hk : SpectralMeasurePVMContinuousLocalPVMKernelMember s k)
    (hx : x = r + k) :
    r = spectralMeasurePVMContinuousLocalPVMRangeComponent s x := by
  cases s
  · have hr0 : r = 0 :=
      spectral_measure_pvm_continuous_local_pvm_empty_range_member_eq_zero r hr
    rw [hx, hr0]
    rfl
  · have hk0 : k = 0 :=
      spectral_measure_pvm_continuous_local_pvm_whole_kernel_member_eq_zero k hk
    rw [hx, hk0]
    simp [spectralMeasurePVMContinuousLocalPVMRangeComponent,
      spectralMeasurePVMSpectralSetSlotContinuousProjection]

/-- Uniqueness of the kernel component in the R4 local range/kernel decomposition.
If `x = r + k`, with `r ∈ Ran P(s)` and `k ∈ Ker P(s)`, then `k = P(sᶜ)x`. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_kernel_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hr : SpectralMeasurePVMContinuousLocalPVMRangeMember s r)
    (hk : SpectralMeasurePVMContinuousLocalPVMKernelMember s k)
    (hx : x = r + k) :
    k = spectralMeasurePVMContinuousLocalPVMKernelComponent s x := by
  cases s
  · have hr0 : r = 0 :=
      spectral_measure_pvm_continuous_local_pvm_empty_range_member_eq_zero r hr
    rw [hx, hr0]
    simp [spectralMeasurePVMContinuousLocalPVMKernelComponent,
      spectralMeasurePVMSpectralSetSlotContinuousProjection,
      spectralMeasurePVMSpectralSetSlotComplement]
  · have hk0 : k = 0 :=
      spectral_measure_pvm_continuous_local_pvm_whole_kernel_member_eq_zero k hk
    rw [hk0]
    rfl

/-- Combined uniqueness target for the R4 local range/kernel decomposition. -/
def SpectralMeasurePVMContinuousLocalPVMRangeKernelUniquenessTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s r →
      SpectralMeasurePVMContinuousLocalPVMKernelMember s k →
      x = r + k →
        r = spectralMeasurePVMContinuousLocalPVMRangeComponent s x ∧
        k = spectralMeasurePVMContinuousLocalPVMKernelComponent s x

/-- The canonical range/kernel decomposition is unique in the R4 local surface. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_uniqueness_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeKernelUniquenessTarget := by
  intro s x r k hr hk hx
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_kernel_range_component_unique s x r k hr hk hx,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_kernel_component_unique s x r k hr hk hx⟩

/-- Existence plus uniqueness packet for the R4 local range/kernel decomposition. -/
def SpectralMeasurePVMContinuousLocalPVMRangeKernelExistUniqueTarget : Prop :=
  SpectralMeasurePVMContinuousLocalPVMRangeKernelDecompositionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelUniquenessTarget

/-- Existence plus uniqueness is ready on the R4 local surface. -/
theorem spectral_measure_pvm_continuous_local_pvm_range_kernel_exist_unique_target_ready :
    SpectralMeasurePVMContinuousLocalPVMRangeKernelExistUniqueTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_range_kernel_decomposition_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_uniqueness_target_ready⟩

/-- Genuine Hilbert range/kernel direct-sum uniqueness theorem remains open. -/
def SpectralMeasurePVMGenuineRangeKernelDirectSumUniquenessStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The genuine range/kernel direct-sum uniqueness theorem remains explicitly open. -/
theorem spectral_measure_pvm_genuine_range_kernel_direct_sum_uniqueness_still_open_ready :
    SpectralMeasurePVMGenuineRangeKernelDirectSumUniquenessStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM range/kernel uniqueness core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionCoreReady ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelUniquenessTarget ∧
  SpectralMeasurePVMContinuousLocalPVMRangeKernelExistUniqueTarget ∧
  SpectralMeasurePVMGenuineRangeKernelDirectSumUniquenessStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM range/kernel uniqueness core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_uniqueness_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_decomposition_core_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_uniqueness_target_ready,
    spectral_measure_pvm_continuous_local_pvm_range_kernel_exist_unique_target_ready,
    spectral_measure_pvm_genuine_range_kernel_direct_sum_uniqueness_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 range/kernel uniqueness core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelDecompositionBoundaryHeld ∧
  SpectralMeasurePVMGenuineRangeKernelDirectSumUniquenessStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 range/kernel uniqueness boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_uniqueness_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeKernelUniquenessBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_uniqueness_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_kernel_decomposition_boundary_held,
    spectral_measure_pvm_genuine_range_kernel_direct_sum_uniqueness_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
