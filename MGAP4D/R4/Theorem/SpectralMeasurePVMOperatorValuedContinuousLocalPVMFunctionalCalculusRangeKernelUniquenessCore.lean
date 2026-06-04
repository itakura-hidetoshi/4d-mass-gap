import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Uniqueness of the functional-calculus range component in the R4 local
range/kernel decomposition.  This reuses the projection-defined uniqueness and
then transfers it across the `FC(χ_E)=P(E)` bridge. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_range_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hr : SpectralMeasurePVMContinuousLocalPVMRangeMember s r)
    (hk : SpectralMeasurePVMContinuousLocalPVMKernelMember s k)
    (hx : x = r + k) :
    r = spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x := by
  calc
    r = spectralMeasurePVMContinuousLocalPVMRangeComponent s x :=
      spectral_measure_pvm_continuous_local_pvm_range_kernel_range_component_unique
        s x r k hr hk hx
    _ = spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x :=
      (spectral_measure_pvm_continuous_functional_calculus_range_component_eq_projection_component
        s x).symm

/-- Uniqueness of the functional-calculus kernel component in the R4 local
range/kernel decomposition. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_kernel_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hr : SpectralMeasurePVMContinuousLocalPVMRangeMember s r)
    (hk : SpectralMeasurePVMContinuousLocalPVMKernelMember s k)
    (hx : x = r + k) :
    k = spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x := by
  calc
    k = spectralMeasurePVMContinuousLocalPVMKernelComponent s x :=
      spectral_measure_pvm_continuous_local_pvm_range_kernel_kernel_component_unique
        s x r k hr hk hx
    _ = spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x :=
      (spectral_measure_pvm_continuous_functional_calculus_kernel_component_eq_projection_component
        s x).symm

/-- Combined uniqueness target for the R4 local functional-calculus range/kernel
decomposition. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelUniquenessTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x r k : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s r →
      SpectralMeasurePVMContinuousLocalPVMKernelMember s k →
      x = r + k →
        r = spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x ∧
        k = spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x

/-- The functional-calculus range/kernel decomposition is unique on the R4 local
surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_uniqueness_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelUniquenessTarget := by
  intro s x r k hr hk hx
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_range_component_unique
      s x r k hr hk hx,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_kernel_component_unique
      s x r k hr hk hx⟩

/-- Existence plus uniqueness packet for the R4 local functional-calculus
range/kernel decomposition. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelExistUniqueTarget : Prop :=
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelDecompositionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelUniquenessTarget

/-- Existence plus uniqueness is ready for the functional-calculus range/kernel
surface. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_exist_unique_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelExistUniqueTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_uniqueness_target_ready⟩

/-- Genuine functional-calculus range/kernel direct-sum uniqueness remains open
beyond the R4 local two-slot surface. -/
def SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelUniquenessStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Genuine functional-calculus range/kernel direct-sum uniqueness remains
explicitly open. -/
theorem spectral_measure_pvm_genuine_functional_calculus_range_kernel_uniqueness_still_open_ready :
    SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelUniquenessStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 functional-calculus range/kernel uniqueness core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelUniquenessTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelExistUniqueTarget ∧
  SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelUniquenessStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus range/kernel uniqueness core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_uniqueness_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_bridge_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_uniqueness_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_exist_unique_target_ready,
    spectral_measure_pvm_genuine_functional_calculus_range_kernel_uniqueness_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 functional-calculus range/kernel uniqueness core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeBoundaryHeld ∧
  SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelUniquenessStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus range/kernel uniqueness boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_uniqueness_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_uniqueness_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_bridge_boundary_held,
    spectral_measure_pvm_genuine_functional_calculus_range_kernel_uniqueness_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
