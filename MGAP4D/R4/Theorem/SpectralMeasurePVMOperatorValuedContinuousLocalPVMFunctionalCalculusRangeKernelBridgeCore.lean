import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Range component expressed through the R4-local indicator functional calculus. -/
def spectralMeasurePVMContinuousFunctionalCalculusRangeComponent
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousFunctionalCalculus
    (spectralMeasurePVMSpectralSetSlotIndicatorFunction s) x

/-- Kernel component expressed through the R4-local complement-indicator
functional calculus. -/
def spectralMeasurePVMContinuousFunctionalCalculusKernelComponent
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    MathlibAnalytic.ConcreteL2R1HilbertCarrier :=
  spectralMeasurePVMContinuousFunctionalCalculus
    (spectralMeasurePVMSpectralSetSlotIndicatorFunction
      (spectralMeasurePVMSpectralSetSlotComplement s)) x

/-- The functional-calculus range component agrees with the projection-defined
range component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_component_eq_projection_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x =
      spectralMeasurePVMContinuousLocalPVMRangeComponent s x := by
  cases s <;> rfl

/-- The functional-calculus kernel component agrees with the projection-defined
kernel component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_kernel_component_eq_projection_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x =
      spectralMeasurePVMContinuousLocalPVMKernelComponent s x := by
  cases s <;> rfl

/-- The functional-calculus range component lies in the range of `P(s)`. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_component_mem_range
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember s
      (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) := by
  cases s <;>
    exact spectral_measure_pvm_continuous_local_pvm_projected_range_member _ x

/-- The functional-calculus kernel component lies in the kernel of `P(s)`. -/
theorem spectral_measure_pvm_continuous_functional_calculus_kernel_component_mem_kernel
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s
      (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x) := by
  cases s <;> rfl

/-- Functional-calculus range and kernel components reconstruct the vector. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
        spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x = x := by
  exact spectral_measure_pvm_continuous_functional_calculus_slot_indicator_complement_sum s x

/-- Reprojection onto `P(s)` recovers the functional-calculus range component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_first_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
          spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x) =
      spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x := by
  cases s <;>
    simp [spectralMeasurePVMContinuousFunctionalCalculusRangeComponent,
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent,
      spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus,
      spectralMeasurePVMSpectralSetSlotComplement]

/-- Reprojection onto `P(sᶜ)` recovers the functional-calculus kernel component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_complement_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotComplement s))
        (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
          spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x) =
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x := by
  cases s <;>
    simp [spectralMeasurePVMContinuousFunctionalCalculusRangeComponent,
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent,
      spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus,
      spectralMeasurePVMSpectralSetSlotComplement]

/-- Functional-calculus components agree with the projection-defined range/kernel
components. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelComponentBridgeTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x =
        spectralMeasurePVMContinuousLocalPVMRangeComponent s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x =
        spectralMeasurePVMContinuousLocalPVMKernelComponent s x)

/-- Functional-calculus range/kernel membership target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelMembershipTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember s
        (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x)) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMKernelMember s
        (spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x))

/-- Functional-calculus range/kernel decomposition target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelDecompositionTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
        spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x = x

/-- Functional-calculus range/kernel reprojection target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelReprojectionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
          (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
            spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x) =
        spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMContinuousFunctionalCalculus
          (spectralMeasurePVMSpectralSetSlotIndicatorFunction
            (spectralMeasurePVMSpectralSetSlotComplement s))
          (spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x +
            spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x) =
        spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x)

/-- Genuine functional-calculus range/kernel bridge remains open beyond the R4
local two-slot surface. -/
def SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelBridgeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Component bridge target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_component_bridge_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelComponentBridgeTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_range_component_eq_projection_component,
    spectral_measure_pvm_continuous_functional_calculus_kernel_component_eq_projection_component⟩

/-- Membership target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_membership_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelMembershipTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_range_component_mem_range,
    spectral_measure_pvm_continuous_functional_calculus_kernel_component_mem_kernel⟩

/-- Decomposition target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelDecompositionTarget := by
  exact spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_apply

/-- Reprojection target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_range_kernel_reprojection_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelReprojectionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_first_reprojection_apply,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_complement_reprojection_apply⟩

/-- Genuine functional-calculus range/kernel bridge remains explicitly open. -/
theorem spectral_measure_pvm_genuine_functional_calculus_range_kernel_bridge_still_open_ready :
    SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelBridgeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 functional-calculus range/kernel bridge core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelComponentBridgeTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelMembershipTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelDecompositionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusRangeKernelReprojectionTarget ∧
  SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelBridgeStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus range/kernel bridge core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_bridge_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_order_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_component_bridge_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_membership_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_reprojection_target_ready,
    spectral_measure_pvm_genuine_functional_calculus_range_kernel_bridge_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 functional-calculus range/kernel bridge core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusOrderBoundaryHeld ∧
  SpectralMeasurePVMGenuineFunctionalCalculusRangeKernelBridgeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus range/kernel bridge boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_bridge_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelBridgeBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_bridge_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_order_boundary_held,
    spectral_measure_pvm_genuine_functional_calculus_range_kernel_bridge_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
