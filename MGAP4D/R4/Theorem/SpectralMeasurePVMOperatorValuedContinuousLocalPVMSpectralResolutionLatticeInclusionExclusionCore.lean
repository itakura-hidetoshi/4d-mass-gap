import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- General lattice inclusion-exclusion for range components of canonical
spectral-resolution packets.  This is still the R4-local two-slot surface. -/
theorem spectral_measure_pvm_spectral_resolution_range_lattice_inclusion_exclusion
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent +
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent := by
  exact spectral_measure_pvm_continuous_functional_calculus_slot_indicator_union_inter_inclusion_exclusion s t x

/-- General lattice inclusion-exclusion for kernel components of canonical
spectral-resolution packets. -/
theorem spectral_measure_pvm_spectral_resolution_kernel_lattice_inclusion_exclusion
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s t) x).kernelComponent +
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s t) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent +
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).kernelComponent := by
  cases s <;> cases t <;>
    simp [spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket,
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent,
      spectralMeasurePVMSpectralSetSlotUnion,
      spectralMeasurePVMSpectralSetSlotInter,
      spectralMeasurePVMSpectralSetSlotComplement,
      spectralMeasurePVMSpectralSetSlotIndicatorFunction,
      spectralMeasurePVMConcreteIndexFromSpectralSetSlot,
      spectralMeasurePVMConcreteIndicatorFunction,
      spectralMeasurePVMContinuousFunctionalCalculus]

/-- Union symmetry for range components of canonical spectral-resolution packets. -/
theorem spectral_measure_pvm_spectral_resolution_union_range_component_comm
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion t s) x).rangeComponent := by
  cases s <;> cases t <;> rfl

/-- Intersection symmetry for range components of canonical spectral-resolution packets. -/
theorem spectral_measure_pvm_spectral_resolution_inter_range_component_comm
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter t s) x).rangeComponent := by
  cases s <;> cases t <;> rfl

/-- Union symmetry for kernel components of canonical spectral-resolution packets. -/
theorem spectral_measure_pvm_spectral_resolution_union_kernel_component_comm
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s t) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion t s) x).kernelComponent := by
  cases s <;> cases t <;> rfl

/-- Intersection symmetry for kernel components of canonical spectral-resolution packets. -/
theorem spectral_measure_pvm_spectral_resolution_inter_kernel_component_comm
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s t) x).kernelComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter t s) x).kernelComponent := by
  cases s <;> cases t <;> rfl

/-- Range inclusion-exclusion target for canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionRangeInclusionExclusionTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent +
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent =
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent

/-- Kernel inclusion-exclusion target for canonical spectral-resolution packets. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionKernelInclusionExclusionTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s t) x).kernelComponent +
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s t) x).kernelComponent =
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent +
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).kernelComponent

/-- Lattice symmetry target for canonical spectral-resolution packet components. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionLatticeSymmetryTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion t s) x).rangeComponent) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter t s) x).rangeComponent) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion s t) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotUnion t s) x).kernelComponent) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter s t) x).kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
          (spectralMeasurePVMSpectralSetSlotInter t s) x).kernelComponent)

/-- Genuine lattice inclusion-exclusion for spectral resolutions remains open
beyond the R4 local two-slot surface. -/
def SpectralMeasurePVMGenuineSpectralResolutionLatticeInclusionExclusionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Range inclusion-exclusion is ready. -/
theorem spectral_measure_pvm_spectral_resolution_range_inclusion_exclusion_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionRangeInclusionExclusionTarget := by
  exact spectral_measure_pvm_spectral_resolution_range_lattice_inclusion_exclusion

/-- Kernel inclusion-exclusion is ready. -/
theorem spectral_measure_pvm_spectral_resolution_kernel_inclusion_exclusion_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionKernelInclusionExclusionTarget := by
  exact spectral_measure_pvm_spectral_resolution_kernel_lattice_inclusion_exclusion

/-- Lattice symmetry is ready. -/
theorem spectral_measure_pvm_spectral_resolution_lattice_symmetry_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionLatticeSymmetryTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_union_range_component_comm,
    spectral_measure_pvm_spectral_resolution_inter_range_component_comm,
    spectral_measure_pvm_spectral_resolution_union_kernel_component_comm,
    spectral_measure_pvm_spectral_resolution_inter_kernel_component_comm⟩

/-- Genuine lattice inclusion-exclusion remains explicitly open. -/
theorem spectral_measure_pvm_genuine_spectral_resolution_lattice_inclusion_exclusion_still_open_ready :
    SpectralMeasurePVMGenuineSpectralResolutionLatticeInclusionExclusionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution lattice inclusion-exclusion core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionLatticeInclusionExclusionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionRangeInclusionExclusionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionKernelInclusionExclusionTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionLatticeSymmetryTarget ∧
  SpectralMeasurePVMGenuineSpectralResolutionLatticeInclusionExclusionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution lattice inclusion-exclusion core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_lattice_inclusion_exclusion_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionLatticeInclusionExclusionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_endpoint_absorption_core_ready,
    spectral_measure_pvm_spectral_resolution_range_inclusion_exclusion_target_ready,
    spectral_measure_pvm_spectral_resolution_kernel_inclusion_exclusion_target_ready,
    spectral_measure_pvm_spectral_resolution_lattice_symmetry_target_ready,
    spectral_measure_pvm_genuine_spectral_resolution_lattice_inclusion_exclusion_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution lattice inclusion-exclusion core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionLatticeInclusionExclusionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionLatticeInclusionExclusionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionEndpointAbsorptionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralResolutionLatticeInclusionExclusionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution lattice inclusion-exclusion boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_lattice_inclusion_exclusion_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionLatticeInclusionExclusionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_lattice_inclusion_exclusion_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_endpoint_absorption_boundary_held,
    spectral_measure_pvm_genuine_spectral_resolution_lattice_inclusion_exclusion_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
