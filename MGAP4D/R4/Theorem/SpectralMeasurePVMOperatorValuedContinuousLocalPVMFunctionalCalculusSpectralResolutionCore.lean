import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- A concrete R4-local spectral-resolution packet for a symbolic spectral-set
slot `s` and a vector `x`.  It records a range component, a kernel component,
and their reconstruction of `x`.  This is still the two-slot local surface, not
a genuine spectral-resolution theorem for a Borel PVM. -/
structure SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) where
  rangeComponent : MathlibAnalytic.ConcreteL2R1HilbertCarrier
  kernelComponent : MathlibAnalytic.ConcreteL2R1HilbertCarrier
  rangeMembership : SpectralMeasurePVMContinuousLocalPVMRangeMember s rangeComponent
  kernelMembership : SpectralMeasurePVMContinuousLocalPVMKernelMember s kernelComponent
  reconstructs : rangeComponent + kernelComponent = x

/-- The canonical R4-local functional-calculus spectral-resolution packet. -/
def spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x where
  rangeComponent := spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x
  kernelComponent := spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x
  rangeMembership :=
    spectral_measure_pvm_continuous_functional_calculus_range_component_mem_range s x
  kernelMembership :=
    spectral_measure_pvm_continuous_functional_calculus_kernel_component_mem_kernel s x
  reconstructs :=
    spectral_measure_pvm_continuous_functional_calculus_range_kernel_decomposition_apply s x

/-- The canonical packet's range component is `FC(χ_s)x`. -/
theorem spectral_measure_pvm_continuous_functional_calculus_canonical_resolution_range_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent =
      spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x := by
  rfl

/-- The canonical packet's kernel component is `FC(χ_{sᶜ})x`. -/
theorem spectral_measure_pvm_continuous_functional_calculus_canonical_resolution_kernel_component
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent =
      spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x := by
  rfl

/-- The canonical packet reconstructs the original vector. -/
theorem spectral_measure_pvm_continuous_functional_calculus_canonical_resolution_reconstructs
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent = x := by
  exact (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).reconstructs

/-- Any R4-local spectral-resolution packet has the canonical functional-calculus
range component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_range_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (p : SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x) :
    p.rangeComponent = spectralMeasurePVMContinuousFunctionalCalculusRangeComponent s x := by
  exact (spectral_measure_pvm_continuous_functional_calculus_range_kernel_uniqueness_target_ready
    s x p.rangeComponent p.kernelComponent p.rangeMembership p.kernelMembership p.reconstructs.symm).1

/-- Any R4-local spectral-resolution packet has the canonical functional-calculus
kernel component. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_kernel_component_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (p : SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x) :
    p.kernelComponent = spectralMeasurePVMContinuousFunctionalCalculusKernelComponent s x := by
  exact (spectral_measure_pvm_continuous_functional_calculus_range_kernel_uniqueness_target_ready
    s x p.rangeComponent p.kernelComponent p.rangeMembership p.kernelMembership p.reconstructs.symm).2

/-- Any R4-local spectral-resolution packet has the same components as the
canonical packet. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_packet_unique
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (p : SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x) :
    p.rangeComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent ∧
      p.kernelComponent =
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_range_component_unique s x p,
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_kernel_component_unique s x p⟩

/-- Canonical packet existence target for the R4-local functional-calculus spectral
resolution. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistenceTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x

/-- Canonical packet uniqueness target for the R4-local functional-calculus spectral
resolution. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionUniquenessTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      ∀ p : SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionPacket s x,
        p.rangeComponent =
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent ∧
          p.kernelComponent =
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).kernelComponent

/-- The canonical packet existence target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_existence_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistenceTarget := by
  intro s x
  exact spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x

/-- The canonical packet uniqueness target is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_uniqueness_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionUniquenessTarget := by
  intro s x p
  exact spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_packet_unique s x p

/-- Existence plus uniqueness packet for the R4-local functional-calculus spectral
resolution. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistUniqueTarget : Prop :=
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistenceTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionUniquenessTarget

/-- Existence plus uniqueness of the R4-local functional-calculus spectral
resolution is ready. -/
theorem spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_exist_unique_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistUniqueTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_existence_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_uniqueness_target_ready⟩

/-- Genuine spectral-resolution theorem remains open beyond this R4-local
functional-calculus packet. -/
def SpectralMeasurePVMGenuineFunctionalCalculusSpectralResolutionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Genuine spectral-resolution theorem remains explicitly open. -/
theorem spectral_measure_pvm_genuine_functional_calculus_spectral_resolution_still_open_ready :
    SpectralMeasurePVMGenuineFunctionalCalculusSpectralResolutionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 functional-calculus spectral-resolution core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistenceTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionUniquenessTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionExistUniqueTarget ∧
  SpectralMeasurePVMGenuineFunctionalCalculusSpectralResolutionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus spectral-resolution core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_spectral_resolution_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_uniqueness_core_ready,
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_existence_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_uniqueness_target_ready,
    spectral_measure_pvm_continuous_functional_calculus_spectral_resolution_exist_unique_target_ready,
    spectral_measure_pvm_genuine_functional_calculus_spectral_resolution_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 functional-calculus spectral-resolution core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusRangeKernelUniquenessBoundaryHeld ∧
  SpectralMeasurePVMGenuineFunctionalCalculusSpectralResolutionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 functional-calculus spectral-resolution boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_spectral_resolution_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMFunctionalCalculusSpectralResolutionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_spectral_resolution_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_functional_calculus_range_kernel_uniqueness_boundary_held,
    spectral_measure_pvm_genuine_functional_calculus_spectral_resolution_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
