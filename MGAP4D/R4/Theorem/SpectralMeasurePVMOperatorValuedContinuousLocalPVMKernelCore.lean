import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Kernel membership for the R4 local PVM projection attached to a symbolic
spectral-set slot.  This is a pointwise kernel surface, not yet a closed Hilbert
subspace theorem. -/
def SpectralMeasurePVMContinuousLocalPVMKernelMember
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) : Prop :=
  spectralMeasurePVMSpectralSetSlotContinuousProjection s x = 0

/-- Every vector is in the kernel of the empty-slot projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_empty_kernel_all
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember
      SpectralMeasurePVMSpectralSetSlot.emptySet x := by
  rfl

/-- A vector in the kernel of the whole-slot projection is zero. -/
theorem spectral_measure_pvm_continuous_local_pvm_whole_kernel_member_eq_zero
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMKernelMember
      SpectralMeasurePVMSpectralSetSlot.wholeSet x) :
    x = 0 := by
  exact hx

/-- Zero is in the kernel of the whole-slot projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_whole_kernel_zero :
    SpectralMeasurePVMContinuousLocalPVMKernelMember
      SpectralMeasurePVMSpectralSetSlot.wholeSet
      (0 : MathlibAnalytic.ConcreteL2R1HilbertCarrier) := by
  rfl

/-- Vectors in the complement range are killed by the original projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_complement_range_subset_kernel
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMRangeMember
      (spectralMeasurePVMSpectralSetSlotComplement s) x) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s x := by
  rcases hx with ⟨y, hy⟩
  rw [← hy]
  exact spectral_measure_pvm_spectral_set_slot_projection_complement_composition_zero s y

/-- Vectors killed by the original projection lie in the complement range. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_subset_complement_range
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMKernelMember s x) :
    SpectralMeasurePVMContinuousLocalPVMRangeMember
      (spectralMeasurePVMSpectralSetSlotComplement s) x := by
  cases s
  · exact spectral_measure_pvm_continuous_local_pvm_whole_range_all x
  · exact ⟨0, hx.symm⟩

/-- Kernel membership is equivalent to complement-range membership on the R4
local two-slot surface, stated as two implications to avoid importing additional
iff machinery. -/
def SpectralMeasurePVMContinuousLocalPVMKernelComplementRangeTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMRangeMember
        (spectralMeasurePVMSpectralSetSlotComplement s) x →
        SpectralMeasurePVMContinuousLocalPVMKernelMember s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      SpectralMeasurePVMContinuousLocalPVMKernelMember s x →
        SpectralMeasurePVMContinuousLocalPVMRangeMember
          (spectralMeasurePVMSpectralSetSlotComplement s) x)

/-- Basic kernel target for empty and whole slots. -/
def SpectralMeasurePVMContinuousLocalPVMBasicKernelTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    SpectralMeasurePVMContinuousLocalPVMKernelMember
      SpectralMeasurePVMSpectralSetSlot.emptySet x) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    SpectralMeasurePVMContinuousLocalPVMKernelMember
      SpectralMeasurePVMSpectralSetSlot.wholeSet x → x = 0) ∧
  SpectralMeasurePVMContinuousLocalPVMKernelMember
    SpectralMeasurePVMSpectralSetSlot.wholeSet
    (0 : MathlibAnalytic.ConcreteL2R1HilbertCarrier)

/-- Order-induced kernel antitonicity: if `s ⊆ t`, then `Ker P(t) ⊆ Ker P(s)`. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_antitone_of_subset
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier)
    (hx : SpectralMeasurePVMContinuousLocalPVMKernelMember t x) :
    SpectralMeasurePVMContinuousLocalPVMKernelMember s x := by
  apply spectral_measure_pvm_continuous_local_pvm_complement_range_subset_kernel
  exact spectral_measure_pvm_continuous_local_pvm_complement_range_inclusion_of_subset
    s t hst x
    (spectral_measure_pvm_continuous_local_pvm_kernel_subset_complement_range t x hx)

/-- Kernel antitonicity target for the R4 local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMKernelAntitoneTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        SpectralMeasurePVMContinuousLocalPVMKernelMember t x →
          SpectralMeasurePVMContinuousLocalPVMKernelMember s x

/-- Genuine Hilbert kernel/complement-range theorem remains open. -/
def SpectralMeasurePVMGenuineKernelComplementRangeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The basic kernel target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_basic_kernel_target_ready :
    SpectralMeasurePVMContinuousLocalPVMBasicKernelTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_empty_kernel_all,
    spectral_measure_pvm_continuous_local_pvm_whole_kernel_member_eq_zero,
    spectral_measure_pvm_continuous_local_pvm_whole_kernel_zero⟩

/-- The kernel/complement-range target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_complement_range_target_ready :
    SpectralMeasurePVMContinuousLocalPVMKernelComplementRangeTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_complement_range_subset_kernel,
    spectral_measure_pvm_continuous_local_pvm_kernel_subset_complement_range⟩

/-- The kernel antitonicity target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_kernel_antitone_target_ready :
    SpectralMeasurePVMContinuousLocalPVMKernelAntitoneTarget := by
  exact spectral_measure_pvm_continuous_local_pvm_kernel_antitone_of_subset

/-- Genuine kernel/complement-range theorem remains explicitly open. -/
theorem spectral_measure_pvm_genuine_kernel_complement_range_still_open_ready :
    SpectralMeasurePVMGenuineKernelComplementRangeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM kernel core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeCoreReady ∧
  SpectralMeasurePVMContinuousLocalPVMBasicKernelTarget ∧
  SpectralMeasurePVMContinuousLocalPVMKernelComplementRangeTarget ∧
  SpectralMeasurePVMContinuousLocalPVMKernelAntitoneTarget ∧
  SpectralMeasurePVMGenuineKernelComplementRangeStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM kernel core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_kernel_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_core_ready,
    spectral_measure_pvm_continuous_local_pvm_basic_kernel_target_ready,
    spectral_measure_pvm_continuous_local_pvm_kernel_complement_range_target_ready,
    spectral_measure_pvm_continuous_local_pvm_kernel_antitone_target_ready,
    spectral_measure_pvm_genuine_kernel_complement_range_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM kernel core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMRangeBoundaryHeld ∧
  SpectralMeasurePVMGenuineKernelComplementRangeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM kernel boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_kernel_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMKernelBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_kernel_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_range_boundary_held,
    spectral_measure_pvm_genuine_kernel_complement_range_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
