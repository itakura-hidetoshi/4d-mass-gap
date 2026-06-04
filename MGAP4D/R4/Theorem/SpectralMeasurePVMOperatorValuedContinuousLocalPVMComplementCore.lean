import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement is involutive on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_complement_involutive
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotComplement s) = s := by
  cases s <;> rfl

/-- A symbolic spectral-set slot union its complement is the whole slot. -/
theorem spectral_measure_pvm_spectral_set_slot_union_complement_whole
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotUnion s
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      SpectralMeasurePVMSpectralSetSlot.wholeSet := by
  cases s <;> rfl

/-- A symbolic spectral-set slot intersect its complement is the empty slot. -/
theorem spectral_measure_pvm_spectral_set_slot_inter_complement_empty
    (s : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotInter s
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      SpectralMeasurePVMSpectralSetSlot.emptySet := by
  cases s <;> rfl

/-- The projection of a slot plus the projection of its complement is the identity
action, pointwise on the Hilbert carrier. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_add_complement_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x = x := by
  cases s <;> simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- The complement projection plus the projection is also the identity action,
pointwise on the Hilbert carrier. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_complement_add_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x = x := by
  cases s <;> simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- A slot projection followed by its complement projection is zero, pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_complement_composition_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x) = 0 := by
  cases s <;> rfl

/-- A complement projection followed by the original slot projection is zero,
pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_composition_complement_zero
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) = 0 := by
  cases s <;> rfl

/-- Complement Boolean laws on the symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotComplementBooleanLawTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotComplement s) = s) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotUnion s
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      SpectralMeasurePVMSpectralSetSlot.wholeSet) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotInter s
        (spectralMeasurePVMSpectralSetSlotComplement s) =
      SpectralMeasurePVMSpectralSetSlot.emptySet)

/-- Complement projection laws for the symbolic spectral-set-slot local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMComplementProjectionLawTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection s x = x)

/-- Complement orthogonality laws for the symbolic spectral-set-slot local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMComplementOrthogonalityTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x) = 0) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) = 0)

/-- Genuine orthogonal-complement projection theorem for the eventual Borel PVM
remains open.  This file only closes the two-slot complement laws. -/
def SpectralMeasurePVMGenuineOrthogonalComplementProjectionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The complement Boolean-law target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_complement_boolean_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotComplementBooleanLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_complement_involutive,
    spectral_measure_pvm_spectral_set_slot_union_complement_whole,
    spectral_measure_pvm_spectral_set_slot_inter_complement_empty⟩

/-- The complement projection-law target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_complement_projection_law_target_ready :
    SpectralMeasurePVMContinuousLocalPVMComplementProjectionLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_add_complement_apply,
    spectral_measure_pvm_spectral_set_slot_projection_complement_add_apply⟩

/-- The complement orthogonality target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_complement_orthogonality_target_ready :
    SpectralMeasurePVMContinuousLocalPVMComplementOrthogonalityTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_complement_composition_zero,
    spectral_measure_pvm_spectral_set_slot_projection_composition_complement_zero⟩

/-- Genuine orthogonal-complement projection remains explicitly open. -/
theorem spectral_measure_pvm_genuine_orthogonal_complement_projection_still_open_ready :
    SpectralMeasurePVMGenuineOrthogonalComplementProjectionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM complement core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotComplementBooleanLawTarget ∧
  SpectralMeasurePVMContinuousLocalPVMComplementProjectionLawTarget ∧
  SpectralMeasurePVMContinuousLocalPVMComplementOrthogonalityTarget ∧
  SpectralMeasurePVMGenuineOrthogonalComplementProjectionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM complement core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_complement_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_symmetry_core_ready,
    spectral_measure_pvm_spectral_set_slot_complement_boolean_law_target_ready,
    spectral_measure_pvm_continuous_local_pvm_complement_projection_law_target_ready,
    spectral_measure_pvm_continuous_local_pvm_complement_orthogonality_target_ready,
    spectral_measure_pvm_genuine_orthogonal_complement_projection_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM complement core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryBoundaryHeld ∧
  SpectralMeasurePVMGenuineOrthogonalComplementProjectionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM complement boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_complement_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_complement_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_symmetry_boundary_held,
    spectral_measure_pvm_genuine_orthogonal_complement_projection_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
