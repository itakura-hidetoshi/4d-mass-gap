import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Order relation on the two symbolic spectral-set slots.  `emptySet` is below
everything and `wholeSet` is only below itself. -/
def SpectralMeasurePVMSpectralSetSlotSubset :
    SpectralMeasurePVMSpectralSetSlot → SpectralMeasurePVMSpectralSetSlot → Prop
  | SpectralMeasurePVMSpectralSetSlot.emptySet, _ => True
  | SpectralMeasurePVMSpectralSetSlot.wholeSet,
      SpectralMeasurePVMSpectralSetSlot.wholeSet => True
  | SpectralMeasurePVMSpectralSetSlot.wholeSet,
      SpectralMeasurePVMSpectralSetSlot.emptySet => False

/-- Reflexivity of the two-slot order. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_refl
    (s : SpectralMeasurePVMSpectralSetSlot) :
    SpectralMeasurePVMSpectralSetSlotSubset s s := by
  cases s <;> trivial

/-- Antisymmetry of the two-slot order. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_antisymm
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (hts : SpectralMeasurePVMSpectralSetSlotSubset t s) :
    s = t := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst
  exact False.elim hts

/-- Transitivity of the two-slot order. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_trans
    (r s t : SpectralMeasurePVMSpectralSetSlot)
    (hrs : SpectralMeasurePVMSpectralSetSlotSubset r s)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t) :
    SpectralMeasurePVMSpectralSetSlotSubset r t := by
  cases r <;> cases s <;> cases t <;> try trivial
  exact False.elim hrs
  exact False.elim hst

/-- Complement is antitone on the two-slot order. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_complement_antitone
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t) :
    SpectralMeasurePVMSpectralSetSlotSubset
      (spectralMeasurePVMSpectralSetSlotComplement t)
      (spectralMeasurePVMSpectralSetSlotComplement s) := by
  cases s <;> cases t <;> try trivial
  exact False.elim hst

/-- If `s ⊆ t`, then `s ∪ t = t`. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_union_right
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t) :
    spectralMeasurePVMSpectralSetSlotUnion s t = t := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- If `s ⊆ t`, then `s ∩ t = s`. -/
theorem spectral_measure_pvm_spectral_set_slot_subset_inter_left
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t) :
    spectralMeasurePVMSpectralSetSlotInter s t = s := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Projection monotonicity: if `s ⊆ t`, then `P(t) P(s) = P(s)` pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_subset_right_absorption_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection t
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Projection monotonicity: if `s ⊆ t`, then `P(s) P(t) = P(s)` pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_subset_left_absorption_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotSubset s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Order laws for the two symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotOrderLawTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s s) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      SpectralMeasurePVMSpectralSetSlotSubset t s → s = t) ∧
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset r s →
      SpectralMeasurePVMSpectralSetSlotSubset s t →
        SpectralMeasurePVMSpectralSetSlotSubset r t) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      SpectralMeasurePVMSpectralSetSlotSubset
        (spectralMeasurePVMSpectralSetSlotComplement t)
        (spectralMeasurePVMSpectralSetSlotComplement s))

/-- Order/lattice compatibility target for the two-slot surface. -/
def SpectralMeasurePVMSpectralSetSlotOrderLatticeCompatibilityTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      spectralMeasurePVMSpectralSetSlotUnion s t = t) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      spectralMeasurePVMSpectralSetSlotInter s t = s)

/-- Projection monotonicity target for the R4 local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMOrderProjectionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMSpectralSetSlotContinuousProjection t
            (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) =
          spectralMeasurePVMSpectralSetSlotContinuousProjection s x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotSubset s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMSpectralSetSlotContinuousProjection s
            (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) =
          spectralMeasurePVMSpectralSetSlotContinuousProjection s x)

/-- Genuine monotone Borel projection theorem remains open. -/
def SpectralMeasurePVMGenuineMonotoneBorelProjectionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The two-slot order-law target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_order_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotOrderLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_subset_refl,
    spectral_measure_pvm_spectral_set_slot_subset_antisymm,
    spectral_measure_pvm_spectral_set_slot_subset_trans,
    spectral_measure_pvm_spectral_set_slot_subset_complement_antitone⟩

/-- The order/lattice compatibility target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_order_lattice_compatibility_target_ready :
    SpectralMeasurePVMSpectralSetSlotOrderLatticeCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_subset_union_right,
    spectral_measure_pvm_spectral_set_slot_subset_inter_left⟩

/-- The projection monotonicity target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_order_projection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMOrderProjectionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_subset_right_absorption_apply,
    spectral_measure_pvm_spectral_set_slot_projection_subset_left_absorption_apply⟩

/-- Genuine monotone Borel projection theorem remains explicitly open. -/
theorem spectral_measure_pvm_genuine_monotone_borel_projection_still_open_ready :
    SpectralMeasurePVMGenuineMonotoneBorelProjectionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM order core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotOrderLawTarget ∧
  SpectralMeasurePVMSpectralSetSlotOrderLatticeCompatibilityTarget ∧
  SpectralMeasurePVMContinuousLocalPVMOrderProjectionTarget ∧
  SpectralMeasurePVMGenuineMonotoneBorelProjectionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM order core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_order_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_partition_core_ready,
    spectral_measure_pvm_spectral_set_slot_order_law_target_ready,
    spectral_measure_pvm_spectral_set_slot_order_lattice_compatibility_target_ready,
    spectral_measure_pvm_continuous_local_pvm_order_projection_target_ready,
    spectral_measure_pvm_genuine_monotone_borel_projection_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM order core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionBoundaryHeld ∧
  SpectralMeasurePVMGenuineMonotoneBorelProjectionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM order boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_order_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMOrderBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_order_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_partition_boundary_held,
    spectral_measure_pvm_genuine_monotone_borel_projection_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
