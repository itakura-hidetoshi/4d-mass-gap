import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Union is commutative on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_union_comm
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotUnion s t =
      spectralMeasurePVMSpectralSetSlotUnion t s := by
  cases s <;> cases t <;> rfl

/-- Intersection is commutative on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_inter_comm
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotInter s t =
      spectralMeasurePVMSpectralSetSlotInter t s := by
  cases s <;> cases t <;> rfl

/-- Union is associative on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_union_assoc
    (r s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotUnion r s) t =
      spectralMeasurePVMSpectralSetSlotUnion r
        (spectralMeasurePVMSpectralSetSlotUnion s t) := by
  cases r <;> cases s <;> cases t <;> rfl

/-- Intersection is associative on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_inter_assoc
    (r s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotInter r s) t =
      spectralMeasurePVMSpectralSetSlotInter r
        (spectralMeasurePVMSpectralSetSlotInter s t) := by
  cases r <;> cases s <;> cases t <;> rfl

/-- Union absorbs intersection on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_union_absorb_inter
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotUnion s
        (spectralMeasurePVMSpectralSetSlotInter s t) = s := by
  cases s <;> cases t <;> rfl

/-- Intersection absorbs union on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_inter_absorb_union
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotInter s
        (spectralMeasurePVMSpectralSetSlotUnion s t) = s := by
  cases s <;> cases t <;> rfl

/-- Projection of an intersection is pointwise composition of the two local
projections. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_inter_composition_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter s t) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection t x) := by
  cases s <;> cases t <;> rfl

/-- Projection of an intersection is also the reversed pointwise composition. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_inter_reversed_composition_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter s t) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection t
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) := by
  cases s <;> cases t <;> rfl

/-- Inclusion-exclusion for the two symbolic spectral-set-slot projections,
stated pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_union_inter_inclusion_exclusion_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotUnion s t) x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter s t) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection t x := by
  cases s <;> cases t <;>
    simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
      spectralMeasurePVMSpectralSetSlotUnion,
      spectralMeasurePVMSpectralSetSlotInter]

/-- Boolean lattice laws on the symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotBooleanLatticeLawTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotUnion s t =
      spectralMeasurePVMSpectralSetSlotUnion t s) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotInter s t =
      spectralMeasurePVMSpectralSetSlotInter t s) ∧
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotUnion r s) t =
      spectralMeasurePVMSpectralSetSlotUnion r
        (spectralMeasurePVMSpectralSetSlotUnion s t)) ∧
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotInter r s) t =
      spectralMeasurePVMSpectralSetSlotInter r
        (spectralMeasurePVMSpectralSetSlotInter s t)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotUnion s
        (spectralMeasurePVMSpectralSetSlotInter s t) = s) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotInter s
        (spectralMeasurePVMSpectralSetSlotUnion s t) = s)

/-- Lattice/projection compatibility laws for the R4 local PVM. -/
def SpectralMeasurePVMContinuousLocalPVMLatticeProjectionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter s t) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMSpectralSetSlotContinuousProjection t x)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter s t) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection t
          (spectralMeasurePVMSpectralSetSlotContinuousProjection s x)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotUnion s t) x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotInter s t) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection t x)

/-- Genuine Boolean-algebra/Borel-lattice compatibility for the eventual spectral
measure remains open. -/
def SpectralMeasurePVMGenuineBooleanLatticeCompatibilityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Boolean lattice law target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_boolean_lattice_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotBooleanLatticeLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_union_comm,
    spectral_measure_pvm_spectral_set_slot_inter_comm,
    spectral_measure_pvm_spectral_set_slot_union_assoc,
    spectral_measure_pvm_spectral_set_slot_inter_assoc,
    spectral_measure_pvm_spectral_set_slot_union_absorb_inter,
    spectral_measure_pvm_spectral_set_slot_inter_absorb_union⟩

/-- The lattice/projection compatibility target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_lattice_projection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMLatticeProjectionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_inter_composition_apply,
    spectral_measure_pvm_spectral_set_slot_projection_inter_reversed_composition_apply,
    spectral_measure_pvm_spectral_set_slot_projection_union_inter_inclusion_exclusion_apply⟩

/-- Genuine Boolean-lattice compatibility remains explicitly open. -/
theorem spectral_measure_pvm_genuine_boolean_lattice_compatibility_still_open_ready :
    SpectralMeasurePVMGenuineBooleanLatticeCompatibilityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM lattice core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotBooleanLatticeLawTarget ∧
  SpectralMeasurePVMContinuousLocalPVMLatticeProjectionTarget ∧
  SpectralMeasurePVMGenuineBooleanLatticeCompatibilityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM lattice core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_lattice_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_complement_core_ready,
    spectral_measure_pvm_spectral_set_slot_boolean_lattice_law_target_ready,
    spectral_measure_pvm_continuous_local_pvm_lattice_projection_target_ready,
    spectral_measure_pvm_genuine_boolean_lattice_compatibility_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM lattice core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMComplementBoundaryHeld ∧
  SpectralMeasurePVMGenuineBooleanLatticeCompatibilityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM lattice boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_lattice_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_lattice_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_complement_boundary_held,
    spectral_measure_pvm_genuine_boolean_lattice_compatibility_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
