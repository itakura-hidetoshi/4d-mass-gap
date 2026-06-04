import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- De Morgan law for complement of union on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_complement_union_demorgan
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotComplement t) := by
  cases s <;> cases t <;> rfl

/-- De Morgan law for complement of intersection on the two symbolic spectral-set
slots. -/
theorem spectral_measure_pvm_spectral_set_slot_complement_inter_demorgan
    (s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotComplement t) := by
  cases s <;> cases t <;> rfl

/-- Union distributes over intersection on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_union_distrib_inter
    (r s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotUnion r
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotUnion r s)
        (spectralMeasurePVMSpectralSetSlotUnion r t) := by
  cases r <;> cases s <;> cases t <;> rfl

/-- Intersection distributes over union on the two symbolic spectral-set slots. -/
theorem spectral_measure_pvm_spectral_set_slot_inter_distrib_union
    (r s t : SpectralMeasurePVMSpectralSetSlot) :
    spectralMeasurePVMSpectralSetSlotInter r
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotInter r s)
        (spectralMeasurePVMSpectralSetSlotInter r t) := by
  cases r <;> cases s <;> cases t <;> rfl

/-- Projection compatibility for De Morgan complement of union, stated pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_complement_union_demorgan_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement
          (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMSpectralSetSlotComplement t)) x := by
  cases s <;> cases t <;> rfl

/-- Projection compatibility for De Morgan complement of intersection, stated
pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_complement_inter_demorgan_apply
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement
          (spectralMeasurePVMSpectralSetSlotInter s t)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotUnion
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMSpectralSetSlotComplement t)) x := by
  cases s <;> cases t <;> rfl

/-- Projection compatibility for union distributing over intersection. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_union_distrib_inter_apply
    (r s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotUnion r
          (spectralMeasurePVMSpectralSetSlotInter s t)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter
          (spectralMeasurePVMSpectralSetSlotUnion r s)
          (spectralMeasurePVMSpectralSetSlotUnion r t)) x := by
  cases r <;> cases s <;> cases t <;> rfl

/-- Projection compatibility for intersection distributing over union. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_inter_distrib_union_apply
    (r s t : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter r
          (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotUnion
          (spectralMeasurePVMSpectralSetSlotInter r s)
          (spectralMeasurePVMSpectralSetSlotInter r t)) x := by
  cases r <;> cases s <;> cases t <;> rfl

/-- De Morgan laws on the two symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotDeMorganLawTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotComplement t)) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotComplement
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotComplement t))

/-- Distributivity laws on the two symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotDistributiveLawTarget : Prop :=
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotUnion r
        (spectralMeasurePVMSpectralSetSlotInter s t) =
      spectralMeasurePVMSpectralSetSlotInter
        (spectralMeasurePVMSpectralSetSlotUnion r s)
        (spectralMeasurePVMSpectralSetSlotUnion r t)) ∧
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    spectralMeasurePVMSpectralSetSlotInter r
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMSpectralSetSlotUnion
        (spectralMeasurePVMSpectralSetSlotInter r s)
        (spectralMeasurePVMSpectralSetSlotInter r t))

/-- Projection compatibility for De Morgan laws. -/
def SpectralMeasurePVMContinuousLocalPVMDeMorganProjectionTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement
            (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter
            (spectralMeasurePVMSpectralSetSlotComplement s)
            (spectralMeasurePVMSpectralSetSlotComplement t)) x) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement
            (spectralMeasurePVMSpectralSetSlotInter s t)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotUnion
            (spectralMeasurePVMSpectralSetSlotComplement s)
            (spectralMeasurePVMSpectralSetSlotComplement t)) x)

/-- Projection compatibility for distributivity laws. -/
def SpectralMeasurePVMContinuousLocalPVMDistributiveProjectionTarget : Prop :=
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotUnion r
            (spectralMeasurePVMSpectralSetSlotInter s t)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter
            (spectralMeasurePVMSpectralSetSlotUnion r s)
            (spectralMeasurePVMSpectralSetSlotUnion r t)) x) ∧
  (∀ r s t : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter r
            (spectralMeasurePVMSpectralSetSlotUnion s t)) x =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotUnion
            (spectralMeasurePVMSpectralSetSlotInter r s)
            (spectralMeasurePVMSpectralSetSlotInter r t)) x)

/-- Genuine Boolean-algebra completion for the eventual Borel spectral measure
remains open. -/
def SpectralMeasurePVMGenuineBooleanAlgebraCompletionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- De Morgan target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_demorgan_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotDeMorganLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_complement_union_demorgan,
    spectral_measure_pvm_spectral_set_slot_complement_inter_demorgan⟩

/-- Distributivity target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_distributive_law_target_ready :
    SpectralMeasurePVMSpectralSetSlotDistributiveLawTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_union_distrib_inter,
    spectral_measure_pvm_spectral_set_slot_inter_distrib_union⟩

/-- De Morgan projection target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_demorgan_projection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMDeMorganProjectionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_complement_union_demorgan_apply,
    spectral_measure_pvm_spectral_set_slot_projection_complement_inter_demorgan_apply⟩

/-- Distributive projection target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_distributive_projection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMDistributiveProjectionTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_union_distrib_inter_apply,
    spectral_measure_pvm_spectral_set_slot_projection_inter_distrib_union_apply⟩

/-- Genuine Boolean-algebra completion remains explicitly open. -/
theorem spectral_measure_pvm_genuine_boolean_algebra_completion_still_open_ready :
    SpectralMeasurePVMGenuineBooleanAlgebraCompletionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM Boolean algebra core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotDeMorganLawTarget ∧
  SpectralMeasurePVMSpectralSetSlotDistributiveLawTarget ∧
  SpectralMeasurePVMContinuousLocalPVMDeMorganProjectionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMDistributiveProjectionTarget ∧
  SpectralMeasurePVMGenuineBooleanAlgebraCompletionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM Boolean algebra core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_boolean_algebra_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_lattice_core_ready,
    spectral_measure_pvm_spectral_set_slot_demorgan_law_target_ready,
    spectral_measure_pvm_spectral_set_slot_distributive_law_target_ready,
    spectral_measure_pvm_continuous_local_pvm_demorgan_projection_target_ready,
    spectral_measure_pvm_continuous_local_pvm_distributive_projection_target_ready,
    spectral_measure_pvm_genuine_boolean_algebra_completion_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM Boolean algebra core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMLatticeBoundaryHeld ∧
  SpectralMeasurePVMGenuineBooleanAlgebraCompletionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM Boolean algebra boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_boolean_algebra_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_boolean_algebra_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_lattice_boundary_held,
    spectral_measure_pvm_genuine_boolean_algebra_completion_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
