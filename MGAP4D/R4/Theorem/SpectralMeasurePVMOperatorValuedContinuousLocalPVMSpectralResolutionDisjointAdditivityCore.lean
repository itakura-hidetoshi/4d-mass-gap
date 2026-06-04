import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- For disjoint slots, the canonical spectral-resolution range component of the
union is the sum of the two range components.  This is the R4-local two-slot
surface, not a genuine Hilbert-space spectral-resolution additivity theorem. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_union_range_component_add
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent := by
  exact spectral_measure_pvm_continuous_functional_calculus_disjoint_union_add_apply s t hst x

/-- For disjoint slots, the canonical spectral-resolution range component of the
intersection is zero. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_inter_range_component_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
        (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent = 0 := by
  exact spectral_measure_pvm_continuous_functional_calculus_disjoint_inter_zero_apply s t hst x

/-- For disjoint slots, the `s` indicator functional calculus kills the `t` range
component. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_range_component_projection_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent = 0 := by
  exact spectral_measure_pvm_continuous_functional_calculus_disjoint_composition_zero_apply s t hst x

/-- For disjoint slots, the reversed range-component projection is zero. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_range_component_reversed_projection_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0 := by
  exact spectral_measure_pvm_continuous_functional_calculus_disjoint_reversed_composition_zero_apply s t hst x

/-- For disjoint slots, the range component of the union packet is fixed by the
union indicator functional calculus. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_union_range_component_fixed
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMSpectralSetSlotDisjoint s t)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMContinuousFunctionalCalculus
        (spectralMeasurePVMSpectralSetSlotIndicatorFunction
          (spectralMeasurePVMSpectralSetSlotUnion s t))
        ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent) =
      (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent := by
  rw [← spectral_measure_pvm_spectral_resolution_disjoint_union_range_component_add s t hst x]
  exact spectral_measure_pvm_continuous_functional_calculus_slot_indicator_idempotent_apply
    (spectralMeasurePVMSpectralSetSlotUnion s t) x

/-- Disjoint spectral-resolution range additivity target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeAdditivityTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
            (spectralMeasurePVMSpectralSetSlotUnion s t) x).rangeComponent =
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent

/-- Disjoint spectral-resolution intersection-zero target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointInterZeroTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket
            (spectralMeasurePVMSpectralSetSlotInter s t) x).rangeComponent = 0

/-- Disjoint spectral-resolution range orthogonality target through indicator
functional calculus. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeOrthogonalityTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction s)
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent = 0) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction t)
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent = 0)

/-- Disjoint spectral-resolution union-range fixed target. -/
def SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointUnionFixedTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMSpectralSetSlotDisjoint s t →
      ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
        spectralMeasurePVMContinuousFunctionalCalculus
            (spectralMeasurePVMSpectralSetSlotIndicatorFunction
              (spectralMeasurePVMSpectralSetSlotUnion s t))
            ((spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
              (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent) =
          (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket s x).rangeComponent +
            (spectralMeasurePVMContinuousFunctionalCalculusCanonicalSpectralResolutionPacket t x).rangeComponent

/-- Genuine disjoint spectral-resolution additivity remains open beyond the R4
local two-slot surface. -/
def SpectralMeasurePVMGenuineDisjointSpectralResolutionAdditivityStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The disjoint range additivity target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_range_additivity_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeAdditivityTarget := by
  exact spectral_measure_pvm_spectral_resolution_disjoint_union_range_component_add

/-- The disjoint intersection-zero target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_inter_zero_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointInterZeroTarget := by
  exact spectral_measure_pvm_spectral_resolution_disjoint_inter_range_component_zero

/-- The disjoint range orthogonality target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_range_orthogonality_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeOrthogonalityTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_resolution_disjoint_range_component_projection_zero,
    spectral_measure_pvm_spectral_resolution_disjoint_range_component_reversed_projection_zero⟩

/-- The disjoint union fixed target is ready. -/
theorem spectral_measure_pvm_spectral_resolution_disjoint_union_fixed_target_ready :
    SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointUnionFixedTarget := by
  exact spectral_measure_pvm_spectral_resolution_disjoint_union_range_component_fixed

/-- Genuine disjoint spectral-resolution additivity remains explicitly open. -/
theorem spectral_measure_pvm_genuine_disjoint_spectral_resolution_additivity_still_open_ready :
    SpectralMeasurePVMGenuineDisjointSpectralResolutionAdditivityStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 spectral-resolution disjoint additivity core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderCoreReady ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeAdditivityTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointInterZeroTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointRangeOrthogonalityTarget ∧
  SpectralMeasurePVMContinuousFunctionalCalculusSpectralResolutionDisjointUnionFixedTarget ∧
  SpectralMeasurePVMGenuineDisjointSpectralResolutionAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution disjoint additivity core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_disjoint_additivity_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_order_core_ready,
    spectral_measure_pvm_spectral_resolution_disjoint_range_additivity_target_ready,
    spectral_measure_pvm_spectral_resolution_disjoint_inter_zero_target_ready,
    spectral_measure_pvm_spectral_resolution_disjoint_range_orthogonality_target_ready,
    spectral_measure_pvm_spectral_resolution_disjoint_union_fixed_target_ready,
    spectral_measure_pvm_genuine_disjoint_spectral_resolution_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 spectral-resolution disjoint additivity core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionOrderBoundaryHeld ∧
  SpectralMeasurePVMGenuineDisjointSpectralResolutionAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 spectral-resolution disjoint additivity boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_disjoint_additivity_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSpectralResolutionDisjointAdditivityBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_disjoint_additivity_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_spectral_resolution_order_boundary_held,
    spectral_measure_pvm_genuine_disjoint_spectral_resolution_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
