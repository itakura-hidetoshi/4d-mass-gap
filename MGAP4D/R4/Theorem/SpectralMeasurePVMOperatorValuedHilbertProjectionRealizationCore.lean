import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedPVMConstructionLiftSpine

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Carrier-level realization of the two Hilbert projection slots.

This is deliberately only a function-level realization on the existing mathlib
Hilbert carrier.  It does not yet claim boundedness, self-adjointness, or a
continuous-linear projection structure. -/
def spectralMeasurePVMHilbertProjectionSlotCarrierRealizer :
    SpectralMeasurePVMHilbertProjectionSlot →
      MathlibAnalytic.ConcreteL2R1HilbertCarrier →
        MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMHilbertProjectionSlot.zeroProjection => fun _ => 0
  | SpectralMeasurePVMHilbertProjectionSlot.identityProjection => fun x => x

/-- The zero projection slot acts as the zero function on the Hilbert carrier. -/
theorem spectral_measure_pvm_hilbert_projection_slot_zero_realizer_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0 := by
  rfl

/-- The identity projection slot acts as the identity function on the Hilbert carrier. -/
theorem spectral_measure_pvm_hilbert_projection_slot_identity_realizer_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x := by
  rfl

/-- Carrier-level idempotence of the two projection-slot realizers. -/
theorem spectral_measure_pvm_hilbert_projection_slot_carrier_realizer_idempotent
    (slot : SpectralMeasurePVMHilbertProjectionSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot
        (spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x) =
      spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x := by
  cases slot <;> rfl

/-- The concrete spectral index selects the expected carrier-level projection
function. -/
theorem spectral_measure_pvm_hilbert_projection_index_carrier_realizer_empty
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0 := by
  rfl

/-- The whole spectral index selects the identity carrier-level projection
function. -/
theorem spectral_measure_pvm_hilbert_projection_index_carrier_realizer_whole
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x := by
  rfl

/-- Carrier-level projection-function target for the current R4 two-slot surface. -/
def SpectralMeasurePVMHilbertProjectionCarrierFunctionTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x) ∧
  (∀ slot : SpectralMeasurePVMHilbertProjectionSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot
          (spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x) =
        spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x)

/-- Carrier-level compatibility between concrete spectral indices and the
projection-slot realizers. -/
def SpectralMeasurePVMHilbertProjectionIndexCarrierCompatibilityTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotCarrierRealizer
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x)

/-- Linear / bounded / self-adjoint projection upgrade is still open.  The current
file only realizes the zero/identity action as carrier-level functions. -/
def SpectralMeasurePVMHilbertProjectionLinearBoundedSelfAdjointUpgradeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Carrier-level Hilbert projection realization core for R4. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedPVMConstructionLiftSpineReady ∧
  SpectralMeasurePVMHilbertProjectionSlotConcreteLawTarget ∧
  SpectralMeasurePVMHilbertProjectionCarrierFunctionTarget ∧
  SpectralMeasurePVMHilbertProjectionIndexCarrierCompatibilityTarget ∧
  SpectralMeasurePVMHilbertProjectionLinearBoundedSelfAdjointUpgradeStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The carrier-level projection-function target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_carrier_function_target_ready :
    SpectralMeasurePVMHilbertProjectionCarrierFunctionTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_slot_zero_realizer_apply,
    spectral_measure_pvm_hilbert_projection_slot_identity_realizer_apply,
    spectral_measure_pvm_hilbert_projection_slot_carrier_realizer_idempotent⟩

/-- The carrier-level index compatibility target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_index_carrier_compatibility_target_ready :
    SpectralMeasurePVMHilbertProjectionIndexCarrierCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_index_carrier_realizer_empty,
    spectral_measure_pvm_hilbert_projection_index_carrier_realizer_whole⟩

/-- The linear/bounded/self-adjoint upgrade remains explicitly open. -/
theorem spectral_measure_pvm_hilbert_projection_linear_bounded_self_adjoint_upgrade_still_open_ready :
    SpectralMeasurePVMHilbertProjectionLinearBoundedSelfAdjointUpgradeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The carrier-level Hilbert projection realization core is ready. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_realization_core_ready :
    SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_pvm_construction_lift_spine_ready,
    spectral_measure_pvm_hilbert_projection_slot_concrete_law_target_ready,
    spectral_measure_pvm_hilbert_projection_carrier_function_target_ready,
    spectral_measure_pvm_hilbert_projection_index_carrier_compatibility_target_ready,
    spectral_measure_pvm_hilbert_projection_linear_bounded_self_adjoint_upgrade_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the carrier-level Hilbert projection realization. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationCoreReady ∧
  SpectralMeasurePVMOperatorValuedR4BoundaryHeld ∧
  SpectralMeasurePVMHilbertProjectionLinearBoundedSelfAdjointUpgradeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The carrier-level Hilbert projection realization boundary is held. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_realization_boundary_held :
    SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_realization_core_ready,
    spectral_measure_pvm_operator_valued_r4_boundary_held,
    spectral_measure_pvm_hilbert_projection_linear_bounded_self_adjoint_upgrade_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
