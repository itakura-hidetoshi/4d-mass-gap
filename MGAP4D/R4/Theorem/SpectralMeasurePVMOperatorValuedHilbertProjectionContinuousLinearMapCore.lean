import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Continuous-linear-map realization of the two Hilbert projection slots on the
concrete mathlib Hilbert carrier.

This upgrades the zero/id linear maps to bundled `ContinuousLinearMap`s.  It
still does not claim that these are the projections of a genuine spectral
measure, nor does it consume the later compact plaquette / `33/20` / positive
weight stages. -/
def spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap :
    SpectralMeasurePVMHilbertProjectionSlot →
      MathlibAnalytic.ConcreteL2R1HilbertCarrier →L[ℝ]
        MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMHilbertProjectionSlot.zeroProjection => 0
  | SpectralMeasurePVMHilbertProjectionSlot.identityProjection =>
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier

/-- The zero projection slot continuous linear map evaluates to zero. -/
theorem spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_zero_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0 := by
  rfl

/-- The identity projection slot continuous linear map evaluates to the input. -/
theorem spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_identity_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x := by
  rfl

/-- The continuous-linear-map realization agrees pointwise with the linear-map
realization. -/
theorem spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_agrees_with_linear_map
    (slot : SpectralMeasurePVMHilbertProjectionSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x =
      spectralMeasurePVMHilbertProjectionSlotLinearMap slot x := by
  cases slot <;> rfl

/-- Pointwise idempotence of the continuous-linear-map projection-slot realizers. -/
theorem spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_pointwise_idempotent
    (slot : SpectralMeasurePVMHilbertProjectionSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot
        (spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x) =
      spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x := by
  cases slot <;> rfl

/-- Empty index selects the zero continuous-linear-map action. -/
theorem spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_empty
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0 := by
  rfl

/-- Whole index selects the identity continuous-linear-map action. -/
theorem spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_whole
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x := by
  rfl

/-- Continuous-linear-map realization target for the two Hilbert projection slots. -/
def SpectralMeasurePVMHilbertProjectionContinuousLinearMapTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x) ∧
  (∀ slot : SpectralMeasurePVMHilbertProjectionSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x =
        spectralMeasurePVMHilbertProjectionSlotLinearMap slot x) ∧
  (∀ slot : SpectralMeasurePVMHilbertProjectionSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot
          (spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x) =
        spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap slot x)

/-- Index compatibility for the continuous-linear-map realization. -/
def SpectralMeasurePVMHilbertProjectionIndexContinuousLinearMapCompatibilityTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x)

/-- Self-adjoint spectral-projection upgrade is still open after the continuous
linear map realization. -/
def SpectralMeasurePVMHilbertProjectionSelfAdjointSpectralProjectionUpgradeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Continuous-linear-map Hilbert projection core for R4. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapCoreReady ∧
  SpectralMeasurePVMHilbertProjectionContinuousLinearMapTarget ∧
  SpectralMeasurePVMHilbertProjectionIndexContinuousLinearMapCompatibilityTarget ∧
  SpectralMeasurePVMHilbertProjectionSelfAdjointSpectralProjectionUpgradeStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The continuous-linear-map realization target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_continuous_linear_map_target_ready :
    SpectralMeasurePVMHilbertProjectionContinuousLinearMapTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_zero_apply,
    spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_identity_apply,
    spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_agrees_with_linear_map,
    spectral_measure_pvm_hilbert_projection_slot_continuous_linear_map_pointwise_idempotent⟩

/-- The index-continuous-linear-map compatibility target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_compatibility_target_ready :
    SpectralMeasurePVMHilbertProjectionIndexContinuousLinearMapCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_empty,
    spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_whole⟩

/-- The self-adjoint spectral-projection upgrade remains explicitly open. -/
theorem spectral_measure_pvm_hilbert_projection_self_adjoint_spectral_projection_upgrade_still_open_ready :
    SpectralMeasurePVMHilbertProjectionSelfAdjointSpectralProjectionUpgradeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 Hilbert projection continuous-linear-map core is ready. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_continuous_linear_map_core_ready :
    SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_linear_map_core_ready,
    spectral_measure_pvm_hilbert_projection_continuous_linear_map_target_ready,
    spectral_measure_pvm_hilbert_projection_index_continuous_linear_map_compatibility_target_ready,
    spectral_measure_pvm_hilbert_projection_self_adjoint_spectral_projection_upgrade_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 Hilbert projection continuous-linear-map realization. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapCoreReady ∧
  SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapBoundaryHeld ∧
  SpectralMeasurePVMHilbertProjectionSelfAdjointSpectralProjectionUpgradeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 Hilbert projection continuous-linear-map boundary is held. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_continuous_linear_map_boundary_held :
    SpectralMeasurePVMOperatorValuedHilbertProjectionContinuousLinearMapBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_continuous_linear_map_core_ready,
    spectral_measure_pvm_operator_valued_hilbert_projection_linear_map_boundary_held,
    spectral_measure_pvm_hilbert_projection_self_adjoint_spectral_projection_upgrade_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
