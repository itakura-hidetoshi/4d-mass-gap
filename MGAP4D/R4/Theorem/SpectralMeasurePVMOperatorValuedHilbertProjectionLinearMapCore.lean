import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Linear-map realization of the two Hilbert projection slots on the concrete
mathlib Hilbert carrier.

This upgrades the previous carrier-level zero/id actions to bundled `LinearMap`s.
It still does not claim boundedness, continuity, orthogonal projection structure,
or self-adjointness as a bounded operator. -/
def spectralMeasurePVMHilbertProjectionSlotLinearMap :
    SpectralMeasurePVMHilbertProjectionSlot →
      MathlibAnalytic.ConcreteL2R1HilbertCarrier →ₗ[ℝ]
        MathlibAnalytic.ConcreteL2R1HilbertCarrier
  | SpectralMeasurePVMHilbertProjectionSlot.zeroProjection =>
      { toFun := fun _ => 0
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro c x
          simp }
  | SpectralMeasurePVMHilbertProjectionSlot.identityProjection =>
      { toFun := fun x => x
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro c x
          rfl }

/-- The zero projection slot linear map evaluates to zero. -/
theorem spectral_measure_pvm_hilbert_projection_slot_linear_map_zero_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0 := by
  rfl

/-- The identity projection slot linear map evaluates to the input. -/
theorem spectral_measure_pvm_hilbert_projection_slot_linear_map_identity_apply
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x := by
  rfl

/-- The linear-map realization agrees with the earlier carrier-level realization. -/
theorem spectral_measure_pvm_hilbert_projection_slot_linear_map_agrees_with_carrier_realizer
    (slot : SpectralMeasurePVMHilbertProjectionSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap slot x =
      spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x := by
  cases slot <;> rfl

/-- Pointwise idempotence of the two linear-map projection-slot realizers. -/
theorem spectral_measure_pvm_hilbert_projection_slot_linear_map_pointwise_idempotent
    (slot : SpectralMeasurePVMHilbertProjectionSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap slot
        (spectralMeasurePVMHilbertProjectionSlotLinearMap slot x) =
      spectralMeasurePVMHilbertProjectionSlotLinearMap slot x := by
  cases slot <;> rfl

/-- Empty index selects the zero linear-map action. -/
theorem spectral_measure_pvm_hilbert_projection_index_linear_map_empty
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0 := by
  rfl

/-- Whole index selects the identity linear-map action. -/
theorem spectral_measure_pvm_hilbert_projection_index_linear_map_whole
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x := by
  rfl

/-- Linear-map realization target for the two Hilbert projection slots. -/
def SpectralMeasurePVMHilbertProjectionLinearMapTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection x = x) ∧
  (∀ slot : SpectralMeasurePVMHilbertProjectionSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotLinearMap slot x =
        spectralMeasurePVMHilbertProjectionSlotCarrierRealizer slot x) ∧
  (∀ slot : SpectralMeasurePVMHilbertProjectionSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotLinearMap slot
          (spectralMeasurePVMHilbertProjectionSlotLinearMap slot x) =
        spectralMeasurePVMHilbertProjectionSlotLinearMap slot x)

/-- Index compatibility for the linear-map realization. -/
def SpectralMeasurePVMHilbertProjectionIndexLinearMapCompatibilityTarget : Prop :=
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.empty) x = 0) ∧
  (∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMHilbertProjectionSlotLinearMap
        (spectralMeasurePVMHilbertProjectionSlotFromIndex SpectralMeasurePVMConcreteIndex.whole) x = x)

/-- Continuous/bounded/self-adjoint upgrade is still open after the linear-map
realization. -/
def SpectralMeasurePVMHilbertProjectionContinuousBoundedSelfAdjointUpgradeStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Linear-map Hilbert projection core for R4. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationCoreReady ∧
  SpectralMeasurePVMHilbertProjectionLinearMapTarget ∧
  SpectralMeasurePVMHilbertProjectionIndexLinearMapCompatibilityTarget ∧
  SpectralMeasurePVMHilbertProjectionContinuousBoundedSelfAdjointUpgradeStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The linear-map realization target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_linear_map_target_ready :
    SpectralMeasurePVMHilbertProjectionLinearMapTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_slot_linear_map_zero_apply,
    spectral_measure_pvm_hilbert_projection_slot_linear_map_identity_apply,
    spectral_measure_pvm_hilbert_projection_slot_linear_map_agrees_with_carrier_realizer,
    spectral_measure_pvm_hilbert_projection_slot_linear_map_pointwise_idempotent⟩

/-- The index-linear-map compatibility target is ready. -/
theorem spectral_measure_pvm_hilbert_projection_index_linear_map_compatibility_target_ready :
    SpectralMeasurePVMHilbertProjectionIndexLinearMapCompatibilityTarget := by
  exact ⟨
    spectral_measure_pvm_hilbert_projection_index_linear_map_empty,
    spectral_measure_pvm_hilbert_projection_index_linear_map_whole⟩

/-- The continuous/bounded/self-adjoint upgrade remains explicitly open. -/
theorem spectral_measure_pvm_hilbert_projection_continuous_bounded_self_adjoint_upgrade_still_open_ready :
    SpectralMeasurePVMHilbertProjectionContinuousBoundedSelfAdjointUpgradeStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The R4 Hilbert projection linear-map core is ready. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_linear_map_core_ready :
    SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_realization_core_ready,
    spectral_measure_pvm_hilbert_projection_linear_map_target_ready,
    spectral_measure_pvm_hilbert_projection_index_linear_map_compatibility_target_ready,
    spectral_measure_pvm_hilbert_projection_continuous_bounded_self_adjoint_upgrade_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 Hilbert projection linear-map realization. -/
def SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapCoreReady ∧
  SpectralMeasurePVMOperatorValuedHilbertProjectionRealizationBoundaryHeld ∧
  SpectralMeasurePVMHilbertProjectionContinuousBoundedSelfAdjointUpgradeStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 Hilbert projection linear-map boundary is held. -/
theorem spectral_measure_pvm_operator_valued_hilbert_projection_linear_map_boundary_held :
    SpectralMeasurePVMOperatorValuedHilbertProjectionLinearMapBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_hilbert_projection_linear_map_core_ready,
    spectral_measure_pvm_operator_valued_hilbert_projection_realization_boundary_held,
    spectral_measure_pvm_hilbert_projection_continuous_bounded_self_adjoint_upgrade_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
