import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Formal adjoint on the two projection slots.  On the current R4 local
empty/whole surface, the zero and identity projections are adjoint-fixed.  This
is a slot-level symmetry bridge, not yet the full mathlib adjoint theorem for a
genuine Borel PVM. -/
def spectralMeasurePVMHilbertProjectionSlotFormalAdjoint :
    SpectralMeasurePVMHilbertProjectionSlot → SpectralMeasurePVMHilbertProjectionSlot
  | SpectralMeasurePVMHilbertProjectionSlot.zeroProjection =>
      SpectralMeasurePVMHilbertProjectionSlot.zeroProjection
  | SpectralMeasurePVMHilbertProjectionSlot.identityProjection =>
      SpectralMeasurePVMHilbertProjectionSlot.identityProjection

/-- The zero projection slot is fixed by the formal adjoint. -/
theorem spectral_measure_pvm_hilbert_projection_slot_formal_adjoint_zero :
    spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
        SpectralMeasurePVMHilbertProjectionSlot.zeroProjection =
      SpectralMeasurePVMHilbertProjectionSlot.zeroProjection := by
  rfl

/-- The identity projection slot is fixed by the formal adjoint. -/
theorem spectral_measure_pvm_hilbert_projection_slot_formal_adjoint_identity :
    spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
        SpectralMeasurePVMHilbertProjectionSlot.identityProjection =
      SpectralMeasurePVMHilbertProjectionSlot.identityProjection := by
  rfl

/-- Every R4 projection slot is fixed by the formal adjoint. -/
theorem spectral_measure_pvm_hilbert_projection_slot_formal_adjoint_fixed
    (slot : SpectralMeasurePVMHilbertProjectionSlot) :
    spectralMeasurePVMHilbertProjectionSlotFormalAdjoint slot = slot := by
  cases slot <;> rfl

/-- Formal-adjoint fixedness descends to the concrete index slots. -/
theorem spectral_measure_pvm_index_projection_slot_formal_adjoint_fixed
    (i : SpectralMeasurePVMConcreteIndex) :
    spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
        (spectralMeasurePVMHilbertProjectionSlotFromIndex i) =
      spectralMeasurePVMHilbertProjectionSlotFromIndex i := by
  cases i <;> rfl

/-- The local continuous PVM projection is formally adjoint-fixed at the slot
level for every concrete index. -/
def SpectralMeasurePVMContinuousLocalPVMFormalSelfAdjointSlotTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
        (spectralMeasurePVMHilbertProjectionSlotFromIndex i) =
      spectralMeasurePVMHilbertProjectionSlotFromIndex i

/-- The local continuous PVM projection action is unchanged by replacing each
slot with its formal adjoint slot. -/
def SpectralMeasurePVMContinuousLocalPVMFormalAdjointActionTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
          (spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
            (spectralMeasurePVMHilbertProjectionSlotFromIndex i)) x =
        spectralMeasurePVMContinuousLocalPVM.projection i x

/-- The local continuous PVM projection action is pointwise idempotent after the
formal adjoint bridge. -/
def SpectralMeasurePVMContinuousLocalPVMFormalAdjointIdempotentActionTarget : Prop :=
  ∀ i : SpectralMeasurePVMConcreteIndex,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMHilbertProjectionSlotContinuousLinearMap
          (spectralMeasurePVMHilbertProjectionSlotFormalAdjoint
            (spectralMeasurePVMHilbertProjectionSlotFromIndex i))
          (spectralMeasurePVMContinuousLocalPVM.projection i x) =
        spectralMeasurePVMContinuousLocalPVM.projection i x

/-- Genuine mathlib adjoint/self-adjointness for the eventual Borel PVM remains
open.  This file only closes the zero/id slot symmetry of the R4 local surface. -/
def SpectralMeasurePVMGenuineAdjointSelfAdjointProjectionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The formal self-adjoint slot target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_formal_self_adjoint_slot_target_ready :
    SpectralMeasurePVMContinuousLocalPVMFormalSelfAdjointSlotTarget := by
  exact spectral_measure_pvm_index_projection_slot_formal_adjoint_fixed

/-- The formal adjoint action target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_formal_adjoint_action_target_ready :
    SpectralMeasurePVMContinuousLocalPVMFormalAdjointActionTarget := by
  intro i x
  cases i <;> rfl

/-- The formal adjoint idempotent action target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_formal_adjoint_idempotent_action_target_ready :
    SpectralMeasurePVMContinuousLocalPVMFormalAdjointIdempotentActionTarget := by
  intro i x
  cases i <;> rfl

/-- Genuine adjoint/self-adjoint projection remains explicitly open. -/
theorem spectral_measure_pvm_genuine_adjoint_self_adjoint_projection_still_open_ready :
    SpectralMeasurePVMGenuineAdjointSelfAdjointProjectionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM symmetry core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMCoreReady ∧
  SpectralMeasurePVMContinuousLocalPVMFormalSelfAdjointSlotTarget ∧
  SpectralMeasurePVMContinuousLocalPVMFormalAdjointActionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMFormalAdjointIdempotentActionTarget ∧
  SpectralMeasurePVMGenuineAdjointSelfAdjointProjectionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM symmetry core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_symmetry_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_core_ready,
    spectral_measure_pvm_continuous_local_pvm_formal_self_adjoint_slot_target_ready,
    spectral_measure_pvm_continuous_local_pvm_formal_adjoint_action_target_ready,
    spectral_measure_pvm_continuous_local_pvm_formal_adjoint_idempotent_action_target_ready,
    spectral_measure_pvm_genuine_adjoint_self_adjoint_projection_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM symmetry core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMBoundaryHeld ∧
  SpectralMeasurePVMGenuineAdjointSelfAdjointProjectionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM symmetry boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_symmetry_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMSymmetryBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_symmetry_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_boundary_held,
    spectral_measure_pvm_genuine_adjoint_self_adjoint_projection_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
