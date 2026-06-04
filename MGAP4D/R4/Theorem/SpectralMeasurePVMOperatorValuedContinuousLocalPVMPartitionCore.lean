import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The union of a symbolic spectral-set slot and its complement projects as the
identity action, pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_union_complement_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotUnion s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x = x := by
  cases s <;> rfl

/-- The intersection of a symbolic spectral-set slot and its complement projects
as the zero action, pointwise. -/
theorem spectral_measure_pvm_spectral_set_slot_projection_inter_complement_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotInter s
          (spectralMeasurePVMSpectralSetSlotComplement s)) x = 0 := by
  cases s <;> rfl

/-- The two complementary local PVM components reconstruct the vector. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_decomposition_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x = x := by
  cases s <;> simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- Reprojection of the reconstructed vector onto the first component recovers
that first component. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_first_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x := by
  cases s <;> simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- Reprojection of the reconstructed vector onto the complement component
recovers that complement component. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_complement_reprojection_apply
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s) x := by
  cases s <;> simp [spectralMeasurePVMSpectralSetSlotContinuousProjection,
    spectralMeasurePVMSpectralSetSlotComplement]

/-- The first component is fixed by its own projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_first_component_fixed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection s
        (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x := by
  cases s <;> rfl

/-- The complement component is fixed by the complement projection. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_complement_component_fixed
    (s : SpectralMeasurePVMSpectralSetSlot)
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s)
        (spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x) =
      spectralMeasurePVMSpectralSetSlotContinuousProjection
        (spectralMeasurePVMSpectralSetSlotComplement s) x := by
  cases s <;> rfl

/-- Boolean partition laws for the symbolic spectral-set slots. -/
def SpectralMeasurePVMSpectralSetSlotPartitionBooleanTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotUnion s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x = x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotInter s
            (spectralMeasurePVMSpectralSetSlotComplement s)) x = 0)

/-- Vector decomposition laws for the R4 local PVM partition. -/
def SpectralMeasurePVMContinuousLocalPVMPartitionDecompositionTarget : Prop :=
  ∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
          spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x = x

/-- Reprojection laws for the R4 local PVM partition components. -/
def SpectralMeasurePVMContinuousLocalPVMPartitionReprojectionTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
            spectralMeasurePVMSpectralSetSlotContinuousProjection
              (spectralMeasurePVMSpectralSetSlotComplement s) x) =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMSpectralSetSlotContinuousProjection s x +
            spectralMeasurePVMSpectralSetSlotContinuousProjection
              (spectralMeasurePVMSpectralSetSlotComplement s) x) =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x)

/-- Component fixedness laws for the R4 local PVM partition. -/
def SpectralMeasurePVMContinuousLocalPVMPartitionComponentFixedTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection s
          (spectralMeasurePVMSpectralSetSlotContinuousProjection s x) =
        spectralMeasurePVMSpectralSetSlotContinuousProjection s x) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
      spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s)
          (spectralMeasurePVMSpectralSetSlotContinuousProjection
            (spectralMeasurePVMSpectralSetSlotComplement s) x) =
        spectralMeasurePVMSpectralSetSlotContinuousProjection
          (spectralMeasurePVMSpectralSetSlotComplement s) x)

/-- Genuine orthogonal direct-sum decomposition for the eventual Borel PVM remains
open.  This file only closes the two-slot partition decomposition. -/
def SpectralMeasurePVMGenuineOrthogonalPartitionDecompositionStillOpen : Prop :=
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The partition Boolean target is ready. -/
theorem spectral_measure_pvm_spectral_set_slot_partition_boolean_target_ready :
    SpectralMeasurePVMSpectralSetSlotPartitionBooleanTarget := by
  exact ⟨
    spectral_measure_pvm_spectral_set_slot_projection_union_complement_apply,
    spectral_measure_pvm_spectral_set_slot_projection_inter_complement_apply⟩

/-- The partition decomposition target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_decomposition_target_ready :
    SpectralMeasurePVMContinuousLocalPVMPartitionDecompositionTarget := by
  exact spectral_measure_pvm_continuous_local_pvm_partition_decomposition_apply

/-- The partition reprojection target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_reprojection_target_ready :
    SpectralMeasurePVMContinuousLocalPVMPartitionReprojectionTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_partition_first_reprojection_apply,
    spectral_measure_pvm_continuous_local_pvm_partition_complement_reprojection_apply⟩

/-- The partition component-fixed target is ready. -/
theorem spectral_measure_pvm_continuous_local_pvm_partition_component_fixed_target_ready :
    SpectralMeasurePVMContinuousLocalPVMPartitionComponentFixedTarget := by
  exact ⟨
    spectral_measure_pvm_continuous_local_pvm_partition_first_component_fixed,
    spectral_measure_pvm_continuous_local_pvm_partition_complement_component_fixed⟩

/-- Genuine orthogonal direct-sum decomposition remains explicitly open. -/
theorem spectral_measure_pvm_genuine_orthogonal_partition_decomposition_still_open_ready :
    SpectralMeasurePVMGenuineOrthogonalPartitionDecompositionStillOpen := by
  exact ⟨
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R4 continuous local PVM partition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionCoreReady : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraCoreReady ∧
  SpectralMeasurePVMSpectralSetSlotPartitionBooleanTarget ∧
  SpectralMeasurePVMContinuousLocalPVMPartitionDecompositionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMPartitionReprojectionTarget ∧
  SpectralMeasurePVMContinuousLocalPVMPartitionComponentFixedTarget ∧
  SpectralMeasurePVMGenuineOrthogonalPartitionDecompositionStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM partition core is ready. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_partition_core_ready :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionCoreReady := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_boolean_algebra_core_ready,
    spectral_measure_pvm_spectral_set_slot_partition_boolean_target_ready,
    spectral_measure_pvm_continuous_local_pvm_partition_decomposition_target_ready,
    spectral_measure_pvm_continuous_local_pvm_partition_reprojection_target_ready,
    spectral_measure_pvm_continuous_local_pvm_partition_component_fixed_target_ready,
    spectral_measure_pvm_genuine_orthogonal_partition_decomposition_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Boundary after the R4 continuous local PVM partition core. -/
def SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionBoundaryHeld : Prop :=
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionCoreReady ∧
  SpectralMeasurePVMOperatorValuedContinuousLocalPVMBooleanAlgebraBoundaryHeld ∧
  SpectralMeasurePVMGenuineOrthogonalPartitionDecompositionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R4 continuous local PVM partition boundary is held. -/
theorem spectral_measure_pvm_operator_valued_continuous_local_pvm_partition_boundary_held :
    SpectralMeasurePVMOperatorValuedContinuousLocalPVMPartitionBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_operator_valued_continuous_local_pvm_partition_core_ready,
    spectral_measure_pvm_operator_valued_continuous_local_pvm_boolean_algebra_boundary_held,
    spectral_measure_pvm_genuine_orthogonal_partition_decomposition_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
