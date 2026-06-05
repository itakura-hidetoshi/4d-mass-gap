import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableSetBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- All-empty families of supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet) : Prop :=
  ∀ n : Nat, E n = SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- A pinned single-whole family of supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet) (k : Nat) : Prop :=
  E k = SpectralMeasurePVMFiniteSupportedMeasurableSet.whole ∧
    ∀ n : Nat, n ≠ k → E n = SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Countable union for the all-empty supported measurable-set branch. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty
    (_E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    SpectralMeasurePVMFiniteSupportedMeasurableSet :=
  SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Countable union for the pinned single-whole supported measurable-set branch. -/
def spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole
    (_E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet) (_k : Nat) :
    SpectralMeasurePVMFiniteSupportedMeasurableSet :=
  SpectralMeasurePVMFiniteSupportedMeasurableSet.whole

/-- The all-empty supported branch has empty supported countable union. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_eq_empty
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (_hE : SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E) :
    spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E =
      SpectralMeasurePVMFiniteSupportedMeasurableSet.empty := by
  rfl

/-- The pinned single-whole supported branch has whole supported countable union. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_eq_whole
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (k : Nat)
    (_hE : SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k) :
    spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k =
      SpectralMeasurePVMFiniteSupportedMeasurableSet.whole := by
  rfl

/-- Operator value of the all-empty supported countable-union branch is zero. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_operator_zero
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_eq_empty E hE]
  rfl

/-- Operator value of the pinned single-whole supported countable-union branch is identity. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_operator_identity
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (k : Nat)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k) =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_eq_whole E k hE]
  rfl

/-- Measurability of the all-empty supported countable-union branch. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_measurable
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E)) := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_eq_empty E hE]
  exact spectral_measure_pvm_finite_supported_measurable_set_measurable
    SpectralMeasurePVMFiniteSupportedMeasurableSet.empty

/-- Measurability of the pinned single-whole supported countable-union branch. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_measurable
    (E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet)
    (k : Nat)
    (hE : SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k) :
    @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
      spectralMeasurePVMFiniteSetCarrierMeasurableSpace
      (spectralMeasurePVMFiniteSupportedMeasurableSetToSet
        (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k)) := by
  rw [spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_eq_whole E k hE]
  exact spectral_measure_pvm_finite_supported_measurable_set_measurable
    SpectralMeasurePVMFiniteSupportedMeasurableSet.whole

/-- Supported measurable-set countable branch target. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget : Prop :=
  (∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E →
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    ∀ k : Nat,
      SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k →
        spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
            (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k) =
          SpectralMeasurePVMConcreteBoundedOperator.identity) ∧
  (∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    ∀ hE : SpectralMeasurePVMFiniteSupportedMeasurableSetAllEmptyFamily E,
      @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
        spectralMeasurePVMFiniteSetCarrierMeasurableSpace
        (spectralMeasurePVMFiniteSupportedMeasurableSetToSet
          (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionAllEmpty E))) ∧
  (∀ E : Nat → SpectralMeasurePVMFiniteSupportedMeasurableSet,
    ∀ k : Nat,
      ∀ hE : SpectralMeasurePVMFiniteSupportedMeasurableSetSingleWholeAt E k,
        @MeasurableSet SpectralMeasurePVMFiniteSetCarrierPoint
          spectralMeasurePVMFiniteSetCarrierMeasurableSpace
          (spectralMeasurePVMFiniteSupportedMeasurableSetToSet
            (spectralMeasurePVMFiniteSupportedMeasurableSetCountableUnionSingleWhole E k)))

/-- The supported measurable-set countable branch target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_branch_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_operator_zero,
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_operator_identity,
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_all_empty_measurable,
    spectral_measure_pvm_finite_supported_measurable_set_countable_union_single_whole_measurable⟩

/-- Bridge extending the finite supported measurable-set local PVM surface with
its two countable branches. -/
def SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableSetBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchTarget ∧
  SpectralMeasurePVMFiniteMeasurableLocalPVMBundleReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite supported measurable-set countable branch bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_set_countable_branch_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableSetCountableBranchBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_set_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_set_countable_branch_target_ready,
    spectral_measure_pvm_finite_measurable_local_pvm_bundle_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
