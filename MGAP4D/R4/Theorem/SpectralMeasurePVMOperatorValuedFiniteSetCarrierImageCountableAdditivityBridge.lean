import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierImagePVMAlgebraBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Slot families whose finite `Set` carrier images are all empty. -/
def SpectralMeasurePVMFiniteSetCarrierImageAllEmptySlotFamily
    (s : Nat → SpectralMeasurePVMSpectralSetSlot) : Prop :=
  ∀ n : Nat, s n = SpectralMeasurePVMSpectralSetSlot.emptySet

/-- Slot families with a single pinned whole slot and all other slots empty. -/
def SpectralMeasurePVMFiniteSetCarrierImageSingleWholeSlotAt
    (s : Nat → SpectralMeasurePVMSpectralSetSlot) (k : Nat) : Prop :=
  s k = SpectralMeasurePVMSpectralSetSlot.wholeSet ∧
    ∀ n : Nat, n ≠ k → s n = SpectralMeasurePVMSpectralSetSlot.emptySet

/-- Countable union slot for the all-empty image branch. -/
def spectralMeasurePVMFiniteSetCarrierImageCountableUnionAllEmptySlot
    (_s : Nat → SpectralMeasurePVMSpectralSetSlot) : SpectralMeasurePVMSpectralSetSlot :=
  SpectralMeasurePVMSpectralSetSlot.emptySet

/-- Countable union slot for the pinned single-whole image branch. -/
def spectralMeasurePVMFiniteSetCarrierImageCountableUnionSingleWholeSlot
    (_s : Nat → SpectralMeasurePVMSpectralSetSlot) (_k : Nat) : SpectralMeasurePVMSpectralSetSlot :=
  SpectralMeasurePVMSpectralSetSlot.wholeSet

/-- In the all-empty branch, the image countable-union operator is zero. -/
theorem spectral_measure_pvm_finite_set_carrier_image_countable_union_all_empty_operator_zero
    (s : Nat → SpectralMeasurePVMSpectralSetSlot)
    (_hs : SpectralMeasurePVMFiniteSetCarrierImageAllEmptySlotFamily s) :
    spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
        (spectralMeasurePVMFiniteSetCarrierImageCountableUnionAllEmptySlot s) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- In the pinned single-whole branch, the image countable-union operator is identity. -/
theorem spectral_measure_pvm_finite_set_carrier_image_countable_union_single_whole_operator_identity
    (s : Nat → SpectralMeasurePVMSpectralSetSlot)
    (k : Nat)
    (_hs : SpectralMeasurePVMFiniteSetCarrierImageSingleWholeSlotAt s k) :
    spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
        (spectralMeasurePVMFiniteSetCarrierImageCountableUnionSingleWholeSlot s k) =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- Operator-valued countable branch target for the finite `Set` carrier image. -/
def SpectralMeasurePVMFiniteSetCarrierImageOperatorCountableBranchTarget : Prop :=
  (∀ s : Nat → SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMFiniteSetCarrierImageAllEmptySlotFamily s →
      spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
          (spectralMeasurePVMFiniteSetCarrierImageCountableUnionAllEmptySlot s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ s : Nat → SpectralMeasurePVMSpectralSetSlot,
    ∀ k : Nat,
      SpectralMeasurePVMFiniteSetCarrierImageSingleWholeSlotAt s k →
        spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
            (spectralMeasurePVMFiniteSetCarrierImageCountableUnionSingleWholeSlot s k) =
          SpectralMeasurePVMConcreteBoundedOperator.identity)

/-- The finite `Set` carrier image operator countable branch target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_countable_branch_target_ready :
    SpectralMeasurePVMFiniteSetCarrierImageOperatorCountableBranchTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_image_countable_union_all_empty_operator_zero,
    spectral_measure_pvm_finite_set_carrier_image_countable_union_single_whole_operator_identity⟩

/-- Bridge: the finite `Set` carrier image now has endpoint, finite PVM algebra,
and the two local countable operator-valued branches.  Genuine operator-topology
countable additivity is still open. -/
def SpectralMeasurePVMFiniteSetCarrierImageCountableAdditivityBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierImagePVMAlgebraBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierCountableUnionBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierImageOperatorCountableBranchTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set` carrier image countable-additivity bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_image_countable_additivity_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierImageCountableAdditivityBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_image_pvm_algebra_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_countable_union_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_image_operator_countable_branch_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
