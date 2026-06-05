import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierBooleanRealizationBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Explicit countable union on the finite `Set` carrier. -/
def spectralMeasurePVMFiniteSetCarrierCountableUnion
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier) : SpectralMeasurePVMFiniteSetCarrier :=
  {x | ∃ n : Nat, x ∈ F n}

/-- All-empty families of finite set-carriers. -/
def SpectralMeasurePVMFiniteSetCarrierAllEmptyFamily
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier) : Prop :=
  ∀ n : Nat, F n = spectralMeasurePVMFiniteSetCarrierEmpty

/-- A pinned single-whole family of finite set-carriers. -/
def SpectralMeasurePVMFiniteSetCarrierSingleWholeAt
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier) (k : Nat) : Prop :=
  F k = spectralMeasurePVMFiniteSetCarrierWhole ∧
    ∀ n : Nat, n ≠ k → F n = spectralMeasurePVMFiniteSetCarrierEmpty

/-- The countable union of an all-empty family is empty. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_all_empty
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier)
    (hF : SpectralMeasurePVMFiniteSetCarrierAllEmptyFamily F) :
    spectralMeasurePVMFiniteSetCarrierCountableUnion F =
      spectralMeasurePVMFiniteSetCarrierEmpty := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨n, hxmem⟩
    rw [hF n] at hxmem
    exact hxmem
  · intro hx
    exact False.elim hx

/-- The countable union of a pinned single-whole family is whole. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_single_whole_at
    (F : Nat → SpectralMeasurePVMFiniteSetCarrier)
    (k : Nat)
    (hF : SpectralMeasurePVMFiniteSetCarrierSingleWholeAt F k) :
    spectralMeasurePVMFiniteSetCarrierCountableUnion F =
      spectralMeasurePVMFiniteSetCarrierWhole := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨k, by
      rw [hF.1]
      trivial⟩

/-- Countable union target on the finite `Set` carrier. -/
def SpectralMeasurePVMFiniteSetCarrierCountableUnionTarget : Prop :=
  (∀ F : Nat → SpectralMeasurePVMFiniteSetCarrier,
    SpectralMeasurePVMFiniteSetCarrierAllEmptyFamily F →
      spectralMeasurePVMFiniteSetCarrierCountableUnion F =
        spectralMeasurePVMFiniteSetCarrierEmpty) ∧
  (∀ F : Nat → SpectralMeasurePVMFiniteSetCarrier,
    ∀ k : Nat,
      SpectralMeasurePVMFiniteSetCarrierSingleWholeAt F k →
        spectralMeasurePVMFiniteSetCarrierCountableUnion F =
          spectralMeasurePVMFiniteSetCarrierWhole)

/-- The finite `Set` carrier countable-union target is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_target_ready :
    SpectralMeasurePVMFiniteSetCarrierCountableUnionTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_countable_union_all_empty,
    spectral_measure_pvm_finite_set_carrier_countable_union_single_whole_at⟩

/-- The finite `Set` carrier now hosts endpoint, Boolean, and the two local
countable-union branches.  This still does not close the genuine Borel
sigma-algebra or genuine operator-topology countable additivity. -/
def SpectralMeasurePVMFiniteSetCarrierCountableUnionBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierBooleanRealizationBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierCountableUnionTarget ∧
  SpectralMeasurePVMGenuineSigmaBooleanClosureStillOpen ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set` carrier countable-union bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_countable_union_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierCountableUnionBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_boolean_realization_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_countable_union_target_ready,
    spectral_measure_pvm_genuine_sigma_boolean_closure_still_open_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
