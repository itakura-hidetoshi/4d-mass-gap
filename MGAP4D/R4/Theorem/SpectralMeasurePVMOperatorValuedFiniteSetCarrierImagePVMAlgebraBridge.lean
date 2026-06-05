import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSetCarrierEndpointOperatorBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Disjointness for finite `Set` carrier image slots, transported from the
concrete two-index disjointness relation. -/
def SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint
    (s t : SpectralMeasurePVMSpectralSetSlot) : Prop :=
  SpectralMeasurePVMConcreteIndexDisjoint
    (spectralMeasurePVMConcreteIndexFromSpectralSetSlot s)
    (spectralMeasurePVMConcreteIndexFromSpectralSetSlot t)

/-- The finite `Set` carrier image operator candidate is idempotent at every slot. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_idempotent
    (s : SpectralMeasurePVMSpectralSetSlot) :
    SpectralMeasurePVMConcreteOperatorIdempotent
      (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s) := by
  cases s <;> rfl

/-- The finite `Set` carrier image operator candidate is self-fixed at every slot. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_self_fixed
    (s : SpectralMeasurePVMSpectralSetSlot) :
    SpectralMeasurePVMConcreteOperatorSelfFixed
      (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s) := by
  cases s <;> rfl

/-- Disjoint finite `Set` carrier image slots have zero product. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_disjoint_product_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Disjoint finite `Set` carrier image slots have zero product in the reversed order. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_disjoint_reversed_product_zero
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t)
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Binary finite additivity for the finite `Set` carrier image operator candidate
on disjoint image slots. -/
theorem spectral_measure_pvm_finite_set_carrier_image_operator_binary_finite_additivity
    (s t : SpectralMeasurePVMSpectralSetSlot)
    (hst : SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t) :
    spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
        (spectralMeasurePVMSpectralSetSlotUnion s t) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)
        (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t) := by
  cases s <;> cases t <;> try rfl
  exact False.elim hst

/-- Projection-valuedness target for the finite `Set` carrier image operator candidate. -/
def SpectralMeasurePVMFiniteSetCarrierImageProjectionValuedTarget : Prop :=
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMConcreteOperatorIdempotent
      (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)) ∧
  (∀ s : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMConcreteOperatorSelfFixed
      (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s))

/-- Orthogonality target for the finite `Set` carrier image operator candidate. -/
def SpectralMeasurePVMFiniteSetCarrierImageOrthogonalityTarget : Prop :=
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t)
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero)

/-- Finite-additivity target for the finite `Set` carrier image operator candidate. -/
def SpectralMeasurePVMFiniteSetCarrierImageFiniteAdditivityTarget : Prop :=
  ∀ s t : SpectralMeasurePVMSpectralSetSlot,
    SpectralMeasurePVMFiniteSetCarrierImageSlotDisjoint s t →
      spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate
          (spectralMeasurePVMSpectralSetSlotUnion s t) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate s)
          (spectralMeasurePVMFiniteSetCarrierImageOperatorCandidate t)

/-- Projection-valuedness is ready for the finite `Set` carrier image operator candidate. -/
theorem spectral_measure_pvm_finite_set_carrier_image_projection_valued_target_ready :
    SpectralMeasurePVMFiniteSetCarrierImageProjectionValuedTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_image_operator_idempotent,
    spectral_measure_pvm_finite_set_carrier_image_operator_self_fixed⟩

/-- Orthogonality is ready for the finite `Set` carrier image operator candidate. -/
theorem spectral_measure_pvm_finite_set_carrier_image_orthogonality_target_ready :
    SpectralMeasurePVMFiniteSetCarrierImageOrthogonalityTarget := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_image_operator_disjoint_product_zero,
    spectral_measure_pvm_finite_set_carrier_image_operator_disjoint_reversed_product_zero⟩

/-- Finite additivity is ready for the finite `Set` carrier image operator candidate. -/
theorem spectral_measure_pvm_finite_set_carrier_image_finite_additivity_target_ready :
    SpectralMeasurePVMFiniteSetCarrierImageFiniteAdditivityTarget := by
  exact spectral_measure_pvm_finite_set_carrier_image_operator_binary_finite_additivity

/-- The finite `Set` carrier image operator candidate satisfies the local PVM
algebra laws on the slot image.  This is still not a genuine Borel PVM. -/
def SpectralMeasurePVMFiniteSetCarrierImagePVMAlgebraBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSetCarrierEndpointOperatorBridgeReady ∧
  SpectralMeasurePVMFiniteSetCarrierImageProjectionValuedTarget ∧
  SpectralMeasurePVMFiniteSetCarrierImageOrthogonalityTarget ∧
  SpectralMeasurePVMFiniteSetCarrierImageFiniteAdditivityTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The finite `Set` carrier image PVM algebra bridge is ready. -/
theorem spectral_measure_pvm_finite_set_carrier_image_pvm_algebra_bridge_ready :
    SpectralMeasurePVMFiniteSetCarrierImagePVMAlgebraBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_set_carrier_endpoint_operator_bridge_ready,
    spectral_measure_pvm_finite_set_carrier_image_projection_valued_target_ready,
    spectral_measure_pvm_finite_set_carrier_image_orthogonality_target_ready,
    spectral_measure_pvm_finite_set_carrier_image_finite_additivity_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
