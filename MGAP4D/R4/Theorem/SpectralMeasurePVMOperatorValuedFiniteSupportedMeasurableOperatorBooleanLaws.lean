import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedFiniteSupportedMeasurableOperatorOrderCompatibility

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Complement gives zero product on the left. -/
theorem spectral_measure_pvm_finite_supported_measurable_complement_left_product_zero
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases E <;> rfl

/-- Complement gives zero product on the right. -/
theorem spectral_measure_pvm_finite_supported_measurable_complement_right_product_zero
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E))
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases E <;> rfl

/-- Complement intersection has zero operator value. -/
theorem spectral_measure_pvm_finite_supported_measurable_inter_complement_operator_zero
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases E <;> rfl

/-- Union with complement has identity operator value. -/
theorem spectral_measure_pvm_finite_supported_measurable_union_complement_operator_identity
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  cases E <;> rfl

/-- Operator value is invariant under double complement. -/
theorem spectral_measure_pvm_finite_supported_measurable_double_complement_operator
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> rfl

/-- Operator multiplication is commutative on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_mul_comm
    (E F : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) := by
  cases E <;> cases F <;> rfl

/-- Operator multiplication is idempotent on supported measurable sets. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_mul_idempotent
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> rfl

/-- Whole acts as a multiplicative identity on the left. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_whole_mul_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.whole)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> rfl

/-- Whole acts as a multiplicative identity on the right. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_whole_mul_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.whole) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E := by
  cases E <;> rfl

/-- Empty acts as a multiplicative zero on the left. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_empty_mul_left
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases E <;> rfl

/-- Empty acts as a multiplicative zero on the right. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_empty_mul_right
    (E : SpectralMeasurePVMFiniteSupportedMeasurableSet) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases E <;> rfl

/-- Operator Boolean law target for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawTarget : Prop :=
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E))
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetInter E
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetUnion E
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      SpectralMeasurePVMConcreteBoundedOperator.identity) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
        (spectralMeasurePVMFiniteSupportedMeasurableSetComplement
          (spectralMeasurePVMFiniteSupportedMeasurableSetComplement E)) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E F : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F) =
      spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate F)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.whole)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.whole) =
      spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E) =
      SpectralMeasurePVMConcreteBoundedOperator.zero) ∧
  (∀ E : SpectralMeasurePVMFiniteSupportedMeasurableSet,
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate E)
        (spectralMeasurePVMFiniteSupportedMeasurableSetOperatorCandidate
          SpectralMeasurePVMFiniteSupportedMeasurableSet.empty) =
      SpectralMeasurePVMConcreteBoundedOperator.zero)

/-- The supported measurable operator Boolean law target is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_boolean_law_target_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawTarget := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_complement_left_product_zero,
    spectral_measure_pvm_finite_supported_measurable_complement_right_product_zero,
    spectral_measure_pvm_finite_supported_measurable_inter_complement_operator_zero,
    spectral_measure_pvm_finite_supported_measurable_union_complement_operator_identity,
    spectral_measure_pvm_finite_supported_measurable_double_complement_operator,
    spectral_measure_pvm_finite_supported_measurable_operator_mul_comm,
    spectral_measure_pvm_finite_supported_measurable_operator_mul_idempotent,
    spectral_measure_pvm_finite_supported_measurable_operator_whole_mul_left,
    spectral_measure_pvm_finite_supported_measurable_operator_whole_mul_right,
    spectral_measure_pvm_finite_supported_measurable_operator_empty_mul_left,
    spectral_measure_pvm_finite_supported_measurable_operator_empty_mul_right⟩

/-- Bridge registering operator Boolean laws for supported measurable sets. -/
def SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawBridgeReady : Prop :=
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorOrderCompatibilityBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawTarget ∧
  SpectralMeasurePVMFiniteSupportedMeasurableBooleanAlgebraLawBridgeReady ∧
  SpectralMeasurePVMFiniteSupportedMeasurableLocalFullAxiomPublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineBorelCarrierRealizationStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The supported measurable operator Boolean law bridge is ready. -/
theorem spectral_measure_pvm_finite_supported_measurable_operator_boolean_law_bridge_ready :
    SpectralMeasurePVMFiniteSupportedMeasurableOperatorBooleanLawBridgeReady := by
  exact ⟨
    spectral_measure_pvm_finite_supported_measurable_operator_order_compatibility_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_operator_boolean_law_target_ready,
    spectral_measure_pvm_finite_supported_measurable_boolean_algebra_law_bridge_ready,
    spectral_measure_pvm_finite_supported_measurable_local_full_axiom_public_boundary_held,
    spectral_measure_pvm_genuine_borel_carrier_realization_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
