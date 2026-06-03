import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteNormalizationCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Minimal multiplication/composition table for the two distinguished concrete
bounded-operator targets used by the first R4 PVM discharge. -/
def spectralMeasurePVMConcreteOperatorMul :
    SpectralMeasurePVMConcreteBoundedOperator →
      SpectralMeasurePVMConcreteBoundedOperator →
        SpectralMeasurePVMConcreteBoundedOperator
  | SpectralMeasurePVMConcreteBoundedOperator.zero, _ =>
      SpectralMeasurePVMConcreteBoundedOperator.zero
  | SpectralMeasurePVMConcreteBoundedOperator.identity, a => a

/-- Minimal star table for the two distinguished concrete bounded-operator
targets.  Both zero and identity are fixed. -/
def spectralMeasurePVMConcreteOperatorStar :
    SpectralMeasurePVMConcreteBoundedOperator →
      SpectralMeasurePVMConcreteBoundedOperator
  | SpectralMeasurePVMConcreteBoundedOperator.zero =>
      SpectralMeasurePVMConcreteBoundedOperator.zero
  | SpectralMeasurePVMConcreteBoundedOperator.identity =>
      SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Idempotence predicate for the minimal concrete bounded-operator surface. -/
def SpectralMeasurePVMConcreteOperatorIdempotent
    (a : SpectralMeasurePVMConcreteBoundedOperator) : Prop :=
  spectralMeasurePVMConcreteOperatorMul a a = a

/-- Self-fixed predicate for the minimal concrete bounded-operator surface. -/
def SpectralMeasurePVMConcreteOperatorSelfFixed
    (a : SpectralMeasurePVMConcreteBoundedOperator) : Prop :=
  spectralMeasurePVMConcreteOperatorStar a = a

/-- The zero target is idempotent. -/
theorem spectral_measure_pvm_concrete_zero_idempotent :
    SpectralMeasurePVMConcreteOperatorIdempotent
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- The identity target is idempotent. -/
theorem spectral_measure_pvm_concrete_identity_idempotent :
    SpectralMeasurePVMConcreteOperatorIdempotent
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- The zero target is self-fixed. -/
theorem spectral_measure_pvm_concrete_zero_self_fixed :
    SpectralMeasurePVMConcreteOperatorSelfFixed
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  rfl

/-- The identity target is self-fixed. -/
theorem spectral_measure_pvm_concrete_identity_self_fixed :
    SpectralMeasurePVMConcreteOperatorSelfFixed
      SpectralMeasurePVMConcreteBoundedOperator.identity := by
  rfl

/-- Every indexed value of the minimal concrete normalization candidate is
idempotent. -/
theorem spectral_measure_pvm_concrete_candidate_idempotent
    (i : SpectralMeasurePVMConcreteIndex) :
    SpectralMeasurePVMConcreteOperatorIdempotent
      (spectralMeasurePVMConcreteNormalizationCandidate i) := by
  cases i <;> rfl

/-- Every indexed value of the minimal concrete normalization candidate is
self-fixed. -/
theorem spectral_measure_pvm_concrete_candidate_self_fixed
    (i : SpectralMeasurePVMConcreteIndex) :
    SpectralMeasurePVMConcreteOperatorSelfFixed
      (spectralMeasurePVMConcreteNormalizationCandidate i) := by
  cases i <;> rfl

/-- First concrete projection-valuedness discharge for the minimal concrete
candidate: every currently available indexed value is idempotent and self-fixed. -/
def SpectralMeasurePVMOperatorValuedConcreteProjectionCoreReady : Prop :=
  (∀ i : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteOperatorIdempotent
      (spectralMeasurePVMConcreteNormalizationCandidate i)) ∧
  (∀ i : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteOperatorSelfFixed
      (spectralMeasurePVMConcreteNormalizationCandidate i)) ∧
  SpectralMeasurePVMOperatorValuedConcreteNormalizationCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete projection-valuedness core is ready. -/
theorem spectral_measure_pvm_operator_valued_concrete_projection_core_ready :
    SpectralMeasurePVMOperatorValuedConcreteProjectionCoreReady := by
  exact ⟨
    spectral_measure_pvm_concrete_candidate_idempotent,
    spectral_measure_pvm_concrete_candidate_self_fixed,
    spectral_measure_pvm_operator_valued_concrete_normalization_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D