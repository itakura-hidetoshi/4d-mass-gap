import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteOrthogonalityCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Minimal union operation on the two distinguished concrete spectral indices. -/
def SpectralMeasurePVMConcreteIndexUnion :
    SpectralMeasurePVMConcreteIndex → SpectralMeasurePVMConcreteIndex →
      SpectralMeasurePVMConcreteIndex
  | SpectralMeasurePVMConcreteIndex.empty, a => a
  | SpectralMeasurePVMConcreteIndex.whole, _ => SpectralMeasurePVMConcreteIndex.whole

/-- Minimal addition table for the two distinguished concrete bounded-operator
targets.  The `identity + identity` branch is defined only to totalize the table;
it is never used by the disjoint finite-additivity law because `(whole, whole)`
is not disjoint. -/
def spectralMeasurePVMConcreteOperatorAdd :
    SpectralMeasurePVMConcreteBoundedOperator →
      SpectralMeasurePVMConcreteBoundedOperator →
        SpectralMeasurePVMConcreteBoundedOperator
  | SpectralMeasurePVMConcreteBoundedOperator.zero, a => a
  | SpectralMeasurePVMConcreteBoundedOperator.identity,
      SpectralMeasurePVMConcreteBoundedOperator.zero =>
      SpectralMeasurePVMConcreteBoundedOperator.identity
  | SpectralMeasurePVMConcreteBoundedOperator.identity,
      SpectralMeasurePVMConcreteBoundedOperator.identity =>
      SpectralMeasurePVMConcreteBoundedOperator.identity

/-- Binary finite additivity for the minimal concrete candidate over disjoint
concrete indices. -/
theorem spectral_measure_pvm_concrete_binary_finite_additivity
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j) :
    spectralMeasurePVMConcreteNormalizationCandidate
        (SpectralMeasurePVMConcreteIndexUnion i j) =
      spectralMeasurePVMConcreteOperatorAdd
        (spectralMeasurePVMConcreteNormalizationCandidate i)
        (spectralMeasurePVMConcreteNormalizationCandidate j) := by
  cases i <;> cases j <;> try rfl
  exact False.elim hij

/-- Concrete binary finite-additivity target. -/
def SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget : Prop :=
  ∀ i j : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteIndexDisjoint i j →
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteIndexUnion i j) =
        spectralMeasurePVMConcreteOperatorAdd
          (spectralMeasurePVMConcreteNormalizationCandidate i)
          (spectralMeasurePVMConcreteNormalizationCandidate j)

/-- Concrete finite-additivity target.  At the two-index stage, finite
additivity is represented by the binary disjoint law; later finite-family files
can replace this alias by a genuine `Finset` formulation. -/
def SpectralMeasurePVMConcreteFiniteAdditivityTarget : Prop :=
  SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget

/-- Concrete finite orthogonal projection-sum target. -/
def SpectralMeasurePVMConcreteFiniteOrthogonalProjectionSumTarget : Prop :=
  SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget

/-- Concrete finite-sum projection target. -/
def SpectralMeasurePVMConcreteFiniteSumProjectionTarget : Prop :=
  SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget

/-- Concrete finite partial-sum coherence target. -/
def SpectralMeasurePVMConcreteFinitePartialSumCoherenceTarget : Prop :=
  SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget

/-- Concrete finite-additivity core: all finite-additivity interfaces currently
exposed by the two-index concrete surface are discharged by the same binary
computational law. -/
def SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady : Prop :=
  SpectralMeasurePVMConcreteBinaryFiniteAdditivityTarget ∧
  SpectralMeasurePVMConcreteFiniteAdditivityTarget ∧
  SpectralMeasurePVMConcreteFiniteOrthogonalProjectionSumTarget ∧
  SpectralMeasurePVMConcreteFiniteSumProjectionTarget ∧
  SpectralMeasurePVMConcreteFinitePartialSumCoherenceTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteOrthogonalityCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete finite-additivity core is ready. -/
theorem spectral_measure_pvm_operator_valued_concrete_finite_additivity_core_ready :
    SpectralMeasurePVMOperatorValuedConcreteFiniteAdditivityCoreReady := by
  exact ⟨
    spectral_measure_pvm_concrete_binary_finite_additivity,
    spectral_measure_pvm_concrete_binary_finite_additivity,
    spectral_measure_pvm_concrete_binary_finite_additivity,
    spectral_measure_pvm_concrete_binary_finite_additivity,
    spectral_measure_pvm_concrete_binary_finite_additivity,
    spectral_measure_pvm_operator_valued_concrete_orthogonality_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D