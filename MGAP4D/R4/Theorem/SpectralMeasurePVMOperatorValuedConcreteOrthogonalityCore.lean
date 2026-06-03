import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedConcreteProjectionCore

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Minimal disjointness relation on the two distinguished concrete spectral
indices.  Only the pair `(whole, whole)` is non-disjoint. -/
def SpectralMeasurePVMConcreteIndexDisjoint :
    SpectralMeasurePVMConcreteIndex → SpectralMeasurePVMConcreteIndex → Prop
  | SpectralMeasurePVMConcreteIndex.whole, SpectralMeasurePVMConcreteIndex.whole => False
  | _, _ => True

/-- Forward orthogonality law for the minimal concrete candidate: disjoint
indices yield zero product. -/
theorem spectral_measure_pvm_concrete_disjoint_product_zero
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMConcreteNormalizationCandidate i)
        (spectralMeasurePVMConcreteNormalizationCandidate j) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases i <;> cases j <;> try rfl
  exact False.elim hij

/-- Reversed orthogonality law for the minimal concrete candidate: disjoint
indices yield zero product in the reversed order. -/
theorem spectral_measure_pvm_concrete_disjoint_reversed_product_zero
    (i j : SpectralMeasurePVMConcreteIndex)
    (hij : SpectralMeasurePVMConcreteIndexDisjoint i j) :
    spectralMeasurePVMConcreteOperatorMul
        (spectralMeasurePVMConcreteNormalizationCandidate j)
        (spectralMeasurePVMConcreteNormalizationCandidate i) =
      SpectralMeasurePVMConcreteBoundedOperator.zero := by
  cases i <;> cases j <;> try rfl
  exact False.elim hij

/-- Minimal range orthogonality target for the concrete two-index surface.
At this stage it is encoded as the two product-zero laws, postponing genuine
Hilbert-range orthogonality until the bounded-operator carrier is replaced by a
mathlib operator. -/
def SpectralMeasurePVMConcreteRangeOrthogonalityTarget : Prop :=
  ∀ i j : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteIndexDisjoint i j →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMConcreteNormalizationCandidate i)
          (spectralMeasurePVMConcreteNormalizationCandidate j) =
        SpectralMeasurePVMConcreteBoundedOperator.zero

/-- Minimal pairwise family orthogonality target for the concrete two-index
surface. -/
def SpectralMeasurePVMConcretePairwiseFamilyOrthogonalityTarget : Prop :=
  ∀ i j : SpectralMeasurePVMConcreteIndex,
    SpectralMeasurePVMConcreteIndexDisjoint i j →
      spectralMeasurePVMConcreteOperatorMul
          (spectralMeasurePVMConcreteNormalizationCandidate j)
          (spectralMeasurePVMConcreteNormalizationCandidate i) =
        SpectralMeasurePVMConcreteBoundedOperator.zero

/-- Concrete orthogonality core: both product-zero directions are proved for all
currently available disjoint concrete indices. -/
def SpectralMeasurePVMOperatorValuedConcreteOrthogonalityCoreReady : Prop :=
  SpectralMeasurePVMConcreteRangeOrthogonalityTarget ∧
  SpectralMeasurePVMConcretePairwiseFamilyOrthogonalityTarget ∧
  SpectralMeasurePVMOperatorValuedConcreteProjectionCoreReady ∧
  SpectralMeasurePVMFullAxiomsStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete orthogonality core is ready. -/
theorem spectral_measure_pvm_operator_valued_concrete_orthogonality_core_ready :
    SpectralMeasurePVMOperatorValuedConcreteOrthogonalityCoreReady := by
  exact ⟨
    spectral_measure_pvm_concrete_disjoint_product_zero,
    spectral_measure_pvm_concrete_disjoint_reversed_product_zero,
    spectral_measure_pvm_operator_valued_concrete_projection_core_ready,
    spectral_measure_pvm_full_axioms_still_open,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D