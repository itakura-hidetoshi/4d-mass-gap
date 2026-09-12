import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceGeometricTail
import Mathlib.Tactic

/-!
# Support-aggregated geometric tails for the current influence kernel

The current same-root route already gives an entrywise finite geometric tail
for the recursive Dobrushin influence kernel and, on actual separated periodic
supports, an exact zero prefix below the plaquette-local separation distance.

This file lifts the entrywise tail to finite support sets.  The generic compact
Dobrushin statement gains only the finite support-cardinality prefactor.  The
actual periodic compact `SU(N)` specialization then packages that support tail
together with the exact zero prefix supplied by the preceding same-root layer.

This remains finite influence-kernel algebra.  No covariance representation,
continuum clustering, positive physical mass, OS Hamiltonian gap, or
factorial-continuum Dobrushin condition is asserted.  Markov update time is not
identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Summing an entrywise strict-Dobrushin geometric tail over two finite support
sets costs only the product of their cardinalities. -/
theorem continuous_compact_oriented_dobrushin_influenceIterateKernel_support_tail_le_geometric
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (data : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hStrict : data.coefficient < 1)
    (D M : ℕ)
    (S T : Finset C.base.geometry.Edge) :
    (∑ target ∈ S, ∑ source ∈ T, ∑ k ∈ Finset.range M,
      finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
        (S.card : ℝ) * (T.card : ℝ) *
          (data.coefficient ^ D / (1 - data.coefficient)) := by
  calc
    (∑ target ∈ S, ∑ source ∈ T, ∑ k ∈ Finset.range M,
        finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
      ∑ target ∈ S, ∑ source ∈ T,
        data.coefficient ^ D / (1 - data.coefficient) := by
          apply Finset.sum_le_sum
          intro target htarget
          apply Finset.sum_le_sum
          intro source hsource
          exact
            continuous_compact_oriented_dobrushin_influenceIterateKernel_tail_le_geometric
              C data hStrict D M target source
    _ = (S.card : ℝ) * (T.card : ℝ) *
        (data.coefficient ^ D / (1 - data.coefficient)) := by
      simp [mul_assoc]

private instance periodicHypercubicEvenSideLength_neZero_supportGeometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- On actual separated periodic compact `SU(N)` midpoint supports, the complete
support-aggregated prefix below `D` is exactly zero, while every finite tail
starting at `D` is bounded by the support-cardinality prefactor times the full
geometric tail. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_support_prefix_zero_and_tail_le_geometric_of_supportsSeparatedBy
    (H N D M : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T) :
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    ((∑ target ∈ S, ∑ source ∈ T, ∑ d ∈ Finset.range D,
        finiteInfluenceIterateKernel data.influence d target source) = 0) ∧
      ((∑ target ∈ S, ∑ source ∈ T, ∑ k ∈ Finset.range M,
          finiteInfluenceIterateKernel data.influence (D + k) target source) ≤
        (S.card : ℝ) * (T.card : ℝ) *
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta))) := by
  dsimp only
  constructor
  · apply Finset.sum_eq_zero
    intro target htarget
    apply Finset.sum_eq_zero
    intro source hsource
    exact
      (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_prefix_zero_and_tail_le_geometric_of_supportsSeparatedBy
        H N D M hH hN beta hBeta hThreshold S T hsep
        target htarget source hsource).1
  · calc
      (∑ target ∈ S, ∑ source ∈ T, ∑ k ∈ Finset.range M,
          finiteInfluenceIterateKernel
            (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
              (PeriodicHypercubicEvenSideLength H) N
              (by
                simp [PeriodicHypercubicEvenSideLength]
                omega)
              hN beta hBeta hThreshold).influence
            (D + k) target source) ≤
        ∑ target ∈ S, ∑ source ∈ T,
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
              apply Finset.sum_le_sum
              intro target htarget
              apply Finset.sum_le_sum
              intro source hsource
              exact
                (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_prefix_zero_and_tail_le_geometric_of_supportsSeparatedBy
                  H N D M hH hN beta hBeta hThreshold S T hsep
                  target htarget source hsource).2
      _ = (S.card : ℝ) * (T.card : ℝ) *
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
        simp [mul_assoc]

end

end MathlibAnalytic
end MGAP4D
