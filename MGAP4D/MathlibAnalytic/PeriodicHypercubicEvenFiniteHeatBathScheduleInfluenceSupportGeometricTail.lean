import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathScheduleInfluenceGeometricTail
import Mathlib.Tactic

/-!
# Support-aggregated geometric tails for finite heat-bath schedules

The preceding same-root layer gives an explicit pointwise geometric bound for
the exact finite heat-bath schedule influence kernel between genuinely
plaquette-local separated periodic compact `SU(N)` supports.  This file sums
that pointwise estimate over both finite supports.

The only new factor is the product of support cardinalities.  In particular,
for a `Nodup` schedule of length `D + M`, the exact schedule kernel summed over
`S × T` is bounded by

`|S| * |T| * (18 * q(beta))^D / (1 - 18 * q(beta))`.

This remains finite heat-bath/Dobrushin algebra.  No covariance decay,
continuum clustering, positive physical mass, OS Hamiltonian gap, or uniform
factorial-continuum Dobrushin threshold is asserted.  Heat-bath update count is
not identified with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathScheduleSupportGeometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Summing the exact finite heat-bath schedule influence kernel over two actual
separated periodic compact `SU(N)` supports costs only the support-cardinality
prefactor. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_support_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_supportsSeparatedBy
    (H N D M : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (schedule : List (PeriodicHypercubicEvenEdge H))
    (hNodup : schedule.Nodup)
    (hLength : schedule.length = D + M) :
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    (∑ target ∈ S, ∑ source ∈ T,
      finiteHeatBathScheduleInfluenceKernel
        data.influence schedule target source) ≤
      (S.card : ℝ) * (T.card : ℝ) *
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
  classical
  dsimp only
  calc
    (∑ target ∈ S, ∑ source ∈ T,
        finiteHeatBathScheduleInfluenceKernel
          (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
            (PeriodicHypercubicEvenSideLength H) N
            (by
              simp [PeriodicHypercubicEvenSideLength]
              omega)
            hN beta hBeta hThreshold).influence
          schedule target source) ≤
      ∑ target ∈ S, ∑ source ∈ T,
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
            apply Finset.sum_le_sum
            intro target htarget
            apply Finset.sum_le_sum
            intro source hsource
            exact
              periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_supportsSeparatedBy
                H N D M hH hN beta hBeta hThreshold S T hsep
                schedule hNodup hLength target htarget source hsource
    _ = (S.card : ℝ) * (T.card : ℝ) *
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) := by
      simp [mul_assoc]

end

end MathlibAnalytic
end MGAP4D
