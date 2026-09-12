import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathCenteredVariationGeometricTail
import Mathlib.Tactic

/-!
# Support-aggregated geometric decay for actual finite heat-bath centered variation

The preceding same-root layer gives the explicit geometric estimate for the
actual finite heat-bath centered variation at every source in a separated
support `T`.  This file sums that estimate over `T`.

If the initial centered variation vanishes outside the left support `S`, then
after a `Nodup` heat-bath schedule of length `D + M`, the total updated
variation over `T` is bounded by

`|T| * ((18 * q(beta))^D / (1 - 18 * q(beta))) *
  ∑ initial ∈ S, variation_before(initial)`.

The only new factor is the finite output-support cardinality.  This remains an
actual finite heat-bath/Feller variation statement, not a covariance theorem.
Heat-bath update count is not Euclidean time.  No continuum clustering,
positive physical mass, OS Hamiltonian gap, or uniform factorial-continuum
Dobrushin threshold is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathCenteredVariationSupportGeometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Summing the actual finite heat-bath centered variation over a separated
output support costs only the cardinality of that output support. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_support_finiteHeatBathCenteredVariationProfile_variation_le_geometric_of_supportsSeparatedBy
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
    let C :=
      periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
    let data :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    ∀ (O : BoundedContinuousFunction C.base.Configuration ℝ)
      (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O),
      (∀ initial : PeriodicHypercubicEvenEdge H,
        initial ∉ S → P.variation initial = 0) →
      (∑ source ∈ T,
        (P.finiteHeatBathCenteredVariationProfile data schedule).variation source) ≤
        (T.card : ℝ) *
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
              ∑ initial ∈ S, P.variation initial := by
  dsimp only
  intro O P hSupport
  calc
    (∑ source ∈ T,
        (P.finiteHeatBathCenteredVariationProfile
          (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
            (PeriodicHypercubicEvenSideLength H) N
            (by
              simp [PeriodicHypercubicEvenSideLength]
              omega)
            hN beta hBeta hThreshold)
          schedule).variation source) ≤
      ∑ _source ∈ T,
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
            ∑ initial ∈ S, P.variation initial := by
              apply Finset.sum_le_sum
              intro source hsource
              exact
                periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathCenteredVariationProfile_variation_le_geometric_of_supportsSeparatedBy
                  H N D M hH hN beta hBeta hThreshold S T hsep
                  schedule hNodup hLength source hsource O P hSupport
    _ = (T.card : ℝ) *
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
            ∑ initial ∈ S, P.variation initial := by
      simp [mul_assoc]

end

end MathlibAnalytic
end MGAP4D
