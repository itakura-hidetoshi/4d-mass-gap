import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathCenteredVariationGeometricTail
import Mathlib.Tactic

/-!
# Geometric one-link variation for the actual finite heat-bath observable

The current same-root route has reached the actual finite heat-bath centered
variation profile.  This file returns that profile estimate to the bounded
continuous observable it carries.

For two configurations agreeing away from one source link in a separated
support `T`, the defining `variation_bound` field of the updated centered
profile bounds the difference of the actual finite heat-bath Feller observable.
Composing that field directly with the periodic geometric estimate gives

`|P_schedule O(A) - P_schedule O(B)| ≤
  ((18 * q(beta))^D / (1 - 18 * q(beta))) *
    ∑ initial ∈ S, variation_before(initial)`.

No additional path multiplicity or support-cardinality factor is introduced.
This remains finite-volume heat-bath/Dobrushin/Feller variation.  Heat-bath
update count is not Euclidean time.  No covariance decay, continuum clustering,
positive physical mass, OS Hamiltonian gap, or uniform factorial-continuum
Dobrushin threshold is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathObservableGeometricVariation
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual finite heat-bath bounded-continuous observable inherits the
explicit geometric one-link variation bound between separated periodic compact
`SU(N)` supports. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathContinuousBCF_difference_abs_le_geometric_of_supportsSeparatedBy
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
    (hLength : schedule.length = D + M)
    (source : PeriodicHypercubicEvenEdge H)
    (hsource : source ∈ T) :
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
      ∀ (A B : C.base.Configuration),
        C.base.AgreeOffLink A B source →
        |C.finiteSingleLinkHeatBathContinuousBCF schedule O A -
          C.finiteSingleLinkHeatBathContinuousBCF schedule O B| ≤
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
              ∑ initial ∈ S, P.variation initial := by
  dsimp only
  intro O P hSupport A B hAgree
  have hVariation :=
    (P.finiteHeatBathCenteredVariationProfile
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold)
      schedule).variation_bound source A B hAgree
  exact
    hVariation.trans
      (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathCenteredVariationProfile_variation_le_geometric_of_supportsSeparatedBy
        H N D M hH hN beta hBeta hThreshold S T hsep
        schedule hNodup hLength source hsource O P hSupport)

end

end MathlibAnalytic
end MGAP4D
