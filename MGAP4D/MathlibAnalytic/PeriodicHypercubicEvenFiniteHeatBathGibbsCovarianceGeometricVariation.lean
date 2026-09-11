import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathGibbsPairingGeometricVariation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathCovarianceGeometricVariation
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathExpectationBCF_gibbsCovarianceReal_eq_and_difference_abs_le_geometric_of_supportsSeparatedBy
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
    ∀ (F O : BoundedContinuousFunction C.base.Configuration ℝ)
      (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O),
      (∀ target ∈ schedule,
        C.base.OffLinkFiberConstant target (fun A => F A)) →
      (∀ initial : PeriodicHypercubicEvenEdge H,
        initial ∉ S → P.variation initial = 0) →
      C.gibbsCovarianceReal (fun A => F A)
          (fun A => C.finiteSingleLinkHeatBathExpectationBCF schedule O A) =
        C.gibbsCovarianceReal (fun A => F A) (fun A => O A) ∧
      ∀ source : PeriodicHypercubicEvenEdge H,
        source ∈ T →
        ∀ (A B : C.base.Configuration),
          C.base.AgreeOffLink A B source →
          |C.finiteSingleLinkHeatBathExpectationBCF schedule O A -
            C.finiteSingleLinkHeatBathExpectationBCF schedule O B| ≤
            ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
              (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
                ∑ initial ∈ S, P.variation initial := by
  dsimp only
  intro F O P hFiber hSupport
  constructor
  · exact
      continuous_compact_oriented_gibbsCovarianceReal_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
        schedule F O hFiber
  · exact
      (periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathExpectationBCF_gibbsPairingReal_eq_and_difference_abs_le_geometric_of_supportsSeparatedBy
        H N D M hH hN beta hBeta hThreshold S T hsep
        schedule hNodup hLength F O P hFiber hSupport).2

end
end MathlibAnalytic
end MGAP4D
