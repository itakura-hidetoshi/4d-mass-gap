import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathObservableGeometricVariation
import Mathlib.Tactic

/-!
# Geometric variation for the actual finite heat-bath kernel expectation

The preceding layer proves geometric one-link variation for the bounded-
continuous Feller representative of a prescribed finite heat-bath schedule.
The current repository already identifies that representative pointwise with
the actual finite heat-bath-kernel observable action.

This file transfers the estimate across that exact equality.  Thus for two
configurations agreeing away from one source link in a separated support `T`,
the actual finite heat-bath expectation itself satisfies

`|E_schedule O(A) - E_schedule O(B)| ≤
  ((18 * q(beta))^D / (1 - 18 * q(beta))) *
    ∑ initial ∈ S, variation_before(initial)`.

No new estimate or multiplicity factor is introduced.  This remains a
finite-volume heat-bath/Dobrushin statement.  Heat-bath update count is not
Euclidean time.  No covariance decay, continuum clustering, positive physical
mass, OS Hamiltonian gap, or uniform factorial-continuum Dobrushin threshold is
asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathExpectationGeometricVariation
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual finite heat-bath-kernel expectation inherits the explicit
geometric one-link variation bound between separated periodic compact `SU(N)`
supports. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathExpectationBCF_difference_abs_le_geometric_of_supportsSeparatedBy
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
    ∀ (O : BoundedContinuousFunction C.base.Configuration ℝ)
      (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O),
      (∀ initial : PeriodicHypercubicEvenEdge H,
        initial ∉ S → P.variation initial = 0) →
      ∀ (A B : C.base.Configuration),
        C.base.AgreeOffLink A B source →
        |C.finiteSingleLinkHeatBathExpectationBCF schedule O A -
          C.finiteSingleLinkHeatBathExpectationBCF schedule O B| ≤
          ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
              ∑ initial ∈ S, P.variation initial := by
  dsimp only
  intro O P hSupport A B hAgree
  rw [← continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
        schedule O A,
      ← continuous_compact_oriented_finiteSingleLinkHeatBathContinuousBCF_eq_expectationBCF
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
        schedule O B]
  exact
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathContinuousBCF_difference_abs_le_geometric_of_supportsSeparatedBy
      H N D M hH hN beta hBeta hThreshold S T hsep
      schedule hNodup hLength source hsource O P hSupport A B hAgree

end

end MathlibAnalytic
end MGAP4D
