import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathExpectationGeometricVariation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathGibbsPairing
import Mathlib.Tactic

/-!
# Gibbs pairing with geometric finite heat-bath variation

The current finite-volume compact `SU(N)` Wilson carrier already has two exact
pieces needed by a static covariance argument:

* a finite heat-bath schedule may be inserted in the right factor of the Gibbs
  pairing whenever the left observable is constant on every updated link
  fiber;
* for separated periodic supports, the same actual finite heat-bath-kernel
  expectation has an explicit geometric one-link variation bound on every
  source link of the remote support.

This file joins those two statements without weakening either hypothesis.  The
result is a single reusable carrier: the Gibbs pairing is unchanged while the
right observable presented to the later covariance step has the geometric
Dobrushin variation bound simultaneously on all links of the separated support.

No covariance decay is asserted here.  In particular, heat-bath update count
is not identified with Euclidean time, and no continuum clustering, positive
physical mass, OS Hamiltonian gap, or uniform factorial-continuum Dobrushin
threshold is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathPairingGeometricVariation
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- For a separated pair of periodic compact `SU(N)` supports, a finite
heat-bath schedule can simultaneously preserve the Gibbs pairing against a left
observable which is constant on all updated fibers and geometrically flatten
the right observable on every link of the remote support. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathExpectationBCF_gibbsPairingReal_eq_and_difference_abs_le_geometric_of_supportsSeparatedBy
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
      C.gibbsPairingReal (fun A => F A)
          (fun A => C.finiteSingleLinkHeatBathExpectationBCF schedule O A) =
        C.gibbsPairingReal (fun A => F A) (fun A => O A) ∧
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
      continuous_compact_oriented_gibbsPairing_finiteSingleLinkHeatBathExpectationBCF_eq_of_left_offLinkFiberConstant
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
        schedule F O hFiber
  · intro source hsource A B hAgree
    exact
      periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteSingleLinkHeatBathExpectationBCF_difference_abs_le_geometric_of_supportsSeparatedBy
        H N D M hH hN beta hBeta hThreshold S T hsep
        schedule hNodup hLength source hsource O P hSupport A B hAgree

end

end MathlibAnalytic
end MGAP4D
