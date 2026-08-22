import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathCenteredVariationSupportKernelBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFiniteHeatBathScheduleInfluenceGeometricTail
import Mathlib.Tactic

/-!
# Periodic geometric decay for actual finite heat-bath centered variation

The current same-root route now has both ingredients needed at the actual
Feller/observable carrier:

* the exact finite heat-bath centered variation profile is controlled by any
  pointwise schedule-kernel bound over the finite support of its initial
  variation;
* on genuinely plaquette-local separated periodic compact `SU(N)` supports,
  the exact schedule kernel has the explicit geometric bound under the current
  strict finite-volume Dobrushin threshold.

This file composes those facts.  If the initial centered variation vanishes
outside the left support `S`, then after a `Nodup` heat-bath schedule of length
`D + M`, every source in a support `T` separated from `S` by `D` satisfies

`variation_after(source) ≤ ((18 * q(beta))^D / (1 - 18 * q(beta))) *
  ∑ initial ∈ S, variation_before(initial)`.

This is an actual finite heat-bath/Feller variation estimate, not yet a
covariance theorem.  Heat-bath update count is not Euclidean time.  No
continuum clustering, positive physical mass, OS Hamiltonian gap, or uniform
factorial-continuum Dobrushin threshold is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_heatBathCenteredVariationGeometricTail
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- Actual finite heat-bath centered variation inherits the explicit geometric
factor between genuinely separated periodic compact `SU(N)` supports. -/
theorem
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathCenteredVariationProfile_variation_le_geometric_of_supportsSeparatedBy
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
      (P.finiteHeatBathCenteredVariationProfile data schedule).variation source ≤
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
            ∑ initial ∈ S, P.variation initial := by
  dsimp only
  intro O P hSupport
  apply
    continuous_compact_oriented_finiteHeatBathCenteredVariationProfile_variation_le_support_sum_mul_of_scheduleInfluenceKernel_le
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
      O P
      (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold)
      S schedule source
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta))
      hSupport
  intro initial hInitial
  exact
    periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_finiteHeatBathScheduleInfluenceKernel_le_geometric_of_supportsSeparatedBy
      H N D M hH hN beta hBeta hThreshold S T hsep
      schedule hNodup hLength initial hInitial source hsource

end

end MathlibAnalytic
end MGAP4D
