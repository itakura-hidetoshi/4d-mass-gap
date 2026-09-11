import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenDobrushinRandomScanFiniteResolventGeometric
import Mathlib.Tactic

/-!
# Periodic separated-support bound for the finite random-scan covariance telescope

The generic finite covariance telescope now gives

`|Cov(F,O) - Cov(F,R^M O)| <= sum_e delta_e(F) w_M(e)`.

For the current periodic compact `SU(N)` system, the finite resolvent profile
`w_M` already has a uniform separated-support geometric bound.  Combining the
two statements, and using the source support of `F`, gives the finite estimate

`|Cov(F,O) - Cov(F,R^M O)|`
`  <= rho^D / (1-rho) * (sum_{e in T} delta_e(F)) * (sum_{i in S} delta_i(O))`.

The estimate is uniform in the finite truncation length `M`.  The remainder
`Cov(F,R^M O)` is deliberately retained here.  Hence this file does not yet
assert absolute spatial covariance clustering, a continuum limit, or a
Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_randomScanPartialCovarianceGeometric
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual periodic compact `SU(N)` finite random-scan covariance telescope
inherits the sharp separated-support finite-resolvent decay, uniformly in the
truncation length.  The terminal random-scan covariance is still present. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_randomScan_partial_telescope_abs_le_geometric_of_supportsSeparatedBy
    (H N D : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (S T : Finset (PeriodicHypercubicEvenEdge H))
    (hsep : periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T)
    (F O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).base.Configuration ℝ)
    (PF : ContinuousCompactOrientedGaugeWilsonLinkVariationBound
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta)
      (fun A => F A))
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta) O)
    (hFSupport :
      ∀ e : PeriodicHypercubicEvenEdge H, e ∉ T → PF.variation e = 0)
    (hOSupport :
      ∀ e : PeriodicHypercubicEvenEdge H, e ∉ S → P.variation e = 0)
    (M : ℕ) :
    let Ddata :=
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
        (PeriodicHypercubicEvenSideLength H) N
        (by
          simp [PeriodicHypercubicEvenSideLength]
          omega)
        hN beta hBeta hThreshold
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).gibbsCovarianceReal
        (fun A => F A) (fun A => O A) -
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).gibbsCovarianceReal
        (fun A => F A)
        (fun A =>
          ((P.toRandomScanCenteredState).randomScanIterate Ddata M).observable A)| ≤
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (∑ e ∈ T, PF.variation e) *
          ∑ i ∈ S, P.variation i := by
  let C :=
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
  let Ddata :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  let w :=
    continuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
      Ddata P.variation M
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEvenEdge H) :=
    periodicHypercubicEvenEdge_card_pos H
  have hPartial :=
    continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_partial_telescope_abs_le_finiteResolventProfile
      C hEdge F PF P Ddata M
  have hPartial' :
      |C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
          C.gibbsCovarianceReal (fun A => F A)
            (fun A =>
              ((P.toRandomScanCenteredState).randomScanIterate Ddata M).observable A)| ≤
        ∑ e : PeriodicHypercubicEvenEdge H, PF.variation e * w e := by
    simpa [C, w] using hPartial
  have hRestrict :
      (∑ e : PeriodicHypercubicEvenEdge H, PF.variation e * w e) =
        ∑ e ∈ T, PF.variation e * w e := by
    exact
      finite_sum_eq_sum_support_of_eq_zero_off T
        (fun e : PeriodicHypercubicEvenEdge H => PF.variation e * w e)
        (by
          intro e he
          change PF.variation e * w e = 0
          rw [hFSupport e he, zero_mul])
  have hw (e : PeriodicHypercubicEvenEdge H) (he : e ∈ T) :
      w e ≤
        ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
          (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
            ∑ i ∈ S, P.variation i := by
    simpa [Ddata, w] using
      periodicHypercubicEvenSpecialUnitary_dobrushinRandomScanFiniteResolventProfile_le_geometric_of_supportsSeparatedBy
        H N D hH hN beta hBeta hThreshold S T hsep P.variation
        P.variation_nonneg hOSupport M e he
  have hSum :
      (∑ e ∈ T, PF.variation e * w e) ≤
        ∑ e ∈ T,
          PF.variation e *
            (((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
              (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
                ∑ i ∈ S, P.variation i) := by
    apply Finset.sum_le_sum
    intro e he
    exact mul_le_mul_of_nonneg_left (hw e he) (PF.variation_nonneg e)
  calc
    |C.gibbsCovarianceReal (fun A => F A) (fun A => O A) -
        C.gibbsCovarianceReal (fun A => F A)
          (fun A =>
            ((P.toRandomScanCenteredState).randomScanIterate Ddata M).observable A)| ≤
      ∑ e : PeriodicHypercubicEvenEdge H, PF.variation e * w e := hPartial'
    _ = ∑ e ∈ T, PF.variation e * w e := hRestrict
    _ ≤ ∑ e ∈ T,
        PF.variation e *
          (((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
            (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
              ∑ i ∈ S, P.variation i) := hSum
    _ =
      ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
        (∑ e ∈ T, PF.variation e) *
          ∑ i ∈ S, P.variation i := by
      rw [← Finset.sum_mul]
      ring

end

end MathlibAnalytic
end MGAP4D
