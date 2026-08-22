import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRandomScanGibbsCovariancePartialGeometric
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceRemainderLimit
import Mathlib.Tactic

/-!
# Periodic finite-volume spatial covariance decay

The separated-support finite random-scan telescope already gives a bound on

`|Cov(F,O) - Cov(F,R^M O)|`

uniformly in `M`, with the geometric factor `rho^D / (1-rho)`.  The terminal
random-scan covariance now tends to zero under the same strict Dobrushin
threshold.  Taking the limit therefore removes the auxiliary remainder and
yields the actual finite-volume two-sided spatial covariance estimate

`|Cov(F,O)|`
`  <= rho^D / (1-rho) * (sum_{e in T} delta_e(F)) * (sum_{i in S} delta_i(O))`.

This is a finite-volume Gibbs covariance clustering theorem.  It does not take
a continuum limit and does not by itself assert a positive physical
Hamiltonian mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

private instance periodicHypercubicEvenSideLength_neZero_spatialCovarianceGeometric
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- The actual periodic compact `SU(N)` Gibbs covariance decays geometrically
between plaquette-locally separated variation supports in finite volume. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_abs_le_geometric_of_supportsSeparatedBy
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
      ∀ e : PeriodicHypercubicEvenEdge H, e ∉ S → P.variation e = 0) :
    |(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).gibbsCovarianceReal
        (fun A => F A) (fun A => O A)| ≤
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
  let remainder : ℕ → ℝ := fun M =>
    C.gibbsCovarianceReal (fun A => F A)
      (fun A =>
        ((P.toRandomScanCenteredState).randomScanIterate Ddata M).observable A)
  let bound : ℝ :=
    ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ D /
      (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta)) *
      (∑ e ∈ T, PF.variation e) *
        ∑ i ∈ S, P.variation i
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEvenEdge H) :=
    periodicHypercubicEvenEdge_card_pos H
  have hCoeff : Ddata.coefficient < 1 := by
    simpa [Ddata,
      periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using
      hThreshold
  have hRemainder : Tendsto remainder atTop (nhds 0) := by
    dsimp [remainder]
    exact
      continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_iterate_tendsto_zero
        C F O P Ddata Ddata.coefficient_nonneg hCoeff hEdge
  have hDifference :
      Tendsto
        (fun M : ℕ =>
          C.gibbsCovarianceReal (fun A => F A) (fun A => O A) - remainder M)
        atTop
        (nhds (C.gibbsCovarianceReal (fun A => F A) (fun A => O A) - 0)) :=
    tendsto_const_nhds.sub hRemainder
  have hNorm :
      Tendsto
        (fun M : ℕ =>
          ‖C.gibbsCovarianceReal (fun A => F A) (fun A => O A) - remainder M‖)
        atTop
        (nhds ‖C.gibbsCovarianceReal (fun A => F A) (fun A => O A)‖) := by
    simpa using hDifference.norm
  have hPartial (M : ℕ) :
      |C.gibbsCovarianceReal (fun A => F A) (fun A => O A) - remainder M| ≤
        bound := by
    simpa [C, Ddata, remainder, bound] using
      periodicHypercubicEvenSpecialUnitary_gibbsCovarianceReal_randomScan_partial_telescope_abs_le_geometric_of_supportsSeparatedBy
        H N D hH hN beta hBeta hThreshold S T hsep F O PF P
        hFSupport hOSupport M
  have hFinal :
      ‖C.gibbsCovarianceReal (fun A => F A) (fun A => O A)‖ ≤ bound := by
    exact
      le_of_tendsto' hNorm
        (fun M => by
          simpa [Real.norm_eq_abs] using hPartial M)
  simpa [C, bound, Real.norm_eq_abs] using hFinal

end

end MathlibAnalytic
end MGAP4D
