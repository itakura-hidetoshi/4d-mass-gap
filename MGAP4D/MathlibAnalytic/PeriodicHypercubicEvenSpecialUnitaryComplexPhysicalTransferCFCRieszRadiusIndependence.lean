import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszProjector

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology Metric
open scoped InnerProductSpace InnerProduct Ring Topology Interval Real

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszRadiusCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

private theorem complex_re_gt_of_mem_closedBall_radius_lt_gap
    {q r : ℝ} (hrgap : r < 1 - q) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) r) :
    q < z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre : |z.re - 1| ≤ ‖z - (1 : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (1 : ℂ))
  have hlow : 1 - z.re ≤ r := by
    calc
      1 - z.re = -(z.re - 1) := by ring
      _ ≤ |-(z.re - 1)| := le_abs_self _
      _ = |z.re - 1| := abs_neg _
      _ ≤ ‖z - (1 : ℂ)‖ := hre
      _ ≤ r := hz
  linarith

/-- For every positive radius strictly below the exact CFC spectral gap,
the centered regular block has zero contour integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredRegularBlock_circleIntegral_eq_zero_of_radius_lt_gap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta
    let Q :=
      (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta
    (∮ z in C((1 : ℂ), r), resolvent R z * Q) = 0 := by
  dsimp
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q :=
    (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) -
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta
  change (∮ z in C((1 : ℂ), r), resolvent R z * Q) = 0
  have hqOfClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r, q < z.re := by
    intro z hz
    apply complex_re_gt_of_mem_closedBall_radius_lt_gap
    · simpa [q] using hrgap
    · exact hz
  have hregDiffClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r,
        DifferentiableAt ℂ (fun w : ℂ => resolvent R w * Q) z := by
    intro z hz
    have hzq :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re := by
      simpa [q] using hqOfClosed z hz
    have hres :
        DifferentiableAt ℂ (fun w : ℂ => resolvent R w) z := by
      simpa [R] using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_differentiableAt_of_excitedNorm_lt_re
          H N hN beta hbeta z hzq
    exact DifferentiableAt.mul_const (𝕜 := ℂ) hres Q
  have hregContinuous :
      ContinuousOn (fun z : ℂ => resolvent R z * Q)
        (Metric.closedBall (1 : ℂ) r) := by
    intro z hz
    exact (hregDiffClosed z hz).continuousAt.continuousWithinAt
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hr.le Set.countable_empty hregContinuous
  intro z hz
  apply hregDiffClosed z
  exact Metric.ball_subset_closedBall hz.1

/-- The CFC resolvent contour integral is `2πi` times the top projection for
any positive circle contained in the exact spectral gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_circleIntegral_resolvent_eq_two_pi_I_smul_cfcTopProjection_of_radius_lt_gap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    (∮ z in C((1 : ℂ), r),
      resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) z) =
      (2 * Real.pi * Complex.I : ℂ) •
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta := by
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q :=
    (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) - P
  change (∮ z in C((1 : ℂ), r), resolvent S z) =
    (2 * Real.pi * Complex.I : ℂ) • P
  have hqOfClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r, q < z.re := by
    intro z hz
    apply complex_re_gt_of_mem_closedBall_radius_lt_gap
    · simpa [q] using hrgap
    · exact hz
  have hSphereClosed :
      ∀ z ∈ Metric.sphere (1 : ℂ) r, z ∈ Metric.closedBall (1 : ℂ) r := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_closedBall]
    exact hz.le
  have hSphereNe :
      ∀ z ∈ Metric.sphere (1 : ℂ) r, z ≠ (1 : ℂ) := by
    intro z hz hzeq
    subst z
    rw [Metric.mem_sphere] at hz
    have hzero : (0 : ℝ) = r := by simpa using hz
    exact hr.ne' hzero.symm
  have hpoleContinuous :
      ContinuousOn (fun z : ℂ => (z - 1)⁻¹ • P)
        (Metric.sphere (1 : ℂ) r) := by
    have hsub :
        ContinuousOn (fun z : ℂ => z - 1)
          (Metric.sphere (1 : ℂ) r) :=
      (continuous_id.sub continuous_const).continuousOn
    have hinv :
        ContinuousOn (fun z : ℂ => (z - 1)⁻¹)
          (Metric.sphere (1 : ℂ) r) :=
      hsub.inv₀ (by
        intro z hz
        exact sub_ne_zero.mpr (hSphereNe z hz))
    exact hinv.smul continuousOn_const
  have hpoleIntegrable :
      CircleIntegrable (fun z : ℂ => (z - 1)⁻¹ • P) (1 : ℂ) r :=
    hpoleContinuous.circleIntegrable hr.le
  have hregDiffClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r,
        DifferentiableAt ℂ (fun w : ℂ => resolvent R w * Q) z := by
    intro z hz
    have hzq :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re := by
      simpa [q] using hqOfClosed z hz
    have hres :
        DifferentiableAt ℂ (fun w : ℂ => resolvent R w) z := by
      simpa [R] using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_differentiableAt_of_excitedNorm_lt_re
          H N hN beta hbeta z hzq
    exact DifferentiableAt.mul_const (𝕜 := ℂ) hres Q
  have hregSphereContinuous :
      ContinuousOn (fun z : ℂ => resolvent R z * Q)
        (Metric.sphere (1 : ℂ) r) := by
    intro z hz
    exact
      (hregDiffClosed z (hSphereClosed z hz)).continuousAt.continuousWithinAt
  have hregIntegrable :
      CircleIntegrable (fun z : ℂ => resolvent R z * Q) (1 : ℂ) r :=
    hregSphereContinuous.circleIntegrable hr.le
  have hLaurentIntegral :
      (∮ z in C((1 : ℂ), r), resolvent S z) =
        ∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P + resolvent R z * Q := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzq :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ < z.re := by
      simpa [q] using hqOfClosed z (hSphereClosed z hz)
    have hz1 : z ≠ 1 := hSphereNe z hz
    simpa [S, P, R, Q] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_eq_topPole_add_centered
        H N hN beta hbeta z hzq hz1
  have hpoleIntegral :
      (∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P) =
        (2 * Real.pi * Complex.I : ℂ) • P := by
    rw [circleIntegral.integral_smul_const]
    have hmem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) r := by
      rw [Metric.mem_ball]
      simpa using hr
    rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
  have hregIntegral :
      (∮ z in C((1 : ℂ), r), resolvent R z * Q) = 0 := by
    simpa [R, Q] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredRegularBlock_circleIntegral_eq_zero_of_radius_lt_gap
        H N hN beta hbeta r hr hrgap
  calc
    (∮ z in C((1 : ℂ), r), resolvent S z) =
        ∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P + resolvent R z * Q :=
      hLaurentIntegral
    _ = (∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P) +
        (∮ z in C((1 : ℂ), r), resolvent R z * Q) :=
      circleIntegral.integral_add hpoleIntegrable hregIntegrable
    _ = (2 * Real.pi * Complex.I : ℂ) • P := by
      rw [hpoleIntegral, hregIntegral, add_zero]

/-- Every admissible CFC circle computes exactly the same normalized Riesz
projector, namely the full CFC top spectral projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection_of_radius_lt_gap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ) (hr : 0 < r)
    (hrgap :
      r < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C((1 : ℂ), r),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hint :
      (∮ z in C((1 : ℂ), r),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
      (2 * Real.pi * Complex.I : ℂ) • P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_circleIntegral_resolvent_eq_two_pi_I_smul_cfcTopProjection_of_radius_lt_gap
        H N hN beta hbeta r hr hrgap
  rw [hint]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  rw [smul_smul, inv_mul_cancel₀ htwoPiI, one_smul]

/-- The normalized CFC Riesz projector is independent of the chosen positive
circle radius as long as both circles stay inside the exact spectral gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_radius_independent
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr₁gap :
      r₁ < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
    (hr₂gap :
      r₂ < 1 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C((1 : ℂ), r₁),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C((1 : ℂ), r₂),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection_of_radius_lt_gap
      H N hN beta hbeta r₁ hr₁ hr₁gap,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection_of_radius_lt_gap
      H N hN beta hbeta r₂ hr₂ hr₂gap]

end
end MathlibAnalytic
end MGAP4D
