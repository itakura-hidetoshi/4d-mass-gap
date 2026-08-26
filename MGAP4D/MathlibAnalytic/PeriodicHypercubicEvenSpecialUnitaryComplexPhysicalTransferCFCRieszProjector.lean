import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventResidueLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set Filter Topology Metric
open scoped InnerProductSpace InnerProduct Ring Topology Interval Real

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexRieszComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- Canonical contour radius separating the isolated CFC top point `1` from the
centered transfer spectrum. -/
def periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  (1 -
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖) / 2

/-- The canonical CFC Riesz radius is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta := by
  have hlt :
      ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
      H N hN beta hbeta
  rw [
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
      H N hN beta hbeta] at hlt
  dsimp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius]
  linarith

private theorem complex_re_gt_of_mem_closedBall_one_half_gap
    {q : ℝ} (hq : q < 1) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) ((1 - q) / 2)) :
    q < z.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre : |z.re - 1| ≤ ‖z - (1 : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (1 : ℂ))
  have hlow : -(z.re - 1) ≤ (1 - q) / 2 := by
    calc
      -(z.re - 1) ≤ |-(z.re - 1)| := le_abs_self _
      _ = |z.re - 1| := abs_neg _
      _ ≤ ‖z - (1 : ℂ)‖ := hre
      _ ≤ (1 - q) / 2 := hz
  linarith

/-- The centered resolvent is complex differentiable at every point of the
right-half-plane region controlled by the exact excited-sector norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_resolvent_differentiableAt_of_excitedNorm_lt_re
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (z : ℂ)
    (hzq :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ < z.re) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
            H N hN beta hbeta) w)
      z := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let A := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  have hzR : z ∈ resolventSet ℂ R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mem_resolventSet_of_excitedNorm_lt_re
        H N hN beta hbeta z hzq
  have hzRUnit : IsUnit (algebraMap ℂ A z - R) := hzR
  have hscalar :
      DifferentiableAt ℂ (fun w : ℂ => w • (1 : A)) z :=
    DifferentiableAt.smul_const (𝕜 := ℂ)
      (show DifferentiableAt ℂ (fun w : ℂ => w) z from differentiableAt_id) (1 : A)
  have hshiftScalar :
      DifferentiableAt ℂ (fun w : ℂ => w • (1 : A) - R) z :=
    hscalar.sub_const R
  have hshift :
      DifferentiableAt ℂ (fun w : ℂ => algebraMap ℂ A w - R) z := by
    simpa [Algebra.algebraMap_eq_smul_one] using hshiftScalar
  have hinv :
      DifferentiableAt ℂ (fun x : A => Ring.inverse x)
        (algebraMap ℂ A z - R) :=
    differentiableAt_inverse (𝕜 := ℂ) hzRUnit
  simpa [resolvent, Function.comp_def] using hinv.comp z hshift

/-- The centered regular block has zero contour integral on the canonical CFC
circle. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredRegularBlock_circleIntegral_eq_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta
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
  let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  let Q :=
    (1 : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) -
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta
  change (∮ z in C((1 : ℂ), r), resolvent R z * Q) = 0
  have hq : q < 1 := by
    have hlt :
        ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
          H N hN beta hbeta‖ < 1 :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
        H N hN beta hbeta
    rw [
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
        H N hN beta hbeta] at hlt
    simpa [q] using hlt
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
  have hrDef : r = (1 - q) / 2 := by
    simp [r, q, periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius]
  have hqOfClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r, q < z.re := by
    intro z hz
    apply complex_re_gt_of_mem_closedBall_one_half_gap hq
    simpa [hrDef] using hz
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

/-- The unnormalized contour integral of the genuine complex normalized Wilson
transfer resolvent is exactly `2πi` times the full CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_circleIntegral_resolvent_eq_two_pi_I_smul_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta
    (∮ z in C((1 : ℂ), r),
      resolvent
        (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) z) =
      (2 * Real.pi * Complex.I : ℂ) •
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta := by
  dsimp
  let q :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
    H N hN beta hbeta
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
  have hq : q < 1 := by
    have hlt :
        ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
          H N hN beta hbeta‖ < 1 :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
        H N hN beta hbeta
    rw [
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
        H N hN beta hbeta] at hlt
    simpa [q] using hlt
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
  have hrDef : r = (1 - q) / 2 := by
    simp [r, q, periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius]
  have hqOfClosed :
      ∀ z ∈ Metric.closedBall (1 : ℂ) r, q < z.re := by
    intro z hz
    apply complex_re_gt_of_mem_closedBall_one_half_gap hq
    simpa [hrDef] using hz
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
    simpa [r, R, Q] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredRegularBlock_circleIntegral_eq_zero
        H N hN beta hbeta
  calc
    (∮ z in C((1 : ℂ), r), resolvent S z) =
        ∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P + resolvent R z * Q :=
      hLaurentIntegral
    _ = (∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P) +
        (∮ z in C((1 : ℂ), r), resolvent R z * Q) :=
      circleIntegral.integral_add hpoleIntegrable hregIntegrable
    _ = (2 * Real.pi * Complex.I : ℂ) • P := by
      rw [hpoleIntegral, hregIntegral, add_zero]

/-- The CFC top projection is the Riesz spectral projector obtained by the
normalized resolvent contour integral around the isolated top point `1`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C((1 : ℂ), r),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  dsimp
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  have hint :
      (∮ z in C((1 : ℂ),
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
          H N hN beta hbeta),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
      (2 * Real.pi * Complex.I : ℂ) • P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_circleIntegral_resolvent_eq_two_pi_I_smul_cfcTopProjection
        H N hN beta hbeta
  rw [hint]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  rw [smul_smul, inv_mul_cancel₀ htwoPiI, one_smul]

/-- Audit-visible package for the isolated CFC Riesz projector. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszProjectorPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  radiusPositive :
    0 < periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta
  normalizedContourProjector :
    let r := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta hbeta
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ z in C((1 : ℂ), r),
        resolvent
          (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta) z) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta

/-- Construct the rank-free CFC Riesz-projector package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszProjectorPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCRieszProjectorPackage
      H N hN beta hbeta :=
  { radiusPositive :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta hbeta
    normalizedContourProjector :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_rieszProjector_eq_cfcTopProjection
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
