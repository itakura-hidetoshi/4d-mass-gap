import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearDerivative
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring Topology

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Left multiplication by a fixed resolvent, as a continuous linear map on
the Banach algebra of continuous endomorphisms. -/
def continuousLinearMapRealResolventLeftPerturbation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  (ContinuousLinearMap.mul ℝ (V →L[ℝ] V)) R

@[simp]
theorem continuousLinearMapRealResolventLeftPerturbation_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R H : V →L[ℝ] V) :
    continuousLinearMapRealResolventLeftPerturbation R H = R * H :=
  rfl

/-- Right multiplication by a fixed resolvent, as a continuous linear map on
the Banach algebra of continuous endomorphisms. -/
def continuousLinearMapRealResolventRightMultiplication
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  (ContinuousLinearMap.mul ℝ (V →L[ℝ] V)).flip R

@[simp]
theorem continuousLinearMapRealResolventRightMultiplication_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R T : V →L[ℝ] V) :
    continuousLinearMapRealResolventRightMultiplication R T = T * R :=
  rfl

/-- The explicit noncommutative power series of the operator-variable real
resolvent at `A`.  It is obtained by composing the geometric series with left
multiplication by the base resolvent and then right multiplication by that
resolvent. -/
def continuousLinearMapRealResolventOperatorFPowerSeries
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ) :
    FormalMultilinearSeries ℝ (V →L[ℝ] V) (V →L[ℝ] V) :=
  let R := continuousLinearMapRealResolvent A z
  (continuousLinearMapRealResolventRightMultiplication R).compFormalMultilinearSeries
    ((formalMultilinearSeries_geometric ℝ (V →L[ℝ] V)).comp
      ((continuousLinearMapRealResolventLeftPerturbation R).fpowerSeries 0))

/-- The local geometric resolvent formula has the explicit operator-variable
power series above at the zero perturbation. -/
theorem continuousLinearMapRealResolventOperatorFPowerSeries_hasFPowerSeriesAt_local
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ) :
    HasFPowerSeriesAt
      (fun H : V →L[ℝ] V =>
        Ring.inverse
            (1 - continuousLinearMapRealResolvent A z * H) *
          continuousLinearMapRealResolvent A z)
      (continuousLinearMapRealResolventOperatorFPowerSeries A z) 0 := by
  let R := continuousLinearMapRealResolvent A z
  let L := continuousLinearMapRealResolventLeftPerturbation R
  let Q := continuousLinearMapRealResolventRightMultiplication R
  have hgeom : HasFPowerSeriesAt
      (fun X : V →L[ℝ] V => Ring.inverse (1 - X))
      (formalMultilinearSeries_geometric ℝ (V →L[ℝ] V)) 0 :=
    (hasFPowerSeriesOnBall_inverse_one_sub ℝ (V →L[ℝ] V)).hasFPowerSeriesAt
  have hlinear : HasFPowerSeriesAt L (L.fpowerSeries 0) 0 :=
    L.hasFPowerSeriesAt 0
  have hcomp := hgeom.comp hlinear
  rcases hcomp with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  simpa [continuousLinearMapRealResolventOperatorFPowerSeries,
    R, L, Q, Function.comp_def] using Q.comp_hasFPowerSeriesOnBall hr

/-- Around every point where the shifted operator is a unit, the actual
operator-variable real resolvent has the explicit power series above. -/
theorem continuousLinearMapRealResolventOperator_hasFPowerSeriesAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z)) :
    HasFPowerSeriesAt
      (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z)
      (continuousLinearMapRealResolventOperatorFPowerSeries A z) A := by
  let S := continuousLinearMapRealShift A z
  let R := continuousLinearMapRealResolvent A z
  let L := continuousLinearMapRealResolventLeftPerturbation R
  have hlocal :=
    continuousLinearMapRealResolventOperatorFPowerSeries_hasFPowerSeriesAt_local A z
  have hsmall : ∀ᶠ H : V →L[ℝ] V in 𝓝 0, ‖R * H‖ < 1 := by
    have hball : Metric.ball (0 : V →L[ℝ] V) 1 ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ one_pos
    have hpre := L.continuous.continuousAt hball
    filter_upwards [hpre] with H hH
    simpa [Metric.mem_ball, dist_zero_right, L] using hH
  have heq :
      (fun H : V →L[ℝ] V => Ring.inverse (1 - R * H) * R) =ᶠ[𝓝 0]
        (fun H : V →L[ℝ] V =>
          continuousLinearMapRealResolvent (A + H) z) := by
    filter_upwards [hsmall] with H hH
    let U : (V →L[ℝ] V)ˣ := Units.oneSub (R * H) hH
    have hOne : IsUnit (1 - R * H) := U.isUnit
    have hSR : S * R = 1 := by
      simpa [S, R, continuousLinearMapRealResolvent] using
        mul_ringInverse_of_isUnit hunit
    have hRS : R * S = 1 := by
      simpa [S, R, continuousLinearMapRealResolvent] using
        ringInverse_mul_of_isUnit hunit
    have hfactor :
        continuousLinearMapRealShift (A + H) z = S * (1 - R * H) := by
      calc
        continuousLinearMapRealShift (A + H) z = S - H := by
          simp [continuousLinearMapRealShift, S]
        _ = S * (1 - R * H) := by
          rw [mul_sub, mul_one, ← mul_assoc, hSR, one_mul]
    have hshiftUnit : IsUnit (continuousLinearMapRealShift (A + H) z) := by
      rw [hfactor]
      exact hunit.mul hOne
    have hcandidateRight :
        continuousLinearMapRealShift (A + H) z *
            (Ring.inverse (1 - R * H) * R) = 1 := by
      rw [hfactor]
      calc
        (S * (1 - R * H)) * (Ring.inverse (1 - R * H) * R) =
            S * ((1 - R * H) * Ring.inverse (1 - R * H)) * R := by
              simp [mul_assoc]
        _ = S * R := by
              rw [mul_ringInverse_of_isUnit hOne]
              simp
        _ = 1 := hSR
    have hactualLeft :
        continuousLinearMapRealResolvent (A + H) z *
            continuousLinearMapRealShift (A + H) z = 1 := by
      simpa [continuousLinearMapRealResolvent] using
        ringInverse_mul_of_isUnit hshiftUnit
    calc
      Ring.inverse (1 - R * H) * R =
          1 * (Ring.inverse (1 - R * H) * R) := by rw [one_mul]
      _ = (continuousLinearMapRealResolvent (A + H) z *
            continuousLinearMapRealShift (A + H) z) *
              (Ring.inverse (1 - R * H) * R) := by rw [hactualLeft]
      _ = continuousLinearMapRealResolvent (A + H) z *
            (continuousLinearMapRealShift (A + H) z *
              (Ring.inverse (1 - R * H) * R)) := by simp [mul_assoc]
      _ = continuousLinearMapRealResolvent (A + H) z := by
            rw [hcandidateRight, mul_one]
  have hzero : HasFPowerSeriesAt
      (fun H : V →L[ℝ] V => continuousLinearMapRealResolvent (A + H) z)
      (continuousLinearMapRealResolventOperatorFPowerSeries A z) 0 := by
    simpa [R] using hlocal.congr heq
  have htranslated := hzero.comp_sub A
  simpa only [zero_add, add_sub_cancel_left] using htranslated

/-- The actual finite-dimensional real resolvent is analytic as a function of
the operator at every point of its resolvent set. -/
theorem continuousLinearMapRealResolventOperator_analyticAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z)) :
    AnalyticAt ℝ
      (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) A :=
  (continuousLinearMapRealResolventOperator_hasFPowerSeriesAt A z hunit).analyticAt

end MathlibAnalytic
end MGAP4D
