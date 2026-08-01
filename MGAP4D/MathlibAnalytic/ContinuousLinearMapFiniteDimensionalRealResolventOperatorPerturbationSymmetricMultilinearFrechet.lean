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
resolvent at `A`.  It is obtained by precomposing the geometric series with
left multiplication by the base resolvent and then postcomposing with right
multiplication by that resolvent. -/
def continuousLinearMapRealResolventOperatorFPowerSeries
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ) :
    FormalMultilinearSeries ℝ (V →L[ℝ] V) (V →L[ℝ] V) :=
  let R := continuousLinearMapRealResolvent A z
  (continuousLinearMapRealResolventRightMultiplication R).compFormalMultilinearSeries
    ((formalMultilinearSeries_geometric ℝ (V →L[ℝ] V)).compContinuousLinearMap
      (continuousLinearMapRealResolventLeftPerturbation R))

/-- The `n`-th coefficient of the explicit resolvent power series is exactly
the ordered noncommutative Dyson word. -/
@[simp]
theorem continuousLinearMapRealResolventOperatorFPowerSeries_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (n : ℕ) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorFPowerSeries A z n H =
      continuousLinearMapRealResolventOrderedDysonMultilinear n
        (continuousLinearMapRealResolvent A z) H := by
  rw [continuousLinearMapRealResolventOrderedDysonMultilinear_apply]
  simp [continuousLinearMapRealResolventOperatorFPowerSeries,
    formalMultilinearSeries_geometric, Function.comp_def]

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
  have hgeomAtLinearZero : HasFPowerSeriesAt
      (fun X : V →L[ℝ] V => Ring.inverse (1 - X))
      (formalMultilinearSeries_geometric ℝ (V →L[ℝ] V)) (L 0) := by
    simpa using hgeom
  have hcomp := hgeomAtLinearZero.compContinuousLinearMap
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
    have hpre : L ⁻¹' Metric.ball (0 : V →L[ℝ] V) 1 ∈ 𝓝 0 :=
      L.continuous.continuousAt (by simpa using hball)
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
    have hfactor :
        continuousLinearMapRealShift (A + H) z = S * (1 - R * H) := by
      calc
        continuousLinearMapRealShift (A + H) z = S - H := by
          simp only [continuousLinearMapRealShift, S]
          abel
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
  have hfun :
      (fun B : V →L[ℝ] V =>
        continuousLinearMapRealResolvent (A + (B - A)) z) =
      (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) := by
    funext B
    congr 1
    abel
  rw [hfun] at htranslated
  simpa using htranslated

/-- The actual finite-dimensional real resolvent is analytic as a function of
the operator at every point of its resolvent set. -/
theorem continuousLinearMapRealResolventOperator_analyticAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z)) :
    AnalyticAt ℝ
      (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) A :=
  (continuousLinearMapRealResolventOperator_hasFPowerSeriesAt A z hunit).analyticAt

/-- The genuine `n`-th Fréchet derivative of the operator-variable real
resolvent is the fully symmetrized noncommutative Dyson word. -/
theorem continuousLinearMapRealResolventOperator_iteratedFDeriv_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z))
    (n : ℕ) (H : Fin n → (V →L[ℝ] V)) :
    iteratedFDeriv ℝ n
        (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) A H =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n A z H := by
  rcases continuousLinearMapRealResolventOperator_hasFPowerSeriesAt A z hunit with
    ⟨r, hr⟩
  rw [continuousLinearMapRealResolventOperatorSymmetricDerivative_apply]
  calc
    iteratedFDeriv ℝ n
        (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) A H =
      ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOperatorFPowerSeries A z n
          (fun i => H (σ i)) :=
      hr.iteratedFDeriv_eq_sum_of_completeSpace H
    _ = ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonMultilinear n
          (continuousLinearMapRealResolvent A z) (fun i => H (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact continuousLinearMapRealResolventOperatorFPowerSeries_apply
        A z n (fun i => H (σ i))

/-- Equality of continuous multilinear maps: the actual iterated Fréchet
derivative is exactly the symmetric resolvent derivative map constructed from
all direction permutations. -/
theorem continuousLinearMapRealResolventOperator_iteratedFDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →L[ℝ] V) (z : ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift A z)) (n : ℕ) :
    iteratedFDeriv ℝ n
        (fun B : V →L[ℝ] V => continuousLinearMapRealResolvent B z) A =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n A z := by
  apply ContinuousMultilinearMap.ext
  intro H
  exact continuousLinearMapRealResolventOperator_iteratedFDeriv_apply
    A z hunit n H

end MathlibAnalytic
end MGAP4D
