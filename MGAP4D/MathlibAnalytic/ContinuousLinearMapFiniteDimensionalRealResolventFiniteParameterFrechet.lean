import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterCore
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring Topology

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The operator-variable resolvent power series pulled back along a finite
family of real perturbation parameters, based at an arbitrary parameter
vector `t₀`. -/
def continuousLinearMapFiniteParameterRealResolventFPowerSeries
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ) :
    FormalMultilinearSeries ℝ (Fin m → ℝ) (V →L[ℝ] V) :=
  (continuousLinearMapRealResolventOperatorFPowerSeries
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z).compContinuousLinearMap
    (continuousLinearMapFiniteParameterDirectionSynthesis m H)

/-- The `n`-th coefficient of the finite-parameter power series is the ordered
Dyson word evaluated on the synthesized parameter directions. -/
@[simp]
theorem continuousLinearMapFiniteParameterRealResolventFPowerSeries_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ) (n : ℕ)
    (u : Fin n → (Fin m → ℝ)) :
    continuousLinearMapFiniteParameterRealResolventFPowerSeries
        m A H z t₀ n u =
      continuousLinearMapRealResolventOrderedDysonMultilinear n
        (continuousLinearMapRealResolvent
          (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z)
        (continuousLinearMapFiniteParameterDirectionTuple m n H u) := by
  simp [continuousLinearMapFiniteParameterRealResolventFPowerSeries,
    continuousLinearMapFiniteParameterDirectionTuple]

/-- At every parameter point where the shifted operator is a unit, the
finite-parameter resolvent chart admits the pulled-back noncommutative power
series. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_hasFPowerSeriesAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z)) :
    HasFPowerSeriesAt
      (continuousLinearMapFiniteParameterRealResolventChart m A H z)
      (continuousLinearMapFiniteParameterRealResolventFPowerSeries m A H z t₀)
      t₀ := by
  let B := continuousLinearMapFiniteParameterOperatorChart m A H t₀
  let L := continuousLinearMapFiniteParameterDirectionSynthesis m H
  let p := continuousLinearMapRealResolventOperatorFPowerSeries B z
  have hB : HasFPowerSeriesAt
      (fun C : V →L[ℝ] V => continuousLinearMapRealResolvent C z) p B :=
    continuousLinearMapRealResolventOperator_hasFPowerSeriesAt B z hunit
  have hzeroRaw := hB.comp_sub (-B)
  have hzero : HasFPowerSeriesAt
      (fun X : V →L[ℝ] V => continuousLinearMapRealResolvent (B + X) z)
      p 0 := by
    have hfun :
        (fun X : V →L[ℝ] V => continuousLinearMapRealResolvent (X - (-B)) z) =
        (fun X : V →L[ℝ] V => continuousLinearMapRealResolvent (B + X) z) := by
      funext X
      congr 1
      abel
    rw [hfun] at hzeroRaw
    simpa using hzeroRaw
  have hparamZero := hzero.compContinuousLinearMap (u := L) (x := (0 : Fin m → ℝ))
  have hparamRaw := hparamZero.comp_sub t₀
  have hfun :
      (fun t : Fin m → ℝ =>
        continuousLinearMapRealResolvent (B + L (t - t₀)) z) =
      continuousLinearMapFiniteParameterRealResolventChart m A H z := by
    funext t
    congr 1
    simp only [continuousLinearMapFiniteParameterRealResolventChart,
      continuousLinearMapFiniteParameterOperatorChart, B, L]
    rw [map_sub]
    abel
  rw [hfun] at hparamRaw
  simpa [continuousLinearMapFiniteParameterRealResolventFPowerSeries, B, L, p,
    Function.comp_def] using hparamRaw

/-- The finite-parameter resolvent chart is analytic at every parameter point
lying in the real resolvent set. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_analyticAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z)) :
    AnalyticAt ℝ
      (continuousLinearMapFiniteParameterRealResolventChart m A H z) t₀ :=
  (continuousLinearMapFiniteParameterRealResolventChart_hasFPowerSeriesAt
    m A H z t₀ hunit).analyticAt

/-- Arbitrary mixed parameter-direction Fréchet derivatives are obtained by
synthesizing every parameter direction and applying the symmetric operator
resolvent derivative. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z))
    (n : ℕ) (u : Fin n → (Fin m → ℝ)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapFiniteParameterRealResolventChart m A H z) t₀ u =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z
        (continuousLinearMapFiniteParameterDirectionTuple m n H u) := by
  rcases continuousLinearMapFiniteParameterRealResolventChart_hasFPowerSeriesAt
      m A H z t₀ hunit with ⟨r, hr⟩
  rw [continuousLinearMapRealResolventOperatorSymmetricDerivative_apply]
  calc
    iteratedFDeriv ℝ n
        (continuousLinearMapFiniteParameterRealResolventChart m A H z) t₀ u =
      ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapFiniteParameterRealResolventFPowerSeries
          m A H z t₀ n (fun i => u (σ i)) :=
      hr.iteratedFDeriv_eq_sum_of_completeSpace u
    _ = ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonMultilinear n
          (continuousLinearMapRealResolvent
            (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z)
          (fun i => continuousLinearMapFiniteParameterDirectionTuple m n H u (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      simpa [continuousLinearMapFiniteParameterDirectionTuple] using
        continuousLinearMapFiniteParameterRealResolventFPowerSeries_apply
          m A H z t₀ n (fun i => u (σ i))

/-- Equality of continuous multilinear maps for the finite-parameter
pullback. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z))
    (n : ℕ) :
    iteratedFDeriv ℝ n
        (continuousLinearMapFiniteParameterRealResolventChart m A H z) t₀ =
      (continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z).compContinuousLinearMap
          (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis m H) := by
  apply ContinuousMultilinearMap.ext
  intro u
  simpa [continuousLinearMapFiniteParameterDirectionTuple] using
    continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_apply
      m A H z t₀ hunit n u

/-- Coordinate mixed partials, with repeated coordinates allowed, are the
symmetric operator derivative evaluated on the corresponding operator
directions. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_coordinateMixedPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t₀ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z))
    (n : ℕ) (κ : Fin n → Fin m) :
    iteratedFDeriv ℝ n
        (continuousLinearMapFiniteParameterRealResolventChart m A H z) t₀
        (fun i => Pi.single (κ i) 1) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t₀) z
        (fun i => H (κ i)) := by
  rw [continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_apply
    m A H z t₀ hunit n]
  congr 1
  exact continuousLinearMapFiniteParameterDirectionTuple_coordinate m n H κ

end MathlibAnalytic
end MGAP4D
