import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterTaylorDysonCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring Topology

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The full diagonal of the genuine finite-parameter Fréchet derivative is
`n!` times the finite-parameter Taylor-Dyson coefficient. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_diagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapFiniteParameterRealResolventChart m A H z) t
        (fun _ => h) =
      (n.factorial : ℝ) •
        continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
          n m A H z t h := by
  rw [continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_apply
    m A H z t hunit n]
  simpa [continuousLinearMapFiniteParameterDirectionTuple,
    continuousLinearMapFiniteParameterOperatorIncrement,
    continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient] using
    continuousLinearMapRealResolventOperatorSymmetricDerivative_const n
      (continuousLinearMapFiniteParameterOperatorChart m A H t)
      (continuousLinearMapFiniteParameterOperatorIncrement m H h) z

/-- The normalized diagonal Fréchet coefficient. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  ((n.factorial : ℝ)⁻¹) •
    iteratedFDeriv ℝ n
      (continuousLinearMapFiniteParameterRealResolventChart m A H z) t
      (fun _ => h)

/-- At a resolvent point, the normalized diagonal Fréchet coefficient is
exactly the Taylor-Dyson coefficient. -/
theorem continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient_eq_taylorDysonCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z)) :
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
        n m A H z t h =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
        n m A H z t h := by
  rw [continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient,
    continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_diagonal
      n m A H z t h hunit]
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  simp [smul_smul, hfactorial]

/-- The genuine finite-parameter Fréchet Taylor polynomial through degree
`N - 1`. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  ∑ n ∈ Finset.range N,
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
      n m A H z t h

/-- At a resolvent point, the genuine Fréchet Taylor polynomial equals the
finite noncommutative Taylor-Dyson polynomial. -/
theorem continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum_eq_taylorDysonPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z)) :
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
        N m A H z t h =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
        N m A H z t h := by
  unfold continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
  unfold continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
  unfold continuousLinearMapRealResolventOperatorDysonPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient_eq_taylorDysonCoefficient
    n m A H z t h hunit

/-- Exact multivariable Fréchet Taylor formula with the true noncommutative
resolvent remainder. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_add_eq_frechetTaylorPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h) =
      continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
          N m A H z t h +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
          N m A H z t h := by
  rw [continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum_eq_taylorDysonPartialSum
    N m A H z t h hunit]
  exact continuousLinearMapFiniteParameterRealResolventChart_add_eq_taylorDysonPartialSum_add_remainder
    N m A H z t h hunit hsmall

/-- Endpoint form of the exact multivariable Fréchet Taylor formula. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_eq_frechetTaylorPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (s t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H s) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z s *
      continuousLinearMapFiniteParameterOperatorIncrement m H (t - s)‖ < 1) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z t =
      continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
          N m A H z s (t - s) +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
          N m A H z s (t - s) := by
  rw [continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum_eq_taylorDysonPartialSum
    N m A H z s (t - s) hunit]
  exact continuousLinearMapFiniteParameterRealResolventChart_eq_taylorDysonPartialSum_add_remainder
    N m A H z s t hunit hsmall

/-- Finite jet of normalized diagonal Fréchet Taylor coefficients. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : Fin N → (V →L[ℝ] V) :=
  fun n => continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
    n.1 m A H z t h

end MathlibAnalytic
end MGAP4D
