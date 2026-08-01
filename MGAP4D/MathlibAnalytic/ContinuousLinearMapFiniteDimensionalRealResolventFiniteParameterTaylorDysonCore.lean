import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterFrechet
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The synthesized operator increment associated with a finite parameter
increment. -/
def continuousLinearMapFiniteParameterOperatorIncrement
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterDirectionSynthesis m H h

@[simp]
theorem continuousLinearMapFiniteParameterOperatorIncrement_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterOperatorIncrement m H h =
      ∑ j : Fin m, h j • H j := by
  simp [continuousLinearMapFiniteParameterOperatorIncrement]

/-- Moving by a parameter increment is exactly an additive operator
perturbation by its synthesis. -/
@[simp]
theorem continuousLinearMapFiniteParameterOperatorChart_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (t h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterOperatorChart m A H (t + h) =
      continuousLinearMapFiniteParameterOperatorChart m A H t +
        continuousLinearMapFiniteParameterOperatorIncrement m H h := by
  simp [continuousLinearMapFiniteParameterOperatorChart,
    continuousLinearMapFiniteParameterOperatorIncrement, map_add]

/-- The operator at an endpoint is the operator at the base parameter plus the
synthesized endpoint difference. -/
theorem continuousLinearMapFiniteParameterOperatorChart_eq_add_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (s t : Fin m → ℝ) :
    continuousLinearMapFiniteParameterOperatorChart m A H t =
      continuousLinearMapFiniteParameterOperatorChart m A H s +
        continuousLinearMapFiniteParameterOperatorIncrement m H (t - s) := by
  simp [continuousLinearMapFiniteParameterOperatorChart,
    continuousLinearMapFiniteParameterOperatorIncrement, map_sub]

/-- The `n`-th finite-parameter Taylor-Dyson coefficient at `t` in increment
`h`. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolventOperatorDysonCoefficient n
    (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapFiniteParameterOperatorIncrement m H h) z

/-- The finite Taylor-Dyson polynomial through degree `N - 1`. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolventOperatorDysonPartialSum N
    (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapFiniteParameterOperatorIncrement m H h) z

/-- The true finite-parameter Taylor-Dyson remainder. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolventOperatorDysonRemainder N
    (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapFiniteParameterOperatorIncrement m H h) z

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
        0 m A H z t h =
      continuousLinearMapFiniteParameterRealResolventChart m A H z t := by
  simp [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterRealResolventChart]

/-- Small synthesized increments preserve the real resolvent set. -/
theorem continuousLinearMapFiniteParameterRealShift_add_isUnit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H (t + h)) z) := by
  rw [continuousLinearMapFiniteParameterOperatorChart_add]
  exact continuousLinearMapRealShift_add_isUnit_of_resolvent_mul_norm_lt_one
    (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapFiniteParameterOperatorIncrement m H h) z hunit
    (by simpa [continuousLinearMapFiniteParameterRealResolventChart] using hsmall)

/-- Exact multivariable Taylor-Dyson expansion along an arbitrary parameter
increment. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_add_eq_taylorDysonPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h) =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
          N m A H z t h +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
          N m A H z t h := by
  unfold continuousLinearMapFiniteParameterRealResolventChart
  rw [continuousLinearMapFiniteParameterOperatorChart_add]
  exact continuousLinearMapRealResolvent_add_eq_operatorDysonPartialSum_add_remainder
    N (continuousLinearMapFiniteParameterOperatorChart m A H t)
      (continuousLinearMapFiniteParameterOperatorIncrement m H h) z hunit
      (by simpa [continuousLinearMapFiniteParameterRealResolventChart] using hsmall)

/-- Exact endpoint form of the finite-parameter Taylor-Dyson expansion. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_eq_taylorDysonPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (s t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H s) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z s *
      continuousLinearMapFiniteParameterOperatorIncrement m H (t - s)‖ < 1) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z t =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
          N m A H z s (t - s) +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
          N m A H z s (t - s) := by
  have hadd : s + (t - s) = t := by abel
  simpa [hadd] using
    continuousLinearMapFiniteParameterRealResolventChart_add_eq_taylorDysonPartialSum_add_remainder
      N m A H z s (t - s) hunit hsmall

/-- The exact finite-parameter approximation defect is the true remainder. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_add_sub_taylorDysonPartialSum_eq_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h) -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
          N m A H z t h =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
        N m A H z t h := by
  rw [continuousLinearMapFiniteParameterRealResolventChart_add_eq_taylorDysonPartialSum_add_remainder
    N m A H z t h hunit hsmall]
  abel

/-- Geometric norm control of the exact finite-parameter remainder. -/
theorem continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z q M : ℝ) (t h : Fin m → ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ ≤ q)
    (hnew : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h)‖ ≤ M) :
    ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
        N m A H z t h‖ ≤ q ^ N * M := by
  exact continuousLinearMapRealResolventOperatorDysonRemainder_norm_le
    N (continuousLinearMapFiniteParameterOperatorChart m A H t)
      (continuousLinearMapFiniteParameterOperatorIncrement m H h) z q M hq hM
      (by simpa [continuousLinearMapFiniteParameterRealResolventChart] using hperturb)
      (by simpa [continuousLinearMapFiniteParameterRealResolventChart,
        continuousLinearMapFiniteParameterOperatorChart_add] using hnew)

end MathlibAnalytic
end MGAP4D
