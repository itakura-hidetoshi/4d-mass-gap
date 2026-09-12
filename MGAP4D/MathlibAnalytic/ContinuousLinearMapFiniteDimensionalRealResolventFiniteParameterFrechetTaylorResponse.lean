import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterFrechetTaylor
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Continuous-linear observation of a finite-parameter Taylor coefficient. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  φ (continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
    n m A H z t h)

/-- Continuous-linear observation of the finite Fréchet Taylor polynomial. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  φ (continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
    N m A H z t h)

/-- Continuous-linear observation of the true finite-parameter remainder. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  φ (continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
    N m A H z t h)

/-- The observed Fréchet Taylor polynomial is the sum of observed normalized
Fréchet coefficients. -/
theorem continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse_eq_sum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse
        φ N m A H z t h =
      ∑ n ∈ Finset.range N,
        continuousLinearMapFiniteParameterRealResolventFrechetTaylorLinearResponse
          φ n m A H z t h := by
  simp [continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse,
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum,
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorLinearResponse]

/-- Exact continuous-linear response form of the multivariable Fréchet Taylor
formula. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_add_linearResponse_eq_frechetTaylorPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    φ (continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h)) =
      continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse
          φ N m A H z t h +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse
          φ N m A H z t h := by
  rw [continuousLinearMapFiniteParameterRealResolventChart_add_eq_frechetTaylorPartialSum_add_remainder
    N m A H z t h hunit hsmall]
  simp [continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse,
    continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse]

/-- Dual-norm geometric bound for an observed true finite-parameter remainder. -/
theorem continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse_abs_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z q M : ℝ) (t h : Fin m → ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ ≤ q)
    (hnew : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h)‖ ≤ M) :
    |continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse
        φ N m A H z t h| ≤ ‖φ‖ * (q ^ N * M) := by
  calc
    |continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse
        φ N m A H z t h| =
      ‖φ (continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
        N m A H z t h)‖ := by
      simp [continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse]
    _ ≤ ‖φ‖ * ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
        N m A H z t h‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (q ^ N * M) :=
      mul_le_mul_of_nonneg_left
        (continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder_norm_le
          N m A H z q M t h hq hM hperturb hnew) (norm_nonneg φ)

/-- Simultaneous family of finite-parameter Taylor coefficient responses. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorLinearResponseFamily
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] ℝ)) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ι → ℝ :=
  fun i => continuousLinearMapFiniteParameterRealResolventFrechetTaylorLinearResponse
    (φ i) n m A H z t h

/-- Exact Fréchet Taylor formula simultaneously for a family of continuous
linear responses. -/
theorem continuousLinearMapFiniteParameterRealResolventChart_add_linearResponseFamily_eq
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] ℝ)) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    (fun i => φ i (continuousLinearMapFiniteParameterRealResolventChart m A H z (t + h))) =
      (fun i =>
        continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSumLinearResponse
            (φ i) N m A H z t h +
          continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainderLinearResponse
            (φ i) N m A H z t h) := by
  funext i
  exact continuousLinearMapFiniteParameterRealResolventChart_add_linearResponse_eq_frechetTaylorPartialSum_add_remainder
    (φ i) N m A H z t h hunit hsmall

/-- Basis-independent trace of a normalized finite-parameter Fréchet Taylor
coefficient. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
      n m A H z t h)

/-- Basis-independent trace of the finite Fréchet Taylor polynomial. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorTracePartialSum
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
      N m A H z t h)

/-- Basis-independent trace of the true finite-parameter remainder. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceRemainder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
      N m A H z t h)

/-- Exact basis-independent trace form of the multivariable Fréchet Taylor
formula. -/
theorem continuousLinearMapFiniteParameterRealResolventTraceResponse_add_eq_frechetTaylorTracePartialSum_add_remainder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H z t *
      continuousLinearMapFiniteParameterOperatorIncrement m H h‖ < 1) :
    continuousLinearMapRealResolventTraceResponse
        (continuousLinearMapFiniteParameterOperatorChart m A H (t + h)) z =
      continuousLinearMapFiniteParameterRealResolventFrechetTaylorTracePartialSum
          V N m A H z t h +
        continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceRemainder
          V N m A H z t h := by
  simpa [continuousLinearMapFiniteParameterRealResolventFrechetTaylorTracePartialSum,
    continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceRemainder,
    continuousLinearMapFiniteParameterRealResolventChart] using
    continuousLinearMapFiniteParameterRealResolventChart_add_linearResponse_eq_frechetTaylorPartialSum_add_remainder
      (continuousLinearMapTrace (V := V)) N m A H z t h hunit hsmall

/-- Finite basis-independent trace jet of normalized Fréchet Taylor
coefficients. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorTraceJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : Fin N → ℝ :=
  fun n => continuousLinearMapFiniteParameterRealResolventFrechetTaylorTraceCoefficient
    V n.1 m A H z t h

end MathlibAnalytic
end MGAP4D
