import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterZero
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterFrechetTaylorDyson
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterObservable
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Arbitrary Banach-valued observation of a normalized joint genuine Fréchet
Taylor coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient
    n m A H z s ds t h)

/-- Arbitrary Banach-valued observation of a joint Taylor-Dyson coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient
    n m A H z s ds t h)

/-- Arbitrary Banach-valued observation of the joint genuine Fréchet Taylor
polynomial. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSumResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
    N m A H z s ds t h)

/-- Arbitrary Banach-valued observation of the exact joint remainder. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
    N m A H z s ds t h)

/-- Observed normalized joint Fréchet and Taylor-Dyson coefficients agree at a
joint resolvent point. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse_eq_taylorDyson
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse
        φ n m A H z s ds t h =
      continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
        φ n m A H z s ds t h := by
  simp [continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient_eq_taylorDyson
      n m A H z s ds t h hunit]

/-- Exact arbitrary Banach-valued response form of the joint Fréchet Taylor
formula. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_add_response_eq_frechetTaylor_add_remainder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
        (z + s) t * (continuousLinearMapFiniteParameterOperatorIncrement m H h -
          ds • (1 : V →L[ℝ] V))‖ < 1) :
    φ (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
        (continuousLinearMapJointSpectralOperatorParameter m (s + ds) (t + h))) =
      continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSumResponse
          φ N m A H z s ds t h +
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse
          φ N m A H z s ds t h := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventChart_add_eq_frechetTaylor_add_remainder
    N m A H z s ds t h hunit hsmall]
  simp [continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSumResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse]

/-- Dual-norm geometric bound for an arbitrary observed joint remainder. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds q M : ℝ) (t h : Fin m → ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
      (z + s) t * (continuousLinearMapFiniteParameterOperatorIncrement m H h -
        ds • (1 : V →L[ℝ] V))‖ ≤ q)
    (hnew : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
      (z + s + ds) (t + h)‖ ≤ M) :
    ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse
        φ N m A H z s ds t h‖ ≤ ‖φ‖ * (q ^ N * M) := by
  calc
    ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainderResponse
        φ N m A H z s ds t h‖ ≤
      ‖φ‖ * ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
        N m A H z s ds t h‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (q ^ N * M) := mul_le_mul_of_nonneg_left
      (continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder_norm_le
        N m A H z s ds q M t h hq hM hperturb hnew) (norm_nonneg φ)

/-- Finite Banach-valued joint Fréchet Taylor response jet. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponseJet
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : Fin N → W :=
  fun n => continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse
    φ n.1 m A H z s ds t h

/-- Basis-independent trace of a normalized joint Fréchet Taylor coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorResponse
    (continuousLinearMapTrace (V := V)) n m A H z s ds t h

/-- Basis-independent trace of a joint Taylor-Dyson coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
    (continuousLinearMapTrace (V := V)) n m A H z s ds t h

/-- Finite basis-independent joint trace jet. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorTraceJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : Fin N → ℝ :=
  fun n => continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorTraceCoefficient
    V n.1 m A H z s ds t h

end MathlibAnalytic
end MGAP4D
