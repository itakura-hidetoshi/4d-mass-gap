import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterFrechet
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterFrechetTaylor
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring Topology

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Joint parameters add componentwise. -/
theorem continuousLinearMapJointSpectralOperatorParameter_add
    (m : ℕ) (s ds : ℝ) (t h : Fin m → ℝ) :
    continuousLinearMapJointSpectralOperatorParameter m s t +
        continuousLinearMapJointSpectralOperatorParameter m ds h =
      continuousLinearMapJointSpectralOperatorParameter m (s + ds) (t + h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Joint parameters subtract componentwise. -/
theorem continuousLinearMapJointSpectralOperatorParameter_sub
    (m : ℕ) (s₀ s₁ : ℝ) (t₀ t₁ : Fin m → ℝ) :
    continuousLinearMapJointSpectralOperatorParameter m s₁ t₁ -
        continuousLinearMapJointSpectralOperatorParameter m s₀ t₀ =
      continuousLinearMapJointSpectralOperatorParameter m (s₁ - s₀) (t₁ - t₀) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- A joint spectral/operator increment synthesizes to the operator increment
minus the spectral increment times the identity. -/
theorem continuousLinearMapJointSpectralOperatorIncrement_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (ds : ℝ)
    (h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterOperatorIncrement (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m ds h) =
      continuousLinearMapFiniteParameterOperatorIncrement m H h -
        ds • (1 : V →L[ℝ] V) := by
  exact continuousLinearMapJointSpectralOperatorDirectionSynthesis_apply
    m H ds h

/-- The `n`-th joint spectral/operator Taylor-Dyson coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
    n (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h)

/-- The joint Taylor-Dyson polynomial through degree `N-1`. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventTaylorDysonPartialSum
    N (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h)

/-- The exact joint finite-order Taylor-Dyson remainder. -/
def continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder
    N (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h)

/-- The normalized diagonal genuine joint Fréchet Taylor coefficient. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
    n (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h)

/-- The genuine joint Fréchet Taylor polynomial through degree `N-1`. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum
    N (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h)

/-- At a joint resolvent point, the normalized genuine Fréchet coefficient is
exactly the joint Taylor-Dyson coefficient. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient_eq_taylorDyson
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient
        n m A H z s ds t h =
      continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient
        n m A H z s ds t h := by
  have hunit' : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart (m + 1) A
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t)) z) := by
    simpa [continuousLinearMapJointSpectralOperatorOperatorChart_eq,
      continuousLinearMapRealShift] using hunit
  exact continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient_eq_taylorDysonCoefficient
    n (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h) hunit'

/-- The joint genuine Fréchet Taylor polynomial equals the joint Taylor-Dyson
polynomial at every joint resolvent point. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum_eq_taylorDyson
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
        N m A H z s ds t h =
      continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonPartialSum
        N m A H z s ds t h := by
  unfold continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
  unfold continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonPartialSum
  apply continuousLinearMapFiniteParameterRealResolventFrechetTaylorPartialSum_eq_taylorDysonPartialSum
  simpa [continuousLinearMapJointSpectralOperatorOperatorChart_eq,
    continuousLinearMapRealShift] using hunit

/-- Exact joint Fréchet Taylor formula for simultaneous spectral and operator
increments. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_add_eq_frechetTaylor_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
        (z + s) t * (continuousLinearMapFiniteParameterOperatorIncrement m H h -
          ds • (1 : V →L[ℝ] V))‖ < 1) :
    continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
        (continuousLinearMapJointSpectralOperatorParameter m (s + ds) (t + h)) =
      continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
          N m A H z s ds t h +
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
          N m A H z s ds t h := by
  have hunit' : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart (m + 1) A
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t)) z) := by
    simpa [continuousLinearMapJointSpectralOperatorOperatorChart_eq,
      continuousLinearMapRealShift] using hunit
  have hsmall' : ‖continuousLinearMapFiniteParameterRealResolventChart (m + 1) A
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
      (continuousLinearMapJointSpectralOperatorParameter m s t) *
      continuousLinearMapFiniteParameterOperatorIncrement (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m ds h)‖ < 1 := by
    simpa [continuousLinearMapJointSpectralOperatorRealResolventChart_apply,
      continuousLinearMapJointSpectralOperatorIncrement_eq] using hsmall
  have h :=
    continuousLinearMapFiniteParameterRealResolventChart_add_eq_frechetTaylorPartialSum_add_remainder
      N (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
      (continuousLinearMapJointSpectralOperatorParameter m s t)
      (continuousLinearMapJointSpectralOperatorParameter m ds h) hunit' hsmall'
  rw [continuousLinearMapJointSpectralOperatorParameter_add] at h
  exact h

/-- Endpoint form of the exact joint Fréchet Taylor formula. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_eq_frechetTaylor_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s₀ s₁ : ℝ) (t₀ t₁ : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t₀) (z + s₀)))
    (hsmall : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
        (z + s₀) t₀ * (continuousLinearMapFiniteParameterOperatorIncrement m H (t₁ - t₀) -
          (s₁ - s₀) • (1 : V →L[ℝ] V))‖ < 1) :
    continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
        (continuousLinearMapJointSpectralOperatorParameter m s₁ t₁) =
      continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorPartialSum
          N m A H z s₀ (s₁ - s₀) t₀ (t₁ - t₀) +
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
          N m A H z s₀ (s₁ - s₀) t₀ (t₁ - t₀) := by
  have hs : s₀ + (s₁ - s₀) = s₁ := by ring
  have ht : t₀ + (t₁ - t₀) = t₁ := by abel
  simpa [hs, ht] using
    continuousLinearMapJointSpectralOperatorRealResolventChart_add_eq_frechetTaylor_add_remainder
      N m A H z s₀ (s₁ - s₀) t₀ (t₁ - t₀) hunit hsmall

/-- Geometric norm control of the exact joint Taylor-Dyson remainder. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds q M : ℝ) (t h : Fin m → ℝ) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
      (z + s) t * (continuousLinearMapFiniteParameterOperatorIncrement m H h -
        ds • (1 : V →L[ℝ] V))‖ ≤ q)
    (hnew : ‖continuousLinearMapFiniteParameterRealResolventChart m A H
      (z + s + ds) (t + h)‖ ≤ M) :
    ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonRemainder
        N m A H z s ds t h‖ ≤ q ^ N * M := by
  apply continuousLinearMapFiniteParameterRealResolventTaylorDysonRemainder_norm_le
    N (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
    z q M (continuousLinearMapJointSpectralOperatorParameter m s t)
    (continuousLinearMapJointSpectralOperatorParameter m ds h) hq hM
  · simpa [continuousLinearMapJointSpectralOperatorRealResolventChart_apply,
      continuousLinearMapJointSpectralOperatorIncrement_eq] using hperturb
  · rw [continuousLinearMapJointSpectralOperatorParameter_add]
    simpa [continuousLinearMapJointSpectralOperatorRealResolventChart_apply,
      add_assoc] using hnew

/-- Finite jet of normalized joint Fréchet Taylor coefficients. -/
def continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s ds : ℝ) (t h : Fin m → ℝ) : Fin N → (V →L[ℝ] V) :=
  fun n => continuousLinearMapJointSpectralOperatorRealResolventFrechetTaylorCoefficient
    n.1 m A H z s ds t h

end MathlibAnalytic
end MGAP4D
