import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The symmetric real-resolvent derivative pulled back from operator space to
a finite-dimensional parameter space. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin m → ℝ)) (V →L[ℝ] V) :=
  (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z).compContinuousLinearMap
    (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis m H)

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z u =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (continuousLinearMapFiniteParameterDirectionTuple m n H u) := by
  rfl

/-- Coordinate mixed derivatives are obtained by inserting the corresponding
operator direction at each slot; repeated coordinates are allowed. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_coordinate
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (kappa : Fin n → Fin m) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z (fun i => Pi.single (kappa i) 1) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (fun i => H (kappa i)) := by
  rw [continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply,
    continuousLinearMapFiniteParameterDirectionTuple_coordinate]

/-- Permuting the parameter directions does not change the pulled-back
symmetric derivative. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_perm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) (sigma : Equiv.Perm (Fin n)) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z (fun i => u (sigma i)) =
      continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z u := by
  change
    continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent A z)
        (fun i => continuousLinearMapFiniteParameterDirectionTuple m n H u (sigma i)) =
      continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent A z)
        (continuousLinearMapFiniteParameterDirectionTuple m n H u)
  exact continuousLinearMapRealResolventSymmetricDysonMultilinear_apply_perm
    n (continuousLinearMapRealResolvent A z) sigma
      (continuousLinearMapFiniteParameterDirectionTuple m n H u)

/-- The full diagonal in parameter space recovers the operator-variable
symmetric derivative in the synthesized direction. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin m → ℝ) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z (fun _ => u) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis m H u) := by
  rfl

/-- The finite parameter mixed-derivative jet through order `N - 1`. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m N : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ (fun _ : Fin n.1 => (Fin m → ℝ)) (V →L[ℝ] V) :=
  fun n => continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
    m n.1 A H z

end MathlibAnalytic
end MGAP4D
