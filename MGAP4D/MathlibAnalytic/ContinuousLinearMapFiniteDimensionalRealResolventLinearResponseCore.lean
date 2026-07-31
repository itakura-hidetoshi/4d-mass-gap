import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventNewtonHermiteExact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- A scalar spectral response obtained by applying a continuous linear
functional to a finite-dimensional real resolvent. -/
def continuousLinearMapRealResolventLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (phi : (V →L[ℝ] V) →L[ℝ] ℝ) (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  phi (continuousLinearMapRealResolvent A z)

/-- The normalized multipoint Hermite response of an arbitrary continuous
linear spectral observable. -/
def continuousLinearMapRealResolventHermiteResponseObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (R : Fin (order + 1) → (V →L[ℝ] V)) : ℝ :=
  phi (continuousLinearMapRealResolventHermiteObservable order R)

/-- Multipoint Hermite response coefficient of a true finite-dimensional real
resolvent. -/
def continuousLinearMapRealResolventHermiteResponseCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (order + 1) → ℝ) : ℝ :=
  phi (continuousLinearMapRealResolventHermiteCoefficient order A nodes)

/-- The finite Hermite response jet through a fixed order. -/
def continuousLinearMapRealResolventHermiteResponseJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (R : Fin (order + 1) → (V →L[ℝ] V)) : Fin (order + 1) → ℝ :=
  fun n => phi (continuousLinearMapRealResolventHermiteJet order R n)

/-- Hermite response observables are continuous in the complete finite
operator tuple. -/
theorem continuous_continuousLinearMapRealResolventHermiteResponseObservable
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ) :
    Continuous
      (continuousLinearMapRealResolventHermiteResponseObservable order phi) := by
  exact phi.continuous.comp
    (continuous_continuousLinearMapRealResolventHermiteObservable order)

/-- Finite Hermite response jets are continuous in product supremum norm. -/
theorem continuous_continuousLinearMapRealResolventHermiteResponseJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ) :
    Continuous
      (continuousLinearMapRealResolventHermiteResponseJet order phi) := by
  unfold continuousLinearMapRealResolventHermiteResponseJet
  apply continuous_pi
  intro n
  exact phi.continuous.comp
    ((continuous_apply n).comp
      (continuous_continuousLinearMapRealResolventHermiteJet order))

/-- Dual-norm control of a normalized Hermite response. -/
theorem abs_continuousLinearMapRealResolventHermiteResponseObservable_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (order : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (R : Fin (order + 1) → (V →L[ℝ] V)) {M : ℝ}
    (hM : 0 ≤ M) (hR : ∀ i, ‖R i‖ ≤ M) :
    |continuousLinearMapRealResolventHermiteResponseObservable order phi R| ≤
      ‖phi‖ * M ^ (order + 1) := by
  unfold continuousLinearMapRealResolventHermiteResponseObservable
  have hphi := phi.le_opNorm
    (continuousLinearMapRealResolventHermiteObservable order R)
  rw [Real.norm_eq_abs] at hphi
  exact hphi.trans (mul_le_mul_of_nonneg_left
    (continuousLinearMapRealResolventHermiteObservable_norm_le order R hM hR)
    (norm_nonneg phi))

/-- On the full diagonal, factorial scaling identifies the Hermite response
with the response of the true iterated resolvent derivative. -/
theorem factorial_mul_continuousLinearMapRealResolventHermiteResponseCoefficient_const_eq_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (phi : (V →L[ℝ] V) →L[ℝ] ℝ) (A : V →L[ℝ] V)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (order : ℕ) {z : ℝ} (hz : z ∈ U) :
    (order.factorial : ℝ) *
        continuousLinearMapRealResolventHermiteResponseCoefficient
          order phi A (fun _ => z) =
      phi (iteratedDeriv order (continuousLinearMapRealResolvent A) z) := by
  have h := congrArg phi
    (factorial_smul_continuousLinearMapRealResolventHermiteCoefficient_const_eq_iteratedDeriv
      A U M hU hM hunit hnorm order hz)
  simpa [continuousLinearMapRealResolventHermiteResponseCoefficient] using h

/-- Scalar Newton-Hermite interpolant associated with a continuous linear
spectral observable. -/
def continuousLinearMapRealResolventNewtonHermiteResponseInterpolant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : ℝ :=
  phi (continuousLinearMapRealResolventNewtonHermiteInterpolant degree A nodes z)

/-- Scalar exact Newton-Hermite remainder associated with a continuous linear
spectral observable. -/
def continuousLinearMapRealResolventNewtonHermiteResponseRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : ℝ :=
  phi (continuousLinearMapRealResolventNewtonHermiteRemainder degree A nodes z)

/-- Exact scalar Newton-Hermite interpolation identity. -/
theorem continuousLinearMapRealResolventLinearResponse_eq_newtonHermiteResponseInterpolant_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hz : IsUnit (continuousLinearMapRealShift A z)) :
    continuousLinearMapRealResolventLinearResponse phi A z =
      continuousLinearMapRealResolventNewtonHermiteResponseInterpolant
          degree phi A nodes z +
        continuousLinearMapRealResolventNewtonHermiteResponseRemainder
          degree phi A nodes z := by
  have h := congrArg phi
    (continuousLinearMapRealResolvent_eq_newtonHermiteInterpolant_add_remainder
      degree A nodes z hnodes hz)
  simpa [continuousLinearMapRealResolventLinearResponse,
    continuousLinearMapRealResolventNewtonHermiteResponseInterpolant,
    continuousLinearMapRealResolventNewtonHermiteResponseRemainder] using h

/-- Every scalar response interpolant agrees with the response at all listed
nodes, including repeated nodes. -/
theorem continuousLinearMapRealResolventNewtonHermiteResponseInterpolant_eq_at_node
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (degree + 1) → ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (i : Fin (degree + 1)) :
    continuousLinearMapRealResolventNewtonHermiteResponseInterpolant
        degree phi A nodes (nodes i) =
      continuousLinearMapRealResolventLinearResponse phi A (nodes i) := by
  have h := congrArg phi
    (continuousLinearMapRealResolventNewtonHermiteInterpolant_eq_at_node
      degree A nodes hnodes i)
  simpa [continuousLinearMapRealResolventLinearResponse,
    continuousLinearMapRealResolventNewtonHermiteResponseInterpolant] using h

/-- Explicit dual-norm interpolation-error bound. -/
theorem abs_continuousLinearMapRealResolventLinearResponse_sub_newtonHermiteResponseInterpolant_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (phi : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A : V →L[ℝ] V) (nodes : Fin (degree + 1) → ℝ)
    (z M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hnodesUnit : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hzUnit : IsUnit (continuousLinearMapRealShift A z))
    (hnodesDist : ∀ i, |z - nodes i| ≤ D)
    (hnodesNorm : ∀ i, ‖continuousLinearMapRealResolvent A (nodes i)‖ ≤ M)
    (hzNorm : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    |continuousLinearMapRealResolventLinearResponse phi A z -
        continuousLinearMapRealResolventNewtonHermiteResponseInterpolant
          degree phi A nodes z| ≤
      ‖phi‖ * (D ^ (degree + 1) * M ^ (degree + 2)) := by
  have hop :=
    continuousLinearMapRealResolvent_sub_newtonHermiteInterpolant_norm_le
      degree A nodes z M D hM hD hnodesUnit hzUnit
      hnodesDist hnodesNorm hzNorm
  have hphi := phi.le_opNorm
    (continuousLinearMapRealResolvent A z -
      continuousLinearMapRealResolventNewtonHermiteInterpolant degree A nodes z)
  rw [Real.norm_eq_abs] at hphi
  calc
    |continuousLinearMapRealResolventLinearResponse phi A z -
        continuousLinearMapRealResolventNewtonHermiteResponseInterpolant
          degree phi A nodes z| =
        |phi (continuousLinearMapRealResolvent A z -
          continuousLinearMapRealResolventNewtonHermiteInterpolant
            degree A nodes z)| := by
          simp [continuousLinearMapRealResolventLinearResponse,
            continuousLinearMapRealResolventNewtonHermiteResponseInterpolant]
    _ ≤ ‖phi‖ * ‖continuousLinearMapRealResolvent A z -
          continuousLinearMapRealResolventNewtonHermiteInterpolant
            degree A nodes z‖ := hphi
    _ ≤ ‖phi‖ * (D ^ (degree + 1) * M ^ (degree + 2)) :=
      mul_le_mul_of_nonneg_left hop (norm_nonneg phi)

end MathlibAnalytic
end MGAP4D
