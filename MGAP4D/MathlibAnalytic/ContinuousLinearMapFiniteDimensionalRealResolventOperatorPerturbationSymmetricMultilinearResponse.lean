import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearDerivative
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventTraceResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Postcompose the symmetric operator derivative with an arbitrary continuous
linear observation.  The result remains a continuous multilinear map in all
perturbation directions. -/
def continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (z : ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) W :=
  φ.compContinuousMultilinearMap
    (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z)

@[simp]
theorem continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (z : ℝ) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z H =
      φ (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z H) :=
  rfl

/-- Every continuous-linear response inherits the full permutation symmetry. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse_apply_perm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (z : ℝ) (τ : Equiv.Perm (Fin n))
    (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z (fun i => H (τ i)) =
      continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z H := by
  change φ
      (continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent A z) (fun i => H (τ i))) =
    φ
      (continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent A z) H)
  rw [continuousLinearMapRealResolventSymmetricDysonMultilinear_apply_perm]

/-- The operator norm of the response map controls every mixed-direction
response by the product of the direction norms. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (z : ℝ) (H : Fin n → (V →L[ℝ] V)) :
    ‖continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z H‖ ≤
      ‖continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z‖ * ∏ i : Fin n, ‖H i‖ :=
  (continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
    φ n A z).le_opNorm H

/-- On the full diagonal, every continuous-linear response recovers `n!`
times the corresponding one-direction Dyson response. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse_const
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
        φ n A z (fun _ => H) =
      (n.factorial : ℝ) •
        φ (continuousLinearMapRealResolventOperatorDysonCoefficient n A H z) := by
  change φ
      (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (fun _ => H)) = _
  rw [continuousLinearMapRealResolventOperatorSymmetricDerivative_const]
  simp

/-- Basis-independent trace of the symmetric operator derivative, bundled as
a continuous multilinear scalar-valued map. -/
def continuousLinearMapRealResolventOperatorSymmetricTraceDerivative
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (V →L[ℝ] V)) ℝ :=
  continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse
    (continuousLinearMapTrace (V := V)) n A z

@[simp]
theorem continuousLinearMapRealResolventOperatorSymmetricTraceDerivative_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V) (z : ℝ)
    (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorSymmetricTraceDerivative V n A z H =
      continuousLinearMapTrace
        (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z H) :=
  rfl

/-- Trace polarization recovers `n!` times the ordinary Dyson trace
coefficient on the full diagonal. -/
theorem continuousLinearMapRealResolventOperatorSymmetricTraceDerivative_const
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorSymmetricTraceDerivative V n A z
        (fun _ => H) =
      (n.factorial : ℝ) *
        continuousLinearMapRealResolventOperatorDysonTraceCoefficient V n A H z := by
  simpa [continuousLinearMapRealResolventOperatorSymmetricTraceDerivative,
    continuousLinearMapRealResolventOperatorDysonTraceCoefficient] using
    continuousLinearMapRealResolventOperatorSymmetricDerivativeLinearResponse_const
      (continuousLinearMapTrace (V := V)) n A H z

end MathlibAnalytic
end MGAP4D
