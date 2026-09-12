import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterDerivative
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- An arbitrary continuous-linear observable composed with the pulled-back
finite-parameter symmetric derivative. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin m → ℝ)) W :=
  φ.compContinuousMultilinearMap
    (continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
      m n A H z)

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z u =
      φ (continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
        m n A H z u) :=
  rfl

/-- Every continuous-linear response inherits permutation invariance in the
parameter directions. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_perm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) (σ : Equiv.Perm (Fin n)) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z (fun i => u (σ i)) =
      continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z u := by
  rw [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply,
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply,
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_perm]

/-- The response-map operator norm controls every mixed parameter-direction
response by the product of the parameter-direction norms. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) :
    ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z u‖ ≤
      ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z‖ * ∏ i : Fin n, ‖u i‖ :=
  (continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
    φ m n A H z).le_opNorm u

/-- Coordinate response mixed partials, with repeated coordinates allowed. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_coordinate
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (κ : Fin n → Fin m) :
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z (fun i => Pi.single (κ i) 1) =
      φ (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
        (fun i => H (κ i))) := by
  rw [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply,
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_coordinate]

/-- A family of arbitrary continuous-linear finite-parameter responses. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponseFamily
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] W)) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ι → ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin m → ℝ)) W :=
  fun i =>
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
      (φ i) m n A H z

/-- Basis-independent trace of the pulled-back finite-parameter symmetric
resolvent derivative. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (Fin m → ℝ)) ℝ :=
  continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
    (continuousLinearMapTrace (V := V)) m n A H z

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (u : Fin n → (Fin m → ℝ)) :
    continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative
        V m n A H z u =
      continuousLinearMapTrace
        (continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
          m n A H z u) :=
  rfl

/-- Coordinate trace mixed partials, including repeated-coordinate cases. -/
theorem continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative_coordinate
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (κ : Fin n → Fin m) :
    continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative
        V m n A H z (fun i => Pi.single (κ i) 1) =
      continuousLinearMapTrace
        (continuousLinearMapRealResolventOperatorSymmetricDerivative n A z
          (fun i => H (κ i))) := by
  rw [continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative_apply,
    continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_coordinate]

/-- The finite trace mixed-partial jet through order `N - 1`. -/
def continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivativeJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m N : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ (fun _ : Fin n.1 => (Fin m → ℝ)) ℝ :=
  fun n => continuousLinearMapFiniteParameterRealResolventSymmetricTraceDerivative
    V m n.1 A H z

end MathlibAnalytic
end MGAP4D
