import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterArbitraryDirectionFrechet
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventTraceResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- An arbitrary Banach-valued continuous-linear observation of the genuine
joint spectral/operator Fréchet derivative carrier. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) W :=
  φ.compContinuousMultilinearMap
    (continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
      m n A H z s t)

@[simp]
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t u =
      φ (continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t u) :=
  rfl

/-- At a joint resolvent point, every response is the observation of the true
joint `iteratedFDeriv`. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_eq_iteratedFDeriv
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t =
      φ.compContinuousMultilinearMap
        (iteratedFDeriv ℝ n
          (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
          (continuousLinearMapJointSpectralOperatorParameter m s t)) := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_eq_iteratedFDeriv
      m n A H z s t hunit]

/-- Every arbitrary-direction response is permutation invariant. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_perm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) (σ : Equiv.Perm (Fin n)) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t (fun i => u (σ i)) =
      continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t u := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_apply,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_apply,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_perm]

/-- The response-map operator norm controls every arbitrary joint direction
tuple by the product of its direction norms. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t u‖ ≤
      ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
        φ m n A H z s t‖ * ∏ i : Fin n, ‖u i‖ :=
  (continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
    φ m n A H z s t).le_opNorm u

/-- A family of arbitrary Banach-valued joint Fréchet responses. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponseFamily
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] W)) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ι → ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) W :=
  fun i =>
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
      (φ i) m n A H z s t

/-- A finite jet of arbitrary Banach-valued joint Fréchet response carriers. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponseJet
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m N : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) W :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
      φ m n.1 A H z s t

/-- Basis-independent trace of the genuine arbitrary-direction joint Fréchet
derivative carrier. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) ℝ :=
  continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
    (continuousLinearMapTrace (V := V)) m n A H z s t

@[simp]
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
        V m n A H z s t u =
      continuousLinearMapTrace
        (continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
          m n A H z s t u) :=
  rfl

/-- A finite basis-independent trace jet of genuine joint Fréchet carriers. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivativeJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m N : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) ℝ :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
      V m n.1 A H z s t

end MathlibAnalytic
end MGAP4D
