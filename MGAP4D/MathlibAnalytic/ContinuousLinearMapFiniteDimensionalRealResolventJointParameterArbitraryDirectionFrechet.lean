import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterFrechet
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The genuine joint spectral/operator Fréchet derivative carrier at an
arbitrary joint base point.  Its domain contains one spectral coordinate and
all finite operator coordinates. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) (V →L[ℝ] V) :=
  continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
    (m + 1) n (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) (z + s)

@[simp]
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t u =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
        (continuousLinearMapFiniteParameterDirectionTuple (m + 1) n
          (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u) :=
  rfl

/-- At every joint resolvent point, the bundled carrier is exactly the genuine
iterated Fréchet derivative of the joint chart. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_eq_iteratedFDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t =
      iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t) := by
  apply ContinuousMultilinearMap.ext
  intro u
  rw [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_apply,
    continuousLinearMapJointSpectralOperatorRealResolventChart_iteratedFDeriv_apply
      m A H z s t hunit n u]

/-- Evaluation form of the exact `iteratedFDeriv` identification. -/
theorem continuousLinearMapJointSpectralOperatorRealResolvent_iteratedFDeriv_eq_symmetricDerivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t) u =
      continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t u := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_eq_iteratedFDeriv
    m n A H z s t hunit]

/-- Arbitrary joint direction tuples are permutation invariant. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_perm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) (σ : Equiv.Perm (Fin n)) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t (fun i => u (σ i)) =
      continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t u := by
  exact continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_perm
    (m + 1) n (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) (z + s) u σ

/-- On the full diagonal, all joint slots synthesize the same operator
increment. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_const
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) (u : Fin (m + 1) → ℝ) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t (fun _ => u) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
        (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
          (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u) := by
  exact continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_const
    (m + 1) n (continuousLinearMapFiniteParameterOperatorChart m A H t)
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) (z + s) u

/-- The operator norm of the genuine joint derivative carrier controls every
arbitrary direction tuple. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (u : Fin n → (Fin (m + 1) → ℝ)) :
    ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t u‖ ≤
      ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t‖ * ∏ i : Fin n, ‖u i‖ :=
  (continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
    m n A H z s t).le_opNorm u

/-- A finite jet of genuine joint Fréchet derivative carriers at an arbitrary
joint base point. -/
def continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m N : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) (V →L[ℝ] V) :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
      m n.1 A H z s t

end MathlibAnalytic
end MGAP4D
