import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMultilinearDysonCarrier
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMixedDysonResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- An arbitrary continuous-linear observable composed with the genuine
continuous multilinear mixed Dyson carrier. -/
def continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ) (A : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) W :=
  φ.compContinuousMultilinearMap
    (continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearMap
      n A z M hM hR)

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z M : ℝ)
    (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
        φ n A z M hM hR H =
      continuousLinearMapRealResolventOperatorMixedDysonLinearResponse
        φ n A H z := by
  simp [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse,
    continuousLinearMapRealResolventOperatorMixedDysonLinearResponse]

/-- Every continuous-linear response recovers the factorial one-direction
Dyson response on the full diagonal. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse_const
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ) (A H : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
        φ n A z M hM hR (fun _ => H) =
      (n.factorial : ℝ) •
        φ (continuousLinearMapRealResolventOperatorDysonCoefficient n A H z) := by
  rw [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse_apply,
    continuousLinearMapRealResolventOperatorMixedDysonLinearResponse_const]

/-- A simultaneous family of genuine continuous multilinear response
carriers. -/
def continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponseFamily
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] W)) (n : ℕ) (A : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ι → ContinuousMultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) W :=
  fun i => continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
    (φ i) n A z M hM hR

/-- Basis-independent trace composed with the genuine continuous multilinear
mixed Dyson carrier. -/
def continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => (V →L[ℝ] V)) ℝ :=
  continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
    (continuousLinearMapTrace (V := V)) n A z M hM hR

@[simp]
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z M : ℝ)
    (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace
        V n A z M hM hR H =
      continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient
        V n A H z := by
  change
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse
        (continuousLinearMapTrace (V := V)) n A z M hM hR H =
      continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient V n A H z
  rw [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearResponse_apply]
  rfl

/-- The trace carrier recovers the factorial one-direction trace coefficient
on the full diagonal. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace_const
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace
        V n A z M hM hR (fun _ => H) =
      (n.factorial : ℝ) *
        continuousLinearMapRealResolventOperatorDysonTraceCoefficient V n A H z := by
  rw [continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace_apply,
    continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient_const]

/-- The finite genuine continuous multilinear trace jet through order `N - 1`. -/
def continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTraceJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A : V →L[ℝ] V)
    (z M : ℝ) (hM : 0 ≤ M) (hR : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ (fun _ : Fin n.1 => (V →L[ℝ] V)) ℝ :=
  fun n => continuousLinearMapRealResolventOperatorMixedDysonContinuousMultilinearTrace
    V n.1 A z M hM hR

end MathlibAnalytic
end MGAP4D
