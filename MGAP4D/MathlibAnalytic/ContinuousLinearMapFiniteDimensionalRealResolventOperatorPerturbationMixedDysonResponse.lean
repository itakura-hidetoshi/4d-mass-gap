import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMixedDysonCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The mixed Dyson polynomial as a function of the resolvent operator itself. -/
def continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent :
    (n : ℕ) → {V : Type*} → [NormedAddCommGroup V] → [NormedSpace ℝ V] →
      (V →L[ℝ] V) → (Fin n → (V →L[ℝ] V)) → (V →L[ℝ] V)
  | 0, V, _, _, R, _ => R
  | n + 1, V, _, _, R, H =>
      ∑ i : Fin (n + 1),
        continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R
            (fun j => H (i.succAbove j)) *
          H i * R

@[simp]
theorem continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) (H : Fin 0 → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent 0 R H = R :=
  rfl

@[simp]
theorem continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin (n + 1) → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent (n + 1) R H =
      ∑ i : Fin (n + 1),
        continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R
            (fun j => H (i.succAbove j)) *
          H i * R :=
  rfl

/-- The operator coefficient is the mixed Dyson polynomial evaluated at the
actual real resolvent. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonCoefficient_eq_fromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z =
      continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n
        (continuousLinearMapRealResolvent A z) H := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [continuousLinearMapRealResolventOperatorMixedDysonCoefficient_succ,
        continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent_succ]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [ih]

/-- Every fixed mixed-direction Dyson polynomial is continuous in the
resolvent variable. -/
theorem continuous_continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (H : Fin n → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R H) := by
  induction n with
  | zero =>
      simpa [continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent] using
        (continuous_id : Continuous (fun R : V →L[ℝ] V => R))
  | succ n ih =>
      change Continuous (fun R : V →L[ℝ] V =>
        ∑ i : Fin (n + 1),
          continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R
              (fun j => H (i.succAbove j)) *
            H i * R)
      apply continuous_finset_sum
      intro i _hi
      exact
        ((ih (fun j => H (i.succAbove j))).mul continuous_const).mul continuous_id

/-- Convergence of resolvents transfers to every fixed mixed-direction Dyson
coefficient. -/
theorem tendsto_continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent
    {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} (n : ℕ) (H : Fin n → (V →L[ℝ] V))
    (R : α → (V →L[ℝ] V)) (R0 : V →L[ℝ] V)
    (hR : Tendsto R l (𝓝 R0)) :
    Tendsto (fun a =>
      continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n (R a) H) l
      (𝓝 (continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent n R0 H)) :=
  (continuous_continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent
    n H).continuousAt.tendsto.comp hR

/-- On the full diagonal of direction tuples, the mixed coefficient is exactly
the true one-variable iterated derivative of the operator resolvent line. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv_eq_mixedDysonDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t =
      continuousLinearMapRealResolventOperatorMixedDysonCoefficient n
        (A + t • H) (fun _ => H) z := by
  rw [continuousLinearMapRealResolventOperatorLine_iteratedDeriv
    A H z U M hU hM hunit hnorm n ht,
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient_const]

/-- An arbitrary continuous-linear observation of a mixed Dyson coefficient. -/
def continuousLinearMapRealResolventOperatorMixedDysonLinearResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) (z : ℝ) : W :=
  φ (continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z)

/-- Continuous-linear observation respects factorial diagonal recovery. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonLinearResponse_const
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonLinearResponse
        φ n A (fun _ => H) z =
      (n.factorial : ℝ) •
        φ (continuousLinearMapRealResolventOperatorDysonCoefficient n A H z) := by
  simp [continuousLinearMapRealResolventOperatorMixedDysonLinearResponse,
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient_const]

/-- Operator-norm control of every continuous-linear mixed response. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonLinearResponse_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n : ℕ)
    (A : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) (z : ℝ) :
    ‖continuousLinearMapRealResolventOperatorMixedDysonLinearResponse φ n A H z‖ ≤
      ‖φ‖ * ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z‖ :=
  φ.le_opNorm _

/-- A simultaneous family of continuous-linear mixed responses. -/
def continuousLinearMapRealResolventOperatorMixedDysonLinearResponseFamily
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] W)) (n : ℕ)
    (A : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) (z : ℝ) : ι → W :=
  fun i => continuousLinearMapRealResolventOperatorMixedDysonLinearResponse
    (φ i) n A H z

/-- Basis-independent trace of a mixed Dyson coefficient. -/
def continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A : V →L[ℝ] V)
    (H : Fin n → (V →L[ℝ] V)) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventOperatorMixedDysonCoefficient n A H z)

/-- Trace polarization recovers the factorial single-direction trace
coefficient on the diagonal. -/
theorem continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient_const
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient
        V n A (fun _ => H) z =
      (n.factorial : ℝ) *
        continuousLinearMapRealResolventOperatorDysonTraceCoefficient V n A H z := by
  simp [continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient,
    continuousLinearMapRealResolventOperatorDysonTraceCoefficient,
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient_const]

/-- The finite trace polarization jet through order `N - 1`. -/
def continuousLinearMapRealResolventOperatorMixedDysonTraceJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A : V →L[ℝ] V)
    (H : ∀ n : Fin N, Fin n.1 → (V →L[ℝ] V)) (z : ℝ) : Fin N → ℝ :=
  fun n => continuousLinearMapRealResolventOperatorMixedDysonTraceCoefficient
    V n.1 A (H n) z

end MathlibAnalytic
end MGAP4D
