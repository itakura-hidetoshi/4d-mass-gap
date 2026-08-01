import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDirectionalDerivative
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventLinearResponseCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventTraceResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The algebraic Dyson coefficient as a function of a resolvent and a direction. -/
def continuousLinearMapRealResolventDysonCoefficientFromPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R H : V →L[ℝ] V) : V →L[ℝ] V :=
  (R * H) ^ n * R

/-- Dyson coefficients are jointly continuous in the resolvent and direction. -/
theorem continuous_continuousLinearMapRealResolventDysonCoefficientFromPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    Continuous (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) =>
      continuousLinearMapRealResolventDysonCoefficientFromPair n p.1 p.2) := by
  simpa [continuousLinearMapRealResolventDysonCoefficientFromPair] using
    (((continuous_fst.mul continuous_snd).pow n).mul continuous_fst)

/-- Joint convergence of resolvents and directions transfers to every fixed
Dyson coefficient. -/
theorem tendsto_continuousLinearMapRealResolventDysonCoefficientFromPair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α : Type*} {l : Filter α}
    (n : ℕ) (R H : α → (V →L[ℝ] V)) (R0 H0 : V →L[ℝ] V)
    (hR : Tendsto R l (𝓝 R0)) (hH : Tendsto H l (𝓝 H0)) :
    Tendsto (fun a => continuousLinearMapRealResolventDysonCoefficientFromPair
      n (R a) (H a)) l
      (𝓝 (continuousLinearMapRealResolventDysonCoefficientFromPair n R0 H0)) := by
  simpa [continuousLinearMapRealResolventDysonCoefficientFromPair] using
    ((hR.mul hH).pow n).mul hR

/-- A continuous-linear scalar observation of the `n`-th operator Dyson
coefficient. -/
def continuousLinearMapRealResolventOperatorDysonLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (n : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  φ (continuousLinearMapRealResolventOperatorDysonCoefficient n A H z)

/-- A continuous-linear observation of the finite Dyson partial sum. -/
def continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  φ (continuousLinearMapRealResolventOperatorDysonPartialSum N A H z)

/-- A continuous-linear observation of the exact Dyson remainder. -/
def continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  φ (continuousLinearMapRealResolventOperatorDysonRemainder N A H z)

/-- The observed partial sum is the sum of the observed coefficients. -/
theorem continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse_eq_sum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse
        φ N A H z =
      ∑ n ∈ Finset.range N,
        continuousLinearMapRealResolventOperatorDysonLinearResponse φ n A H z := by
  simp [continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse,
    continuousLinearMapRealResolventOperatorDysonPartialSum,
    continuousLinearMapRealResolventOperatorDysonLinearResponse]

/-- Exact continuous-linear response Dyson expansion. -/
theorem continuousLinearMapRealResolvent_add_linearResponse_eq_dysonPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    φ (continuousLinearMapRealResolvent (A + H) z) =
      continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse φ N A H z +
        continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse φ N A H z := by
  rw [continuousLinearMapRealResolvent_add_eq_operatorDysonPartialSum_add_remainder
    N A H z hA hsmall]
  simp [continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse,
    continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse]

/-- Exact observed approximation defect. -/
theorem continuousLinearMapRealResolvent_add_linearResponse_sub_dysonPartialSum_eq_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    φ (continuousLinearMapRealResolvent (A + H) z) -
        continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse φ N A H z =
      continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse φ N A H z := by
  rw [continuousLinearMapRealResolvent_add_linearResponse_eq_dysonPartialSum_add_remainder
    φ N A H z hA hsmall]
  ring

/-- Dual-norm geometric bound for an observed exact Dyson remainder. -/
theorem continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse_abs_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ) (N : ℕ)
    (A H : V →L[ℝ] V) (z q M : ℝ)
    (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapRealResolvent A z * H‖ ≤ q)
    (hnew : ‖continuousLinearMapRealResolvent (A + H) z‖ ≤ M) :
    |continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse
        φ N A H z| ≤ ‖φ‖ * (q ^ N * M) := by
  calc
    |continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse φ N A H z| =
        ‖φ (continuousLinearMapRealResolventOperatorDysonRemainder N A H z)‖ := by
      simp [continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse]
    _ ≤ ‖φ‖ * ‖continuousLinearMapRealResolventOperatorDysonRemainder N A H z‖ :=
      φ.le_opNorm _
    _ ≤ ‖φ‖ * (q ^ N * M) :=
      mul_le_mul_of_nonneg_left
        (continuousLinearMapRealResolventOperatorDysonRemainder_norm_le
          N A H z q M hq hM hperturb hnew) (norm_nonneg φ)

/-- A finite or arbitrary family of simultaneous Dyson coefficient responses. -/
def continuousLinearMapRealResolventOperatorDysonLinearResponseFamily
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] ℝ)) (n : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ) : ι → ℝ :=
  fun i => continuousLinearMapRealResolventOperatorDysonLinearResponse
    (φ i) n A H z

/-- The exact Dyson formula holds simultaneously for every response in a
family. -/
theorem continuousLinearMapRealResolvent_add_linearResponseFamily_eq
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : ι → ((V →L[ℝ] V) →L[ℝ] ℝ)) (N : ℕ)
    (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    (fun i => φ i (continuousLinearMapRealResolvent (A + H) z)) =
      (fun i =>
        continuousLinearMapRealResolventOperatorDysonPartialSumLinearResponse
          (φ i) N A H z +
        continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse
          (φ i) N A H z) := by
  funext i
  exact continuousLinearMapRealResolvent_add_linearResponse_eq_dysonPartialSum_add_remainder
    (φ i) N A H z hA hsmall

/-- Applying a continuous-linear response to the operator directional jet gives
the factorial Dyson response jet. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv_linearResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (φ : (V →L[ℝ] V) →L[ℝ] ℝ)
    (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    φ (iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t) =
      (n.factorial : ℝ) *
        continuousLinearMapRealResolventOperatorDysonLinearResponse
          φ n (A + t • H) H z := by
  rw [continuousLinearMapRealResolventOperatorLine_iteratedDeriv
    A H z U M hU hM hunit hnorm n ht]
  simp [continuousLinearMapRealResolventOperatorDysonLinearResponse]

/-- Basis-independent trace of an operator Dyson coefficient. -/
def continuousLinearMapRealResolventOperatorDysonTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventOperatorDysonCoefficient n A H z)

/-- Basis-independent trace of the finite Dyson partial sum. -/
def continuousLinearMapRealResolventOperatorDysonTracePartialSum
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventOperatorDysonPartialSum N A H z)

/-- Basis-independent trace of the exact Dyson remainder. -/
def continuousLinearMapRealResolventOperatorDysonTraceRemainder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventOperatorDysonRemainder N A H z)

/-- Exact basis-independent trace Dyson expansion. -/
theorem continuousLinearMapRealResolventTraceResponse_add_eq_dysonTracePartialSum_add_remainder
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    continuousLinearMapRealResolventTraceResponse (A + H) z =
      continuousLinearMapRealResolventOperatorDysonTracePartialSum V N A H z +
        continuousLinearMapRealResolventOperatorDysonTraceRemainder V N A H z := by
  simpa [continuousLinearMapRealResolventTraceResponse,
    continuousLinearMapRealResolventOperatorDysonTracePartialSum,
    continuousLinearMapRealResolventOperatorDysonTraceRemainder] using
    continuousLinearMapRealResolvent_add_linearResponse_eq_dysonPartialSum_add_remainder
      (continuousLinearMapTrace (V := V)) N A H z hA hsmall

/-- Explicit trace-norm bound for the exact Dyson remainder. -/
theorem continuousLinearMapRealResolventOperatorDysonTraceRemainder_abs_le
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N : ℕ) (A H : V →L[ℝ] V) (z q M : ℝ)
    (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapRealResolvent A z * H‖ ≤ q)
    (hnew : ‖continuousLinearMapRealResolvent (A + H) z‖ ≤ M) :
    |continuousLinearMapRealResolventOperatorDysonTraceRemainder V N A H z| ≤
      ‖continuousLinearMapTrace (V := V)‖ * (q ^ N * M) := by
  simpa [continuousLinearMapRealResolventOperatorDysonTraceRemainder,
    continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse] using
    continuousLinearMapRealResolventOperatorDysonRemainderLinearResponse_abs_le
      (continuousLinearMapTrace (V := V)) N A H z q M hq hM hperturb hnew

/-- Trace of the operator directional derivative jet equals the factorial trace
Dyson jet. -/
theorem continuousLinearMapRealResolventOperatorLine_iteratedDeriv_trace
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A H : V →L[ℝ] V) (z : ℝ)
    (U : Set ℝ) (M : ℝ) (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ t ∈ U, IsUnit (continuousLinearMapRealShift (A + t • H) z))
    (hnorm : ∀ t ∈ U,
      ‖continuousLinearMapRealResolventOperatorLine A H z t‖ ≤ M)
    (n : ℕ) {t : ℝ} (ht : t ∈ U) :
    continuousLinearMapTrace
        (iteratedDeriv n (continuousLinearMapRealResolventOperatorLine A H z) t) =
      (n.factorial : ℝ) *
        continuousLinearMapRealResolventOperatorDysonTraceCoefficient
          V n (A + t • H) H z := by
  simpa [continuousLinearMapRealResolventOperatorDysonTraceCoefficient,
    continuousLinearMapRealResolventOperatorDysonLinearResponse] using
    continuousLinearMapRealResolventOperatorLine_iteratedDeriv_linearResponse
      (continuousLinearMapTrace (V := V)) A H z U M hU hM hunit hnorm n ht

end MathlibAnalytic
end MGAP4D
