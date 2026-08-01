import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMultilinearDysonResponse
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Left multiplication by a fixed finite-dimensional operator, as a
continuous linear map on the operator algebra. -/
def continuousLinearMapOperatorLeftMultiplication
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  ((ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)) R) 1

/-- Right multiplication by a fixed finite-dimensional operator, as a
continuous linear map on the operator algebra. -/
def continuousLinearMapOperatorRightMultiplication
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) :=
  ((ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)) 1) R

@[simp]
theorem continuousLinearMapOperatorLeftMultiplication_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R H : V →L[ℝ] V) :
    continuousLinearMapOperatorLeftMultiplication R H = R * H := by
  simp [continuousLinearMapOperatorLeftMultiplication,
    ContinuousLinearMap.mulLeftRight_apply]

@[simp]
theorem continuousLinearMapOperatorRightMultiplication_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R H : V →L[ℝ] V) :
    continuousLinearMapOperatorRightMultiplication R H = H * R := by
  simp [continuousLinearMapOperatorRightMultiplication,
    ContinuousLinearMap.mulLeftRight_apply]

/-- The ordered Dyson formal multilinear series obtained by precomposing the
geometric series with left multiplication by `R` and postcomposing with right
multiplication by `R`. -/
def continuousLinearMapRealResolventDysonFormalMultilinearSeries
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : V →L[ℝ] V) :
    FormalMultilinearSeries ℝ (V →L[ℝ] V) (V →L[ℝ] V) :=
  (continuousLinearMapOperatorRightMultiplication R).compFormalMultilinearSeries
    ((formalMultilinearSeries_geometric ℝ (V →L[ℝ] V)).compContinuousLinearMap
      (continuousLinearMapOperatorLeftMultiplication R))

/-- The ordered coefficient represented by the explicit Dyson formal power
series. -/
def continuousLinearMapRealResolventOrderedDysonCoefficientFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) : V →L[ℝ] V :=
  (List.ofFn (fun i => R * H i)).prod * R

@[simp]
theorem continuousLinearMapRealResolventDysonFormalMultilinearSeries_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (R : V →L[ℝ] V) (H : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventDysonFormalMultilinearSeries R n H =
      continuousLinearMapRealResolventOrderedDysonCoefficientFromResolvent n R H := by
  simp [continuousLinearMapRealResolventDysonFormalMultilinearSeries,
    continuousLinearMapRealResolventOrderedDysonCoefficientFromResolvent,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- Explicit Neumann power series for `H ↦ (1 - R H)⁻¹ R`. -/
theorem hasFPowerSeriesOnBall_continuousLinearMapRealResolvent_neumann
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (R : V →L[ℝ] V) :
    HasFPowerSeriesOnBall
      (fun H : V →L[ℝ] V => Ring.inverse (1 - R * H) * R)
      (continuousLinearMapRealResolventDysonFormalMultilinearSeries R) 0
      (1 / ‖continuousLinearMapOperatorLeftMultiplication R‖ₑ) := by
  have hin :=
    (hasFPowerSeriesOnBall_inverse_one_sub ℝ (V →L[ℝ] V)).compContinuousLinearMap
      (u := continuousLinearMapOperatorLeftMultiplication R)
      (x := (0 : V →L[ℝ] V))
  have hout :=
    (continuousLinearMapOperatorRightMultiplication R).comp_hasFPowerSeriesOnBall hin
  simpa [continuousLinearMapRealResolventDysonFormalMultilinearSeries,
    Function.comp_def] using hout

/-- The true `n`-th Fréchet derivative of the explicit Neumann resolvent is
the sum of all ordered Dyson words over permutations of the directions. -/
theorem iteratedFDeriv_continuousLinearMapRealResolvent_neumann_eq_sum_orderedDyson
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (R : V →L[ℝ] V) (n : ℕ)
    (H : Fin n → (V →L[ℝ] V)) :
    iteratedFDeriv ℝ n
        (fun K : V →L[ℝ] V => Ring.inverse (1 - R * K) * R) 0 H =
      ∑ σ : Equiv.Perm (Fin n),
        continuousLinearMapRealResolventOrderedDysonCoefficientFromResolvent
          n R (fun i => H (σ i)) := by
  have hseries := hasFPowerSeriesOnBall_continuousLinearMapRealResolvent_neumann R
  rw [hseries.iteratedFDeriv_eq_sum_of_completeSpace H]
  apply Finset.sum_congr rfl
  intro σ _hσ
  simp

end MathlibAnalytic
end MGAP4D
