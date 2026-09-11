import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterFrechetTaylorResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- A quantitative continuity lemma used to transport uniform operator-valued
estimates through an arbitrary continuous linear observable. -/
theorem continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt
    {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : X →L[ℝ] W) {x y : X} {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hxy : ‖x - y‖ < epsilon / (‖φ‖ + 1)) :
    ‖φ x - φ y‖ < epsilon := by
  rw [← map_sub]
  have hpositive : 0 < ‖φ‖ + 1 := by positivity
  calc
    ‖φ (x - y)‖ ≤ ‖φ‖ * ‖x - y‖ := φ.le_opNorm _
    _ ≤ (‖φ‖ + 1) * ‖x - y‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg φ]) (norm_nonneg _)
    _ < (‖φ‖ + 1) * (epsilon / (‖φ‖ + 1)) :=
      mul_lt_mul_of_pos_left hxy hpositive
    _ = epsilon := by
      field_simp [ne_of_gt hpositive]

/-- Arbitrary Banach-valued continuous-linear observation of a
finite-parameter Taylor-Dyson coefficient. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
    n m A H z t h)

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
        φ n m A H z t h =
      φ (continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
        n m A H z t h) :=
  rfl

/-- Arbitrary Banach-valued observation of the normalized diagonal genuine
Fréchet Taylor coefficient. -/
def continuousLinearMapFiniteParameterRealResolventFrechetTaylorResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : W :=
  φ (continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient
    n m A H z t h)

/-- At a real-resolvent point, arbitrary continuous-linear observations of the
genuine normalized Fréchet coefficient and the Taylor-Dyson coefficient agree. -/
theorem continuousLinearMapFiniteParameterRealResolventFrechetTaylorResponse_eq_taylorDyson
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (n m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) z)) :
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorResponse
        φ n m A H z t h =
      continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
        φ n m A H z t h := by
  simp [continuousLinearMapFiniteParameterRealResolventFrechetTaylorResponse,
    continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse,
    continuousLinearMapFiniteParameterRealResolventFrechetTaylorCoefficient_eq_taylorDysonCoefficient
      n m A H z t h hunit]

/-- Finite jet of Banach-valued Taylor-Dyson coefficient observations. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonResponseJet
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (N m : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : Fin N → W :=
  fun n => continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
    φ n.1 m A H z t h

/-- Basis-independent trace observation of a finite-parameter Taylor-Dyson
coefficient. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : ℝ :=
  continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse
    (continuousLinearMapTrace (V := V)) n m A H z t h

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient_apply
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) :
    continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
        V n m A H z t h =
      continuousLinearMapTrace
        (continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
          n m A H z t h) :=
  rfl

/-- Finite basis-independent trace jet of Taylor-Dyson coefficients. -/
def continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceJet
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (N m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t h : Fin m → ℝ) : Fin N → ℝ :=
  fun n => continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient
    V n.1 m A H z t h

end MathlibAnalytic
end MGAP4D
