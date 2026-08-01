import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearFrechet
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Synthesis of a finite family of operator perturbation directions from a
real parameter vector. -/
def continuousLinearMapFiniteParameterDirectionSynthesis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    (Fin m → ℝ) →L[ℝ] (V →L[ℝ] V) :=
  ∑ j : Fin m,
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).smulRight (H j)

@[simp]
theorem continuousLinearMapFiniteParameterDirectionSynthesis_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (t : Fin m → ℝ) :
    continuousLinearMapFiniteParameterDirectionSynthesis m H t =
      ∑ j : Fin m, t j • H j := by
  simp [continuousLinearMapFiniteParameterDirectionSynthesis]

/-- Each coordinate basis vector synthesizes its corresponding operator
direction. -/
@[simp]
theorem continuousLinearMapFiniteParameterDirectionSynthesis_single
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (j : Fin m) :
    continuousLinearMapFiniteParameterDirectionSynthesis m H
        (Pi.single j 1) = H j := by
  rw [continuousLinearMapFiniteParameterDirectionSynthesis_apply]
  simp

/-- The finite-parameter operator perturbation chart through a base operator. -/
def continuousLinearMapFiniteParameterOperatorChart
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (t : Fin m → ℝ) : V →L[ℝ] V :=
  A + continuousLinearMapFiniteParameterDirectionSynthesis m H t

@[simp]
theorem continuousLinearMapFiniteParameterOperatorChart_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) :
    continuousLinearMapFiniteParameterOperatorChart m A H 0 = A := by
  simp [continuousLinearMapFiniteParameterOperatorChart]

/-- The real resolvent pulled back to a finite-dimensional parameter space. -/
def continuousLinearMapFiniteParameterRealResolventChart
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (t : Fin m → ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolvent
    (continuousLinearMapFiniteParameterOperatorChart m A H t) z

@[simp]
theorem continuousLinearMapFiniteParameterRealResolventChart_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) :
    continuousLinearMapFiniteParameterRealResolventChart m A H z 0 =
      continuousLinearMapRealResolvent A z := by
  simp [continuousLinearMapFiniteParameterRealResolventChart]

/-- A finite tuple of parameter-space directions synthesizes componentwise to
a tuple of operator directions. -/
def continuousLinearMapFiniteParameterDirectionTuple
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : Fin n → (Fin m → ℝ)) : Fin n → (V →L[ℝ] V) :=
  fun i => continuousLinearMapFiniteParameterDirectionSynthesis m H (u i)

@[simp]
theorem continuousLinearMapFiniteParameterDirectionTuple_coordinate
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (kappa : Fin n → Fin m) :
    continuousLinearMapFiniteParameterDirectionTuple m n H
        (fun i => Pi.single (kappa i) 1) =
      fun i => H (kappa i) := by
  funext i
  simp [continuousLinearMapFiniteParameterDirectionTuple]

end MathlibAnalytic
end MGAP4D
