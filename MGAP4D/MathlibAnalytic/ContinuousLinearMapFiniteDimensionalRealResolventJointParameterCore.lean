import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterFrechetTaylorResponse
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The augmented finite parameter family in which coordinate zero moves the
real spectral parameter and the successor coordinates move the operator.  A
positive spectral displacement is represented by the operator direction
`-I`, since
`R_{A - sI}(z) = R_A(z+s)`. -/
def continuousLinearMapJointSpectralOperatorDirectionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    Fin (m + 1) → (V →L[ℝ] V) :=
  Fin.cases (-(1 : V →L[ℝ] V)) H

/-- Assemble a spectral displacement and an operator-parameter vector into the
augmented parameter space. -/
def continuousLinearMapJointSpectralOperatorParameter
    (m : ℕ) (s : ℝ) (t : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases s t

@[simp]
theorem continuousLinearMapJointSpectralOperatorDirectionFamily_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    continuousLinearMapJointSpectralOperatorDirectionFamily m H 0 =
      -(1 : V →L[ℝ] V) :=
  rfl

@[simp]
theorem continuousLinearMapJointSpectralOperatorDirectionFamily_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (j : Fin m) :
    continuousLinearMapJointSpectralOperatorDirectionFamily m H j.succ = H j :=
  rfl

@[simp]
theorem continuousLinearMapJointSpectralOperatorParameter_zero
    (m : ℕ) (s : ℝ) (t : Fin m → ℝ) :
    continuousLinearMapJointSpectralOperatorParameter m s t 0 = s :=
  rfl

@[simp]
theorem continuousLinearMapJointSpectralOperatorParameter_succ
    (m : ℕ) (s : ℝ) (t : Fin m → ℝ) (j : Fin m) :
    continuousLinearMapJointSpectralOperatorParameter m s t j.succ = t j :=
  rfl

/-- Synthesis in the augmented parameter space is exactly operator synthesis
minus the spectral displacement times the identity. -/
theorem continuousLinearMapJointSpectralOperatorDirectionSynthesis_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (s : ℝ)
    (t : Fin m → ℝ) :
    continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t) =
      continuousLinearMapFiniteParameterDirectionSynthesis m H t -
        s • (1 : V →L[ℝ] V) := by
  rw [continuousLinearMapFiniteParameterDirectionSynthesis_apply,
    Fin.sum_univ_succ,
    continuousLinearMapFiniteParameterDirectionSynthesis_apply]
  simp [continuousLinearMapJointSpectralOperatorDirectionFamily,
    continuousLinearMapJointSpectralOperatorParameter]
  abel

/-- The augmented operator chart is the original finite-parameter chart shifted
by `-sI`. -/
theorem continuousLinearMapJointSpectralOperatorOperatorChart_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (s : ℝ) (t : Fin m → ℝ) :
    continuousLinearMapFiniteParameterOperatorChart (m + 1) A
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t) =
      continuousLinearMapFiniteParameterOperatorChart m A H t -
        s • (1 : V →L[ℝ] V) := by
  rw [continuousLinearMapFiniteParameterOperatorChart,
    continuousLinearMapJointSpectralOperatorDirectionSynthesis_apply,
    continuousLinearMapFiniteParameterOperatorChart]
  abel

/-- The resolvent pulled back to the augmented parameter space. -/
def continuousLinearMapJointSpectralOperatorRealResolventChart
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (p : Fin (m + 1) → ℝ) : V →L[ℝ] V :=
  continuousLinearMapFiniteParameterRealResolventChart (m + 1) A
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z p

/-- Exact identification of the augmented chart with simultaneous spectral and
operator displacement. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    continuousLinearMapJointSpectralOperatorRealResolventChart m A H z
        (continuousLinearMapJointSpectralOperatorParameter m s t) =
      continuousLinearMapFiniteParameterRealResolventChart m A H (z + s) t := by
  unfold continuousLinearMapJointSpectralOperatorRealResolventChart
  unfold continuousLinearMapFiniteParameterRealResolventChart
  unfold continuousLinearMapRealResolvent
  congr 1
  rw [continuousLinearMapJointSpectralOperatorOperatorChart_eq]
  unfold continuousLinearMapRealShift
  module

/-- A coordinate word for the joint calculus: `none` denotes one spectral
coordinate and `some j` denotes the `j`-th operator parameter. -/
def continuousLinearMapJointSpectralOperatorCoordinate
    (m : ℕ) : Option (Fin m) → Fin (m + 1)
  | none => 0
  | some j => j.succ

@[simp]
theorem continuousLinearMapJointSpectralOperatorDirectionFamily_coordinate_none
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    continuousLinearMapJointSpectralOperatorDirectionFamily m H
        (continuousLinearMapJointSpectralOperatorCoordinate m none) =
      -(1 : V →L[ℝ] V) :=
  rfl

@[simp]
theorem continuousLinearMapJointSpectralOperatorDirectionFamily_coordinate_some
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) (j : Fin m) :
    continuousLinearMapJointSpectralOperatorDirectionFamily m H
        (continuousLinearMapJointSpectralOperatorCoordinate m (some j)) = H j :=
  rfl

/-- Coordinate basis directions associated with a joint spectral/operator word. -/
def continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple
    (m n : ℕ) (κ : Fin n → Option (Fin m)) :
    Fin n → (Fin (m + 1) → ℝ) :=
  fun i => Pi.single
    (continuousLinearMapJointSpectralOperatorCoordinate m (κ i)) 1

/-- Synthesizing a joint coordinate word gives `-I` in every spectral slot and
the selected perturbation operator in every operator slot. -/
theorem continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple_synthesis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (κ : Fin n → Option (Fin m)) :
    continuousLinearMapFiniteParameterDirectionTuple (m + 1) n
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ) =
      fun i => match κ i with
        | none => -(1 : V →L[ℝ] V)
        | some j => H j := by
  funext i
  unfold continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple
  rw [continuousLinearMapFiniteParameterDirectionTuple,
    continuousLinearMapFiniteParameterDirectionSynthesis_single]
  cases hκ : κ i with
  | none => simp [continuousLinearMapJointSpectralOperatorCoordinate, hκ]
  | some j => simp [continuousLinearMapJointSpectralOperatorCoordinate, hκ]

end MathlibAnalytic
end MGAP4D
