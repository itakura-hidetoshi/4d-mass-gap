import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFactorialSpectralDerivative
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring Topology

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Shifting the operator by `-sI` at spectral parameter `z` is exactly the
same real resolvent as shifting the spectral parameter to `z+s`. -/
theorem continuousLinearMapRealResolvent_sub_smul_one_eq_spectralShift
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z s : ℝ) :
    continuousLinearMapRealResolvent (A - s • (1 : V →L[ℝ] V)) z =
      continuousLinearMapRealResolvent A (z + s) := by
  unfold continuousLinearMapRealResolvent continuousLinearMapRealShift
  congr 1
  module

/-- The augmented real shift is exactly the original operator chart evaluated
at the shifted real spectral parameter. -/
theorem continuousLinearMapJointSpectralOperatorRealShift_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    continuousLinearMapRealShift
        (continuousLinearMapFiniteParameterOperatorChart (m + 1) A
          (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
          (continuousLinearMapJointSpectralOperatorParameter m s t)) z =
      continuousLinearMapRealShift
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s) := by
  rw [continuousLinearMapJointSpectralOperatorOperatorChart_eq]
  unfold continuousLinearMapRealShift
  module

/-- Every symmetric operator derivative is unchanged when an operator shift by
`-sI` is transferred to the real spectral parameter. -/
theorem continuousLinearMapRealResolventOperatorSymmetricDerivative_sub_smul_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (n : ℕ) (A : V →L[ℝ] V) (z s : ℝ)
    (K : Fin n → (V →L[ℝ] V)) :
    continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (A - s • (1 : V →L[ℝ] V)) z K =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        A (z + s) K := by
  change
    continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent
          (A - s • (1 : V →L[ℝ] V)) z) K =
      continuousLinearMapRealResolventSymmetricDysonMultilinear n
        (continuousLinearMapRealResolvent A (z + s)) K
  rw [continuousLinearMapRealResolvent_sub_smul_one_eq_spectralShift]

/-- The genuine joint spectral/operator formal power series at an arbitrary
joint parameter point. -/
def continuousLinearMapJointSpectralOperatorRealResolventFPowerSeries
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z : ℝ) (p₀ : Fin (m + 1) → ℝ) :
    FormalMultilinearSeries ℝ (Fin (m + 1) → ℝ) (V →L[ℝ] V) :=
  continuousLinearMapFiniteParameterRealResolventFPowerSeries (m + 1) A
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z p₀

/-- At every joint point in the real resolvent set, the augmented chart has the
pulled-back noncommutative power series. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_hasFPowerSeriesAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    HasFPowerSeriesAt
      (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
      (continuousLinearMapJointSpectralOperatorRealResolventFPowerSeries m A H z
        (continuousLinearMapJointSpectralOperatorParameter m s t))
      (continuousLinearMapJointSpectralOperatorParameter m s t) := by
  have hunit' : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart (m + 1) A
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t)) z) := by
    rw [continuousLinearMapJointSpectralOperatorRealShift_eq]
    exact hunit
  exact continuousLinearMapFiniteParameterRealResolventChart_hasFPowerSeriesAt
    (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t) hunit'

/-- The joint spectral/operator resolvent chart is analytic at every point in
its real resolvent set. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_analyticAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))) :
    AnalyticAt ℝ
      (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
      (continuousLinearMapJointSpectralOperatorParameter m s t) :=
  (continuousLinearMapJointSpectralOperatorRealResolventChart_hasFPowerSeriesAt
    m A H z s t hunit).analyticAt

/-- Arbitrary joint parameter-direction Fréchet derivatives are the symmetric
operator derivative at the shifted physical point, evaluated on the augmented
synthesized directions. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_iteratedFDeriv_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (n : ℕ) (u : Fin n → (Fin (m + 1) → ℝ)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t) u =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
        (continuousLinearMapFiniteParameterDirectionTuple (m + 1) n
          (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u) := by
  have hunit' : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart (m + 1) A
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
        (continuousLinearMapJointSpectralOperatorParameter m s t)) z) := by
    rw [continuousLinearMapJointSpectralOperatorRealShift_eq]
    exact hunit
  unfold continuousLinearMapJointSpectralOperatorRealResolventChart
  rw [continuousLinearMapFiniteParameterRealResolventChart_iteratedFDeriv_apply
    (m + 1) A (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorParameter m s t) hunit' n u]
  rw [continuousLinearMapJointSpectralOperatorOperatorChart_eq]
  exact continuousLinearMapRealResolventOperatorSymmetricDerivative_sub_smul_one
    n (continuousLinearMapFiniteParameterOperatorChart m A H t) z s _

/-- Coordinate-word joint mixed partials insert `-I` at spectral slots and the
selected perturbation operator at operator slots. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (n : ℕ) (κ : Fin n → Option (Fin m)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
        (fun i => match κ i with
          | none => -(1 : V →L[ℝ] V)
          | some j => H j) := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventChart_iteratedFDeriv_apply
    m A H z s t hunit n]
  congr 1
  exact continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple_synthesis
    m n H κ

/-- Joint coordinate mixed partials are invariant under every permutation of
spectral and operator slots. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial_perm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (n : ℕ) (κ : Fin n → Option (Fin m)) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n
          (fun i => κ (σ i))) =
      iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ) := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial
    m A H z s t hunit n (fun i => κ (σ i)),
    continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial
    m A H z s t hunit n κ]
  change continuousLinearMapRealResolventSymmetricDysonMultilinear n _
      (fun i => (match κ (σ i) with
        | none => -(1 : V →L[ℝ] V)
        | some j => H j)) =
    continuousLinearMapRealResolventSymmetricDysonMultilinear n _
      (fun i => (match κ i with
        | none => -(1 : V →L[ℝ] V)
        | some j => H j))
  exact continuousLinearMapRealResolventSymmetricDysonMultilinear_apply_perm
    (V := V) n
    (continuousLinearMapRealResolvent
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s))
    σ (fun i => match κ i with
      | none => -(1 : V →L[ℝ] V)
      | some j => H j)

/-- A pure operator-coordinate word recovers the established finite-parameter
operator mixed partial at the shifted spectral point. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_pureOperator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (n : ℕ) (κ : Fin n → Fin m) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n
          (fun i => some (κ i))) =
      continuousLinearMapRealResolventOperatorSymmetricDerivative n
        (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
        (fun i => H (κ i)) := by
  simpa using
    continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial
      m A H z s t hunit n (fun i => some (κ i))

/-- A pure spectral-coordinate word gives the signed factorial spectral jet. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventChart_pureSpectral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ)
    (hunit : IsUnit (continuousLinearMapRealShift
      (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)))
    (n : ℕ) :
    iteratedFDeriv ℝ n
        (continuousLinearMapJointSpectralOperatorRealResolventChart m A H z)
        (continuousLinearMapJointSpectralOperatorParameter m s t)
        (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n
          (fun _ => none)) =
      continuousLinearMapRealResolventSpectralCoefficient n •
        (continuousLinearMapRealResolvent
          (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)) ^
            (n + 1) := by
  rw [continuousLinearMapJointSpectralOperatorRealResolventChart_coordinateMixedPartial
    m A H z s t hunit n (fun _ => none)]
  rw [continuousLinearMapRealResolventOperatorSymmetricDerivative_const]
  let R := continuousLinearMapRealResolvent
    (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)
  change (n.factorial : ℝ) • ((R * (-(1 : V →L[ℝ] V))) ^ n * R) =
    continuousLinearMapRealResolventSpectralCoefficient n • R ^ (n + 1)
  have hmul : R * (-(1 : V →L[ℝ] V)) = (-1 : ℝ) • R := by
    module
  have hscalar :
      (n.factorial : ℝ) * (-1 : ℝ) ^ n =
        continuousLinearMapRealResolventSpectralCoefficient n := by
    unfold continuousLinearMapRealResolventSpectralCoefficient
    ring
  rw [hmul, smul_pow, smul_mul_assoc, smul_smul, ← pow_succ, hscalar]

end MathlibAnalytic
end MGAP4D
