import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventStabilityCore
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Changing the operator at fixed real spectral parameter changes the shifted
operator by the opposite operator increment. -/
theorem continuousLinearMapRealShift_sub_realShift_operator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B : V →L[ℝ] V) (z : ℝ) :
    continuousLinearMapRealShift A z - continuousLinearMapRealShift B z = B - A := by
  simp [continuousLinearMapRealShift]
  abel

/-- Exact fixed-spectral-parameter resolvent identity under an operator
perturbation. -/
theorem continuousLinearMapRealResolvent_sub_eq_mul_operator_sub_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hB : IsUnit (continuousLinearMapRealShift B z)) :
    continuousLinearMapRealResolvent B z - continuousLinearMapRealResolvent A z =
      continuousLinearMapRealResolvent B z * (B - A) *
        continuousLinearMapRealResolvent A z := by
  have hRA : continuousLinearMapRealShift A z *
      continuousLinearMapRealResolvent A z = 1 := mul_ringInverse_of_isUnit hA
  have hRB : continuousLinearMapRealResolvent B z *
      continuousLinearMapRealShift B z = 1 := ringInverse_mul_of_isUnit hB
  calc
    continuousLinearMapRealResolvent B z - continuousLinearMapRealResolvent A z =
        continuousLinearMapRealResolvent B z * 1 -
          1 * continuousLinearMapRealResolvent A z := by rw [mul_one, one_mul]
    _ = continuousLinearMapRealResolvent B z *
          (continuousLinearMapRealShift A z * continuousLinearMapRealResolvent A z) -
        (continuousLinearMapRealResolvent B z * continuousLinearMapRealShift B z) *
          continuousLinearMapRealResolvent A z := by rw [hRA, hRB]
    _ = continuousLinearMapRealResolvent B z *
          (continuousLinearMapRealShift A z - continuousLinearMapRealShift B z) *
          continuousLinearMapRealResolvent A z := by noncomm_ring
    _ = continuousLinearMapRealResolvent B z * (B - A) *
          continuousLinearMapRealResolvent A z := by
      rw [continuousLinearMapRealShift_sub_realShift_operator]

/-- The exact operator perturbation identity gives a three-factor norm bound. -/
theorem continuousLinearMapRealResolvent_sub_norm_le_operatorPerturbation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hB : IsUnit (continuousLinearMapRealShift B z)) :
    ‖continuousLinearMapRealResolvent B z - continuousLinearMapRealResolvent A z‖ ≤
      ‖continuousLinearMapRealResolvent B z‖ * ‖B - A‖ *
        ‖continuousLinearMapRealResolvent A z‖ := by
  rw [continuousLinearMapRealResolvent_sub_eq_mul_operator_sub_mul A B z hA hB]
  calc
    ‖continuousLinearMapRealResolvent B z * (B - A) *
        continuousLinearMapRealResolvent A z‖ ≤
      ‖continuousLinearMapRealResolvent B z * (B - A)‖ *
        ‖continuousLinearMapRealResolvent A z‖ := norm_mul_le _ _
    _ ≤ (‖continuousLinearMapRealResolvent B z‖ * ‖B - A‖) *
        ‖continuousLinearMapRealResolvent A z‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- A bounded pair of resolvents gives the usual quadratic condition-number
bound for operator perturbations. -/
theorem continuousLinearMapRealResolvent_sub_norm_le_operatorPerturbation_of_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V →L[ℝ] V) (z MA MB : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hB : IsUnit (continuousLinearMapRealShift B z))
    (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hnormA : ‖continuousLinearMapRealResolvent A z‖ ≤ MA)
    (hnormB : ‖continuousLinearMapRealResolvent B z‖ ≤ MB) :
    ‖continuousLinearMapRealResolvent B z - continuousLinearMapRealResolvent A z‖ ≤
      MB * ‖B - A‖ * MA := by
  calc
    ‖continuousLinearMapRealResolvent B z - continuousLinearMapRealResolvent A z‖ ≤
        ‖continuousLinearMapRealResolvent B z‖ * ‖B - A‖ *
          ‖continuousLinearMapRealResolvent A z‖ :=
      continuousLinearMapRealResolvent_sub_norm_le_operatorPerturbation A B z hA hB
    _ ≤ MB * ‖B - A‖ * MA := by gcongr

/-- The perturbed shift factors through the reference shift and the normalized
operator increment. -/
theorem continuousLinearMapRealShift_add_eq_mul_one_sub_resolvent_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z)) :
    continuousLinearMapRealShift (A + H) z =
      continuousLinearMapRealShift A z *
        (1 - continuousLinearMapRealResolvent A z * H) := by
  have hAR : continuousLinearMapRealShift A z *
      continuousLinearMapRealResolvent A z = 1 := mul_ringInverse_of_isUnit hA
  calc
    continuousLinearMapRealShift (A + H) z =
        continuousLinearMapRealShift A z - H := by
      simp [continuousLinearMapRealShift]
    _ = continuousLinearMapRealShift A z *
        (1 - continuousLinearMapRealResolvent A z * H) := by
      rw [mul_sub, mul_one, ← mul_assoc, hAR, one_mul]

/-- A normalized operator increment of norm less than one preserves
invertibility at the fixed spectral parameter. -/
theorem continuousLinearMapRealShift_add_isUnit_of_resolvent_mul_norm_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    IsUnit (continuousLinearMapRealShift (A + H) z) := by
  rw [continuousLinearMapRealShift_add_eq_mul_one_sub_resolvent_mul A H z hA]
  exact hA.mul (Units.isUnit_oneSub _ hsmall)

/-- Exact local inverse representation for an operator perturbation. -/
theorem continuousLinearMapRealResolvent_add_eq_inverse_one_sub_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    continuousLinearMapRealResolvent (A + H) z =
      Ring.inverse (1 - continuousLinearMapRealResolvent A z * H) *
        continuousLinearMapRealResolvent A z := by
  let R := continuousLinearMapRealResolvent A z
  let X := continuousLinearMapRealShift A z
  let P := R * H
  let U : (V →L[ℝ] V)ˣ := Units.oneSub P (by simpa [P] using hsmall)
  let S : V →L[ℝ] V := (↑U⁻¹ : V →L[ℝ] V) * R
  have hRX : R * X = 1 := ringInverse_mul_of_isUnit hA
  have hXR : X * R = 1 := mul_ringInverse_of_isUnit hA
  have hUval : (↑U : V →L[ℝ] V) = 1 - P := by simp [U]
  have hshift : continuousLinearMapRealShift (A + H) z = X * (1 - P) := by
    simpa [X, R, P] using
      continuousLinearMapRealShift_add_eq_mul_one_sub_resolvent_mul A H z hA
  have hSleft : S * continuousLinearMapRealShift (A + H) z = 1 := by
    rw [hshift]
    dsimp [S]
    calc
      ((↑U⁻¹ : V →L[ℝ] V) * R) * (X * (1 - P)) =
          (↑U⁻¹ : V →L[ℝ] V) * (R * X) * (1 - P) := by simp [mul_assoc]
      _ = (↑U⁻¹ : V →L[ℝ] V) * (1 - P) := by rw [hRX, mul_one]
      _ = (↑U⁻¹ : V →L[ℝ] V) * (↑U : V →L[ℝ] V) := by rw [hUval]
      _ = 1 := by simp
  have hSright : continuousLinearMapRealShift (A + H) z * S = 1 := by
    rw [hshift]
    dsimp [S]
    calc
      (X * (1 - P)) * ((↑U⁻¹ : V →L[ℝ] V) * R) =
          X * ((1 - P) * (↑U⁻¹ : V →L[ℝ] V)) * R := by simp [mul_assoc]
      _ = X * ((↑U : V →L[ℝ] V) * (↑U⁻¹ : V →L[ℝ] V)) * R := by rw [hUval]
      _ = X * R := by simp
      _ = 1 := hXR
  have hnew : IsUnit (continuousLinearMapRealShift (A + H) z) :=
    continuousLinearMapRealShift_add_isUnit_of_resolvent_mul_norm_lt_one A H z hA hsmall
  have hinvMul : Ring.inverse (continuousLinearMapRealShift (A + H) z) *
      continuousLinearMapRealShift (A + H) z = 1 := ringInverse_mul_of_isUnit hnew
  have hEq : continuousLinearMapRealResolvent (A + H) z = S := by
    unfold continuousLinearMapRealResolvent
    calc
      Ring.inverse (continuousLinearMapRealShift (A + H) z) =
          Ring.inverse (continuousLinearMapRealShift (A + H) z) * 1 := by simp
      _ = Ring.inverse (continuousLinearMapRealShift (A + H) z) *
          (continuousLinearMapRealShift (A + H) z * S) := by rw [hSright]
      _ = (Ring.inverse (continuousLinearMapRealShift (A + H) z) *
          continuousLinearMapRealShift (A + H) z) * S := by rw [mul_assoc]
      _ = S := by rw [hinvMul, one_mul]
  rw [hEq]
  have hInv : Ring.inverse (1 - P) = (↑U⁻¹ : V →L[ℝ] V) := by
    simpa [U] using NormedRing.inverse_one_sub P (by simpa [P] using hsmall)
  simpa [S, R, P] using congrArg (fun T : V →L[ℝ] V => T * R) hInv

/-- The `n`-th noncommutative Dyson coefficient around a reference operator. -/
def continuousLinearMapRealResolventOperatorDysonCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : V →L[ℝ] V :=
  (continuousLinearMapRealResolvent A z * H) ^ n *
    continuousLinearMapRealResolvent A z

/-- The finite Dyson partial sum. -/
def continuousLinearMapRealResolventOperatorDysonPartialSum
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : V →L[ℝ] V :=
  ∑ n ∈ Finset.range N,
    continuousLinearMapRealResolventOperatorDysonCoefficient n A H z

/-- The exact finite-order Dyson remainder. -/
def continuousLinearMapRealResolventOperatorDysonRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ) : V →L[ℝ] V :=
  (continuousLinearMapRealResolvent A z * H) ^ N *
    continuousLinearMapRealResolvent (A + H) z

/-- Exact finite noncommutative Dyson expansion with its true remainder. -/
theorem continuousLinearMapRealResolvent_add_eq_operatorDysonPartialSum_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    continuousLinearMapRealResolvent (A + H) z =
      continuousLinearMapRealResolventOperatorDysonPartialSum N A H z +
        continuousLinearMapRealResolventOperatorDysonRemainder N A H z := by
  let R := continuousLinearMapRealResolvent A z
  let P := R * H
  have hlocal : continuousLinearMapRealResolvent (A + H) z =
      Ring.inverse (1 - P) * R := by
    simpa [R, P] using
      continuousLinearMapRealResolvent_add_eq_inverse_one_sub_mul A H z hA hsmall
  calc
    continuousLinearMapRealResolvent (A + H) z = Ring.inverse (1 - P) * R := hlocal
    _ = ((∑ n ∈ Finset.range N, P ^ n) +
          P ^ N * Ring.inverse (1 - P)) * R := by
      exact congrArg (fun T : V →L[ℝ] V => T * R)
        (NormedRing.inverse_one_sub_nth_order' N (by simpa [P] using hsmall))
    _ = (∑ n ∈ Finset.range N, P ^ n * R) +
          P ^ N * (Ring.inverse (1 - P) * R) := by
      rw [add_mul, Finset.sum_mul]
      noncomm_ring
    _ = continuousLinearMapRealResolventOperatorDysonPartialSum N A H z +
          continuousLinearMapRealResolventOperatorDysonRemainder N A H z := by
      rw [← hlocal]
      simp [continuousLinearMapRealResolventOperatorDysonPartialSum,
        continuousLinearMapRealResolventOperatorDysonCoefficient,
        continuousLinearMapRealResolventOperatorDysonRemainder, R, P]

/-- The exact approximation defect equals the Dyson remainder. -/
theorem continuousLinearMapRealResolvent_add_sub_operatorDysonPartialSum_eq_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1) :
    continuousLinearMapRealResolvent (A + H) z -
        continuousLinearMapRealResolventOperatorDysonPartialSum N A H z =
      continuousLinearMapRealResolventOperatorDysonRemainder N A H z := by
  rw [continuousLinearMapRealResolvent_add_eq_operatorDysonPartialSum_add_remainder
    N A H z hA hsmall]
  abel

/-- Explicit geometric norm bound for the exact Dyson remainder. -/
theorem continuousLinearMapRealResolventOperatorDysonRemainder_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z q M : ℝ)
    (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapRealResolvent A z * H‖ ≤ q)
    (hnew : ‖continuousLinearMapRealResolvent (A + H) z‖ ≤ M) :
    ‖continuousLinearMapRealResolventOperatorDysonRemainder N A H z‖ ≤ q ^ N * M := by
  unfold continuousLinearMapRealResolventOperatorDysonRemainder
  calc
    ‖(continuousLinearMapRealResolvent A z * H) ^ N *
        continuousLinearMapRealResolvent (A + H) z‖ ≤
      ‖(continuousLinearMapRealResolvent A z * H) ^ N‖ *
        ‖continuousLinearMapRealResolvent (A + H) z‖ := norm_mul_le _ _
    _ ≤ ‖continuousLinearMapRealResolvent A z * H‖ ^ N *
        ‖continuousLinearMapRealResolvent (A + H) z‖ :=
      mul_le_mul_of_nonneg_right (norm_pow_le' _ (by omega)) (norm_nonneg _)
    _ ≤ q ^ N * M := by
      exact mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hperturb N) hnew
        (norm_nonneg _) (pow_nonneg hq N)

/-- Explicit geometric error estimate for the finite Dyson approximation. -/
theorem continuousLinearMapRealResolvent_add_sub_operatorDysonPartialSum_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (N : ℕ) (A H : V →L[ℝ] V) (z q M : ℝ)
    (hA : IsUnit (continuousLinearMapRealShift A z))
    (hsmall : ‖continuousLinearMapRealResolvent A z * H‖ < 1)
    (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hperturb : ‖continuousLinearMapRealResolvent A z * H‖ ≤ q)
    (hnew : ‖continuousLinearMapRealResolvent (A + H) z‖ ≤ M) :
    ‖continuousLinearMapRealResolvent (A + H) z -
        continuousLinearMapRealResolventOperatorDysonPartialSum N A H z‖ ≤
      q ^ N * M := by
  rw [continuousLinearMapRealResolvent_add_sub_operatorDysonPartialSum_eq_remainder
    N A H z hA hsmall]
  exact continuousLinearMapRealResolventOperatorDysonRemainder_norm_le
    N A H z q M hq hM hperturb hnew

end MathlibAnalytic
end MGAP4D
