import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventSpectralDerivativeCore
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff LinearPMap Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The signed factorial coefficient in the spectral derivative formula for
`R_A(z) = (z I - A)⁻¹`. -/
def continuousLinearMapRealResolventSpectralCoefficient (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (n.factorial : ℝ)

@[simp]
theorem continuousLinearMapRealResolventSpectralCoefficient_zero :
    continuousLinearMapRealResolventSpectralCoefficient 0 = 1 := by
  simp [continuousLinearMapRealResolventSpectralCoefficient]

/-- The signed factorial coefficients obey the differentiation recursion. -/
theorem continuousLinearMapRealResolventSpectralCoefficient_succ (n : ℕ) :
    continuousLinearMapRealResolventSpectralCoefficient (n + 1) =
      continuousLinearMapRealResolventSpectralCoefficient n *
        (-((n + 1 : ℕ) : ℝ)) := by
  simp [continuousLinearMapRealResolventSpectralCoefficient,
    pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  ring

/-- The norm of the signed factorial spectral coefficient is exactly `n!`. -/
theorem continuousLinearMapRealResolventSpectralCoefficient_norm (n : ℕ) :
    ‖continuousLinearMapRealResolventSpectralCoefficient n‖ =
      (n.factorial : ℝ) := by
  simp [continuousLinearMapRealResolventSpectralCoefficient, norm_mul,
    Real.norm_natCast]

/-- The spectral derivative of the `k`-th composition power of a true real
resolvent is `-k R^(k+1)` throughout any common real resolvent region. -/
theorem continuousLinearMapRealResolvent_pow_hasDerivWithinAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (k : ℕ) {z : ℝ} (hz : z ∈ U) :
    HasDerivWithinAt
      (fun w => (continuousLinearMapRealResolvent A w) ^ k)
      (-((k : ℝ) •
        (continuousLinearMapRealResolvent A z) ^ (k + 1))) U z := by
  induction k with
  | zero =>
      have hconst :
          HasDerivWithinAt
            (fun _ : ℝ => (1 : V →L[ℝ] V))
            (0 : V →L[ℝ] V) U z :=
        hasDerivWithinAt_const z U (1 : V →L[ℝ] V)
      simpa using hconst
  | succ k ih =>
      have hR := continuousLinearMapRealResolvent_hasDerivWithinAt
        A U M hM hunit hnorm hz
      have hmul := HasDerivWithinAt.mul
        (𝕜 := ℝ) (𝔸 := V →L[ℝ] V) ih hR
      have hmul' :
          HasDerivWithinAt
            (fun w => (continuousLinearMapRealResolvent A w) ^ (k + 1))
            ((-((k : ℝ) •
                  (continuousLinearMapRealResolvent A z) ^ (k + 1))) *
                continuousLinearMapRealResolvent A z +
              (continuousLinearMapRealResolvent A z) ^ k *
                (-((continuousLinearMapRealResolvent A z) ^ 2)))
            U z := by
        simpa only [Pi.mul_apply, pow_succ] using hmul
      have hderiv :
          (-((k : ℝ) •
                (continuousLinearMapRealResolvent A z) ^ (k + 1))) *
              continuousLinearMapRealResolvent A z +
            (continuousLinearMapRealResolvent A z) ^ k *
              (-((continuousLinearMapRealResolvent A z) ^ 2)) =
          -((((Nat.succ k : ℕ) : ℝ) •
            (continuousLinearMapRealResolvent A z) ^
              (Nat.succ k + 1))) := by
        let Rz := continuousLinearMapRealResolvent A z
        change
          (-((k : ℝ) • Rz ^ (k + 1))) * Rz +
              Rz ^ k * (-(Rz ^ 2)) =
            -((((Nat.succ k : ℕ) : ℝ) •
              Rz ^ (Nat.succ k + 1)))
        have hfirst : Rz ^ (k + 1) * Rz = Rz ^ (k + 2) := by
          simpa [Nat.add_assoc] using (pow_succ Rz (k + 1)).symm
        have hsecond : Rz ^ k * Rz ^ 2 = Rz ^ (k + 2) := by
          simpa using (pow_add Rz k 2).symm
        rw [neg_mul, Algebra.smul_mul_assoc, hfirst, mul_neg, hsecond]
        rw [Nat.cast_succ]
        module
      rw [hderiv] at hmul'
      exact hmul'

/-- The true real resolvent is `Cⁿ` in operator norm for every finite order on
an open common real resolvent region. -/
theorem continuousLinearMapRealResolvent_contDiffOn_nat
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (n : ℕ) :
    ContDiffOn ℝ n (continuousLinearMapRealResolvent A) U := by
  induction n with
  | zero =>
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (continuousLinearMapRealResolvent_continuousOn
          A U M hM hunit hnorm)
  | succ n ih =>
      apply (contDiffOn_succ_iff_deriv_of_isOpen
        (n := (n : ℕ∞ω)) hU).2
      refine ⟨continuousLinearMapRealResolvent_differentiableOn
        A U M hM hunit hnorm, ?_, ?_⟩
      · simp
      · have hsquare :
            ContDiffOn ℝ n
              (fun z =>
                (continuousLinearMapRealResolvent A z).comp
                  (continuousLinearMapRealResolvent A z)) U :=
          ih.clm_comp ih
        have hnegative := hsquare.neg
        apply hnegative.congr
        intro z hz
        simpa [pow_two, ContinuousLinearMap.mul_def] using
          (continuousLinearMapRealResolvent_deriv
            A U M hU hM hunit hnorm hz)

/-- The true real resolvent is smooth in operator norm on every open common
real resolvent region with a uniform inverse bound. -/
theorem continuousLinearMapRealResolvent_contDiffOn_infty
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M) :
    ContDiffOn ℝ ∞ (continuousLinearMapRealResolvent A) U :=
  contDiffOn_infty.2 fun n =>
    continuousLinearMapRealResolvent_contDiffOn_nat
      A U M hU hM hunit hnorm n

/-- Every iterated within-derivative is the signed factorial multiple of the
corresponding real resolvent composition power. -/
theorem continuousLinearMapRealResolvent_iteratedDerivWithin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (n : ℕ) {z : ℝ} (hz : z ∈ U) :
    iteratedDerivWithin n
        (continuousLinearMapRealResolvent A) U z =
      continuousLinearMapRealResolventSpectralCoefficient n •
        (continuousLinearMapRealResolvent A z) ^ (n + 1) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hcongr :
          derivWithin
              (iteratedDerivWithin n
                (continuousLinearMapRealResolvent A) U) U z =
            derivWithin
              (fun w =>
                continuousLinearMapRealResolventSpectralCoefficient n •
                  (continuousLinearMapRealResolvent A w) ^ (n + 1)) U z :=
        derivWithin_congr
          (fun w hw => ih (z := w) hw)
          (ih (z := z) hz)
      rw [hcongr]
      have hpow := continuousLinearMapRealResolvent_pow_hasDerivWithinAt
        A U M hM hunit hnorm (n + 1) hz
      have hscaled :
          HasDerivWithinAt
            (fun w =>
              continuousLinearMapRealResolventSpectralCoefficient n •
                (continuousLinearMapRealResolvent A w) ^ (n + 1))
            (continuousLinearMapRealResolventSpectralCoefficient n •
              (-(((n + 1 : ℕ) : ℝ) •
                (continuousLinearMapRealResolvent A z) ^ (n + 2)))) U z := by
        simpa only [Pi.smul_apply] using
          (HasDerivWithinAt.const_smul
            (𝕜 := ℝ) (R := ℝ) (F := V →L[ℝ] V)
            (continuousLinearMapRealResolventSpectralCoefficient n) hpow)
      let derivativeValue : V →L[ℝ] V :=
        continuousLinearMapRealResolventSpectralCoefficient n •
          (-(((n + 1 : ℕ) : ℝ) •
            (continuousLinearMapRealResolvent A z) ^ (n + 2)))
      have hfscaled :
          HasFDerivWithinAt
            (fun w =>
              continuousLinearMapRealResolventSpectralCoefficient n •
                (continuousLinearMapRealResolvent A w) ^ (n + 1))
            (toSpanSingleton ℝ derivativeValue) U z := by
        simpa [derivativeValue] using hscaled.hasFDerivWithinAt
      have hfderiv :
          fderivWithin ℝ
              (fun w =>
                continuousLinearMapRealResolventSpectralCoefficient n •
                  (continuousLinearMapRealResolvent A w) ^ (n + 1)) U z =
            toSpanSingleton ℝ derivativeValue :=
        hfscaled.fderivWithin (hU.uniqueDiffOn z hz)
      have hscaledDeriv :
          derivWithin
              (fun w =>
                continuousLinearMapRealResolventSpectralCoefficient n •
                  (continuousLinearMapRealResolvent A w) ^ (n + 1)) U z =
            derivativeValue := by
        unfold derivWithin
        rw [hfderiv]
        simp [derivativeValue]
      rw [hscaledDeriv]
      rw [continuousLinearMapRealResolventSpectralCoefficient_succ]
      simp [derivativeValue, smul_smul, Nat.add_assoc]

/-- Explicit ordinary all-order spectral derivative formula on an open common
real resolvent region. -/
theorem continuousLinearMapRealResolvent_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (n : ℕ) {z : ℝ} (hz : z ∈ U) :
    iteratedDeriv n (continuousLinearMapRealResolvent A) z =
      continuousLinearMapRealResolventSpectralCoefficient n •
        (continuousLinearMapRealResolvent A z) ^ (n + 1) := by
  calc
    iteratedDeriv n (continuousLinearMapRealResolvent A) z =
      iteratedDerivWithin n
        (continuousLinearMapRealResolvent A) U z :=
      (iteratedDerivWithin_of_isOpen
        (n := n) (f := continuousLinearMapRealResolvent A) hU hz).symm
    _ = continuousLinearMapRealResolventSpectralCoefficient n •
        (continuousLinearMapRealResolvent A z) ^ (n + 1) :=
      continuousLinearMapRealResolvent_iteratedDerivWithin
        A U M hU hM hunit hnorm n hz

/-- Every operator-norm spectral derivative obeys the factorial Cauchy-type
bound `n! M^(n+1)` on a uniformly bounded real resolvent region. -/
theorem continuousLinearMapRealResolvent_iteratedDeriv_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (n : ℕ) {z : ℝ} (hz : z ∈ U) :
    ‖iteratedDeriv n (continuousLinearMapRealResolvent A) z‖ ≤
      (n.factorial : ℝ) * M ^ (n + 1) := by
  rw [continuousLinearMapRealResolvent_iteratedDeriv
    A U M hU hM hunit hnorm n hz]
  let Rz := continuousLinearMapRealResolvent A z
  change
    ‖continuousLinearMapRealResolventSpectralCoefficient n • Rz ^ (n + 1)‖ ≤
      (n.factorial : ℝ) * M ^ (n + 1)
  calc
    ‖continuousLinearMapRealResolventSpectralCoefficient n • Rz ^ (n + 1)‖ ≤
        ‖continuousLinearMapRealResolventSpectralCoefficient n‖ *
          ‖Rz ^ (n + 1)‖ :=
      ContinuousLinearMap.opNorm_smul_le
        (continuousLinearMapRealResolventSpectralCoefficient n)
        (Rz ^ (n + 1))
    _ = (n.factorial : ℝ) * ‖Rz ^ (n + 1)‖ := by
      rw [continuousLinearMapRealResolventSpectralCoefficient_norm]
    _ ≤ (n.factorial : ℝ) * ‖Rz‖ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (norm_pow_le' Rz (by omega)) (by positivity)
    _ ≤ (n.factorial : ℝ) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg Rz)
          (by simpa [Rz, continuousLinearMapRealResolventNorm] using hnorm z hz)
          (n + 1))
        (by positivity)

/-- Smoothness, exact signed factorial derivatives, and their uniform
operator-norm bounds packaged together. -/
theorem continuousLinearMapRealResolventFactorialSpectralDerivative_package
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M) :
    ContDiffOn ℝ ∞ (continuousLinearMapRealResolvent A) U ∧
      (∀ (n : ℕ) {z : ℝ} (hz : z ∈ U),
        iteratedDeriv n (continuousLinearMapRealResolvent A) z =
          continuousLinearMapRealResolventSpectralCoefficient n •
            (continuousLinearMapRealResolvent A z) ^ (n + 1)) ∧
      ∀ (n : ℕ) {z : ℝ} (hz : z ∈ U),
        ‖iteratedDeriv n (continuousLinearMapRealResolvent A) z‖ ≤
          (n.factorial : ℝ) * M ^ (n + 1) := by
  refine ⟨continuousLinearMapRealResolvent_contDiffOn_infty
      A U M hU hM hunit hnorm, ?_, ?_⟩
  · intro n z hz
    exact continuousLinearMapRealResolvent_iteratedDeriv
      A U M hU hM hunit hnorm n hz
  · intro n z hz
    exact continuousLinearMapRealResolvent_iteratedDeriv_norm_le
      A U M hU hM hunit hnorm n hz

end MathlibAnalytic
end MGAP4D
