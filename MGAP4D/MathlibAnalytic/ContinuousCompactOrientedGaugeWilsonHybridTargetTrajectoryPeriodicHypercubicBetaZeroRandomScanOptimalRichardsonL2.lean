import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanCenteredGreenCovarianceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Exact quadratic expansion of one Richardson error step for a continuous
linear endomorphism on a real inner-product space. -/
theorem continuousLinearMap_norm_sub_smul_apply_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau : ℝ)
    (x : E) :
    ‖x - tau • A x‖ ^ 2 =
      ‖x‖ ^ 2 -
        2 * tau * inner ℝ (A x) x +
        tau ^ 2 * ‖A x‖ ^ 2 := by
  calc
    ‖x - tau • A x‖ ^ 2 =
        inner ℝ (x - tau • A x) (x - tau • A x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ =
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 * ‖A x‖ ^ 2 := by
      simp only [
        inner_sub_left,
        inner_sub_right,
        real_inner_smul_left,
        real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [real_inner_comm x (A x)]
      ring

/-- A finite orthogonal spectral sum with coefficients in `[m, 1]` satisfies
the sharp secant inequality for the square function. -/
theorem finset_norm_sum_smul_sq_le_secant_inner_sub_mul_norm_sum_sq_of_pairwise_inner_eq_zero
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → V)
    (a : ι → ℝ)
    (m : ℝ)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0)
    (hNonneg : ∀ i ∈ s, 0 ≤ a i)
    (hLower : ∀ i ∈ s, m ≤ a i)
    (hUpper : ∀ i ∈ s, a i ≤ 1) :
    ‖∑ i ∈ s, a i • v i‖ ^ 2 ≤
      (1 + m) *
          inner ℝ (∑ i ∈ s, a i • v i) (∑ i ∈ s, v i) -
        m * ‖∑ i ∈ s, v i‖ ^ 2 := by
  have hWeightedOrth :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℝ (a i • v i) (a j • v j) = 0 := by
    intro i hi j hj hij
    rw [real_inner_smul_left, real_inner_smul_right,
      hOrth i hi j hj hij, mul_zero, mul_zero]
  have hWeightedNorm :=
    finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      s (fun i => a i • v i) hWeightedOrth
  have hInner :=
    finset_inner_sum_smul_sum_eq_sum_mul_norm_sq_of_pairwise_inner_eq_zero
      s v a hOrth
  have hUnweightedNorm :=
    finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      s v hOrth
  rw [hWeightedNorm, hInner, hUnweightedNorm]
  calc
    ∑ i ∈ s, ‖a i • v i‖ ^ 2 ≤
        ∑ i ∈ s, (((1 + m) * a i - m) * ‖v i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hNonneg i hi)]
      have hCoeff :
          a i ^ 2 ≤ (1 + m) * a i - m := by
        have hProduct :
            0 ≤ (a i - m) * (1 - a i) :=
          mul_nonneg
            (sub_nonneg.mpr (hLower i hi))
            (sub_nonneg.mpr (hUpper i hi))
        nlinarith
      calc
        (a i * ‖v i‖) ^ 2 = a i ^ 2 * ‖v i‖ ^ 2 := by ring
        _ ≤ ((1 + m) * a i - m) * ‖v i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hCoeff (sq_nonneg ‖v i‖)
    _ =
        ∑ i ∈ s,
          ((1 + m) * (a i * ‖v i‖ ^ 2) - m * ‖v i‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ =
        (1 + m) * (∑ i ∈ s, a i * ‖v i‖ ^ 2) -
          m * (∑ i ∈ s, ‖v i‖ ^ 2) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]

/-- Generic squared Richardson contraction from the sharp secant inequality for
an operator whose spectrum lies in `[m, 1]`. -/
theorem continuousLinearMap_richardson_sq_contraction_of_secant
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (m tau q : ℝ)
    (hTauSq : 0 ≤ tau ^ 2)
    (hCancel : tau ^ 2 * (1 + m) - 2 * tau = 0)
    (hBalance : 1 - tau ^ 2 * m = q ^ 2)
    (hSecant :
      ∀ x : E,
        ‖A x‖ ^ 2 ≤
          (1 + m) * inner ℝ (A x) x - m * ‖x‖ ^ 2)
    (x : E) :
    ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := by
  have hSecantMul :
      tau ^ 2 * ‖A x‖ ^ 2 ≤
        tau ^ 2 *
          ((1 + m) * inner ℝ (A x) x - m * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (hSecant x) hTauSq
  calc
    ‖x - tau • A x‖ ^ 2 =
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 * ‖A x‖ ^ 2 :=
      continuousLinearMap_norm_sub_smul_apply_sq A tau x
    _ ≤
        ‖x‖ ^ 2 -
          2 * tau * inner ℝ (A x) x +
          tau ^ 2 *
            ((1 + m) * inner ℝ (A x) x - m * ‖x‖ ^ 2) := by
      nlinarith
    _ =
        (1 - tau ^ 2 * m) * ‖x‖ ^ 2 +
          (tau ^ 2 * (1 + m) - 2 * tau) * inner ℝ (A x) x := by
      ring
    _ = q ^ 2 * ‖x‖ ^ 2 := by
      rw [hCancel, zero_mul, add_zero, hBalance]

/-- A squared contraction with a nonnegative factor gives the ordinary norm
contraction. -/
theorem continuousLinearMap_richardson_contraction_of_sq
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau q : ℝ)
    (hq : 0 ≤ q)
    (hSq :
      ∀ x : E,
        ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2)
    (x : E) :
    ‖x - tau • A x‖ ≤ q * ‖x‖ := by
  have hSq' :
      ‖x - tau • A x‖ ^ 2 ≤
        (q * ‖x‖) ^ 2 := by
    calc
      ‖x - tau • A x‖ ^ 2 ≤ q ^ 2 * ‖x‖ ^ 2 := hSq x
      _ = (q * ‖x‖) ^ 2 := by ring
  have hLeft : 0 ≤ ‖x - tau • A x‖ :=
    norm_nonneg _
  have hRight : 0 ≤ q * ‖x‖ :=
    mul_nonneg hq (norm_nonneg x)
  nlinarith

/-- A Richardson error endomorphism acts by the scalar error multiplier on any
real eigenvector. -/
theorem continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau c : ℝ)
    (x : E)
    (hAction : A x = c • x) :
    (ContinuousLinearMap.id ℝ E - tau • A) x =
      (1 - tau * c) • x := by
  change x - tau • A x = (1 - tau * c) • x
  rw [hAction, smul_smul]
  module

/-- The actual beta-zero Poisson operator satisfies the sharp square-function
secant inequality associated with the interval `[1 / 324, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_secant_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ ^ 2 ≤
      ((325 : ℝ) / 324) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              f)
            f -
        ((1 : ℝ) / 324) * ‖f‖ ^ 2 := by
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_positive_fluctuationCardinalityProjectorL2_apply_eq_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hAction :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        ∑ k ∈ Finset.range 324,
          (((k + 1 : ℕ) : ℝ) / 324) •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (∑ k ∈ Finset.range 324,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        rw [hDecomposition]
      _ = ∑ k ∈ Finset.range 324,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        simp only [map_sum]
      _ = ∑ k ∈ Finset.range 324,
          (((k + 1 : ℕ) : ℝ) / 324) •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
        apply Finset.sum_congr rfl
        intro k hk
        have hUpper : k + 1 ≤ 324 := by
          simp only [Finset.mem_range] at hk
          omega
        let component : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f
        have hRandomPow :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
            (k + 1) 1 component
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_mem_randomScanCardinalityEigenspaceL2
              (k + 1) hUpper f)
        have hRandom :
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
                component =
              (1 - (((k + 1 : ℕ) : ℝ) / 324)) • component := by
          simpa [component] using hRandomPow
        change
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              component =
            (((k + 1 : ℕ) : ℝ) / 324) • component
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
          hRandom]
        rw [sub_smul, one_smul]
        abel
  have hFamilyOrth :
      ∀ i ∈ Finset.range 324, ∀ j ∈ Finset.range 324, i ≠ j →
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (i + 1) f)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (j + 1) f) = 0 := by
    intro i _hi j _hj hij
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_same_input_eq_zero_of_ne
        (i + 1) (j + 1) (by omega) f
  have hCoeffNonneg :
      ∀ k ∈ Finset.range 324,
        0 ≤ (((k + 1 : ℕ) : ℝ) / 324) := by
    intro k _hk
    positivity
  have hCoeffLower :
      ∀ k ∈ Finset.range 324,
        ((1 : ℝ) / 324) ≤ (((k + 1 : ℕ) : ℝ) / 324) := by
    intro k _hk
    have hLowerNat : 1 ≤ k + 1 := by omega
    have hLowerReal : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hLowerNat
    nlinarith
  have hCoeffUpper :
      ∀ k ∈ Finset.range 324,
        (((k + 1 : ℕ) : ℝ) / 324) ≤ 1 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hUpperNat : k + 1 ≤ 324 := by omega
    have hUpperReal : (((k + 1 : ℕ) : ℝ) ≤ 324) := by
      exact_mod_cast hUpperNat
    nlinarith
  have hSecant :=
    finset_norm_sum_smul_sq_le_secant_inner_sub_mul_norm_sum_sq_of_pairwise_inner_eq_zero
      (s := Finset.range 324)
      (v := fun k =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f)
      (a := fun k => (((k + 1 : ℕ) : ℝ) / 324))
      ((1 : ℝ) / 324)
      hFamilyOrth hCoeffNonneg hCoeffLower hCoeffUpper
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ ^ 2 =
      ‖∑ k ∈ Finset.range 324,
        (((k + 1 : ℕ) : ℝ) / 324) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ ^ 2 :=
      congrArg (fun g => ‖g‖ ^ 2) hAction
    _ ≤
      (1 + ((1 : ℝ) / 324)) *
          inner ℝ
            (∑ k ∈ Finset.range 324,
              (((k + 1 : ℕ) : ℝ) / 324) •
                periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                  (k + 1) f)
            (∑ k ∈ Finset.range 324,
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                (k + 1) f) -
        ((1 : ℝ) / 324) *
          ‖∑ k ∈ Finset.range 324,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f‖ ^ 2 := hSecant
    _ =
      ((325 : ℝ) / 324) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              f)
            f -
        ((1 : ℝ) / 324) * ‖f‖ ^ 2 := by
      rw [← hAction, hDecomposition]
      norm_num

/-- The exact optimal constant step for the beta-zero Poisson Richardson
iteration. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 :
    ℝ :=
  (648 : ℝ) / 325

/-- The exact minimax contraction factor for the beta-zero Poisson Richardson
iteration. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 :
    ℝ :=
  (323 : ℝ) / 325

/-- The Richardson error endomorphism `I - tau A` on the actual beta-zero
Gibbs-vacuum orthogonal sector. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
    (tau : ℝ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  ContinuousLinearMap.id ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 -
    tau •
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2

/-- Pointwise action of the beta-zero Richardson error endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply
    (tau : ℝ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        tau e =
      e -
        tau •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            e := by
  rfl

/-- Internal form of the sharp beta-zero Poisson secant inequality. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_secant
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        e‖ ^ 2 ≤
      ((325 : ℝ) / 324) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              e)
            e -
        ((1 : ℝ) / 324) * ‖e‖ ^ 2 := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (e : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (e : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      e.property
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (e : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      ((325 : ℝ) / 324) *
          inner ℝ
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              (e : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
            (e : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
        ((1 : ℝ) / 324) *
          ‖(e : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_secant_of_inner_vacuum_eq_zero
      (e : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hOrthogonal

/-- The optimal beta-zero Richardson step has squared contraction factor
`(323 / 325)^2`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_sq_contraction
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        e‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ 2 *
        ‖e‖ ^ 2 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply]
  exact
    continuousLinearMap_richardson_sq_contraction_of_secant
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      ((1 : ℝ) / 324)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
      (by
        norm_num [
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2])
      (by
        norm_num [
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2])
      (by
        norm_num [
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2])
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_secant
      e

/-- The optimal beta-zero Richardson error map contracts every centered error by
exact factor at most `323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        e‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
        ‖e‖ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply]
  apply
    continuousLinearMap_richardson_contraction_of_sq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]
  · intro x
    simpa only [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_sq_contraction
        x
  · exact e

/-- Operator-norm upper bound for the optimal Richardson error map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_le :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2).opNorm_le_bound
  · norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]
  · intro e
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
        e

/-- A cardinality-one mode attains the positive Richardson endpoint
`323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply,
    hAction]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  module

/-- A terminal-cardinality mode attains the negative Richardson endpoint
`-323 / 325`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_neg_factor_smul :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        (-periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2) •
          e := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply,
    hAction]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  module

/-- The optimal Richardson contraction factor is attained in norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_optimalRichardsonErrorEndL2_apply_eq_factor_mul_norm :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e‖ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
          ‖e‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul
    with ⟨e, heNe, hAction⟩
  refine ⟨e, heNe, ?_⟩
  rw [hAction, norm_smul, Real.norm_eq_abs]
  norm_num [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]

/-- Exact operator norm of the optimal beta-zero Richardson error map. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_eq :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_le
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_optimalRichardsonErrorEndL2_apply_eq_factor_mul_norm
      with ⟨e, heNe, hNorm⟩
    have hFundamental :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2).le_opNorm
        e
    rw [hNorm] at hFundamental
    have hNormPos : 0 < ‖e‖ := norm_pos_iff.mpr heNe
    nlinarith [
      ContinuousLinearMap.opNorm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2)]

/-- Every uniform Richardson contraction constant, at every real step, is at
least `323 / 325`; hence the displayed step is globally minimax-optimal over
constant-step Richardson maps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonFactor_le_of_uniform_bound
    (tau C : ℝ)
    (hUniform :
      ∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            tau e‖ ≤
          C * ‖e‖) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ≤
      C := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨eLow, heLowNe, hLowAction⟩
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨eHigh, heHighNe, hHighAction⟩
  have hLowRichardson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          tau eLow =
        (1 - tau * ((1 : ℝ) / 324)) • eLow := by
    exact
      continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        tau ((1 : ℝ) / 324) eLow hLowAction
  have hHighRichardson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          tau eHigh =
        (1 - tau) • eHigh := by
    have hRaw :=
      continuousLinearMap_richardson_apply_eq_smul_of_apply_eq_smul
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        tau 1 eHigh
        (by simpa using hHighAction)
    simpa using hRaw
  have hLowBound := hUniform eLow
  have hHighBound := hUniform eHigh
  rw [hLowRichardson, norm_smul, Real.norm_eq_abs] at hLowBound
  rw [hHighRichardson, norm_smul, Real.norm_eq_abs] at hHighBound
  have hLowNormPos : 0 < ‖eLow‖ := norm_pos_iff.mpr heLowNe
  have hHighNormPos : 0 < ‖eHigh‖ := norm_pos_iff.mpr heHighNe
  have hLowAbs :
      |1 - tau * ((1 : ℝ) / 324)| ≤ C := by
    nlinarith
  have hHighAbs :
      |1 - tau| ≤ C := by
    nlinarith
  have hLowUpper :
      1 - tau * ((1 : ℝ) / 324) ≤ C :=
    (abs_le.mp hLowAbs).2
  have hHighLower :
      -C ≤ 1 - tau :=
    (abs_le.mp hHighAbs).1
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  nlinarith

/-- Recursive optimal Richardson propagation of an initial centered error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2 :
    ℕ →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
  | 0 => fun e => e
  | Nat.succ n => fun e =>
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n e)

/-- Geometric error estimate for every finite number of optimal Richardson
steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
    (n : ℕ)
    (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n e‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖e‖ := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      calc
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n e)‖ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n e‖ :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
            _
        _ ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
              ‖e‖) :=
          mul_le_mul_of_nonneg_left ih
            (by
              norm_num [
                periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2])
        _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ Nat.succ n *
            ‖e‖ := by
          rw [pow_succ]
          ring

/-- The exact beta-zero Richardson factor is strictly between zero and one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ∈
      Set.Ioo 0 1 := by
  constructor <;>
    norm_num [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2]

/-- Structured receipt for the exact optimal beta-zero Richardson iteration. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt :
    Prop where
  step_size :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 =
      (648 : ℝ) / 325
  contraction_factor :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 =
      (323 : ℝ) / 325
  contraction :
    ∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 *
          ‖e‖
  exact_operator_norm :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2‖ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
  positive_endpoint_attained :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 •
          e
  negative_endpoint_attained :
    ∃ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      e ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          e =
        (-periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2) •
          e
  minimax_optimal :
    ∀ tau C : ℝ,
      (∀ e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            tau e‖ ≤
          C * ‖e‖) →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ≤
        C
  finite_iteration_bound :
    ∀ (n : ℕ)
      (e : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n e‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖e‖

/-- The exact optimal beta-zero Richardson receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonL2Receipt := by
  exact
    { step_size := rfl
      contraction_factor := rfl
      contraction :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonErrorEndL2_norm_contraction
      exact_operator_norm :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorEndL2_eq
      positive_endpoint_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_factor_smul
      negative_endpoint_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_optimalRichardsonErrorEndL2_apply_eq_neg_factor_smul
      minimax_optimal :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonFactor_le_of_uniform_bound
      finite_iteration_bound :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le }

end

end MathlibAnalytic
end MGAP4D
