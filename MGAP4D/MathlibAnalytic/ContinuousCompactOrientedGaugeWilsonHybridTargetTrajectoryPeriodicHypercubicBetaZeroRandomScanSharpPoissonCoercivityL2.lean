import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonFixedPointAffineClassificationL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The beta-zero Poisson operator with domain restricted to the actual
Gibbs-vacuum orthogonal subspace. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalRestrictionL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2.subtypeL

/-- The restricted Poisson operator acts by the ambient operator `I - P`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalRestrictionL2_apply
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalRestrictionL2
        f =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The beta-zero Poisson operator has the sharp vacuum-orthogonal coercive
lower bound `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ((1 : ℝ) / 324) * ‖f‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply]
  have hContraction :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanHeatBathL2_apply_le_slem_mul_norm_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hSLEM :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 =
        (323 : ℝ) / 324 := by
    norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]
  rw [hSLEM] at hContraction
  have hReverse :=
    norm_sub_norm_le
      f
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        f)
  nlinarith [
    norm_nonneg f,
    norm_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        f)]

/-- Equivalent a priori form of sharp beta-zero Poisson coercivity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_le_324_mul_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖f‖ ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f‖ := by
  have hLower :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
      f hOrthogonal
  nlinarith [
    norm_nonneg f,
    norm_nonneg
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f)]

/-- Bundled form of the sharp coercive lower bound on `Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonVacuumOrthogonalRestrictionL2_apply
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 324) * ‖f‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalRestrictionL2
          f‖ := by
  change
    ((1 : ℝ) / 324) *
        ‖(f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
        f.property)

/-- A nonzero cardinality-one vector attains the Poisson factor `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        ((1 : ℝ) / 324) • f := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero
    with ⟨f, hfNe, hfSecond, hfOrthogonal⟩
  have hfEigen := hfSecond
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondEigenspaceL2,
    Module.End.mem_genEigenspace_one] at hfEigen
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
    hfEigen]
  calc
    f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2 •
          f =
      (1 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2) •
        f := by
      rw [sub_smul, one_smul]
    _ = ((1 : ℝ) / 324) • f := by
      norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSecondSpectralValueL2]

/-- The restricted Poisson coercive factor `1 / 324` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_randomScanPoissonVacuumOrthogonalRestrictionL2_apply_eq_inv_324_mul_norm :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalRestrictionL2
          f‖ =
        ((1 : ℝ) / 324) * ‖f‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨f, hfNe, hfOrthogonal, hPoisson⟩
  let fOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨f,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2 hfOrthogonal⟩
  have hfOrthogonalNe : fOrthogonal ≠ 0 := by
    intro hZero
    apply hfNe
    have hCoe := congrArg
      (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (x : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hZero
    simpa [fOrthogonal] using hCoe
  refine ⟨fOrthogonal, hfOrthogonalNe, ?_⟩
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ =
      ((1 : ℝ) / 324) * ‖f‖
  rw [hPoisson, norm_smul]
  norm_num

/-- The Green operator with domain restricted to `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2.comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2.subtypeL

/-- The restricted Green operator acts by the ambient Green operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenVacuumOrthogonalRestrictionL2_apply
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2
        f =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rfl

/-- The Green operator is a right inverse of the Poisson operator on
vacuum-orthogonal data. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_greenVacuumOrthogonalRestrictionL2_eq_subtype
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2
          f) =
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      f.property)
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hOrthogonal, zero_smul]
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) =
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply]
  simpa [hVacuumZero] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The restricted Green operator norm is at most `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_le_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2‖ ≤
      324 := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2.opNorm_le_bound
      (by norm_num)
  intro f
  have hFundamental :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2.le_opNorm
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_eq_324]
    at hFundamental
  simpa using hFundamental

/-- The cardinality-one vector attains the restricted Green norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_ge_324 :
    (324 : ℝ) ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenOperatorL2_apply_eq_324_smul
    with ⟨f, hfNe, hfOrthogonal, hGreen⟩
  let fOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨f,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2 hfOrthogonal⟩
  have hfOrthogonalNe : fOrthogonal ≠ 0 := by
    intro hZero
    apply hfNe
    have hCoe := congrArg
      (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (x : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hZero
    simpa [fOrthogonal] using hCoe
  have hNormPos : 0 < ‖fOrthogonal‖ := norm_pos_iff.mpr hfOrthogonalNe
  have hFundamental :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2.le_opNorm
      fOrthogonal
  have hGreenNorm :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2
          fOrthogonal‖ =
        324 * ‖fOrthogonal‖ := by
    change
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          f‖ =
        324 * ‖f‖
    rw [hGreen, norm_smul]
    norm_num
  rw [hGreenNorm] at hFundamental
  nlinarith [
    ContinuousLinearMap.opNorm_nonneg
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2]

/-- The exact restricted Green-operator norm is `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_eq_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2‖ =
      324 := by
  exact le_antisymm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_le_324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_ge_324

/-- Compact receipt for sharp beta-zero Poisson coercivity and its exact Green
right inverse on the Gibbs-vacuum orthogonal subspace. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpPoissonCoercivityL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 →
      ((1 : ℝ) / 324) * ‖f‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f‖) ∧
  (∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        ((1 : ℝ) / 324) • f) ∧
  ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2‖ =
      324 ∧
  ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenVacuumOrthogonalRestrictionL2
          f) =
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The sharp beta-zero Poisson-coercivity receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpPoissonCoercivityL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSharpPoissonCoercivityL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenVacuumOrthogonalRestrictionL2_eq_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_greenVacuumOrthogonalRestrictionL2_eq_subtype⟩

end

end MathlibAnalytic
end MGAP4D
