import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroVacuumOrthogonalCardinalityDecompositionL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanNStepSpectralDecayL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite pairwise-orthogonal family remains contractive after scalar
weighting when every scalar modulus is bounded by a common nonnegative factor. -/
theorem finset_norm_sum_smul_le_mul_norm_sum_of_pairwise_inner_eq_zero
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → V)
    (a : ι → ℝ)
    (r : ℝ)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0)
    (hCoeff : ∀ i ∈ s, |a i| ≤ r)
    (hr : 0 ≤ r) :
    ‖∑ i ∈ s, a i • v i‖ ≤ r * ‖∑ i ∈ s, v i‖ := by
  have hScaledOrth :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℝ (a i • v i) (a j • v j) = 0 := by
    intro i hi j hj hij
    rw [real_inner_smul_left, real_inner_smul_right,
      hOrth i hi j hj hij]
    simp
  have hScaledPythagoras :=
    finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      s (fun i => a i • v i) hScaledOrth
  have hOriginalPythagoras :=
    finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      s v hOrth
  have hTerm :
      ∀ i ∈ s, ‖a i • v i‖ ^ 2 ≤ r ^ 2 * ‖v i‖ ^ 2 := by
    intro i hi
    have hScalarSq : |a i| ^ 2 ≤ r ^ 2 := by
      nlinarith [hCoeff i hi, abs_nonneg (a i)]
    calc
      ‖a i • v i‖ ^ 2 = (|a i| * ‖v i‖) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |a i| ^ 2 * ‖v i‖ ^ 2 := by ring
      _ ≤ r ^ 2 * ‖v i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hScalarSq (sq_nonneg ‖v i‖)
  have hSumLe :
      (∑ i ∈ s, ‖a i • v i‖ ^ 2) ≤
        r ^ 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := by
    calc
      (∑ i ∈ s, ‖a i • v i‖ ^ 2) ≤
          ∑ i ∈ s, r ^ 2 * ‖v i‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hTerm i hi
      _ = r ^ 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hSquare :
      ‖∑ i ∈ s, a i • v i‖ ^ 2 ≤
        (r * ‖∑ i ∈ s, v i‖) ^ 2 := by
    calc
      ‖∑ i ∈ s, a i • v i‖ ^ 2 =
          ∑ i ∈ s, ‖a i • v i‖ ^ 2 := hScaledPythagoras
      _ ≤ r ^ 2 * ∑ i ∈ s, ‖v i‖ ^ 2 := hSumLe
      _ = r ^ 2 * ‖∑ i ∈ s, v i‖ ^ 2 := by
        rw [← hOriginalPythagoras]
      _ = (r * ‖∑ i ∈ s, v i‖) ^ 2 := by ring
  have hLeftNonneg : 0 ≤ ‖∑ i ∈ s, a i • v i‖ := norm_nonneg _
  have hRightNonneg : 0 ≤ r * ‖∑ i ∈ s, v i‖ :=
    mul_nonneg hr (norm_nonneg _)
  nlinarith

/-- Every cardinality-projector component belongs to its corresponding actual
beta-zero random-scan eigenspace. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_mem_randomScanCardinalityEigenspaceL2
    (k : ℕ)
    (hk : k ≤ 324)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        k f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        k := by
  rw [←
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_randomScanCardinalityEigenspaceL2
      k hk]
  exact ⟨f, rfl⟩

/-- Every vacuum-orthogonal actual beta-zero Gibbs `L²` vector contracts under
`n` random-scan steps by at most the exact nonstationary SLEM factor
`(323 / 324)^n`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_inner_vacuum_eq_zero
    (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        f‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ := by
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_positive_fluctuationCardinalityProjectorL2_apply_eq_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hAction :
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f =
        ∑ k ∈ Finset.range 324,
          (1 - ((k + 1 : ℕ) : ℝ) / 324) ^ n •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
    calc
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f =
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          (∑ k ∈ Finset.range 324,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        rw [hDecomposition]
      _ = ∑ k ∈ Finset.range 324,
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        simp only [map_sum]
      _ = ∑ k ∈ Finset.range 324,
          (1 - ((k + 1 : ℕ) : ℝ) / 324) ^ n •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
        apply Finset.sum_congr rfl
        intro k hk
        have hUpper : k + 1 ≤ 324 := by
          simp only [Finset.mem_range] at hk
          omega
        exact
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
            (k + 1) n
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f)
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_mem_randomScanCardinalityEigenspaceL2
              (k + 1) hUpper f)
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
  have hCoeff :
      ∀ k ∈ Finset.range 324,
        |(1 - ((k + 1 : ℕ) : ℝ) / 324) ^ n| ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n := by
    intro k hk
    simp only [Finset.mem_range] at hk
    let kFin : Fin 325 := ⟨k + 1, by omega⟩
    have hkNe : kFin.1 ≠ 0 := by
      simp [kFin]
    have hAbs :
        |1 - ((k + 1 : ℕ) : ℝ) / 324| ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 := by
      simpa [kFin,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2] using
        fin_affine_grid_abs_le_second_of_ne_zero 324 (by omega) kFin hkNe
    have hPow :=
      real_pow_le_pow_of_nonneg
        (abs_nonneg (1 - ((k + 1 : ℕ) : ℝ) / 324)) hAbs n
    simpa [abs_pow,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2] using
      hPow
  have hWeightedBound :=
    finset_norm_sum_smul_le_mul_norm_sum_of_pairwise_inner_eq_zero
      (s := Finset.range 324)
      (v := fun k =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f)
      (a := fun k => (1 - ((k + 1 : ℕ) : ℝ) / 324) ^ n)
      (r := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n)
      hFamilyOrth hCoeff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2_nonneg n)
  calc
    ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
        f‖ =
      ‖∑ k ∈ Finset.range 324,
        (1 - ((k + 1 : ℕ) : ℝ) / 324) ^ n •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ := congrArg norm hAction
    _ ≤ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖∑ k ∈ Finset.range 324,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ := hWeightedBound
    _ = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
        ‖f‖ := by
      rw [hDecomposition]

/-- One-step form of the full vacuum-orthogonal contraction. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanHeatBathL2_apply_le_slem_mul_norm_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 * ‖f‖ := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_inner_vacuum_eq_zero
      1 f hOrthogonal

/-- Compact receipt for the exact finite-time beta-zero random-scan contraction
on the full vacuum-orthogonal Gibbs `L²` subspace. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalRandomScanNStepContractionL2Receipt :
    Prop :=
  ∀ (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f = 0 →
      ‖(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 ^ n)
          f‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanNStepSLEML2 n *
          ‖f‖

/-- The full vacuum-orthogonal beta-zero random-scan `n`-step contraction receipt
is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalRandomScanNStepContractionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalRandomScanNStepContractionL2Receipt := by
  intro n f hOrthogonal
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowL2_apply_le_nStepSLEM_mul_norm_of_inner_vacuum_eq_zero
      n f hOrthogonal

end

end MathlibAnalytic
end MGAP4D
