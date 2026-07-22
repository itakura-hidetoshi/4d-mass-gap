import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanSharpTwoSidedGreenKuboL2
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter Topology
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The full-space beta-zero vacuum-projector error operators form an
operator-norm summable Neumann series. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2 :
    Summable
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2 := by
  apply Summable.of_norm_bounded
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow
  intro n
  exact le_of_eq
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_323_div_324_pow
      n)

/-- For every Gibbs `L²` vector, the vacuum-centered random-scan orbit is
summable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    Summable
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f) := by
  let M : ℝ := ‖f‖
  have hGeom : Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n * M) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow.mul_right
      M
  apply Summable.of_norm_bounded hGeom
  intro n
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n‖ * ‖f‖ :=
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n).le_opNorm f
    _ = ((323 : ℝ) / 324) ^ n * M := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_323_div_324_pow]
      rfl

/-- The pointwise beta-zero Green linear map is the Neumann sum of the
vacuum-projector error orbit. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenLinearMapL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →ₗ[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure where
  toFun f :=
    ∑' n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f
  map_add' f g := by
    calc
      (∑' n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n (f + g)) =
        ∑' n : ℕ,
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n g) := by
          apply tsum_congr
          intro n
          rw [map_add]
      _ =
        (∑' n : ℕ,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n f) +
        ∑' n : ℕ,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n g := by
          rw [tsum_add
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2_apply
              f)
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2_apply
              g)]
  map_smul' c f := by
    calc
      (∑' n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n (c • f)) =
        ∑' n : ℕ,
          c •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n f := by
          apply tsum_congr
          intro n
          rw [map_smul]
      _ =
        c •
          ∑' n : ℕ,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n f := by
          rw [tsum_const_smul'']

/-- The pointwise Green linear map has the sharp universal upper bound
`324 * ‖f‖`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenLinearMapL2_apply_le_324_mul_norm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenLinearMapL2
        f‖ ≤
      324 * ‖f‖ := by
  let M : ℝ := ‖f‖
  have hApply :
      Summable
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n f) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2_apply
      f
  have hNorm :
      Summable
        (fun n : ℕ =>
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n f‖) :=
    hApply.norm
  have hGeom : Summable (fun n : ℕ => ((323 : ℝ) / 324) ^ n * M) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow.mul_right
      M
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenLinearMapL2
        f‖ =
      ‖∑' n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f‖ := rfl
    _ ≤
      ∑' n : ℕ,
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤
      ∑' n : ℕ, ((323 : ℝ) / 324) ^ n * M := by
        exact Summable.tsum_le_tsum
          (fun n => by
            calc
              ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
                  n f‖ ≤
                ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
                  n‖ * ‖f‖ :=
                (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
                  n).le_opNorm f
              _ = ((323 : ℝ) / 324) ^ n * M := by
                rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPowVacuumProjectorErrorL2_eq_323_div_324_pow]
                rfl)
          hNorm hGeom
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ n) * M := by
      rw [tsum_mul_right]
    _ = 324 * ‖f‖ := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324]
      rfl

/-- The beta-zero Green operator, defined as the continuous realization of the
pointwise Neumann series. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenLinearMapL2.mkContinuous
    324
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenLinearMapL2_apply_le_324_mul_norm

/-- The Green operator acts by the vacuum-centered Neumann series. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f =
      ∑' n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f := by
  rfl

/-- The beta-zero Green operator norm is at most `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_le_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2‖ ≤
      324 := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2.opNorm_le_bound
      (by norm_num)
  intro f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenLinearMapL2_apply_le_324_mul_norm
      f

/-- A nonzero cardinality-one vector is multiplied by exactly `324` by the
Green operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenOperatorL2_apply_eq_324_smul :
    ∃ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      f ≠ 0 ∧
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          f =
        (324 : ℝ) • f := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_secondEigenspaceL2_inner_vacuum_eq_zero
    with ⟨f, hfNe, hfSecond, hfOrthogonal⟩
  refine ⟨f, hfNe, hfOrthogonal, ?_⟩
  have hfCardinalityOne :
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCardinalityEigenspaceL2
        1 := by
    rw [←
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanSecondEigenspaceL2_eq_cardinalityOne]
    exact hfSecond
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hfOrthogonal, zero_smul]
  have hPointwise :
      ∀ n : ℕ,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n f =
          ((323 : ℝ) / 324) ^ n • f := by
    intro n
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply,
      hVacuumZero, sub_zero]
    have hAction :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
        1 n f hfCardinalityOne
    rw [hAction]
    norm_num
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_apply]
  calc
    (∑' n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        n f) =
      ∑' n : ℕ, ((323 : ℝ) / 324) ^ n • f := by
        apply tsum_congr
        intro n
        exact hPointwise n
    _ = (∑' n : ℕ, ((323 : ℝ) / 324) ^ n) • f :=
      Summable.tsum_smul_const
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_323_div_324_pow
        f
    _ = (324 : ℝ) • f := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_tsum_323_div_324_pow_eq_324]

/-- The exact beta-zero Green-operator norm is `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_eq_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2‖ =
      324 := by
  apply le_antisymm
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_le_324
  · rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenOperatorL2_apply_eq_324_smul
      with ⟨f, hfNe, _, hGreen⟩
    have hFundamental :=
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2.le_opNorm
        f
    have hGreenNorm :
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
            f‖ =
          324 * ‖f‖ := by
      rw [hGreen, norm_smul]
      norm_num
    rw [hGreenNorm] at hFundamental
    have hfNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
    nlinarith [
      ContinuousLinearMap.opNorm_nonneg
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2]

/-- Applying one beta-zero random-scan step to the `n`th centered error gives
the `(n+1)`st centered error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_apply_randomScanPowVacuumProjectorErrorL2
    (n : ℕ)
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
          n f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
        (n + 1) f := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowVacuumProjectorErrorL2_apply]
  rw [pow_succ']
  rfl

/-- The Green operator solves the centered beta-zero Poisson equation
pointwise: `(I - P) G f = f - E₀ f`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
        f -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  have hSummable :
      Summable
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            n f) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2_apply
      f
  have hShiftHasSum :
      HasSum
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            (n + 1) f)
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (∑' n : ℕ,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n f)) := by
    simpa only [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_apply_randomScanPowVacuumProjectorErrorL2] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2.hasSum
        hSummable.hasSum
  have hShift :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (∑' n : ℕ,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
              n f) =
        ∑' n : ℕ,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2
            (n + 1) f := by
    exact hShiftHasSum.tsum_eq.symm
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_apply,
    hShift]
  rw [hSummable.tsum_eq_zero_add]
  simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2]

/-- Operator form of the centered beta-zero Poisson equation:
`(I - P) ∘ G = I - E₀`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperator_comp_greenOperatorL2_eq_centeringOperator :
    ((ContinuousLinearMap.id ℝ
          (Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2).comp
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 =
    (ContinuousLinearMap.id ℝ
        (Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) -
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 := by
  ext f
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          f -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
            f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered
      f

/-- Compact receipt for the exact beta-zero Green operator and centered
Poisson equation. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactGreenOperatorPoissonL2Receipt :
    Prop :=
  Summable
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPowVacuumProjectorErrorL2 ∧
  ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2‖ =
      324 ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
          f -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
            f) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f)

/-- The exact beta-zero Green-operator/Poisson receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactGreenOperatorPoissonL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanExactGreenOperatorPoissonL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_summable_randomScanPowVacuumProjectorErrorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_eq_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered⟩

end

end MathlibAnalytic
end MGAP4D
