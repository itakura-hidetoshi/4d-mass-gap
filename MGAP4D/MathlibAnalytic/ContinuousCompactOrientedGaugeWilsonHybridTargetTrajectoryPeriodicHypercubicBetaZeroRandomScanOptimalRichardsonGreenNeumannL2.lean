import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonCertifiedSolverL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The canonical centered Poisson solution of an already centered datum is the
internal centered Green inverse applied to that datum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_subtype_eq_centeredGreen
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        g := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringToVacuumOrthogonalL2_apply_subtype_eq_self]

/-- For an already centered datum, the centered Poisson residual at the zero
approximation is exactly the datum itself. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_subtype_zero_eq_self
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        0 =
      g := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_subtype_eq_centeredGreen,
    sub_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]

/-- The finite optimal-Richardson Neumann approximation to the internal centered
Green inverse. It is the natural solution iterate from the zero initial guess. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
    (g : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    n
    0

/-- The zeroth Green Neumann partial sum is zero. -/
@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_zero
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        0 g =
      0 := by
  rfl

/-- Successive finite Green Neumann approximants add the next optimal Richardson
error mode `tau_* R_*^n g`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_succ
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        (Nat.succ n) g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
            n g := by
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (Nat.succ n)
        0 =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          n
          0 +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
            n g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2]
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          n
          0 +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
            (g : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
              (g : Lp ℝ 2
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
              n
              0) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          n
          0 +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
            n g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionIterate_eq_errorIterate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_subtype_zero_eq_self]

/-- Exact finite Neumann-sum representation
`N_n g = tau_* sum_{k<n} R_*^k g`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_eq_sum
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
        n g =
      ∑ k ∈ Finset.range n,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
            k g := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_succ,
        ih,
        Finset.sum_range_succ]

/-- Exact Green truncation remainder: the missing tail is the `n`th optimal
Richardson error iterate applied to the exact centered Green solution. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_eq_errorIterate
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g) := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_subtype_eq_centeredGreen,
    sub_zero] using
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionIterateL2
      (g : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      n
      0)

/-- Exact finite truncation residual: the bundled residual of the `n`th Green
Neumann partial sum is `R_*^n g`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_eq_errorIterate
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n g := by
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_subtype_zero_eq_self] using
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionIterate_eq_errorIterate
      (g : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      n
      0)

/-- Pointwise geometric error bound for the finite Green Neumann approximation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g‖ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_eq_errorIterate]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
      n
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        g)

/-- Uniform finite Green Neumann truncation error with the exact inverse norm
constant `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g‖ ≤
      324 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖g‖ := by
  have hPointwise :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le
      n g
  have hGreen :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2.le_opNorm
      g
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324]
    at hGreen
  have hPowNonneg :
      0 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n :=
    pow_nonneg
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      n
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g‖ := hPointwise
    _ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        (324 * ‖g‖) :=
      mul_le_mul_of_nonneg_left hGreen hPowNonneg
    _ =
      324 *
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖g‖ := by ring

/-- The finite Green Neumann truncation residual contracts geometrically. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
    (n : ℕ)
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        (g : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g)‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖g‖ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_eq_errorIterate]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
      n g

/-- The finite optimal-Richardson Green Neumann sums converge strongly to the
exact centered Green inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_tendsto_centeredGreen
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g)
      atTop
      (nhds
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hPow :
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
  have hEnvelope :
      Tendsto
        (fun n : ℕ =>
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
              g‖ *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hPow)
  exact
    squeeze_zero
      (fun n => norm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g))
      (fun n => by
        simpa only [norm_sub_rev, mul_comm] using
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le
            n g)
      hEnvelope

/-- The residuals of the finite Green Neumann sums converge strongly to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_tendsto_zero
    (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g))
      atTop
      (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hPow :
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (le_of_lt
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
  have hEnvelope :
      Tendsto
        (fun n : ℕ =>
          ‖g‖ *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hPow)
  exact
    squeeze_zero
      (fun n => norm_nonneg
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g)))
      (fun n => by
        simpa only [mul_comm] using
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
            n g)
      hEnvelope

/-- Structured receipt for the finite optimal-Richardson Neumann representation
of the centered Green inverse and its strong convergence. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannL2Receipt :
    Prop where
  finite_sum :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
          n g =
        ∑ k ∈ Finset.range n,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              k g
  exact_remainder :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g)
  exact_residual :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n g
  uniform_error :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g‖ ≤
        324 *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖g‖
  residual_geometric :
    ∀ (n : ℕ)
      (g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          (g : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g)‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖g‖
  strong_limit :
    ∀ g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
            n g)
        atTop
        (nhds
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            g))
  residual_limit :
    ∀ g : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      Tendsto
        (fun n : ℕ =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
            (g : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
              n g))
        atTop
        (nhds 0)

/-- The finite optimal-Richardson Green Neumann representation and convergence
receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannL2Receipt := by
  exact
    { finite_sum :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_eq_sum
      exact_remainder :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_eq_errorIterate
      exact_residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_eq_errorIterate
      uniform_error :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
      residual_geometric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
      strong_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_tendsto_centeredGreen
      residual_limit :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_tendsto_zero }

end

end MathlibAnalytic
end MGAP4D
