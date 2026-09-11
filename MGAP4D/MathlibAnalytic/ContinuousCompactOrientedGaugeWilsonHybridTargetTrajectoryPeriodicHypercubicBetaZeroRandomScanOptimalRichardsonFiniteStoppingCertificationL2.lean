import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonGreenNeumannOperatorNormL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanGreenPoissonEnergyCauchySchwarzEqualityL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- A real sequence converging to zero eventually lies below every positive
threshold, with an explicit finite starting index. -/
theorem real_tendsto_zero_exists_forall_ge_lt
    (u : ℕ → ℝ)
    (hu : Tendsto u atTop (nhds 0))
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, u n < epsilon := by
  have hEventually : ∀ᶠ n : ℕ in atTop, u n ∈ Iio epsilon :=
    hu.eventually (Iio_mem_nhds hEpsilon)
  simpa only [mem_Iio] using (eventually_atTop.1 hEventually)

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "H₀" =>
  Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
local notation "G₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
local notation "Nvec₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannPartialSumL2
local notation "Rem₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannRemainderEndL2
local notation "Def₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonGreenNeumannInverseDefectEndL2
local notation "Res₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
local notation "GE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenEnergyNormL2
local notation "PE₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonEnergyNormL2
local notation "Φ₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFenchelValueL2

/-- The pointwise ambient error magnitude of the finite Green--Neumann solver
converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_tendsto_zero
    (g : Ω₀) :
    Tendsto
      (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖)
      atTop
      (nhds 0) := by
  have hStrong :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_tendsto_centeredGreen
      g
  rw [tendsto_iff_norm_sub_tendsto_zero] at hStrong
  exact hStrong

/-- The norm of the bundled finite Green--Neumann residual converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_tendsto_zero
    (g : Ω₀) :
    Tendsto
      (fun n : ℕ =>
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖)
      atTop
      (nhds 0) := by
  have hStrong :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_tendsto_zero
      g
  rw [tendsto_iff_norm_sub_tendsto_zero] at hStrong
  simpa only [sub_zero] using hStrong

/-- The Poisson-energy magnitude of the finite Green--Neumann solution error
converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_tendsto_zero
    (g : Ω₀) :
    Tendsto
      (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g))
      atTop
      (nhds 0) := by
  have hErrorNorm :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_tendsto_zero
      g
  exact
    squeeze_zero
      (fun n =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
          (Nvec₀ n g - G₀ g))
      (fun n =>
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
          (Nvec₀ n g - G₀ g)).2)
      hErrorNorm

/-- The exact Poisson-side Fenchel gap of the finite Green--Neumann solver
converges to zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_tendsto_zero
    (g : Ω₀) :
    Tendsto
      (fun n : ℕ =>
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g))
      atTop
      (nhds 0) := by
  have hEnergy :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_tendsto_zero
      g
  have hSquare :
      Tendsto
        (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g) ^ 2)
        atTop
        (nhds 0) := by
    simpa only [pow_two, zero_mul] using hEnergy.mul hEnergy
  have hHalfSquare :
      Tendsto
        (fun n : ℕ =>
          ((1 : ℝ) / 2) * PE₀ (Nvec₀ n g - G₀ g) ^ 2)
        atTop
        (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hSquare)
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq] using
    hHalfSquare

/-- Every positive operator-norm tolerance is attained after finitely many
Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Rem₀ n‖ < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ => ‖Rem₀ n‖)
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_tendsto_zero
    epsilon
    hEpsilon

/-- Every positive inverse-defect tolerance is attained after finitely many
Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Def₀ n‖ < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ => ‖Def₀ n‖)
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_tendsto_zero_in_operatorNorm
    epsilon
    hEpsilon

/-- Every positive pointwise solution-error tolerance is attained after finitely
many Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_tendsto_zero
      g)
    epsilon
    hEpsilon

/-- Every positive residual tolerance is attained after finitely many
Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ => ‖Res₀ (g : H₀) (Nvec₀ n g)‖)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_tendsto_zero
      g)
    epsilon
    hEpsilon

/-- Every positive Poisson-energy error tolerance is attained after finitely many
Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N, PE₀ (Nvec₀ n g - G₀ g) < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g))
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_tendsto_zero
      g)
    epsilon
    hEpsilon

/-- Every positive Fenchel-gap tolerance is attained after finitely many
Green--Neumann truncation steps. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon :=
  real_tendsto_zero_exists_forall_ge_lt
    (fun n : ℕ =>
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g))
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_tendsto_zero
      g)
    epsilon
    hEpsilon

/-- A residual threshold of `epsilon / 324` is eventually reached, and the
existing residual-only a posteriori certificate then bounds the canonical
solution error by `epsilon`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertifiedError
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        ‖G₀ g - Nvec₀ n g‖ ≤ epsilon := by
  have hResidualNorm :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_tendsto_zero
      g
  have hScaledResidual :
      Tendsto
        (fun n : ℕ => 324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖)
        atTop
        (nhds 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hResidualNorm)
  rcases
      real_tendsto_zero_exists_forall_ge_lt
        (fun n : ℕ => 324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖)
        hScaledResidual
        epsilon
        hEpsilon with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hResidualSmall := hN n hn
  refine ⟨hResidualSmall, ?_⟩
  have hAmbientCertificate :
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (g : H₀) (Nvec₀ n g)‖ ≤
        epsilon := by
    have hBundledCertificate :
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ ≤ epsilon :=
      le_of_lt hResidualSmall
    change
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (g : H₀) (Nvec₀ n g)‖ ≤
        epsilon at hBundledCertificate
    exact hBundledCertificate
  have hCertified :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_canonical_sub_le_of_324_mul_norm_residual_le
      (g : H₀)
      (Nvec₀ n g)
      epsilon
      hAmbientCertificate
  simpa only [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCanonicalPoissonSolutionToVacuumOrthogonalL2_apply_subtype_eq_centeredGreen] using
    hCertified

/-- A single finite index simultaneously satisfies operator, inverse-defect,
pointwise error, residual, Poisson-energy, and Fenchel-gap tolerances. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
        epsilon hEpsilon with
    ⟨NRem, hRem⟩
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
        epsilon hEpsilon with
    ⟨NDef, hDef⟩
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
        g epsilon hEpsilon with
    ⟨NErr, hErr⟩
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
        g epsilon hEpsilon with
    ⟨NRes, hRes⟩
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
        g epsilon hEpsilon with
    ⟨NEnergy, hEnergy⟩
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
        g epsilon hEpsilon with
    ⟨NGap, hGap⟩
  refine
    ⟨max NRem (max NDef (max NErr (max NRes (max NEnergy NGap)))), ?_⟩
  intro n hn
  exact
    ⟨hRem n (by omega),
      hDef n (by omega),
      hErr n (by omega),
      hRes n (by omega),
      hEnergy n (by omega),
      hGap n (by omega)⟩

/-- Structured receipt for finite stopping of the actual optimal Richardson
Green--Neumann solver. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonFiniteStoppingCertificationL2Receipt :
    Prop where
  operator_remainder_stopping :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ‖Rem₀ n‖ < epsilon
  inverse_defect_stopping :
    ∀ (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ‖Def₀ n‖ < epsilon
  pointwise_error_stopping :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon
  residual_stopping :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon
  poisson_energy_stopping :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, PE₀ (Nvec₀ n g - G₀ g) < epsilon
  fenchel_gap_stopping :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N,
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  residual_certified_error :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          ‖G₀ g - Nvec₀ n g‖ ≤ epsilon
  simultaneous_stopping :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N,
        ‖Rem₀ n‖ < epsilon ∧
        ‖Def₀ n‖ < epsilon ∧
        ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  claim_boundary :
    True

/-- The finite stopping certification receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonFiniteStoppingCertificationL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonFiniteStoppingCertificationL2Receipt := by
  refine
    { operator_remainder_stopping := ?_
      inverse_defect_stopping := ?_
      pointwise_error_stopping := ?_
      residual_stopping := ?_
      poisson_energy_stopping := ?_
      fenchel_gap_stopping := ?_
      residual_certified_error := ?_
      simultaneous_stopping := ?_
      claim_boundary := trivial }
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
        epsilon hEpsilon
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
        epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertifiedError
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
        g epsilon hEpsilon

end
end MathlibAnalytic
end MGAP4D
