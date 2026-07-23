import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonLogarithmicIterationCountsL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- A strict logarithmic ceiling count for a nonnegative geometric prefactor.
The zero-prefactor case has exact stopping count zero; otherwise this is the
closed doubled-prefactor ceiling from the generic logarithmic theory. -/
noncomputable def realNonnegativeGeometricStrictCeilingIterationCount
    (q C epsilon : ℝ) : ℕ :=
  if C = 0 then 0 else
    realGeometricStrictCeilingIterationCount q C epsilon

/-- The nonnegative-prefactor count handles both the zero sequence and every
strictly positive geometric envelope. -/
theorem realNonnegativeGeometricStrictCeilingIterationCount_spec
    (q C epsilon : ℝ)
    (hqPos : 0 < q)
    (hqLtOne : q < 1)
    (hC : 0 ≤ C)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ realNonnegativeGeometricStrictCeilingIterationCount q C epsilon,
      C * q ^ n < epsilon := by
  by_cases hCZero : C = 0
  · subst C
    intro n hn
    simpa [realNonnegativeGeometricStrictCeilingIterationCount] using hEpsilon
  · have hCPos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCZero)
    intro n hn
    exact
      realGeometricStrictCeilingIterationCount_spec
        q C epsilon hqPos hqLtOne hCPos hEpsilon n
        (by
          simpa [realNonnegativeGeometricStrictCeilingIterationCount, hCZero] using hn)

local notation "Ω₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
local notation "H₀" =>
  Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
local notation "q₀" =>
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2
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

/-- Explicit logarithmic count for the pointwise ambient solution error. For
nonzero data its closed coefficient is `324 ‖g‖`; for zero data it is zero. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realNonnegativeGeometricStrictCeilingIterationCount
    q₀ (324 * ‖g‖) epsilon

/-- The pointwise ambient solution error is strictly below tolerance from its
explicit logarithmic count onward. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
        g epsilon,
      ‖Nvec₀ n g - G₀ g‖ < epsilon := by
  intro n hn
  have hEnvelope : (324 * ‖g‖) * q₀ ^ n < epsilon :=
    realNonnegativeGeometricStrictCeilingIterationCount_spec
      q₀ (324 * ‖g‖) epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (mul_nonneg (by norm_num) (norm_nonneg g))
      hEpsilon
      n hn
  have hError :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_centeredGreen_sub_optimalRichardsonGreenNeumannPartialSumL2_le_324_mul_pow_mul_norm
      n g
  calc
    ‖Nvec₀ n g - G₀ g‖ = ‖G₀ g - Nvec₀ n g‖ := by
      rw [norm_sub_rev]
    _ ≤ 324 * q₀ ^ n * ‖g‖ := hError
    _ = (324 * ‖g‖) * q₀ ^ n := by ring
    _ < epsilon := hEnvelope

/-- The canonical least strict pointwise-error index is bounded by the explicit
logarithmic count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_le_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
      g epsilon hEpsilon)

/-- Explicit logarithmic count for the bundled residual norm. For nonzero data
its geometric coefficient is `‖g‖`; for zero data it is zero. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  realNonnegativeGeometricStrictCeilingIterationCount q₀ ‖g‖ epsilon

/-- The bundled residual is strictly below tolerance from its explicit
logarithmic count onward. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt_of_ge_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logarithmicIterationCount
        g epsilon,
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon := by
  intro n hn
  have hEnvelope : ‖g‖ * q₀ ^ n < epsilon :=
    realNonnegativeGeometricStrictCeilingIterationCount_spec
      q₀ ‖g‖ epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (norm_nonneg g)
      hEpsilon
      n hn
  have hResidual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
      n g
  calc
    ‖Res₀ (g : H₀) (Nvec₀ n g)‖ ≤ q₀ ^ n * ‖g‖ := hResidual
    _ = ‖g‖ * q₀ ^ n := by ring
    _ < epsilon := hEnvelope

/-- The canonical least residual index is bounded by the explicit logarithmic
count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_le_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt_of_ge_logarithmicIterationCount
      g epsilon hEpsilon)

/-- The Poisson-energy error uses the same explicit logarithmic count as the
ambient error, since the Poisson-energy norm is bounded above by the ambient
Hilbert norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
    g epsilon

/-- The Poisson-energy error is below tolerance from the explicit logarithmic
count onward. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt_of_ge_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logarithmicIterationCount
        g epsilon,
      PE₀ (Nvec₀ n g - G₀ g) < epsilon := by
  intro n hn
  exact
    lt_of_le_of_lt
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
        (Nvec₀ n g - G₀ g)).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n hn)

/-- The canonical least Poisson-energy stopping index is bounded by the explicit
logarithmic count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_le_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt_of_ge_logarithmicIterationCount
      g epsilon hEpsilon)

/-- Explicit logarithmic count for the exact Poisson Fenchel gap, obtained by
requiring ambient error below `sqrt (2 epsilon)`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
    g (Real.sqrt (2 * epsilon))

/-- The exact Fenchel gap is below tolerance from its explicit logarithmic count
onward. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt_of_ge_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logarithmicIterationCount
        g epsilon,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  intro n hn
  have hTwoEpsilonPos : 0 < 2 * epsilon := mul_pos (by norm_num) hEpsilon
  have hSqrtPos : 0 < Real.sqrt (2 * epsilon) := Real.sqrt_pos.2 hTwoEpsilonPos
  have hError :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
      g (Real.sqrt (2 * epsilon)) hSqrtPos n hn
  have hEnergyLe :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_bounds
      (Nvec₀ n g - G₀ g)).2
  have hEnergyLt : PE₀ (Nvec₀ n g - G₀ g) < Real.sqrt (2 * epsilon) :=
    lt_of_le_of_lt hEnergyLe hError
  have hEnergyNonneg :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonEnergyNormL2_nonneg
      (Nvec₀ n g - G₀ g)
  have hSqrtSq : Real.sqrt (2 * epsilon) ^ 2 = 2 * epsilon := by
    rw [sq_sqrt hTwoEpsilonPos.le]
  have hEnergySq : PE₀ (Nvec₀ n g - G₀ g) ^ 2 < 2 * epsilon := by
    nlinarith
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonFenchelGapL2_eq_half_error_sq]
  nlinarith

/-- The canonical least Fenchel-gap stopping index is bounded by its explicit
logarithmic count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_le_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt_of_ge_logarithmicIterationCount
      g epsilon hEpsilon)

/-- The residual-only a posteriori certificate has the same logarithmic envelope
coefficient `324 ‖g‖` as the uniform ambient error estimate. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount
    g epsilon

/-- From the explicit residual-certificate count onward, the scaled residual is
strictly below tolerance and the certified ambient error is at most tolerance. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_spec_of_ge_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logarithmicIterationCount
        g epsilon,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        ‖G₀ g - Nvec₀ n g‖ ≤ epsilon := by
  intro n hn
  have hEnvelope : (324 * ‖g‖) * q₀ ^ n < epsilon :=
    realNonnegativeGeometricStrictCeilingIterationCount_spec
      q₀ (324 * ‖g‖) epsilon
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.2
      (mul_nonneg (by norm_num) (norm_nonneg g))
      hEpsilon
      n hn
  have hResidual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonGreenNeumannPartialSum_le
      n g
  have hScaledResidual :
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon := by
    calc
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ ≤
          324 * (q₀ ^ n * ‖g‖) :=
        mul_le_mul_of_nonneg_left hResidual (by norm_num)
      _ = (324 * ‖g‖) * q₀ ^ n := by ring
      _ < epsilon := hEnvelope
  have hErrorLt :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
      g epsilon hEpsilon n hn
  exact
    ⟨hScaledResidual,
      by simpa only [norm_sub_rev] using (le_of_lt hErrorLt)⟩

/-- The canonical minimal residual-certificate index is bounded by the explicit
logarithmic count. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_le_logarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (fun n hn =>
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_spec_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n hn).1)

/-- A single explicit logarithmic index satisfying all six stopping conditions. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ) : ℕ :=
  max
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_strictLogarithmicIterationCount epsilon)
    (max
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_strictLogarithmicIterationCount epsilon)
      (max
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount g epsilon)
        (max
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logarithmicIterationCount g epsilon)
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logarithmicIterationCount g epsilon))))

/-- All six stopping conditions hold from the single explicit logarithmic index
onward. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount
        g epsilon,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  intro n hn
  exact
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
        epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt_of_ge_strictLogarithmicIterationCount
        epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n (by omega),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt_of_ge_logarithmicIterationCount
        g epsilon hEpsilon n (by omega)⟩

/-- The canonical least simultaneous stopping index is bounded by the explicit
single logarithmic index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_le_simultaneousLogarithmicIterationCount
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
        g epsilon hEpsilon ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount
        g epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_isLeast
    g epsilon hEpsilon).2
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount_spec
      g epsilon hEpsilon)

/-- Structured receipt for explicit logarithmic stopping certification of all
actual beta-zero optimal Richardson criteria. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicStoppingCertificationL2Receipt :
    Prop where
  pointwise_error :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_logarithmicIterationCount g epsilon,
        ‖Nvec₀ n g - G₀ g‖ < epsilon
  residual :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_logarithmicIterationCount g epsilon,
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon
  poisson_energy :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_logarithmicIterationCount g epsilon,
        PE₀ (Nvec₀ n g - G₀ g) < epsilon
  fenchel_gap :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_logarithmicIterationCount g epsilon,
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  residual_certificate :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_logarithmicIterationCount g epsilon,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          ‖G₀ g - Nvec₀ n g‖ ≤ epsilon
  simultaneous :
    ∀ (g : Ω₀) (epsilon : ℝ), 0 < epsilon →
      ∀ n ≥ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount g epsilon,
        ‖Rem₀ n‖ < epsilon ∧
        ‖Def₀ n‖ < epsilon ∧
        ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  claim_boundary : True

/-- The all-criteria logarithmic stopping receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicStoppingCertificationL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonLogarithmicStoppingCertificationL2Receipt := by
  exact
    { pointwise_error :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt_of_ge_logarithmicIterationCount
      residual :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt_of_ge_logarithmicIterationCount
      poisson_energy :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt_of_ge_logarithmicIterationCount
      fenchel_gap :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt_of_ge_logarithmicIterationCount
      residual_certificate :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_spec_of_ge_logarithmicIterationCount
      simultaneous :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousLogarithmicIterationCount_spec
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
