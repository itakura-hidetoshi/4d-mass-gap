import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonFiniteStoppingCertificationL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000

/-- The tail predicate asserting that `P` holds from the natural index `N`
onwards. -/
def naturalTailPredicate (P : ℕ → Prop) (N : ℕ) : Prop :=
  ∀ n ≥ N, P n

/-- Tail predicates are monotone in their starting index. -/
theorem naturalTailPredicate_mono
    {P : ℕ → Prop}
    {N M : ℕ}
    (hN : naturalTailPredicate P N)
    (hNM : N ≤ M) :
    naturalTailPredicate P M := by
  intro n hn
  exact hN n (le_trans hNM hn)

/-- The least natural index from which an eventually permanent predicate holds. -/
noncomputable def naturalLeastTailIndex
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N) :
    ℕ := by
  classical
  exact Nat.find hP

/-- The least tail index itself starts a valid tail. -/
theorem naturalLeastTailIndex_spec
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N) :
    naturalTailPredicate P (naturalLeastTailIndex P hP) := by
  classical
  unfold naturalLeastTailIndex
  exact Nat.find_spec hP

/-- The least tail index is no larger than any other valid tail index. -/
theorem naturalLeastTailIndex_le
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N)
    {N : ℕ}
    (hN : naturalTailPredicate P N) :
    naturalLeastTailIndex P hP ≤ N := by
  classical
  unfold naturalLeastTailIndex
  exact Nat.find_min' hP hN

/-- No index strictly before the least tail index starts a valid tail. -/
theorem naturalLeastTailIndex_not_before
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N)
    {N : ℕ}
    (hN : N < naturalLeastTailIndex P hP) :
    ¬ naturalTailPredicate P N := by
  classical
  unfold naturalLeastTailIndex at hN
  exact Nat.find_min hP hN

/-- The canonical least-tail index is the least element of all valid permanent
starting indices. -/
theorem naturalLeastTailIndex_isLeast
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N) :
    IsLeast
      {N : ℕ | naturalTailPredicate P N}
      (naturalLeastTailIndex P hP) :=
  ⟨naturalLeastTailIndex_spec P hP,
    fun _ hN => naturalLeastTailIndex_le P hP hN⟩

/-- An index starts a valid tail exactly when it lies at or after the least tail
index. -/
theorem naturalLeastTailIndex_le_iff
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N)
    (N : ℕ) :
    naturalLeastTailIndex P hP ≤ N ↔ naturalTailPredicate P N := by
  constructor
  · intro hLeast
    exact naturalTailPredicate_mono (naturalLeastTailIndex_spec P hP) hLeast
  · intro hN
    exact naturalLeastTailIndex_le P hP hN

/-- Exact well-ordering characterization of the least tail index. -/
theorem naturalLeastTailIndex_eq_iff
    (P : ℕ → Prop)
    (hP : ∃ N : ℕ, naturalTailPredicate P N)
    (N : ℕ) :
    naturalLeastTailIndex P hP = N ↔
      naturalTailPredicate P N ∧
        ∀ M < N, ¬ naturalTailPredicate P M := by
  classical
  unfold naturalLeastTailIndex
  exact Nat.find_eq_iff hP

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

/-- Pointwise operator-remainder stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ‖Rem₀ n‖ < epsilon

/-- The operator-remainder stopping predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate_tail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate
          epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
      epsilon hEpsilon

/-- Least permanent stopping index for the Green--Neumann operator remainder. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate
      epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate_tail
      epsilon hEpsilon)

/-- The operator-remainder minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate
        epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_stoppingPredicate_tail
        epsilon hEpsilon)

/-- Pointwise inverse-defect stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ‖Def₀ n‖ < epsilon

/-- The inverse-defect stopping predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate_tail
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate
          epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
      epsilon hEpsilon

/-- Least permanent stopping index for the inverse defect. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate
      epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate_tail
      epsilon hEpsilon)

/-- The inverse-defect minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Def₀ n‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate
        epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_stoppingPredicate_tail
        epsilon hEpsilon)

/-- Pointwise ambient solution-error stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ‖Nvec₀ n g - G₀ g‖ < epsilon

/-- The pointwise error predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate
          g epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
      g epsilon hEpsilon

/-- Least permanent stopping index for the pointwise ambient solution error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate_tail
      g epsilon hEpsilon)

/-- The pointwise-error minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_stoppingPredicate_tail
        g epsilon hEpsilon)

/-- Pointwise residual-norm stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon

/-- The residual-norm predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate
          g epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
      g epsilon hEpsilon

/-- Least permanent stopping index for the bundled residual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate_tail
      g epsilon hEpsilon)

/-- The residual minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_stoppingPredicate_tail
        g epsilon hEpsilon)

/-- Pointwise Poisson-energy error stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  PE₀ (Nvec₀ n g - G₀ g) < epsilon

/-- The Poisson-energy error predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate
          g epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
      g epsilon hEpsilon

/-- Least permanent stopping index for the Poisson-energy error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate_tail
      g epsilon hEpsilon)

/-- The Poisson-energy minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N, PE₀ (Nvec₀ n g - G₀ g) < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_stoppingPredicate_tail
        g epsilon hEpsilon)

/-- Pointwise exact Poisson Fenchel-gap stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon

/-- The exact Poisson Fenchel-gap predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate
          g epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
      g epsilon hEpsilon

/-- Least permanent stopping index for the exact Poisson Fenchel gap. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate_tail
      g epsilon hEpsilon)

/-- The Fenchel-gap minimal stopping index is the least permanent one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N,
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_stoppingPredicate_tail
        g epsilon hEpsilon)

/-- Residual-only stopping predicate underlying the a posteriori error
certificate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon

/-- The residual-only stopping predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
          g epsilon)
        N := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertifiedError
        g epsilon hEpsilon with
    ⟨N, hN⟩
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- Least permanent index for the operational residual-only certificate. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
      g epsilon hEpsilon)

/-- The residual-only certified index is the least permanent observable
certificate index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
        g epsilon hEpsilon)

/-- From the least residual-only stopping index onwards, the observable
residual threshold holds and certifies the ambient solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
          g epsilon hEpsilon,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        ‖G₀ g - Nvec₀ n g‖ ≤ epsilon := by
  intro n hn
  have hResidualSmall :
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_isLeast
      g epsilon hEpsilon).1 n hn
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

/-- The six-condition pointwise stopping predicate. -/
def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
    (g : Ω₀)
    (epsilon : ℝ)
    (n : ℕ) :
    Prop :=
  ‖Rem₀ n‖ < epsilon ∧
  ‖Def₀ n‖ < epsilon ∧
  ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
  ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
  PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
  ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon

/-- The six-condition simultaneous predicate eventually holds permanently. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate_tail
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ,
      naturalTailPredicate
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
          g epsilon)
        N := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
      g epsilon hEpsilon

/-- Least permanent index satisfying all six stopping conditions
simultaneously. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
      g epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate_tail
      g epsilon hEpsilon)

/-- The simultaneous stopping index is the least permanent six-condition
index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_isLeast
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | ∀ n ≥ N,
        ‖Rem₀ n‖ < epsilon ∧
        ‖Def₀ n‖ < epsilon ∧
        ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon}
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
        g epsilon hEpsilon) := by
  simpa only [naturalTailPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex] using
    naturalLeastTailIndex_isLeast
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate_tail
        g epsilon hEpsilon)

/-- All six conditions hold from the simultaneous minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
          g epsilon hEpsilon,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_isLeast
    g epsilon hEpsilon).1

/-- Structured receipt for canonical least Richardson stopping indices in the
actual finite beta-zero system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt :
    Prop where
  generic_least_tail :
    ∀ (P : ℕ → Prop) (hP : ∃ N : ℕ, naturalTailPredicate P N),
      IsLeast {N : ℕ | naturalTailPredicate P N}
        (naturalLeastTailIndex P hP)
  operator_remainder_least :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Rem₀ n‖ < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
          epsilon hEpsilon)
  inverse_defect_least :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Def₀ n‖ < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
          epsilon hEpsilon)
  pointwise_error_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
          g epsilon hEpsilon)
  residual_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N,
          ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
          g epsilon hEpsilon)
  poisson_energy_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N,
          PE₀ (Nvec₀ n g - G₀ g) < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
          g epsilon hEpsilon)
  fenchel_gap_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N,
          ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
          g epsilon hEpsilon)
  residual_only_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N,
          324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
          g epsilon hEpsilon)
  residual_only_certificate :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
            g epsilon hEpsilon,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          ‖G₀ g - Nvec₀ n g‖ ≤ epsilon
  simultaneous_least :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      IsLeast
        {N : ℕ | ∀ n ≥ N,
          ‖Rem₀ n‖ < epsilon ∧
          ‖Def₀ n‖ < epsilon ∧
          ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
          ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
          ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon}
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
          g epsilon hEpsilon)
  claim_boundary :
    True

/-- The minimal stopping-indices receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt := by
  refine
    { generic_least_tail := ?_
      operator_remainder_least := ?_
      inverse_defect_least := ?_
      pointwise_error_least := ?_
      residual_least := ?_
      poisson_energy_least := ?_
      fenchel_gap_least := ?_
      residual_only_least := ?_
      residual_only_certificate := ?_
      simultaneous_least := ?_
      claim_boundary := trivial }
  · intro P hP
    exact naturalLeastTailIndex_isLeast P hP
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_isLeast
        epsilon hEpsilon
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_isLeast
        epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_isLeast
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_isLeast
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_isLeast
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_isLeast
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_isLeast
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_isLeast
        g epsilon hEpsilon

end
end MathlibAnalytic
end MGAP4D
