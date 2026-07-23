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
  unfold naturalLeastTailIndex at hN ⊢
  exact Nat.find_min hP hN

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

/-- Least permanent stopping index for the Green--Neumann operator remainder. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ => ‖Rem₀ n‖ < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
      epsilon hEpsilon)

/-- The operator-remainder condition holds from its minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
          epsilon hEpsilon,
      ‖Rem₀ n‖ < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ => ‖Rem₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
        epsilon hEpsilon)

/-- Every permanent operator-remainder stopping index is at least the canonical
minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_le
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N, ‖Rem₀ n‖ < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ => ‖Rem₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
        epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent operator-remainder stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_not_before
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
        epsilon hEpsilon) :
    ¬ (∀ n ≥ N, ‖Rem₀ n‖ < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ => ‖Rem₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannRemainderEndL2_norm_lt
        epsilon hEpsilon)
      hN

/-- Least permanent stopping index for the inverse defect. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ => ‖Def₀ n‖ < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
      epsilon hEpsilon)

/-- The inverse-defect condition holds from its minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_spec
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
          epsilon hEpsilon,
      ‖Def₀ n‖ < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ => ‖Def₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
        epsilon hEpsilon)

/-- Every permanent inverse-defect stopping index is at least the canonical
minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_le
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N, ‖Def₀ n‖ < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ => ‖Def₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
        epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent inverse-defect stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_not_before
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
        epsilon hEpsilon) :
    ¬ (∀ n ≥ N, ‖Def₀ n‖ < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ => ‖Def₀ n‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannInverseDefectEndL2_norm_lt
        epsilon hEpsilon)
      hN

/-- Least permanent stopping index for the pointwise ambient solution error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖ < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
      g epsilon hEpsilon)

/-- The pointwise ambient error condition holds from its minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
          g epsilon hEpsilon,
      ‖Nvec₀ n g - G₀ g‖ < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
        g epsilon hEpsilon)

/-- Every permanent pointwise-error stopping index is at least the canonical
minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent pointwise-error stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N, ‖Nvec₀ n g - G₀ g‖ < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ => ‖Nvec₀ n g - G₀ g‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_lt
        g epsilon hEpsilon)
      hN

/-- Least permanent stopping index for the bundled residual norm. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ => ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
      g epsilon hEpsilon)

/-- The residual condition holds from its minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
          g epsilon hEpsilon,
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ => ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
        g epsilon hEpsilon)

/-- Every permanent residual stopping index is at least the canonical minimal
one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N, ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ => ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent residual stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N, ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ => ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_lt
        g epsilon hEpsilon)
      hN

/-- Least permanent stopping index for the Poisson-energy error. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g) < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
      g epsilon hEpsilon)

/-- The Poisson-energy error condition holds from its minimal stopping index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
          g epsilon hEpsilon,
      PE₀ (Nvec₀ n g - G₀ g) < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
        g epsilon hEpsilon)

/-- Every permanent Poisson-energy stopping index is at least the canonical
minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N, PE₀ (Nvec₀ n g - G₀ g) < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent Poisson-energy stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N, PE₀ (Nvec₀ n g - G₀ g) < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ => PE₀ (Nvec₀ n g - G₀ g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_lt
        g epsilon hEpsilon)
      hN

/-- Least permanent stopping index for the exact Poisson Fenchel gap. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ℕ :=
  naturalLeastTailIndex
    (fun n : ℕ =>
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
      g epsilon hEpsilon)

/-- The exact Poisson Fenchel-gap condition holds from its minimal stopping
index. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_spec
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon) :
    ∀ n ≥
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
          g epsilon hEpsilon,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (fun n : ℕ =>
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
        g epsilon hEpsilon)

/-- Every permanent Fenchel-gap stopping index is at least the canonical
minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (fun n : ℕ =>
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent Fenchel-gap stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N,
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (fun n : ℕ =>
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_lt
        g epsilon hEpsilon)
      hN

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
  have hResidualTail :=
    naturalLeastTailIndex_spec
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
        g epsilon hEpsilon)
  have hResidualSmall :
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon := by
    exact hResidualTail n hn
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

/-- Every permanent residual-certificate stopping index is at least the
canonical minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent residual-certificate stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N,
      324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumannPartialSumL2_residualCertificatePredicate_tail
        g epsilon hEpsilon)
      hN

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
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
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
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
  exact
    naturalLeastTailIndex_spec
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
        g epsilon hEpsilon)

/-- Every permanent six-condition stopping index is at least the canonical
simultaneous minimal one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_le
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : ∀ n ≥ N,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
        g epsilon hEpsilon ≤ N := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
  exact
    naturalLeastTailIndex_le
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
        g epsilon hEpsilon)
      hN

/-- No earlier index starts a permanent six-condition stopping tail. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_not_before
    (g : Ω₀)
    (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
        g epsilon hEpsilon) :
    ¬ (∀ n ≥ N,
      ‖Rem₀ n‖ < epsilon ∧
      ‖Def₀ n‖ < epsilon ∧
      ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
      ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
      PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
      ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon) := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex at hN ⊢
  exact
    naturalLeastTailIndex_not_before
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousStoppingPredicate
        g epsilon)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_optimalRichardsonGreenNeumann_simultaneous_stopping_index
        g epsilon hEpsilon)
      hN

/-- Structured receipt for canonical least Richardson stopping indices in the
actual finite beta-zero system. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt :
    Prop where
  generic_least_tail_spec :
    ∀ (P : ℕ → Prop) (hP : ∃ N : ℕ, naturalTailPredicate P N),
      naturalTailPredicate P (naturalLeastTailIndex P hP)
  generic_least_tail_minimal :
    ∀ (P : ℕ → Prop) (hP : ∃ N : ℕ, naturalTailPredicate P N)
      (N : ℕ),
      naturalTailPredicate P N → naturalLeastTailIndex P hP ≤ N
  operator_remainder_minimal :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex
            epsilon hEpsilon,
        ‖Rem₀ n‖ < epsilon
  inverse_defect_minimal :
    ∀ (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex
            epsilon hEpsilon,
        ‖Def₀ n‖ < epsilon
  pointwise_error_minimal :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex
            g epsilon hEpsilon,
        ‖Nvec₀ n g - G₀ g‖ < epsilon
  residual_minimal :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex
            g epsilon hEpsilon,
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon
  poisson_energy_minimal :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex
            g epsilon hEpsilon,
        PE₀ (Nvec₀ n g - G₀ g) < epsilon
  fenchel_gap_minimal :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex
            g epsilon hEpsilon,
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  residual_only_certificate :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex
            g epsilon hEpsilon,
        324 * ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
          ‖G₀ g - Nvec₀ n g‖ ≤ epsilon
  simultaneous_minimal :
    ∀ (g : Ω₀) (epsilon : ℝ) (hEpsilon : 0 < epsilon),
      ∀ n ≥
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex
            g epsilon hEpsilon,
        ‖Rem₀ n‖ < epsilon ∧
        ‖Def₀ n‖ < epsilon ∧
        ‖Nvec₀ n g - G₀ g‖ < epsilon ∧
        ‖Res₀ (g : H₀) (Nvec₀ n g)‖ < epsilon ∧
        PE₀ (Nvec₀ n g - G₀ g) < epsilon ∧
        ((1 : ℝ) / 2) * GE₀ g ^ 2 - Φ₀ g (Nvec₀ n g) < epsilon
  claim_boundary :
    True

/-- The minimal stopping-indices receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonMinimalStoppingIndicesL2Receipt := by
  refine
    { generic_least_tail_spec := ?_
      generic_least_tail_minimal := ?_
      operator_remainder_minimal := ?_
      inverse_defect_minimal := ?_
      pointwise_error_minimal := ?_
      residual_minimal := ?_
      poisson_energy_minimal := ?_
      fenchel_gap_minimal := ?_
      residual_only_certificate := ?_
      simultaneous_minimal := ?_
      claim_boundary := trivial }
  · intro P hP
    exact naturalLeastTailIndex_spec P hP
  · intro P hP N hN
    exact naturalLeastTailIndex_le P hP hN
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_minimalStoppingIndex_spec
        epsilon hEpsilon
  · intro epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_minimalStoppingIndex_spec
        epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_errorNorm_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualNorm_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonEnergyError_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_poissonFenchelGap_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannPartialSumL2_residualCertified_minimalStoppingIndex_spec
        g epsilon hEpsilon
  · intro g epsilon hEpsilon
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumann_simultaneousMinimalStoppingIndex_spec
        g epsilon hEpsilon

end
end MathlibAnalytic
end MGAP4D
