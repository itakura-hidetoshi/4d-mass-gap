import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Every continuous linear endomorphism commutes with its constant-step
Richardson error map `I - tau A`. -/
theorem continuousLinearMap_apply_richardsonError_commutes
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (tau : ℝ)
    (x : E) :
    A ((ContinuousLinearMap.id ℝ E - tau • A) x) =
      (ContinuousLinearMap.id ℝ E - tau • A) (A x) := by
  change A (x - tau • A x) = A x - tau • A (A x)
  rw [map_sub, map_smul]

/-- The actual centered Poisson residual, bundled as a vector of `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
      f u,
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u)).2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonResidualL2_eq_zero
        f u)⟩

/-- Coercing the bundled residual returns the ambient residual. -/
@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_coe
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f u :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u := by
  rfl

/-- Internally, the bundled residual is the Poisson image of the canonical
solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          u) := by
  apply Subtype.ext
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u) :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply]
  rfl

/-- One optimal Richardson solution update `u + tau* r_f(u)` inside `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
  u +
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2 •
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f u

/-- The canonical solution error after one solution update is exactly one
application of the optimal Richardson error endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionStepL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
          f u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          u) := by
  unfold
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanRichardsonErrorEndL2_apply]
  module

/-- The canonical centered solution is a fixed point of the optimal Richardson
solution update. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonSolutionStepL2_canonical_eq_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f := by
  have hError :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionStepL2
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
        f)
  have hZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) = 0 := by
    simpa using hError
  exact (sub_eq_zero.mp hZero).symm

/-- One solution update propagates the bundled residual by the same optimal
Richardson error endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionStep_eq_errorEnd_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
          f u) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          f u) := by
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
          f u) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
            f u) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub
        f _
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u)) := by
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionStepL2]
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u)) := by
      unfold
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
      exact
        continuousLinearMap_apply_richardsonError_commutes
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u)
    _ =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          f u) := by
      rw [
        ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_eq_poissonEnd_apply_canonical_sub]

/-- Recursive optimal Richardson approximation to the canonical centered Poisson
solution. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ℕ →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 →
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2
  | 0 => fun u => u
  | Nat.succ n => fun u =>
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u)

/-- Exact finite-step error representation for the natural solution iteration. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionIterateL2
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          u) := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      calc
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
              f
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
                f n u) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
                f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
                f n u) :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionStepL2
            f _
        _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
                  f -
                u)) := by
          rw [ih]

/-- Exact finite-step residual representation for the natural solution
iteration. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionIterate_eq_errorIterate
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          f u) := by
  induction n with
  | zero =>
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
  | succ n ih =>
      rw [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2]
      calc
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
              f
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
                f n u)) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
              f
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
                f n u)) :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionStep_eq_errorEnd_apply
            f _
        _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanRichardsonErrorEndL2
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonStepSizeL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
              n
              (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
                f u)) := by
          rw [ih]

/-- Geometric canonical-solution error bound for every finite number of natural
optimal Richardson updates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_canonical_sub_optimalRichardsonSolutionIterateL2_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          u‖ := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionIterateL2]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
      n
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        u)

/-- The actual residual contracts geometrically with the same exact factor. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_optimalRichardsonSolutionIterate_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u)‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ := by
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
          f n u)‖ ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          f u‖
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionIterate_eq_errorIterate]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_optimalRichardsonErrorIterateL2_le
      n
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
        f u)

/-- Geometric residual-only Dirichlet energy-gap bound along the natural
optimal Richardson solution iteration. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_optimalRichardsonSolutionIterate_sub_canonical_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ≤
      162 *
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖) ^ 2 := by
  have hEnergy :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_162_mul_norm_residual_sq
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
        f n u)
  have hResidual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_optimalRichardsonSolutionIterate_le
      f n u
  have hLeft :
      0 ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u)‖ :=
    norm_nonneg _
  have hRight :
      0 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ :=
    mul_nonneg
      (pow_nonneg
        (le_of_lt
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
        n)
      (norm_nonneg _)
  have hSq :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u)‖ ^ 2 ≤
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖) ^ 2 := by
    nlinarith
  exact hEnergy.trans
    (mul_le_mul_of_nonneg_left hSq (by norm_num))

/-- Geometric residual-only Green maximum-gap bound along the natural optimal
Richardson solution iteration. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_optimalRichardsonSolutionIterate_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (n : ℕ)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u) ≤
      324 *
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖) ^ 2 := by
  have hGreen :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_324_mul_norm_residual_sq
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
        f n u)
  have hResidual :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_optimalRichardsonSolutionIterate_le
      f n u
  have hLeft :
      0 ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u)‖ :=
    norm_nonneg _
  have hRight :
      0 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ :=
    mul_nonneg
      (pow_nonneg
        (le_of_lt
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonContractionFactorL2_mem_Ioo.1)
        n)
      (norm_nonneg _)
  have hSq :
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u)‖ ^ 2 ≤
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖) ^ 2 := by
    nlinarith
  exact hGreen.trans
    (mul_le_mul_of_nonneg_left hSq (by norm_num))

/-- Residual-only a posteriori certification of the canonical solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_canonical_sub_le_of_324_mul_norm_residual_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (epsilon : ℝ)
    (hCertificate :
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ≤
        epsilon) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        u‖ ≤
      epsilon := by
  have hError :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_generalizedInverse_sub_subtype_le_324_mul_norm_residual
      f u
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f -
        u‖ =
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ := by
        rw [
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply]
        rfl
    _ ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ := hError
    _ ≤ epsilon := hCertificate

/-- Residual-only a posteriori certification of the Dirichlet energy gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_of_162_mul_norm_residual_sq_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (epsilon : ℝ)
    (hCertificate :
      162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2 ≤
        epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ≤
      epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_162_mul_norm_residual_sq
    f u).trans hCertificate

/-- Residual-only a posteriori certification of the Green maximum gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_of_324_mul_norm_residual_sq_le
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (epsilon : ℝ)
    (hCertificate :
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2 ≤
        epsilon) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u ≤
      epsilon :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_324_mul_norm_residual_sq
    f u).trans hCertificate

/-- Structured receipt for the natural optimal Richardson Poisson solver,
geometric residual propagation, and residual-only stopping certificates. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonCertifiedSolverL2Receipt :
    Prop where
  canonical_fixed :
    ∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionStepL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          f
  error_representation :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u)
  residual_representation :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonErrorIterateL2
          n
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualToVacuumOrthogonalL2
            f u)
  error_geometric :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f -
            u‖
  residual_geometric :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
            f n u)‖ ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖
  energy_geometric :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
              f n u) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ≤
        162 *
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
              f u‖) ^ 2
  green_geometric :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (n : ℕ)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonSolutionIterateL2
              f n u) ≤
        324 *
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonContractionFactorL2 ^ n *
            ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
              f u‖) ^ 2
  error_certificate :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
      (epsilon : ℝ),
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ≤
        epsilon →
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f -
          u‖ ≤
        epsilon
  energy_certificate :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
      (epsilon : ℝ),
      162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2 ≤
        epsilon →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ≤
        epsilon
  green_certificate :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
      (epsilon : ℝ),
      324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2 ≤
        epsilon →
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u ≤
        epsilon

/-- The natural optimal Richardson certified-solver receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonCertifiedSolverL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonCertifiedSolverL2Receipt := by
  exact
    { canonical_fixed :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonSolutionStepL2_canonical_eq_canonical
      error_representation :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_canonical_sub_optimalRichardsonSolutionIterateL2
      residual_representation :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualToVacuumOrthogonalL2_optimalRichardsonSolutionIterate_eq_errorIterate
      error_geometric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_canonical_sub_optimalRichardsonSolutionIterateL2_le
      residual_geometric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_optimalRichardsonSolutionIterate_le
      energy_geometric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_optimalRichardsonSolutionIterate_sub_canonical_le
      green_geometric :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_optimalRichardsonSolutionIterate_le
      error_certificate :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_canonical_sub_le_of_324_mul_norm_residual_le
      energy_certificate :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_of_162_mul_norm_residual_sq_le
      green_certificate :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_of_324_mul_norm_residual_sq_le }

end

end MathlibAnalytic
end MGAP4D
