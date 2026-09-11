import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanExactGreenOperatorPoissonL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The centered beta-zero random-scan Poisson operator `I - P`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  ContinuousLinearMap.id ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) -
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2

/-- Pointwise form of the beta-zero random-scan Poisson operator. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f =
      f - periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f := by
  rfl

/-- Every fixed vector of the actual beta-zero random-scan operator is exactly
its cardinality-zero Gibbs-vacuum projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_fixed_iff_eq_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f = f ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  constructor
  · intro hFixed
    let r : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f
    have hOrthogonal :
        inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            r = 0 := by
      simpa [r] using
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_sub_fluctuationCardinalityProjectorL2_zero_apply_eq_zero
          f
    have hProjectorFixed :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f := by
      simpa using
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_fluctuationCardinalityProjectorL2_zero_eq_self
          1 f
    have hResidualFixed :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 r =
          r := by
      change
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            (f -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
                0 f) =
          f -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f
      rw [map_sub, hFixed, hProjectorFixed]
    have hContraction :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanHeatBathL2_apply_le_slem_mul_norm_of_inner_vacuum_eq_zero
        r hOrthogonal
    rw [hResidualFixed] at hContraction
    have hSLEM :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2 =
          (323 : ℝ) / 324 := by
      norm_num [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanSLEML2]
    rw [hSLEM] at hContraction
    have hrNormZero : ‖r‖ = 0 := by
      nlinarith [norm_nonneg r]
    have hrZero : r = 0 := norm_eq_zero.mp hrNormZero
    dsimp [r] at hrZero
    exact sub_eq_zero.mp hrZero
  · intro hVacuum
    calc
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f =
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 f) := by
        exact congrArg
          (fun x =>
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 x)
          hVacuum
      _ =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f := by
        simpa using
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_fluctuationCardinalityProjectorL2_zero_eq_self
            1 f
      _ = f := hVacuum.symm

/-- The kernel of the beta-zero Poisson operator is exactly the Gibbs-vacuum
line, expressed through the cardinality-zero projector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_eq_zero_iff_eq_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 f = 0 ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  constructor
  · intro hKernel
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_fixed_iff_eq_vacuumProjector
        f).1
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply]
      at hKernel
    exact (sub_eq_zero.mp hKernel).symm
  · intro hVacuum
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply]
    exact sub_eq_zero.mpr
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_fixed_iff_eq_vacuumProjector
        f).2 hVacuum).symm

/-- Two vectors with the same beta-zero Poisson image differ only by their
cardinality-zero Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_solution_difference_eq_vacuumProjector
    (u v : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 v) :
    u - v =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 (u - v) := by
  apply
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_fixed_iff_eq_vacuumProjector
      (u - v)).1
  rw [map_sub]
  apply eq_of_sub_eq_zero
  calc
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 u -
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 v) -
        (u - v) =
      -((u -
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 u) -
          (v -
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 v)) := by
        abel
    _ = 0 := by
      simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply]
        using congrArg Neg.neg (sub_eq_zero.mpr hPoisson)

/-- Beta-zero Poisson solutions with the same vacuum projection are unique. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_solution_unique_of_same_vacuumProjector
    (u v : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 v)
    (hVacuum :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 v) :
    u = v := by
  apply sub_eq_zero.mp
  calc
    u - v =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 (u - v) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_solution_difference_eq_vacuumProjector
        u v hPoisson
    _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 v := by
      rw [map_sub]
    _ = 0 := by
      rw [hVacuum, sub_self]

/-- Every solution of the centered beta-zero Poisson equation is the Green
solution plus a Gibbs-vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_eq_green_add_vacuumProjector
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (u -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) := by
  have hGreen :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply] using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered
        f
  have hDifference :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoisson_solution_difference_eq_vacuumProjector
      u
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f)
      (hPoisson.trans hGreen.symm)
  calc
    u =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
          (u -
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) := by
      abel
    _ =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0
            (u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) := by
      exact congrArg
        (fun z =>
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f + z)
        hDifference

/-- Rank-one explicit form of the affine classification of centered beta-zero
Poisson solutions. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_eq_green_add_inner_vacuum_smul_vacuum
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) :
    u =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
        inner ℝ
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
            (u -
              periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) •
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  simpa [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum] using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_eq_green_add_vacuumProjector
      f u hPoisson

/-- Adding an arbitrary Gibbs-vacuum component to the Green solution preserves
the centered beta-zero Poisson equation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_green_add_vacuumProjector_solves_centeredPoisson
    (f w : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 w) =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
  have hProjectorFixed :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 w) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 w := by
    simpa using
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_fluctuationCardinalityProjectorL2_zero_eq_self
        1 w
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
    map_add, hProjectorFixed]
  calc
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 w) -
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) +
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 w) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f) := by
      abel
    _ =
      f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanGreenOperatorL2_sub_randomScanHeatBathL2_apply_eq_centered
        f

/-- Complete affine classification of centered beta-zero Poisson solutions. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_iff_exists_vacuumProjector
    (f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f ↔
      ∃ w : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 w := by
  constructor
  · intro hPoisson
    exact ⟨
      u - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_eq_green_add_vacuumProjector
        f u hPoisson⟩
  · rintro ⟨w, rfl⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_green_add_vacuumProjector_solves_centeredPoisson
        f w

/-- Compact receipt for beta-zero fixed-point rigidity and the affine
classification of centered Poisson solutions modulo the Gibbs vacuum. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFixedPointAffineClassificationL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2 f = f ↔
      f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) ∧
  (∀ f u : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2 u =
        f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f ↔
      ∃ w : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
        u =
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f +
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              0 w) ∧
  ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2‖ = 324

/-- The beta-zero fixed-point/Poisson affine-classification receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFixedPointAffineClassificationL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonFixedPointAffineClassificationL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanHeatBathL2_fixed_iff_eq_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredPoisson_solution_iff_exists_vacuumProjector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanGreenOperatorL2_eq_324⟩

end

end MathlibAnalytic
end MGAP4D
