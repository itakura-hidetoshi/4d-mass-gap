import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroOneEigenspaceInfiniteRankL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionLaws
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The dedicated rational-rotation energy sequence is transcendental as an
    element of the function algebra `ℕ → ℝ`, because its range is infinite. -/
theorem specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_transcendental :
    Transcendental ℝ specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence := by
  rw [transcendental_iff]
  intro p hp
  apply Polynomial.eq_zero_of_infinite_isRoot p
  have hRangeInfinite :
      (Set.range specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence).Infinite :=
    Set.infinite_range_of_injective
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_injective
  refine hRangeInfinite.mono ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  have hn := congrFun hp n
  simpa using hn

/-- Positive powers of the dedicated rational-rotation energy sequence are
    linearly independent. -/
theorem specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_positivePowers_linearIndependent :
    LinearIndependent ℝ
      (fun n : ℕ => fun m : ℕ =>
        specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)) := by
  have hAevalInjective :
      Function.Injective
        (Polynomial.aeval (R := ℝ)
          specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence) :=
    transcendental_iff_injective.mp
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_transcendental
  have hAll :
      LinearIndependent ℝ
        (fun n : ℕ =>
          specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence ^ n) := by
    have hMapped :=
      (Polynomial.basisMonomials ℝ).linearIndependent.map'
        (Polynomial.aeval (R := ℝ)
          specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence).toLinearMap
        (LinearMap.ker_eq_bot.mpr hAevalInjective)
    simpa [Function.comp_def, Polynomial.coe_basisMonomials] using hMapped
  have hPositive := hAll.comp Nat.succ Nat.succ_injective
  simpa [Function.comp_def, Pi.pow_apply, Nat.succ_eq_add_one] using hPositive

/-- Positive powers of the distinguished-coordinate Wilson energy. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF ^ (n + 1)

/-- Center each positive Wilson-energy power by the exact beta-zero target-link
    conditional expectation. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF n -
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF n)

/-- Difference evaluation between each rational-rotation configuration and the
    identity background. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (ℕ → ℝ) where
  toFun F n :=
    F
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          n) -
      F periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
  map_add' F G := by
    funext n
    simp
    ring
  map_smul' a F := by
    funext n
    simp
    ring

/-- Difference evaluation kills the projected target-fiber-constant term and
    returns the corresponding positive power of the explicit energy sequence. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap_apply_powerFluctuationBCF
    (n m : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
          n)
        m =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
  have hProjection :=
    continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
      periodicHypercubicThreeOriginAxisZeroTarget
      (specialUnitaryTwoBetaZeroOneInfiniteRankRationalRotation (m : ℝ))
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          m) -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          m)) -
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration) =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)
  have hProjection' :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
            m) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration]
      using hProjection
  rw [hProjection']
  simp [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF]

/-- The centered positive-power bounded-continuous observables are linearly
    independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF := by
  apply LinearIndependent.of_comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap
  have hPointwise :
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
            n)) =
        (fun n : ℕ => fun m : ℕ =>
          specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)) := by
    funext n m
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap_apply_powerFluctuationBCF
        n m
  rw [hPointwise]
  exact
    specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_positivePowers_linearIndependent

end

end MathlibAnalytic
end MGAP4D
