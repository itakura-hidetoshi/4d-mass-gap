import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointMeanProjectionVarianceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The part of the native one-link pair energy not consumed by the endpoint
cross moment.  PR #907 identifies the same quantity as the single-trajectory
endpoint second moment plus native energy minus twice global Gibbs variance. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
      target O (Fintype.card C.base.geometry.Edge) +
    C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
      2 * C.gibbsVarianceBCF O

/-- Fixed-original-pair conditional variance of the single-trajectory endpoint
transport. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
      target O (Fintype.card C.base.geometry.Edge) z -
    C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
      target O z

/-- The endpoint conditional-variance gap is exactly native pair energy minus the
endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O =
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_two_variance_sub_single]
  ring

/-- The endpoint conditional-variance gap is one half of the double-trajectory
endpoint pair energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_half_double
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O =
      (1 / 2 : ℝ) *
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
          target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_native_sub_two_cross]
  ring

/-- Equivalently, the global gap is the single-trajectory endpoint second moment
minus the square of its conditional mean, averaged over original Gibbs pairs. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_single_sub_integral_mean_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O =
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) -
        ∫ z : C.base.Configuration × C.base.Configuration,
          C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
            target O z
          ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
  rw [continuous_compact_oriented_integral_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_eq_two_variance_sub_native]
  ring

/-- On each fixed original Gibbs pair, the conditional variance is one half of the
corresponding iid double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_half_double
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z =
      (1 / 2 : ℝ) *
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
          target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
  have hVariance :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_two_single_sub_two_mean_sq
      C target O z
  nlinarith

/-- Every fixed-pair endpoint conditional variance is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 ≤ C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_half_double]
  apply mul_nonneg
  · norm_num
  · unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
    dsimp only
    apply integral_nonneg
    intro xy
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    exact sq_nonneg _

/-- The global endpoint conditional-variance gap is the Gibbs average of the
fixed-pair conditional variances. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hSingle :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
      C target O (Fintype.card C.base.geometry.Edge) le_rfl
  have hMean :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_integrable
      C target O
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_single_sub_integral_mean_sq,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_eq_integral_fiber
      C target O (Fintype.card C.base.geometry.Edge) le_rfl]
  change
    (∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) z ∂μ) -
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
          target O z ∂μ =
    ∫ z : C.base.Configuration × C.base.Configuration,
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) z -
        C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
          target O z) ∂μ
  exact (integral_sub hSingle hMean).symm

/-- The global endpoint conditional-variance gap is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_integral_fiber]
  exact integral_nonneg fun z =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_nonneg
      C target O z

/-- Endpoint cross moment is always bounded above by the native one-link pair
energy.  This is the universal `rho = 1` statement. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  have hGap :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_nonneg
      C target O
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross] at hGap
  linarith

/-- Quantitative endpoint correlation domination is exactly a lower bound on the
conditional-variance gap. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_rho_native_iff_gap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤
      ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ↔
    (1 - ρ) * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ≤
      C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross]
  constructor <;> intro h <;> linarith

/-- The previous correlation condition is equivalently a lower bound on the
actual double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_rho_native_iff_double
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤
      ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ↔
    2 * (1 - ρ) * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ≤
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_rho_native_iff_gap,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_half_double]
  constructor <;> intro h <;> nlinarith

/-- A strict `rho < 1` domination on a positive native energy forces a strictly
positive conditional-variance gap. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_of_cross_le_rho_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ)
    (hρ : ρ < 1)
    (hNative : 0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hCross :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  have hGap :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_le_rho_native_iff_gap
      C target O ρ).mp hCross
  nlinarith

/-- Sum of endpoint conditional-variance gaps over all physical links. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∑ target : C.base.geometry.Edge,
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O

/-- The total gap is the sum of native energies minus the sum of endpoint cross
moments. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O =
      (∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) -
      ∑ target : C.base.geometry.Edge,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF
  calc
    (∑ target : C.base.geometry.Edge,
      C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O) =
      ∑ target : C.base.geometry.Edge,
        (C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
          C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
            target O) := by
        apply Finset.sum_congr rfl
        intro target _
        exact
          continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
            C target O
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-- The total endpoint conditional-variance gap is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF
  exact Finset.sum_nonneg fun target _ =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_nonneg
      C target O

/-- A common correlation factor on every link is equivalently a total-gap lower
bound after summation. -/
theorem continuous_compact_oriented_sum_cross_le_rho_mul_sum_native_iff_total_gap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ) :
    (∑ target : C.base.geometry.Edge,
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O) ≤
      ρ * ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ↔
    (1 - ρ) *
        (∑ target : C.base.geometry.Edge,
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) ≤
      C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross]
  constructor <;> intro h <;> linarith

end

end MathlibAnalytic
end MGAP4D
