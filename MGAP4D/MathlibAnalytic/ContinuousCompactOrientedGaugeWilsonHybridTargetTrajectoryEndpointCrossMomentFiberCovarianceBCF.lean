import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCrossMomentBCF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Rank-zero endpoint observable on one fixed original Gibbs-pair trajectory fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (x : (i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) : ℝ :=
  O (C.base.replaceLink
    (C.independentPairHybridConfiguration z.1 z.2 0)
    target
    (x ⟨0, Finset.mem_Iic.2 (Nat.zero_le _)⟩))

/-- Full-rank endpoint observable on one fixed original Gibbs-pair trajectory fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (x : (i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) : ℝ :=
  O (C.base.replaceLink
    (C.independentPairHybridConfiguration z.1 z.2
      (Fintype.card C.base.geometry.Edge))
    target
    (x ⟨Fintype.card C.base.geometry.Edge, Finset.mem_Iic.2 le_rfl⟩))

/-- The rank-zero fixed-pair endpoint observable is continuous in the trajectory. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
        target O z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
  exact O.continuous.comp
    ((continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk
        (continuous_apply
          (⟨0, Finset.mem_Iic.2 (Nat.zero_le _)⟩ :
            Finset.Iic (Fintype.card C.base.geometry.Edge)))))

/-- The full-rank fixed-pair endpoint observable is continuous in the trajectory. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
        target O z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
  exact O.continuous.comp
    ((continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk
        (continuous_apply
          (⟨Fintype.card C.base.geometry.Edge, Finset.mem_Iic.2 le_rfl⟩ :
            Finset.Iic (Fintype.card C.base.geometry.Edge)))))

/-- The existing single-trajectory endpoint transport is exactly the difference of
its rank-zero and full-rank fiber endpoint observables. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (x : (i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
        target O (Fintype.card C.base.geometry.Edge) (z, x) =
      C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
          target O z x -
        C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
          target O z x := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
      target O (Fintype.card C.base.geometry.Edge) 0 (Nat.zero_le _) x,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
      target O (Fintype.card C.base.geometry.Edge)
        (Fintype.card C.base.geometry.Edge) le_rfl x]
  rfl

/-- Conditional covariance of the two single-trajectory endpoint observables for
one fixed original Gibbs pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  (∫ x,
      C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
          target O z x *
        C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
          target O z x
      ∂trajectory) -
    (∫ x,
      C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
        target O z x
      ∂trajectory) *
    (∫ x,
      C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
        target O z x
      ∂trajectory)

/-- Fixed-original-pair fiber of the global endpoint cross moment. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  ∫ xy,
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
      target O (z, xy)
    ∂trajectory.prod trajectory

/-- Conditional mean of the single-trajectory endpoint transport. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  ∫ x,
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
      target O (Fintype.card C.base.geometry.Edge) (z, x)
    ∂C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)

/-- Square of the conditional mean single-trajectory endpoint transport. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  (C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF
    target O z) ^ 2

/-- Exact disintegration of the global endpoint cross moment over the original
independent Gibbs pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryDoubleKernel target
  let f :=
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
      target O
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF_integrable
      C target O
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure]
      using hJointNamed
  have hFubini := Measure.integral_compProd hJoint
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
  change (∫ w, f w ∂(μ ⊗ₘ κ)) = _
  calc
    (∫ w, f w ∂(μ ⊗ₘ κ)) =
      ∫ z, ∫ xy, f (z, xy) ∂κ z ∂μ := hFubini
    _ = ∫ z,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
          target O z ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp [κ]
        rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleKernel_apply]
        unfold
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
        rfl

/-- Conditional iid polarization: the fixed-pair endpoint cross moment is exactly
twice the conditional covariance of the two endpoint observables. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF_eq_two_mul_covariance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
        target O z =
      2 * C.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
        target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let U :=
    C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
      target O z
  let V :=
    C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
      target O z
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hUContinuous : Continuous U := by
    simpa [U] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF_continuous
        C target O z
  have hVContinuous : Continuous V := by
    simpa [V] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF_continuous
        C target O z
  have hUV : Integrable (fun x => U x * V x) trajectory :=
    (hUContinuous.mul hVContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hUxVx : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        U xy.1 * V xy.1)
      (trajectory.prod trajectory) :=
    hUV.comp_fst trajectory
  have hUyVy : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        U xy.2 * V xy.2)
      (trajectory.prod trajectory) :=
    hUV.comp_snd trajectory
  have hUxVy : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        U xy.1 * V xy.2)
      (trajectory.prod trajectory) :=
    ((hUContinuous.comp continuous_fst).mul
      (hVContinuous.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hUyVx : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        U xy.2 * V xy.1)
      (trajectory.prod trajectory) :=
    ((hUContinuous.comp continuous_snd).mul
      (hVContinuous.comp continuous_fst)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (xy : C.independentPairHybridTargetTrajectoryDoubleCarrier) :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
          target O (z, xy) =
        (U xy.1 - U xy.2) * (V xy.1 - V xy.2) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
    rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
        C target O 0 (Nat.zero_le _) (z, xy),
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
        C target O (Fintype.card C.base.geometry.Edge) le_rfl (z, xy)]
    rfl
  have hFstUV :
      (∫ xy, U xy.1 * V xy.1 ∂trajectory.prod trajectory) =
        ∫ x, U x * V x ∂trajectory := by
    calc
      (∫ xy, U xy.1 * V xy.1 ∂trajectory.prod trajectory) =
          trajectory.real Set.univ • ∫ x, U x * V x ∂trajectory := by
        exact MeasureTheory.integral_fun_fst
          (μ := trajectory) (ν := trajectory) (f := fun x => U x * V x)
      _ = ∫ x, U x * V x ∂trajectory := by simp
  have hSndUV :
      (∫ xy, U xy.2 * V xy.2 ∂trajectory.prod trajectory) =
        ∫ x, U x * V x ∂trajectory := by
    calc
      (∫ xy, U xy.2 * V xy.2 ∂trajectory.prod trajectory) =
          trajectory.real Set.univ • ∫ x, U x * V x ∂trajectory := by
        exact MeasureTheory.integral_fun_snd
          (μ := trajectory) (ν := trajectory) (f := fun x => U x * V x)
      _ = ∫ x, U x * V x ∂trajectory := by simp
  have hCrossUV :
      (∫ xy, U xy.1 * V xy.2 ∂trajectory.prod trajectory) =
        (∫ x, U x ∂trajectory) * ∫ x, V x ∂trajectory := by
    exact MeasureTheory.integral_prod_mul U V
  have hCrossVU :
      (∫ xy, U xy.2 * V xy.1 ∂trajectory.prod trajectory) =
        (∫ x, V x ∂trajectory) * ∫ x, U x ∂trajectory := by
    calc
      (∫ xy, U xy.2 * V xy.1 ∂trajectory.prod trajectory) =
          ∫ xy, V xy.1 * U xy.2 ∂trajectory.prod trajectory := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun xy => by ring
      _ = (∫ x, V x ∂trajectory) * ∫ x, U x ∂trajectory := by
        exact MeasureTheory.integral_prod_mul V U
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
  dsimp only
  calc
    (∫ xy,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossIntegrandBCF
          target O (z, xy)
        ∂trajectory.prod trajectory) =
      ∫ xy, (U xy.1 - U xy.2) * (V xy.1 - V xy.2)
        ∂trajectory.prod trajectory := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hPoint
    _ = ∫ xy,
        ((U xy.1 * V xy.1 - U xy.1 * V xy.2) -
          (U xy.2 * V xy.1 - U xy.2 * V xy.2))
        ∂trajectory.prod trajectory := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun xy => by ring
    _ =
        (∫ xy, (U xy.1 * V xy.1 - U xy.1 * V xy.2)
          ∂trajectory.prod trajectory) -
        ∫ xy, (U xy.2 * V xy.1 - U xy.2 * V xy.2)
          ∂trajectory.prod trajectory := by
      exact integral_sub (hUxVx.sub hUxVy) (hUyVx.sub hUyVy)
    _ =
        ((∫ xy, U xy.1 * V xy.1 ∂trajectory.prod trajectory) -
          ∫ xy, U xy.1 * V xy.2 ∂trajectory.prod trajectory) -
        ((∫ xy, U xy.2 * V xy.1 ∂trajectory.prod trajectory) -
          ∫ xy, U xy.2 * V xy.2 ∂trajectory.prod trajectory) := by
      rw [integral_sub hUxVx hUxVy, integral_sub hUyVx hUyVy]
    _ = 2 * ((∫ x, U x * V x ∂trajectory) -
        (∫ x, U x ∂trajectory) * ∫ x, V x ∂trajectory) := by
      rw [hFstUV, hSndUV, hCrossUV, hCrossVU]
      ring
    _ = 2 * C.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
        target O z := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
      dsimp [trajectory, U, V]

/-- The global endpoint cross moment is the Gibbs average of twice the fixed-pair
conditional endpoint covariance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_two_mul_integral_covariance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O =
      2 * ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_integral_fiber]
  calc
    (∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure)) =
      ∫ z,
        2 * C.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z =>
            continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentFiberBCF_eq_two_mul_covariance
              C target O z
    _ = 2 * ∫ z,
        C.independentPairHybridTargetTrajectoryEndpointFiberCovarianceBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
      rw [integral_const_mul]

/-- Conditional iid variance identity: the fixed-pair double endpoint energy is
twice the single-trajectory endpoint second moment minus twice the square of its
conditional mean. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_two_single_sub_two_mean_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z =
      2 *
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
            target O (Fintype.card C.base.geometry.Edge) z -
        2 *
          C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
            target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T : ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) → ℝ :=
    fun x =>
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
        target O (Fintype.card C.base.geometry.Edge) (z, x)
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hTContinuous : Continuous T := by
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_continuous
        C target O (Fintype.card C.base.geometry.Edge)).comp
        (continuous_const.prodMk continuous_id)
  have hT2 : Integrable (fun x => (T x) ^ 2) trajectory :=
    (hTContinuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLeft : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        (T xy.1) ^ 2)
      (trajectory.prod trajectory) :=
    hT2.comp_fst trajectory
  have hRight : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        (T xy.2) ^ 2)
      (trajectory.prod trajectory) :=
    hT2.comp_snd trajectory
  have hCross : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        T xy.1 * T xy.2)
      (trajectory.prod trajectory) :=
    ((hTContinuous.comp continuous_fst).mul
      (hTContinuous.comp continuous_snd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (xy : C.independentPairHybridTargetTrajectoryDoubleCarrier) :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O (z, xy) =
        (T xy.1 - T xy.2) ^ 2 := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_left_sub_right
        C target O (z, xy)]
  have hFstSq :
      (∫ xy, (T xy.1) ^ 2 ∂trajectory.prod trajectory) =
        ∫ x, (T x) ^ 2 ∂trajectory := by
    calc
      (∫ xy, (T xy.1) ^ 2 ∂trajectory.prod trajectory) =
          trajectory.real Set.univ • ∫ x, (T x) ^ 2 ∂trajectory := by
        exact MeasureTheory.integral_fun_fst
          (μ := trajectory) (ν := trajectory) (f := fun x => (T x) ^ 2)
      _ = ∫ x, (T x) ^ 2 ∂trajectory := by simp
  have hSndSq :
      (∫ xy, (T xy.2) ^ 2 ∂trajectory.prod trajectory) =
        ∫ x, (T x) ^ 2 ∂trajectory := by
    calc
      (∫ xy, (T xy.2) ^ 2 ∂trajectory.prod trajectory) =
          trajectory.real Set.univ • ∫ x, (T x) ^ 2 ∂trajectory := by
        exact MeasureTheory.integral_fun_snd
          (μ := trajectory) (ν := trajectory) (f := fun x => (T x) ^ 2)
      _ = ∫ x, (T x) ^ 2 ∂trajectory := by simp
  have hProd :
      (∫ xy, T xy.1 * T xy.2 ∂trajectory.prod trajectory) =
        (∫ x, T x ∂trajectory) ^ 2 := by
    rw [MeasureTheory.integral_prod_mul]
    ring
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
  dsimp only
  calc
    (∫ xy,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O (z, xy)
        ∂trajectory.prod trajectory) =
      ∫ xy, (T xy.1 - T xy.2) ^ 2
        ∂trajectory.prod trajectory := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hPoint
    _ = ∫ xy,
        ((T xy.1) ^ 2 + (T xy.2) ^ 2 -
          2 * (T xy.1 * T xy.2))
        ∂trajectory.prod trajectory := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun xy => by ring
    _ =
        (∫ xy, ((T xy.1) ^ 2 + (T xy.2) ^ 2)
          ∂trajectory.prod trajectory) -
        ∫ xy, 2 * (T xy.1 * T xy.2)
          ∂trajectory.prod trajectory := by
      exact integral_sub (hLeft.add hRight) (hCross.const_mul 2)
    _ =
        ((∫ xy, (T xy.1) ^ 2 ∂trajectory.prod trajectory) +
          ∫ xy, (T xy.2) ^ 2 ∂trajectory.prod trajectory) -
        2 * (∫ xy, T xy.1 * T xy.2 ∂trajectory.prod trajectory) := by
      rw [integral_add hLeft hRight, integral_const_mul]
    _ = 2 * (∫ x, (T x) ^ 2 ∂trajectory) -
        2 * (∫ x, T x ∂trajectory) ^ 2 := by
      rw [hFstSq, hSndSq, hProd]
      ring
    _ =
      2 *
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
            target O (Fintype.card C.base.geometry.Edge) z -
        2 *
          C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
            target O z := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF
      dsimp [T, trajectory]
      rfl

/-- Dropping the nonnegative conditional-mean square improves the old fixed-pair
factor four comparison to the sharp iid factor two comparison. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_le_two_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z ≤
      2 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) z := by
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_two_single_sub_two_mean_sq]
  have hMeanSq :
      0 ≤ C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
        target O z := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
    exact sq_nonneg _
  nlinarith

/-- The conditional-mean transport square is integrable over the independent
Gibbs-pair base. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
        target O)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hSingle :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
      C target O (Fintype.card C.base.geometry.Edge) le_rfl
  have hDouble :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_integrable
      C target O
  have hDiff : Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
            target O (Fintype.card C.base.geometry.Edge) z -
          (1 / 2 : ℝ) *
            C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
              target O z)
      μ :=
    hSingle.sub (hDouble.const_mul (1 / 2 : ℝ))
  apply hDiff.congr
  exact Filter.Eventually.of_forall fun z => by
    have hEq :=
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_two_single_sub_two_mean_sq
        C target O z
    nlinarith

/-- Global law-of-total-variance identity for the double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_single_sub_two_integral_mean_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O =
      2 *
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
            target O (Fintype.card C.base.geometry.Edge) -
        2 * ∫ z : C.base.Configuration × C.base.Configuration,
          C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
            target O z
          ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hSingle :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
      C target O (Fintype.card C.base.geometry.Edge) le_rfl
  have hMean :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF_integrable
      C target O
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_integral_fiber,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_eq_integral_fiber
      C target O (Fintype.card C.base.geometry.Edge) le_rfl]
  calc
    (∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
          target O z ∂μ) =
      ∫ z,
        (2 *
            C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
              target O (Fintype.card C.base.geometry.Edge) z -
          2 *
            C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
              target O z)
        ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z =>
            continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_two_single_sub_two_mean_sq
              C target O z
    _ =
        (∫ z,
          2 *
            C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
              target O (Fintype.card C.base.geometry.Edge) z
          ∂μ) -
        ∫ z,
          2 *
            C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
              target O z
          ∂μ := by
      exact integral_sub (hSingle.const_mul 2) (hMean.const_mul 2)
    _ =
      2 *
          (∫ z,
            C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
              target O (Fintype.card C.base.geometry.Edge) z
            ∂μ) -
        2 *
          ∫ z,
            C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
              target O z
            ∂μ := by
      rw [integral_const_mul, integral_const_mul]

/-- Global factor-two comparison between double and single endpoint energies. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_two_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      2 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) := by
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_single_sub_two_integral_mean_sq]
  have hMean :
      0 ≤ ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
    exact integral_nonneg fun z => by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
      exact sq_nonneg _
  nlinarith

/-- The completed source-path estimate inherits the improved global factor two. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_two_mul_boundaryResidualPath_add_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      2 *
        ((Fintype.card C.base.geometry.Edge : ℝ) *
          (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
            2 * ∑ source : C.base.geometry.Edge,
              (P.variation source) ^ 2)) := by
  exact le_trans
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_two_single
      C target O)
    (mul_le_mul_of_nonneg_left
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_le_boundaryResidualPath_add_variation
        C target O P)
      (by norm_num))

/-- Exact rewrite of the endpoint correlation obstruction into native energy,
single-trajectory second moment, and conditional-mean transport square. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF_eq_native_sub_single_add_integral_mean_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O =
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O -
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) +
        ∫ z : C.base.Configuration × C.base.Configuration,
          C.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF
            target O z
          ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  have hPolarization :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_native_sub_two_cross
      C target O
  have hVariance :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_two_single_sub_two_integral_mean_sq
      C target O
  nlinarith

end

end MathlibAnalytic
end MGAP4D
