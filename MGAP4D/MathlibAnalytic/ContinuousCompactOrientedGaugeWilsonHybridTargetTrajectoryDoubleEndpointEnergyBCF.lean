import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryDoubleConditionalPairBCF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Carrier of two complete target trajectories over one original configuration
pair. -/
abbrev
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleCarrier
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :=
  (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
    ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge))

/-- Joint carrier of an original configuration pair and two complete target
trajectories. -/
abbrev
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointCarrier
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :=
  (C.base.Configuration × C.base.Configuration) ×
    C.independentPairHybridTargetTrajectoryDoubleCarrier

/-- Difference of the two observable values reconstructed at one canonical rank.
The zero branch only totalizes ranks beyond the complete finite path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (r : ℕ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) : ℝ :=
  if hr : r ≤ Fintype.card C.base.geometry.Edge then
    let pair :=
      C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target r hr w
    O pair.1 - O pair.2
  else 0

@[simp]
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) :
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
        target O r w =
      O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 r)
          target (w.2.1 ⟨r, Finset.mem_Iic.2 hr⟩)) -
        O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 r)
          target (w.2.2 ⟨r, Finset.mem_Iic.2 hr⟩)) := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap,
    hr]

/-- Every rankwise pair observable is continuous on the common double-trajectory
carrier. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (r : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
        target O r) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
  split_ifs with hr
  · have hPair :=
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
        C target r hr
    exact (O.continuous.comp hPair.fst).sub (O.continuous.comp hPair.snd)
  · exact continuous_const

/-- One adjacent increment of the rankwise conditional-pair observable process. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (k : ℕ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) : ℝ :=
  C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O k w -
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O (k + 1) w

/-- Endpoint transport of the rankwise pair-observable process across the complete
canonical source path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) : ℝ :=
  C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O 0 w -
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O (Fintype.card C.base.geometry.Edge) w

/-- Exact finite telescoping of the double-trajectory pair-observable process. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_sum_adjacent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
        target O w =
      ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
        C.independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF
          target O k w := by
  let d : ℕ → ℝ := fun r =>
    C.independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF
      target O r w
  have hTel := Finset.sum_range_sub (fun r => -d r)
    (Fintype.card C.base.geometry.Edge)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF
  change d 0 - d (Fintype.card C.base.geometry.Edge) =
    ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      (d k - d (k + 1))
  calc
    d 0 - d (Fintype.card C.base.geometry.Edge) =
        (-d (Fintype.card C.base.geometry.Edge)) - (-d 0) := by ring
    _ = ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
        ((-d (k + 1)) - (-d k)) := hTel.symm
    _ = ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
        (d k - d (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring

/-- Each genuine adjacent pair-observable increment is the difference of the two
single-trajectory source-background increments. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF_eq_left_sub_right
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (k : ℕ)
    (hk : k + 1 ≤ Fintype.card C.base.geometry.Edge)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) :
    C.independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF
        target O k w =
      C.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
          (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
          target O (Fintype.card C.base.geometry.Edge) k w.2.1 -
        C.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
          (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
          target O (Fintype.card C.base.geometry.Edge) k w.2.2 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleAdjacentPairObservableTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
      C target O k (k.le_succ.trans hk) w,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
      C target O (k + 1) hk w]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) k (k.le_succ.trans hk) w.2.1,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) (k + 1) hk w.2.1,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) k (k.le_succ.trans hk) w.2.2,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) (k + 1) hk w.2.2]
  ring

/-- The complete pair-observable endpoint transport is exactly the difference of
the two complete single-trajectory endpoint transports. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_left_sub_right
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
        target O w =
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
          target O (Fintype.card C.base.geometry.Edge) (w.1, w.2.1) -
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
          target O (Fintype.card C.base.geometry.Edge) (w.1, w.2.2) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
      C target O 0 (Nat.zero_le _) w,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankPairObservableBCF_of_le
      C target O (Fintype.card C.base.geometry.Edge) le_rfl w]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) 0 (Nat.zero_le _) w.2.1,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge)
        (Fintype.card C.base.geometry.Edge) le_rfl w.2.1,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge) 0 (Nat.zero_le _) w.2.2,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O (Fintype.card C.base.geometry.Edge)
        (Fintype.card C.base.geometry.Edge) le_rfl w.2.2]
  ring

/-- The complete double endpoint pair-observable transport is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
        target O) := by
  have hSingle :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_continuous
      C target O (Fintype.card C.base.geometry.Edge)
  have hLeftMap : Continuous
      (fun w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier =>
        (w.1, w.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hRightMap : Continuous
      (fun w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier =>
        (w.1, w.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  rw [show
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
        target O =
      (fun w =>
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
            target O (Fintype.card C.base.geometry.Edge) (w.1, w.2.1) -
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
            target O (Fintype.card C.base.geometry.Edge) (w.1, w.2.2)) by
      funext w
      exact
        continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_left_sub_right
          C target O w]
  exact (hSingle.comp hLeftMap).sub (hSingle.comp hRightMap)

/-- Pointwise square cost of the complete double endpoint pair-observable
transport. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : C.independentPairHybridTargetTrajectoryDoubleJointCarrier) : ℝ :=
  (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
    target O w) ^ 2

/-- The double endpoint square integrand is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
        target O) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_continuous
      C target O).pow 2

/-- The double endpoint square is integrable on the joint probability carrier. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
        target O)
      (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_continuous
      C target O).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Jointly averaged square transport of the complete rankwise conditional-pair
observable process. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ w,
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
      target O w
    ∂C.independentPairHybridTargetTrajectoryDoubleJointMeasure target

/-- Fixed-original-pair version of the double endpoint pair-observable energy. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  ∫ xy,
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
      target O (z, xy)
    ∂trajectory.prod trajectory

/-- Exact disintegration of the double endpoint energy over the original
independent Gibbs pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
          target O z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryDoubleKernel target
  let f :=
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
      target O
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_integrable
      C target O
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure]
      using hJointNamed
  have hFubini := Measure.integral_compProd hJoint
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
  change (∫ w, f w ∂(μ ⊗ₘ κ)) = _
  calc
    (∫ w, f w ∂(μ ⊗ₘ κ)) =
      ∫ z, ∫ xy, f (z, xy) ∂κ z ∂μ := hFubini
    _ = ∫ z,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
          target O z ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleKernel_apply]
        unfold
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        rfl

/-- The fixed-pair double endpoint energy is at most four times the corresponding
single-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_le_four_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z ≤
      4 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) z := by
  let n := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target n
  let transport : ((i : Finset.Iic n) → C.base.Gauge) → ℝ := fun x =>
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
      (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
      target O n x
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hTransport : Integrable (fun x => (transport x) ^ 2) trajectory := by
    simpa [transport, trajectory] using
      continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_sq_integrable
        C z.1 z.2
          (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
          target O n
  have hLeft : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        (transport xy.1) ^ 2)
      (trajectory.prod trajectory) :=
    hTransport.comp_fst trajectory
  have hRight : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        (transport xy.2) ^ 2)
      (trajectory.prod trajectory) :=
    hTransport.comp_snd trajectory
  have hDouble : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O (z, xy))
      (trajectory.prod trajectory) := by
    exact
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_continuous
        C target O).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hUpper : Integrable
      (fun xy : C.independentPairHybridTargetTrajectoryDoubleCarrier =>
        2 * (transport xy.1) ^ 2 + 2 * (transport xy.2) ^ 2)
      (trajectory.prod trajectory) :=
    (hLeft.const_mul 2).add (hRight.const_mul 2)
  have hPoint (xy : C.independentPairHybridTargetTrajectoryDoubleCarrier) :
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O (z, xy) ≤
        2 * (transport xy.1) ^ 2 + 2 * (transport xy.2) ^ 2 := by
    have hEq :
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF
            target O (z, xy) =
          transport xy.1 - transport xy.2 := by
      simpa [transport,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF]
        using
          continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_left_sub_right
            C target O (z, xy)
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    rw [hEq]
    nlinarith [sq_nonneg (transport xy.1 + transport xy.2)]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
  dsimp only
  calc
    (∫ xy,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
          target O (z, xy) ∂trajectory.prod trajectory) ≤
      ∫ xy,
        (2 * (transport xy.1) ^ 2 + 2 * (transport xy.2) ^ 2)
        ∂trajectory.prod trajectory := by
          exact integral_mono hDouble hUpper hPoint
    _ = 2 * (∫ xy, (transport xy.1) ^ 2 ∂trajectory.prod trajectory) +
        2 * (∫ xy, (transport xy.2) ^ 2 ∂trajectory.prod trajectory) := by
      rw [integral_add (hLeft.const_mul 2) (hRight.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ = 2 * (∫ x, (transport x) ^ 2 ∂trajectory) +
        2 * (∫ x, (transport x) ^ 2 ∂trajectory) := by
      rw [MeasureTheory.integral_fun_fst, MeasureTheory.integral_fun_snd]
      simp
    _ = 4 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O n z := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
      dsimp [transport, trajectory, n]
      ring

/-- The fixed-pair double endpoint-energy function is integrable under the
independent Gibbs-pair law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryDoubleKernel target
  let f :=
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
      target O
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF_integrable
      C target O
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure]
      using hJointNamed
  have hOuter : Integrable (fun z => ∫ xy, f (z, xy) ∂κ z) μ := by
    simpa using hJoint.integral_compProd
  apply hOuter.congr
  exact Filter.Eventually.of_forall fun z => by
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleKernel_apply]
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
    rfl

/-- The global double endpoint pair-observable energy is at most four times the
single-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_four_single
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      4 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hDouble :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_integrable
      C target O
  have hSingle :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
      C target O (Fintype.card C.base.geometry.Edge) le_rfl
  calc
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O =
      ∫ z,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
          target O z ∂μ := by
      simpa [μ] using
        continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_integral_fiber
          C target O
    _ ≤ ∫ z,
        4 *
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
            target O (Fintype.card C.base.geometry.Edge) z ∂μ := by
      apply integral_mono hDouble (hSingle.const_mul 4)
      intro z
      exact
        continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_le_four_single
          C target O z
    _ = 4 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) := by
      rw [integral_const_mul]
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_eq_integral_fiber
        C target O (Fintype.card C.base.geometry.Edge) le_rfl]

/-- At full canonical rank, the double endpoint pair-observable energy is
controlled by four times the established source-overlap path plus variation
budget. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_boundaryResidualPath_add_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      4 *
        ((Fintype.card C.base.geometry.Edge : ℝ) *
          (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
            2 * ∑ source : C.base.geometry.Edge,
              (P.variation source) ^ 2)) := by
  calc
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ≤
      4 *
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
          target O (Fintype.card C.base.geometry.Edge) :=
      continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_le_four_single
        C target O
    _ ≤ 4 *
        ((Fintype.card C.base.geometry.Edge : ℝ) *
          (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
            2 * ∑ source : C.base.geometry.Edge,
              (P.variation source) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_le_boundaryResidualPath_add_variation
          C target O P)
        (by norm_num)

end

end MathlibAnalytic
end MGAP4D