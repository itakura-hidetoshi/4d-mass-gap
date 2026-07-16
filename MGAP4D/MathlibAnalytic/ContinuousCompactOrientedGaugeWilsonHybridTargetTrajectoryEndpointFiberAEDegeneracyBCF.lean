import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointStrictCorrelationRatioBCF
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The complete fixed-original-pair target-trajectory carrier. -/
abbrev
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberCarrier
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :=
  (i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge

/-- The single-trajectory endpoint transport viewed as a function on one fixed
original Gibbs-pair trajectory fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier) : ℝ :=
  C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    target O (Fintype.card C.base.geometry.Edge) (z, x)

/-- The fixed-pair endpoint transport is continuous on the complete trajectory
fiber. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_continuous
      C target O (Fintype.card C.base.geometry.Edge)).comp
      (continuous_const.prodMk continuous_id)

/-- The square of the fixed-pair endpoint transport is integrable under the
complete trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
          target O z x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_continuous
      C target O z).pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- The fixed-pair endpoint transport belongs to `L²` of its complete trajectory
law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_memLp_two
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    MemLp
      (C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z)
      2
      (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)) := by
  apply
    (memLp_two_iff_integrable_sq
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_continuous
        C target O z).aestronglyMeasurable).2
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_sq_integrable
      C target O z

/-- The fixed-pair conditional-variance gap is exactly the ordinary probability
variance of the endpoint transport under the complete trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_variance
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z =
      ProbabilityTheory.variance
        (C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
          target O z)
        (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
          (Fintype.card C.base.geometry.Edge)) := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hT : MemLp T 2 trajectory := by
    simpa [T, trajectory] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_memLp_two
        C target O z
  simpa [trajectory, T,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportSqBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberMeanTransportBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF]
    using (ProbabilityTheory.variance_eq_sub hT).symm

/-- The canonical degeneracy predicate: the endpoint transport equals its own
conditional mean almost everywhere on a fixed trajectory fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  ∀ᵐ x ∂trajectory, T x = ∫ y, T y ∂trajectory

/-- Fixed-pair variance vanishes exactly when the endpoint transport is almost
everywhere equal to its conditional mean. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hT : MemLp T 2 trajectory := by
    simpa [T, trajectory] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_memLp_two
        C target O z
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_variance]
  constructor
  · intro hZero
    have hAE := ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hT hZero
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF,
      trajectory, T] using hAE
  · intro hAE
    have hAE' : ∀ᵐ x ∂trajectory, T x = ∫ y, T y ∂trajectory := by
      simpa [
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF,
        trajectory, T] using hAE
    rw [ProbabilityTheory.variance_eq_integral hT.aemeasurable]
    apply integral_eq_zero_of_ae
    filter_upwards [hAE'] with x hx
    rw [hx]
    simp

/-- The fixed-pair iid double endpoint energy is the integral of the squared
difference of the two endpoint transports. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_integral_pairwise_transport_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z =
      ∫ xy,
        (C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
            target O z xy.1 -
          C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
            target O z xy.2) ^ 2
        ∂(C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
            (Fintype.card C.base.geometry.Edge)).prod
          (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
            (Fintype.card C.base.geometry.Edge)) := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
  dsimp only
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun xy => by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableIntegrandBCF
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableTransportBCF_eq_left_sub_right]
    rfl

/-- Pairwise almost-everywhere equality of two iid endpoint transports on one
fixed original Gibbs-pair fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  ∀ᵐ xy ∂trajectory.prod trajectory, T xy.1 = T xy.2

/-- The fixed-pair iid double endpoint energy vanishes exactly when the two iid
endpoint transports agree almost everywhere. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_zero_iff_pairwise_ae_equal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
        target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  have hTContinuous : Continuous T := by
    simpa [T] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_continuous
        C target O z
  have hIntegrable : Integrable
      (fun xy => (T xy.1 - T xy.2) ^ 2)
      (trajectory.prod trajectory) :=
    (((hTContinuous.comp continuous_fst).sub
      (hTContinuous.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_integral_pairwise_transport_sq]
  change (∫ xy, (T xy.1 - T xy.2) ^ 2 ∂trajectory.prod trajectory) = 0 ↔ _
  rw [integral_eq_zero_iff_of_nonneg]
  · simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF,
      trajectory, T, sub_eq_zero]
  · exact fun _ => sq_nonneg _
  · exact hIntegrable

/-- Pairwise iid equality and almost-everywhere constancy at the conditional mean
are equivalent descriptions of the same fixed-fiber degeneracy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF_iff_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_zero_iff_pairwise_ae_equal
      C target O z).symm.trans
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_double_eq_zero
        C target O z).symm.trans
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
          C target O z))

/-- The fixed-pair iid double endpoint energy vanishes exactly when the endpoint
transport is almost everywhere constant at its conditional mean. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_eq_zero_iff_transport_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_double_eq_zero
      C target O z).symm.trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
        C target O z)

/-- Positive fixed-pair conditional variance is exactly failure of almost-everywhere
constancy of the endpoint transport. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_not_transport_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  have hNonneg :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_nonneg
      C target O z
  constructor
  · intro hPos hConstant
    have hZero :=
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
        C target O z).2 hConstant
    linarith
  · intro hNotConstant
    have hNe :
        C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
            target O z ≠ 0 := by
      intro hZero
      exact hNotConstant
        ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
          C target O z).1 hZero)
    exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Positive fixed-pair iid double endpoint energy is exactly failure of
a.e.-constancy of the single-trajectory endpoint transport. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_pos_iff_not_transport_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_double_pos
      C target O z).symm.trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_not_transport_ae_constant
        C target O z)

/-- Global degeneracy predicate: for almost every original Gibbs pair, the
single-trajectory endpoint transport is a.e. constant on its trajectory fiber. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∀ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
      target O z

/-- Equivalent global pairwise formulation of endpoint-transport degeneracy. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∀ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
      target O z

/-- The fixed-pair conditional-variance gap is integrable over the independent
Gibbs-pair base. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  have hDouble :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_integrable
      C target O
  refine (hDouble.const_mul (1 / 2 : ℝ)).congr ?_
  exact Filter.Eventually.of_forall fun z => by
    symm
    exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_half_double
        C target O z

/-- The global conditional-variance gap vanishes exactly when the endpoint
transport is fiberwise almost everywhere constant for almost every Gibbs pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_integral_fiber]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
  rw [integral_eq_zero_iff_of_nonneg]
  · constructor
    · intro hZero
      filter_upwards [hZero] with z hz
      exact
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
          C target O z).1 hz
    · intro hConstant
      filter_upwards [hConstant] with z hz
      exact
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_transport_ae_constant
          C target O z).2 hz
  · exact fun z =>
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_nonneg
        C target O z
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_integrable
        C target O

/-- Fiberwise pairwise equality and fiberwise a.e.-constancy are equivalent global
degeneracy predicates. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF_iff_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
  constructor
  · intro hPairwise
    filter_upwards [hPairwise] with z hz
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF_iff_ae_constant
        C target O z).1 hz
  · intro hConstant
    filter_upwards [hConstant] with z hz
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF_iff_ae_constant
        C target O z).2 hz

/-- The global iid double endpoint energy vanishes exactly under fiberwise
a.e.-constancy of the single-trajectory endpoint transport. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_zero_iff_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_double_eq_zero
      C target O).symm.trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_fiberwise_ae_constant
        C target O)

/-- The global iid double endpoint energy vanishes exactly under the equivalent
fiberwise pairwise-equality predicate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_zero_iff_fiberwise_pairwise_ae_equal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O = 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_eq_zero_iff_fiberwise_ae_constant
      C target O).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwisePairwiseAEEqualBCF_iff_fiberwise_ae_constant
        C target O).symm

/-- Positive global conditional variance is exactly failure of fiberwise endpoint
transport degeneracy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_not_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  have hNonneg :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_nonneg
      C target O
  constructor
  · intro hPos hDegenerate
    have hZero :=
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_fiberwise_ae_constant
        C target O).2 hDegenerate
    linarith
  · intro hNondegenerate
    have hNe :
        C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
            target O ≠ 0 := by
      intro hZero
      exact hNondegenerate
        ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_fiberwise_ae_constant
          C target O).1 hZero)
    exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Positive global iid double endpoint energy is exactly failure of fiberwise
almost-everywhere constancy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_pos_iff_not_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_double_pos
      C target O).symm.trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_not_fiberwise_ae_constant
        C target O)

end

end MathlibAnalytic
end MGAP4D
