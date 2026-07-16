import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointFiberAEDegeneracyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Positive-measure innovation on one fixed original Gibbs-pair fiber: two iid
complete trajectories give different endpoint transports on a set of nonzero
product measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
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
  ∃ᵐ xy ∂trajectory.prod trajectory, T xy.1 ≠ T xy.2

/-- The actual product-measure mass of the fixed-fiber endpoint-transport
innovation event. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ≥0∞ :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
      target O z
  (trajectory.prod trajectory) {xy | T xy.1 ≠ T xy.2}

/-- Fixed-fiber innovation is exactly failure of pairwise almost-everywhere
equality for the two iid endpoint transports. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_pairwise_ae_equal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF
  simp only [not_eventually]

/-- Fixed-fiber innovation is exactly failure of almost-everywhere constancy of
the single-trajectory endpoint transport. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_transport_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointFiberTransportAEConstantBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_pairwise_ae_equal
      C target O z).trans
      (not_congr
        (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportPairwiseAEEqualBCF_iff_ae_constant
          C target O z))

/-- The fixed-fiber innovation mass is nonzero exactly when the fixed-fiber
innovation predicate holds. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_ne_zero_iff_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
        target O z ≠ 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
  dsimp only
  exact frequently_ae_iff.symm

/-- The fixed-fiber innovation mass is positive exactly when the innovation event
has nonzero product measure. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_pos_iff_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z := by
  rw [pos_iff_ne_zero]
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_ne_zero_iff_innovation
      C target O z

/-- Positive fixed-pair conditional variance is exactly positive-measure
endpoint-transport innovation on the trajectory fiber. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_not_transport_ae_constant
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_transport_ae_constant
        C target O z).symm

/-- Positive fixed-pair iid double endpoint energy is exactly positive-measure
endpoint-transport innovation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_pos_iff_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_pos_iff_not_transport_ae_constant
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_transport_ae_constant
        C target O z).symm

/-- Positive fixed-fiber innovation mass and positive iid double endpoint energy
are equivalent. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_pos_iff_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
        target O z ↔
      0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_pos_iff_innovation
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_pos_iff_innovation
        C target O z).symm

/-- Global positive-measure innovation: on a non-null set of original Gibbs pairs,
the complete trajectory fiber itself has a positive-measure endpoint-transport
innovation event. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
      target O z

/-- Gibbs-pair measure of the set of original pairs whose trajectory fiber has
positive-measure endpoint-transport innovation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ≥0∞ :=
  (C.gibbsMeasure.prod C.gibbsMeasure)
    {z |
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
        target O z}

/-- Fiberwise innovation is exactly failure of the global fiberwise a.e.-constancy
predicate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF_iff_not_fiberwise_ae_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O ↔
      ¬ C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseAEConstantBCF
  rw [not_eventually]
  apply frequently_congr
  exact Filter.Eventually.of_forall fun z =>
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF_iff_not_transport_ae_constant
      C target O z).symm

/-- The Gibbs-pair base mass of innovative fibers is nonzero exactly when the
global fiberwise-innovation predicate holds. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF_ne_zero_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF
        target O ≠ 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
  exact frequently_ae_iff.symm

/-- The Gibbs-pair base mass of innovative fibers is positive exactly under
global fiberwise innovation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF_pos_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  rw [pos_iff_ne_zero]
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF_ne_zero_iff_fiberwise_innovation
      C target O

/-- Positive global conditional variance is exactly positive-measure innovation on
a non-null family of original Gibbs-pair trajectory fibers. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_not_fiberwise_ae_constant
      C target O).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF_iff_not_fiberwise_ae_constant
        C target O).symm

/-- Positive global iid double endpoint energy is exactly positive-measure
fiberwise innovation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_pos_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_pos_iff_not_fiberwise_ae_constant
      C target O).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF_iff_not_fiberwise_ae_constant
        C target O).symm

/-- Positive Gibbs-pair base mass of innovative fibers is equivalent to positive
global iid double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF_pos_iff_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF
        target O ↔
      0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportInnovationBaseMassBCF_pos_iff_fiberwise_innovation
      C target O).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_pos_iff_fiberwise_innovation
        C target O).symm

/-- With positive native one-link energy, the exact endpoint correlation ratio is
strictly below one exactly under positive-measure fiberwise innovation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_lt_one_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_lt_one_iff_gap_pos
      C target O hNative).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_fiberwise_innovation
        C target O)

/-- With positive native energy, existence of some strict endpoint correlation
factor is exactly positive-measure fiberwise innovation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryExistsStrictCorrelationFactorBCF_iff_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    (∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
        target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_exists_strict_correlation_factor
      C target O hNative).symm.trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_fiberwise_innovation
        C target O)

end

end MathlibAnalytic
end MGAP4D
