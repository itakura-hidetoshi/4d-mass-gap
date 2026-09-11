import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The mass of a measurable coordinate cylinder under the complete target-trajectory
law is exactly the corresponding single-link conditional mass at that hybrid rank. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMeasure_eq_conditionalRegionMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (region : Set C.base.Gauge)
    (hRegion : MeasurableSet region) :
    let trajectory :=
      C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)
    trajectory
        (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
          rank region) =
      C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target region := by
  let m := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target m
  let eval : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier →
      C.base.Gauge := fun x => x rank
  have hRank : rank.1 ≤ m := mem_Iic.1 rank.2
  have hEval : Measurable eval := measurable_pi_apply rank
  have hEvalEq :
      eval =
        (fun x : (i : Finset.Iic m) → C.base.Gauge =>
          x ⟨rank.1, mem_Iic.2 hRank⟩) := by
    funext x
    apply congrArg x
    exact Subtype.ext (by rfl)
  have hMap :
      Measure.map eval trajectory =
        C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target := by
    rw [hEvalEq]
    exact
      continuous_compact_oriented_map_coordinate_independentPairHybridTargetTrajectoryMeasure
        C z.1 z.2 target rank.1 m hRank
  change
    trajectory
        (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
          rank region) =
      C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target region
  calc
    trajectory
        (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
          rank region) =
      Measure.map eval trajectory region := by
        rw [Measure.map_apply hEval hRegion]
        rfl
    _ = C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target region := by
      rw [hMap]

/-- A fixed-fiber innovation witness expressed entirely through exact hybrid
conditional region masses, together with endpoint-transport separation on the
corresponding trajectory cylinders. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
    ∃ lower upper : Set C.base.Gauge,
      MeasurableSet lower ∧
      MeasurableSet upper ∧
      C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target lower ≠ 0 ∧
      C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target upper ≠ 0 ∧
      ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower,
        ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper,
          T x ≠ T y

/-- Two exact hybrid conditional region masses give a quantitative lower bound on
the fixed-fiber endpoint innovation mass whenever the corresponding trajectory
cylinders are transport-separated. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionMassMul_le_innovationMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (lower upper : Set C.base.Gauge)
    (hLower : MeasurableSet lower)
    (hUpper : MeasurableSet upper)
    (hSeparate :
      ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower,
        ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper,
          C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
              target O z x ≠
            C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
              target O z y) :
    C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target lower *
        C.singleLinkConditionalMeasure
          (C.independentPairHybridConfiguration z.1 z.2 rank.1) target upper ≤
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
        target O z := by
  rw [←
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMeasure_eq_conditionalRegionMassBCF
      C target z rank lower hLower]
  rw [←
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMeasure_eq_conditionalRegionMassBCF
      C target z rank upper hUpper]
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMassMul_le_innovationMassBCF
      C target O z rank lower upper hSeparate

/-- An exact conditional-region witness produces the trajectory-coordinate witness
from the previous layer. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_coordinate_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
    at hWitness
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
  dsimp only at hWitness ⊢
  rcases hWitness with
    ⟨rank, lower, upper, hLowerMeas, hUpperMeas, hLower, hUpper, hSeparate⟩
  refine ⟨rank, lower, upper, ?_, ?_, hSeparate⟩
  · rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMeasure_eq_conditionalRegionMassBCF
        C target z rank lower hLowerMeas]
    exact hLower
  · rw [
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMeasure_eq_conditionalRegionMassBCF
        C target z rank upper hUpperMeas]
    exact hUpper

/-- A fixed-fiber conditional-region witness forces positive endpoint innovation
mass. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_innovationMass_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovationMass_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_coordinate_witness
        C target O z hWitness)

/-- A fixed-fiber conditional-region witness forces positive conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_gap_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_coordinate_witness
        C target O z hWitness)

/-- A fixed-fiber conditional-region witness forces positive iid double endpoint
energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_double_energy_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_coordinate_witness
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying exact conditional-region innovation
witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
      target O z

/-- Gibbs-pair mass of fibers carrying exact conditional-region witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ≥0∞ :=
  (C.gibbsMeasure.prod C.gibbsMeasure)
    {z : C.base.Configuration × C.base.Configuration |
      C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
        target O z}

/-- Conditional-region witness base mass is nonzero exactly when such witnesses
occur on a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF
        target O ≠ 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let P := fun z : C.base.Configuration × C.base.Configuration =>
    C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
      target O z
  change μ {z : C.base.Configuration × C.base.Configuration | P z} ≠ 0 ↔
    ∃ᵐ z ∂μ, P z
  exact (frequently_ae_iff (μ := μ) (p := P)).symm

/-- Conditional-region witness base mass is positive exactly when such witnesses
occur on a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF_pos_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O := by
  constructor
  · intro hPos
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).1 (ne_of_gt hPos)
  · intro hWitness
    have hNe :=
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportConditionalRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).2 hWitness
    exact lt_of_le_of_ne (zero_le _) (Ne.symm hNe)

/-- A non-null family of exact conditional-region witnesses produces the existing
fiberwise coordinate-witness predicate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_fiberwise_coordinate_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_coordinate_witness
      C target O z hz

/-- A non-null family of exact conditional-region witnesses forces positive global
conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_fiberwise_coordinate_witness
        C target O hWitness)

/-- A non-null family of exact conditional-region witnesses forces positive global
iid double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_double_energy_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_fiberwise_coordinate_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of exact conditional-region
witnesses forces the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_fiberwise_coordinate_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of exact conditional-region
witnesses produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_fiberwise_coordinate_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
