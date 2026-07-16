import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointPositiveMeasureInnovationBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The cylinder in the complete target-trajectory fiber selected by requiring one
rank coordinate to lie in a prescribed gauge region. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (region : Set C.base.Gauge) :
    Set C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
  {x | x rank ∈ region}

/-- A concrete fixed-fiber coordinate innovation witness.  One trajectory rank has
 two gauge regions whose cylinders both have nonzero trajectory measure, and the
 endpoint transport separates every cross-cylinder pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
    ∃ lower upper : Set C.base.Gauge,
      trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower) ≠ 0 ∧
      trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank upper) ≠ 0 ∧
      ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower,
        ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper,
          T x ≠ T y

/-- A separated coordinate-cylinder rectangle gives a quantitative lower bound on
 the fixed-fiber innovation mass. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMassMul_le_innovationMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (lower upper : Set C.base.Gauge)
    (hSeparate :
      ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower,
        ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper,
          C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
              target O z x ≠
            C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
              target O z y) :
    let trajectory :=
      C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)
    trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower) *
        trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank upper) ≤
      C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
        target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  let lowerCylinder :=
    C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
      rank lower
  let upperCylinder :=
    C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
      rank upper
  change
    trajectory lowerCylinder * trajectory upperCylinder ≤
      (trajectory.prod trajectory)
        {xy : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier ×
            C.independentPairHybridTargetTrajectoryEndpointFiberCarrier |
          T xy.1 ≠ T xy.2}
  rw [← Measure.prod_prod]
  apply measure_mono
  intro xy hxy
  exact hSeparate xy.1 hxy.1 xy.2 hxy.2

/-- A fixed-fiber coordinate innovation witness forces positive innovation mass. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovationMass_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
      target O z := by
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
      (Fintype.card C.base.geometry.Edge)
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  change
    ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
      ∃ lower upper : Set C.base.Gauge,
        trajectory
            (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank lower) ≠ 0 ∧
        trajectory
            (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper) ≠ 0 ∧
        ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank lower,
          ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
                rank upper,
            T x ≠ T y at hWitness
  rcases hWitness with ⟨rank, lower, upper, hLower, hUpper, hSeparate⟩
  have hLowerPos :
      0 < trajectory
        (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
          rank lower) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hLower)
  have hUpperPos :
      0 < trajectory
        (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
          rank upper) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hUpper)
  have hProductNe :
      trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower) *
        trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank upper) ≠ 0 :=
    mul_ne_zero hLower hUpper
  have hProductPos :
      0 < trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower) *
        trajectory
          (C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank upper) :=
    lt_of_le_of_ne (zero_le _) (Ne.symm hProductNe)
  exact lt_of_lt_of_le hProductPos
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateCylinderMassMul_le_innovationMassBCF
      C target O z rank lower upper hSeparate)

/-- A fixed-fiber coordinate innovation witness forces the canonical innovation
predicate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointFiberInnovationBCF
      target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF_pos_iff_innovation
      C target O z).1
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovationMass_pos
        C target O z hWitness)

/-- A fixed-fiber coordinate innovation witness forces positive conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_innovation
      C target O z).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovation
        C target O z hWitness)

/-- A fixed-fiber coordinate innovation witness forces positive iid double endpoint
energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
      target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF_pos_iff_innovation
      C target O z).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovation
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying concrete coordinate innovation witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
      target O z

/-- The Gibbs-pair mass of fibers carrying a coordinate innovation witness. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ≥0∞ :=
  (C.gibbsMeasure.prod C.gibbsMeasure)
    {z : C.base.Configuration × C.base.Configuration |
      C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
        target O z}

/-- Coordinate-witness base mass is nonzero exactly when coordinate witnesses occur
on a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF
        target O ≠ 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let P := fun z : C.base.Configuration × C.base.Configuration =>
    C.independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF
      target O z
  change μ {z : C.base.Configuration × C.base.Configuration | P z} ≠ 0 ↔
    ∃ᵐ z ∂μ, P z
  exact (frequently_ae_iff (μ := μ) (p := P)).symm

/-- Coordinate-witness base mass is positive exactly when coordinate witnesses occur
on a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF_pos_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O := by
  constructor
  · intro hPos
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).1 (ne_of_gt hPos)
  · intro hWitness
    have hNe :=
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportCoordinateInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).2 hWitness
    exact lt_of_le_of_ne (zero_le _) (Ne.symm hNe)

/-- A non-null family of coordinate witnesses implies the canonical global
fiberwise innovation predicate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_fiberwise_innovation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInnovationBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateInnovationWitnessBCF_implies_innovation
      C target O z hz

/-- A non-null family of coordinate witnesses forces positive global conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_fiberwise_innovation
      C target O).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_fiberwise_innovation
        C target O hWitness)

/-- A non-null family of coordinate witnesses forces positive global iid double
endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
      target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF_pos_iff_fiberwise_innovation
      C target O).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_fiberwise_innovation
        C target O hWitness)

/-- With positive native energy, a non-null family of coordinate witnesses forces
the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_lt_one_iff_fiberwise_innovation
      C target O hNative).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_fiberwise_innovation
        C target O hWitness)

/-- With positive native energy, a non-null family of coordinate witnesses produces
an explicit strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryExistsStrictCorrelationFactorBCF_iff_fiberwise_innovation
      C target O hNative).2
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateInnovationWitnessBCF_implies_fiberwise_innovation
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
