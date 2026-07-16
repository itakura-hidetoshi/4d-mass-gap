import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The normalized real density of the exact single-link conditional law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.singleLinkBoltzmannFactor A target g /
    C.singleLinkPartitionFunction A target

/-- The exact single-link conditional density is pointwise strictly positive. -/
theorem continuous_compact_oriented_singleLinkConditionalDensityBCF_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 < C.singleLinkConditionalDensityBCF A target g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)

/-- The exact single-link conditional density is continuous. -/
theorem continuous_compact_oriented_singleLinkConditionalDensityBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkConditionalDensityBCF A target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityBCF
  exact
    (continuous_compact_oriented_singleLinkBoltzmannFactor C A target).div_const _

/-- Density representation of the exact single-link conditional law in terms of
its normalized positive continuous density. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensityBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target =
      (normalizedCompactHaar C.base.Gauge).withDensity
        (fun g => ENNReal.ofReal
          (C.singleLinkConditionalDensityBCF A target g)) := by
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  rfl

/-- Every exact single-link conditional law is positive on every nonempty open
Gauge region.  Equivalently, its density has full normalized-Haar support. -/
instance continuousCompactOriented_singleLinkConditionalMeasure_isOpenPosMeasureBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.IsOpenPosMeasure (C.singleLinkConditionalMeasure A target) := by
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensityBCF]
  let μ : Measure C.base.Gauge := normalizedCompactHaar C.base.Gauge
  let f : C.base.Gauge → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (C.singleLinkConditionalDensityBCF A target g)
  change Measure.IsOpenPosMeasure (μ.withDensity f)
  have hf : Measurable f :=
    (continuous_compact_oriented_singleLinkConditionalDensityBCF_continuous
      C A target).measurable.ennreal_ofReal
  refine ⟨?_⟩
  intro U hU hUne
  intro hZero
  have hBase : μ ({g | f g ≠ 0} ∩ U) = 0 :=
    (withDensity_apply_eq_zero (μ := μ) hf).1 hZero
  have hEverywhere : {g | f g ≠ 0} = Set.univ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ne_of_gt
      (ENNReal.ofReal_pos.2
        (continuous_compact_oriented_singleLinkConditionalDensityBCF_pos
          C A target g))
  rw [hEverywhere, Set.univ_inter] at hBase
  exact hU.measure_ne_zero μ hUne hBase

/-- The support of every exact single-link conditional law is the whole compact
Gauge group. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_support_eq_univBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (C.singleLinkConditionalMeasure A target).support = Set.univ := by
  exact Measure.support_eq_univ

/-- Every nonempty open Gauge region has positive exact conditional mass. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_open_posBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (region : Set C.base.Gauge)
    (hOpen : IsOpen region)
    (hNonempty : region.Nonempty) :
    0 < C.singleLinkConditionalMeasure A target region := by
  exact hOpen.measure_pos (C.singleLinkConditionalMeasure A target) hNonempty

/-- Every nonempty open Gauge region has nonzero exact conditional mass. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_open_ne_zeroBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (region : Set C.base.Gauge)
    (hOpen : IsOpen region)
    (hNonempty : region.Nonempty) :
    C.singleLinkConditionalMeasure A target region ≠ 0 :=
  ne_of_gt
    (continuous_compact_oriented_singleLinkConditionalMeasure_open_posBCF
      C A target region hOpen hNonempty)

/-- A concrete fixed-fiber endpoint innovation witness using two nonempty open
Gauge regions at one trajectory rank.  No separate measure-positivity assumptions
are needed because the exact conditional law has full support. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
    ∃ lower upper : Set C.base.Gauge,
      IsOpen lower ∧
      lower.Nonempty ∧
      IsOpen upper ∧
      upper.Nonempty ∧
      ∀ x ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
            rank lower,
        ∀ y ∈ C.independentPairHybridTargetTrajectoryEndpointCoordinateCylinderBCF
              rank upper,
          T x ≠ T y

/-- Two nonempty open conditional regions give the same quantitative lower bound
on endpoint innovation mass as their exact conditional masses. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionMassMul_le_innovationMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (lower upper : Set C.base.Gauge)
    (hLowerOpen : IsOpen lower)
    (hUpperOpen : IsOpen upper)
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
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionMassMul_le_innovationMassBCF
      C target O z rank lower upper hLowerOpen.measurableSet
        hUpperOpen.measurableSet hSeparate

/-- An open-region witness automatically supplies the exact conditional-region
witness from the previous layer. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_conditional_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
    at hWitness
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF
  dsimp only at hWitness ⊢
  rcases hWitness with
    ⟨rank, lower, upper, hLowerOpen, hLowerNonempty,
      hUpperOpen, hUpperNonempty, hSeparate⟩
  refine
    ⟨rank, lower, upper, hLowerOpen.measurableSet, hUpperOpen.measurableSet,
      ?_, ?_, hSeparate⟩
  · exact
      continuous_compact_oriented_singleLinkConditionalMeasure_open_ne_zeroBCF
        C (C.independentPairHybridConfiguration z.1 z.2 rank.1) target
          lower hLowerOpen hLowerNonempty
  · exact
      continuous_compact_oriented_singleLinkConditionalMeasure_open_ne_zeroBCF
        C (C.independentPairHybridConfiguration z.1 z.2 rank.1) target
          upper hUpperOpen hUpperNonempty

/-- A fixed-fiber open-region witness forces positive endpoint innovation mass. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_innovationMass_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_innovationMass_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_conditional_region_witness
        C target O z hWitness)

/-- A fixed-fiber open-region witness forces positive conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_gap_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_conditional_region_witness
        C target O z hWitness)

/-- A fixed-fiber open-region witness forces positive iid double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalRegionInnovationWitnessBCF_implies_double_energy_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_conditional_region_witness
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying open-region endpoint innovation
witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z

/-- Gibbs-pair mass of fibers carrying open-region innovation witnesses. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ≥0∞ :=
  (C.gibbsMeasure.prod C.gibbsMeasure)
    {z : C.base.Configuration × C.base.Configuration |
      C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
        target O z}

/-- Open-region witness base mass is nonzero exactly when such witnesses occur on
a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF
        target O ≠ 0 ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let P := fun z : C.base.Configuration × C.base.Configuration =>
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z
  change μ {z : C.base.Configuration × C.base.Configuration | P z} ≠ 0 ↔
    ∃ᵐ z ∂μ, P z
  exact (frequently_ae_iff (μ := μ) (p := P)).symm

/-- Open-region witness base mass is positive exactly when such witnesses occur on
a non-null Gibbs-pair family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF_pos_iff_fiberwise_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O := by
  constructor
  · intro hPos
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).1 (ne_of_gt hPos)
  · intro hWitness
    have hNe :=
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportOpenRegionInnovationWitnessBaseMassBCF_ne_zero_iff_fiberwise_witness
        C target O).2 hWitness
    exact lt_of_le_of_ne (zero_le _) (Ne.symm hNe)

/-- A non-null family of open-region witnesses produces the exact conditional-region
witness family from the previous layer. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_fiberwise_conditional_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF_implies_conditional_region_witness
      C target O z hz

/-- A non-null family of open-region witnesses forces positive global conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_fiberwise_conditional_region_witness
        C target O hWitness)

/-- A non-null family of open-region witnesses forces positive global iid double
endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_double_energy_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_fiberwise_conditional_region_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of open-region witnesses forces
the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_fiberwise_conditional_region_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of open-region witnesses produces
a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseConditionalRegionInnovationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseOpenRegionInnovationWitnessBCF_implies_fiberwise_conditional_region_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
