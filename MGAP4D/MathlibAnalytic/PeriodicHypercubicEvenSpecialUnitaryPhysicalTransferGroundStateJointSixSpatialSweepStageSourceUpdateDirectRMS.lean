import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateMeanDecomposition
import MGAP4D.MathlibAnalytic.ProbabilityMeanL2Cauchy
import Mathlib.Tactic

/-!
# Direct source-update term as an exact RMS difference energy

PR #4717 decomposes one source update of a target conditional mean into:

1. a direct change of the concrete target section at one fixed target law;
2. a change of the target law, controlled by the full physical envelope.

PR #4719 supplies the coefficient-one probability-space Cauchy estimate

  | integral f dμ | <= sqrt (integral f^2 dμ).

This file applies that estimate to the direct section difference.  The center
cancels exactly, and bounded-concrete representatives provide genuine L2
membership under the literal physical target-fiber probability law.

No influence coefficient, cardinality factor, or arbitrary L2 quotient
representative is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance sourceUpdateDirectRMSSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceUpdateDirectRMSSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceUpdateDirectRMSSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceUpdateDirectRMSSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceUpdateDirectRMSSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceUpdateDirectRMSSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Squared direct section-change energy at one source update, evaluated under
one fixed target-fiber probability law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let retainedU :=
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
      target source hne retained u
  let retainedV :=
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
      target source hne retained v
  ∫ g,
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retainedU g -
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retainedV g) ^ 2
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source u)

/-- For a bounded concrete representative, the direct source-update mean
change is bounded by the square root of its exact direct difference energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_direct_difference_le_sqrt_directDifferenceEnergy_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained u)
          distinguishedSource k g₂ u center -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained v)
          distinguishedSource k g₂ u center| ≤
      Real.sqrt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
          H N hN beta hbeta target source hne F left B A retained
          distinguishedSource k g₂ u v) := by
  let retainedU :=
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
      target source hne retained u
  let retainedV :=
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
      target source hne retained v
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source u)
  let XU : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retainedU
  let XV : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retainedV
  let delta : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g => XU g - XV g
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)
  have hXUStrong : StronglyMeasurable XU := by
    simpa [XU] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retainedU
  have hXVStrong : StronglyMeasurable XV := by
    simpa [XV] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retainedV
  have hXUBound : ∀ g, ‖XU g‖ ≤ bound := by
    intro g
    simpa [
      XU,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection] using
      hbound
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
              retainedU))
  have hXVBound : ∀ g, ‖XV g‖ ≤ bound := by
    intro g
    simpa [
      XV,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection] using
      hbound
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
              retainedV))
  have hXU : MemLp XU 2 μ :=
    MemLp.of_bound hXUStrong.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hXUBound)
  have hXV : MemLp XV 2 μ :=
    MemLp.of_bound hXVStrong.aestronglyMeasurable bound
      (Filter.Eventually.of_forall hXVBound)
  have hDelta : MemLp delta 2 μ := by
    simpa [delta] using hXU.sub hXV
  have hXUInt : Integrable XU μ := hXU.integrable one_le_two
  have hXVInt : Integrable XV μ := hXV.integrable one_le_two
  have hCenteredU : Integrable (fun g => XU g - center) μ :=
    hXUInt.sub (integrable_const center)
  have hCenteredV : Integrable (fun g => XV g - center) μ :=
    hXVInt.sub (integrable_const center)
  have hDirectEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A retainedU
          distinguishedSource k g₂ u center -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A retainedV
          distinguishedSource k g₂ u center =
        ∫ g, delta g ∂μ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
    change
      (∫ g, XU g - center ∂μ) -
        (∫ g, XV g - center ∂μ) =
      ∫ g, delta g ∂μ
    rw [← integral_sub hCenteredU hCenteredV]
    apply integral_congr_ae
    filter_upwards with g
    dsimp [delta]
    ring
  rw [show
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne retained u = retainedU by rfl,
    show
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne retained v = retainedV by rfl,
    hDirectEq]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy,
    retainedU, retainedV, μ, delta, XU, XV] using
    (integral_abs_le_sqrt_integral_sq_of_memLp_two_probability μ delta hDelta)

/-- Combining the direct RMS estimate with the #4717 law-response
decomposition gives the exact one-step additive physical bound

  direct RMS + K(target,source) * target profile.
-/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_difference_le_sqrt_directDifferenceEnergy_add_envelope_mul_targetProfile_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hResponse :
      ∀ retained' :
          PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionTargetResponseBoundedBy
          H N hN beta hbeta target F left B A retained'
          distinguishedSource k g₂ center profile)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained u)
          distinguishedSource k g₂ u center -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained v)
          distinguishedSource k g₂ v center| ≤
      Real.sqrt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
          H N hN beta hbeta target source hne F left B A retained
          distinguishedSource k g₂ u v) +
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile target := by
  have hSplit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_difference_le_direct_add_envelope_mul_targetProfile
      H N hN beta hbeta target F left B A retained distinguishedSource
      k g₂ center profile hResponse source hne u v
  have hDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_direct_difference_le_sqrt_directDifferenceEnergy_of_bounded
      H N hN beta hbeta target source hne F hF bound hbound
      left B A retained distinguishedSource k g₂ u v center
  exact hSplit.trans (add_le_add hDirect (le_refl _))

end

end MGAP4D.MathlibAnalytic
