import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairOrderedCrossResidualLiteral
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Exact Pythagorean decomposition of the ordered first cross energy

PR #4781 exposes the remaining first-law cross residual in literal ordered
coordinates.  At a fixed ordered source/background point (C,v), let

  X_v(g) = F(left, C[source <- v][target <- g]),

sampled under the old target law kappa_target(C).  The residual in PR #4781 is

  X_v(g) - m_new,

where m_new is the mean of the same X_v under the new target law based at
C[source <- v].

This file inserts the old-law mean

  m_old = E_{kappa_target(C)} X_v

and proves the exact scalar Pythagorean identity

  E_old (X_v - m_new)^2
    = E_old (X_v - m_old)^2 + (m_old - m_new)^2.

No triangle inequality and no factor two are used.

The same mean gap is exactly the concrete target-law response from PR #4775,
evaluated on the canonical ordered source-pair representative.  Hence the
cross energy splits into a true old-law variance plus the squared response.

This is the sharp algebraic decomposition needed before deciding where the
remaining law comparison genuinely enters.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairFirstCrossEnergyPythagoreanSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairFirstCrossEnergyPythagoreanSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairFirstCrossEnergyPythagoreanSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairFirstCrossEnergyPythagoreanSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairFirstCrossEnergyPythagoreanSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairFirstCrossEnergyPythagoreanSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- On a probability space, squared distance from an arbitrary scalar center is
exactly variance plus squared distance between the mean and that center. -/
private theorem probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ x, (X x - c) ^ 2 ∂μ) =
      (∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ) +
        ((∫ y, X y ∂μ) - c) ^ 2 := by
  have hShift : MemLp (fun x => X x - c) 2 μ :=
    hX.sub (memLp_const c)
  have hXIntegrable : Integrable X μ :=
    hX.integrable one_le_two
  have hMeanShift :
      (∫ x, X x - c ∂μ) = (∫ x, X x ∂μ) - c := by
    rw [integral_sub hXIntegrable (integrable_const c)]
    simp
  have hVarShift :
      variance (fun x => X x - c) μ =
        (∫ x, (X x - c) ^ 2 ∂μ) -
          (∫ x, X x - c ∂μ) ^ 2 := by
    simpa only [Pi.pow_apply] using
      (variance_eq_sub hShift)
  have hVarInvariant :
      variance (fun x => X x - c) μ = variance X μ :=
    variance_sub_const hX.aestronglyMeasurable c
  have hVarBase :
      variance X μ =
        ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ := by
    exact variance_eq_integral hX.aestronglyMeasurable.aemeasurable
  rw [hVarInvariant, hVarBase, hMeanShift] at hVarShift
  linarith

/-- Old-target-law mean of the frozen section on ordered coordinates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
    H N hN beta hbeta B distinguishedSource source target k g₂
    F left 0
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv)

/-- The old-law mean is strongly measurable on the ordered (C,v) carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left 0).comp_measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection_measurable
        H N source)

/-- Old-law variance energy of the frozen section, centered at its own old-law
mean. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
    H N hN beta hbeta B distinguishedSource source target k g₂
    F left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left Cv)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv)

/-- Fiberwise exact Pythagorean decomposition of the first-law energy centered
at an arbitrary scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_eq_firstVariance_add_meanGapSq_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left center
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv - center) ^ 2 := by
  let z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂ z
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
            H N source z))
        g
  letI : IsProbabilityMeasure μ := by
    infer_instance
  have hEmbed :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => (z, g)) := by
    exact measurable_const.prodMk measurable_id
  have hXStrong : StronglyMeasurable X := by
    have h :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_stronglyMeasurable
        H N target source F hF left 0).comp_measurable hEmbed
    simpa [
      X, Function.comp_def,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection] using h
  have hXBound : ∀ g, ‖X g‖ ≤ |bound| := by
    intro g
    simpa [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_norm_le
        H N target source F bound hbound left 0 (z, g)
  have hXLp : MemLp X 2 μ :=
    MemLp.of_bound hXStrong.aestronglyMeasurable |bound|
      (Filter.Eventually.of_forall hXBound)
  have hPyth :=
    probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq
      μ X hXLp center
  have hMean :
      (∫ g, X g ∂μ) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
    change
      (∫ g, X g ∂μ) =
        ∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
            H N target source F left 0 (z, g)
          ∂μ
    apply integral_congr_ae
    filter_upwards with g
    simp [
      X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
  change
    (∫ g, (X g - center) ^ 2 ∂μ) =
      (∫ g,
        (X g -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv) ^ 2 ∂μ) +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv - center) ^ 2
  simpa [hMean] using hPyth

/-- On ordered coordinates, the old-law mean minus the new-law mean is exactly
the concrete target-law response, provided target is off the source diagonal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedMeanGap_eq_responseOnCarrier
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
        H N hN beta hbeta target source F left B distinguishedSource
        k g₂ 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_eq]
  simp only [hne, if_false]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
  rfl

/-- Sharp ordered Pythagorean identity: cross energy equals old-law variance
plus the squared concrete target-law response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_secondMean_eq_firstVariance_add_responseSq_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
          H N hN beta hbeta target source F left B distinguishedSource
          k g₂ 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
            H N source Cv)) ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_eq_firstVariance_add_meanGapSq_of_bounded
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂ F left Cv)
      Cv,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedMeanGap_eq_responseOnCarrier
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F left Cv]

end

end MGAP4D.MathlibAnalytic
