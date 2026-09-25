import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawSecondCenter
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourcePairExactReorderedLaw
import Mathlib.Tactic

/-!
# Exact reordering of the first-law cross energy

PR #4779 chooses the actual second target-law fiber mean as the pointwise
center.  The remaining nontrivial RMS contribution is the first-law cross
energy: the target sample is drawn from the law based at A[source <- u], while
the observable section and its center are frozen at A[source <- v].

The source-pair exact reordered law from PR #4727 is designed precisely for
this situation.  After absorbing the first source sample into

  C = A[source <- u],

the second source sample remains as v and the first-law target sample remains
distributed by the target law based at C.

This file makes that coordinate change explicit.  It constructs a canonical
section

  (C,v) |-> (C,(C(source),v))

of the reordered source-pair map, proves that the second-law center factors
through the reordered coordinates, and transports the complete first-law
cross-energy ENNReal integral exactly to the fully ordered law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

No inequality, response coefficient, or finite-cardinality factor is
introduced.  The next theorem unit may compare the resulting ordered cross
energy with the genuine target residual/profile.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairFirstCrossEnergyReorderedSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairFirstCrossEnergyReorderedSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairFirstCrossEnergyReorderedSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairFirstCrossEnergyReorderedSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairFirstCrossEnergyReorderedSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairFirstCrossEnergyReorderedSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical source-pair representative of one ordered pair (C,v).

The first source sample is chosen to be the source coordinate already stored
in C, so the first update leaves C unchanged. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (Cv.1, (Cv.1 source, Cv.2))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection_measurable
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
        H N source) := by
  have hEval :
      Measurable
        (fun Cv :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Cv.1 source) :=
    (measurable_pi_apply source).comp measurable_fst
  exact measurable_fst.prodMk (hEval.prodMk measurable_snd)

/-- The canonical ordered section is a right inverse of the PR #4727 reordered
map. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_orderedSection
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source Cv) =
      Cv := by
  apply Prod.ext
  · unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
    exact Function.update_eq_self source Cv.1
  · rfl

/-- Reconstructing a source-pair point from its reordered coordinates preserves
the second-updated background exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection_reorderedMap
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
        H N source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
          H N source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
        H N source z := by
  funext e
  by_cases he : e = source
  · subst e
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground,
      he]

/-- The second-law center written purely on the ordered (C,v) carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
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
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
    H N hN beta hbeta B distinguishedSource source target k g₂
    F left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_stronglyMeasurable
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left).comp_measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection_measurable
        H N source)

/-- The original second-law center factors through the exact reordered
coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_eq_ordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z) := by
  let z' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source z)
  have hBackground :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
          H N source z' =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
          H N source z := by
    simpa [z'] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection_reorderedMap
        H N source z
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply]
  rw [hBackground]
  apply integral_congr_ae
  filter_upwards with g
  simp [
    z',
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
    hBackground]

/-- First-law cross residual on the fully ordered ((C,v),g) carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
    H N target source F left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
      H N hN beta hbeta B distinguishedSource source target k g₂ F left Cvg.1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cvg.1,
      Cvg.2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual_stronglyMeasurable
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
        H N hN beta hbeta B distinguishedSource source target k g₂ F left) := by
  have hEmbed :
      Measurable
        (fun Cvg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
              H N source Cvg.1,
            Cvg.2)) :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection_measurable
      H N source).comp measurable_fst).prodMk measurable_snd
  have hZero :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_stronglyMeasurable
      H N target source F hF left 0).comp_measurable hEmbed
  have hCenter :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left).comp_measurable
      measurable_fst
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
    Function.comp_def] using hZero.sub hCenter

/-- The original first-law residual centered by the second-law mean factors
pointwise through the reordered triple coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCrossResidual_eq_ordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (zg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
        H N target source F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left zg.1)
        zg =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
          H N source zg) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_eq_ordered
      H N hN beta hbeta B distinguishedSource source target k g₂ F left zg.1]
  have hBackground :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection_reorderedMap
      H N source zg.1
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
  simp only
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
  rw [hBackground]

/-- ENNReal square of the ordered first-law cross residual. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cvg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual
      H N hN beta hbeta B distinguishedSource source target k g₂ F left Cvg) ^ 2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_measurable
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
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂ F left) := by
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossResidual_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  exact ENNReal.continuous_ofReal.measurable.comp
    (hResidual.measurable.pow_const 2)

/-- Exact PR #4727 reordering of the complete first-law cross energy centered
at the actual second-law mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCrossEnergy_lintegral_eq_ordered
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
    (∫⁻ zg,
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
            H N target source F left
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
              H N hN beta hbeta B distinguishedSource source target k g₂ F left zg.1)
            zg) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
  let Phi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  have hPhi : Measurable Phi := by
    simpa [Phi] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_measurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  calc
    (∫⁻ zg,
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
            H N target source F left
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
              H N hN beta hbeta B distinguishedSource source target k g₂ F left zg.1)
            zg) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ zg,
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
            H N source zg)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      apply lintegral_congr
      intro zg
      unfold Phi
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCrossResidual_eq_ordered
          H N hN beta hbeta B distinguishedSource source target k g₂ F left zg]
    _ =
      ∫⁻ Cvg, Phi Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_lintegral_reordered
        H N hN beta hbeta B distinguishedSource source target k g₂ Phi hPhi
    _ =
      ∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      rfl

end

end MGAP4D.MathlibAnalytic
