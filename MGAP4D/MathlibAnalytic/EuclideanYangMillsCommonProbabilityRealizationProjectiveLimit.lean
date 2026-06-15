import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveContinuumMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A simultaneous realization of all finite-dimensional marginals on one
common probability space.

This is the exact additional hypothesis needed for the direct pushforward route
to a projective-limit measure: one probability space carries a measurable full
field whose every finite restriction has the prescribed law. -/
structure EuclideanYangMillsCommonProbabilityRealization
    (F : EuclideanYangMillsProjectiveCylinderFamily) where
  sampleSpace : Type
  [sampleMeasurableSpace : MeasurableSpace sampleSpace]
  sourceMeasure : Measure sampleSpace
  sourceProbability : IsProbabilityMeasure sourceMeasure
  globalField : sampleSpace → F.Configuration
  globalField_measurable : Measurable globalField
  finiteLaw :
    ∀ J : Finset EuclideanFourSpace,
      sourceMeasure.map (fun ω => J.restrict (globalField ω)) =
        F.finiteMarginal J

attribute [instance]
  EuclideanYangMillsCommonProbabilityRealization.sampleMeasurableSpace

/-- The continuum measure induced by the common probability realization. -/
noncomputable def
    EuclideanYangMillsCommonProbabilityRealization.continuumMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    Measure F.Configuration :=
  R.sourceMeasure.map R.globalField

/-- Coordinate restriction from the full configuration space to a finite
subproduct is measurable. -/
theorem euclidean_yang_mills_finite_restriction_measurable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (J : Finset EuclideanFourSpace) :
    Measurable
      (J.restrict : F.Configuration → (∀ x : J, F.fieldValue x)) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- A common simultaneous realization produces a genuine projective-limit
measure. -/
theorem
    EuclideanYangMillsCommonProbabilityRealization.continuumMeasure_isProjectiveLimit
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    IsProjectiveLimit R.continuumMeasure F.finiteMarginal := by
  intro J
  have hrestrict :
      Measurable
        (J.restrict : F.Configuration → (∀ x : J, F.fieldValue x)) :=
    euclidean_yang_mills_finite_restriction_measurable J
  change
    (R.sourceMeasure.map R.globalField).map J.restrict =
      F.finiteMarginal J
  calc
    (R.sourceMeasure.map R.globalField).map J.restrict =
        R.sourceMeasure.map (J.restrict ∘ R.globalField) :=
      Measure.map_map hrestrict R.globalField_measurable
    _ = R.sourceMeasure.map
          (fun ω => J.restrict (R.globalField ω)) := by
      rfl
    _ = F.finiteMarginal J := R.finiteLaw J

/-- The projective-limit measure object obtained from a common realization. -/
noncomputable def
    EuclideanYangMillsCommonProbabilityRealization.projectiveLimitMeasure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    EuclideanYangMillsProjectiveLimitMeasure F :=
  { continuumMeasure := R.continuumMeasure
    projectiveLimit := R.continuumMeasure_isProjectiveLimit }

/-- Existence of a projective-limit measure under the common-realization
hypothesis. -/
theorem euclidean_yang_mills_projective_limit_exists_of_common_realization
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  ⟨R.continuumMeasure, R.continuumMeasure_isProjectiveLimit⟩

/-- Structure-level existence form. -/
theorem euclidean_yang_mills_projective_limit_nonempty_of_common_realization
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    Nonempty (EuclideanYangMillsProjectiveLimitMeasure F) :=
  ⟨R.projectiveLimitMeasure⟩

/-- The induced projective-limit measure is a probability measure. -/
theorem
    EuclideanYangMillsCommonProbabilityRealization.continuumMeasure_probability
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    IsProbabilityMeasure R.continuumMeasure := by
  letI : IsProbabilityMeasure R.sourceMeasure := R.sourceProbability
  exact Measure.isProbabilityMeasure_map
    R.globalField_measurable.aemeasurable

/-- Every measurable cylinder has exactly the prescribed finite-dimensional
probability. -/
theorem
    EuclideanYangMillsCommonProbabilityRealization.continuumMeasure_cylinder
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, F.fieldValue x)}
    (hs : MeasurableSet s) :
    R.continuumMeasure (cylinder J s) = F.finiteMarginal J s := by
  exact R.continuumMeasure_isProjectiveLimit.measure_cylinder J hs

/-- The induced measure is the unique projective limit of the given finite
marginal family. -/
theorem
    EuclideanYangMillsCommonProbabilityRealization.continuumMeasure_unique
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F)
    (ν : Measure F.Configuration)
    (hν : IsProjectiveLimit ν F.finiteMarginal) :
    ν = R.continuumMeasure := by
  letI : ∀ J, IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability
  exact hν.unique R.continuumMeasure_isProjectiveLimit

/-- Audit-visible certificate for the common-realization existence route. -/
structure EuclideanYangMillsCommonProbabilityRealizationCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) where
  projectiveLimit :
    IsProjectiveLimit R.continuumMeasure F.finiteMarginal
  probability : IsProbabilityMeasure R.continuumMeasure
  finiteMarginalsRecovered :
    ∀ J : Finset EuclideanFourSpace,
      R.continuumMeasure.map J.restrict = F.finiteMarginal J
  unique :
    ∀ ν : Measure F.Configuration,
      IsProjectiveLimit ν F.finiteMarginal →
        ν = R.continuumMeasure

/-- Construct the common-realization existence certificate. -/
def euclideanYangMillsCommonProbabilityRealizationCertificate
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    EuclideanYangMillsCommonProbabilityRealizationCertificate R :=
  { projectiveLimit := R.continuumMeasure_isProjectiveLimit
    probability := R.continuumMeasure_probability
    finiteMarginalsRecovered := R.continuumMeasure_isProjectiveLimit
    unique := fun ν hν => R.continuumMeasure_unique ν hν }

end

end MathlibAnalytic
end MGAP4D
