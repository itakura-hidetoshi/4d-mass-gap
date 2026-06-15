import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishKolmogorovExtension
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsProjectiveFamilyTheorems
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Direct Gibbs-preserving coarse graining plus Polish coordinate spaces gives
an actual projective-limit measure. -/
theorem finite_wilson_gibbs_coherent_polish_projective_limit_exists
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  euclidean_yang_mills_polish_projective_limit_exists

/-- Common-refinement Wilson projectivity plus Polish coordinate spaces gives
an actual projective-limit measure. -/
theorem finite_wilson_gibbs_common_refinement_polish_projective_limit_exists
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  euclidean_yang_mills_polish_projective_limit_exists

/-- Single-source Wilson projectivity also admits the general Polish
Kolmogorov extension, independently of its direct common-source construction. -/
theorem finite_wilson_gibbs_single_source_polish_projective_limit_exists
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  euclidean_yang_mills_polish_projective_limit_exists

/-- The direct coarse-graining Polish extension is a probability measure. -/
theorem finite_wilson_gibbs_coherent_polish_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    IsProbabilityMeasure
      (euclideanYangMillsPolishKolmogorovMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  euclidean_yang_mills_polish_kolmogorov_probability

/-- The common-refinement Polish extension is a probability measure. -/
theorem finite_wilson_gibbs_common_refinement_polish_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    IsProbabilityMeasure
      (euclideanYangMillsPolishKolmogorovMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  euclidean_yang_mills_polish_kolmogorov_probability

/-- The single-source Polish extension is a probability measure. -/
theorem finite_wilson_gibbs_single_source_polish_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    IsProbabilityMeasure
      (euclideanYangMillsPolishKolmogorovMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  euclidean_yang_mills_polish_kolmogorov_probability

/-- For the single-source route, the direct common-source measure and the
Polish Kolmogorov extension coincide by projective-limit uniqueness. -/
theorem finite_wilson_gibbs_single_source_direct_eq_polish
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :
    R.continuumMeasure =
      euclideanYangMillsPolishKolmogorovMeasure
        R.toProjectiveRealization.toProjectiveCylinderFamily := by
  exact euclidean_yang_mills_polish_kolmogorov_unique
    R.continuumMeasure
    (finite_wilson_gibbs_single_source_continuumMeasure_isProjectiveLimit R)

end

end MathlibAnalytic
end MGAP4D
