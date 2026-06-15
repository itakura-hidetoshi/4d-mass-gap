import MGAP4D.MathlibAnalytic.EuclideanYangMillsCommonProbabilityRealizationProjectiveLimit
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Compile gate: a common probability realization yields a projective-limit
measure. -/
theorem euclidean_yang_mills_common_realization_exists_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    ∃ μ : Measure F.Configuration,
      IsProjectiveLimit μ F.finiteMarginal :=
  euclidean_yang_mills_projective_limit_exists_of_common_realization R

/-- Compile gate: the concrete pushforward from the common probability space is
the projective limit. -/
theorem euclidean_yang_mills_common_realization_isProjectiveLimit_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    IsProjectiveLimit R.continuumMeasure F.finiteMarginal :=
  R.continuumMeasure_isProjectiveLimit

/-- Compile gate: the common-realization projective limit is a probability
measure. -/
theorem euclidean_yang_mills_common_realization_probability_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F) :
    IsProbabilityMeasure R.continuumMeasure :=
  R.continuumMeasure_probability

/-- Compile gate: every finite marginal is recovered from the constructed
continuum measure. -/
theorem euclidean_yang_mills_common_realization_marginal_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : EuclideanYangMillsCommonProbabilityRealization F)
    (J : Finset EuclideanFourSpace) :
    R.continuumMeasure.map J.restrict = F.finiteMarginal J :=
  R.continuumMeasure_isProjectiveLimit J

/-- Compile gate: the single-source Wilson Gibbs construction satisfies the
additional common-realization hypothesis. -/
theorem finite_wilson_single_source_common_realization_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    Nonempty
      (EuclideanYangMillsCommonProbabilityRealization
        R.toProjectiveRealization.toProjectiveCylinderFamily) :=
  finite_wilson_gibbs_single_source_common_realization_exists R

/-- Compile gate: the Wilson projective-limit existence theorem is a direct
specialization of the general common-realization theorem. -/
theorem finite_wilson_single_source_common_realization_limit_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    ∃ μ : Measure
        R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration,
      IsProjectiveLimit μ
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  euclidean_yang_mills_projective_limit_exists_of_common_realization
    R.toCommonProbabilityRealization

end

end MathlibAnalytic
end MGAP4D
