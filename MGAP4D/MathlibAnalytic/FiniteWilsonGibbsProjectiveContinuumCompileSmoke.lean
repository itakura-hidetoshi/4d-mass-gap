import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsProjectiveContinuumMeasureCertificate
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Compile gate: coherent finite Wilson Gibbs data produce a typed projective
family of finite-dimensional distributions. -/
theorem finite_wilson_coherent_projective_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  finite_wilson_gibbs_coherent_pushforwards_projective R

/-- Compile gate: common-refinement finite Wilson Gibbs data also produce a
typed projective family. -/
theorem finite_wilson_common_refinement_projective_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  finite_wilson_gibbs_common_refinement_projective R

/-- Compile gate: compatible observations of one fixed Wilson Gibbs measure
already form a typed projective family. -/
theorem finite_wilson_single_source_projective_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :
    IsProjectiveMeasureFamily
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal :=
  finite_wilson_gibbs_single_source_projective R

/-- Compile gate: the common-refinement continuum certificate exposes the
actual continuum probability measure. -/
theorem finite_wilson_common_refinement_probability_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C) :
    IsProbabilityMeasure C.limit.continuumMeasure :=
  finite_wilson_common_refinement_continuum_probability K

/-- Compile gate: every continuum finite marginal is the selected finite Wilson
Gibbs pushforward. -/
theorem finite_wilson_common_refinement_marginal_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C)
    (J : Finset EuclideanFourSpace) :
    C.limit.continuumMeasure.map J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) :=
  finite_wilson_common_refinement_continuum_recovers_marginal K J

/-- Compile gate: the common-refinement continuum measure package reaches the
OS/Wightman readiness interface. -/
theorem finite_wilson_common_refinement_ready_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C) :
    C.toMeasurePackage.ready :=
  finite_wilson_common_refinement_continuum_measure_package_ready K

/-- Compile gate: the single-source continuum certificate exposes an actual
continuum probability measure. -/
theorem finite_wilson_single_source_probability_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C) :
    IsProbabilityMeasure C.limit.continuumMeasure :=
  finite_wilson_single_source_continuum_probability K

/-- Compile gate: every continuum finite marginal is the pushforward of the
fixed Wilson Gibbs source. -/
theorem finite_wilson_single_source_marginal_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C)
    (J : Finset EuclideanFourSpace) :
    C.limit.continuumMeasure.map J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) :=
  finite_wilson_single_source_continuum_recovers_marginal K J

/-- Compile gate: the single-source continuum measure package reaches the
OS/Wightman readiness interface. -/
theorem finite_wilson_single_source_ready_compile_smoke
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C) :
    C.toMeasurePackage.ready :=
  finite_wilson_single_source_continuum_measure_package_ready K

end

end MathlibAnalytic
end MGAP4D
