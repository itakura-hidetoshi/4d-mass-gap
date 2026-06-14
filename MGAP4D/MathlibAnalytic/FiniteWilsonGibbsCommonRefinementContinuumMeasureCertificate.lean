import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Unified certificate joining a common-refinement family of finite Wilson
Gibbs measures to a four-dimensional projective-limit continuum measure. -/
structure FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) where
  commonRefinement : FiniteWilsonGibbsCommonRefinementCertificate R
  continuum : EuclideanYangMillsProjectiveContinuumMeasureCertificate C
  continuumCylinderIsWilsonGibbs :
    ∀ (J : Finset EuclideanFourSpace)
      (s : Set (∀ x : J, R.fieldValue x)),
      MeasurableSet s →
        C.limit.continuumMeasure (cylinder J s) =
          (W.system (R.scale J)).gibbsMeasure
            ((R.observe J) ⁻¹' s)

/-- Construct the common-refinement-to-continuum certificate. -/
def finiteWilsonGibbsCommonRefinementContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCommonRefinementRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) :
    FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C :=
  { commonRefinement := finiteWilsonGibbsCommonRefinementCertificate R
    continuum := euclideanYangMillsProjectiveContinuumMeasureCertificate C
    continuumCylinderIsWilsonGibbs := fun J _s hs =>
      finite_wilson_gibbs_common_refinement_projective_limit_cylinder
        R C.limit J hs }

/-- The continuum measure generated from common Wilson refinements is a
probability measure. -/
theorem finite_wilson_common_refinement_continuum_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C) :
    IsProbabilityMeasure C.limit.continuumMeasure :=
  K.continuum.continuumProbability

/-- Every finite-dimensional marginal of the continuum measure is the concrete
Wilson Gibbs pushforward selected by the common-refinement realization. -/
theorem finite_wilson_common_refinement_continuum_recovers_marginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C)
    (J : Finset EuclideanFourSpace) :
    C.limit.continuumMeasure.map J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) := by
  calc
    C.limit.continuumMeasure.map J.restrict =
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J :=
      K.continuum.finiteMarginalsRecovered J
    _ = (W.system (R.scale J)).gibbsMeasure.map (R.observe J) := by
      rfl

/-- The continuum measure is uniquely determined by the common-refinement
finite Wilson marginal family. -/
theorem finite_wilson_common_refinement_continuum_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν = C.limit.continuumMeasure :=
  K.continuum.continuumUnique ν hν

/-- The generated continuum measure package is ready for the OS/Wightman
reconstruction interface. -/
theorem finite_wilson_common_refinement_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCommonRefinementRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate R C) :
    C.toMeasurePackage.ready :=
  K.continuum.measurePackageReady

end

end MathlibAnalytic
end MGAP4D
