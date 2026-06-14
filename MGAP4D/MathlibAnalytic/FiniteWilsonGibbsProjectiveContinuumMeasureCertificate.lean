import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCoherentProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Unified certificate joining concrete finite Wilson Gibbs measures to a
four-dimensional projective-limit continuum Yang--Mills measure.

The finite-dimensional distributions are not abstract measures: they are the
pushforwards of normalized Wilson Gibbs measures.  Their projectivity is derived
from a measurable Gibbs-preserving coarse-graining diagram, and the continuum
measure recovers every one of those marginals. -/
structure FiniteWilsonGibbsProjectiveContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) where
  finiteWilsonProjectivity :
    FiniteWilsonGibbsCoherentProjectiveCertificate R
  continuumConstruction :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate C
  continuumCylinderIsWilsonGibbs :
    ∀ (J : Finset EuclideanFourSpace)
      (s : Set (∀ x : J, R.fieldValue x)),
      MeasurableSet s →
        C.limit.continuumMeasure (cylinder J s) =
          (W.system (R.scale J)).gibbsMeasure
            ((R.observe J) ⁻¹' s)

/-- Assemble the unified finite-Wilson-to-continuum certificate. -/
def finiteWilsonGibbsProjectiveContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsCoherentProjectiveRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) :
    FiniteWilsonGibbsProjectiveContinuumMeasureCertificate R C :=
  { finiteWilsonProjectivity :=
      finiteWilsonGibbsCoherentProjectiveCertificate R
    continuumConstruction :=
      euclideanYangMillsProjectiveContinuumMeasureCertificate C
    continuumCylinderIsWilsonGibbs := fun J s hs =>
      finite_wilson_gibbs_coherent_projective_limit_cylinder
        R C.limit J hs }

/-- The continuum measure obtained from coherent finite Wilson data is a
probability measure. -/
theorem finite_wilson_projective_continuum_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCoherentProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsProjectiveContinuumMeasureCertificate R C) :
    IsProbabilityMeasure C.limit.continuumMeasure :=
  K.continuumConstruction.continuumProbability

/-- Every finite-dimensional distribution of the continuum measure is exactly
the pushforward of the selected finite Wilson Gibbs measure. -/
theorem finite_wilson_projective_continuum_recovers_gibbs_marginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCoherentProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsProjectiveContinuumMeasureCertificate R C)
    (J : Finset EuclideanFourSpace) :
    C.limit.continuumMeasure.map J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) := by
  calc
    C.limit.continuumMeasure.map J.restrict =
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J :=
      K.continuumConstruction.finiteMarginalsRecovered J
    _ = (W.system (R.scale J)).gibbsMeasure.map (R.observe J) :=
      finite_wilson_gibbs_coherent_projective_family_marginal_eq_map R J

/-- The continuum measure is uniquely determined by the concrete family of
finite Wilson Gibbs pushforwards. -/
theorem finite_wilson_projective_continuum_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCoherentProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsProjectiveContinuumMeasureCertificate R C)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν = C.limit.continuumMeasure :=
  K.continuumConstruction.continuumUnique ν hν

/-- The generated Euclidean Yang--Mills measure package satisfies the analytic
readiness interface required by the OS/Wightman reconstruction route. -/
theorem finite_wilson_projective_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsCoherentProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsProjectiveContinuumMeasureCertificate R C) :
    C.toMeasurePackage.ready :=
  K.continuumConstruction.measurePackageReady

end

end MathlibAnalytic
end MGAP4D
