import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveMarginals

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Unified certificate joining one fixed finite Wilson Gibbs source to a
four-dimensional projective-limit continuum measure. -/
structure FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) where
  singleSource : FiniteWilsonGibbsSingleSourceProjectiveCertificate R
  continuum : EuclideanYangMillsProjectiveContinuumMeasureCertificate C
  continuumCylinderIsWilsonGibbs :
    ∀ (J : Finset EuclideanFourSpace)
      (s : Set (∀ x : J, R.fieldValue x)),
      MeasurableSet s →
        C.limit.continuumMeasure (cylinder J s) =
          (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s)

/-- Construct the single-source-to-continuum certificate. -/
def finiteWilsonGibbsSingleSourceContinuumMeasureCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily) :
    FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C :=
  { singleSource := finiteWilsonGibbsSingleSourceProjectiveCertificate R
    continuum := euclideanYangMillsProjectiveContinuumMeasureCertificate C
    continuumCylinderIsWilsonGibbs := fun J _s hs =>
      finite_wilson_gibbs_single_source_projective_limit_cylinder
        R C.limit J hs }

/-- The continuum measure generated from one fixed Wilson Gibbs source is a
probability measure. -/
theorem finite_wilson_single_source_continuum_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C) :
    IsProbabilityMeasure C.limit.continuumMeasure :=
  K.continuum.continuumProbability

/-- Every finite-dimensional marginal of the continuum measure is exactly the
pushforward of the fixed finite Wilson Gibbs source through the corresponding
observation map. -/
theorem finite_wilson_single_source_continuum_recovers_marginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C)
    (J : Finset EuclideanFourSpace) :
    C.limit.continuumMeasure.map J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) := by
  calc
    C.limit.continuumMeasure.map J.restrict =
        R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal J :=
      K.continuum.finiteMarginalsRecovered J
    _ = (W.system R.sourceScale).gibbsMeasure.map (R.observe J) := by
      rfl

/-- The continuum measure is uniquely determined by the compatible
single-source Wilson marginal family. -/
theorem finite_wilson_single_source_continuum_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν = C.limit.continuumMeasure :=
  K.continuum.continuumUnique ν hν

/-- The generated continuum measure package reaches the OS/Wightman
reconstruction readiness interface. -/
theorem finite_wilson_single_source_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {C : EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily}
    (K : FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate R C) :
    C.toMeasurePackage.ready :=
  K.continuum.measurePackageReady

end

end MathlibAnalytic
end MGAP4D
