import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourcePolishContinuumConstruction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

theorem finite_wilson_single_source_polish_probability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    IsProbabilityMeasure
      (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure :=
  finite_wilson_single_source_continuum_probability
    (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D)

theorem finite_wilson_single_source_polish_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν =
      (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure :=
  finite_wilson_single_source_continuum_unique
    (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D) ν hν

theorem finite_wilson_single_source_polish_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).toMeasurePackage.ready :=
  finite_wilson_single_source_continuum_measure_package_ready
    (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D)

end

end MathlibAnalytic
end MGAP4D
