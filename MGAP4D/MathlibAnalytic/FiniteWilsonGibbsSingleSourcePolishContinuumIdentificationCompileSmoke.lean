import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourcePolishContinuumIdentification

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, TopologicalSpace (R.fieldValue x)]
  [∀ x, BorelSpace (R.fieldValue x)]
  [∀ x, PolishSpace (R.fieldValue x)]
  (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)

/-- Compile gate for identification of the abstract Kolmogorov law with the
direct global-observation pushforward. -/
theorem finite_wilson_single_source_polish_identification_compile_smoke :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
      (W.system R.sourceScale).gibbsMeasure.map R.globalObserve :=
  finite_wilson_single_source_polish_measure_eq_globalObserve_map R D

/-- Compile gate for the bundled identification audit packet. -/
noncomputable def finiteWilsonGibbsSingleSourcePolishIdentificationCertificateCompileSmoke :
    FiniteWilsonGibbsSingleSourcePolishIdentificationCertificate R D :=
  finiteWilsonGibbsSingleSourcePolishIdentificationCertificate R D

end

end MathlibAnalytic
end MGAP4D
