import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishProjectiveContinuumConstruction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {F : EuclideanYangMillsProjectiveCylinderFamily}
  [∀ x, TopologicalSpace (F.fieldValue x)]
  [∀ x, BorelSpace (F.fieldValue x)]
  [∀ x, PolishSpace (F.fieldValue x)]

/-- Compile gate: the canonical Kolmogorov measure is promoted to the complete
continuum-construction interface. -/
theorem euclidean_yang_mills_polish_continuum_construction_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction F :=
  D.toContinuumConstruction

/-- Compile gate: the promoted construction recovers the finite-dimensional
projective family. -/
theorem euclidean_yang_mills_polish_continuum_projectiveLimit_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    IsProjectiveLimit
      D.toContinuumConstruction.limit.continuumMeasure
      F.finiteMarginal :=
  D.projectiveLimit

/-- Compile gate: the promoted continuum measure is a probability measure. -/
theorem euclidean_yang_mills_polish_continuum_probability_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    IsProbabilityMeasure
      D.toContinuumConstruction.limit.continuumMeasure :=
  D.continuumProbability

/-- Compile gate: the promoted construction exposes the complete typed
continuum certificate. -/
theorem euclidean_yang_mills_polish_continuum_certificate_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    EuclideanYangMillsProjectiveContinuumMeasureCertificate
      D.toContinuumConstruction :=
  D.toContinuumCertificate

/-- Compile gate: after supplying the remaining analytic OS properties, the
resulting package is ready for the existing reconstruction bridge. -/
theorem euclidean_yang_mills_polish_measure_package_ready_compile_smoke
    (D : EuclideanYangMillsPolishContinuumAnalyticData F) :
    D.toContinuumConstruction.toMeasurePackage.ready :=
  D.measurePackageReady

end

end MathlibAnalytic
end MGAP4D
