import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishProjectiveContinuumConstruction
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

abbrev FiniteWilsonGibbsSingleSourcePolishAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)] :=
  EuclideanYangMillsPolishContinuumAnalyticData
    R.toProjectiveRealization.toProjectiveCylinderFamily

noncomputable def finiteWilsonGibbsSingleSourcePolishContinuumConstruction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  D.toContinuumConstruction

noncomputable def finiteWilsonGibbsSingleSourcePolishContinuumCertificate
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate
      R (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D) :=
  finiteWilsonGibbsSingleSourceContinuumMeasureCertificate
    R (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D)

theorem finite_wilson_single_source_polish_recovers_marginal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) :=
  finite_wilson_single_source_continuum_recovers_marginal
    (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D) J

theorem finite_wilson_single_source_polish_cylinder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    [∀ x, BorelSpace (R.fieldValue x)]
    [∀ x, PolishSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure
        (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) :=
  (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D)
    .continuumCylinderIsWilsonGibbs J s hs

end

end MathlibAnalytic
end MGAP4D
