import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishProjectiveContinuumConstruction
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section SingleSourcePolishContinuum

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [hTop : ∀ x, TopologicalSpace (R.fieldValue x)]
  [hBorel : ∀ x, BorelSpace (R.fieldValue x)]
  [hPolish : ∀ x, PolishSpace (R.fieldValue x)]

local instance singleSourceProjectedTopologicalSpace
    (x : EuclideanFourSpace) :
    TopologicalSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hTop x

local instance singleSourceProjectedBorelSpace
    (x : EuclideanFourSpace) :
    BorelSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hBorel x

local instance singleSourceProjectedPolishSpace
    (x : EuclideanFourSpace) :
    PolishSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hPolish x

abbrev FiniteWilsonGibbsSingleSourcePolishAnalyticData :=
  EuclideanYangMillsPolishContinuumAnalyticData
    R.toProjectiveRealization.toProjectiveCylinderFamily

noncomputable def finiteWilsonGibbsSingleSourcePolishContinuumConstruction
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  D.toContinuumConstruction

noncomputable def finiteWilsonGibbsSingleSourcePolishContinuumCertificate
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R) :
    FiniteWilsonGibbsSingleSourceContinuumMeasureCertificate
      R (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D) :=
  finiteWilsonGibbsSingleSourceContinuumMeasureCertificate
    R (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D)

theorem finite_wilson_single_source_polish_recovers_marginal
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) :=
  finite_wilson_single_source_continuum_recovers_marginal
    (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D) J

theorem finite_wilson_single_source_polish_cylinder
    (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure
        (cylinder J s) =
      (W.system R.sourceScale).gibbsMeasure ((R.observe J) ⁻¹' s) :=
  (finiteWilsonGibbsSingleSourcePolishContinuumCertificate R D).continuumCylinderIsWilsonGibbs
    J s hs

end SingleSourcePolishContinuum

end

end MathlibAnalytic
end MGAP4D
