import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementPolishContinuumConstruction
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourcePolishContinuumTheorems

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}

section CommonRefinement

variable (R : FiniteWilsonGibbsCommonRefinementRealization W)
  [∀ x, TopologicalSpace (R.fieldValue x)]
  [∀ x, BorelSpace (R.fieldValue x)]
  [∀ x, PolishSpace (R.fieldValue x)]
  (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R)

theorem finite_wilson_common_refinement_polish_compile_smoke
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) :=
  finite_wilson_common_refinement_polish_recovers_marginal R D J

end CommonRefinement

section SingleSource

variable (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, TopologicalSpace (R.fieldValue x)]
  [∀ x, BorelSpace (R.fieldValue x)]
  [∀ x, PolishSpace (R.fieldValue x)]
  (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)

theorem finite_wilson_single_source_polish_compile_smoke
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) :=
  finite_wilson_single_source_polish_recovers_marginal R D J

theorem finite_wilson_single_source_polish_ready_compile_smoke :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).toMeasurePackage.ready :=
  finite_wilson_single_source_polish_measure_package_ready R D

end SingleSource

end

end MathlibAnalytic
end MGAP4D
