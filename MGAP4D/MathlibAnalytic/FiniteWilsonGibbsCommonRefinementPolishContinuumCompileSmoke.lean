import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementPolishContinuumConstruction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsCommonRefinementRealization W)
  [∀ x, TopologicalSpace (R.fieldValue x)]
  [∀ x, BorelSpace (R.fieldValue x)]
  [∀ x, PolishSpace (R.fieldValue x)]
  (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R)

/-- Compile gate for automatic construction of the Polish continuum measure. -/
theorem finite_wilson_common_refinement_polish_construction_compile_smoke :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D

/-- Compile gate for exact recovery of the finite Wilson Gibbs marginals. -/
theorem finite_wilson_common_refinement_polish_marginal_compile_smoke
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) :=
  finite_wilson_common_refinement_polish_recovers_marginal R D J

/-- Compile gate for exact measurable-cylinder probabilities. -/
theorem finite_wilson_common_refinement_polish_cylinder_compile_smoke
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure
        (cylinder J s) =
      (W.system (R.scale J)).gibbsMeasure ((R.observe J) ⁻¹' s) :=
  finite_wilson_common_refinement_polish_cylinder R D J hs

/-- Compile gate for uniqueness of the continuum law. -/
theorem finite_wilson_common_refinement_polish_unique_compile_smoke
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν =
      (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure :=
  finite_wilson_common_refinement_polish_unique R D ν hν

/-- Compile gate for the downstream OS/Wightman readiness interface. -/
theorem finite_wilson_common_refinement_polish_ready_compile_smoke :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).toMeasurePackage.ready :=
  finite_wilson_common_refinement_polish_measure_package_ready R D

end

end MathlibAnalytic
end MGAP4D
