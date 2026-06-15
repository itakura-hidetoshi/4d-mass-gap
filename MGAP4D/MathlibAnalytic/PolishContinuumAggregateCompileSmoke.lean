import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsPolishContinuumCompileSmoke
import MGAP4D.MathlibAnalytic.ProjectiveLimitThreeRoutesCompileSmoke

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

/-- Focused PR compile gate for the canonical Wilson--Kolmogorov continuum
measure and its exact finite-dimensional marginal law. -/
theorem polish_continuum_aggregate_compile_smoke
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system R.sourceScale).gibbsMeasure.map (R.observe J) :=
  finite_wilson_single_source_polish_recovers_marginal R D J

end

end MathlibAnalytic
end MGAP4D
