import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

noncomputable def finiteDiscrete_standardBorel_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteStandardBorelLimit

noncomputable def finiteDiscrete_compactTight_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteCompactTightLimit

theorem finiteDiscrete_standardBorel_compactTight_agree_compile_smoke :
    R.finiteDiscreteStandardBorelLimit.continuumMeasure =
      R.finiteDiscreteCompactTightLimit.continuumMeasure :=
  finite_wilson_single_source_finiteDiscrete_routes_agree R

end

end MathlibAnalytic
end MGAP4D
