import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Focused compile gate for the countable-discrete standard-Borel instance. -/
theorem finiteDiscrete_fieldValue_standardBorel_compile_smoke
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) :=
  finite_wilson_single_source_fieldValue_standardBorel R x

/-- Focused compile gate for the bundled Standard-Borel projective limit. -/
noncomputable def finiteDiscrete_standardBorel_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteStandardBorelLimit

end

end MathlibAnalytic
end MGAP4D
