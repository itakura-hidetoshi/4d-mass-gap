import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Focused compile gate for the finite-discrete standard-Borel instance. -/
theorem finiteDiscrete_fieldValue_standardBorel_compile_smoke
    (x : EuclideanFourSpace) :
    StandardBorelSpace (R.fieldValue x) :=
  finite_wilson_single_source_fieldValue_standardBorel R x

/-- Focused compile gate for compact finite-product subsets. -/
theorem finiteDiscrete_finiteProduct_set_compact_compile_smoke
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsCompact A :=
  finite_wilson_single_source_finiteProduct_set_compact R J A

/-- Focused compile gate for closed finite-product subsets. -/
theorem finiteDiscrete_finiteProduct_set_closed_compile_smoke
    (J : Finset EuclideanFourSpace)
    (A : Set (∀ x : J, R.fieldValue x)) :
    IsClosed A :=
  finite_wilson_single_source_finiteProduct_set_closed R J A

/-- Focused compile gate for the bundled Standard-Borel projective limit. -/
noncomputable def finiteDiscrete_standardBorel_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteStandardBorelLimit

end

end MathlibAnalytic
end MGAP4D
