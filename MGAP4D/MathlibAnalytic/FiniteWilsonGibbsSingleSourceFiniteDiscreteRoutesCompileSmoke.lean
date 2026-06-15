import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteDiscreteRoutes

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem finiteSet_isCompact_compile_smoke
    {α : Type*} [TopologicalSpace α] {A : Set α} (hA : A.Finite) :
    IsCompact A :=
  finite_set_isCompact_probe hA

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

noncomputable def finiteDiscrete_standardBorel_limit_compile_smoke :
    EuclideanYangMillsProjectiveLimitMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.finiteDiscreteStandardBorelLimit

end

end MathlibAnalytic
end MGAP4D
