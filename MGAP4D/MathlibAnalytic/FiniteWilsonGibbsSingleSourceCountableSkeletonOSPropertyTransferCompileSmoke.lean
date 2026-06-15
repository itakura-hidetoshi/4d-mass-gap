import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceCountableSkeletonOSPropertyTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- Focused compile gate for countable-skeleton measure identification. -/
theorem finite_wilson_countableSkeleton_eq_explicit_compile_smoke
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β) :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure :=
  finite_wilson_single_source_countableSkeleton_eq_explicit R S

end

end MathlibAnalytic
end MGAP4D
