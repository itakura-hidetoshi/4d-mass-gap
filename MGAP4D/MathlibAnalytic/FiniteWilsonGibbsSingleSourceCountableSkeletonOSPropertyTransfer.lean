import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceOSPropertyRouteTransfer
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCountableSkeletonExtension

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

/-- Any countable standard-Borel skeleton reconstruction recovering the finite
Wilson laws is the same continuum law as the explicit common-source
`globalObserve` pushforward. -/
theorem finite_wilson_single_source_countableSkeleton_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β) :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure := by
  change S.continuumMeasure = R.continuumMeasure
  exact finite_wilson_gibbs_single_source_constructed_unique R
    S.continuumMeasure S.isProjectiveLimit

/-- Transport the four theorem-generated OS analytic properties from the
explicit common-source Wilson law to an equal countable-skeleton realization. -/
noncomputable def finite_wilson_single_source_countableSkeleton_analyticTransferData
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      S.projectiveLimitMeasure :=
  D.rebaseLimit (finite_wilson_single_source_countableSkeleton_eq_explicit R S)

end

end MathlibAnalytic
end MGAP4D
