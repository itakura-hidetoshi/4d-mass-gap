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

variable
  (S : EuclideanYangMillsCountableSkeletonData
    R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
  (D : FiniteWilsonGibbsSingleSourceOSPropertyTransferData R)

/-- Focused compile gate for countable-skeleton measure identification. -/
theorem finite_wilson_countableSkeleton_eq_explicit_compile_smoke :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure :=
  finite_wilson_single_source_countableSkeleton_eq_explicit R S

/-- Focused compile gate for countable-skeleton analytic-data transport. -/
noncomputable def finite_wilson_countableSkeleton_transfer_compile_smoke :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      S.projectiveLimitMeasure :=
  finite_wilson_single_source_countableSkeleton_analyticTransferData R S D

/-- The transferred construction retains exactly the explicit Wilson law. -/
theorem finite_wilson_countableSkeleton_transfer_measure_compile_smoke :
    (finite_wilson_countableSkeleton_transfer_compile_smoke R S D)
        .toContinuumConstruction.limit.continuumMeasure =
      R.continuumMeasure :=
  finite_wilson_single_source_countableSkeleton_transfer_measure R S D

/-- Focused compile gate for countable-skeleton OS/Wightman readiness. -/
theorem finite_wilson_countableSkeleton_ready_compile_smoke :
    (finite_wilson_countableSkeleton_transfer_compile_smoke R S D)
      .toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_single_source_countableSkeleton_transfer_ready R S D

end

end MathlibAnalytic
end MGAP4D
