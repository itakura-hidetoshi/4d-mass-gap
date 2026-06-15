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

/-- Compile gate for equality of the countable-skeleton and explicit laws. -/
theorem finite_wilson_countableSkeleton_limit_eq_explicit_compile_smoke :
    S.projectiveLimitMeasure.continuumMeasure =
      R.projectiveLimitMeasure.continuumMeasure :=
  finite_wilson_single_source_countableSkeletonLimit_eq_explicitLimit R S

/-- Compile gate for the rebased countable-skeleton analytic transfer datum. -/
noncomputable def finite_wilson_countableSkeleton_os_data_compile_smoke :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData
      R.toProjectiveRealization.toProjectiveCylinderFamily
      S.projectiveLimitMeasure :=
  R.countableSkeletonOSAnalyticTransferData S D

/-- Compile gate for the countable-skeleton continuum construction. -/
noncomputable def finite_wilson_countableSkeleton_os_construction_compile_smoke :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  R.countableSkeletonOSContinuumConstruction S D

/-- Compile gate showing that the countable-skeleton construction uses the
explicit `globalObserve` pushforward law. -/
theorem finite_wilson_countableSkeleton_os_measure_compile_smoke :
    (R.countableSkeletonOSContinuumConstruction S D).limit.continuumMeasure =
      R.continuumMeasure :=
  finite_wilson_single_source_countableSkeleton_os_measure_eq_explicit R S D

/-- Compile gate for countable-skeleton OS/Wightman readiness. -/
theorem finite_wilson_countableSkeleton_os_ready_compile_smoke :
    (R.countableSkeletonOSContinuumConstruction S D).toMeasurePackage.ready :=
  finite_wilson_single_source_countableSkeleton_os_ready R S D

/-- Compile gate for simultaneous readiness of all four continuum routes. -/
theorem finite_wilson_four_os_routes_ready_compile_smoke :
    (R.explicitOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction D).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S D).toMeasurePackage.ready :=
  finite_wilson_single_source_four_os_routes_ready R S D

/-- Compile gate for equality of all four theorem-generated continuum laws. -/
theorem finite_wilson_four_os_route_measures_compile_smoke :
    (R.explicitOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction D).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S D).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_four_os_route_measures_eq_explicit R S D

end

end MathlibAnalytic
end MGAP4D
