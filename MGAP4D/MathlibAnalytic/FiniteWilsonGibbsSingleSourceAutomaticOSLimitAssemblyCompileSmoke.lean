import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceAutomaticOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R)

/-- Compile gate for the complete concrete finite Wilson transfer record. -/
noncomputable def finite_wilson_automatic_os_limit_data_compile_smoke :
    FiniteWilsonGibbsSingleSourceOSPropertyTransferData R :=
  R.automaticOSLimitTransferData D

/-- Compile gate for all four limiting OS properties. -/
theorem finite_wilson_automatic_four_limit_properties_compile_smoke :
    D.reflectionLimit.ContinuumReflectionPositive ∧
      D.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_automatic_four_limit_properties D

/-- Compile gate for the explicit continuum Wilson measure package. -/
theorem finite_wilson_automatic_os_limit_ready_compile_smoke :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData D)).toMeasurePackage.ready :=
  finite_wilson_single_source_automatic_os_limit_ready R D

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

variable
  (S : EuclideanYangMillsCountableSkeletonData
    R.toProjectiveRealization.toProjectiveCylinderFamily κ β)

/-- Compile gate for simultaneous readiness of all four continuum routes. -/
theorem finite_wilson_automatic_four_routes_ready_compile_smoke :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData D)).toMeasurePackage.ready :=
  finite_wilson_single_source_automatic_four_routes_ready R S D

/-- Compile gate for exact equality of all four continuum laws. -/
theorem finite_wilson_automatic_four_route_measures_compile_smoke :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData D)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData D)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_automatic_four_route_measures_eq_explicit R S D

end

end MathlibAnalytic
end MGAP4D
