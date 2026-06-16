import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceTransferOperatorOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

variable (D : FiniteWilsonGibbsSingleSourceTransferOperatorOSLimitData R)

/-- Compile gate for the complete transfer-operator four-property package. -/
noncomputable def finite_wilson_transfer_operator_automatic_data_compile_smoke :
    FiniteWilsonOSAutomaticAnalyticLimitConstructionData W
      R.toProjectiveRealization.toProjectiveCylinderFamily
      R.projectiveLimitMeasure :=
  D.toAutomaticData

/-- Compile gate for all four limiting properties. -/
theorem finite_wilson_transfer_operator_four_properties_compile_smoke :
    D.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_transfer_operator_four_limit_properties D

/-- Compile gate for the inherited continuum cluster bound. -/
theorem finite_wilson_transfer_operator_cluster_bound_compile_smoke
    (O : D.clusterTransferOperator.Observable) (r : ℕ) :
    ‖D.clusterTransferOperator.continuumConnectedCorrelation O r‖ ≤
      D.clusterTransferOperator.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_transfer_operator_continuum_cluster_bound D O r

/-- Compile gate for the explicit continuum measure package. -/
theorem finite_wilson_transfer_operator_os_ready_compile_smoke :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_transfer_operator_os_limit_ready R D

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

variable
  (S : EuclideanYangMillsCountableSkeletonData
    R.toProjectiveRealization.toProjectiveCylinderFamily κ β)

/-- Compile gate for simultaneous readiness of all four continuum routes. -/
theorem finite_wilson_transfer_operator_four_routes_compile_smoke :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_transfer_operator_four_routes_ready R S D

end

end MathlibAnalytic
end MGAP4D
