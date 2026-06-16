import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_symmetric_rayleigh_transfer_data_compile_smoke :
    FiniteWilsonOSAutomaticTransferOperatorAnalyticLimitConstructionData W F L :=
  D.toTransferAnalyticData

theorem finite_wilson_symmetric_rayleigh_four_properties_compile_smoke :
    D.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_symmetric_rayleigh_four_limit_properties D

theorem finite_wilson_symmetric_rayleigh_continuum_bound_compile_smoke
    (O : D.clusterRayleigh.Observable) (r : ℕ) :
    ‖D.clusterRayleigh.continuumConnectedCorrelation O r‖ ≤
      D.clusterRayleigh.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_symmetric_rayleigh_continuum_bound D O r

theorem finite_wilson_symmetric_rayleigh_package_ready_compile_smoke :
    D.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_symmetric_rayleigh_continuum_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
