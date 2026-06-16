import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourcePositiveRayleighOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_positive_rayleigh_symmetric_data_compile_smoke :
    FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L :=
  D.toSymmetricRayleighAnalyticData

theorem finite_wilson_positive_rayleigh_four_properties_compile_smoke :
    D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_positive_rayleigh_four_limit_properties D

theorem finite_wilson_positive_rayleigh_continuum_bound_compile_smoke
    (O : D.clusterPositive.Observable) (r : ℕ) :
    ‖D.clusterPositive.continuumConnectedCorrelation O r‖ ≤
      D.clusterPositive.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_positive_rayleigh_continuum_bound D O r

theorem finite_wilson_positive_rayleigh_package_ready_compile_smoke :
    D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_positive_rayleigh_continuum_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
