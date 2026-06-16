import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteSpectralOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticFiniteSpectralAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_finite_spectral_positive_data_compile_smoke :
    FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L :=
  D.toPositiveRayleighAnalyticData

theorem finite_wilson_finite_spectral_four_properties_compile_smoke :
    D.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_finite_spectral_four_limit_properties D

theorem finite_wilson_finite_spectral_continuum_bound_compile_smoke
    (O : D.clusterSpectral.Observable) (r : ℕ) :
    ‖D.clusterSpectral.continuumConnectedCorrelation O r‖ ≤
      D.clusterSpectral.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_finite_spectral_continuum_bound D O r

theorem finite_wilson_finite_spectral_package_ready_compile_smoke :
    D.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_finite_spectral_continuum_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
