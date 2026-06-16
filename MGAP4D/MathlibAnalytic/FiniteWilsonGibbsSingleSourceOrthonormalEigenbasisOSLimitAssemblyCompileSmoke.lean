import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_orthonormal_eigenbasis_finite_spectral_analytic_data_compile_smoke :
    FiniteWilsonOSAutomaticFiniteSpectralAnalyticLimitConstructionData W F L :=
  D.toFiniteSpectralAnalyticData

theorem finite_wilson_orthonormal_eigenbasis_four_properties_compile_smoke :
    D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_orthonormal_eigenbasis_four_limit_properties D

theorem finite_wilson_orthonormal_eigenbasis_assembly_continuum_bound_compile_smoke
    (O : D.clusterEigenbasis.Observable) (r : ℕ) :
    ‖D.clusterEigenbasis.continuumConnectedCorrelation O r‖ ≤
      D.clusterEigenbasis.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_orthonormal_eigenbasis_continuum_bound D O r

theorem finite_wilson_orthonormal_eigenbasis_package_ready_compile_smoke :
    D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_orthonormal_eigenbasis_continuum_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
