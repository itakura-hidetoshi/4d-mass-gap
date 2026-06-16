import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticSingleLinkHeatBathAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_single_link_heat_bath_vacuum_poincare_data_compile_smoke :
    FiniteWilsonOSAutomaticVacuumPoincareAnalyticLimitConstructionData W F L :=
  D.toVacuumPoincareAnalyticData

noncomputable def finite_wilson_single_link_heat_bath_automatic_os_data_compile_smoke :=
  D.toAutomaticOSData

theorem finite_wilson_single_link_heat_bath_four_properties_compile_smoke :
    D.toAutomaticOSData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toAutomaticOSData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toAutomaticOSData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toAutomaticOSData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_single_link_heat_bath_four_limit_properties D

theorem finite_wilson_single_link_heat_bath_os_continuum_bound_compile_smoke
    (O : D.clusterHeatBath.Observable) (r : ℕ) :
    ‖D.clusterHeatBath.continuumConnectedCorrelation O r‖ ≤
      D.clusterHeatBath.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_os_single_link_heat_bath_continuum_bound D O r

theorem finite_wilson_single_link_heat_bath_package_ready_compile_smoke :
    D.toAutomaticOSData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_single_link_heat_bath_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
