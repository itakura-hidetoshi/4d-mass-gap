import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceExactGapOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  {F : EuclideanYangMillsProjectiveCylinderFamily}
  {L : EuclideanYangMillsProjectiveLimitMeasure F}
  (D : FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData W F L)

noncomputable def finite_wilson_exact_gap_automatic_data_compile_smoke :
    FiniteWilsonOSAutomaticAnalyticLimitConstructionData W F L :=
  D.toAutomaticData

theorem finite_wilson_exact_gap_four_properties_compile_smoke :
    D.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_exact_gap_four_limit_properties D

theorem finite_wilson_exact_gap_package_ready_compile_smoke :
    D.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_exact_gap_continuum_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
