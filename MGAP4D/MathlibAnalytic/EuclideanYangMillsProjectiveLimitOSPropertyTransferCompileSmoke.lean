import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransfer

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Focused compile gate for reflection positivity under pointwise form limits. -/
theorem projective_limit_reflection_positive_compile_smoke
    (D : EuclideanYangMillsReflectionPositivityLimitData) :
    D.ContinuumReflectionPositive :=
  euclidean_yang_mills_reflection_positivity_passes_to_limit D

/-- Focused compile gate for Euclidean invariance under expectation limits. -/
theorem projective_limit_euclidean_invariant_compile_smoke
    (D : EuclideanYangMillsEuclideanInvarianceLimitData) :
    D.ContinuumEuclideanInvariant :=
  euclidean_yang_mills_euclidean_invariance_passes_to_limit D

/-- Focused compile gate for clustering under a decaying uniform envelope. -/
theorem projective_limit_cluster_compile_smoke
    (D : EuclideanYangMillsClusterLimitData) :
    D.ContinuumClusterProperty :=
  euclidean_yang_mills_cluster_property_passes_to_limit D

/-- Focused compile gate for inherited Schwinger regularity bounds. -/
theorem projective_limit_regularity_compile_smoke
    (D : EuclideanYangMillsRegularityLimitData) :
    D.ContinuumRegularity :=
  euclidean_yang_mills_regularity_passes_to_limit D

/-- Focused compile gate for assembly into the continuum measure package. -/
noncomputable def projective_limit_os_transfer_construction_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction F :=
  D.toContinuumConstruction

/-- All four transferred properties make the induced measure package ready. -/
theorem projective_limit_os_transfer_ready_compile_smoke
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L) :
    D.toContinuumConstruction.toMeasurePackage.ready :=
  euclidean_yang_mills_projective_limit_transferred_measure_package_ready D

end

end MathlibAnalytic
end MGAP4D
