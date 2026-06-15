import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransfer

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Rebase analytic limit-transfer data along equality of the underlying
continuum measures.  All four OS analytic limit packages are unchanged; only
the measure used by gauge invariance is transported. -/
noncomputable def
    EuclideanYangMillsProjectiveLimitAnalyticTransferData.rebaseLimit
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L L' : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L)
    (hMeasure : L'.continuumMeasure = L.continuumMeasure) :
    EuclideanYangMillsProjectiveLimitAnalyticTransferData F L' :=
  { gaugeGroup := D.gaugeGroup
    gaugeGroupGroup := D.gaugeGroupGroup
    gaugeGroupTopology := D.gaugeGroupTopology
    gaugeGroupCompact := D.gaugeGroupCompact
    gaugeGroupNontrivial := D.gaugeGroupNontrivial
    gaugeAction := D.gaugeAction
    gaugeActionMeasurable := D.gaugeActionMeasurable
    gaugeInvariant := by
      intro g
      rw [hMeasure]
      exact D.gaugeInvariant g
    fieldAlgebra := D.fieldAlgebra
    schwingerFunctions := D.schwingerFunctions
    reflectionLimit := D.reflectionLimit
    euclideanLimit := D.euclideanLimit
    symmetric := D.symmetric
    symmetric_proof := D.symmetric_proof
    clusterLimit := D.clusterLimit
    regularityLimit := D.regularityLimit }

/-- Rebased data builds a continuum construction whose measure is the target
projective-limit law. -/
theorem euclidean_yang_mills_projective_limit_rebase_continuum_measure
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L L' : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L)
    (hMeasure : L'.continuumMeasure = L.continuumMeasure) :
    (D.rebaseLimit hMeasure).toContinuumConstruction.limit.continuumMeasure =
      L'.continuumMeasure := by
  rfl

/-- The rebased construction inherits all four theorem-generated OS properties
and is ready for the OS/Wightman bridge. -/
theorem euclidean_yang_mills_projective_limit_rebase_ready
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L L' : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : EuclideanYangMillsProjectiveLimitAnalyticTransferData F L)
    (hMeasure : L'.continuumMeasure = L.continuumMeasure) :
    (D.rebaseLimit hMeasure).toContinuumConstruction.toMeasurePackage.ready :=
  euclidean_yang_mills_projective_limit_transferred_measure_package_ready
    (D.rebaseLimit hMeasure)

end

end MathlibAnalytic
end MGAP4D
