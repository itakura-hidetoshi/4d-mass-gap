import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceAutomaticOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapStepContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson analytic package with clustering supplied by
an initial estimate and one exact-gap contraction step. -/
structure FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  gaugeGroup : Type
  [gaugeGroupGroup : Group gaugeGroup]
  [gaugeGroupTopology : TopologicalSpace gaugeGroup]
  [gaugeGroupCompact : CompactSpace gaugeGroup]
  [gaugeGroupNontrivial : Nontrivial gaugeGroup]
  [gaugeAction : MulAction gaugeGroup F.Configuration]
  gaugeActionMeasurable :
    ∀ g : gaugeGroup, Measurable (fun A : F.Configuration => g • A)
  gaugeInvariant :
    ∀ g : gaugeGroup,
      L.continuumMeasure.map (fun A : F.Configuration => g • A) =
        L.continuumMeasure
  fieldAlgebra : Type
  schwingerFunctions : ℕ → Type
  symmetric : Prop
  symmetric_proof : symmetric
  reflectionLimit : FiniteWilsonOSAutomaticReflectionLimitData W
  euclideanLimit : FiniteWilsonOSAutomaticEuclideanLimitData W
  clusterStep : FiniteWilsonOSAutomaticExactGapStepContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.gaugeAction

/-- Forget the stronger exact-gap step structure and recover the general
four-property automatic assembly input. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData.toAutomaticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticAnalyticLimitConstructionData W F L :=
  { gaugeGroup := D.gaugeGroup
    gaugeGroupGroup := D.gaugeGroupGroup
    gaugeGroupTopology := D.gaugeGroupTopology
    gaugeGroupCompact := D.gaugeGroupCompact
    gaugeGroupNontrivial := D.gaugeGroupNontrivial
    gaugeAction := D.gaugeAction
    gaugeActionMeasurable := D.gaugeActionMeasurable
    gaugeInvariant := D.gaugeInvariant
    fieldAlgebra := D.fieldAlgebra
    schwingerFunctions := D.schwingerFunctions
    symmetric := D.symmetric
    symmetric_proof := D.symmetric_proof
    reflectionLimit := D.reflectionLimit
    euclideanLimit := D.euclideanLimit
    clusterLimit := D.clusterStep.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, exact-gap clustering, and
regularity are simultaneously available in the continuum limit. -/
theorem finite_wilson_os_exact_gap_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData W F L) :
    D.reflectionLimit.ContinuumReflectionPositive ∧
      D.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.clusterStep.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.
        toClusterLimitData.ContinuumClusterProperty ∧
      D.regularityLimit.toRegularityLimitData.ContinuumRegularity := by
  exact finite_wilson_os_automatic_four_limit_properties D.toAutomaticData

/-- The assembled continuum measure package is OS/Wightman-ready. -/
theorem finite_wilson_os_exact_gap_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData W F L) :
    D.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.
      toMeasurePackage.ready :=
  finite_wilson_os_automatic_continuum_measure_package_ready D.toAutomaticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Exact-gap automatic analytic data for the explicit single-source Wilson law. -/
abbrev FiniteWilsonGibbsSingleSourceExactGapOSLimitData :=
  FiniteWilsonOSAutomaticExactGapAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source Wilson continuum law is ready when clustering is
provided only through an initial estimate and one exact-gap contraction step. -/
theorem finite_wilson_single_source_exact_gap_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_automatic_os_limit_ready R D.toAutomaticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are OS/Wightman-ready with exact-gap clustering
constructed from one-step contraction. -/
theorem finite_wilson_single_source_exact_gap_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData D.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_automatic_four_routes_ready R S D.toAutomaticData

end

end MathlibAnalytic
end MGAP4D
