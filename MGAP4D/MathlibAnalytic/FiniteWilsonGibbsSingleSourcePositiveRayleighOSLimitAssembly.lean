import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapPositiveRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson continuum package with clustering generated
from a positive symmetric transfer operator and an upper Rayleigh bound. -/
structure FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData
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
  clusterPositive :
    FiniteWilsonOSAutomaticExactGapPositiveRayleighContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.gaugeAction

/-- Forget positivity only after it has generated the absolute Rayleigh bound
required by the symmetric-Rayleigh assembly. -/
noncomputable def
    FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData.toSymmetricRayleighAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L :=
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
    clusterRayleigh := D.clusterPositive.toSymmetricRayleighData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, positive-Rayleigh exact-gap
clustering, and regularity hold simultaneously for the continuum law. -/
theorem finite_wilson_os_positive_rayleigh_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L) :
    D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_symmetric_rayleigh_four_limit_properties
    D.toSymmetricRayleighAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate
constructed from transfer positivity and the upper Rayleigh bound. -/
theorem finite_wilson_os_positive_rayleigh_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L)
    (O : D.clusterPositive.Observable) (r : ℕ) :
    ‖D.clusterPositive.continuumConnectedCorrelation O r‖ ≤
      D.clusterPositive.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_positive_rayleigh_continuum_bound
    D.clusterPositive O r

/-- The positive-Rayleigh assembled continuum measure package is
OS/Wightman-ready. -/
theorem finite_wilson_os_positive_rayleigh_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W F L) :
    D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_symmetric_rayleigh_continuum_measure_package_ready
    D.toSymmetricRayleighAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Positive-Rayleigh analytic data for the explicit common-source Wilson
continuum law. -/
abbrev FiniteWilsonGibbsSingleSourcePositiveRayleighOSLimitData :=
  FiniteWilsonOSAutomaticPositiveRayleighAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source Wilson continuum law is OS/Wightman-ready when
clustering is generated from transfer positivity and an upper Rayleigh bound. -/
theorem finite_wilson_single_source_positive_rayleigh_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourcePositiveRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_symmetric_rayleigh_os_limit_ready
    R D.toSymmetricRayleighAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are simultaneously OS/Wightman-ready with
clustering generated from the positive Rayleigh package. -/
theorem finite_wilson_single_source_positive_rayleigh_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourcePositiveRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_symmetric_rayleigh_four_routes_ready
    R S D.toSymmetricRayleighAnalyticData

/-- All four positive-Rayleigh constructions use exactly the explicit
`globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_positive_rayleigh_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourcePositiveRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_symmetric_rayleigh_four_route_measures_eq_explicit
    R S D.toSymmetricRayleighAnalyticData

end

end MathlibAnalytic
end MGAP4D
