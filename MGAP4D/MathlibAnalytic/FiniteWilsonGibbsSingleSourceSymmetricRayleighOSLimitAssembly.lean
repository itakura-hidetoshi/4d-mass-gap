import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceTransferOperatorOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSymmetricRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson continuum package with clustering generated
from a symmetric transfer operator and an absolute Rayleigh quadratic-form
bound.

The scalar all-distance cluster estimate, the scalar one-step estimate, the
operator-norm contraction, and the all-matrix-coefficient estimate are all
derived rather than stored as fields. -/
structure FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData
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
  clusterRayleigh :
    FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.gaugeAction

/-- Forget the symmetric-Rayleigh presentation only after deriving the
transfer-operator contraction package. -/
noncomputable def
    FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData.toTransferAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticTransferOperatorAnalyticLimitConstructionData W F L :=
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
    clusterTransfer :=
      D.clusterRayleigh.toHilbertMatrixData.toTransferOperatorData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, symmetric-Rayleigh exact-gap
clustering, and regularity hold simultaneously for the continuum law. -/
theorem finite_wilson_os_symmetric_rayleigh_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L) :
    D.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_transfer_operator_four_limit_properties
    D.toTransferAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate
generated from symmetry and the absolute Rayleigh bound. -/
theorem finite_wilson_os_symmetric_rayleigh_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L)
    (O : D.clusterRayleigh.Observable) (r : ℕ) :
    ‖D.clusterRayleigh.continuumConnectedCorrelation O r‖ ≤
      D.clusterRayleigh.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_symmetric_rayleigh_continuum_bound
    D.clusterRayleigh O r

/-- The symmetric-Rayleigh assembled continuum measure package is
OS/Wightman-ready. -/
theorem finite_wilson_os_symmetric_rayleigh_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W F L) :
    D.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_transfer_operator_continuum_measure_package_ready
    D.toTransferAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Symmetric-Rayleigh automatic analytic data for the explicit common-source
Wilson continuum law. -/
abbrev FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitData :=
  FiniteWilsonOSAutomaticSymmetricRayleighAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source Wilson continuum law is OS/Wightman-ready when
clustering is generated from symmetry and the absolute Rayleigh estimate. -/
theorem finite_wilson_single_source_symmetric_rayleigh_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_transfer_operator_os_limit_ready
    R D.toTransferAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are simultaneously OS/Wightman-ready with
clustering generated from the symmetric Rayleigh package. -/
theorem finite_wilson_single_source_symmetric_rayleigh_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_transfer_operator_four_routes_ready
    R S D.toTransferAnalyticData

/-- All four symmetric-Rayleigh constructions use exactly the explicit
`globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_symmetric_rayleigh_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceSymmetricRayleighOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_transfer_operator_four_route_measures_eq_explicit
    R S D.toTransferAnalyticData

end

end MathlibAnalytic
end MGAP4D
