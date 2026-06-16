import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceFiniteSpectralOSLimitAssembly
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The automatic finite-Wilson continuum package with clustering generated
from an orthonormal transfer eigenbasis whose energies are uniformly bounded
below by the public exact gap. -/
structure FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData
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
  clusterEigenbasis :
    FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W
  regularityLimit : FiniteWilsonOSAutomaticRegularityLimitData W

attribute [instance]
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.gaugeGroupGroup
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.gaugeGroupTopology
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.gaugeGroupCompact
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.gaugeGroupNontrivial
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.gaugeAction

/-- Forget the orthonormal eigenbasis presentation only after Parseval has
generated the finite spectral package. -/
noncomputable def
    FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData.toFiniteSpectralAnalyticData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L) :
    FiniteWilsonOSAutomaticFiniteSpectralAnalyticLimitConstructionData W F L :=
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
    clusterSpectral := D.clusterEigenbasis.toFiniteSpectralData
    regularityLimit := D.regularityLimit }

/-- Reflection positivity, Euclidean invariance, eigenbasis exact-gap
clustering, and regularity hold simultaneously for the continuum law. -/
theorem finite_wilson_os_orthonormal_eigenbasis_four_limit_properties
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L) :
    D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.reflectionLimit.ContinuumReflectionPositive ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.euclideanLimit.toEuclideanInvarianceLimitData.ContinuumEuclideanInvariant ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.clusterLimit.toClusterLimitData.ContinuumClusterProperty ∧
      D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.regularityLimit.toRegularityLimitData.ContinuumRegularity :=
  finite_wilson_os_finite_spectral_four_limit_properties
    D.toFiniteSpectralAnalyticData

/-- The continuum connected correlation inherits the exact-gap estimate
constructed from the orthonormal eigenbasis support condition. -/
theorem finite_wilson_os_orthonormal_eigenbasis_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L)
    (O : D.clusterEigenbasis.Observable) (r : ℕ) :
    ‖D.clusterEigenbasis.continuumConnectedCorrelation O r‖ ≤
      D.clusterEigenbasis.decayAmplitude O *
        exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_orthonormal_eigenbasis_continuum_bound
    D.clusterEigenbasis O r

/-- The orthonormal-eigenbasis assembled continuum measure package is
OS/Wightman-ready. -/
theorem finite_wilson_os_orthonormal_eigenbasis_continuum_measure_package_ready
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    (D : FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W F L) :
    D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData.toProjectiveLimitTransferData.toContinuumConstruction.toMeasurePackage.ready :=
  finite_wilson_os_finite_spectral_continuum_measure_package_ready
    D.toFiniteSpectralAnalyticData

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, Fintype (R.fieldValue x)]
  [∀ x, Countable (R.fieldValue x)]
  [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]

/-- Orthonormal-eigenbasis analytic data for the explicit common-source Wilson
continuum law. -/
abbrev FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitData :=
  FiniteWilsonOSAutomaticOrthonormalEigenbasisAnalyticLimitConstructionData W
    R.toProjectiveRealization.toProjectiveCylinderFamily
    R.projectiveLimitMeasure

/-- The explicit common-source Wilson continuum law is OS/Wightman-ready when
clustering is generated from an orthonormal eigenbasis above the exact gap. -/
theorem finite_wilson_single_source_orthonormal_eigenbasis_os_limit_ready
    (D : FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitData R) :
    (R.explicitOSContinuumConstruction
      (R.automaticOSLimitTransferData
        D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_finite_spectral_os_limit_ready
    R D.toFiniteSpectralAnalyticData

variable {κ : Type*} [Countable κ] [Nonempty κ]
  {β : κ → Type*} [∀ k, MeasurableSpace (β k)]
  [∀ k, StandardBorelSpace (β k)]

/-- All four continuum routes are simultaneously OS/Wightman-ready with
clustering generated from orthonormal eigenbasis support above the exact gap. -/
theorem finite_wilson_single_source_orthonormal_eigenbasis_four_routes_ready
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).toMeasurePackage.ready :=
  finite_wilson_single_source_finite_spectral_four_routes_ready
    R S D.toFiniteSpectralAnalyticData

/-- All four orthonormal-eigenbasis constructions use exactly the explicit
`globalObserve` pushforward continuum law. -/
theorem finite_wilson_single_source_orthonormal_eigenbasis_four_route_measures_eq_explicit
    (S : EuclideanYangMillsCountableSkeletonData
      R.toProjectiveRealization.toProjectiveCylinderFamily κ β)
    (D : FiniteWilsonGibbsSingleSourceOrthonormalEigenbasisOSLimitData R) :
    (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.standardBorelOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.compactTightOSContinuumConstruction
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure ∧
      (R.countableSkeletonOSContinuumConstruction S
        (R.automaticOSLimitTransferData
          D.toFiniteSpectralAnalyticData.toPositiveRayleighAnalyticData.toSymmetricRayleighAnalyticData.toTransferAnalyticData.toAutomaticData)).limit.continuumMeasure =
        R.continuumMeasure :=
  finite_wilson_single_source_finite_spectral_four_route_measures_eq_explicit
    R S D.toFiniteSpectralAnalyticData

end

end MathlibAnalytic
end MGAP4D
